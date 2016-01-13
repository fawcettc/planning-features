
/* 2012 (C) Jussi Rintanen, jrintanen.jr@gmail.com */

#include <stdio.h>
#include <stdlib.h>

#include "interface.h"
#include "clausedb.h"
#include "printplan.h"

#include "main.h"
#include "asyntax.h"
#include "ordintsets.h"
#include "operators.h"
#include "translate2sat.h"

#include <assert.h>

#ifdef __LP64__
#include <xmmintrin.h>
#endif

#define noUCC

#define ASSERTS

#ifdef ASSERTS
#define ASSERT(a) (assert(a))
#else
#define ASSERT(a) (1)
#endif

#include "varvals.c"

#define unlikely(expr) (__builtin_expect((expr),0))
#define likely(expr) (__builtin_expect((expr),1))
//#define unlikely(expr) (expr)
//#define likely(expr) (expr)

#define CACHEALIGN
#ifdef CACHEALIGN
#define CACHELINESIZE 64
#define CACHELINESIZEi 16
PTRINT cachelineboundary(PTRINT addr) {
  if(addr&63) {
    return addr+(64-(addr&63));
  } else return addr;
}
PTRINT cachelineboundaryi(PTRINT addr) {
  if(addr&63) {
    return addr+(16-(addr&15));
  } else return addr;
}
#else
#define CACHELINESIZE 0
#define CACHELINESIZEi 0
PTRINT cachelineboundary(PTRINT addr) {
  return addr;
}
PTRINT cachelineboundaryi(PTRINT addr) {
  return addr;
}
#endif

/* Interface to malloc */

void *ownalloc(int code,int i) {
  void *ptr = malloc(i);
  ASSERT(ptr);
  allocatedbyCL += i;
  check_malloc_success(ptr,1000+code);
  return (PTRINT)ptr;
}

#define min(a,b) (((a)<(b))?(a):(b))
#define max(a,b) (((a)>(b))?(a):(b))

/* Heap data structure */

#ifdef VSIDS
heap heap_create(int);
void freeheap(heap);
int heap_emptyp(satinstance);
int heap_taketop(satinstance);
void heap_delete(satinstance,int);
void heap_insert(satinstance,int,int);
void heap_increment(satinstance,int);
void heap_increment_by(satinstance,int,int);
void heap_decay(satinstance);
void checkheapconsistency(satinstance);
#endif

/* Macros for accessing
   - the value of a propositional variable,
   - the reason for the value of a propositional variable,
   - the decision level of the propositional variable,
   - the status (mainly the phase) of a propositional variable.
*/

#if defined(__LP64__)
#define REASON_INPUT -2L
#define REASON_DECISION -1L
#else
#define REASON_INPUT -2
#define REASON_DECISION -1
#endif


int VALUE(int l) { return (l&1)^1; }
int NEG(int l) { return l^1; }
int VAR(int l) { return l>>1; }
int PLIT(int v) { return v << 1; }
int NLIT(int v) { return 1+(PLIT(v)); }
int LIT(int v) { return PLIT(v); }

/* Macros for accessing
   - the score of a literal,
   - the clauses in which the literal is watched,
   - two literal clauses -l V l' for a literal l.
*/

#define LITSCORE(l) (sati->lits[(l)].score)

/* Macros for accessing the heap. */

#define HINDEX(v) (sati->hindex[(v)])

void report_malloc(char *arrayname,int size) {
#ifdef DEBUG
  printf("%s: %.2f MB\n",arrayname,((float)size)/1024.0/1024.0);
#endif
}

/****** INCLUDED SOURCE FILES: ********************************************/
#include "heuristics2.c"
/**************************************************************************/

#define noDEBUG
#define noHARDDEBUG


/* Initialize data structures used for all problem instances. */

int adjustheap;

#ifndef MULTICORE
int cround;	/* Counter which is incremented for new conflict clauses */
int maxwasseen;
int *wasseen;	/* Counter when literal was last encountered */
#endif

/* Functions for marking literals for different purposes. */

void nextround(satinstance sati) {
#ifdef MULTICORE
  threads[sati->thread].cround += 1;
#else
  cround += 1;
#endif
}

int seenp(satinstance sati,int l) {	/* Was literal already seen on the current round? */
  int tmp;
#ifdef MULTICORE
  ASSERT(l < threads[sati->thread].maxwasseen);
#else
  ASSERT(l < maxwasseen);
#endif
#ifdef MULTICORE
  tmp = (threads[sati->thread].wasseen[l] == threads[sati->thread].cround);
  threads[sati->thread].wasseen[l] = threads[sati->thread].cround;	/* Mark the literal as seen on the current round. */
#else
  tmp = (wasseen[l] == cround);
  wasseen[l] = cround;	/* Mark the literal as seen on the current round. */
#endif
  return tmp;
}

/* This is called from outside after all clauses are there. */

float memoryused() {
  float MB;
  MB = (allocatedbyFE+allocatedbyCDB+allocatedbyCL)/1024.0/1024.0;
  return MB;
}

void init_clausesets(int varspertime) {
  int i;
  allocatedbyCL = 0.0;

#ifdef MULTICORE
  threads = (thread *)malloc(sizeof(thread) * nOfThreads);

  for(j=0;j<nOfThreads;j++) {
    threads[j].cround = 1;
    threads[j].maxwasseen = varspertime * 2 * 150;
    threads[j].wasseen = (int *)ownalloc(700,threads[j].maxwasseen * sizeof(int));
    for(i=0;i<threads[j].maxwasseen;i++) threads[j].wasseen[i] = 0;
  }
#else
  cround = 1;
  maxwasseen = varspertime * 2 * 150;
  wasseen = (int *)ownalloc(700,maxwasseen * sizeof(int));
  for(i=0;i<maxwasseen;i++) wasseen[i] = 0;
#endif


  adjustheap = 1; /* Variable scores may change now. */
}

#ifdef DEBUG
void printclause(satinstance sati,int *c) {
  while(*c != -1) {
    printf(" %i:",VAR(*c)); printTlit(sati,*c);
    if(litfalsep(sati,*c)) printf(" F");
    if(littruep(sati,*c)) printf(" T");
    c += 1;
  }
  printf("\n");
}
#endif

#ifdef ASSERTS
int isliteral(satinstance sati,int i) {
  if(i < 0) return 0;
  if(VAR(i) < 0) return 0;
  if(VAR(i) >= sati->nOfVars) return 0;
  return 1;
}
#endif

nintlist *nintcons(int i,nintlist *l) {
  nintlist *l2;
  l2 = (nintlist *)malloc(sizeof(nintlist));
  l2->hd = i;
  l2->tl = l;
  return l2;
}


/*************************************************************************/
/** The size of an instance **********************************************/
/*************************************************************************/

/* Return an estimated size in MB of an instance data structure */

float estimateinstancesize(int tpoints,int varsPT,int actions) {
  float size;
  size = ((float)(tpoints*varsPT)) * 
    ((float)
    (sizeof(int) +    /* unitstack, int */
     2*sizeof(literal) + /* literal, literal */
     sizeof(short) + /* variableval, 2*char */
#ifdef VSIDS
     sizeof(STATUSTYPE) + /* variablestatus, STATUSTYPE */
#endif
     sizeof(PTRINT) + /* variablereason, PTRINT */
     sizeof(int) + /* variabledlevel, int */
     sizeof(int) + /* declevels, int */
#ifdef COSTS
     sizeof(int) + /* declevelscost, int */
#endif
     sizeof(int))) + /* wasseen, int */
    (float)(sizeof(int) * actions * 5); /* Frame axioms, very bad estimate */

  return size / 1024.0 / 1024.0;
}

/*************************************************************************/
/** Initialize an instance                                              **/
/*************************************************************************/

satinstance newinstance(int id,int times,int varsPT,int svars,int actions) {
  int i;
  satinstance sati = (satinstance)ownalloc(701,sizeof(struct _satinstance));

  sati->value = -1;	/* Truth-value unknown */
  sati->id = id;
  sati->thread = -1;

  sati->nOfSVars = svars;
  sati->nOfActions = actions;
  sati->nOfVarsPerTime = varsPT;
  sati->nOfTPoints = times;

  /* Last time point has only state variables, no actions or auxiliaries. */
  /* Is this correct? What happens with complex goals that require Tseitin? */

  sati->nOfVars = (times-1)*varsPT+sati->nOfSVars;

#ifdef DEBUG
  printf("\n==================================================\n");
  printf("nOfSVars = %i\n",sati->nOfSVars);
  printf("nOfActions = %i\n",sati->nOfActions);
  printf("nOfVars = %i\n",sati->nOfVars);
  printf("nOfVarsPerTime = %i\n",sati->nOfVarsPerTime);
  printf("nOfTPoints = %i\n",sati->nOfTPoints);
#endif

  sati->unitstack = (int *)ownalloc(702,sizeof(int) * sati->nOfVars);
  report_malloc("unitstack",sizeof(int) * sati->nOfVars);
  sati->endunitstack = -1;
  sati->startunitstack = 0;

  /* This does not take into account the initial unit clauses coming
     from the goal formula (which might also involve Tseitin!). */

  sati->initialunits = 0;
  sati->maxinitialunits = sati->nOfSVars+200;
  sati->initialunittable = (int *)ownalloc(703,sati->maxinitialunits * sizeof(int));
  report_malloc("initialunittable",sati->maxinitialunits * sizeof(int));

  sati->notcalledbefore = 1;
  sati->complete = 0;

  if(!noT2clauses) {
    sati->l2its = (nintlist **)ownalloc(704,sizeof(nintlist *)
					* sati->nOfVarsPerTime * 2);
    report_malloc("l2its",sizeof(nintlist *) * sati->nOfVarsPerTime * 2);
    for(i=0;i<sati->nOfVarsPerTime*2;i++) sati->l2its[i] = NULL;
  }

  sati->lits = (literal *)ownalloc(706,sizeof(literal) * sati->nOfVars * 2);
  report_malloc("lits",sizeof(literal) * sati->nOfVars * 2);

  /* variableval according to the chosen literal value representation */

#ifdef REPRONE
  sati->variableval = (VALTYPE *)ownalloc(707,sizeof(VALTYPE) * sati->nOfVars);
#endif

#ifdef REPRTWO
  sati->variableval = (VALTYPE *)ownalloc(708,sizeof(VALTYPE) * (1 + sati->nOfVars / 8));
#endif

#ifdef REPRTHREE
  sati->variableval = (VALTYPE *)ownalloc(708,sizeof(VALTYPE) * 2 * sati->nOfVars);
#endif

#ifdef REPRFOUR
  sati->variableval = (VALTYPE *)ownalloc(708,sizeof(VALTYPE) * (1 + sati->nOfVars / 8));
#endif


#ifdef VSIDS
  sati->variablestatus = (STATUSTYPE *)ownalloc(709,sizeof(STATUSTYPE) * sati->nOfVars);
  report_malloc("variablestatus",sizeof(STATUSTYPE) * sati->nOfVars);
#endif

#ifdef REASONDLEVEL
  sati->variablerd = (RD *)ownalloc(710,sizeof(RD) * sati->nOfVars);
  report_malloc("variablerd",sizeof(RD) * sati->nOfVars);
#else
  sati->variablereason = (PTRINT *)ownalloc(710,sizeof(PTRINT) * sati->nOfVars);
  sati->variabledlevel = (int *)ownalloc(711,sizeof(int) * sati->nOfVars);
  report_malloc("variablereason",sizeof(PTRINT) * sati->nOfVars);
  report_malloc("variabledlevel",sizeof(int) * sati->nOfVars);
#endif
  report_malloc("variableval",sizeof(VALTYPE) * sati->nOfVars);

  sati->declevels = (int *)ownalloc(800,sizeof(int) * sati->nOfVars);
#ifdef COSTS
  sati->declevelscost = (int *)ownalloc(801,sizeof(int) * sati->nOfVars);
#endif

  /* Resize tag arrays if too small. */

#ifdef MULTICORE
  if(2*sati->nOfVars > threads[0].maxwasseen) {
    int i,j;
    for(j=0;j<nOfThreads;j++) {
      threads[j].cround = 1;
      threads[j].maxwasseen = sati->nOfVars*3;
      threads[j].wasseen = (int *)realloc(threads[j].wasseen,threads[j].maxwasseen * sizeof(int));
      for(i=0;i<threads[j].maxwasseen;i++) {
	threads[j].wasseen[i] = 0;
      }
    }
  }
#else
  if(2*sati->nOfVars > maxwasseen) {
    int i;
    cround = 1;
    maxwasseen = sati->nOfVars*3;
    wasseen = (int *)realloc(wasseen,maxwasseen * sizeof(int));
    for(i=0;i<maxwasseen;i++) {
      wasseen[i] = 0;
    }
  }
#endif

  sati->decisions = 0;
  sati->conflicts = 0;
  sati->decaysteps = 0;

  sati->pheuristic = 0;
  sati->heuristic = 0;
  //  sati->nlevel = -1;


#ifdef VSIDS
  /* Heap for maintaining a priority queue of variables. */

  /* This is the location of a variable in the heap array. */
  sati->hindex = (int *)ownalloc(712,sizeof(int) * (sati->nOfVars+2));
  report_malloc("hindex",sizeof(int) * sati->nOfVars);

  sati->scoreheap = heap_create(sati->nOfVars);

  /* For efficiency reasons, we don't use heap_insert, and won't order
     the heap before all variable weights have been calculated. */
  /* Initially each variable i is in the heap in position i. */
  for(i=0;i<sati->nOfVars;i++) {
    HINDEX(i) = i;
    sati->scoreheap->array[i].k = i;
    sati->scoreheap->array[i].v = 0;
  }
  sati->scoreheap->els = sati->nOfVars;

  adjustheap = 0;	/* Don't adjust the heap before instance complete. */

#endif

  for(i=0;i<sati->nOfVars*2;i++) {	/* Initialize literals. */
    LITWATCHES(i) = NULL;

#ifdef WEIGHTS
    LITSCORE(i) = 0;
#endif
  }

  for(i=0;i<sati->nOfVars;i++) {	/* Initialize variables. */
    varunset(sati,i);
#ifdef VSIDS
    VARSTATUS(i) = 0;
#endif
  }

#ifdef LBD
  sati->LBDflag = (int *)ownalloc(718,sati->nOfVars * sizeof(int));
  for(i=0;i<sati->nOfVars;i++) sati->LBDflag[i]=0;
  sati->LBDcounter = 1;
#endif

  /* Cost vector used when finding assignments with low costs */

#ifdef COSTS
  sati->costs = (int *)ownalloc(719,sizeof(int) * sati->nOfVarsPerTime);
  for(i=0;i<sati->nOfVarsPerTime;i++) sati->costs[i] = 0;
  sati->currentcost = 0;
  sati->costbound = 0x7fffffff;
#endif

#ifdef DEBUG
  printf("================================\n");
  printf("Initialized instance:\n");
  printf("total vars: %i\n",sati->nOfVars);
  printf("state vars: %i\n",sati->nOfSVars);
  printf("vars per time: %i\n",sati->nOfVarsPerTime);
  printf("time points: %i\n",sati->nOfTPoints);
  printf("================================\n");
#endif

  return sati;
}

void setheuristic(satinstance sati,int h) {
  sati->heuristic = h;
}

void setpheuristic(satinstance sati,int h) {
  sati->pheuristic = h;
}


/**************************************************************************/
/*******  Keeping track of the heuristic ordering of literals       *******/
/**************************************************************************/

#ifdef WEIGHTS
int scoreof(satinstance sati,int var) {
  return LITSCORE(PLIT(var)) + LITSCORE(NLIT(var));
}

void decay_score(satinstance sati) {
  int i;
  sati->decaysteps += 1;
  if((sati->decaysteps & 31) == 0) { /* Discount scores. */
#ifdef VSIDS
    heap_decay(sati);
#endif
    for(i=0;i<2*sati->nOfVars;i++) LITSCORE(i) = (LITSCORE(i) >> 1);
  }
}

/* Increase score and update the heap. */

void increase_score(satinstance sati,int lit) {
  ASSERT(VAR(lit) < sati->nOfVars);
  LITSCORE(lit) += 1;
#ifdef VSIDS
  if(adjustheap && HINDEX(VAR(lit)) != -1) {	/* Update heap. */
    heap_increment(sati,HINDEX(VAR(lit)));
  }
#endif
}

void increase_score_by(satinstance sati,int lit,int n) {
  LITSCORE(lit) += n;
#ifdef VSIDS
  if(adjustheap && HINDEX(VAR(lit)) != -1) {	/* Update heap. */
    heap_increment_by(sati,HINDEX(VAR(lit)),n);
  }
#endif
}

#ifdef VSIDS
int getbest(satinstance sati) {
  int var;

  if(!heap_emptyp(sati)) {
    do {
      var = heap_taketop(sati);
    } while((!varunsetp(sati,var)) && (!heap_emptyp(sati)));

    if(!varunsetp(sati,var)) return -1;

    /* Next, decide whether to have the literal POSITIVE or NEGATIVE. */

    /* Use PHASE and SCORE. Break ties randomly. */

    switch(VARSTATUS(var) & 3) {	/* Check phase. */
    case 2: return NLIT(var);
    case 3: return PLIT(var);
    default:
      if(LITSCORE(PLIT(var)) > LITSCORE(NLIT(var))) return PLIT(var);
      if(LITSCORE(PLIT(var)) < LITSCORE(NLIT(var))) return NLIT(var);
      if(2&(random())) return NLIT(var); else return PLIT(var);
    }

  }
  return -1;
}

int NEWgetbest(satinstance sati) {
  int var;
  while(!heap_emptyp(sati)) {
    var = heap_taketop(sati);
    if(varunsetp(sati,var)) {
      switch(VARSTATUS(var) & 3) {	/* Check phase. */
      case 2: return NLIT(var);
      case 3: return PLIT(var);
      default:
	/* Otherwise use SCORE to decide polarity. Break ties randomly. */
	if(LITSCORE(PLIT(var)) > LITSCORE(NLIT(var))) return PLIT(var);
	if(LITSCORE(PLIT(var)) < LITSCORE(NLIT(var))) return NLIT(var);
	if(2&(random())) return NLIT(var); else return PLIT(var);
      }
    }
  }
  return -1;
}
#endif
#endif

/**************************************************************************/
/*******  Construction and extension of clause sets                 *******/
/**************************************************************************/

/*
As explained in Biere's PicoSAT implementation paper.
For each literal, the list of clauses in which it is watched,
is embedded in the clause data structure.
From each literal there is a pointer to the first clause in which the literal
is watched. The clause data includes a pointer to the next (and consequent)
clauses in which the literal occurs.

IMPLEMENTATION:
table WATCHEDIN[literal]
two additional pointers in each clause

When new clause C is added for a literal, WATCHEDIN[literal] := C,
and C has pointers to the old WATCHEDIN[literal]

When watched literal changes, one literal gets a new clause (added
in front of the list), and the other loses one clause (removed from
the middle of the list by changing the pointer in the preceding clause).

When clauses have been deleted (garbage collection), we must traverse
WATCHEDIN[literal] for all literals, to skip the deleted clauses.

*/

/* Add clause c to literal's watched clause list. */

void setwatch(satinstance sati,int lit,int *c,int index) {
  if(index==0) ASSIGN_WATCHA = LITWATCHES(lit);
  else ASSIGN_WATCHB = LITWATCHES(lit);
  LITWATCHES(lit) = c;
}

/* Create a clause */

int from,to,bias,currentlen,minvar,maxvar;
int *currentClause = NULL;
int maxlen = 0;

/* Insert an input clause (permanent) to the clause database. */

void addnewclause(satinstance sati,int len,clausetype ct) {
  ASSERT(len >= 2);

  if(currentClause == NULL) {
    maxlen = 10000;
    currentClause = (int *)malloc(sizeof(int) * maxlen);
  }

  currentlen = len;

  if(len > maxlen) {
    maxlen = len * 3/2;
    currentClause = (int *)realloc(currentClause,sizeof(int) * maxlen);
  }

  switch(ct) {
  case InitC: from=0; to=0; break;
  case FinalC: from=sati->nOfTPoints-1; to=from; break;
  case TransC: from=0; to=sati->nOfTPoints-2; break;
  }
  
  minvar = 1000000;
  maxvar = -1000000;
  bias = from*sati->nOfVarsPerTime;

}

void addliteral(satinstance sati,int c,int l) {
  int index = l+bias*2;

  currentClause[c] = index;

  minvar = min(VAR(index),minvar);
  maxvar = max(VAR(index),maxvar);
}

/* Finish the clause(s) and return the index of the last clause
   that was generated. */

void finishclause(satinstance sati) {
  int i,j,bias2,l,len;
  int *c;

  for(i=from;i<=to;i++) {

    len = currentlen;
    bias2 = i*sati->nOfVarsPerTime;

    if(maxvar-bias+bias2 >= sati->nOfVars) goto notthisclause;
    if(minvar-bias+bias2 < 0) goto notthisclause;

    c = allocpermclause(sati->id,len);

    ASSERT(c != 0);

    for(j=0;j<len;j++) {
      l = currentClause[j]-2*bias+2*bias2;
      c[j] = l;
      ASSERT(isliteral(sati,l));
#ifdef WEIGHTS
      increase_score(sati,l);
#endif
      if(j<2) setwatch(sati,l,c,j);
    }

    ASSERT(c[len] == -1);

  notthisclause: 1;
  }

}

/* Add a unit clause to the clause base. */

int add1clause(satinstance sati,int l,clausetype ct) {
  int from,to,i;
  int index;
  switch(ct) {
  case InitC: from=0; to=0; break;
  case FinalC: from=sati->nOfTPoints-1; to=from; break;
  case TransC: from=0; to=sati->nOfTPoints-2; break;
   default: assert(1==2); break;
  }

  for(i=from;i<=to;i++) {
    index = l+2*i*sati->nOfVarsPerTime;
    if(sati->initialunits+5 > sati->maxinitialunits) {
      sati->maxinitialunits = sati->maxinitialunits*2;
      sati->initialunittable = (int *)realloc(sati->initialunittable,sati->maxinitialunits*sizeof(int));
    }
    sati->initialunittable[sati->initialunits++] = index;
#ifdef WEIGHTS
    increase_score(sati,index);
#endif
  }
  return 0;
}

/* Add a 2-literal clause to the clause base.

   The input is clauses without an absolute time. The relative time limits to
   InitC: initial state (first time point) only
   FinalC: goal state (last time point) only
   TransC: transition relation, with current and next state

   The 2-literal clause representation used by the solver associates with
   each clause an array of literals that follow from it.
   As an intermediate stage, we here construct linked lists that will
   be later mapped to those arrays after all input clauses are there.

*/

void add2clauseRAW(satinstance sati,int l1,int l2,clausetype ct) {
  int t;
#ifdef WEIGHTS
  int i,i1,i2;
#endif

#ifdef asasASSERTS
  assert(l1 >= 0);
  assert(l1 < sati->nOfVarsPerTime*4);
  assert(l2 >= 0);
  assert(l2 < sati->nOfVarsPerTime*4);
#endif

  if(ct == TransC) {

    if(!noT2clauses) {

      int l1time = VAR(l1) / sati->nOfVarsPerTime;
      int l2time = VAR(l2) / sati->nOfVarsPerTime;
      int nl1 = l1 - 2*l1time*sati->nOfVarsPerTime;
      int nl2 = l2 - 2*l2time*sati->nOfVarsPerTime;
      int tdiff = l2time-l1time;
      int bias = 2*tdiff*sati->nOfVarsPerTime;

      //      printf("ADDING 2-LIT "); printTlit(sati,nl1); printf(" ");
      //      printTlit(sati,nl2); printf(" with tdiff %i\n",tdiff);

      sati->l2its[NEG(nl1)] = nintcons(nl2+bias,sati->l2its[NEG(nl1)]);
      sati->l2its[NEG(nl2)] = nintcons(nl1-bias,sati->l2its[NEG(nl2)]);

    }

#ifdef WEIGHTS
    /* Scores of the 2-literal clauses for all literals */
    for(i=0;i<sati->nOfTPoints;i++) {
      
      i1 = l1+2*i*sati->nOfVarsPerTime;
      i2 = l2+2*i*sati->nOfVarsPerTime;

      if((i1 >= 0)
	 && (i2 >= 0)
	 && (i1 < 2*sati->nOfVars)
	 && (i2 < 2*sati->nOfVars)) {
	increase_score(sati,i1);
	increase_score(sati,i2);
      }
    }
#endif
    
  } else {
    if(ct == InitC) t = 0;		/* First time point */
    else t=sati->nOfTPoints-1;		/* Last time point */

    // These are not needed if the increase_score below is their only use!!!!
    l1 += 2*t*sati->nOfVarsPerTime;
    l2 += 2*t*sati->nOfVarsPerTime;

#ifdef WEIGHTS
      increase_score(sati,l1);
      increase_score(sati,l2);
#endif

      //    LIT2LITS(NEG(l1)) = nintcons(l2,LIT2LITS(NEG(l1)));
      //    LIT2LITS(NEG(l2)) = nintcons(l1,LIT2LITS(NEG(l2)));
  }
}

void add2clause(satinstance sati,int l1,int l2,clausetype ct) {
  if(ct == TransC) add2clauseRAW(sati,l1,l2,ct);
  else { /* non-recurring 2-lit clauses handled as long clauses. */
    //    printf("@");
    addnewclause(sati,2,ct);
    addliteral(sati,0,l1);
    addliteral(sati,1,l2);
    finishclause(sati);
  }
}

#ifdef COSTS
void addtimedvarcost(satinstance sati,int v,int cost) {
  sati->costs[v] = cost;
}
#endif

int nintlistlen(nintlist *ls) {
  int c;
  c = 0;
  while(ls != NULL) {
    c += 1;
    ls = ls->tl;
  }
  return c;
}

float megab(int i) {
  return ((float)i)/(1024.0*1024.0);
}

#ifdef DEBUG
void showinstancesize(satinstance sati) {
  int cnt;
  int i;
  int longclauses;
  nintlist *ls;

  cnt = 0;

  for(i=0;i<2*sati->nOfVarsPerTime;i++) cnt += nintlistlen(sati->l2its[i]);

  longclauses = 0;
  for(i=0;i<2*sati->nOfVars;i++) {
    ls = LITWATCHES(i);
    while(ls != NULL) {
      longclauses += ((clauselen((int *)(ls->hd))+5)*4);
      ls = ls->tl;
    }
  }
  printf("===========================\n");
  printf("l2its is %.1f MB\n",megab((sati->nOfSVars+2*cnt)*4));
  printf("al2its is %.1f MB\n",megab((sati->nOfSVars+cnt)*4));
  printf("lits is %.1f MB\n",megab(3*4*2*sati->nOfVars+longclauses));
  printf("vars is %.1f MB\n",megab(4*4*sati->nOfVars));
  printf("unitstack is %.1f MB\n",megab(4*sati->nOfVars));
#ifdef VSIDS
  printf("scoreheap is %.1f MB\n",megab(sati->nOfVars*8));
#endif
#ifdef UCC
  printf("UCC is %.1f MB\n",megab(10000*4));
#endif
  printf("===========================\n");
}
#endif

/* Run this when all binary clauses are known.
 Main function: translated the binary clause linked lists to arrays for
 faster access.
*/

/* An ordering on lits, based on the variable indices and ignoring polarity */
int litCmp(int *a,int *b) {
  if(((*a) >> 1) < ((*b) >> 1)) return 1;
  else return 0;
}

int litCmp2(int *a,int *b) {
  if(((*a) >> 1) > ((*b) >> 1)) return 1;
  else return 0;
}


void instancecomplete(satinstance sati) {
  int i,c,j;
  nintlist *ls;

  sati->complete = 1;

  /* Update the heap. */

#ifdef VSIDS
  for(i=0;i<sati->nOfVars;i++) heap_increment_by(sati,HINDEX(i),LITSCORE(PLIT(i))+LITSCORE(NLIT(i)));
#endif

  adjustheap = 1;

#ifdef VSIDS
#ifdef ASSERTS
  checkheapconsistency(sati);
#endif
#endif
  if(!noT2clauses) {	/* First SAT instance: map linked lists to arrays. */

    int arraysize,*a2litarray,*ptr;

    /* Put the binary clauses' linked lists into arrays. Create one huge
     array, and then point into the middle. */

    arraysize = 1;

    for(i=0;i<sati->nOfVarsPerTime*2;i++) {
      arraysize = cachelineboundaryi(arraysize);
      arraysize += (1+nintlistlen(sati->l2its[i]));
    }

    arraysize += (CACHELINESIZEi-1);

    a2litarray = (int *)ownalloc(713,sizeof(int) * arraysize);
    report_malloc("a2litarray",sizeof(int) * arraysize);

    a2litarray[0] = 0; /* There is only one copy of the empty array, here. */

    ptr = a2litarray+1;

    sati->al2its = (int **)ownalloc(714,sizeof(int *) * sati->nOfVarsPerTime * 2);

    for(i=0;i<sati->nOfVarsPerTime*2;i++) {
      c = nintlistlen(sati->l2its[i]);
      if(c == 0) sati->al2its[i] = a2litarray;
      else {
	//	printf("{%u,",(PTRINT)ptr);
	ptr = cachelineboundary((PTRINT)ptr);
	//	printf("%u}",(PTRINT)ptr);
	sati->al2its[i] = ptr;
	ptr[0] = c;	/* First element of the array is the # of elements. */
	ls = sati->l2its[i];
	for(j=0;j<c;j++) {
	  ptr[j+1] = ls->hd;
	  ls = ls->tl;
	}
	/* Sort the array to reduce cache misses. */
	qsort(sati->al2its[i]+1,c,sizeof(int),litCmp2);
	ptr += (c+1);
#define noSHOW
#ifdef SHOW
	printTlit(sati,i);
	printf(": ");
	for(j=0;j<c;j++) {
	  printf(" %i:",(sati->al2its[i][j+1]+2*sati->nOfVarsPerTime) % sati->nOfVarsPerTime);
	  printTlit(sati,sati->al2its[i][j+1]+2*sati->nOfVarsPerTime);
	}
	printf("\n");
#endif
      }
    }
    /* Completed the move to arrays. */
  }

}


/**************************************************************************/
/*******  Functions for unit propagation                            *******/
/**************************************************************************/

/* Set literals in unitstack true and unit propagate.

The reason parameter denotes the cause of the literal being set.
-1 means that the literal is a decision literal
-2 means that the literal is one of the unit clauses in the input CNF
if the 2 lsbs are 0, the reason is a pointer to a clause where
   the literal was a unit (HERE WE ASSUME THAT ADDRESSES OF CLAUSES
   ALWAYS HAVE THEIR 2 LSBs 0.)
otherwise the reason is (l << 1)|1 for another literal l

If contradiction is reached, return the index of a falsified
clause. */


inline int addtoqueue(satinstance sati,int l,PTRINT reason,int level) {

  if((litunsetp(sati,l))) {	/* Literal has no value yet. */

    sati->unitstack[++(sati->endunitstack)] = l;    /* Push it into the stack. */
    litsettrue(sati,l);	/* Assign */

#ifdef VSIDS
    VARSTATUS(VAR(l)) = 2|(VALUE(l)); /* Record phase */
#endif

    LITREASON(l) = reason;
    LITDLEVEL(l) = level;

#ifdef HARDDEBUG
    printf("Inferred "); printTlit(sati,l); printf(".\n");
    printf("  REASON: "); fflush(stdout);
    switch(reason) {
    case REASON_DECISION: printf("DECISION\n"); break;
    case REASON_INPUT: printf("INPUT\n"); break;
    default:
      if((reason&1) == 0) {
	printf("Clause %i of length %i:",reason,clauselen((int *)reason));
	printclause(sati,reason);
	printf("\n");
      } else {
	printTlit(sati,reason >> 1); printf("\n");
      }
      break;
    }
#endif

    ASSERT(sati->endunitstack < sati->nOfVars);

#ifdef COSTS
    if((l&1)==0) { /* Variable is true: observe cost. */
      sati->currentcost = sati->currentcost + sati->costs[untimevar(sati,VAR(l))];
#ifdef HARDDEBUG
      printTlit(sati,l);
      printf("Adding %i to currentcost.\n",sati->costs[untimevar(sati,VAR(l))]);
      printf("Currentcost = %i.\n",sati->currentcost);
#endif
    }
#endif

    return 0;
  }

  /* Variable had a value already. */

  if(unlikely(litfalsep(sati,l))) return 1; /* Literal is false. */

  return 0; /* Literal was true. */
}

/* Same as addtoqueue, except that we KNOW that the variable is unassigned. */

void simpleaddtoqueue(satinstance sati,int l,PTRINT reason,int level) {

  litsettrue(sati,l);	/* Assign */
#ifdef VSIDS
  VARSTATUS(VAR(l)) = 2|(VALUE(l)); /* Record phase */
#endif
  LITREASON(l) = reason;
  LITDLEVEL(l) = level;

  sati->unitstack[++(sati->endunitstack)] = l;    /* Push it into the stack. */

  ASSERT(sati->endunitstack < sati->nOfVars);

#ifdef COSTS
    if((l&1)==0) { /* Variable is true: observe cost. */
      sati->currentcost += sati->costs[untimevar(VAR(l))];
#ifdef HARDDEBUG
      printTlit(sati,l);
      printf("Adding %i to currentcost for %i/%i.\n",sati->costs[untimevar(sati,VAR(l))],VAR(l),untimevar(sat,VAR(l)));
      printf("Currentcost = %i.\n",sati->currentcost);
#endif
    }
#endif
}


/* Propagation with 2-literal clauses. */

/* These variables are the interface from propaga{2lit,long} to learn(). */

inline int propagate2lit(satinstance sati,int lit,int level) {
  int glit,bias2;
  PTRINT reason;
  int j;
  int nofv2;
  int *AAA;

  reason = (lit << 1)|1;	/* Reason for the literals to be set. */

  /* Propagate the 2-literal clauses for all time points. */

  /* Compact binary clause representation */
  glit = lit%(2*sati->nOfVarsPerTime);
  bias2 = lit-glit;

  ASSERT(glit >= 0);
  ASSERT(glit < sati->nOfVarsPerTime*2);

  AAA = sati->al2its[glit];

  nofv2 = 2*sati->nOfVars;

  for(j=1;j<=AAA[0];j++) {
    if(likely(AAA[j]+bias2 < nofv2)
       && likely(AAA[j]+bias2 >= 0)
       && unlikely(addtoqueue(sati,AAA[j]+bias2,reason,level))) {
      sati->conflicttype2lit = 1;
      sati->conflictl1 = NEG(AAA[j]+bias2);
      sati->conflictl2 = lit;
      return 1;
    }
  }

  return 0;
}

/* Propagation with long clauses (> 2 literals):
   Go through clauses in which literal is watched.
   If only one unassigned literal left, put into queue.
*/

inline int propagatelong(satinstance sati,int l,int level) {
  int *c,*c2;
  int *nextclause;
  PTRINT *prev;
  int tmp;
  PTRINT *ptmp;

  //  printf("#");

  prev = &(LITWATCHES(NEG(l)));
  nextclause = LITWATCHES(NEG(l));	/* Clauses where -l is watched */

  while(nextclause != NULL) { /* Visit clauses where -l is watched. */
    c = nextclause;

    /* The watched literals are always the first two in a clause. */
    /* Make the current literal the first in the clause. */

    if(c[0] != NEG(l)) {
      tmp = c[0]; c[0] = c[1]; c[1] = tmp;
      ptmp = ACCESS_WATCHA; ASSIGN_WATCHA = ACCESS_WATCHB; ASSIGN_WATCHB = ptmp;
    }

    //    __builtin_prefetch(ACCESS_WATCHA);

    /* If the second watched literal is true, don't do anything. */
    
    if(littruep(sati,c[1])) {
      prev = ADDRESS_WATCHA;
      nextclause = ACCESS_WATCHA;
      continue;
    }

    ASSERT(isliteral(sati,c[0]));
    ASSERT(isliteral(sati,c[1]));

    c2 = c+2;

    /* Find a non-false literal. */

    while(*c2 != -1) {
      ASSERT(isliteral(sati,*c2));
      if(!litfalsep(sati,*c2)) goto nonfalse;
      c2 += 1;
    }

    /* 2nd watched literal is a new unit clause. */

    //    updateactivity(c,sati->conflicts);
    c[PREFIX_ACTIVITY] = sati->conflicts;

    if(addtoqueue(sati,c[1],(PTRINT)c,level)) {
      //      printf("C");
      sati->conflicttype2lit = 0;
      sati->conflictclause = c;
      return 1;
      /* You might exit here before fixing all the clauses with
	 the literal watched. Is this correct? */
    } else {
      //      printf("U%i",*(c+1));
    }
    prev = ADDRESS_WATCHA;
    nextclause = ACCESS_WATCHA;
    continue;

  nonfalse:

    /* Swap the old watched literal (at *c) and the new (at *c2). */

    tmp = *c2; *c2 = *c; *c = tmp;

    /* Remove the clause from the old literal's watched clause list. */

    *prev = ACCESS_WATCHA;

    nextclause = ACCESS_WATCHA; /* Go to the next clause. */

    /* Add the clause to the new literal's watched clause list. */

    ASSIGN_WATCHA = LITWATCHES(*c);
    LITWATCHES(*c) = c;

  }
  return 0;
}

void setUPstacktop(satinstance sati,int top) {
  sati->endunitstack = top;
  sati->startunitstack = top+1;
}


/* Main function for propagation */

int propagate(satinstance sati) {
  int l;
  int startlong;

  startlong = sati->startunitstack;
  while(startlong <= sati->endunitstack) {

    while(sati->startunitstack <= sati->endunitstack) {
      l = sati->unitstack[sati->startunitstack++];

      /* Propagate with 2-literal clauses. */
      if(propagate2lit(sati,l,sati->dlevel)) return 1;
    }

    /* Propagate with long clauses. */
    
    l = sati->unitstack[startlong++];

    if(propagatelong(sati,l,sati->dlevel)) return 1;
    
  }

  return 0; /* No contradiction */
}

/*************************************************************************/
/** Computation of learned clauses                                      **/
/*************************************************************************/

#ifdef UCC
/* 
   The literals that have been added as unit clauses.
   They have to be remembered until decision level 0 is visited again,
   because their assignments will be undone for example during
   the standard CDCL main loop run on levels > 0.
 */

void addUCC(satinstance sati,int l) {
  sati->UCC[sati->NofUCClauses++] = l;
  ASSERT(sati->NofUCClauses < MAXUCC);

#ifdef HARDDEBUG
  printf("New unit clause "); printTlit(sati,l); printf("\n");
  printf("lvl: %i start: %i end: %i\n",-999,sati->endunitstack,sati->startunitstack);
#endif
}

int returnUCC(satinstance sati) {
  int i;
  for(i=0;i<sati->NofUCClauses;i++) {
    // The return 1 below should never happen!!!!!
    if(addtoqueue(sati,sati->UCC[i],REASON_INPUT,0) || propagate(sati)) return 1;
  }
  if(sati->dlevel == 0) sati->NofUCClauses = 0;

#ifdef HARDDEBUG
  printf("lvl: %i start: %i end: %i\n",sati->dlevel,sati->endunitstack,sati->startunitstack);
#endif

  return 0;
}
#endif UCC


/* Compute a 1-UIP or Last-UIP clause.

1. Go through the literals in the current clause.
2. If literal for non-decision level, store it.
3. If non-decision literal for the top level, traverse its reasons.
4. If the reason is -2, ignore the literal.

*/

satinstance dlcsati;
int dlevelCmp(int *l1,int *l2) {
#ifdef REASONDLEVEL
  if(dlcsati->variablerd[VAR(*l1)].dlevel > dlcsati->variablerd[VAR(*l2)].dlevel) {
#else
  if(dlcsati->variabledlevel[VAR(*l1)] > dlcsati->variabledlevel[VAR(*l2)]) {
#endif
    return 1;
  }
  return 0;
}

#define noFIRSTUIP 1

#ifdef FUIP
#include "learn1UIP.c"
#else
//#include "learn1.c"
#include "learn2.c"
//#include "learn3.c"
#endif

/**************************************************************************/
/*******       The Conflict-Driven Clause Learning algorithm      *******/
/**************************************************************************/


int chooseliteral(satinstance sati) {
  switch(PLANheuristic) {
  case 0: break;
  default:
    return do_cpath_heuristic(sati);
  }

  /* If planning heuristic was not applicable, use the SAT heuristic. */

#ifdef VSIDS
  /* Choose unassigned literal with highest score. */
  return getbest(sati);
#else
  fprintf(stderr,"No decision literal chosen.\n");
  exit(1);
#endif
}

#ifdef HARDDEBUG
void showstack(satinstance sati) {
  int i,l;
  printf("============================\n");
  for(i=sati->endunitstack;i>max(0,sati->endunitstack-20);i--) {
    l = sati->unitstack[i];
    printf("%2i: %2i ",i,LITDLEVEL(l));
    printTlit(sati,l);
    printf("\n");
  }
  printf("----------------------------\n");
  printf("levels:");
  for(i=max(0,sati->dlevel-8);i<=sati->dlevel;i++) {
    printf(" %i@%i",i,sati->declevels[i-1]);
  }
  printf("\n");
  printf("============================\n");
}
#endif

void emptystack(satinstance sati) {
  int i;
  for(i=0;i<=sati->endunitstack;i++)
    litunset(sati,sati->unitstack[i]);
  
  setUPstacktop(sati,-1);
}

/* Make btlevel the new top decision level by
   - undoing all assignments on levels higher than btlevel
   - setting current dlevel to btlevel
*/

void undo_assignments_until_level(satinstance sati,int btlevel) {
  int i,l;
  //  printf("FROM %i TO %i AT BTLEVEL %i\n",sati->declevels[btlevel],sati->endunitstack,btlevel);

  for(i=sati->declevels[btlevel];i<=sati->endunitstack;i++) {
    l = sati->unitstack[i];

    litunset(sati,l);
#ifdef HARDDEBUG
    printf("UNSET "); printTlit(sati,l); printf("\n");
#endif

#ifdef VSIDS
    if(HINDEX(VAR(l)) == -1) heap_insert(sati,VAR(l),scoreof(sati,VAR(l)));
#endif
  }
#ifdef COSTS
  sati->currentcost = sati->declevelscost[btlevel];
#ifdef HARDDEBUG
  printf("Reverted currentcost = %i.\n",sati->currentcost);
#endif
#endif
  sati->dlevel = btlevel;
  setUPstacktop(sati,sati->declevels[btlevel]-1);
}

void undo_assignments_until_level_NOHEAP(satinstance sati,int btlevel) {

  int i,l;
  //  printf("FROM %i TO %i AT BTLEVEL %i\n",sati->declevels[btlevel],sati->endunitstack,btlevel);

  for(i=sati->declevels[btlevel];i<=sati->endunitstack;i++) {
    l = sati->unitstack[i];

    litunset(sati,l);
    //    printf("UNSET "); printTlit(sati,l); printf("\n");

  }
#ifdef COSTS
  sati->currentcost = sati->declevelscost[btlevel];
#ifdef HARDDEBUG
  printf("Reverted currentcost = %i.\n",sati->currentcost);
#endif
#endif
      
  setUPstacktop(sati,sati->declevels[btlevel]-1);
}

/* The standard CDCL Conflict Driven Clause Learning algorithm */

int solve0(satinstance sati,int conflictstogo,int restart) {
  int l,p,btlevel;
  int q;
  PTRINT CCreason;

  if(sati->notcalledbefore) {
    sati->notcalledbefore = 0;
    for(p=0;p<sati->initialunits;p++) {
      if(addtoqueue(sati,sati->initialunittable[p],REASON_INPUT,0)) goto UNSAT;
    }

    if(propagate(sati)) goto UNSAT;
#ifdef UCC
    sati->NofUCClauses = 0;
#endif
    setUPstacktop(sati,-1); /* Drop the input unit clauses from the stack. */

    sati->dlevel = 0;

    if(sati->pheuristic >= 1) sati->heuristic_mode = 0;
  }

  q = 0;

  do {

    if(q || propagate(sati)) {	/* Got a conflict? */

      if(sati->dlevel == 0) goto UNSAT;

#ifdef WEIGHTS
      decay_score(sati);
#endif

      sati->heuristic_mode = 0;
      sati->conflicts += 1;
      conflictstogo -= 1;

      learn(sati,sati->dlevel,&p,&CCreason,&btlevel);
      /* When exiting learn(), CCreason points to the newly learned clause,
	 and btlevel is the decision level of the second highest literal
	 in the clause. */

      ASSERT(btlevel >= 0);
      ASSERT(btlevel < sati->dlevel);
      ASSERT(LITDLEVEL(p) == sati->dlevel);

#ifdef HARDDEBUG
      printf("Conflict level %i literal ",sati->dlevel); printTlit(sati,p);
      printf(", next level is %i.\n",btlevel);
      showstack(sati);
#endif

      undo_assignments_until_level(sati,btlevel);
      ASSERT(litunsetp(sati,p));

#ifdef UCC
      if(returnUCC(sati)) goto UNSAT;
#endif

#ifdef HARDDEBUG
      printf("Setting "); printTlit(sati,p); printf(" true (flipping).\n"); fflush(stdout);
#endif

      /* CCreason refers to the conflict clause. */

      q = addtoqueue(sati,p,CCreason,sati->dlevel);
      ASSERT(littruep(sati,p));

      // IF THE NEXT LINE IS MISSING, LEARNING A CLAUSE RIGHT BEFORE
      // A RESTART SOMTIMES LEADS TO UNASSIGNING DEC LEVEL 0 LITERAL p
      // AND IF IT IS THERE, heuristic2.c SOMTIMES CRASHES BECAUSE NO
      // BEST VARIABLE IS FOUND. REASON UNCLEAR!!!!!!!!
      //      sati->declevels[sati->dlevel] = sati->endunitstack+1;

    } else {	/* Extend the assignment. */

      if(conflictstogo <= 0) {
	sati->declevels[sati->dlevel] = sati->endunitstack+1;
	break;
      }

      l = chooseliteral(sati);

      if(l == -1) goto SAT;	/* All variables assigned already. */

      ASSERT(VAR(l) < sati->nOfVars);
      ASSERT(litunsetp(sati,l));

#ifdef DEBUG
      printf("DECISION %i: ",sati->dlevel);
      printTlit(sati,l);
      printf("\n");
#endif

      sati->declevels[sati->dlevel] = sati->endunitstack+1;
#ifdef COSTS
      sati->declevelscost[sati->dlevel] = sati->currentcost;
#endif
      sati->dlevel += 1;
      sati->decisions += 1;

      simpleaddtoqueue(sati,l,REASON_DECISION,sati->dlevel);
      q=0;
    }

    //  } while(conflictstogo);
  } while(1==1);

  /* Satisfiability status not determined. */

  if(restart) {

    // PROBLEM: if decision level 0 learned clause is added right before
    // a restart, it will never get propagated. KESKEN

#ifdef HARDDEBUG
    printf("DOING A RESTART\n");
#endif

    undo_assignments_until_level(sati,0);

    //    if(propagate(sati)) goto UNSAT;
#ifdef UCC
    if(returnUCC(sati)) goto UNSAT;
#endif
    setUPstacktop(sati,-1);
  }
  
  return -1;

 UNSAT:
  sati->value = 0;
  return 0;
 SAT:
  printf("SAT (%i decisions %i conflicts)\n",sati->decisions,sati->conflicts);
#ifdef COSTS
  printf("FINAL COST %i.\n",sati->currentcost);
  sati->costbound = sati->currentcost;
#endif
  sati->value = 1;
  return 1;
}

int solve(satinstance sati) {
  int result;
  int interval;
  interval = 32;
  do {
    result = solve0(sati,interval,1);
    interval = interval + 5;
  } while(result == -1);
  return result;
}


void freeinstance(satinstance sati) {
  /* sati->lits is needed when garbage collecting the first time after
     the instance has become useless. */
  //  if(sati->lits) { free(sati->lits); sati->lits = NULL; }

  if(sati->variableval) { free(sati->variableval); sati->variableval = NULL; }
#ifdef VSIDS
  if(sati->variablestatus) { free(sati->variablestatus); sati->variablestatus = NULL; }
#endif
#ifdef REASONDLEVEL
  if(sati->variablerd) { free(sati->variablerd); sati->variablerd = NULL; }
#else
  if(sati->variablereason) { free(sati->variablereason); sati->variablereason = NULL; }
  if(sati->variabledlevel) { free(sati->variabledlevel); sati->variabledlevel = NULL; }
#endif
  if(sati->initialunittable) { free(sati->initialunittable); sati->initialunittable = NULL; }
  if(sati->unitstack) { free(sati->unitstack); sati->unitstack = NULL; }

#ifdef VSIDS
  if(sati->hindex) { free(sati->hindex); sati->hindex = NULL; }
  if(sati->scoreheap) { freeheap(sati->scoreheap); sati->scoreheap = NULL; }
#endif
}


void showvaluation(satinstance sati) {
  int i;
  printf("Valuation:");
  for(i=0;i<sati->nOfVars;i++)
    if(vartruep(sati,i)) {
      printf(" ");
      printTlit(sati,PLIT(i));
    }
  printf("\n");
}


/*************************************************************************/
/** Heap for keeping track of highest score variables                   **/
/*************************************************************************/

#ifdef VSIDS

/* Calculate the index of the parent of an index. */

inline int parent(int i) {
  return (i-1) >> 1;
}

/* Calculate the index of the 1st child of an index. */

inline int child1(int i) {
  return i*2+1;
}

/* Calculate the index of the 2nd child of an index. */

inline int child2(int i) {
  return i*2+2;
}

/* Test whether the heap is empty. */

int heap_emptyp(satinstance sati) {
  return (sati->scoreheap->els == 0);
}

/* Return true if index is a leaf. */

int leafp(heap h,int index) {
  return (child1(index) >= h->els);
}

heap heap_create(int elements) {
  heap h;
  h = (heap)ownalloc(716,sizeof(struct _heap));
  h->els = 0;
  h->maxels = elements;
  h->array = (pair *)ownalloc(717,sizeof(pair) * elements);
  return h;
}

void freeheap(heap h) {
  free(h->array);
  free(h);
}

/* After moving a non-top element to the top, restore the heap property. */

inline int heap_property_down(satinstance sati,int index) {
  int c1index,c2index;
  int swap;
  int key,val;
  heap h;

  h = sati->scoreheap;

  ASSERT(index < h->els && index >= 0);

  key = h->array[index].k;
  val = h->array[index].v;

  c1index = child1(index);
  c2index = child2(index);

  /* Should one child be higher than the parent? */

  while(((c1index < h->els && h->array[c1index].v > val) || (c2index < h->els && h->array[c2index].v > val))) {	/* Not a leaf */

    if(c2index < h->els) {
      if(h->array[c1index].v > h->array[c2index].v) swap = c1index;
      else swap = c2index;
    } else swap = c1index;

    ASSERT(index < h->els && index >= 0);

    /* Move child to the parent's node. */

    h->array[index].k = h->array[swap].k;
    h->array[index].v = h->array[swap].v;

    HINDEX(h->array[index].k) = index;

    /* Continue with the child's node. */

    index = swap;

    c1index = child1(index);
    c2index = child2(index);

  }

  /* Leave the node here when low enough. */

  h->array[index].k = key;
  h->array[index].v = val;

  HINDEX(h->array[index].k) = index;

  return index;
}

void printheap(satinstance sati) {
  heap h = sati->scoreheap;
  int node;
  for(node=0;node<h->els;node++) {
    printf("(%i,%i) ",h->array[node].k,h->array[node].v);
  }
  printf("\n");
}

/* Get the top element of the heap (with the highest value). */

int heap_taketop(satinstance sati) {
  int key;
  heap h = sati->scoreheap;

  ASSERT(h->els);

  key = h->array[0].k;

  if(h->els > 1) { /* Move last element to top and then push down. */

    h->array[0].k = h->array[h->els-1].k;
    h->array[0].v = h->array[h->els-1].v;

    HINDEX(h->array[0].k) = 0;

  }
  HINDEX(key) = -1;

  h->els -= 1;

  if(h->els) heap_property_down(sati,0);

  return key;
}

/* Move a new element to an appropriate place in the heap. */

void heap_property_up(satinstance sati,int index) {
  int pindex;
  int key,val;
  heap h = sati->scoreheap;

  ASSERT(index >= 0 && index < h->els);

  key = h->array[index].k;
  val = h->array[index].v;

  pindex = parent(index);
  while(index > 0 && val > h->array[pindex].v) {
    /* Move parent down. */
    h->array[index].k = h->array[pindex].k;
    h->array[index].v = h->array[pindex].v;

    HINDEX(h->array[index].k) = index;

    /* Continue with the parent. */
    index = pindex;
    pindex = parent(index);
  }
  /* When all parents are OK, leave the new element here. */
  h->array[index].k = key;
  h->array[index].v = val;

  HINDEX(h->array[index].k) = index;
}

/* Add new element to the heap. */

void heap_insert(satinstance sati,int key,int val) {
  heap h = sati->scoreheap;

  /* You could speed this a bit up by not writing key and val to memory yet. */
  /* But this would be for heap_insert only. */
  h->array[h->els].k = key;
  h->array[h->els].v = val;
  h->els += 1;
  ASSERT(h->els <= h->maxels);
  heap_property_up(sati,h->els-1);
}

/* Increment the value of a heap element. */

void heap_increment(satinstance sati,int index) {
  heap h = sati->scoreheap;

  h->array[index].v += 1;
  heap_property_up(sati,index);
}

void heap_increment_by(satinstance sati,int index,int n) {
  heap h = sati->scoreheap;

  h->array[index].v += n;
  heap_property_up(sati,index);
}

/* Perform the decay operation, i.e. halve the value of each element. */

void heap_decay(satinstance sati) {
  int i;
  heap h = sati->scoreheap;
  for(i=0;i<h->els;i++) h->array[i].v = (h->array[i].v) >> 1;
}

/* Delete an arbitrary element from the heap. */

void heap_delete(satinstance sati,int index) {
  int loc;
  heap h = sati->scoreheap;

  ASSERT((h->els > index) && (index >= 0));

  h->array[index].v = -1000;
  loc = heap_property_down(sati,index);

  ASSERT(leafp(h,loc));

  h->array[loc].k = h->array[h->els-1].k;
  h->array[loc].v = h->array[h->els-1].v;

  HINDEX(h->array[loc].k) = loc;

  h->els -= 1;

  if(loc < h->els) heap_property_up(sati,loc);
}
#ifdef ASSERTS
void checkheapproperty(heap h) {
  int i;
  for(i=1;i<h->els;i++) {
    assert(h->array[parent(i)].v >= h->array[i].v);
  }
}

void checkheapconsistency(satinstance sati) {
  int i;
  heap h = sati->scoreheap;

  for(i=0;i<h->els;i++) {
    assert(HINDEX(h->array[i].k) == i);
  }

  checkheapproperty(h);
}
#endif
#endif

/**************************** INCLUDED SOURCE FILES ***********************/
#include "shortcuts.c"
/**************************************************************************/
