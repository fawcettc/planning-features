
/* 2012 (C) Jussi Rintanen, jrintanen.jr@gmail.com */

#define noASSERTS

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "main.h"
#include "asyntax.h"
#include "tables.h"
#include "intsets.h"
#include "ordintsets.h"
#include "operators.h"
#include "dimacs.h"
#include "invariants.h"
#include "scc.h"

#include "interface.h"
#include "clausedb.h"

#include "translate2sat.h"

#ifdef CP3
#include "libcp3c.h"
#endif

#define noDEBUG

#define OPtag	0x10000000
#define VARtag	0x20000000
#define AUXtag	0x30000000
#define NEGtag	0x40000000
#define NEXTtag	0x80000000
#define TYPEtag	0x30000000
#define INDEX	0x0FFFFFFF

/* Tags for op, var, aux encoding */

#define OP(n) ((n)|OPtag)
#define SVAR(n) ((n)|VARtag)
#define AUX(n) ((n)|AUXtag)
#define NEXT(n) ((n)|NEXTtag)

#define fmaOP(n) (Fatom(OP(n)))
#define fmaVAR(n) (Fatom(SVAR(n)))
#define fmaAUX(n) (Fatom(AUX(n)))

#define VARINDEX(v) ((v)&INDEX)
#define VARNEXT(v) ((v)&NEXTtag)
#define VARTYPE(v) ((v)&TYPEtag)

/* Tags for DIMACs clause encoding */

#define INITtag	0x20000000
#define GOALtag	0x40000000
#define TRtag	0x60000000
#define TIMEtags	0x60000000
#define LENBITS	0x0FFFFFFF

void outputDIMACS();
satinstance outputNSAT(int,int,int);


int nOfAux;
int nOfClauses;
int nOfTClauses;

int allocAUX(int n) {
  int temp;
  temp = nOfAux;
  nOfAux += n;
  return temp;
}

/* Functions for handling formula sets and translating them into CNF. */

typedef enum { inittime, goaltime, transition } formulaclass;

typedef struct {
  formulaclass cl;
  fma *f;
} timedfma;

int nOfFmas;
int maxFmas;

timedfma *fmas;

void initformuladb() {
  nOfAux = 0;
  nOfFmas = 0;
  maxFmas = 500000;
  fmas = (timedfma *)statmalloc(500,maxFmas * sizeof(timedfma));
}

void addformula(formulaclass c,fma *f) {
  nOfFmas += 1;

  /* Table size exceeded */
  if(nOfFmas > maxFmas) {
    maxFmas += 1000000;
    fmas = (timedfma *)realloc(fmas,maxFmas * sizeof(timedfma));
  }

  fmas[nOfFmas-1].cl = c;
  fmas[nOfFmas-1].f = f;

  //  printFfma(f);
}

/* Make a copy of a formula with each state variable tagged with
   the StateVar tag (to distinguish it from the action and auxiliary variables.
*/

fma *makeVARfma(fma *f) {
  fmalist *l;
  fma *nf;
  nf = (fma *)statmalloc(501,sizeof(fma));
  nf->t = f->t;
  switch(f->t) {
  case patom:
  case natom:
    nf->a = SVAR(f->a); break;
  case disj:
  case conj:
    nf->juncts = NULL;
    l = f->juncts;
    while(l != NULL) {
      nf->juncts = fmacons(makeVARfma(l->hd),nf->juncts);
      l = l->tl;
    }
    break;
  default: 1;
  }
  return nf;
}

/* Make a copy of a formula with the NEXT version of each state variable. */

fma *fmaNEXT(fma *f) {
  fmalist *l;
  switch(f->t) {
  case patom:
  case natom:
    f->a = NEXT(f->a); break;
  case disj:
  case conj:
    l = f->juncts;
    while(l != NULL) {
      fmaNEXT(l->hd);
      l = l->tl;
    }
    break;
  default: 1;
  }
  return f;
}


/* How many bits are needed for expressing numbers from 1 to n? */

int bitsneeded(int n) {
  int cnt;
  cnt = 0;
  while(n > 0) {
    n = n >> 1;
    cnt += 1;
  }
  return cnt;
}

/* Return a conjunction of literals, with the positives in the first list
   and the negatives in the second. */

//fma *effectsof(intlist *pos,intlist *neg) {
//  fmalist *fs;
//
//  fs = NULL;
//
//  while(pos != NULL) {
//    fs = fmacons(fmaVAR(NEXT(pos->hd)),fs);
//    pos = pos->tl;
//  }
//
//  while(neg != NULL) {
//    fs = fmacons(Fneg(fmaVAR(NEXT(neg->hd))),fs);
//    neg = neg->tl;
//  }
//  return Fconj(fs);
//}

fma *effectsofL(int *lits) {
  fmalist *fs;

  fs = NULL;

  while(*lits != -1) {
    if((*lits)&1) fs = fmacons(Fneg(fmaVAR(NEXT(feVAR(*lits)))),fs);
    else fs = fmacons(fmaVAR(NEXT(feVAR(*lits))),fs);
    lits = lits + 1;
  }

  return Fconj(fs);
}

/* Add a new action/effect to the data structure that enumerates for
   each literal all the possible ways of making it true. */

void storeinCEsL(int *lits,int var,fma *precon) {
  CEstruct *s;
  int i;
  for(;*lits != -1;lits = lits + 1) {
    s = (CEstruct *)statmalloc(503,sizeof(CEstruct));
#ifdef ASSERTS
    assert(s != NULL);
#endif
    i = *lits;
    s->next = CEs[i];
    s->var = var;
    s->condition = precon;
    s->disjunctive = disjunctivep(precon);
    CEs[i] = s;
  }
}

/* Count the number of ways a literal can be made true. */

int nOfCEs(CEstruct *ptr) {
  int n;
  n = 0;
  while(ptr != NULL) {
    n = n + 1;
    ptr = ptr->next;
  }
  return n;
}

/* Create a compact data structure with references to effect variables
   and the associated (pre)conditions. This is used when the flagCEvariables
   is true, and it is used for the computation of the heuristic.
*/

void compactCEs() {
  int i,j;
  int len;
  CEstruct *ptr;
  for(i=0;i<nOfAtoms*2;i++) {
    len = nOfCEs(CEs[i]);
    cCEs[i] = (compactCEstruct *)statmalloc(503,(len+1)*sizeof(compactCEstruct));
#ifdef ASSERTS
    assert(cCEs[i] != NULL);
#endif
    ptr = CEs[i];
    for(j=0;j<len;j++) {
      cCEs[i][j].var = finalNOTIME(ptr->var);
      cCEs[i][j].disjunctive = ptr->disjunctive;
      cCEs[i][j].condition = ptr->condition;
      ptr = ptr->next;
    }
    //    printf("\n");
    cCEs[i][len].var = -1;
  }
}

/* Test whether action or conditional effect represented by variable v1
can disable or affect the one represented by v2.
We dont' want to tabulate all pairs, as their number grows quadratically.
Instead, we tabulate the precondition literals and the possible effects
of each variable, and test whether the sets intersect. */

int actaffects(int v1,int v2) {
  int *i,*j;

  i = actvars[v1].effectlits;
  assert(i);
  while(*i != -1) {
    j = actvars[v2].conditionlits;
    assert(j);
    while(*j != -1) {
      if(*j == NEG(*i)) return 1;
      j = j + 1;
    }
    i = i + 1;
  }
  return 0;
}

int countlits(fma *f) {
  int cnt;
  fmalist *fs;

  switch(f->t) {
  case conj:
  case disj:
    cnt = 0;
    fs = f->juncts;
    while(fs != NULL) {
      cnt = cnt + countlits(fs->hd);
      fs = fs->tl;
    }
    return cnt;
  case patom:
  case natom:
    return 1;
  default:
    return 0;
  }

}

int *storelits(fma *f,int *ptr) {
  fmalist *fs;

  switch(f->t) {
  case conj:
  case disj:
    fs = f->juncts;
    while(fs != NULL) {
      ptr = storelits(fs->hd,ptr);
      fs = fs->tl;
    }
    return ptr;
  case patom:
    *(ptr++) = PLIT(f->a);
    return ptr;
  case natom:
    *(ptr++) = NLIT(f->a);
    return ptr;
  default:
    return ptr;
  }

}

void storeactvars(int var,int *effectlits,fma *preconlits) {
  int len,*ptr;

  if(var >= maxactvars) {
    int oldmax,i;

    oldmax = maxactvars;
    maxactvars = var + 100000;

    actvars = (actvar *)realloc(actvars,sizeof(actvar) * maxactvars);

    for(i=oldmax;i<maxactvars;i++) {
      actvars[i].effectlits = NULL;
      actvars[i].conditionlits = NULL;
    }
  }

  actvars[var].effectlits = effectlits;

  len = countlits(preconlits);

  actvars[var].conditionlits = (int *)malloc(sizeof(int) * (len+1));

  ptr = storelits(preconlits,actvars[var].conditionlits);

  *ptr = -1;

#ifdef DEBUG
  printUvar(var);
  printf(" preconditions:"); printUlits(actvars[var].conditionlits);
  printf("\n effects:"); printUlits(actvars[var].effectlits);
  printf("\n");
#endif

}

void translateaction(int i) {
  eff *e;
  fma *ef;
  int aux;

  /* Precondition axiom */

  addformula(transition,Fimpl(fmaOP(i),makeVARfma(actions[i].precon)));

  /* Effect axioms */

  e = &(actions[i].effects);

  if(flagCEvariables == 0) { /* Do the regular translation. */

    fma *cond;

    while(e != NULL) {
      ef = effectsofL(e->effectlits);
      addformula(transition,Fimpl(fmaOP(i),Fimpl(makeVARfma(e->condition),ef)));

      cond = Fconj2(e->condition,actions[i].precon);
      storeactvars(i+nOfAtoms,e->effectlits,cond);
      e = e->tl;
    }

  } else { /* Do the translation with variables for conditional effects. */

    while(e != NULL) {
      ef = effectsofL(e->effectlits);
      if(e->condition->t == TRUE) { /* The condition is always true. */
	addformula(transition,Fimpl(fmaOP(i),ef));
	/* Store
	     - the action variable, to be used by the heuristic AND
	     - the associated precondition
	*/
	storeinCEsL(e->effectlits,OP(i),actions[i].precon);
	storeactvars(i+nOfAtoms,e->effectlits,actions[i].precon);
      } else {
	fma *cond;
	aux = allocAUX(1);
	addformula(transition,Fimpl(fmaOP(i),Fimpl(makeVARfma(e->condition),fmaAUX(aux))));
	addformula(transition,Fimpl(fmaAUX(aux),ef));
	addformula(transition,Fimpl(fmaAUX(aux),makeVARfma(e->condition)));
	addformula(transition,Fimpl(fmaAUX(aux),fmaOP(i)));
	/* Store
	     - the auxiliary variable, to be used by the heuristic AND
	     - the associated condition and precondition
	*/
	cond = Fconj2(e->condition,actions[i].precon);
	storeinCEsL(e->effectlits,AUX(aux),cond);
	storeactvars(aux+nOfActions+nOfAtoms,e->effectlits,cond);
      }
      e = e->tl;
    }

  }
}

/* Print encoding */

void printvar(int v) {
  if(v & NEGtag) printf("-");
  if(VARNEXT(v)) printf("*");
  switch(VARTYPE(v)) {
  case AUXtag: printf("AUX%i",VARINDEX(v)); break;
  case VARtag: printatomi(VARINDEX(v)); break;
  case OPtag: printf("OP%i",VARINDEX(v)); break;
  default: printf("(INCORRECT VAR TYPE %i",v); break;
  }
}

void printFfmalist(fmalist *,char *);
void printFfma(fma *f) {
  switch(f->t) {
  case patom: printvar(f->a); break;
  case natom: printf("-"); printvar(f->a); break;
  case conj:
    printf("(");
    printFfmalist(f->juncts,"&");
    printf(")");
    break;
  case disj:
    printf("(");
    printFfmalist(f->juncts,"|");
    printf(")");
    break;
  case TRUE: printf("TRUE"); break;
  case FALSE: printf("FALSE"); break;
  }
}

void printFfmalist(fmalist *l,char *sep) {
  if(l == NULL) return;
  printFfma(l->hd);
  if(l->tl != NULL) printf("%s",sep);
  printFfmalist(l->tl,sep);
}

/* Construct formula expressing conditions when var becomes
   true or false in terms of an applied operator + additional conditions. */

int iamember(int n,int *l) {
  while(*l != -1) {
    if(*l == n) return 1;
    l = l + 1;
  }
  return 0;
}

fma *makes(int val,int var) {
  int i;
  fmalist *fs0,*fs;
  eff *e;
  int *ptr;

  fs = NULL;
 
  if(val == 1) ptr = AeffectoccP[var];
  else ptr = AeffectoccN[var];

  while(*ptr != -1) {

#ifdef ASSERTS
    assert(*ptr >= 0);
#endif
   
    fs0 = NULL; /* Disjuncts of the condition for one operator */
   
    e = &(actions[*ptr].effects);

    while(e != NULL) {
      int *l;

      l = e->effectlits;

      //      if((val && iamember(fePLIT(var),l)) || (!val && iamember(feNLIT(var),l))) {
      if(iamember((val ? fePLIT(var) :  feNLIT(var)),l)) {
	if(e->condition->t == TRUE) { /* Becomes true unconditionally */
	  fs = fmacons(fmaOP(*ptr),fs);
	  goto nextop;
	}
	fs0 = fmacons(makeVARfma(e->condition),fs0); /* Add one disjunct. */
      }

      e = e->tl;
    }

    fs = fmacons(Fconj2(fmaOP(i),Fdisj(fs0)),fs);

  nextop: 1;

    ptr = ptr + 1;

  }

  return Fdisj(fs);
  
}

/**********************************************************************/
/* */
/**********************************************************************/

/* Computation of clauses that restrict the parallel execution of
operators for three forms of plans.
- sequential plans with (at most) one action per time point
- parallel plans with A-step semantics [Rintanen et al. 2006]
- parallel plans with E-step semantics [Rintanen et al. 2006]
*/

void SEQUmutexes() {
  int i,j,bit;
  int indexbits;
  int firstindexbit;
  /* Each action sets its index in log2 nOfActions auxiliary variables. */

  /* Allocate auxiliary variables for index bits */
  indexbits = bitsneeded(nOfActions);
  firstindexbit = allocAUX(indexbits);
  
  for(i=0;i<nOfActions;i++) {
    bit = 1;
    for(j=0;j<indexbits;j++) {
      if(i&bit) addformula(transition,Fimpl(fmaOP(i),fmaAUX(firstindexbit+j)));
      else addformula(transition,Fimpl(fmaOP(i),Fneg(fmaAUX(firstindexbit+j))));
      bit = bit << 1;
    }
  }
}

/* Linear encoding for E-step constraints:

For each SCC of a disabling graph
   For each literal l

   Find set M operators that make l true.
   Find set R operators that require l to be true.
   (If either set is empty, skip to the next literal.)

   Generate chain of implications from each o in M to
   -o' for all o' in L such that o < o'.

   An auxiliary variable aux_o is true if any of the preceding
   o in M is true. This way the number of 2-literal clauses is
   linear in |M|+|L|.

Small SCCs (size =< 10): NOT IMPLEMENTED YET!!!
   Generate the trivial constraints o -> -o' for every pair
   o and o' such that
     o < o' and o may affect o'
     Effects are (may be) consistent.
     Preconditions are (may be) consistent.
 */

#define MAXNM 10000
int auxM[MAXNM];
int auxR[MAXNM];

int intCmp(int *a,int *b) {
  if(*a > *b) return 1;
  else return 0;
}

/* Optimization to the chain encoding:
   if few operators are included, generate binary mutexes. */

void ESTEPprod(int NM, int NR) {
  int i,j,op1,op2;
  for(i=0;i<NM;i++) {
    for(j=0;j<NR;j++) {
      op1 = auxM[i];
      op2 = auxR[j];
      if(op1 == op2) continue;
      if(!parallel(op1,op2)) continue;
      /* Emit a binary clause for mutual exclusion. */
      addformula(transition,Fimpl(fmaOP(op1),Fneg(fmaOP(op2))));
    }
  }
}

/* Check whether there are any two actions without contradicting effects
   or preconditions. */

int noparallels(int NM, int NR) {
  int i,j,op1,op2;
  for(i=0;i<NM;i++) {
    for(j=0;j<NR;j++) {
      op1 = auxM[i];
      op2 = auxR[j];
      if(op1 != op2 && parallel(op1,op2)) {
	//	printactionname(op1); printactionname(op2); printf(" ARE PARALLEL\n");
	return 0;
      } else {
	//	printactionname(op1); printactionname(op2); printf(" ARE *N*O*T* PARALLEL\n");
      }
    }
  }
  return 1;
}

/* Compute E-step axioms for variable i.
   WHAT parameter:
   0: Do the chain for an SCC of the disabling graph.
   1: Do the chain from 0..nOfActions-1.
   2: Do the chain from nOfActions-1..0.
 */

void ESTEPchain(int i,sccs s,int WHAT) {
  int NM,NR,pM,pR,X,tmp,neednewaux,j,op;
  NM = 0;
  NR = 0;

  switch(WHAT) {
  case 1:
    for(j=0;j<nOfActions;j++) {
      if(canmaketrue(j,i)) auxM[NM++] = j;
      if(isaffectedby(j,i) && Lparallel(i,j)) auxR[NR++] = j;
    }
    break;
  case 2:
    for(j=nOfActions-1;j>=0;j--) {
      if(canmaketrue(j,i)) auxM[NM++] = j;
      if(isaffectedby(j,i) && Lparallel(i,j)) auxR[NR++] = j;
    }
    break;
  case 0:
    for(j=0;j<s->NofEls;j++) {
      if(canmaketrue(s->els[j],i)) auxM[NM++] = s->els[j];
      if(isaffectedby(s->els[j],i) && Lparallel(i,s->els[j])) auxR[NR++] = s->els[j];
    }

    /* Both auxR and auxM are sorted to ascending order. */

    qsort(auxR,NR,sizeof(int),intCmp);
    qsort(auxM,NM,sizeof(int),intCmp);
    break;
  }

#ifdef ASSERTS
  assert(NM < MAXNM);
  assert(NR < MAXNM);
#endif

  /* WARNING: The code that follows assumes that auxR and auxM are sorted
     in an ascending order. ASTEPmutexes tries to use this in descending
     order, and therefore produces non-A-step plans. */

  if(NM == 0 || NR == 0) return; /* Nothing to do */

  if(NM == 1 && NR == 1 && auxR[0] == auxM[0]) return; /* Nothing to do */

  if(NM*NR <= (NM+NR)*3) { ESTEPprod(NM,NR); return; }
 
  if(NM*NR < 5000 && noparallels(NM,NR)) return;

  //	printf("%i modify and %i require ",NM,NR);
  //	if(i&i) { printf("-"); printatomi(i >> 1); }
  //	else printatomi(i >> 1);
  //	printf("\n");

#ifdef DEBUG
  printf("PARALLELISM AXIOMS %i %i for ",NM,NR);
  printlit(i); printf("\n");
  
  for(j=0;j<NM;j++) { printf("%i ",auxM[j]); printactionname(auxM[j]); }
  printf("\n");
  for(j=0;j<NR;j++) { printf("%i ",auxR[j]); printactionname(auxR[j]); }
  printf("\n");

#endif

  X = -1;
  neednewaux = 0;
  
  pM = 0; pR = 0;

  while(pM < NM || pR < NR) {

    if(pM < NM && auxM[pM] < auxR[pR]) op = auxM[pM]; else op = auxR[pR];

    //	  printf("%i@%i!",pM,pR);
    
    if(pR < NR && op == auxR[pR]) { /* Operator may need to be disabled. */
      /* disable the operator */
      if(X != -1) {
	addformula(transition,Fimpl(Fatom(X),Fneg(fmaOP(op))));
#ifdef DEBUG
	printFfma(Fatom(X)); printf(" implies "); printFfma(Fneg(fmaOP(op))); printf("\n");
#endif
      }
      neednewaux = 1;
    }

    if(pM < NM && op == auxM[pM]) { /* Operator may disable */

      /* FIX: the last AUX may be unnecessary. */

      if(neednewaux && X != -1) {
	tmp = AUX(allocAUX(1));
	addformula(transition,Fimpl(Fatom(X),Fatom(tmp)));
#ifdef DEBUG
	printFfma(Fatom(X)); printf(" implies "); printFfma(Fatom(tmp)); printf("\n");
#endif
	X = tmp;
      }

      neednewaux = 0;
      
      if(X == -1) {
	neednewaux = 1;
	X = OP(op);
      } else {
	addformula(transition,Fimpl(fmaOP(op),Fatom(X)));
#ifdef DEBUG
	printFfma(fmaOP(op)); printf(" implies "); printFfma(Fatom(X)); printf("\n");
#endif
      }
    }

    if(auxR[pR] == op) pR += 1;
    if(auxM[pM] == op) pM += 1;
    
  }
}

/* This is the linear-size encoding of A-step mutexes. */

void ASTEPmutexesLINEAR() {
  int i;
  for(i=0;i<2*nOfAtoms;i++) { /* Go through all literals. */
    ESTEPchain(i,NULL,1);
    ESTEPchain(i,NULL,2);
  }
}

/* This is the practically more efficient quadratic encoding of the mutexes. */

#define MAXCANDS 20000
int nCands;
int cands[MAXCANDS];

void ASTEPmutexCANDIDATE(int op1,int op2) {
  int i;
  if(op2 >= op1) return;
  if(!parallel(op1,op2)) return;
  for(i=0;i<nCands;i++) if(cands[i] == op2) return;
  cands[nCands++] = op2;
#ifdef ASSERTS
  assert(nCands < MAXCANDS);
#endif
}

void ASTEPprecond(int op,fma *f,int polarity) {
  fmalist *fs;
  int *ptr;

  switch(f->t) {

  case conj:
  case disj:
    fs = f->juncts;
    while(fs != NULL) {
      ASTEPprecond(op,fs->hd,polarity);
      fs = fs->tl;
    }
    break;

  case patom:
  case natom:

    if(polarity == 0 || f->t == patom) {
      ptr = AeffectoccN[f->a];
      while(*ptr != -1) {
	ASTEPmutexCANDIDATE(op,*ptr);
	ptr = ptr + 1;
      }
    }

    if(polarity == 0 || f->t == natom) {
      ptr = AeffectoccP[f->a];
      while(*ptr != -1) {
	ASTEPmutexCANDIDATE(op,*ptr);
	ptr = ptr + 1;
      }
    }

    break;

  default: break;

  }
}

void ASTEPmutexes() {
  int i,j,op;
  eff *es;
  int *ptr,*ptr2;

  for(i=0;i<nOfActions;i++) { /* Go through all actions. */
    /* Locate ones that interfere and can be taken simultaneously. */
    nCands = 0;
    /* Go through effects. */
    es = &(actions[i].effects);

    while(es != NULL) {

      /* Go through all effects. */
      ptr = es->effectlits;
      while(*ptr != -1) {

	if((*ptr)&1)  ptr2 = ApreconoccP[feVAR(*ptr)];
	else ptr2 = ApreconoccN[feVAR(*ptr)];

	while(*ptr2 != -1) {
	  ASTEPmutexCANDIDATE(i,*ptr2);
	  ptr2 = ptr2 + 1;
	}
	ptr2 = Acondocc[feVAR(*ptr)];
	while(*ptr2 != -1) {
	  ASTEPmutexCANDIDATE(i,*ptr2);
	  ptr2 = ptr2 + 1;
	}
	ptr = ptr + 1;
      }

      ASTEPprecond(i,es->condition,1);
      es = es->tl;
    }

    /* Go through preconditions. */
    ASTEPprecond(i,actions[i].precon,0);
    /* Emit parallelism constraints. */
    for(j=0;j<nCands;j++) {
      addformula(transition,Fimpl(fmaOP(i),Fneg(fmaOP(cands[j]))));
    }
  }
}


void ESTEPmutexes() {
  int i;
  sccs s;
  ordintset temp;
  intlist *iterate;

  temp = OScreate();

  /* Go through SCCs. */
  s = SCCS;
  while(s != NULL) {

    if(s->NofEls == 1) goto NEXTSCC;

    if(s->NofEls == 2) {
      addformula(transition,Fimpl(fmaOP(s->els[0]),Fneg(fmaOP(s->els[1]))));
      goto NEXTSCC;
    }

    /* Big SCCs are handled through linearization. */

   if(s->NofEls > nOfActions / 3) {
     //   if(s->NofEls > 2) {
#ifdef DEBUG
    printf("SCC of size %i\n",s->NofEls);
#endif

      for(i=0;i<2*nOfAtoms;i++) { /* Go through all literals */
	ESTEPchain(i,s,0);
      }

    } else { /* Or slightly more cleverly. */

      //      printf("Doing SCC number N of size %i.\n",s->NofEls);

      for(i=0;i<s->NofEls;i++) collectliterals(temp,s->els[i]);

      //      printf("OUTPUTTING axioms: "); fflush(stdout);

      OSstart(temp,&iterate);
      while(OSnext(&i,&iterate)) {
	//	printf("%i:",i); fflush(stdout);
	//	printatomi(i); 
	ESTEPchain(i,s,0);
      }

      //      printf("\n");

      OSmakeempty(temp);

    }
  NEXTSCC:

    s = s->next;
  }
}

int varsPerTime;

/* Test whether l1 implies l2 directly or through invariants. */

int redundant(int l1,int l2) {
  //  printlit(l1); printf(" -> "); printlit(l2);
  if(l1 == l2 || ISmember(l2,twolits[NEG(l1)])) {
    //    printf(" IS REDUNDANT\n");
    return 1;
  }
  //    printf(" IS NOT\n");
  return 0;
}

void printlit(int l) {
  if(VALUE(l) == 0) printf("-");
  printatomi(VAR(l));
}

fma *fslit(int succ,int l) {
  int v;
  if(succ) v = NEXT(VAR(l)); else v = VAR(l);
  if(VALUE(l)) return fmaVAR(v); else return Fneg(fmaVAR(v));
}


#define SKIPFRAMECLAUSES
#ifdef SKIPFRAMECLAUSES

/* Avoid using a a frame action (x@t & -x@t+1) -> a1 V ... V an
   when all of a1,...,an are falsified by fact f, i.e. f != -a1&...&-an.
   These frame axioms, with large n, lead to huge learned clauses.
   We add the clause x@t & -x@t+1 -> -f. */

void skipframeclauses() {

}
#endif

void runalgorithmA(int,int);
void runalgorithmB(double,int);

/**********************************************************************/
/* Encoding a planning problem as a set of propositional formulae     */
/**********************************************************************/

int clauseptr,maxClauseEls;
int *clauseset;

fma *osubstitute(fma *f,int *a) {
  fma *new;
  fmalist *l;

  switch(f->t) {

  case patom: return Fatom(a[f->a]);
  case natom: return Fnatom(a[f->a]);

  case conj:
  case disj:
    new = (fma *)statmalloc(504,sizeof(struct _fma));

    new->t = f->t;

    l = f->juncts;
    new->juncts = NULL;

    while(l != NULL) {
      new->juncts = fmacons(osubstitute(l->hd,a),new->juncts);
      l = l->tl;
    }

    return new;

  default:
    return f;
  }
}

void encodingOgata() {
  int i,j;

    int tempVars[nOfAtoms];
    int tempVarsNEW[nOfAtoms];
    int lastAffecting[nOfAtoms];
    int evars[nOfAtoms],evarcnt;
    fma *epos[nOfAtoms];
    fma *eneg[nOfAtoms];

    int *ls;

    /* The encoding in Ogata, Tsuchiya & Kikuno, "SAT-based verification
       of safe Petri nets", ATVA 2004, LNCS 3299, 79-92, Springer 2004.
    */

    /* 
       Initialize an array A that shows which variable represents a given
       state variable x. Initialize A[x] to x@t.

       Go through all actions sequentially.

       For the precondition have o@t -> phi[x] for precondition phi where
       each x has been replaced by A[x].

       For effects
         IF phi1 THEN x := 1
       and
         IF phi0 THEN x := 0
       we introduce new auxiliary variables aux (unless the action is
       the last one affecting x, in which case we define aux = x@t+1.)

       The definition of aux is aux <-> (A[x] & -phi0) V phi1, where
       variable y in phi0 and phi1 have been replaced by A[y].

       Assign A[x] := aux.
       
     */

    /* Initialize state variable array. */

    for(i=0;i<nOfAtoms;i++) tempVars[i] = SVAR(i);

    /* Initialize an array with the last action affecting each variable. */

    for(i=0;i<nOfAtoms;i++) {
      int *ptr;

      lastAffecting[i] = -1;

      ptr = AeffectoccP[i];

      while(*ptr != -1) {
	if(*ptr > lastAffecting[i]) {
	  lastAffecting[i] = *ptr;
	}
	ptr++;
      }

      ptr = AeffectoccN[i];

      while(*ptr != -1) {
	if(*ptr > lastAffecting[i]) {
	  lastAffecting[i] = *ptr;
	}
	ptr++;
      }

      //      printf("Last affecting %i is %i.\n",i,lastAffecting[i]);
    }

    /* Go through all actions. */

    for(i=0;i<nOfActions;i++) {

      eff *e;

      int k;

      evarcnt = 0;

      for(j=0;j<nOfAtoms;j++) {
	tempVarsNEW[j] = tempVars[j];
	//printf("tempvar[%i] = %x.\n",j,tempVars[j]);
      }

      /* Enforce precondition. */

      addformula(transition,Fimpl(fmaOP(i),osubstitute(actions[i].precon,tempVars)));

      /* Define effect. Go through all effects a of the action, and for each
	 construct formulas epos[a] and eneg[a] which respectively correspond
	 to the conditions under which the state variable becomes true or
	 false. */

      e = &(actions[i].effects);

      while(e != NULL) {

	ls = e->effectlits;

	while(*ls != -1) {

	  //	  printf("Positive effect "); printatomi(ls->hd); printf("\n");

	  j = 0;
	  while(j < evarcnt && evars[j] != *ls) {
	    j = j+1;
	  }

	  if(j == evarcnt) {

	    if((*ls)&1) {
	      eneg[j] = e->condition;
	      epos[j] = Ffalse();
	    } else {
	      epos[j] = e->condition;
	      eneg[j] = Ffalse();
	    }

	    evars[j] = *ls;

	    evarcnt += 1;

	  } else {

	    if((*ls)&1) {
	      eneg[j] = Fdisj2(eneg[j],e->condition);
	    } else {
	      epos[j] = Fdisj2(epos[j],e->condition);
	    }
	  }

	  ls = ls + 1;
	}

	e = e->tl;
      }

      /* Create an equivalence tempVar[a]NEW <-> (OPi & epos[a]) V (tempvar[a] & -(OPi & eneg[a]))
	 for every effect a of the action. */

      for(j=0;j<evarcnt;j++) {

	int v;

	v = evars[j];

	if(lastAffecting[v] == i) {
	  k = SVAR(NEXT(v));
	} else {
	  k = AUX(allocAUX(1));
	  //	  printf("Created aux %i for var %i.\n",k&0xffff,v);
	}

	tempVarsNEW[v] = k;

	//	printf("Considering effect "); printatomi(v); printf("\n");

	//	printfma(epos[j]); printf("\n");
	//	printfma(eneg[j]); printf("\n");
	//	fflush(stdout);

	addformula(transition,Fimpl(Fatom(k),
				    Fdisj2(Fconj2(fmaOP(i),
						  osubstitute(epos[j],tempVars)),
					   Fconj2(Fatom(tempVars[v]),
						  Fneg(Fconj2(fmaOP(i),
							      osubstitute(eneg[j],tempVars)))))));

	addformula(transition,Fimpl(Fconj2(fmaOP(i),
					   osubstitute(epos[j],tempVars)),
				    Fatom(k)));

	addformula(transition,Fimpl(Fconj2(Fatom(tempVars[v]),
					   Fneg(Fconj2(fmaOP(i),
						       osubstitute(eneg[j],tempVars)))),
				    Fatom(k)));
      }

      for(j=0;j<nOfAtoms;j++) tempVars[j] = tempVarsNEW[j];

    }

}

//fma *conjofCEs(int i) {
//  ptrlist *fs;
//  CEstruct *s;
//  fs = NULL;
//  for(s=CEs[i];s!=NULL;s=s->next) {
//    fs = fmacons(Fatom(s->var),fs);
//  }
//  if(fs == NULL) return Ftrue();
//  else return Fconj(fs);
//}

fma *disjofCEs(int i) {
  ptrlist *fs;
  CEstruct *s;
  fs = NULL;
  for(s=CEs[i];s!=NULL;s=s->next) {
    fs = fmacons(Fatom(s->var),fs);
  }
  if(fs == NULL) return Ffalse();
  else return Fdisj(fs);
}

void addshortcuts() {
  satinstance tmp = outputNSAT(0,flagShortCutHorizon*2+1,1);
  shortcuts(tmp);
}


/***************************************************************************/
/* Management of the temporary clauseset.                                  */
/***************************************************************************/

int *tmpclauseset,tmpnOfClauses,tmpptr;

/* Go through all clauses in the temporaryclauseset and emit them. */

void emitclause(int *,int,formulaclass);

void emittemporarygoalinitclauses() {
  int clen,class,cnt;

#ifdef DEBUG
  printf("Start moving init and goal clauses.\n");
#endif

  cnt = 0;
  tmpptr = 0;
  while(cnt < tmpnOfClauses) {
    switch(tmpclauseset[tmpptr] & TIMEtags) {
    case INITtag: class = inittime; break;
    case GOALtag: class = goaltime; break;
    case TRtag: class = transition; break;
    default: fprintf(stderr,"emittemporarygoalinitclauses"); exit(1);
    }
    clen = tmpclauseset[tmpptr] & LENBITS;
    if(class != transition) /* Only copy non-transition clauses. */
      emitclause(&(tmpclauseset[tmpptr+1]),clen,class);
    tmpptr += clen+1;
    cnt += 1;
  }
#ifdef DEBUG
  printf("Finished moving init and goal clauses.\n");
#endif
}

/* PROBLEM ABOVE: goal formulas may be Tseitin-transformed, and if
   the external preprocess has changed the variable numbering, then
   we would have to rename the auxiliary variables at this point.
   However, this is not necessary if the numbering only affects the
   "next state" and auxiliary variables.
*/

/* Functions and variables for interfacing with the external preprocessor */

int ppclause[0x100000];
int pplen;
int ppSVars,ppActions,ppAux,ppNewAux;

void initializepprenaming(int nSVars,int nActions,int nAux,int newtotal) {
  ppSVars = nSVars;
  ppActions = nActions;
  ppAux = nAux;
  ppNewAux = newtotal-(ppSVars+ppActions+ppAux+ppSVars); // How many new aux?
  varsPerTime = ppSVars+ppActions+ppNewAux+ppAux;
  printf("SVars = %i Actions = %i Aux = %i newAux = %i\n",
	 nSVars,nActions,nAux,ppNewAux);
}

int pprenamelit(int lit) { // Rename literal after using external preprocessor
  int negated;
  int index,newindex;
  int NAUXBEGIN;

  if(lit < 0) {
    negated = 1;
    index = (0-lit)-1;
  } else {
    negated = 0;
    index = lit-1;
  }

  NAUXBEGIN = ppSVars+ppActions+ppAux+ppSVars;

  if(index < ppSVars+ppActions+ppAux) { // SVar, Action, Aux indexing unchanged
    newindex = index;
  } else if(index >= NAUXBEGIN) { // New auxiliaries will go after old auxiliaries.
    newindex = index-ppSVars;
  } else { // Next state variables will be shifted after new auxiliaries.
    newindex = index+ppNewAux;
  }

  return (negated ? 0-(newindex+1) : (newindex+1));
}

/******************************************************************************/
/* CP3 interface                                                              */
/******************************************************************************/

#ifdef CP3

void docp3preprocessing() {

  int freezeVar = 0,
      cpClss = 0,
      cpVars = 0,
      cpTotalLits = 0,
      lit = 0,
      testLits = 0,
      testClss = 0;

      int ptr,len;
      int i,j;

    printf("c start CNF preprocessing\n");
    printf("1\n");
    void *preprocessor = CPinit();
    int myargc = 7; // 6 number of elements of parameters (so far, must be set manually)
    /*
     * Here, the actual interesting stuff can be done
     * Could do experiments to extract the reduction without actually perform search for a plan at the beginning
     * 
     * "-bve" does variable elimination. When action variables would not be freezed, that might become much more interesting  (for-loop below)
     * "-bva" does variable addition, independent of frozen variables. However, introduces fresh variables as new "high" variables, so that the order on the variables breaks 
     */
    const char * myargv [] = {"pseudobinary","-enabled_cp3","-up","-subsimp","-unhide","-bva","-bve"}; // configuration - bve, because important vars are freezed
    printf("2\n");
    CPparseOptions( preprocessor, &myargc, myargv, 0 ); // parse the configuration!
    
    // add clauses to preprocessor
    printf("3\n");
    printf("c send formula to Coprocessor (%d)\n",nOfClauses);
    
    // test the kind of clauses
    testClss = 0;ptr = 0;
    for(i=0;i<nOfClauses;i++) if( (clauseset[ptr] &TIMEtags) == INITtag ) testClss ++;
    printf("c %d init clauses\n", testClss );
    
    testClss = 0;ptr = 0;
    for(i=0;i<nOfClauses;i++) if( (clauseset[ptr] &TIMEtags) == TRtag ) testClss ++;
    printf("c %d transition clauses\n", testClss );
    
    testClss = 0;ptr = 0;
    for(i=0;i<nOfClauses;i++) if( (clauseset[ptr] &TIMEtags) ==  GOALtag ) testClss ++;
    printf("c %d goal clauses\n", testClss );
    
    // send clauses to preprocessor (and print them)
    ptr = 0;
    for(i=0;i<nOfClauses;i++) {
      len = (clauseset[ptr])&LENBITS;
      if( (clauseset[ptr] &TIMEtags) == TRtag ) { // this is a transition clause
	for(j=1;j<=len;j++) {
	  CPaddLit( preprocessor, clauseset[ptr+j] );
	  // 	  printf("%d ",clauseset[ptr+j]);
	}
	CPaddLit( preprocessor, 0 );
	// 	printf("0\n");
      }
      ptr = ptr+len+1;
    }
    printf("4\n");
    // freeze important variables -- here, easy, everything that might be used from the outside
    for( freezeVar = 0; freezeVar < nOfAtoms; ++freezeVar ) { // this time steps atom variables
      CPfreezeVariable(preprocessor, freezeVar );
    }
    printf("5\n");
    for( freezeVar = varsPerTime; freezeVar < varsPerTime + nOfAtoms; ++ freezeVar ) { // next time steps atom variables
      CPfreezeVariable(preprocessor, freezeVar );
    }
    if( 1 ) { // should have a parameter here!
      printf("6\n");
      for( freezeVar = nOfAtoms; freezeVar < nOfAtoms + nOfActions; ++ freezeVar ) { // action variables -- not necessary to be frozen, however, disappear otherwise, can be reconstructed
	CPfreezeVariable(preprocessor, freezeVar ); 
      }  
    }
    printf("7\n");

    /* Create a new clause DB and copy the old Init and Goal clauses there. */

    tmpclauseset = clauseset; // Keep the old clause set for emittemporarygoalinitclauses.
    tmpnOfClauses = nOfClauses;

    initclauseset(); // Start constructing a new clause set.

    emittemporarygoalinitclauses(); /* Copy Goal and Init clauses to new set. */

    /* After this, it remains to obtain the preprocessed Transition clauses
       from the preprocessor and add them to the new clause set. */

    // preprocess (equivalence stuff!)
    CPpreprocess( preprocessor );
    
    // get formula back
    printf("8\n");
    cpClss = CPnClss (preprocessor);
    cpVars = CPnVars( preprocessor ); // should be the same as varsPerTime, as long as neither "-bva" nor "-dense" is used in the Coprocessor configuration
    cpTotalLits = CPnLits ( preprocessor ); // for getting space with malloc/realloc
    
    // running over all clauses:
    printf("9\n");
//     printf("c transition formula\n");
    CPresetOutput(preprocessor);
    initializepprenaming(nOfAtoms,nOfActions,nOfAux,cpVars);
    pplen = 0;
    while( CPhasNextOutputLit(preprocessor) ) { // printing all clauses, and checking whether the numbers actually work and all literals are printed
      lit = CPnextOutputLit( preprocessor );
      if( lit != 0 ) { 
	ppclause[pplen++] = pprenamelit(lit);
	testLits ++; 
	//  	printf("%d ", lit );
      }
      else {
	emitclause(ppclause,pplen,transition);
	pplen = 0;
	testClss ++;
	//  	printf("0\n");
      }
    }

    printf("cls (inside/outside): %d / %d , totalLits: %d / %d\n", cpClss, testClss, cpTotalLits, testLits);
    
    // free resources again
    // CPdestroy( preprocessor ); // TODO needs to be fixed
}

#endif

/***************************************************************************/
/* Top-level function for producing planning encodings. */
/***************************************************************************/

void encoding() {
  int i,j,ptr,len;

  if(firstTimePoint > lastTimePoint) {
    printf("Check -F %i and -T %i: first time point > last\nExiting...",firstTimePoint,lastTimePoint);
    exit(0);
  }

  initformuladb();

  for(i=0;i<nOfAtoms;i++) {
    if(initialstate[i] == 1) addformula(inittime,fmaVAR(i));
    else addformula(inittime,Fneg(fmaVAR(i)));
  }

  addformula(goaltime,makeVARfma(goal));

  if(planSemantics == EStepOgata) { /* Do Ogata style encoding. */

    encodingOgata();

  } else { /* Do all other encodings. */

    CEs = (CEstruct **)statmalloc(505,nOfAtoms * 2 * sizeof(CEstruct *));
    cCEs = (CEstruct **)statmalloc(506,nOfAtoms * 2 * sizeof(compactCEstruct *));
    for(i=0;i<nOfAtoms*2;i++) CEs[i] = NULL;

    /* Action (cond. effect) variables' precondition and effect literals */

    actvars = (actvar *)malloc(sizeof(actvar) * nOfActions);

    for(i=0;i<nOfActions;i++) {
      actvars[i].effectlits = NULL;
      actvars[i].conditionlits = NULL;
    }

    /* Translate actions in the standard way (preconditions, effects). */

#define RANDOMORDER
#ifdef RANDOMORDER
    /* Shuffle the action set to make planning insensitive to the syntactic
       ordering of the actions. */

    {
      int indices[nOfActions],tmp;
      for(i=0;i<nOfActions;i++) indices[i] = i;
      for(i=0;i<nOfActions-1;i++) {
	int r;
	r = i+1+(random() % (nOfActions-i-1));
#ifdef ASSERTS
	assert(r>i);
	assert(r<nOfActions);
	assert(r != i);
#endif
	tmp = indices[i]; indices[i] = indices[r]; indices[r] = tmp;
      }
      for(i=0;i<nOfActions;i++) translateaction(indices[i]);
    }
#else
    for(i=nOfActions-1;i>=0;i--) translateaction(i);
#endif

    /* Frame axioms */


    if(flagCEvariables == 0) { /* The base encoding. */

      for(i=0;i<nOfAtoms;i++) {
	fma *toT,*toF;
	
	/* Condition under which i becomes true */
	toT = makes(1,i);
	/* Condition under which i becomes false */
	toF = makes(0,i);

	addformula(transition,Fimpl(Fneg(fmaVAR(i)),Fimpl(fmaVAR(NEXT(i)),toT)));
	addformula(transition,Fimpl(Fneg(fmaVAR(NEXT(i))),Fimpl(fmaVAR(i),toF)));
	
      }

    } else {

      for(i=0;i<nOfAtoms;i++) {
	addformula(transition,Fimpl(Fneg(fmaVAR(i)),Fimpl(fmaVAR(NEXT(i)),disjofCEs(fePLIT(i)))));
	addformula(transition,Fimpl(Fneg(fmaVAR(NEXT(i))),Fimpl(fmaVAR(i),disjofCEs(feNLIT(i)))));
      }
      
    }


    /* Mutual exclusion of actions. Dependent on the parallel semantics. */

    printf("Plan type: ");

    switch(planSemantics) {
    case Sequ: /* Sequential semantics one action per time */
      printf("Sequential\n");
      SEQUmutexes();
      break;
    case AStep:	/* parallel A-step semantics */
      printf("A-step\n");
      ASTEPmutexes();
      //    ASTEPmutexesLINEAR();
      break;
    case EStep:	/* parallel E-step semantics */
      printf("E-step\n");
      ESTEPmutexes();
      break;
    case EStepOgata:	/* "sequential" E-step semantics */
      assert(1==0);
      break;
    }

    /* Additional constraints */

#ifdef SKIPFRAMECLAUSES
    skipframeclauses();
#endif

  }

  initclauseset();

  init_clausesets(nOfAtoms+nOfActions+nOfAux);

  //  printf("Outputting clauses.\n");

  for(i=0;i<nOfFmas;i++) {
    //    printFfma(fmas[i].f); printf("\n");
    simplifyfma(fmas[i].f);

    if(flagShowInput) {
      switch(fmas[i].cl) {
      case inittime: printf("I:"); break;
      case goaltime: printf("G:"); break;
      case transition: printf("T:"); break;
      }
      printFfma(fmas[i].f); printf("\n");
    }

    produceclauses(fmas[i].f,fmas[i].cl);
  }

  /* Now the number of auxiliary variables is known. */

  varsPerTime = nOfAtoms+nOfActions+nOfAux;

  /* Calculate all variables indices. */

  ptr = 0;
  for(i=0;i<nOfClauses;i++) {
    len = (clauseset[ptr])&LENBITS;
    for(j=1;j<=len;j++) clauseset[ptr+j] = final(clauseset[ptr+j],0);
    ptr = ptr+len+1;
  }

  if(flagCEvariables) compactCEs();

#ifdef CP3
  if(flagExternalPreprocessor) {
    docp3preprocessing();
  }
#endif

  if(flagOutputDIMACS) {
    outputDIMACS();
  } else {

    if(PLANheuristic == 0) printf("Heuristic: VSIDS\n");

    nofshortcutclauses = 0;
    if(flagShortCutHorizon) addshortcuts();

    switch(evalAlgorithm) {
    case 0: runalgorithmA(paramA,outputTimeStep); break;
    case 1: runalgorithmB(paramB,outputTimeStep); break;
    case 2: runalgorithmC(); break;
    default: 1;
    }
  }
}

void callprintplan(satinstance sati) {
  int usingstd;
  FILE *f;
  if(outputfile == NULL) {
    usingstd = 1;
  } else {
    f = fopen(outputfile,"w");
    if(f == NULL) {
      fprintf(stderr,"WARNING: could not open output file\n");
      usingstd = 1;
    } else {
      usingstd = 0;
    }

  }
  if(usingstd) {
    fprintplan(stdout,sati);
  } else {
    fprintplan(f,sati);
    fclose(f);
  }
}

#define max(A,B) ((A)>(B) ? (A) : (B))
#define min(A,B) ((A)<(B) ? (A) : (B))

void startlength(int i,int len) {
  seqs[i].sati = outputNSAT(i,len+1,0);

  printf("Horizon %i:",len);
  printf(" %i variables\n",seqs[i].sati->nOfVars);

  seqs[i].restart = 0;
  seqs[i].callsleft = 0;
  seqs[i].effort = 0;
  // The following test was i > 1. Was it redundant? See outputNSAT.
  if(i > 0) seqs[i].sati->al2its = seqs[0].sati->al2its;
}

int gcinterval; /* How often will GC be performed. */
int gccounter; /* Counter to see if gccinterval has been reached. */
int notstart; /* Instance length for which no-start has been notified. */

void init_gc() {
  gcinterval = 20000;
  gccounter = gcinterval;
  notstart = 0;
}

void reset_gccounter(int freed) {
  gccounter = gcinterval;
  if(GCaggressiveness == 0) gcinterval += 500;
}

/*
  Luby series:
   t_i = 2^{k-1} if i = 2^k-1
   t_i = t_{i-2^{k-1}+1} if 2^{k-1} <= i < 2^k - 1

  Jinbo Huang (2007?) proposed the Luby series as a restart strategy.
  (Or was it already used in SATZ_rand by Selman and others before?)

  Warning: luby is not defined for 0, but for all i >= 1.
*/

int luby(int i) {
  int k,p;
  k = 1;
  p = 2;
  while (p < (i+1)) {
    k += 1;
    p *= 2;
  }
  if (p == (i+1)) return (p/2);
  return (luby(i - (p/2) + 1));
}


/* How many steps per ith restart? */

inline int RESTART(int i) {
  switch(flagRestartScheme) {
  case 0: return 1;
  case 1: return luby(i+1);
  default: return 1;
  }
}


int instancelength(int i) {
  return i*outputTimeStep+firstTimePoint;
}

void testtimeout() {
  if(flagTimeout && (timefromstart() > (float)flagTimeout)) {
    printf("Timeout after %i seconds of CPU time.\n",flagTimeout);
    givememorystatistics();
    exit(0);
  }
}

int actives;

/* Make one SAT call, and update the seqs[] data structure according
   to the result. Return TRUE if a satisfying assignment was found. */

int computeonestep(int i,int forcedrestart) {
  int j;

  /* Do restart now? Yes, if there is only one call left. */
  int restart;

  /* If all calls for the preivous restart were done, start a new restart. */

  if(seqs[i].callsleft == 0) {
    seqs[i].restart += 1;
    seqs[i].callsleft = RESTART(seqs[i].restart);
  }

  restart = (seqs[i].callsleft == 1) || forcedrestart;

  /* The number of clauses learned is determined by flagRestartInterval. */
  solve0(seqs[i].sati,flagRestartInterval,restart);

  seqs[i].effort += 1;
  seqs[i].callsleft -= 1;

  /* If instance turned out to be TRUE. */
  if(seqs[i].sati->value == 1) {
#ifdef MULTICORE
#pragma omp critical
#endif
    {
      actives -= 1; // printf("actives = %i\n",actives);
      printf("PLAN FOUND: %i steps\n",seqs[i].sati->nOfTPoints-1);
      callprintplan(seqs[i].sati);
    }
    return 1;
  }

#ifdef MULTICORE
#pragma omp critical
#endif
  {
  /* If instance turned out to be FALSE. */
    if(seqs[i].sati->value == 0) {
      actives -= 1; // printf("actives = %i\n",actives);
      printf("%i UNSAT (%i decisions %i conflicts)\n",seqs[i].sati->nOfTPoints-1,seqs[i].sati->decisions,seqs[i].sati->conflicts);
      for(j=0;j<i;j++) {
	if(seqs[j].sati->value == -1) {	/* Formulas that must be UNSAT. */
	  seqs[j].sati->value = 0;
	  printf("%i must be UNSAT (%i decisions %i conflicts)\n",seqs[j].sati->nOfTPoints-1,seqs[j].sati->decisions,seqs[j].sati->conflicts);
	  freeinstance(seqs[j].sati);
	}
      }
      freeinstance(seqs[i].sati);
    }
  }
  return 0;
}

/* Can start a new instance without exhausting memory? */

int instancefitsmemory(int new) {
  return (memoryused() + estimateinstancesize(new,nOfActions*3,nOfActions) < flagMemoryLimit);
}

/* If memory exhausted, reduce GC interval and stop increasing it. */

void testmemoryexhaustion() {
  if(GCaggressiveness == 0 && memoryused() > flagMemoryLimit) {
    printf("ATTENTION: Memory bound %.2f MB reached, %.2f MB allocated\n",flagMemoryLimit,memoryused());
    GCaggressiveness = 1;
    gcinterval = gcinterval / 2;
    gccounter = -1;
  }
}


/* With one restart split to several pieces (as with Luby), we must
delay clause deletion / garbage collection to when all SAT instances
are restarted. This may involve delaying some of the restarts.
Alternatively, we immediately terminate the current restarts when we want
to collect garbage. */

void runalgorithmA(int n,int step) {
  int last;
  int i,j;
  int restart;

  initclausedb();

  actives = 0;
  last = -1;
  
  init_gc();

  do {

    testtimeout();

    /* Start new lengths if there are not enough. */

    while(actives < n && instancelength(last+1) <= lastTimePoint && instancefitsmemory(instancelength(last+1))) {
      last += 1;
      startlength(last,instancelength(last));
      if(seqs[last].sati->value != 0) actives += 1;
    }

    //    printf("solving ..%i with %i active\n",last,actives);

    for(i=0;i<=last;i++) {

      testmemoryexhaustion();

      if(seqs[i].sati->value == -1) {

	if(computeonestep(i,0)) return;
	gccounter -= flagRestartInterval;

      }
   
    }

    if(gccounter < 0) {
      /* Must initiate a restart at this point: GC will move clauses, and
	 we would otherwise need to redirect pointers in the decision stack. */
      for(j=0;j<=last;j++) if(seqs[j].sati->value == -1 && seqs[j].callsleft && computeonestep(j,1)) return;
      reset_gccounter(garbagecollection());
    }

  } while((instancelength(last+1) <= lastTimePoint) || (seqs[last].sati->value == -1));

  printf("PLAN NOT FOUND: steps %i..%i tested\n",firstTimePoint,lastTimePoint);
  return;
}

void MULTICORErunalgorithmA(int n,int step) {
  int PLANFOUND,DOGC,NOPLAN;
  int first,last;
  int nextinst,i,j;
  int currentThread;

  initclausedb();

  actives = 0;

  nextinst = -1;
  first = 0;
  last = -1;
  
  init_gc();

  while(actives < n && instancelength(last+1) <= lastTimePoint) {
    startlength(last+1,instancelength(last+1));
    last += 1;
    if(seqs[last].sati->value != 0) actives += 1;
  }

#ifdef MULTICORE
#pragma omp parallel private(i,j,currentThread)
#endif
  {
#ifdef MULTICORE
    currentThread = omp_get_thread_num();
#else
    currentThread = 0;
#endif

    DOGC = 0;
    NOPLAN = 0;
    PLANFOUND = 0;

    do {

#ifdef MULTICORE
#pragma omp master
      testtimeout();
#endif

    do {

    /* Start new lengths if there are not enough. */

#pragma omp master
      {
	while(actives < n && instancelength(last+1) <= lastTimePoint) {
	  startlength(last+1,instancelength(last+1));
	  last += 1;
	  if(seqs[last].sati->value != 0) actives += 1;
	}
      }

#pragma omp critical
      {

	/* Find next SAT instance to solve. */

	do {
	  nextinst += 1;
	  printf("NEXTINST = %i for thread %i\n",nextinst,currentThread); fflush(stdout);
	  if(nextinst > last) nextinst = first;

	} while(seqs[nextinst].sati->thread != -1 || seqs[nextinst].sati->value != -1);

	/* nextinst is an instance that has not been and is not being solved. */

	i = nextinst;
	seqs[i].sati->thread = currentThread; /* Record running thread. */

	printf("Computing length %i in thread %i.\n",seqs[i].sati->nOfTPoints,currentThread); fflush(stdout);

      }

      if(computeonestep(i,0)) {
	PLANFOUND = 1;
      }
      seqs[i].sati->thread = -1; /* Not running any more. */

#pragma omp atomic
      gccounter -= flagRestartInterval;

      if(gccounter < 0) {
	DOGC = 1;
	printf("DOING GC!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n");
      /* Must initiate a restart at this point: GC will move clauses, and
	 we would otherwise need to redirect pointers in the decision stack. */
	for(j=0;j<=last;j++) if(seqs[j].sati->value == -1 && seqs[j].callsleft && computeonestep(j,1)) PLANFOUND = 1;
      }

      if((instancelength(last+1) > lastTimePoint) && (seqs[last].sati->value != -1)) NOPLAN = 1;


    } while(!PLANFOUND && ! NOPLAN && !DOGC);

#pragma omp barrier

#pragma omp master
    {
      if(DOGC) {
	reset_gccounter(garbagecollection());
	DOGC = 0;
      }
    }

#pragma omp barrier

  } while(!PLANFOUND && !NOPLAN);

  }

  if(NOPLAN) {
    printf("PLAN NOT FOUND: steps %i..%i tested\n",firstTimePoint,lastTimePoint);
  }
  return;
}

double power(double r,int i) {
  int j;
  double value;
  value = 1.0;
  for(j=0;j<i;j++) {
    value = value*r;
  }
  return value;
}

void runalgorithmB(double r,int step) {
  int last,firstactive;
  float threshold;
  int i,j;

  initclausedb();

  last = -1;

  init_gc();
  
  actives = 0;

  do {

    testtimeout();

    firstactive = -1;

    for(i=0;i<=last;i++) {

      if(seqs[i].sati->value == -1) {

	if(firstactive == -1) {
	  firstactive = i;

	  /* The lowest active horizon length is always computed. */

	  seqs[i].sati->thread = 0;
	  if(computeonestep(i,0)) return;

	  gccounter -= flagRestartInterval;

	} else {

	  threshold = ((float)(seqs[firstactive].effort))*power(r,i-firstactive)+0.5;
	  if(((float)(seqs[i].effort)) < threshold) {
	    
	    seqs[i].sati->thread = 0;
	    if(computeonestep(i,0)) return;

	    gccounter -= flagRestartInterval;
	  }
	}

	//	if(i==5) printplanT(seqs[i].sati);

      }

    testmemoryexhaustion();

    }

    /* Check whether to start new length. */

    if(last > -1) threshold = ((float)(seqs[firstactive].effort))*power(r,last+1-firstactive);

    if((instancelength(last) < lastTimePoint) && (actives < paramM) && (firstactive == -1 || threshold > 0.5)) {
      
      if(instancefitsmemory(instancelength(last+1))) {
	startlength(last+1,instancelength(last+1));
	last += 1;
	actives += 1; // printf("ADD: actives = %i %i\n",actives,paramM);
      } else {
	if(notstart < instancelength(last+1))
	  printf("ATTENTION: Horizon %i will not be started: memory allocated %.2f MB limit %.2f MB\n",instancelength(last+1),memoryused(),flagMemoryLimit);
	notstart = instancelength(last+1);
      }
    }

    if(gccounter < 0) {
      /* Must initiate a restart at this point: GC will move clauses, and
	 we would otherwise need to redirect pointers in the decision stack. */
      for(j=0;j<=last;j++) if(seqs[j].sati->value == -1 && seqs[j].callsleft && computeonestep(j,1)) return;
      reset_gccounter(garbagecollection());
    }
    

  } while((instancelength(last+1) <= lastTimePoint) || (seqs[last].sati->value == -1));

  printf("PLAN NOT FOUND: %i steps tested\n",lastTimePoint);
}

/* Algorithm C: consider horizon lengths r^0, r^1, r^2, ... */

int Clength(int i) {
  return (int)(5.0*power(paramC,(float)i));
}

void runalgorithmC() {
  int last;
  int i,j;

  initclausedb();

  actives = 0;
  last = -1;
  
  init_gc();

  do {

    /* Start new lengths if there are not enough. */

    if(actives < paramM && Clength(last+1) <= lastTimePoint && instancefitsmemory(Clength(last+1))) {
      startlength(last+1,Clength(last+1));
      last += 1;
      if(seqs[last].sati->value != 0) actives += 1;
    }
    //    printf("instancesizeestimate is %.2f (len %i vars %i actions %i\n",estimateinstancesize(Clength(last+1),varsPerTime,nOfActions),Clength(last+1),varsPerTime,nOfActions);

    if(actives == 0) {
      printf("Was not allowed to increase horizon length. Exiting..\n");
      exit(1);
    }

    //    printf("solving ..%i with %i active\n",last,actives);

    for(i=0;i<=last;i++) {

      if(seqs[i].sati->value == -1) {

	if(computeonestep(i,0)) return;
	gccounter -= flagRestartInterval;

      }

      testmemoryexhaustion();
   
    }

    if(gccounter < 0) {
      /* Must initiate a restart at this point: GC will move clauses, and
	 we would otherwise need to redirect pointers in the decision stack. */
      for(j=0;j<=last;j++) if(seqs[j].sati->value == -1 && seqs[j].callsleft && computeonestep(j,1)) return;
      reset_gccounter(garbagecollection());
    }

  } while((Clength(last+1) <= lastTimePoint) || (seqs[last].sati->value == -1));

  printf("PLAN NOT FOUND: steps %i..%i tested\n",firstTimePoint,lastTimePoint);
  return;
}


/*******************************************************************/
/*    DIMACS output                                                */
/*******************************************************************/

inline int final(int i,int time) {
  int j;
  switch(i&TYPEtag) {
  case AUXtag: j = nOfAtoms+nOfActions; break;
  case VARtag: j = 0; break;
  case OPtag: j = nOfAtoms; break;
  default: fprintf(stderr,"ERROR: 43346 %i %i\n",i%TYPEtag,i); exit(1); break;
  }
  if(i&NEXTtag) j += varsPerTime;
  j += VARINDEX(i)+time*varsPerTime;
  if(i&NEGtag) return -(j+1); else return j+1;
}

inline int finalNOTIME(int i) {
  int j;
  switch(i&TYPEtag) {
  case AUXtag: j = nOfAtoms+nOfActions; break;
  case VARtag: j = 0; break;
  case OPtag: j = nOfAtoms; break;
  default: assert(1 == 0); // fprintf(stderr,"ERROR: 43346\n"); exit(1); break;
  }
  return j+VARINDEX(i);
}

void initclauseset() {
  nOfClauses = 0;
  nOfTClauses = 0;
  clauseptr = 0;
  maxClauseEls = 0x40000;
  clauseset = (int *)malloc(maxClauseEls * sizeof(int));
}

void reallocclauseset(int minsize) {
  maxClauseEls = max(maxClauseEls * 2,minsize);
  clauseset = (int *)realloc(clauseset,maxClauseEls * sizeof(int));
}

void emitclause(int *vector,int cnt,formulaclass class) {
  int i,j,tmp,realcnt,*tag;
  nOfClauses += 1;
  if(class == transition) nOfTClauses += 1;
  if(clauseptr + cnt + 1 > maxClauseEls) reallocclauseset(clauseptr+cnt+1);
  realcnt = 0;
  tag = &(clauseset[clauseptr++]);
#ifdef DEBUG
  printf("EMIT: ");
#endif
  for(i=0;i<cnt;i++) {
#ifdef DEBUG
    printvar(vector[i]); printf(" ");
#endif
    for(j=i+1;j<cnt;j++) {
      if(vector[i] == vector[j]) goto skipliteral;
    }
    realcnt += 1;
    clauseset[clauseptr++] = vector[i];
  skipliteral: 1;
  }
  switch(class) {
  case inittime: tmp = realcnt|INITtag; break;
  case goaltime: tmp = realcnt|GOALtag; break;
  case transition: tmp = realcnt|TRtag; break;
  }
  *tag = tmp;
#ifdef DEBUG
  printf("\n");
#endif
}


/*******************************************************************/
/*    CNF transformation                                           */
/*******************************************************************/

#define MAXXCLAUSELEN 200000
int xclauselen;
int xclause[MAXXCLAUSELEN];

#define MAXXSTACK 200000
int xstackptr;
int xstackv[MAXXSTACK];
fma *xstack[MAXXSTACK];

/* Locate all conjuncts, and produce a clause for each. */

void produceclauses(fma *f,formulaclass class) {
  fmalist *fs;

  switch(f->t) {
  case conj:
    fs = f->juncts;
    while(fs != NULL) {
      produceclauses(fs->hd,class);
      fs = fs->tl;
    }
    break;
  case disj:
    /* Find all disjuncts, get a literal representing each, and output a clause.
       For non-atomic disjuncts, do the same recursively. */
    if(!biggerthan(f,200)) {
#ifdef DEBUG
      printf("Calling produceclausesENUM with: ");
      printFfma(f);
      printf("\n");
#endif
      produceclausesENUMERATIVE(f,class);
    } else {
      xstackptr = -1;
      xclauselen = 0;
      produceclausesDD(f,class);
      emitclause(xclause,xclauselen,class);
      produceclausesTseitin(class);
    }
    break;
  case patom:
    xclause[0] = f->a;
    emitclause(xclause,1,class);
    break;
  case natom:
    xclause[0] = (f->a)|NEGtag;
    emitclause(xclause,1,class);
  case TRUE: break;
  case FALSE:
    printf("WARNING: Emitting top-level constant FALSE.\n");
    xclause[0] = 0|VARtag;
    emitclause(xclause,1,class);
    xclause[0] = 0|NEGtag|VARtag;
    emitclause(xclause,1,class);
    /* There must be at least one state variable. */
    if(nOfAtoms == 0) nOfAtoms = 1;
    /* Sometimes all vars are eliminated, and we would get errors elsewhere. */
    break;
  }
}

/* Identify the disjuncts of a clause, and put them in the xclause
  array. Disjuncts that are conjunctions are represented by a new
  auxiliary literal, and for each such literal an appropriate equivalence
  is later generated by the produceclausesTseitin procedure.
*/

void produceclausesDD(fma *f,formulaclass class) {
  fmalist *fs;
  int aux;

  switch(f->t) {
  case disj:
    fs = f->juncts;
    while(fs != NULL) {
      produceclausesDD(fs->hd,class);
      fs = fs->tl;
    }
    break;
  case conj:
    aux = allocAUX(1);
    xclause[xclauselen++] = AUX(aux);
    xstack[++xstackptr] = f;
    xstackv[xstackptr] = AUX(aux);
    break;
  case patom:
    xclause[xclauselen++] = f->a;
    break;
  case natom:
    xclause[xclauselen++] = (f->a)|NEGtag;
    break;
  case TRUE:
    /* Clause is TRUE: don't generate it!!!!!!!!!!!!!!!!!!!!!!!! */
#ifdef ASSERTS
    assert(1 == 0);
#endif
    break;
  case FALSE:
    /* No literal in the clause. */
    break;
  }
}

void produceclausesTseitin(formulaclass class) {
  int type;
  fma *f;
  int aux;

#ifdef ASSERTS
  assert(xstackptr >= -1);
  assert(xclauselen >= 0);
  assert(xclauselen < MAXXCLAUSELEN);
  assert(xstackptr < MAXXSTACK);
#endif
  
  while(xstackptr >= 0) {
    /* Pop  x <-> formula from stack and generate clauses. */
    aux = xstackv[xstackptr];
    f = xstack[xstackptr--];

    xclauselen = 0;

    type = f->t;

    /* First disjunct to The Long Clause. */

    switch(type) {
    case disj:
      xclause[xclauselen++] = aux|NEGtag;	/* aux -> l1 V .. V ln */
      break;
    case conj:
      xclause[xclauselen++] = aux;	/* l1 & .. & ln -> aux */
      break;
    default:
      assert(1 == 0);
    }

    /* Generate aux <-> (lit) clauses, and add literals to The Long Clause. */

    pcTseitinRecurse(class,type,aux,f->juncts);

    /* Emit The Long Clause. */

    emitclause(xclause,xclauselen,class);

#ifdef ASSERTS
    assert(xclauselen < MAXXCLAUSELEN);
    assert(xstackptr < MAXXSTACK);
#endif
    
  }
}

void pcTseitinRecurse(int class,int type, int aux, fmalist *fs) {
  fma *f;
  int aux2;
  int c2lause[2];

  while(fs != NULL) {

#ifdef ASSERTS
    assert(xclauselen < MAXXCLAUSELEN);
    assert(xstackptr < MAXXSTACK);
#endif

    f = fs->hd;

    switch(f->t) {

    case conj:

      if(type == conj) pcTseitinRecurse(class,type,aux,f->juncts);
      else {
	aux2 = allocAUX(1);

	xclause[xclauselen++] = AUX(aux2);

	c2lause[0] = aux;
	c2lause[1] = AUX(aux2)|NEGtag;
	emitclause(c2lause,2,class);

	xstack[++xstackptr] = f;
	xstackv[xstackptr] = AUX(aux2);
      }
      break;

    case disj:

      if(type == disj) pcTseitinRecurse(class,type,aux,f->juncts);
      else {
	aux2 = allocAUX(1);

	xclause[xclauselen++] = AUX(aux2)|NEGtag;

	c2lause[0] = aux|NEGtag;
	c2lause[1] = AUX(aux2);
	emitclause(c2lause,2,class);

	xstack[++xstackptr] = f;
	xstackv[xstackptr] = AUX(aux2);
      }
      break;

    case patom:

      if(type == disj) {

	xclause[xclauselen++] = f->a;

	c2lause[0] = aux;
	c2lause[1] = f->a|NEGtag;

      } else {

	xclause[xclauselen++] = (f->a)|NEGtag;

	c2lause[0] = aux|NEGtag;
	c2lause[1] = f->a;

      }

      emitclause(c2lause,2,class);

      break;

    case natom:

      if(type == disj) {

	xclause[xclauselen++] = (f->a)|NEGtag;

	c2lause[0] = aux;
	c2lause[1] = f->a;

      } else {

	xclause[xclauselen++] = f->a;

	c2lause[0] = aux|NEGtag;
	c2lause[1] = f->a|NEGtag;

      }

      emitclause(c2lause,2,class);

      break;

    case TRUE:
      /* Clause is TRUE: don't generate it!!!!!!!!!!!!!!!!!!!!!!!! */
      assert(1 == 0);
      break;
    case FALSE: break;
      assert(1 == 0);
    }

    fs = fs->tl;

  }


}

/* Count the size of the CNF (# of clauses) with the trivial
   transformation based on associativity laws and no auxiliary
   variables.
THIS IS USELESS BECAUSE, WITH 32 BIT INTEGERS, IT OVERFLOWS WITH
MANY NON-STRIPS PROBLEMS, ESPECIALLY ONES THAT CONTAIN QUANTIFICATION.
*/

//int trivialsize(fma *f) {
//  fmalist *fs;
//  int c;
//  if(f==NULL) return 1;
//  switch(f->t) {
//  case TRUE:
//  case FALSE:
//    return 1;
//  case patom:
//  case natom:
//    return 1;
//  case conj:
//    fs = f->juncts;
//    c = 1;
//    while(fs != NULL) {
//      c += trivialsize(fs->hd);
//      fs = fs->tl;
//    }
//    return c;
//  case disj:
//    fs = f->juncts;
//    if(fs == NULL) return 1;
//    c = 1;
//    while(fs != NULL) {
//      c = c * trivialsize(fs->hd);
//      fs = fs->tl;
//    }
//    return c;
//  }
//}

/* Test whether formula is likely to lead clause sets bigger than bound. */

int biggerthan0(fma *f,int bound,int *size) {
  fmalist *fs;
  int size0;

  if(f==NULL) {
    *size = 1;
    return 1;
  }

  switch(f->t) {

  case TRUE:
  case FALSE:
  case patom:
  case natom:
    *size = 1;
    return 0;

  case conj:

    fs = f->juncts;
    *size = 0;
    while(fs != NULL) {
      if(biggerthan0(fs->hd,bound,&size0)) return 1;
      *size += size0;
      if(*size > bound) return 1;
      fs = fs->tl;
    }
    return 0;

  case disj:

    fs = f->juncts;
    *size = 1;
    while(fs != NULL) {
      if(biggerthan0(fs->hd,bound,&size0)) return 1;
      *size *= size0;
      if(*size > bound) return 1;
      fs = fs->tl;
    }
    return 0;
  }

  return 0;
}

int biggerthan(fma *f,int bound) {
  int guesstimate;
  if(biggerthan0(f,bound,&guesstimate) ||
     (guesstimate > bound)) return 1;
  else return 0;
}


#define MAXLITERALSCL 2000000
int clauselist[MAXLITERALSCL];
int clausealloc;

/* Trivial CNF transformation by recursively translating subformulas
to clauses, and then recursively combining the clause sets.
For a conjunction, the clauseset is simply the union of the constituent
clause sets.
For a disjunction, the clauseset is the "Cartesian product" of the
clause sets.
*/

void csproduct(int f0,int l0,int f1,int l1,int *f2,int *l2) {
  int i,j,k;
  *f2 = clausealloc;
  *l2 = clausealloc-1;
  i = f0;
  while(i <= l0) {
    j = f1;
    while(j <= l1) {
      /* New clause obtained by concatenation. */
      *l2 = clausealloc;	/* Index of the last clause generated */
      clauselist[clausealloc++] = clauselist[i]+clauselist[j];
      for(k=1;k<=clauselist[i];k++) clauselist[clausealloc++] = clauselist[i+k];
      for(k=1;k<=clauselist[j];k++) clauselist[clausealloc++] = clauselist[j+k];
      j += clauselist[j]+1;
    }
    i += clauselist[i]+1;
  }
#ifdef ASSERTS
  assert(clausealloc < MAXLITERALSCL);
#endif
}

int copyclauses(int first,int last) {
  int i,tmp;
  tmp = clausealloc;
  i = first;
  while(i <= last+clauselist[last]) {
    clauselist[clausealloc++] = clauselist[i++];
#ifdef ASSERTS
    assert(clausealloc < MAXLITERALSCL);
#endif
  }
  return tmp+(last-first);
}

void csconcatenate(int f0,int l0,int f1,int l1,int *f2,int *l2) {
  *f2 = clausealloc;
  copyclauses(f0,l0);
  *l2 = copyclauses(f1,l1);
  return;
}

int onlyliterals(fmalist *fs) {
  while(fs != NULL) {
    switch(fs->hd->t) {
    case patom:
    case natom:
      break;
    default:
      return 0;
    }
    fs = fs->tl;
  }
  return 1;
}

/* Translation from circuits to CNF */

void pc30(fma *f,formulaclass cl,int *first,int *last) {
  fmalist *fs;
  int f0,l0,f1,l1,f2,l2,len;
  switch(f->t) {
  case disj:
    fs = f->juncts;
    if(onlyliterals(fs)) {
      *first = clausealloc;
      *last = clausealloc;
      clausealloc += 1;
      len = 0;
      while(fs != NULL) {
	len += 1;
	switch(fs->hd->t) {
	case patom:
	  clauselist[clausealloc++] = fs->hd->a;
	  break;
	case natom:
	  clauselist[clausealloc++] = fs->hd->a|NEGtag;
	  break;
	default:
	  assert(1 == 0);
	}
	fs = fs->tl;
      }
      clauselist[*first] = len;
    } else {
      pc30(fs->hd,cl,&f0,&l0);
      fs = fs->tl;
      while(fs != NULL) {	/* Repeatedly construct the product. */
	pc30(fs->hd,cl,&f1,&l1);
	csproduct(f0,l0,f1,l1,&f2,&l2);
	f0 = f2;
	l0 = l2;
	fs = fs->tl;
      }
      *first = f0;
      *last = l0;
    }
    return;
  case conj:
    fs = f->juncts;
    if(fs == NULL) {	/* Empty conjunction is the empty clause set. */
      *first = 0;
      *last = -1;
      return;
    }
    pc30(fs->hd,cl,&f0,&l0);
    fs = fs->tl;
    while(fs != NULL) {	/* Repeatedly concatenate. */
      pc30(fs->hd,cl,&f1,&l1);
      csconcatenate(f0,l0,f1,l1,&f2,&l2);
      f0 = f2;
      l0 = l2;
      fs = fs->tl;
    }
    *first = f0;
    *last = l0;
    return;
  case patom:	/* Clause with one positive literal */
    *first = clausealloc;
    *last = clausealloc;
    clauselist[clausealloc] = 1;
    clauselist[clausealloc+1] = f->a;
    clausealloc += 2;
#ifdef ASSERTS
    assert(clausealloc < MAXLITERALSCL);
#endif
    break;
  case natom:	/* Clause with one negative literal */
    *first = clausealloc;
    *last = clausealloc;
    clauselist[clausealloc] = 1;
    clauselist[clausealloc+1] = f->a|NEGtag;
    clausealloc += 2;
#ifdef ASSERTS
    assert(clausealloc < MAXLITERALSCL);
#endif
    break;
  case TRUE:	/* No clauses. */
    *first = 0;
    *last = -1;
    break;
  case FALSE:	/* One empty clause */
    *first = clausealloc;
    *last = clausealloc;
    clauselist[clausealloc++] = 0;
#ifdef ASSERTS
    assert(clausealloc < MAXLITERALSCL);
#endif
    break;
  }
}

void produceclausesENUMERATIVE(fma *f,formulaclass cl) {
  int first,last,c,len;
  clausealloc = 0;
  pc30(f,cl,&first,&last);
  c = first;
  while(c <= last) {
    len = clauselist[c];
    emitclause(clauselist+c+1,len,cl);
    c += len+1;
  }
}

/*******************************************************************/
/*      DIMACS interface                                           */
/*******************************************************************/

void outputDIMACS() {
  int i,j,k,ptr,h,with,len,bias;
  int nOfInvariants;
  FILE *F;
  char filename[1000];

  printf("DIMACS output\n");

  /* Count how many invariant clauses will be output later. */

  nOfInvariants = 0;

  for(k=0;k<nOfAtoms;k++) {
    nOfInvariants += IScard(twolits[fePLIT(k)]);
    nOfInvariants += IScard(twolits[feNLIT(k)]);
  }

  for(i=firstTimePoint;i<=lastTimePoint;i+=outputTimeStep) { /* Write files for different lengths. */
    if(filenamebase) {
      sprintf(filename,"%s.%.3i.cnf",filenamebase,i);
    } else {
      sprintf(filename,"%s-%s.%.3i.cnf",domainname(),problemname(),i);
    }
    printf("Writing %s",filename);
#ifdef __LP64__
    F = fopen(filename,"w");
#else
    F = fopen64(filename,"w");
#endif
    fprintf(F,"p cnf %i %i\n",varsPerTime*(i+1)-nOfActions,nOfClauses+(i-1)*nOfTClauses+i*nOfInvariants/2);
    for(j=0;j<=i;j++) { /* Go through time points for one formula. */
      printf(" %i",j); fflush(stdout);
      ptr = 0;
      bias = j*varsPerTime;
      for(k=0;k<nOfClauses;k++) { /* Output clauses for each time point. */
	with = 0;
	len = clauseset[ptr]&LENBITS;
	switch(clauseset[ptr]&TIMEtags) { /* 1st element = size, timepoints */
	case TRtag: if(j < i) with = 1; break;
	case INITtag: if(j == 0) with = 1; break;
	case GOALtag: if(j == i) with = 1; break;
	default: fprintf(stderr,"ERROR: 56567\n"); exit(1); break;
	}
	ptr += 1;
	if(with) {
	  for(h=ptr;h<ptr+len;h++) {
	    if(clauseset[h] < 0) fprintf(F,"%i ",clauseset[h]-bias);
	    else fprintf(F,"%i ",clauseset[h]+bias);
	  }
	  fprintf(F,"0\n");
	}
	ptr += len;
      }
      /* Output invariants. (They are not in clauseset). */
      if(j>0) {
	for(k=0;k<nOfAtoms;k++) {
	  ITstart(twolits[fePLIT(k)]); /* invariants k V l */
	  while(ITnext(&h)) {
	    if(feVAR(h) < k) { /* Only output one of l1 V l2 and l2 V l1. */
	      if(h&1) fprintf(F,"%i -%i 0\n",k+1+bias,feVAR(h)+1+bias);
	      else fprintf(F,"%i %i 0\n",k+1+bias,feVAR(h)+1+bias);
	    }
	  }
	  ITstart(twolits[feNLIT(k)]); /* invariants -k V l */
	  while(ITnext(&h)) {
	    if(feVAR(h) < k) { /* Only output one of l1 V l2 and l2 V l1. */
	      if(h&1) fprintf(F,"-%i -%i 0\n",k+1+bias,feVAR(h)+1+bias);
	      else fprintf(F,"-%i %i 0\n",k+1+bias,feVAR(h)+1+bias);
	    }
	  }
	}
      }
    }
    printf("\n");
    fclose(F);
  }
}


/*******************************************************************/
/*       Call to the Integrated SAT solver                         */
/*******************************************************************/

/* Encoding in CNF has earlier been generated by encoding(). */

/* Map literals from 1,-1,2,-2,... to 0,1,2,3,... */

int nsatlit(int l) {
  if(l < 0) return ((-l-1) << 1)|1;
  return ((l-1) << 1);
}

satinstance outputNSAT(int id,int timepoints,int TRonly) {
  int j,k,ptr,h,len;
  clausetype ct;
  satinstance sati;

  sati = newinstance(id,timepoints,varsPerTime,nOfAtoms,nOfActions);
  noT2clauses = (id > 0);
  setheuristic(sati,SATheuristic);
  setpheuristic(sati,PLANheuristic);

  ptr = 0;

  for(k=0;k<nOfClauses;k++) { /* Output clauses. */

    len = clauseset[ptr]&LENBITS;

    switch(clauseset[ptr]&TIMEtags) {
    case TRtag: ct = TransC; break;
    case INITtag: ct = InitC; break;
    case GOALtag: ct = FinalC; break;
    default: fprintf(stderr,"ERROR: 56567\n"); exit(1); break;
    }

    ptr += 1;

    if((TRonly == 0) || (ct == TransC)) {
      switch(len) {
      case 1: add1clause(sati,nsatlit(clauseset[ptr]),ct); break;
      case 2:
	add2clause(sati,nsatlit(clauseset[ptr]),nsatlit(clauseset[ptr+1]),ct);
	break;
      default:
	addnewclause(sati,len,ct);
	for(j=0;j<len;j++) {
	  addliteral(sati,j,nsatlit(clauseset[ptr+j]));
	}
	finishclause(sati);
      }
    }

    ptr += len;
  }

  /* Add invariants. */

  for(k=0;k<nOfAtoms;k++) {
    ITstart(twolits[fePLIT(k)]); /* invariants k V l */
    while(ITnext(&h)) {
      if(feVAR(h) < k) { /* Only output one of l1 V l2 and l2 V l1. */
	add2clause(sati,fePLIT(k),h,TransC);
      }
    }
    ITstart(twolits[feNLIT(k)]); /* invariants -k V l */
    while(ITnext(&h)) {
      if(feVAR(h) < k) { /* Only output one of l1 V l2 and l2 V l1. */
	add2clause(sati,feNLIT(k),h,TransC);
      }
    }
  }

  /* Add shortcut clauses. */

  for(k=0;k<nofshortcutclauses;k++) {
#ifdef PRINTSHORTCUTS
    printf("shortcut clause %i ",k);
    printlit(shortcutclauses[k].l1);
    printf(" V ");
    printlit(shortcutclauses[k].l2);
    printf("@%i",shortcutclauses[k].tdiff);
    printf("\n");
#endif
    if(shortcutclauses[k].tdiff >= 0) {
      add2clause(sati,shortcutclauses[k].l1,shortcutclauses[k].l2+2*sati->nOfVarsPerTime*shortcutclauses[k].tdiff,TransC);
    } else {
      add2clause(sati,shortcutclauses[k].l2,shortcutclauses[k].l1-2*sati->nOfVarsPerTime*shortcutclauses[k].tdiff,TransC);
    }
  }

  //  printf("Total of %i clauses.\n",clausecount);

#ifdef COSTS
  // Add action costs to the cost vector
  for(j=0;j<nOfActions;j++) {
    addtimedvarcost(sati,nOfAtoms+j,actions[j].cost);
    //    printf("Cost of action %i is %i.\n",j,actions[j].cost);
  }
#endif

  // Finish.
  instancecomplete(sati);
  if(noT2clauses) sati->al2its = seqs[id-1].sati->al2its;

  return sati;
}
