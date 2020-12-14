
/* 2012 (C) Jussi Rintanen jrintanen.jr@gmail.com */

#include <stdio.h>
#include <stdlib.h>

#include "asyntax.h"
#include "intsets.h"
#include "ordintsets.h"
#include "operators.h"
#include "tables.h"
#include "invariants.h"
#include "main.h"

#define noDEBUG


/* Local copies (for inlining) of intsets.c functions */

int *iITptr;
int iITcounter;

inline void iITstart(intset s) {
  iITcounter = s->nOfEls;
  iITptr = s->elements;
}

inline int iITnext(int *i) {
  if(iITcounter <= 0) return 0;
  iITcounter -= 1;
  *i = *(iITptr++);
  return 1;
}

/* */

void printlitlist(intset s) {
  int i;
  iITstart(s);
  while(iITnext(&i)) {
    if(i&1) printf(" -");
    else printf(" ");
    printatomi(feVAR(i));
  }
}

void showInvariants() {
  int i,cntpersistent;

  cntpersistent = 0;
  printf("PERSISTENT LITERALS:"); fflush(stdout);
  for(i=0;i<nOfAtoms;i++) {
    if(onelits[i] == 1) { printf(" "); printatomi(i); }
    else if(onelits[i] == 0) { printf(" -"); printatomi(i); }
    if(onelits[i] != -1) cntpersistent += 1;
  }
  printf("\nThere are %i persistent literals (out of total of %i literals).\n",cntpersistent,nOfAtoms);

  printf("Invariants:\n");
  
  for(i=0;i<nOfAtoms;i++) {
    printatomi(i); printf(" OR:");
    printlitlist(twolits[fePLIT(i)]);
    printf("\n");
    
    printf("-"); printatomi(i); printf(" OR:");
    printlitlist(twolits[feNLIT(i)]);
    printf("\n");
  }
}

void showInvariantsBrief() {
  int i;
  printf("True literals:");
  for(i=0;i<nOfAtoms;i++) {
    if(onelits[i] == 1) { printf(" "); printatomi(i); }
    else if(onelits[i] == 0) { printf(" -"); printatomi(i); }
  }
  printf("\nTrue 2-literal clauses:\n");
  
  for(i=0;i<nOfAtoms;i++) {
    
    printatomi(i); printf(" OR ");
    printlitlist(twolits[fePLIT(i)]);
    printf("\n");
    
    printf("-"); printatomi(i); printf(" OR ");
    printlitlist(twolits[feNLIT(i)]);
    printf("\n");
  }
}



//#define iITnext ITnext
//#define iITstart ITstart

int *onelits;
intset *twolits;

/* Preprocessing for operators:
  For each operator and conditional effect compute

  A. list of literals guaranteed to be true before
     the conditional effect is executed

  B. list of literals guaranteed to be true after

Literals derived from the precondition are included in lists A.

If there are unconditional effects (condition TRUE) then
these are included in all lists B.

Literals in list A that are guaranteed not to be falsified
by a simultaneous conditional effect are included in B.

*/

typedef struct _llist {
  intset before;
  intset after;
}  llist;

/* Compute effect literals consisting of the positive, the negative
   and the ones in a conditional effect with an always-true condition. */

void addeffectlitsL(int *lits,eff *current,eff *all,intset s) {
  int *ptr;
  while(*lits != -1) { ISinsert(*lits,s); lits = lits + 1; }
  while(all != NULL) {
    if(all->condition->t == TRUE && all != current) {
      ptr = all->effectlits;
      while(*ptr != -1) {
	ISinsert(*ptr,s);
	ptr = ptr+1;
      }
    }
    all = all->tl;
  }
}

void guaranteedtrue(fma *f,intset ac) {
  fmalist *fs;
  switch(f->t) {
  case FALSE:
  case TRUE:
    break;
  case conj:
    fs = f->juncts;
    while(fs != NULL) {
      guaranteedtrue(fs->hd,ac);
      fs = fs->tl;
    }
    break;
  case disj: break;
  case patom: ISinsert(fePLIT(f->a),ac); break;
  case natom: ISinsert(feNLIT(f->a),ac); break;
  }
}

int nofcondeffs(eff *e) {
  int cnt;
  cnt = 0;
  while(e != NULL) {
    cnt = cnt + 1;
    e = e->tl;
  }
  return cnt;
}

llist **prepros; /* */

void preprocess() {
  int i,j,effcnt;
  intset preconlits;
  eff *e;

  prepros = (llist **)statmalloc(401,nOfActions * sizeof(llist *));
  preconlits = IScreate(1000);

  for(i=0;i<nOfActions;i++) {

    e = &(actions[i].effects);

    effcnt = nofcondeffs(e);
    
    prepros[i] = statmalloc(402,sizeof(llist) * effcnt);

#ifdef DEBUG
    printf("Preprocessing for operator %i:",i); fflush(stdout);
    printaction(i); fflush(stdout);
#endif

    ISmakeempty(preconlits);

    guaranteedtrue(actions[i].precon,preconlits);

    j = 0;

    while(e != NULL) { /* Go through the conditional effects */

      prepros[i][j].before = IScreateSize(10);
     
      guaranteedtrue(e->condition,prepros[i][j].before);
      ISaddelements(preconlits,prepros[i][j].before);

#ifdef DEBUG
      printf("BEFORE"); fflush(stdout);
      printlitlist(prepros[i][j].before); fflush(stdout);
      printf("\n"); fflush(stdout);
#endif

      prepros[i][j].after = IScreateSize(20);

      addeffectlitsL(e->effectlits,e,&(actions[i].effects),prepros[i][j].after);
#ifdef DEBUG
      printf("AFTER"); fflush(stdout);
      printlitlist(prepros[i][j].after); fflush(stdout);
      printf("\n\n"); fflush(stdout);
#endif

      e = e->tl;
      j = j + 1;
    }

  }
}

int **alleffectlits;

int nofeffectlits(eff *e) {
  int cnt = 0;
  int *ptr;

  while(e != NULL) {
    ptr = e->effectlits;
    while(*ptr != -1) {
      cnt = cnt + 1;
      ptr = ptr + 1;
    }
    e = e-> tl;
  }
  return cnt;
}

void preprocess2() {
  int i,sz;
  eff *e;
  int *ptr,*fill;

  alleffectlits = (int **)statmalloc(499,nOfActions * sizeof(int *));
  for(i=0;i<nOfActions;i++) {
    sz = 1 + nofeffectlits(&(actions[i].effects));
    alleffectlits[i] = (int *)statmalloc(498,sz * sizeof(int));
    fill = alleffectlits[i];
    e = &(actions[i].effects);
    while(e != NULL) {
      ptr = e->effectlits;
      while(*ptr != -1) {
	*fill = *ptr;
	fill = fill + 1;
	ptr = ptr + 1;
      }
      e = e->tl;
    }
    *fill = -1;
  }
}

#ifdef CFMA
inline int ctruep(cfma f) {

  switch(((int)f)&7) {

  case cNATOMtag: return (onelits[((int)f) >> 3] != 1);
  case cPATOMtag: return (onelits[((int)f) >> 3] != 0);
  case cTRUEtag: return 1;
  case cFALSEtag: return 0;

  default:
    
    if(((int)(*f))&1) { /* Conjunction */

      int i,cnt;
      cnt = ((int)(f[0])) >> 1;

      for(i=0;i<cnt;i++) {
	if(!ctruep(f[i+1])) return 0;
      }
      return 1;

    } else { /* Disjunction */

      int i,cnt;
      cnt = ((int)(f[0])) >> 1;

      for(i=0;i<cnt;i++) {
	if(ctruep(f[i+1])) return 1;
      }
      return 0;
    }
  }
  return 0;
}
#endif

int truep(fma *f) {
  fmalist *fs;
  switch(f->t) {
  case natom: return (onelits[f->a] != 1);
  case patom: return (onelits[f->a] != 0);
  case disj:
    fs = f->juncts;
    while(fs != NULL) {
      if(truep(fs->hd)) return 1;
      fs = fs->tl;
    }
    return 0;
  case conj:
    fs = f->juncts;
    while(fs != NULL) {
      if(!truep(fs->hd)) return 0;
      fs = fs->tl;
    }
    return 1;
  case TRUE: return 1;
  case FALSE: return 0;
  }
  return 0;
}

//int notmadefalse(int l,eff *e) {
//  int *ls;
//  while(e != NULL) {
//    ls = e->effectlits;
//    while(*ls != -1) {
//      if(l == feNEG(*ls)) return 0;
//      ls = ls + 1;
//    }
//    e = e->tl;
//  }
//  return 1;
//}

int madefalse(int l,int i) {
  int *ptr;
  ptr = alleffectlits[i];
  while(*ptr != -1) {
    if(*ptr == feNEG(l)) return 1; 
    ptr = ptr + 1;
  }
  return 0;
}

void removefalsified(eff *e,intset s) {
  int *ptr;
  while(e != NULL) {
    ptr = e->effectlits;
    while(*ptr != -1) { ISremove(feNEG(*ptr),s); ptr = ptr + 1; }
    e = e->tl;
  }
}

int localISmember0(int i,intset s) {
  int j;
  for(j=0;j<s->nOfEls;j++) {
    if(s->elements[j] == i) return 1;
  }
  return 0;
}

int localISmember1(int i,intset s) {
  int j;
  for(j=0;j<s->nOfEls;j++) {
    if(s->elements[j] == i) return 1;
  }
  return 0;
}

int localISmember2(int i,intset s) {
  int j;

  for(j=0;j<s->nOfEls;j++) {
    if(s->elements[j] == i) return 1;
  }
  return 0;
}

int localISmember3(int i,intset s) {
  int j;
  for(j=0;j<s->nOfEls;j++) {
    if(s->elements[j] == i) return 1;
  }
  return 0;
}

int wastruebefore(int l,intset before) {
  int i;
  //  if(localISmember(l,before)) return 1;
  /* Go through the relevant invariants. */
  for(i=0;i<before->nOfEls;i++) {
    if(before->elements[i] == l) return 1;
    if(localISmember0(l,twolits[feNEG(before->elements[i])])) return 1;
  }
  return 0;
}

void computeinvariants() {
  int i,iteration,change,j,k;
  eff *e;
  int *il;
  llist *prep;
  intset trueones,ext;
  int trueonesinitialized;

  preprocess();
  preprocess2();

  ext = IScreateSize(10000);

  trueones = IScreateSize(10000);

  onelits = (int *)statmalloc(403,sizeof(int) * nOfAtoms);
  twolits = (intset *)statmalloc(404,sizeof(intset) * nOfAtoms * 2);

  for(i=0;i<nOfAtoms;i++) {
    onelits[i] = initialstate[i];
    twolits[fePLIT(i)] = IScreate();
    twolits[feNLIT(i)] = IScreate();
  }

  if(flagNoInvariants) {
    for(i=0;i<nOfAtoms;i++) {
      onelits[i] = -1;
    }
    return;
  }

  printf("Invariants:");

  iteration = 0;
  change = 1;

  while(change) {

    printf(" %i",iteration); fflush(stdout);
    change = 0;

    for(i=0;i<nOfActions;i++) {

#ifdef DEBUG
      printf("\nConsidering action %i:",i); fflush(stdout);
      printaction(i);
      printf("\n");
#endif

	  /* Both the precondition and the cond. eff. antecedents are tested without looking at the mutexes: would not usually make a difference! */

#ifdef CFMA
      if(!ctruep(actions[i].cprecon)) continue; /* Not applicable (yet) */
#else
      if(!truep(actions[i].precon)) continue; /* Not applicable (yet) */
#endif

      /* Go through all first-time falsified literals:
	 weaken to all possible 2-literal clauses

	 Go through all 2-literal clauses with one disjunct falsified:
	 must the other disjunct be true?
      */

      e = &(actions[i].effects);

      /* prep is a list of known necessary preconditions and effects. */
      prep = prepros[i];

      while(e != NULL) {

	trueonesinitialized = 0;

#ifdef CFMA
	if(ctruep(e->ccondition)) {
#else
	if(truep(e->condition)) {
#endif

	  /* In the following:
	     We have newly true literals in prep->after and
	     all true literals in trueones.

	     For every l in prep->after and m in trueones, -l V m
             is an invariant.
	     These are all invariants involving -l.

	     We want to store all of these such that both -l and m
             can have both value true and false.
	   */

	  /* Go through effect literals */

	  il = e->effectlits;

	  while(*il != -1) {
	    int l;
	    l = *il;
	    il = il + 1;

	    /* See whether making literal l true falsifies something. */

	    if(onelits[feVAR(l)] == (l&1)) { /* Falsified a 1-literal */

	      if(trueonesinitialized == 0) {

		trueonesinitialized = 1;
		ISmakeempty(trueones);

		/* literals true because they are in the precondition */
		ISaddelements(prep->before,trueones);
	  
		/* literals true because a 2-literal clause is satisfied */
		iITstart(prep->before);
		while(iITnext(&j)) ISaddelements(twolits[feNEG(j)],trueones);

		/* Remove literals that are falsified by this conditional effect
		   or possibly by other conditional effects. */
		removefalsified(&(actions[i].effects),trueones);

		/* Add literals that are made true. */
		ISaddelements(prep->after,trueones);
	      }

	      change = 1;

	      onelits[feVAR(l)] = -1;

	      /* Add 2-literals -a | l */

	      iITstart(trueones);
	      while(iITnext(&k)) {
		if(l != k && (onelits[feVAR(k)] == -1 || (localISmember1(k,prep->after) && onelits[feVAR(k)] == (k&1)))) {
		  ISinsertNODUP(k,twolits[feNEG(l)]);
		  ISinsertNODUP(feNEG(l),twolits[k]);
		}
	      }
	    } else if(onelits[feVAR(l)] == -1) { /* Check preservation of 2-literal clauses */

	      /* Remove candidate 2-literal invariants which were falsified. */

	      IScopyto(twolits[feNEG(l)],ext);

	      iITstart(ext);
	      while(iITnext(&k)) {
		if(!(localISmember2(k,prep->after)
		     || (
			 wastruebefore(k,prep->before)
			 &&
			 !madefalse(k,i)
			 ))) {
		  change = 1;
		  ISremove(k,twolits[feNEG(l)]);
		  ISremove(feNEG(l),twolits[k]);
		}
	      }

	      /* If enabled a new state variable value (= invalidated
		 a candidate one-literal invariant), add new candidate
		 two-literal invariants that still remain true. */

	      iITstart(prep->after);
	      while(iITnext(&k)) {
		if(l != k && onelits[feVAR(k)] == -1 && localISmember3(k,twolits[feNEG(l)])) {
		  ISinsert(feNEG(l),twolits[k]);
		}
	      }

	    }

	  }

	}
	e = e->tl;
	prep++;
      }

      //      showInvariantsBrief();
    }

    iteration += 1;
  }

  for(i=0;i<nOfActions;i++) {
    //    ISfree(prepros[i].before);
    //    ISfree(prepros[i].after);
    free(prepros[i]);
    free(alleffectlits[i]);
  }

  free(prepros);
  free(alleffectlits);

  printf(" ");

  if(flagShowInput) showInvariants();
  
}
