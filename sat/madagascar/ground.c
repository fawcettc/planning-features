
/*  2012 (C) Jussi Rintanen jrintanen.jr@gmail.com  */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "asyntax.h"
#include "tables.h"
#include "intsets.h"
#include "ordintsets.h"
#include "operators.h"
#include "main.h"
//#include "instantiation.h"

#define noDEBUG

/*****************************************************************************/
/*************************** Preprocess **************************************/
/*****************************************************************************/

int binding[200];
int nOfBindings;
int scope[200];

#ifdef CFMA
#include "Cground.c"
#endif

/* replace parameter variables by their index in the parameter list */

int NEWparamindex(int i,int qdepth) {
  int j;
  for(j=qdepth-1;j>=0;j--) {
    if(scope[j] == i) return -1-j;
  }
  fprintf(stderr,"ERROR: variable %s is not a parameter\n",symbol(i));
  exit(1);
}

/* This applies paramindex in the right places */

void NEWpreprocessatom(atom a,int qdepth) {
  int i;
  for(i=2;i<2+a[1];i++) {
    if(isvar(a[i])) {
      a[i] = NEWparamindex(a[i],qdepth);
    }
  }
}

/* This applies paramindex in the right places. */
/* For quantification, this replaces the quantified variables name
   with the next available integer index. */

void NEWpreprocessfma(Sfma *f,int qdepth) {
  Sfmalist *l;
  switch(Sfmatypeof(f)) {
  case STRUE:
  case SFALSE:
    break;
  case Spatom: 
  case Snatom: 
    NEWpreprocessatom(f->a,qdepth);
    break;
  case Sdisj:
  case Sconj:
#ifdef CFMA
    f->cnt = listlen(f->juncts);
#endif
    l = f->juncts;
    while(l != NULL) {
      NEWpreprocessfma(l->hd,qdepth);
      l = l->tl;
    }
    break;
  case Sforall:
  case Sforsome:
    if(f->ss->tl) { /* Split multiple quantification. */
      Sfma *f1 = (Sfma*)malloc(sizeof(Sfma));
      f1->t = f->t;
      f1->ss = f->ss->tl;
      f1->f = f->f;

      f->ss->tl = NULL;
      f->f = f1;
    }
    scope[qdepth] = f->ss->v;
#ifdef DEBUG
    printf("scope[%i] = %s\n",qdepth,symbol(f->ss->v));
#endif
    f->ss->v = -1-qdepth;
    NEWpreprocessfma(f->f,qdepth+1);
    break;
  case Seq:
  case Sneq:
    if(isvar(f->p1)) f->p1 = NEWparamindex(f->p1,qdepth);
    if(isvar(f->p2)) f->p2 = NEWparamindex(f->p2,qdepth);
    break;
  }
}

/* This applies paramindex in the right places */

void NEWpreprocesseff(Seff *e,int qdepth) {
  Sfmalist *l;
  switch(e->t) {
  case SEpatom:
  case SEnatom:
    NEWpreprocessatom(e->a,qdepth);
    break;
  case SEconj:
    l = e->juncts;
    while(l != NULL) {
      NEWpreprocesseff(l->hd,qdepth);
      l = l->tl;
    }
    break;
  case SEforall:
    if(e->ss->tl) { /* Split multiple quantification. */
      Seff *e1 = (Seff*)malloc(sizeof(Seff));
      e1->t = SEforall;
      e1->ss = e->ss->tl;
      e1->effect = e->effect;

      e->ss->tl = NULL;
      e->effect = e1;
    }
    scope[qdepth] = e->ss->v;
#ifdef DEBUG
    printf("scope[%i] = %s\n",qdepth,symbol(e->ss->v));
#endif
    e->ss->v = -1-qdepth;
    NEWpreprocesseff(e->effect,qdepth+1);
    break;
  case SEwhen:
    NEWpreprocessfma(e->cond,qdepth);
    NEWpreprocesseff(e->effect,qdepth);
    break;
  }
}

void NEWpreprocessoperators() {
  int i,qdepth;
  typedvarlist *ps;

  for(i=0;i<nOfSActions;i++) {

#ifdef DEBUG
    printf("BEFORE:\n");
    if(flagShowInput) printSaction(&Sactions[i]);
#endif

    qdepth = 0;
    ps = Sactions[i].params;

    while(ps != NULL) {
#ifdef DEBUG
      printf("scope[%i] = %s\n",qdepth,symbol(ps->v));
#endif
      scope[qdepth++] = ps->v;
      ps = ps->tl;
    }

    //    printf("Qdepth = %i\n",qdepth);
    NEWpreprocessfma(Sactions[i].precon,qdepth);
    NEWpreprocesseff(Sactions[i].effect,qdepth);

#ifdef DEBUG
    printf("AFTER:\n");
#endif
    if(flagShowInput) printSaction(&Sactions[i]);
  }
  NEWpreprocessfma(Sgoal,0);
}


/***************************************************************************/
/********************************* Grounding *******************************/
/***************************************************************************/

Sfma *whenstack[1000]; /* Array for nested when-conditions */

int NEWnOfEffectLitsL(Sefflist *);

int NEWnOfEffectLits(Seff *se) {
  switch(se->t) {
  case SEpatom: return 1;
  case SEnatom: return 1;
  case SEconj: return NEWnOfEffectLitsL(se->juncts);
  case SEwhen: return 0;
  case SEforall: return (getdomainsize(se->ss->t)) * NEWnOfEffectLits(se->effect);
  }
  return 0;
}

int NEWnOfEffectLitsL(Sefflist *l) {
  if(l == NULL) return 0;
  return NEWnOfEffectLits(l->hd) + NEWnOfEffectLitsL(l->tl);
}

int *NEWinserteffectlitsL(int *,Sefflist *,int *);

int *NEWinserteffectlits(int *a,Seff *se,int *b) {
  int *vals;
  switch(se->t) {
  case SEpatom: *a = fePLIT(atomindex(se->a,b)); return a+1;
  case SEnatom: *a = feNLIT(atomindex(se->a,b)); return a+1;
  case SEconj: return NEWinserteffectlitsL(a,se->juncts,b);
  case SEwhen: return a;
  case SEforall:
    vals = getdomain(se->ss->t);
    while(*vals != -1) {
      b[-1-se->ss->v] = *vals;

      a = NEWinserteffectlits(a,se->effect,b);

      vals = vals + 1;
    }
    return a;

  default: return a;
  }
}

int *NEWinserteffectlitsL(int *a,Sefflist *l,int *b) {
  if(l == NULL) return a;
  return NEWinserteffectlitsL(NEWinserteffectlits(a,l->hd,b),l->tl,b);
}

int someunconditional(Seff *se) {
  Sefflist *ses;
  switch(se->t) {
  case SEconj:
    ses = se->juncts;
    while(ses != NULL) {
      if(someunconditional(ses->hd)) return 1;
      ses = ses->tl;
    }
    return 0;
  case SEpatom: return 1;
  case SEnatom: return 1;
  case SEwhen: return 0;
  case SEforall: return someunconditional(se->effect);
  default: return 0;
  }
}

fma *NEWgroundfma(Sfma *,int *);

eff *NEWlocateconditionals(Seff *se,int *b,eff *ac,int whennesting) {
  int *vals,i,*ptr;
  eff *e,*ac0;
  Sefflist *ses;

  switch(se->t) {

  case SEconj:
    ses = se->juncts;
    while(ses != NULL) {
      ac = NEWlocateconditionals(ses->hd,b,ac,whennesting);
      ses = ses->tl;
    }
    return ac;

  case SEwhen:
    e = (eff *)malloc(sizeof(eff));

    whenstack[whennesting] = se->cond;
    ac0 = NEWlocateconditionals(se->effect,b,ac,whennesting+1);

    if(se->cond->t == SFALSE) return ac0;
    if(!someunconditional(se->effect)) return ac0;

    if(whennesting == 0) { /* Non-nested when */

      e->condition = NEWgroundfma(se->cond,b);
#ifdef CFMA
      e->ccondition = Cgroundfma(se->cond,b);
      //      printcfma(e->ccondition);
#endif

    } else{ /* Nesting of 2 or more whens */

      fmalist *fs = NULL;
      for(i=0;i<=whennesting;i++) {
	fs = fmacons(NEWgroundfma(whenstack[i],b),fs);
      }
      e->condition = (fma *)malloc(sizeof(fma));
      e->condition->t = conj;
      e->condition->juncts = fs;
    }

    e->effectlits = (int *)malloc((NEWnOfEffectLits(se->effect)+1) * sizeof(int));
    ptr = NEWinserteffectlits(e->effectlits,se->effect,b);
    *ptr = -1;
    e->tl = ac0;
    return e;

  case SEforall:

    vals = getdomain(se->ss->t);

    while(*vals != -1) {
      b[-1-se->ss->v] = *vals;

      ac = NEWlocateconditionals(se->effect,b,ac,whennesting);

      vals = vals + 1;
    }
    return ac;

  default: return ac;
  }
}


void NEWgroundeff(Seff *se,int *b, eff *e) {
  int *ptr,cnt;
  //  eff *e = (eff *)malloc(sizeof(eff));
  e->condition = (fma *)malloc(sizeof(fma));
  e->condition->t = TRUE;
#ifdef CFMA
  e->ccondition = cTRUE;
#endif
  cnt = NEWnOfEffectLits(se);
  //  printf("There are %i effect literals: ",cnt);
  e->effectlits = (int *)malloc((cnt+1) * sizeof(int));
  ptr = NEWinserteffectlits(e->effectlits,se,b);
  *ptr = -1;
  //  printlitarr(e->effectlits);
  e->tl = NEWlocateconditionals(se,b,NULL,0);
}

fmalist *NEWgroundfmalist(Sfmalist *,int *);

fma *NEWgroundfma(Sfma *sf,int *b) {
  int *vals;
  fma *f = (fma *)malloc(sizeof(fma));

  switch(Sfmatypeof(sf)) {

  case STRUE: f->t = TRUE; break;
  case SFALSE: f->t = FALSE; break;

  case Sconj:
    f->t = conj;
    f->juncts = NEWgroundfmalist(sf->juncts,b);
    break;

  case Sdisj:
    f->t = disj;
    f->juncts = NEWgroundfmalist(sf->juncts,b);
    break;

  case Seq:
    if(bvalue(sf->p1,b) == bvalue(sf->p2,b)) {
      f->t = TRUE;
    } else {
      f->t = FALSE;
    }
    break;

  case Sneq:
    if(bvalue(sf->p1,b) == bvalue(sf->p2,b)) {
      f->t = FALSE;
    } else {
      f->t = TRUE;
    }
    break;

  case Spatom:
    f->t = patom;
    f->a = atomindex(sf->a,b);
    break;

  case Snatom:
    f->t = natom;
    f->a = atomindex(sf->a,b);
    break;

  case Sforall:  /* Iterate over all values of the variable. */

    f->t = conj;
    f->juncts = NULL;

    vals = getdomain(sf->ss->t);

    while(*vals != -1) {
      b[-1-sf->ss->v] = *vals;
      f->juncts = fmacons(NEWgroundfma(sf->f,b),f->juncts);
      vals = vals + 1;
    }
    break;

  case Sforsome: /* Iterate over all values of the variable. */

    f->t = disj;
    f->juncts = NULL;

    vals = getdomain(sf->ss->t);

    while(*vals != -1) {
      b[-1-sf->ss->v] = *vals;
      f->juncts = fmacons(NEWgroundfma(sf->f,b),f->juncts);
      vals = vals + 1;
    }
    break;
  }
  return f;
}

fmalist *NEWgroundfmalist(Sfmalist *l,int *b) {
  if(l == NULL) return NULL;
  return fmacons(NEWgroundfma(l->hd,b),NEWgroundfmalist(l->tl,b));
}

/* Is it a variable, and not assigned? */

inline int assignedvar(int v,int i) {
  if(v < 0 && (-1-v) <= i) return 1;
  else return 0;
}

/* Check all static atomic conjuncts of precon to found out whether the bindings
   until parameter i are compatible with the initial state. */

inline int staticp(int i) {
  return index2stentry[i]->staticpredicate;
}

/*
  Generate bindings so that the formula f is not trivially violated by
  the true literals in the initial state in the sense that there is a positive
  literal as a conjunct of f that is false in the initial state.

  How is this done? 
 */

/* 
   Test whether the formula f with the current partial binding is compatible
   with the true literals in the initial state.
   This is only tested for positive literals appearing as conjuncts of
   the formula. All such literals must match the initial state.
 */

int legalstaticbindingA(int i,int *a) {
  int j;
  atom *as;

  /* Go through the atoms in the initial state description, and check. */
  as = Sinit;
  if(staticp(a[0]) == 0) return 1;
  while(*as != NULL) {  /* Go through all initial state atoms. */

#ifdef DEBUG
    printf("Matching ");
    printSfma(f);
    printf(" against ");
    printatom(*as);
    printf(" with");
    for(j=0;j<=i;j++) {
      printf(" #%i:%s",j,symbol(binding[j]));
    }
    printf("\n");
#endif

    if((*as)[0] == a[0]) { /* Same predicate. Binding OK? */
      for(j=2;j<a[1]+2;j++) { /* Go through parameters. */
	/* Is it unassigned or a match. */
	if(assignedvar(a[j],i) && ((*as)[j] != binding[-1-a[j]])) {
	  goto nextinitatom; /* Did not match. */
	}
      }
#ifdef DEBUG
      printf("MATCH!\n");
#endif
      return 1;
    }
  nextinitatom:
    as = as  + 1;
  }
#ifdef DEBUG
  printf("NO MATCH!\n");
#endif
  return 0;
}

int legalstaticbinding(int i,Sfma *f) {
  Sfmalist *fs;

  switch(f->t) {

  case Spatom: return legalstaticbindingA(i,f->a);

  case Sconj:
    fs = f->juncts;
    while(fs != NULL) {
      if(legalstaticbinding(i,fs->hd) == 0) return 0;
      fs = fs->tl;
    }

  default: return 1;
  }
  return 1;
}

#define noNEWSTATICB
#ifdef NEWSTATICB
int litcnt;
int *trueposlits[1000];
int relevantbindings[100000];

/* General procedure for identifying relevant bindings.
Check every conjunct of the precondition and every true variable in
the initial state, and check if there is a match, binding the current
parameter.
Match the first literal first, to identify a candidate value.
If there is a second (and further literals), check whether the match
is good.
 */

void identifyposlits(int i,Sfma *f) {
  Sfmalist *fs;
  int j;

  switch(f->t) {
  case Spatom:
    if(!staticp(f->a[0])) return;
    for(j=0;j<f->a[1];j++) {
      if(f->a[j+2] == -1-i) {
	trueposlits[litcnt++] = f->a;
	printatom(f->a);
	return;
      }
    }
    return;
  case Sconj:
    fs = f->juncts;
    while(fs != NULL) {
      identifyposlits(i,fs->hd);
      fs = fs->tl;
    }
    return;

  default: return;
  }
}

int match(int *patom,int *initlit,int param,int *value) {
  int i;
  *value = -1;

  if(initlit[0] != patom[0]) return 0; /* Wrong predicate */
  if(initlit[1] != patom[1]) return 0; /* Wrong arity */

  for(i=0;i<initlit[1];i++) {
    if(assignedvar(patom[i+2],param-1) && (binding[-1-patom[i+2]] != initlit[i+2])) return 0;
    if(patom[i+2] == -1-param) *value = initlit[i+2];
  }
  assert(*value != -1);
  return 1;
}

void findrelevantbindings(int i,Sfma *f) {
  int cnt,j;
  int value;
  atom *as;

  litcnt = 0;
  cnt = 0;

  /* Identify literals that have to be matched. */

  printf("Positive literals with parameter %i are:",i);

  identifyposlits(i,f);
  assert(litcnt > 0);

  printf("\n");

  /* Match first lit with the initial state to obtain a binding, and
     verify that others match with this binding. */

  printf("Relevant bindings for parameter %i are...\n",i);

  as = Sinit;

  while(*as != NULL) {
    printf("Trying match with "); printatom(*as); printf(":");
    if(match(trueposlits[0],*as,i,&value)) { /* There is a match. */
      for(j=0;j<cnt;j++) {
	if(relevantbindings[j] == value) goto hadalready;
      }
      relevantbindings[cnt++] = value;
      printf(" %s OK",symbol(relevantbindings[cnt-1]));
    }

    hadalready:
    printf("\n");

    as = as + 1;
  }

  printf("\n");

  relevantbindings[cnt] = -1; /* The list is terminated with -1. */
}
#endif


/* produce list with parameter values */

void copybindings(int *dest,int *binding,int bindings) {
  int i;
  for(i=0;i<bindings;i++) dest[i] = binding[i];
  dest[bindings] = -1;
}

/* Go through all bindings.
   i   which variable to bind (0..nOfBindings-1)
   sc  which schema are we instantiating
   domains[]           the values for each of the variables 0..nOfBindings-1
   staticrestriction   whether variable i is restricted by a static fact
*/


void NEWgothrough(int i,int sc,int **domains,int *staticrestriction) {
  if(i < nOfBindings) { /* base case, instantiate */
    int *l = domains[i]; /* Values in the domain for the ith variable. */

    /* Some of the variables are limited by their occurrence in a static
       predicate that is a necessary precondition. In those cases go
       only through the allowed values of the variable. */

    if(staticrestriction[i]) { /* Restricted by a static predicate. */

#ifdef NEWSTATICB
      /* Find relevant bindings by one traversal of the initial literals. */

      findrelevantbindings(i,Sactions[sc].precon);
      l = &relevantbindings;
#endif

      /* PROBLEM: This can be really bad. Why don't you just generate
	 sensible bindings by going through the initial state, rather
	 than go through all possible domain values and test for each
	 whether it is sanctioned by the initial state? */

      while(*l != -1) {

	binding[i] = *l;
	//	printf("(%s)",symbol(l->hd));
#ifdef DEBUG
	printf("----------------------------------\n");
#endif

#ifdef NEWSTATICB
	NEWgothrough(i+1,sc,domains,staticrestriction);
#else
	if(legalstaticbinding(i,Sactions[sc].precon)) { /* Legal binding? */
	  NEWgothrough(i+1,sc,domains,staticrestriction);
	}
#endif

	l = l + 1;
      }
    } else {

      /* Value not restricted by a static predicate. */

      while(*l != -1) {
	binding[i] = *l;
	//	printf("(%s)",symbol(l->hd));
	NEWgothrough(i+1,sc,domains,staticrestriction);
	l = l + 1;
      }
    }
  } else {

#ifdef DEBUG
    printf("INSTANTIATE\n");
#endif

    nOfActions += 1;

    if(nOfActions >= maxActions) {
      maxActions = 2*maxActions;
      actions = (action *)realloc(actions,maxActions * sizeof(action));
    }

    actions[nOfActions-1].name = (int *)malloc((nOfBindings+2) * sizeof(int));
    actions[nOfActions-1].name[0] = Sactions[sc].name;
    copybindings(actions[nOfActions-1].name+1,binding,nOfBindings);

    actions[nOfActions-1].precon = NEWgroundfma(Sactions[sc].precon,binding);
#ifdef CFMA
    actions[nOfActions-1].cprecon = Cgroundfma(Sactions[sc].precon,binding);
    //    printcfma(actions[nOfActions-1].cprecon);
#endif
    NEWgroundeff(Sactions[sc].effect,binding,&(actions[nOfActions-1].effects));
    actions[nOfActions-1].cost = Sactions[sc].cost;

    //    printaction(nOfActions-1);
  }

}

/* Does parameter i occur in a static positive literal, a conjunct of f? */

int occursinstatic(int i,Sfma *f) {
  Sfmalist *fs;
  int j;

  switch(f->t) {
  case Spatom:
    if(!staticp(f->a[0])) return 0;
    for(j=0;j<f->a[1];j++) {
      if(f->a[j+2] == -1-i) {
	return 1;
      }
    }
    return 0;
  case Sconj:
    fs = f->juncts;
    while(fs != NULL) {
      if(occursinstatic(i,fs->hd)) return 1;
      fs = fs->tl;
    }
    return 0;

  default: return 0;
  }
}

void NEWgroundoperators() {
  int i,j;
  int *domains[1000];
  int binding[1000];
  int staticrestriction[1000];
  atom *al;

  NEWpreprocessoperators();

  initactions(); /* initialize the ground action data structure */
  initatomtable(); /* initialize the tables for atoms */

  for(i=0;i<nOfSActions;i++) {
    typedvarlist *params = Sactions[i].params;
    typedvarlist *l = params;

    if(flagShowInput) {
      printf("Grounding schema %i:%s\n",i,symbol(Sactions[i].name));
      printSaction(&Sactions[i]);
    }

    /* Fetch domains of the parameters */
    nOfBindings = 0;
    while(l != NULL) {
      staticrestriction[nOfBindings] = occursinstatic(nOfBindings,Sactions[i].precon);
#ifdef DEBUG
      if(staticrestriction[nOfBindings]) {
	printf("Parameter %i is static.\n",nOfBindings);
	printSaction(&Sactions[i]);
      } else { printf("."); }
#endif
#ifdef ASSERTS
      assert(isvar(l->v));
#endif
      domains[nOfBindings] = getdomain(l->t);
      nOfBindings += 1;
      l = l->tl;
    }

#ifdef ASSERTS
    assert(nOfBindings < 100);
#endif

    /* Go through all parameter assignments and ground */

    NEWgothrough(0,i,domains,staticrestriction);

  }

  goal = NEWgroundfma(Sgoal,binding);

  /* Go through the initial state description to assign
     indices to initial state atoms. */

  al = Sinit;
  while(*al != NULL) {
    atomindex(*al,NULL);
    al = al + 1;
  }

  initialstate = (int *)malloc(sizeof(int) * nOfAtoms);
  for(i=0;i<nOfAtoms;i++) initialstate[i] = 0;

  al = Sinit;
  while(*al != NULL) {
    j = atomindex(*al,NULL);
    initialstate[j] = 1;

#ifdef ASSERTS
    assert(j>=0); assert(j<nOfAtoms);
#endif

    al = al + 1;
  }

}
