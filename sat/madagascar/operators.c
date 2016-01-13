
/*  2012 (C) Jussi Rintanen jrintanen.jr@gmail.com */

#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

#include "main.h"
#include "asyntax.h"
#include "intsets.h"
#include "ordintsets.h"
#include "operators.h"
#include "tables.h"
#include "invariants.h"

#define noASSERTS
#define noDEBUG

/* Local copies (for inlining) of intsets.c functions */

int *jITptr;
int jITcounter;

void jITstart(intset s) {
  jITcounter = s->nOfEls;
  jITptr = s->elements;
}

int jITnext(int *i) {
  if(jITcounter <= 0) return 0;
  jITcounter -= 1;
  *i = *(jITptr++);
  return 1;
}

fmalist *fmacons(fma *h,fmalist *t) {
  fmalist *r = (fmalist *)statmalloc(4,sizeof(fmalist));
  r->hd = h;
  r->tl = t;
  return r;
}

void initactions() {
  nOfActions = 0;
  maxActions = 100000;
  actions = (action *)statmalloc(5,maxActions * sizeof(action));
}

fma *Fconj(fmalist *fs) {
  fma *f;

  if(fs == NULL) { /* No conjuncts */
    f = (fma *)statmalloc(6,sizeof(fma));
    f->t = TRUE;
  } else if(fs->tl == NULL) { /* Only one conjunct */
    return fs->hd;
  } else {
    f = (fma *)statmalloc(7,sizeof(fma));
    f->t = conj;
    f->juncts = fs;
  }
  return f;
}

/* Test whether a formula has disjunction in it. */

int disjunctivep(fma *f) {
  fmalist *l;
  switch(f->t) {
  case patom:
  case natom:
    return 0;
  case disj: return 1;
  case conj:
    l = f->juncts;
    while(l != NULL) {
      if(disjunctivep(l->hd)) return 1;
      l = l->tl;
    }
  }
  return 0;
}

fma *Fdisj(fmalist *fs) {
  fma *f;

  if(fs == NULL) { /* No disjuncts */
    f = (fma *)statmalloc(8,sizeof(fma));
    f->t = FALSE;
  } else if(fs->tl == NULL) { /* Only one disjunct */
    return fs->hd;
  } else {
    f = (fma *)statmalloc(9,sizeof(fma));
    f->t = disj;
    f->juncts = fs;
  }
  return f;
}

fma *Fconj2(fma *f1,fma *f2) {
  fma *f;

  f = (fma *)statmalloc(10,sizeof(fma));
  f->t = conj;
  f->juncts = fmacons(f1,fmacons(f2,NULL));

  return f;
}

fma *Fdisj2(fma *f1,fma *f2) {
  fma *f;

  f = (fma *)statmalloc(11,sizeof(fma));
  f->t = disj;
  f->juncts = fmacons(f1,fmacons(f2,NULL));

  return f;
}

fma *Fatom(int a) {
  fma *f = (fma *)statmalloc(12,sizeof(fma));
  f->t = patom;
  f->a = a;
  return f;
}

fma *Fnatom(int a) {
  fma *f = (fma *)statmalloc(13,sizeof(fma));
  f->t = natom;
  f->a = a;
  return f;
}

fma *Ffalse() {
  fma *f = (fma *)statmalloc(14,sizeof(fma));
  f->t = FALSE;
  return f;
}

fma *Ftrue() {
  fma *f = (fma *)statmalloc(15,sizeof(fma));
  f->t = TRUE;
  return f;
}

fma *Fimpl(fma *f1,fma *f2) {
  if(f1->t == TRUE) return f2;
  return Fdisj(fmacons(Fneg(f1),fmacons(f2,NULL)));
}

fma *Fneg(fma *f) {
  fmalist *l;
  fma *nf;
  nf = (fma *)statmalloc(16,sizeof(fma));

  switch(f->t) {

  case TRUE: nf->t = FALSE; break;
  case FALSE: nf->t = TRUE; break;

  case patom: nf->t = natom; nf->a = f->a; break;
  case natom: nf->t = patom; nf->a = f->a; break;

  case conj:
    nf->t = disj;
    l = f->juncts;
    nf->juncts = NULL;
    while(l != NULL) {
      nf->juncts = fmacons(Fneg(l->hd),nf->juncts);
      l = l->tl;
    }
    break;

  case disj:
    nf->t = conj;
    l = f->juncts;
    nf->juncts = NULL;
    while(l != NULL) {
      nf->juncts = fmacons(Fneg(l->hd),nf->juncts);
      l = l->tl;
    }
    break;
  }

  return nf;
}

/* Test whether a formula is true in a state. */


int ptruep(fma *f,int *state) {
  fmalist *fs;
  switch(f->t) {
  case natom: return (state[f->a] != 1);
  case patom: return (state[f->a] != 0);
  case disj:
    fs = f->juncts;
    while(fs != NULL) {
      if(ptruep(fs->hd,state)) return 1;
      fs = fs->tl;
    }
    return 0;
  case conj:
    fs = f->juncts;
    while(fs != NULL) {
      if(!ptruep(fs->hd,state)) return 0;
      fs = fs->tl;
    }
    return 1;
  case TRUE: return 1;
  case FALSE: return 0;
  }
  return 0;
}

/* Execute action in a state and modify the successor state.
*/

int execute(int a,int *state,int *state2) {
  eff *e;
  int *ls;

  if(!ptruep(actions[a].precon,state)) return 0;

  e = &(actions[a].effects);
  while(e != NULL) {
    if(ptruep(e->condition,state)) {
      ls = e->effectlits;
      while(*ls != -1) {
#ifdef DEBUG
	printf("Changing value of "); printatomi(feVAR(*ls)); printf(" TRUE\n");
#endif
	state2[feVAR(*ls)] = 1-((*ls)&1);
	ls = ls + 1;
      }
    }
    e = e->tl;
  }
  return 1;
}

void executeNOprecon(int a,int *state,int *state2) {
  eff *e;
  int *ls;

  e = &(actions[a].effects);
  while(e != NULL) {
    if(ptruep(e->condition,state)) {
      ls = e->effectlits;
      while(*ls != -1) {
	state2[feVAR(*ls)] = 1-((*ls)&1);
	ls = ls + 1;
      }
    }
    e = e->tl;
  }
}

/* Test whether o1 affects o2 in state. This means: is there an _active_
   effect of o1 that disables o2 or changes it's (conditional) effects. */

int opaffectsinstate(int *state,int o1,int o2) {
  eff *es;
  int *ls;

  es = &(actions[o1].effects);

  /* Go through all effects of o1. */
  while(es != NULL) {

    if(ptruep(es->condition,state)) { /* Only look at active effects. */

	ls = es->effectlits;
	while(*ls != -1) {
	  if(isaffectedby(o2,*ls)) return 1;
	  //	  printf("{"); printatomi((*ls) >> 1); printf("}");
	  ls = ls + 1;
	}

      }

    es = es->tl;
	
  }

  return 0;
}


/* Print various things. */

void printfmalist(fmalist *);
void printfma(fma *f) {
  switch(f->t) {
  case patom: printatomi(f->a); break;
  case natom: printf("(not "); printatomi(f->a); printf(")"); break;
  case conj:
    printf("(and ");
    printfmalist(f->juncts);
    printf(")");
    break;
  case disj:
    printf("(or ");
    printfmalist(f->juncts);
    printf(")");
    break;
  case TRUE:
    printf("TRUE"); break;
  case FALSE:
    printf("FALSE"); break;
  }
}

void printfmalist(fmalist *l) {
  if(l == NULL) return;
  printfma(l->hd);
  if(l->tl != NULL) printf(" ");
  printfmalist(l->tl);
}

void printeff(eff *e) {
  fma *c;
  int *ls;
  if(e == NULL) return;
  c = e->condition;
  if(c->t != TRUE) {
    printf("(when ");
    printfma(c);
  }
  ls = e->effectlits;
  while(*ls != -1) {
    printf(" ");
    if((*ls)&1) {
      printf("(not ");
      printatomi(feVAR(*ls));
      printf(")");
    } else {
      printatomi(feVAR(*ls));
    }
    ls = ls + 1;
  }
  if(c->t != TRUE) printf(")");
  printeff(e->tl);
}

int fprintactionname(FILE *f,int i) {
  int *l;
  int len;
  l = actions[i].name;
  fprintf(f,"%s(",symbol(*l));
  len = strlen(symbol(*l))+1;
  l = l + 1;
  while(*l != -1) {
    fprintf(f,"%s",symbol(*l));
    len += strlen(symbol(*l));
    if(*(l+1) != -1) {
      fprintf(f,",");
      len += 1;
    }
    l = l + 1;
  }
  fprintf(f,")");
  return len+1;
}

int printactionname(int i) {
  return fprintactionname(stdout,i);
}

int fprintactionnameIPC(FILE *f,int i) {
  int *l;
  int len;
  l = actions[i].name;
  fprintf(f,"(%s",symbol(*l));
  len = strlen(symbol(*l))+1;
  l = l + 1;
  while(*l != -1) {
    fprintf(f," %s",symbol(*l));
    len += strlen(symbol(*l));
    l = l + 1;
  }
  fprintf(f,")");
  return len+1;
}

int printactionnameIPC(int i) {
  return fprintactionnameIPC(stdout,i);
}

void printaction(int i) {
  int *l;
  /* Print operator name action(p1,...,pn) */
  l = actions[i].name;
  printf("ACTION %i:%s(",i,symbol(*l));
  l = l + 1;
  while(*l != -1) {
    printf("%s",symbol(*l));
    if(*(l+1) != -1) printf(",");
    l = l + 1;
  }
  printf(")      (COST %i)\n",actions[i].cost);
  /* Print precondition */
  printfma(actions[i].precon);
  printf("\n");
  /* Print effect */
  printeff(&(actions[i].effects));
  printf("\n");
}

/* Simplify a formula */

fmalist *allconjuncts(fmalist *fs,fmalist *ac) {
  while(fs != NULL) {
    if(fs->hd->t == conj) ac = allconjuncts(fs->hd->juncts,ac);
    else if(fs->hd->t != TRUE) ac = fmacons(fs->hd,ac);
    fs = fs->tl;
  }
  return ac;
}

fmalist *alldisjuncts(fmalist *fs,fmalist *ac) {
  while(fs != NULL) {
    if(fs->hd->t == disj) ac = alldisjuncts(fs->hd->juncts,ac);
    else if(fs->hd->t != FALSE) ac = fmacons(fs->hd,ac);
    fs = fs->tl;
  }
  return ac;
}

void simplifyfma(fma *f) {
  fmalist *fs;
  int trueone,falseone;
  switch(f->t) {
  case conj:
    falseone = 0;
    fs = f->juncts;
    while(fs != NULL) {
      simplifyfma(fs->hd);
      if(fs->hd->t == FALSE) { falseone = 1; break; }
      fs = fs->tl;
    }
    if(falseone) f->t = FALSE;
    else {
      f->juncts = allconjuncts(f->juncts,NULL);
      if(f->juncts == NULL) f->t = TRUE;
    }
    break;
  case disj:
    trueone = 0;
    fs = f->juncts;
    while(fs != NULL) {
      simplifyfma(fs->hd);
      if(fs->hd->t == TRUE) { trueone = 1; break; }
      fs = fs->tl;
    }
    if(trueone) f->t = TRUE;
    else {
      f->juncts = alldisjuncts(f->juncts,NULL);
      if(f->juncts == NULL) f->t = FALSE;
    }
    break;
  default:
    break;
  }
}

/* Simplify operator set */

void simplifyoperators() {
  int i,removed;
  removed = 0;
  i=0;
  while(i < nOfActions) {
    simplifyfma(actions[i].precon);
    if(actions[i].precon->t == FALSE) {
      actions[i] = actions[nOfActions-1];
      removed += 1;
      nOfActions -= 1;
    }
    i += 1;
  }
  if(debugOutput > 1)
    printf("Removed %i unapplicable actions.\n",removed);
}

/* Test whether a formula can make literal true */

int canmaketrue(int op,int l) {
  eff *effs;
  int *ls;
  effs = &(actions[op].effects);
  while(effs != NULL) {
    ls = effs->effectlits;
    while(*ls != -1) {
      if(*ls == l) return 1;
      ls = ls + 1;
    }
    effs = effs->tl;
  }
  return 0;
}

int occursin(int v,fma *f) {
  fmalist *fs;
  switch(f->t) {
  case conj:
  case disj:
    fs = f->juncts;
    while(fs != NULL) {
      if(occursin(v,fs->hd)) return 1;
      fs = fs->tl;
    }
    return 0;
  case natom:
  case patom:
    if(f->a == v) return 1;
    return 0;
  default:
    return 0;
  }
}

int Loccursin(int l,fma *f) {
  fmalist *fs;
  switch(f->t) {
  case conj:
  case disj:
    fs = f->juncts;
    while(fs != NULL) {
      if(Loccursin(l,fs->hd)) return 1;
      fs = fs->tl;
    }
    return 0;
  case natom:
    if(feNLIT(f->a) == l) return 1;
    return 0;
  case patom:
    if(fePLIT(f->a) == l) return 1;
    return 0;
  default:
    return 0;
  }
}

/* Test whether operator op is affected by literal l. */

int isaffectedby(int op,int l) {
  eff *effs;
  if(Loccursin(feNEG(l),actions[op].precon)) return 1;
  effs = &(actions[op].effects);
  while(effs != NULL) {
    if(occursin(feVAR(l),effs->condition)) return 1;
    effs = effs->tl;
  }
  return 0;
}

/* Test whether one operator affects the other.
 This is:
 o1 has an effect that falsifies the precondition of o2 or
 affects the lhs of a conditional effect of o2.
This must be in accordance with the computation of disabling graphs. */

int opaffects(int o1,int o2) {
  eff *es;
  //  intlist *vs;
  int *ls;

  es = &(actions[o1].effects);

  /* Go through all effects of o1. */
  while(es != NULL) {

    ls = es->effectlits;
    while(*ls != -1) {
      if(isaffectedby(o2,*ls)) return 1;
      ls = ls + 1;
    }

    es = es->tl;
  }

  return 0;
}

/* Test whether two operators can be concurrent, i.e. neither preconditions
   nor effects contradict each other. */

inline int Amember(int i,int *a) {
  while(*a != i) {
    if(*a == -1) return 0;
    a++;
  }
  return 1;
}

int parallel(int op1,int op2) {
  int *i,j;

  /* Preconditions contradict? */

  i = AnecessarypreconP[op1];
  while(*i != -1) { /* Go through operators positive precons. */
    if(Amember(*(i++),AnecessarypreconN[op2])) return 0; /* Direct conflict. */
  }
    
  i = AnecessarypreconN[op1];
  while(*i != -1) { /* Go through operators negative precons. */
    if(Amember(*(i++),AnecessarypreconP[op2])) return 0; /* Direct conflict. */
  }

  /* Effects contradict? */

  i = AforcedeffectsP[op1];
  while(*i != -1) { /* Go through operator's positive effects. */

    if(Amember(*i,AforcedeffectsN[op2])) return 0; /* Direct conflict. */

    /* Conflicts through a 2-literal invariant l1 | l2. */

    jITstart(twolits[feNLIT(*i)]);
    while(jITnext(&j)) {
      if((j&1) && Amember(feVAR(j),AforcedeffectsP[op2])) return 0;
      if((j&1) == 0 && Amember(feVAR(j),AforcedeffectsN[op2])) return 0;
    }

    i++;

  }

  i = AforcedeffectsN[op1];
  while(*i != -1) { /* Go through operator's negative effects. */

    if(Amember(*i,AforcedeffectsP[op2])) return 0; /* Direct conflict. */

    /* Conflicts through a 2-literal invariant l1 | l2. */

    jITstart(twolits[fePLIT(*i)]);
    while(jITnext(&j)) {
      if((j&1) && Amember(feVAR(j),AforcedeffectsP[op2])) return 0;
      if((j&1) == 0 && Amember(feVAR(j),AforcedeffectsN[op2])) return 0;
    }

    i++;

  }

  return 1;
}


/* Test whether an effect l can be concurrent with an operator,
   i.e. whether l contradicts the effects of the operator. */

int Lparallel(int l,int op2) {
  int j;

  if((l&1) == 0) { /* Literal is positive. */
    if(Amember(feVAR(l),AforcedeffectsN[op2])) { return 0; } /* Direct conflict. */

  } else { /* Literal is negative. */

    if(Amember(feVAR(l),AforcedeffectsP[op2])) { return 0; } /* Direct conflict. */

  }

  /* Conflicts through a 2-literal invariant l1 | l2. */

  jITstart(twolits[feNEG(l)]);
  while(jITnext(&j)) {
    if((j&1) && Amember(feVAR(j),AforcedeffectsP[op2])) { return 0; }
    if((j&1) == 0 && Amember(feVAR(j),AforcedeffectsN[op2])) { return 0; }
  }

  return 1;
}

/* Store literals occurring in a formula or in the formulas of an action
   in an ordintset. */

void Fcollectliterals(ordintset s,fma *f) {
  fmalist *fs;
  switch(f->t) {
  case conj:
  case disj:
    fs = f->juncts;
    while(fs != NULL) {
      Fcollectliterals(s,fs->hd);
      fs = fs->tl;
    }
    break;
  case natom:
  case patom:
    OSinsert(fePLIT(f->a),s);
    OSinsert(feNLIT(f->a),s);
    break;
  default: 1;
  }
}

void collectliterals(ordintset s,int op) {
  eff *effs;
  int *ls;

  Fcollectliterals(s,actions[op].precon);

  effs = &(actions[op].effects);

  while(effs != NULL) {

    Fcollectliterals(s,effs->condition);

    ls = effs->effectlits;
    while(*ls != -1) {
      OSinsert(*ls,s);
      ls = ls + 1;
    }

    effs = effs->tl;
  }

}

/* Replace static variables with truth values */

fma *simplifyfmastatic(fma *f) {
  fmalist *fs;
  fmalist **prev;
  int trueone,falseone;
  switch(f->t) {
  case conj:
    falseone = 0;
    fs = f->juncts;
    prev = &(f->juncts);
    while(fs != NULL) {
      fs->hd = simplifyfmastatic(fs->hd);
      if(fs->hd->t == FALSE) { falseone = 1; break; }
      if(fs->hd->t == TRUE) { *prev = fs->tl; } /* TRUE conjunct: remove */
      else prev = &(fs->tl);
      fs = fs->tl;
    }
    if(falseone) f->t = FALSE;
    if(f->juncts == NULL) f->t = TRUE;
    else if(f->juncts->tl == NULL) return f->juncts->hd;
    break;
  case disj:
    trueone = 0;
    fs = f->juncts;
    prev = &(f->juncts);
    while(fs != NULL) {
      fs->hd = simplifyfmastatic(fs->hd);
      if(fs->hd->t == TRUE) { trueone = 1; break; }
      if(fs->hd->t == FALSE) { *prev = fs->tl; } /* FALSE disjunct: remove */
      else prev = &(fs->tl);
      fs = fs->tl;
    }
    if(trueone) f->t = TRUE;
    if(f->juncts == NULL) f->t = FALSE;
    else if(f->juncts->tl == NULL) return f->juncts->hd;
    break;
  case patom:
    switch(onelits[f->a]) {
    case -1: break;
    case 0: f->t = FALSE; break;
    case 1: f->t = TRUE; break;
    }
    break;
  case natom:
    switch(onelits[f->a]) {
    case -1: break;
    case 1: f->t = FALSE; break;
    case 0: f->t = TRUE; break;
    }
    break;
  default:
    break;
  }
  return f;
}

/* Remove static effects from a list of effect literals. */

intlist *removeirrelevantlits(int *ls) {
  int *wp,*rp;
  wp = ls;
  rp = ls;
  while(1==1) {
    *wp = *rp;
    if(*wp == -1) break;
    if(onelits[feVAR(*wp)] == -1) wp = wp + 1; /* Irrelevant if onelits[*wp] == -1. */
    rp = rp + 1;
  }
}

eff *simplifyeffstatic(eff *e) {
  if(e == NULL) return NULL;
  e->condition = simplifyfmastatic(e->condition);
  if(e->condition->t == FALSE) return simplifyeffstatic(e->tl);
  else {
    removeirrelevantlits(e->effectlits);
    e->tl = simplifyeffstatic(e->tl);
    return e;
  }
}

#ifdef ASDFASDFASDFASDFASDFASDFASDFASDFASDFASDF
/* Check if a conjunction has two literals that conflict through a mutex. */
/* This is to eliminate actions with always-false preconditions. */

int conjunctof(fmalist *fs,int l) {
  int v;
  v = l >> 1;
  if(l&1) { /* Negative literal */
    while(fs != NULL) {
      if((fs->hd->t == patom) && (fs->hd->a == v)) {
#ifdef DEBUG
	printatomi(fs->hd->a); printf(" MUTEX CONTRADICTS WITH ");
#endif
	return 1;
      }
      fs = fs->tl;
    }
  } else { /* Positive literal */
    while(fs != NULL) {
      if((fs->hd->t == natom) && (fs->hd->a == v)) {
#ifdef DEBUG
	printf("NOT "); printatomi(fs->hd->a); printf(" MUTEX CONTRADICTS WITH ");
#endif
	return 1;
      }
      fs = fs->tl;
    }
  }
  return 0;
}

int conjunctof0(fmalist *fs,intset ls) {
  int l;
  jITstart(ls);
  while(jITnext(&l)) {
    if(conjunctof(fs,l)) return 1;
  }
  return 0;
}

int mutexcontradict(fma *f) {
  fmalist *fs;
  if(f->t ==  conj) {
    fs = f->juncts;
    while(fs != NULL) {
      switch(fs->hd->t) {
      case patom:
	if(conjunctof0(fs,twolits[feNLIT(fs->hd->a)])) {
#ifdef DEBUG
	  printatomi(fs->hd->a); printf("\n");
#endif
	  return 1;
	}
	break;
      case natom:
	if(conjunctof0(fs,twolits[fePLIT(fs->hd->a)])) {
#ifdef DEBUG
	  printf("\n"); printatomi(fs->hd->a); printf("\n");
#endif
	  return 1;
	}
	break;
      default: break;
      }
      fs = fs->tl;
    }
  }
  return 0;
}
#endif

int mutcon2(int l1,int l2) {
  int l;
  jITstart(twolits[feNEG(l1)]);
  while(jITnext(&l)) {
    if(l==feNEG(l2)) return 1;
  }
  return 0;
}

int mutcon(int l,fmalist *fs) {
  while(fs != NULL) {
    if(fs->hd->t == patom && mutcon2(l,fePLIT(fs->hd->a))) return 1;
    if(fs->hd->t == natom && mutcon2(l,feNLIT(fs->hd->a))) return 1;
    fs = fs->tl;
  }
  return 0;
}

int mutexcontradict2(fma *f) {
  fmalist *fs;
  if(f->t ==  conj) {
    fs = f->juncts;
    while(fs != NULL) {
      if(fs->hd->t == patom && mutcon(fePLIT(fs->hd->a),fs->tl)) return 1;
      if(fs->hd->t == natom && mutcon(feNLIT(fs->hd->a),fs->tl)) return 1;
      fs = fs->tl;
    }
  }
  return 0;
}


/* Replace static variables by T of F. */

void simplifyoperatorsstatic() {
  int i,removed;
  removed = 0;
  i=0;
  while(i < nOfActions) {
    simplifyeffstatic(&(actions[i].effects));
    actions[i].precon = simplifyfmastatic(actions[i].precon);
    if(mutexcontradict2(actions[i].precon)) {
#ifdef DEBUG
      printf("MUTEX precondition in action "); printaction(i);
#endif
      actions[i].precon->t = FALSE;
    }
    if(actions[i].precon->t == FALSE || actions[i].effects.condition->t == FALSE) {
      //      printf("REMOVING "); printaction(i);
      actions[i] = actions[nOfActions-1];
      removed += 1;
      nOfActions -= 1;
    } else i += 1;
  }
  if(debugOutput > 1 && removed) printf("Removed %i unapplicable actions.\n",removed);
}

void findfmaoccurrences(int op,fma *f,int polarity) {
  fmalist *fs;
  switch(f->t) {
  case conj:
  case disj:
    fs = f->juncts;
    while(fs != NULL) {
      findfmaoccurrences(op,fs->hd,polarity);
      fs = fs->tl;
    }
    break;
  case patom:
    if(polarity == 2) {
#ifdef DEBUG
      printatomi(f->a); printf(" occurs in ");
      printaction(op); printf("\n");
#endif
      OSinsert(op,preconoccP[f->a]);
    } else OSinsert(op,condocc[f->a]);
    break;
  case natom:
    if(polarity == 2) OSinsert(op,preconoccN[f->a]);
    else OSinsert(op,condocc[f->a]);
    break;
  default:
    break;
  }
}

/* Compute literals that are necessarily true when formula f is true.
This also takes into account known 2-literal invariants.
*/

void findnecessaryprecons(int i,fma *f) {
  int j;
  fmalist *fs;
  switch(f->t) {
  case patom:
    OSinsert(f->a,necessarypreconP[i]);
    OSinsert(i,necessarypreconofP[f->a]);
    jITstart(twolits[feNLIT(f->a)]);
    while(jITnext(&j)) {
      if(j&1) {
	OSinsert(feVAR(j),necessarypreconN[i]); /* Problem with Blai's example */
	OSinsert(i,necessarypreconofN[feVAR(j)]);
      } else {
	OSinsert(feVAR(j),necessarypreconP[i]); /* Problem with Blai's example */
	OSinsert(i,necessarypreconofP[feVAR(j)]);
      }
    }
    break;
  case natom:
    OSinsert(f->a,necessarypreconN[i]);
    OSinsert(i,necessarypreconofN[f->a]);
    jITstart(twolits[fePLIT(f->a)]);
    while(jITnext(&j)) {
      if(j&1) {
	OSinsert(feVAR(j),necessarypreconN[i]); /* Problem with Blai's example */
	OSinsert(i,necessarypreconofN[feVAR(j)]);
      } else {
	OSinsert(feVAR(j),necessarypreconP[i]); /* Problem with Blai's example */
	OSinsert(i,necessarypreconofP[feVAR(j)]);
      }
    }
    break;
  case conj:
    fs = f->juncts;
    while(fs != NULL) {
      findnecessaryprecons(i,fs->hd);
      fs = fs->tl;
    }
    break;
  case disj:
    break;
  case TRUE:
  case FALSE:
    break;
  }
}

void findoccurrences() {
  int i;
  eff *e;
  int always;

  /* Which operators do a variable occur in positively/negatively ? */
  effectoccP = (ordintset *)statmalloc(300,nOfAtoms * sizeof(ordintset));
  effectoccN = (ordintset *)statmalloc(300,nOfAtoms * sizeof(ordintset));

  preconoccP = (ordintset *)statmalloc(300,nOfAtoms * sizeof(ordintset));
  preconoccN = (ordintset *)statmalloc(300,nOfAtoms * sizeof(ordintset));

  condocc = (ordintset *)statmalloc(300,nOfAtoms * sizeof(ordintset));

  forcedeffectsP = (ordintset *)statmalloc(300,nOfActions * sizeof(ordintset));
  forcedeffectsN = (ordintset *)statmalloc(300,nOfActions * sizeof(ordintset));

  forcedeffectoccP = (ordintset *)statmalloc(300,nOfAtoms * sizeof(ordintset));
  forcedeffectoccN = (ordintset *)statmalloc(300,nOfAtoms * sizeof(ordintset));

  necessarypreconP = (ordintset *)statmalloc(300,nOfActions * sizeof(ordintset));
  necessarypreconN = (ordintset *)statmalloc(300,nOfActions * sizeof(ordintset));

  necessarypreconofP = (ordintset *)statmalloc(300,nOfAtoms * sizeof(ordintset));
  necessarypreconofN = (ordintset *)statmalloc(300,nOfAtoms * sizeof(ordintset));

  /* We use the ordintset data structure here because the sets
     involving operators will be ordered without additional
     ordering effort.
     FIX: The lists of literals need effort to order. Should
     these be represented by some other data structure for
     additional efficiency? */


  for(i=0;i<nOfAtoms;i++) {
    effectoccP[i] = OScreateSize(20);
    effectoccN[i] = OScreateSize(20);
    preconoccP[i] = OScreateSize(20);
    preconoccN[i] = OScreateSize(20);
    condocc[i] = OScreateSize(20);
  }

  for(i=0;i<nOfActions;i++) {
    forcedeffectsP[i] = OScreateSize(10);
    forcedeffectsN[i] = OScreateSize(10);

    necessarypreconP[i] = OScreateSize(30);
    necessarypreconN[i] = OScreateSize(30);
  }

  for(i=0;i<nOfAtoms;i++) {
    forcedeffectoccP[i] = OScreateSize(10);
    forcedeffectoccN[i] = OScreateSize(10);

    necessarypreconofP[i] = OScreateSize(30);
    necessarypreconofN[i] = OScreateSize(30);
  }

  for(i=nOfActions-1;i>=0;i--) {

    /* Go through precondition */

    findnecessaryprecons(i,actions[i].precon);
    findfmaoccurrences(i,actions[i].precon,2);

    /* Go through effects and update effect occurrences */

    e = &(actions[i].effects);
    
    while(e != NULL) {
      int *l;

      findfmaoccurrences(i,e->condition,1);

      always = (e->condition->t == TRUE);

      l = e->effectlits;
      while(*l != -1) {
	if((*l)&1) {
	  OSinsert(i,effectoccN[feVAR(*l)]);
	  if(always) OSinsert(i,forcedeffectoccN[feVAR(*l)]);
	  if(always) OSinsert(feVAR(*l),forcedeffectsN[i]);
	} else {
	  OSinsert(i,effectoccP[feVAR(*l)]);
	  if(always) OSinsert(i,forcedeffectoccP[feVAR(*l)]);
	  if(always) OSinsert(feVAR(*l),forcedeffectsP[i]);
	}
	l = l + 1;
      }


      e = e->tl;
    }

  }

  constructoperatorarrays();
}

/* Sort actions alphabetically according to their name. */

int actionCmp(action *a1,action *a2) {
  int v;

  int *n1,*n2;
  n1 = a1->name;
  n2 = a2->name;
  while(*n1 != -1 && n2 != -1) {
    v = strcmp(symbol(*n1),symbol(*n2));
    if(v != 0) return v;
    n1 = n1 + 1; n2 = n2 + 1;
  }
  if(*n1 != -1) return 1;
  if(*n2 != -1) return 1;
  return 0;
}

void sortactions() {
  qsort(actions,nOfActions,sizeof(action),actionCmp);
}

/**************************************************************************/
/******************** Eliminate static variables **************************/
/**************************************************************************/


/* After detecting static variables, eliminate them so that the
variable numbering without the static variables is contiguous. */

void renamefma(fma *f,int *mapping) {
  fmalist *fs;
  switch(f->t) {
  case patom:
  case natom:
    f->a = mapping[f->a]; break;
  case conj:
  case disj:
    fs = f->juncts;
    while(fs != NULL) {
      renamefma(fs->hd,mapping);
      fs = fs->tl;
    }
    break;
  default: break;
  }
}

void renameeff(eff *e,int *mapping) {
  int *ls;
  while(e != NULL) {
    renamefma(e->condition,mapping);
    ls = e->effectlits;
    while(*ls != -1) {
      if((*ls)&1) *ls = feNLIT(mapping[feVAR(*ls)]);
      else *ls = fePLIT(mapping[feVAR(*ls)]);
      ls = ls + 1;
    }
    e = e->tl;
  }
}

void renameaction(action *a,int *mapping) {
  renamefma(a->precon,mapping);
  renameeff(&(a->effects),mapping);
}

void renametwolits(intset is,int *mapping) {
  int i;
  for(i=0;i<is->nOfEls;i++) {
    if(1&(is->elements[i])) {
      is->elements[i] = feNLIT(mapping[feVAR(is->elements[i])]);
    } else {
      is->elements[i] = fePLIT(mapping[feVAR(is->elements[i])]);
    }
  }
}

/* Remove static variables completely, to make the numbering of
   variables contiguous. */

void eliminatestaticvariables() {
  int i;
  int from,to;
  int NEWnOfAtoms;
  int mapping[nOfAtoms];

  /* Do the mapping: move a variable one step earlier if the preceding
     variable is a static one. */

  //  for(i=0;i<nOfAtoms;i++) mapping[i] = i;

  to = 0;
  for(from = 0;from<nOfAtoms;from++) {
    if(onelits[from] == -1) { /* Variable is not static. */
      mapping[from] = to;
      to += 1;
    } else {
      mapping[from] = -1;
    }
  }
  NEWnOfAtoms = to;

  /* Elimination requires
     - renaming of the variables in actions
     - restructuring the index->name symbol table
     - twolits
     Elimination happens after the actions and the goal formula have been
     simplified (i.e. static variables have been replaced by T or F.)
  */

  for(i=0;i<nOfActions;i++) renameaction(&(actions[i]),mapping);
  for(i=0;i<nOfAtoms;i++) {
    renametwolits(twolits[fePLIT(i)],mapping);
    renametwolits(twolits[feNLIT(i)],mapping);
  }

  goal = simplifyfmastatic(goal);

  goalisdisjunctive = disjunctivep(goal);
  if(goalisdisjunctive) printf("Goal: disjunctive\n");
  else printf("Goal: conjunctive\n");

  renamefma(goal,mapping);

  /* Move twolits' contents into place. */

  for(i=0;i<nOfAtoms;i++) {
    if(mapping[i] != -1) {
      //      assert(mapping[i] >= 0);
      //      printf("mapping[%i] = %i.\n",i,mapping[i]);
      twolits[fePLIT(mapping[i])] = twolits[fePLIT(i)];
      twolits[feNLIT(mapping[i])] = twolits[feNLIT(i)];
    }
  }

  /* Fix initial state description. */
  
  for(i=0;i<nOfAtoms;i++) {
    if(mapping[i] != -1) initialstate[mapping[i]] = initialstate[i];
  }

  /* Fix symbol table: state vars' indices have changed! */

  renameatomtable(nOfAtoms,mapping);

  //  printf("WAS %i vars and IS %i vars.\n",nOfAtoms,NEWnOfAtoms);

  nOfAtoms = NEWnOfAtoms;
}

/**************************************************************************/
/******************* Eliminate converse literals **************************/
/**************************************************************************/

void renamefmaL(fma *f,int *mapping) {
  fmalist *fs;
  switch(f->t) {
  case patom:
    if(mapping[f->a] != -1) {
      if(mapping[f->a] & 1) f->t = natom;
      f->a = (mapping[f->a] >> 1);
    }
    break;
  case natom:
    if(mapping[f->a] != -1) {
      if(mapping[f->a] & 1) f->t = patom;
      f->a = (mapping[f->a] >> 1);
    }
    break;
  case conj:
  case disj:
    fs = f->juncts;
    while(fs != NULL) {
      renamefmaL(fs->hd,mapping);
      fs = fs->tl;
    }
    break;
  default: break;
  }
}

/* Here, instead of renaming, we will just remove the effect, as
   the remaining variable will be changed anyway.
   Seems to be wrong.
*/

void renameeffL(eff *e,int *mapping) {
  int *readptr,*writeptr;
  while(e != NULL) {
    renamefmaL(e->condition,mapping);
    readptr = e->effectlits;
    writeptr = e->effectlits;
    while(*readptr != -1) {

      *writeptr = *readptr;

      if(mapping[feVAR(*readptr)] != -1) { /* Eliminate */
      } else { /* Keep */
	writeptr = writeptr + 1;
      }
      
      readptr = readptr + 1;

    }
    *writeptr = -1;
    e = e->tl;
  }
}

void eliminatefromtwolits(intset is,int *mapping) {
  int i,iread,iwrite;
  int removed;
  removed = 0;
  iread = 0; iwrite = 0;

  for(i=0;i<is->nOfEls;i++) {

    is->elements[iwrite] = is->elements[iread];

    if(mapping[feVAR(is->elements[iread])] != -1) { /* Eliminate */
      removed = removed + 1;
    } else {
      iwrite = iwrite + 1;
    }

    iread = iread + 1;
  }
  is->nOfEls = is->nOfEls-removed;
}

void deletetwolits(int l) {
  twolits[l]->nOfEls = 0;
}

void renameactionL(action *a,int *mapping) {
  renamefmaL(a->precon,mapping);
  renameeffL(&(a->effects),mapping);
}

/* Identify pairs of variables that always have the opposite truth value. */

void mergecontras() {
  int l0,l,l2,cnt;
  int i;
  int mapping[nOfAtoms];

  for(i=0;i<nOfAtoms;i++) mapping[i] = -1;

  cnt = 0;
  for(l0=0;l0<nOfAtoms;l0++) {
    l = fePLIT(l0);
    jITstart(twolits[l]);
    while(jITnext(&l2)) {
      if(feVAR(l) < feVAR(l2) && ISmember(feNEG(l),twolits[feNEG(l2)])) {
	//	if(flagShowInput) {
	//	  if(l&1) printf("NOT ");
	//	  printatomi(feVAR(l));
	//	  printf(" and ");
	//	  if(l2&1) printf("NOT ");
	//	  printatomi(feVAR(l2));
	//	  printf(" are converses.\n");
	//	}
	if((mapping[feVAR(l2)] == -1) ||
	   ((mapping[feVAR(l2)] >> 1) > feVAR(l))) {
	  mapping[feVAR(l2)] = ((l&1) == (l2&1)) + (feVAR(l) << 1);
	}
	cnt += 1;
      }
    }
  }
  if(flagShowInput) {
    printf("TOTAL OF %i CONVERSES FOR %i VARIABLES.\n",cnt,nOfAtoms);
    for(i=0;i<nOfAtoms;i++) { if(mapping[i] != -1) { printatomi(i); printf(" will be replaced by "); if(mapping[i] & 1) printf("NOT "); printatomi(mapping[i] >> 1); printf("\n"); } }
  }
  for(i=0;i<nOfActions;i++) renameactionL(&(actions[i]),mapping);
  for(i=0;i<nOfAtoms;i++) {
    if(mapping[i] != -1) { deletetwolits(fePLIT(i)); deletetwolits(feNLIT(i)); }
    eliminatefromtwolits(twolits[fePLIT(i)],mapping);
    eliminatefromtwolits(twolits[feNLIT(i)],mapping);
  }
  renamefmaL(goal,mapping);
}

/***************************************************************************/
/* Generate linear array representation of the main data structures here.  */
/***************************************************************************/

/* We will have an array representation of many of the lists in operators.h
  which were first constructed as linked lists. Linked lists have poor
  cache locality and using them has a relatively high performance penalty
  in many cases.
*/

void movearraydata(int index,ordintset *sourceset,int **destarray,int **fillptr) {
  int item;
  intlist *iterate;

  destarray[index] = *fillptr;

  OSstart(sourceset[index],&iterate);
  while(OSnext(&item,&iterate)) {
    *((*fillptr)++) = item;
  }
  *((*fillptr)++) = -1;

  OSmakeempty(sourceset[index]);
}

void constructoperatorarrays() {
  int allocsize;
  int i;
  int *fill;
  int *arrayfordata;

  /* Calculate the size of the array that is needed. */

  allocsize = 0;

  for(i=0;i<nOfAtoms;i++) { /* Go through state variable -indexed lists. */
    allocsize += OScard(effectoccP[i]);
    allocsize += OScard(effectoccN[i]);
    allocsize += OScard(condocc[i]);
    allocsize += OScard(preconoccP[i]);
    allocsize += OScard(preconoccN[i]);
  }

  allocsize += 5*nOfAtoms; /* space for end-of-array markers -1 */

  for(i=0;i<nOfActions;i++) { /* Go through action-indexed lists. */
    allocsize += OScard(necessarypreconP[i]);
    allocsize += OScard(necessarypreconN[i]);
    allocsize += OScard(forcedeffectsP[i]);
    allocsize += OScard(forcedeffectsN[i]);
  }

  allocsize += 6*nOfActions; /* space for end-of-array markers -1 */


  /* Allocate pointer arrays for actions and state variables. */
  
  AnecessarypreconP = (int **)statmalloc(300,nOfActions * sizeof(int *));
  AnecessarypreconN = (int **)statmalloc(301,nOfActions * sizeof(int *));
  AforcedeffectsP = (int **)statmalloc(302,nOfActions * sizeof(int *));
  AforcedeffectsN = (int **)statmalloc(303,nOfActions * sizeof(int *));
  
  AeffectoccP = (int **)statmalloc(304,nOfAtoms * sizeof(int *));
  AeffectoccN = (int **)statmalloc(305,nOfAtoms * sizeof(int *));
  ApreconoccP = (int **)statmalloc(306,nOfAtoms * sizeof(int *));
  ApreconoccN = (int **)statmalloc(307,nOfAtoms * sizeof(int *));
  Acondocc = (int **)statmalloc(308,nOfAtoms * sizeof(int *));

  arrayfordata = (int *)statmalloc(309,allocsize * sizeof(int));

#ifdef ASSERTS
  assert(arrayfordata != NULL);
#endif

  fill = arrayfordata;

  /* Fill the massive array, and put pointers to the individual atom's
     and actions's arrays. */

  for(i=0;i<nOfActions;i++) {
    movearraydata(i,necessarypreconP,AnecessarypreconP,&fill);
    movearraydata(i,necessarypreconN,AnecessarypreconN,&fill);
    movearraydata(i,forcedeffectsP,AforcedeffectsP,&fill);
    movearraydata(i,forcedeffectsN,AforcedeffectsN,&fill);
  }

  free(necessarypreconP);
  free(necessarypreconN);
  free(forcedeffectsP);
  free(forcedeffectsN);

  for(i=0;i<nOfAtoms;i++) {
    movearraydata(i,effectoccP,AeffectoccP,&fill);
    movearraydata(i,effectoccN,AeffectoccN,&fill);
    movearraydata(i,preconoccP,ApreconoccP,&fill);
    movearraydata(i,preconoccN,ApreconoccN,&fill);
    movearraydata(i,condocc,Acondocc,&fill);
  }

  free(effectoccP);
  free(effectoccN);
  free(preconoccP);
  free(preconoccN);
  free(condocc);

  //  for(i=0;i<nOfAtoms*2;i++) {
  //    movearraydata(i,preconocc,Apreconocc,&fill);
  //  }

}

/* Check if a formula is a conjunction of 1 or more atomic formulas. */

int conjunctivep(fma *f) {
  fmalist *fs;
  switch(f->t) {
  case disj: return 0;
  case conj:
    fs = f->juncts;
    while(fs != NULL) {
      if(!conjunctivep(fs->hd)) return 0;
      fs = fs->tl;
    }
  default: return 1;
  }
}

/* Check if a formula has a fixed truth-value (TRUE or FALSE).
   This is a simple syntactic test, not a full SAT/TAUT test. */

int constantp(fma *f) {
  fmalist *fs;
  switch(f->t) {
  case patom:
  case natom:
    return 0;
  case disj:
  case conj:
    fs = f->juncts;
    while(fs != NULL) {
      if(!constantp(fs->hd)) return 0;
      fs = fs->tl;
    }
    return 1;
  case TRUE:
  case FALSE:
    return 1;
  }
}

int STRIPSaction(int i) {
  eff *e;
  if(!conjunctivep(actions[i].precon)) return 0;
  e = &(actions[i].effects);
  while(e != NULL) {
    if(!constantp(e->condition)) return 0;
    e = e->tl;
  }
  return 1;
}

int CONJUNCTIVEaction(int i) {
  eff *e;
  if(!conjunctivep(actions[i].precon)) return 0;
  e = &(actions[i].effects);
  while(e != NULL) {
    if(!conjunctivep(e->condition)) return 0;
    e = e->tl;
  }
  return 1;
}

syntacticclass actionclass(int i) {
  eff *e;
  syntacticclass class;

  if(!conjunctivep(actions[i].precon)) return GeneralPDDL;
  e = &(actions[i].effects);

  class = STRIPS;
  while(e != NULL) {
    if(!conjunctivep(e->condition)) return GeneralPDDL;
    if(!constantp(e->condition)) class = Conjunctive;
    e = e->tl;
  }
  return class;
}

syntacticclass goalclass() {
  if(!conjunctivep(goal)) return GeneralPDDL;
  else return STRIPS;
}


/********************************************************************/
/******************* Ordered integer sets ***************************/
/********************************************************************/

intlist *freeels = NULL;

inline intlist *OScons(int v,intlist *l) {
  intlist *tmp;
  if(freeels != NULL) {
    tmp = freeels;
    freeels = (intlist *)(freeels->tl);
  } else {
    tmp = (intlist *)statmalloc(200,sizeof(struct _intlist));
  }
  tmp->hd = v;
  tmp->tl = l;
  return tmp;
}

/* Free a cons pair to be used by OScons later. */

inline void OSfree(intlist *l) {
  l->tl = freeels;
  freeels = l;
}

/* Really release all cons pairs allocated with OScons and freed by OSfree. */

void OSreleasefree() {
  intlist *l,*tmp;
  l = freeels;
  while(l != NULL) {
    tmp = l;
    l = l->tl;
    free(tmp);
  }
  freeels = NULL;
}

void OSfreeset(ordintset s) {
  OSfree(s->elements);
  free(s);
}

ordintset OScreate() {
  ordintset tmp;
  tmp = (ordintset)statmalloc(201,sizeof(struct _ordintset));
  tmp->nOfEls = 0;
  tmp->elements = NULL;
  return tmp;
}

ordintset OScreateSize(int i) { return OScreate(); }

inline int OScard(ordintset s) {
  return s->nOfEls;
}

inline int OSemptyp(ordintset s) {
  return (s->nOfEls == 0);
}

inline void OSmakeempty(ordintset s) {
  intlist *l,*tmp;
  s->nOfEls = 0;
  l = s->elements;
  s->elements = NULL;
  while(l != NULL) {
    tmp = l;
    l = l->tl;
    OSfree(tmp);
  }
}

inline void OSinsert(int v,ordintset s) {
  intlist **prev,*l;

  prev = &(s->elements);
  l = s->elements;
  while(l != NULL && l->hd < v) {
    prev = &(l->tl);
    l = l->tl;
  }

  if(l != NULL && l->hd == v) return;

  *prev = OScons(v,l);
  s->nOfEls += 1;
}

inline void OSremove(int v,ordintset s) {
  printf("ERROR: not implemented\n");
  exit(1);
}

inline void OSremoveSet(ordintset s1,ordintset s2) {
  intlist *l1,*l2,**prev,*tmp;

#ifdef DEBUG
  printf("REMOVE "); OSprint(s1);
  printf("FROM "); OSprint(s2);
#endif

  l1 = s1->elements;
  l2 = s2->elements;

  prev = &(s2->elements);

  while(l1 != NULL) {
    while(l2 != NULL && l1->hd > l2->hd) { /* Find location for element. */
      prev = &(l2->tl);
      l2 = l2->tl;
    }

    if(l2 == NULL) break;
    if(l1->hd == l2->hd) { /* Something to remove */
      tmp = l2;
      *prev = l2->tl;
      s2->nOfEls -= 1;
      l2 = l2->tl;
      OSfree(tmp);
    }
    l1 = l1->tl;
  }
  
#ifdef DEBUG
  printf("TO GET "); OSprint(s2);
  printf("\n");
#endif
}

inline void OS2removeSet(ordintset s1,ordintset s2) {
  intlist *l1,*l2,**prev,*tmp;

#ifdef DEBUG
  printf("REMOVE "); OSprint(s1);
  printf("FROM "); OSprint(s2);
#endif

  l1 = s1->elements;
  l2 = s2->elements;

  prev = &(s2->elements);

  while(l1 != NULL) {
    while(l2 != NULL && l1->hd > l2->hd) { /* Find location for element. */
      prev = &(l2->tl);
      l2 = l2->tl;
    }

    if(l2 == NULL) break;
    if(l1->hd == l2->hd) {
      tmp = l2;
      *prev = l2->tl;
      s2->nOfEls -= 1;
      l2 = l2->tl;
      OSfree(tmp);
    }
    l1 = l1->tl;
  }
  
#ifdef DEBUG
  printf("TO GET "); OSprint(s2);
  printf("\n");
#endif
}

/* Intersect set s1 with s2:    s1 := s1 /\ s2  */

inline void OSintersect(ordintset s1,ordintset s2) {
  intlist *l1,*l2,**prev,*tmp;

#ifdef DEBUG
  printf("INTERSECT "); OSprint(s1);
  printf("WITH "); OSprint(s2);
#endif

  l1 = s1->elements;
  l2 = s2->elements;

  prev = &(s1->elements);

  while(l1 != NULL) {
    while((l2 != NULL) && (l1->hd > l2->hd)) { /* Skip elements not in l1. */
      l2 = l2->tl;
    }

    if((l2 != NULL) && (l1->hd == l2->hd)) { /* Retain element. */

      prev = &(l1->tl);
      l1 = l1->tl;
      l2 = l2->tl;

    } else { /* Remove the first element of l1. */

      tmp = l1;
      *prev = l1->tl;
      s1->nOfEls -= 1;
      l1 = l1->tl;
      OSfree(tmp);

    }
  }
  
#ifdef DEBUG
  printf("TO GET "); OSprint(s1);
  printf("\n");
#endif
}


inline void OSaddelementsSTUPID(ordintset s1,ordintset s2) {
  intlist *l1;
  l1 = s1->elements;
  while(l1 != NULL) {
    OSinsert(l1->hd,s2);
    l1 = l1->tl;
  }
}

inline void OSaddelements(ordintset s1,ordintset s2) {
  intlist *l1,*l2,**prev,*tmp;

  //  printf("ADD "); OSprint(s1);
  //  printf("TO "); OSprint(s2);

  l1 = s1->elements;
  l2 = s2->elements;

  prev = &(s2->elements);

  while(l1 != NULL) {

    while(l2 != NULL && l1->hd > l2->hd) { /* Find location for element. */
      prev = &(l2->tl);
      l2 = l2->tl;
    }

    if(l2 == NULL || l1->hd < l2->hd) {
      tmp = OScons(l1->hd,l2);
      *prev = tmp;
      prev = &(tmp->tl);
      s2->nOfEls += 1;
    }
    l1 = l1->tl;
  }
  
  //  printf("TO GET "); OSprint(s2);
  //  printf("\n");
}

/* Iterator */

inline void OSstart(ordintset s,intlist **iterate) {
  *iterate = s->elements;
}

inline int OSnext(int *v,intlist **iterate) {
  if(*iterate != NULL) {
    *v = (*iterate)->hd;
    *iterate = (*iterate)->tl;
    return 1;
  } else {
    return 0;
  }
}


inline void OSprint(ordintset s) {
  intlist *l;
  l = s->elements;
  while(l != NULL) {
    printf(" %i",l->hd);
    l = l->tl;
  }
  printf("\n");
}
