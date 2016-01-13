
/* 2012 (C) Jussi Rintanen jrintanen.jr@gmail.com */

#include <stdio.h>

#include "main.h"
#include "asyntax.h"
#include "intsets.h"
#include "ordintsets.h"
#include "operators.h"

#define noDEBUG

int unconditional(int l,fma *f) {
  fmalist *fs;
  switch(f->t) {
  case disj:
    return 0;
  case conj:
    fs = f->juncts;
    while(fs != NULL) {
      if(unconditional(l,fs->hd)) return 1;
      fs = fs->tl;
    }
    return 0;
    break;
  case natom:
    if(feNLIT(f->a) == l) return 1;
    return 0;
    break;
  case patom:
    if(fePLIT(f->a) == l) return 1;
    return 0;
    break;
  default:
    return 0;
  }
  return 0;
}

int doesnothing(fma *p,eff *e) {
  int *l;
  while(e != NULL) {
    l = e->effectlits;
    while(*l != -1) {
      if(!unconditional(*l,p)) return 0;
      l = l + 1;
    }
    e = e->tl;
  }
  return 1;
}

/* Remove operators which don't do anything. */

void cleanupoperatorsNOOP() {
  int i;
  int removed;
  removed = 0;
  for(i=0;i<nOfActions;i++) {
  again:
    if(doesnothing(actions[i].precon,&(actions[i].effects))) {
      removed += 1;
      actions[i] = actions[nOfActions-1];
      nOfActions -= 1;
      if(i <= nOfActions-1) goto again;
    }
  }
  if(debugOutput > 1 && removed) printf("Removed %i actions with inconsistent effects.\n",removed);
}

/* Remove operators with inconsistent effects. */

int inconsistentp(int *ls) {
  int *i,*j;
  i = ls;
  while(*i != -1) {
    j = i+1;
    while(*j != -1) {
      if(*j == feNEG(*i)) return 1;
      j = j + 1;
    }
    i = i + 1;
  }
  return 0;
}

void cleanupoperators0() {
  int i;
  int removed;
  eff *e;
  removed = 0;
  for(i=0;i<nOfActions;i++) {
  again:
    e = &(actions[i].effects);
    while(e != NULL) {
      if(inconsistentp(e->effectlits)) {
	removed += 1;
	actions[i] = actions[nOfActions-1];
	nOfActions -= 1;
	if(i <= nOfActions-1) goto again;
      }
      e = e->tl;
    }
  }
  if(debugOutput > 1 && removed) printf("Removed %i actions with inconsistent effects.\n",removed);
}

/* Conform with funny PDDL semantics on actions that _simultaneously_
   set something both TRUE and FALSE. */

void removefrom(eff *e) {
  int *nptr;
  int *pptr = e->effectlits;
  while(*pptr != -1) {
    if(((*pptr)&1) == 0) { /* It's a positive literal. */
      nptr = e->effectlits;
      while(*nptr != -1) {
	if(*nptr == feNEG(*pptr)) { /* Remove positive literal's complement. */
	  while(*nptr != -1) {
	    *nptr = *(nptr+1);
	    nptr = nptr + 1;
	  }
	  pptr = e->effectlits;
	  break;
	}
	nptr = nptr + 1;
      }
    }
    pptr = pptr + 1;
  }
}

/* Standard PDDL behaviour: if both v:=0 and v:=1, then ignore v:=0. */

void cleanupoperators1() {
  int i;
  int removed;
  eff *e;
  removed = 0;
  for(i=0;i<nOfActions;i++) {
    e = &(actions[i].effects);
    while(e != NULL) {
      removefrom(e);
      e = e->tl;
    }
  }
  if(debugOutput > 1 && removed) printf("Removed %i actions with inconsistent effects.\n",removed);
}

/* Remove effects that are entailed by the precondition. */

int entailed(int l,fma *f) {
  fmalist *fs;

  switch(f->t) {

  case patom: return (l == fePLIT(f->a));
  case natom: return (l == feNLIT(f->a));

  case conj:
    fs = f->juncts;
    while(fs != NULL) {
      if(entailed(l,fs->hd)) return 1;
      fs = fs->tl;
    }
    return 0;
  default: return 0;
  }
}

int aseffect(int l,eff *effects) {
  int *es;

  while(effects != NULL) {
    es = effects->effectlits;
    while(*es != -1) {
      if(*es == l) return 1;
      es = es + 1;
    }
    effects = effects->tl;
  }
  return 0;
}

int a;

void removeredundante(eff *alleffects,eff *e,fma *f) {
  int *rp,*wp;

  rp = e->effectlits;
  wp = rp;

  while(*rp != -1) {

    *wp = *rp;

    if((!entailed(*wp,f) && !entailed(*wp,e->condition))
       || (aseffect(feNEG(*wp),alleffects))) {
      wp = wp + 1;
    } else {
#ifdef DEBUG
      printf("Removing effect ");
      if((*wp) & 1) printf("NOT ");
      printatomi(feVAR(*wp));
      printf(" in action %i\n",a);
#endif
    }
    rp = rp + 1;
  }
}

void removeredundanteffects() {
  int i;
  eff *e;
  for(i=0;i<nOfActions;i++) {
    a = i;
    e = &(actions[i].effects);
    while(e != NULL) {
      removeredundante(&(actions[i].effects),e,actions[i].precon);
      e = e->tl;
    }
  }
}

void cleanupoperators() {
  int i;
  if(flagPDDLadddel) cleanupoperators1();
  else cleanupoperators0();
  //  removeredundanteffects();
  cleanupoperatorsNOOP();
  //  printf("After simplifications: %i actions\n",nOfActions);

  if(planSemantics == EStepOgata) {
    /* Randomly shuffle the action array. */

    for(i=0;i<nOfActions;i++) {
      int *l;
      fma *f;
      eff e;
      int j;

      j = random() % nOfActions;

      l = actions[i].name;
      f = actions[i].precon;
      e = actions[i].effects;

      actions[i].name = actions[j].name;
      actions[i].precon = actions[j].precon;
      actions[i].effects = actions[j].effects;

      actions[j].name = l;
      actions[j].precon = f;
      actions[j].effects = e;
    }
  }

}
