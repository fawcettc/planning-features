
/* 2012 (C) Jussi Rintanen */

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

#define noDEBUG 1

#include "parser.tab.h"

//void printlitarr(int *ptr) {
//  if(*ptr == -1) { printf("NOTHING TO PRINT"); }
//  while(*ptr != -1) {
//    if((*ptr)&1) printf("NOT "); else printf(".");
//    printatomi((*ptr) >> 1);
//    ptr ++;
//  }
//  printf("\n");
//}

/* DESTRUCTIVE negation of a formula */

Sfma *Sneg(Sfma *f) {
  Sfmalist *l;
  switch(f->t) {
  case STRUE: f->t = SFALSE; break;
  case SFALSE: f->t = STRUE; break;
  case Spatom: f->t = Snatom; break;
  case Snatom: f->t = Spatom; break;
  case Sconj:
    f->t = Sdisj;
    l = f->juncts;
    while(l != NULL) {
      Sneg(l->hd);
      l = l->tl;
    }
    break;
  case Sdisj:
    f->t = Sconj;
    l = f->juncts;
    while(l != NULL) {
      Sneg(l->hd);
      l = l->tl;
    }
    break;
  case Sforall: f->t = Sforsome; Sneg(f->f); break;
  case Sforsome: f->t = Sforall; Sneg(f->f); break;
  case Seq: f->t = Sneq; break;
  case Sneq: f->t = Seq; break;
  }
  return f;
}

/* constructors for schematic formulae */

Sfma* Sdisjunction(Sfmalist *fs) {
  Sfma *f = (Sfma*)statmalloc(20,sizeof(Sfma));
  f->t = Sdisj;
  f->juncts = fs;
  return f;
}

Sfma* Sconjunction(Sfmalist *fs) {
  Sfma *f = (Sfma*)statmalloc(21,sizeof(Sfma));
  f->t = Sconj;
  f->juncts = fs;
  return f;
}

Sfma* Satom(atom a) {
  Sfma *f = (Sfma*)statmalloc(22,sizeof(Sfma));
  f->t = Spatom;
  f->a = a;
  return f;
}

Sfma* Sfalse() {
  Sfma *f = (Sfma*)statmalloc(23,sizeof(Sfma));
  f->t = SFALSE;
  return f;
}

Sfma* Strue() {
  Sfma *f = (Sfma*)statmalloc(24,sizeof(Sfma));
  f->t = STRUE;
  return f;
}

Sfma* Sfmaforall(typedvarlist *ss, Sfma *f) {
  Sfma *f1 = (Sfma*)statmalloc(25,sizeof(Sfma));
  f1->t = Sforall;
  f1->ss = ss;
  f1->f = f;
  return f1;
}

Sfma* SconstantTRUE() {
  Sfma *f = (Sfma*)statmalloc(26,sizeof(Sfma));
  f->t = STRUE;
  return f;
}

Sfma* Sfmaforsome(typedvarlist *ss, Sfma *f) {
  Sfma *f1 = (Sfma*)statmalloc(27,sizeof(Sfma));
  f1->t = Sforsome;
  f1->ss = ss;
  f1->f = f;
  return f1;
}

Sfma* SfmaEQ(int p1, int p2) {
  Sfma *f1 = (Sfma*)statmalloc(28,sizeof(Sfma));
  f1->t = Seq;
  f1->p1 = p1;
  f1->p2 = p2;
  return f1;
}

/******* Accessors ********/

Sfmatype Sfmatypeof(Sfma *f) {
  return f->t;
}

//atom *makeatom(int pr,intlist *pars) {
//  atom a = (atom)statmalloc(29,sizeof(atom));
//  a->pred = pr;
//  a->params = pars;
//  return a;
//}

/* Printing */

void printSfmalist(Sfmalist *);
void printSefflist(Sefflist *);

void printatom(atom a) {
  int n,i;
  printf("%s(",symbol(a[0]));
  n = a[1];
  for(i=2;i<n+2;i++) {
    if(a[i] < 0) printf("#%i",-1-(a[i]));
    else printf("%s",symbol(a[i]));
    if(i<n+1) printf(",");
  }
  printf(")");
}

void printtypedvars(typedvarlist *ss) {
  printf(" (");
  while(ss != NULL) {
    printf("%s:%s",symbol(ss->v),symbol(ss->t));
    if(ss->tl != NULL) printf(" ");
    ss = ss->tl;
  }
  printf(")");
}

void printSfma(Sfma *f) {
  switch(Sfmatypeof(f)) {
  case STRUE: printf("TRUE"); break;
  case SFALSE: printf("FALSE"); break;
  case Seq: printf(" (= %s %s)",symbol(f->p1),symbol(f->p2)); break;
  case Sneq: printf(" (not (= %s %s))",symbol(f->p1),symbol(f->p2)); break;
  case Spatom: printatom(f->a); break;
  case Snatom: printf("(not "); printatom(f->a); printf(")"); break;
  case Sdisj: printf("(or "); printSfmalist(f->juncts); printf(")"); break;
  case Sconj: printf("(and "); printSfmalist(f->juncts); printf(")"); break;
  case Sforall: printf("(forall "); printtypedvars(f->ss); printSfma(f->f); printf(")"); break;
  case Sforsome: printf("(exists "); printtypedvars(f->ss); printSfma(f->f); printf(")"); break;
    
  }
}

void printSfmalist(Sfmalist *fs) {
  while(fs != NULL) {
    printSfma(fs->hd);
    printf(" ");
    fs = fs->tl;
  }
}

void printSeff(Seff *);
void printSefflist(Sefflist *fs) {
  while(fs != NULL) {
    printSeff(fs->hd);
    printf(" ");
    fs = fs->tl;
  }
}

void printSeff(Seff *e) {
  switch(e->t) {
  case SEpatom: printatom(e->a); break;
  case SEnatom: printf("(not "); printatom(e->a); printf(")"); break;
  case SEconj: printf("(and "); printSefflist(e->juncts); printf(")"); break;
  case SEforall: printf("(forall "); printtypedvars(e->ss); printSeff(e->effect); printf(")"); break;
  case SEwhen:
    printf("(when ");
    printSfma(e->cond);
    printf(" ");
    printSeff(e->effect);
    printf(")");
    break;
  }
}

void printSaction(Saction *a) {
  typedvarlist *l;
  printf(":action %s(",symbol(a->name));
  l = a->params;
  while(l != NULL) {
    printf("%s",symbol(l->v));
    if(l->t) printf(":%s",symbol(l->t));
    else printf(":UNIV");
    if(l->tl != NULL) printf(" ");
    l = l->tl;
  }
  printf(")    (COST %i)\n",a->cost);
  printSfma(a->precon);
  printf("\n");
  printSeff(a->effect);
  printf("\n\n");
}

/* constructors for schematic effects */

Seff* SPeffatom(atom a) {
  Seff *e = (Seff *)statmalloc(30,sizeof(Seff));
  e->t = SEpatom;
  e->a = a;
  return e;
}

Seff* SNeffatom(atom a) {
  Seff *e = (Seff *)statmalloc(31,sizeof(Seff));
  e->t = SEnatom;
  e->a = a;
  return e;
}


Seff* Seffconjunction(Sefflist *efs) {
  Seff *e = (Seff *)statmalloc(32,sizeof(Seff));
  e->t = SEconj;
  e->juncts = efs;
  return e;
}

Seff* Seffwhen(Sfma *c,Seff *e) {
  Seff *e1 = (Seff *)statmalloc(33,sizeof(Seff));
  e1->t = SEwhen;
  e1->cond = c;
  e1->effect = e;
  return e1;
}

Seff* Seffforall(typedvarlist *p,Seff *e) {
  Seff *e1 = (Seff *)statmalloc(34,sizeof(Seff));
  e1->t = SEforall;
  e1->ss = p;
  e1->effect = e;
  return e1;
}

int listlen(intlist *l) {
  int len = 0;
  while(l != NULL) {
    len = len+1;
    l = l->tl;
  }
  return len;
}

/* Create atom */

atom newatom(int s,intlist *p) {
  int len,i;
  int *a;
  len = listlen(p);
  a = (atom)statmalloc(35,sizeof(int) * (len+2));
  a[0] = s;
  a[1] = len;
  i = 2;
  while(p != NULL) {
    a[i++] = p->hd;
    p = p->tl;
  }
  return a;
}

/* PDDL domain definitions */

int nOfTypes;

#define MAXOBTYPES 1000
obtype Stypes[MAXOBTYPES];
int *AStypes[MAXOBTYPES];
int *AStypesCARD[MAXOBTYPES];

#define MAXSCHEMATICACTIONS 10000

Sfma *Sgoal;

void initPDDL() {
  nOfSActions = 0;
  maxSActions = MAXSCHEMATICACTIONS;
  Sactions = (Saction *)statmalloc(36,sizeof(Saction) * maxSActions);
  nOfTypes = 0;
  Sgoal = (Sfma *)0;
  Sactions[0].precon = NULL;
  Sactions[0].effect = NULL;
  Sactions[0].params = NULL;
  Sactions[0].cost = 0.0;
}

/* Definitions */


/* Typed var lists */

typedvarlist *TVappend(typedvarlist *l1,typedvarlist *l2) {
  if(l1 == NULL) {
    return l2;
  } else {
    typedvarlist *l3 = TVappend(l1->tl,l2);
    typedvarlist *l4 = (typedvarlist *)statmalloc(37,sizeof(typedvarlist));
    l4->v = l1->v;
    l4->t = l1->t;
    l4->tl = l3;
    return l4;
  }
}

/* For a (possibly untyped) list of variables, assign a type */

typedvarlist *withtype(int t,intlist *ss) {
  typedvarlist *l;
  if(ss == NULL) return NULL;
  l = (typedvarlist *)statmalloc(38,sizeof(typedvarlist));
  l->v = ss->hd;
  l->t = t;
  l->tl = withtype(t,ss->tl);
  return l;
}

/* Add a new action */

void checkSactionsSize() {
  if(nOfSActions >= maxSActions-1) {
    maxSActions = maxSActions * 2;
    Sactions = (Saction *)realloc(Sactions,maxSActions * sizeof(Saction));
    assert(Sactions != NULL);
  }
}

void addnewaction(int name) {
  nOfSActions += 1;
  checkSactionsSize();
  Sactions[nOfSActions-1].name = name;
  if(Sactions[nOfSActions-1].effect == NULL) {
    fprintf(stderr,"ERROR: action has not effect.\n");
    exit(1);
  }
  if(Sactions[nOfSActions-1].precon == NULL) {
    Sactions[nOfSActions-1].precon = SconstantTRUE();
  }
  /* Next action */
  Sactions[nOfSActions].precon = NULL;
  Sactions[nOfSActions].effect = NULL;
  Sactions[nOfSActions].params = NULL;
  Sactions[nOfSActions].cost = 0.0;
}

/* The following three are called by the parser BEFORE addnewaction */

void addactionparameters(typedvarlist *params) {
  Sactions[nOfSActions].params = params;
}

void addactionprecond(Sfma *p) {
  Sactions[nOfSActions].precon = p;
}

void addactioncost(int cost) {
  //  printf("Action cost %i.\n",cost);
  Sactions[nOfSActions].cost = cost;
}

/* Go through the predicates in an action effect and mark non-static ones. */

void checkifstatic(Seff *e) {
  atom a;
  Sefflist *es;
  switch(e->t) {
  case SEpatom:
  case SEnatom:
    a = e->a;
    setnonstatic(a[0]);
    break;
  case SEconj:
    es = e->juncts;
    while(es != NULL) {
      checkifstatic(es->hd);
      es = es->tl;
    }
    break;
  case SEwhen:
  case SEforall:
    checkifstatic(e->effect); break;
  default:
    break;
  }
}

void addactioneffect(Seff *e) {
  Sactions[nOfSActions].effect = e;
  checkifstatic(e);
}

/* Requirements */

void checkrequirements(intlist *l) {
  while(l != NULL) {
    if(strcmp(symbol(l->hd),":strips") == 0) {
    } else if(strcmp(symbol(l->hd),":conditional-effects") == 0) {
    } else if(strcmp(symbol(l->hd),":adl") == 0) {
    } else if(strcmp(symbol(l->hd),":typing") == 0) {
    } else if(strcmp(symbol(l->hd),":equality") == 0) {
    } else if(strcmp(symbol(l->hd),":typing") == 0) {
    } else if(strcmp(symbol(l->hd),":conditional-effects") == 0) {
    } else if(strcmp(symbol(l->hd),":negative-preconditions") == 0) {
    } else if(strcmp(symbol(l->hd),":quantified-preconditions") == 0) {
    } else if(strcmp(symbol(l->hd),":action-costs") == 0) {
    } else {
      fprintf(stderr,"WARNING: unsupported :requirement %s\n",symbol(l->hd));
    }

    if(strcmp(symbol(l->hd),":action-costs") == 0) {
      fprintf(stderr,"WARNING: will ignore action costs\n");
    }

    l = l->tl;
  }
}

    /* Handling types and objects */

int member(int i,intlist *l) {
  while(l != NULL) {
    if(l->hd == i) return 1;
    l = l->tl;
  }
  return 0;
}

/* Destructive addition of a non-duplicate element to a NON-EMPTY list */
intlist *addtolist(int s,intlist *l) {
  if(member(s,l)) return l;
  return intcons(s,l);
}

void addobject(int v,int t) {
  int i;
  i = 0;
  while(i<nOfTypes) {
    if(t == Stypes[i].typename) { /* Add to type */
      Stypes[i].elements = addtolist(v,Stypes[i].elements);
      return;
    }
    i+=1;
  }
  nOfTypes += 1;
  Stypes[nOfTypes-1].typename = t;
  Stypes[nOfTypes-1].elements = intcons(v,EMPTYLIST);
  Stypes[nOfTypes-1].subtypes = EMPTYLIST;
  Stypes[nOfTypes-1].supertypes = EMPTYLIST;
  assert(nOfTypes < MAXOBTYPES);
}

/* Predicate definition */

void storepredicates() {
  /* We don't use the predicate definition for anything. */
  /* It could be used for some form of type-checking. */
}

/* Constant definitions */

void storeconstants(typedvarlist *cs) { /* Note: Same as 'storeobjects'. */
  while(cs != NULL) {
    addobject(cs->v,UNIVTYPE);
    addobject(cs->v,cs->t);
    cs = cs->tl;
  }
}

/* Type definitions */

void addsubtype(int t1,int t2) {
  int i;
  i = 0;
  while(i<nOfTypes) {
    if(Stypes[i].typename == t2) {
      Stypes[i].subtypes = addtolist(t1,Stypes[i].subtypes);
      return;
    }
    i = i + 1;
  }
  nOfTypes += 1;
  Stypes[i].typename = t2;
  Stypes[i].supertypes = EMPTYLIST;
  Stypes[i].elements = EMPTYLIST;
  Stypes[i].subtypes = intcons(t1,EMPTYLIST);
}

void addsupertype(int t1,int t2) {
  int i;
  i = 0;
  while(i<nOfTypes) {
    if(Stypes[i].typename == t1) {
      Stypes[i].supertypes = addtolist(t2,Stypes[i].supertypes);
      return;
    }
    i = i + 1;
  }
  nOfTypes += 1;
  Stypes[i].typename = t1;
  Stypes[i].supertypes = intcons(t2,EMPTYLIST);
  Stypes[i].subtypes = EMPTYLIST;
  Stypes[i].elements = EMPTYLIST;
}

void extendsubtyperelation(int t1,int t2) {
  addsubtype(t1,t2);
  addsupertype(t1,t2);
}

void storetypes(typedvarlist *ts) {
  while(ts != NULL) {
    extendsubtyperelation(ts->v,ts->t);
    ts = ts->tl;
  }
}

void processtypes() {
    int i;
    intlist *il,*il2;

  /* Extend subtypes and supertypes to non-immediate ones. */
  for(i=0;i<nOfTypes;i++) {
    il = Stypes[i].subtypes;
    while(il != NULL) {
      il2 = Stypes[i].supertypes;
      while(il2 != NULL) {
	addsubtype(il->hd,il2->hd);
	addsupertype(il->hd,il2->hd);
	il2 = il2->tl;
      }
      il = il->tl;
    }
  }

  if(flagShowInput) {
    for(i=0;i<nOfTypes;i++) {
      printf("TYPE %s:\n",symbol(Stypes[i].typename));
      printf(" ELEMENTS:");
      il = Stypes[i].elements;
      while(il != NULL) {
	printf(" %s",symbol(il->hd));
	il = il->tl;
      }
      printf("\n");
      printf(" SUBTYPES:");
      il = Stypes[i].subtypes;
      while(il != NULL) {
	printf(" %s",symbol(il->hd));
	il = il->tl;
      }
      printf("\n");
      printf(" SUPERTYPES:");
      il = Stypes[i].supertypes;
      while(il != NULL) {
	printf(" %s",symbol(il->hd));
	il = il->tl;
      }
      printf("\n");
    }
  }

  /* Add objects of a type to all its supertypes. */  
  for(i=0;i<nOfTypes;i++) {
    il = Stypes[i].elements;
    while(il != NULL) {
      il2 = Stypes[i].supertypes;
      while(il2 != NULL) {
	addobject(il->hd,il2->hd);
	il2 = il2->tl;
      }
      il = il->tl;
    }
  }
}

        /* PDDL problem definitions */

/* Add objects to a type. */

void storeobjects(typedvarlist *cs) {
  while(cs != NULL) {
    addobject(cs->v,UNIVTYPE);
    addobject(cs->v,cs->t);
    cs = cs->tl;
  }
}

void storeinit(atomlist *a) {
  int cnt,i;
  cnt = listlen(a);
  Sinit = (atom *)malloc((cnt+1) * sizeof(atom));
  for(i=0;i<cnt;i++) {
    Sinit[i] = a->hd;
    a = a->tl;
  }
  Sinit[cnt] = NULL;
}

void storegoal(Sfma *f) {
  Sgoal = f;
}

/* Domain name */

int domain,problem;

void storedomain(int s) { domain = s; }
void checkdomain(int s) {
  if(s != domain) {
    fprintf(stderr,"WARNING: problem domain '%s' does not match domain name '%s'\n",symbol(s),symbol(domain));
  }
}
char *domainname() { return symbol(domain); }

void addproblem(int s) { problem = s; }
char *problemname() { return symbol(problem); }

/* Lists */

Sfmalist *Sfmacons(Sfma *h,Sfmalist *t) {
  Sfmalist *r = (Sfmalist *)statmalloc(39,sizeof(Sfmalist));
  r->hd = h;
  r->tl = t;
  return r;
}

Sefflist *Seffcons(Seff *h,Sefflist *t) {
  Sefflist *r = (Sefflist *)statmalloc(40,sizeof(Sefflist));
  r->hd = h;
  r->tl = t;
  return r;
}

intlist *intcons(int h,intlist *t) {
  intlist *r = (intlist *)statmalloc(41,sizeof(intlist));
  r->hd = h;
  r->tl = t;
  return r;
}

ptrlist *ptrcons(int *h,ptrlist *t) {
  ptrlist *r = (ptrlist *)statmalloc(42,sizeof(ptrlist));
  r->hd = h;
  r->tl = t;
  return r;
}

atomlist *atomcons(atom h,atomlist *t) {
  atomlist *r = (atomlist *)statmalloc(43,sizeof(atomlist));
  r->hd = h;
  r->tl = t;
  return r;
}

/* Reading and processing an input file */

void showstatistics() {
  int i;
  printf("%3i action schemata\n",nOfSActions);
  for(i=0;i<nOfSActions;i++) {
    printSaction(&(Sactions[i]));
  }
  printf("%3i types\n",nOfTypes);
  for(i=0;i<nOfTypes;i++) {
    intlist *ss;
    printf("%s consists of",symbol(Stypes[i].typename));
    ss = Stypes[i].elements;
    while(ss != NULL) {
      printf(" %s",symbol(ss->hd));
      ss = ss->tl;
    }
    printf("\n");
  }
}

/* Turn object lists Stypes to object arrays AStypes. */

void constructtypearrays() {
  int i,*ptr,cnt;
  intlist *l;
  for(i=0;i<nOfTypes;i++) {
    cnt = listlen(Stypes[i].elements);
    AStypesCARD[i] = cnt;
    AStypes[i] = (int *)malloc((1+cnt) * sizeof(int));
    l = Stypes[i].elements;
    //    printf("%s has elements ",symbol(Stypes[i].typename));
    ptr = AStypes[i];
    while(l != NULL) {
      *ptr = l->hd;
      //      printf(" %s",symbol(*ptr));
      l = l->tl;
      ptr = ptr + 1;
    }
    //    printf("\n");
    *ptr = -1;
  }
}

void readfile() {
  linenumber = 1;
  if(nOfInputFiles == 0) {
    printf("Reading from standard input\n");
    lexeropenstdin();
  } else {
    lexeropen(inputfiles[0]);
  }
  errorstring = "";
  initPDDL();
  initsymboltable();
  UNIVTYPE = symbolindex("***UNIVTYPE***");
  yyparse();
  processtypes();
  constructtypearrays();
  if(flagShowInput) showstatistics();
}

void yyerror( char *s) {
  printf("%s; %s on line %i.\n",s,errorstring,linenumber);
  exit(1);
}

/*******************************************************************/
/********************* Bindings and domains ************************/
/*******************************************************************/

/* elements associated with a type */

int *getdomain(int type) {
  int j;
  for(j=0;j<nOfTypes;j++) {
    if(Stypes[j].typename == type) return AStypes[j];
  }
  fprintf(stderr,"WARNING: type %s not defined\n",symbol(type));
  exit(1);
  return NULL;
}

int getdomainsize(int type) {
  int j;
  for(j=0;j<nOfTypes;j++) {
    if(Stypes[j].typename == type) return AStypesCARD[j];
  }
  fprintf(stderr,"WARNING: type %s not defined\n",symbol(type));
  exit(1);
  return 0;
}
