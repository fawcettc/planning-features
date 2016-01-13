
/*  2012 (C) Jussi Rintanen  */

/* Symboltable for IDs and VARs in lexer */

#include "asyntax.h"
#include "tables.h"
#include "main.h"

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>

#define noASSERTS

int maxSymbols;
int nOfSymbols;

void initsymboltable() {
  int i;

  maxSymbols = 50000;
  nOfSymbols = 0;
  for(i=0;i<MAXBUCKETS;i++) {
    symboltable[i].index = -1;
    symboltable[i].s = "";
    symboltable[i].next = NULL;
  }

  index2stentry = (stentry **)statmalloc(50,maxSymbols * sizeof(stentry *));
}

/* Hash function for strings (PDDL symbols) */

int symbolhash(char *s) {
  int hash,c,shift;
  hash = 0;
  while(*s != 0) {
    c = (*s)-48;
    hash = (hash << 5)-hash+c;
    s += 1;
  }
  return hash&(MAXBUCKETS-1);
}

/* Return the index of a symbol. Either the symbol is already
   in the symbol table with a given index, or it will be added
   and assigne the next available non-negative integer. */

int symbolindex(char *s) {
  int tmp;
  char *ns;
  stentry *ste;
  
  tmp = symbolhash(s);
  ste = symboltable+tmp;

  //  printf("Lookup: %s with hash %i.\n",s,symbolhash(s));

  /* Search through all symbols in the bucket. */

  while(ste->next != NULL && strcmp(s,ste->s) != 0) ste = ste->next;

  /* Found one that matches: return its index. */

  if(strcmp(s,ste->s) == 0) return ste->index;

  /* New symbol. */

  ns = (char *)statmalloc(51,strlen(s)+1); /* Make a new copy of the string */
  strcpy(ns,s);

  if(ste->index == -1) {
    ste->s = ns;
    ste->index = nOfSymbols++;
    ste->staticpredicate = 1;
  } else {
    //    printf("Hash collision\n");
    //    printf("[%i/%i]\n",tmp,nOfSymbols);
    ste->next = (stentry *)statmalloc(52,sizeof(stentry));
    ste->next->s = ns;
    ste->next->index = nOfSymbols++;
    ste->next->staticpredicate = 1;
    ste->next->next = NULL;
    ste = ste->next;
  }

  //  printf("New entry %i with has %i is %s\n",nOfSymbols-1,symbolhash(s),ns);

  if(nOfSymbols >= maxSymbols) {
    maxSymbols = maxSymbols * 2;
    index2stentry = (stentry **)realloc(index2stentry,maxSymbols * sizeof(stentry *));
  }

  index2stentry[nOfSymbols-1] = ste;

  return ste->index;

}

char *symbol(int i) {
  switch(i) {
  case -1: return "PARAM-0";
  case -2: return "PARAM-1";
  case -3: return "PARAM-2";
  case -4: return "PARAM-3";
  case -5: return "PARAM-4";
  case -6: return "PARAM-5";
  case -7: return "PARAM-6";
  case -8: return "PARAM-7";
  case -9: return "PARAM-8";
  case -10: return "PARAM-9";
  default:
    if(i<0) return "PARAMn";
    else {
      //      printf("entry %i is %s\n",i,index2stentry[i]->s);
      return index2stentry[i]->s;
    }
  }
}

void setnonstatic(int i) {
  index2stentry[i]->staticpredicate = 0;
}

int isvar(int i) {
  char *s;
  s = index2stentry[i]->s;
  return (*s == '?');
}

/* Symboltable for p(o1,...,on) atoms. */

#define ATABLESIZE 0x10000
#define MAXARITY 100

typedef struct _atomhashelement{ /* Mapping from atoms to indices */
  int index;
  intlist *a;
  struct _atomhashelement *tl;
} atomhashelement;

atomhashelement *atomhash[ATABLESIZE]; /* Mapping from atoms to indices */

intlist **atomtable; /* Mapping from indices to atoms (lists of strings) */
int maxAtoms;

void initatomtable() {
  int i;

  nOfAtoms = 0;
  maxAtoms = 50000;

  atomtable = (intlist **)statmalloc(53,sizeof(intlist *) * maxAtoms);

  for(i=0;i<ATABLESIZE;i++) atomhash[i] = NULL;
}


/* What is the index of the variable in action's parameter list? */

//int bindingindex(int i,typedvarlist *p) {
//  int j;
//  j = 0;
//  while(p->v != i) {
//    p = p->tl;
//    j += 1;
//    assert(p != NULL);
//  }
//  return j;
//}

/* silly auxiliary function */

int sameatom(int *i,intlist *j) {
  while(j != NULL) {
    if(*i != j->hd) return 0;
    i+=1;
    j = j->tl;
  }
  return 1;
}

int bvalue(int i,int *b) {
  if(i<0) {
    return b[-1-i];
  } else {
    return i; /* If not variable, it is already an object. */
  }
}

/* Fetch the index of an atom from the hash table, or create new. */

int atomindex(atom a,int *b) {
  atomhashelement *l,*ol;
  int hash,n,i,j;
  int syms[MAXARITY+1]; /* vector of symbols in the atom */

  /* Compute a hash number for the atom */
  syms[0] = a[0];
  hash = a[0];
  j=1;
  for(i=2;i<2+a[1];i++) {
    /* Fetch from the current assignment */
    n = bvalue(a[i],b);
    hash = (hash << 5)^n;
#ifdef ASSERTS
    assert(j < MAXARITY);
#endif
    syms[j] = n;
    j += 1;
  }

  hash = hash & (ATABLESIZE-1);

  l = atomhash[hash];

  ol = NULL;

  while(l != NULL) {
    /*    printf("%i %i %i*\n",hash,(int)(l->tl),(int)(l->a)); */
    if(sameatom(syms,l->a)) return l->index;
    ol = l;
    l = l->tl;
  }

  /* Was not in the list, create new. */

  l = (atomhashelement *)statmalloc(54,sizeof(atomhashelement));

  if(ol == NULL) {
    atomhash[hash] = l;
  } else {
    ol->tl = l;
  }

  l->index = nOfAtoms;
  l->a = NULL;
  l->tl = NULL;

  for(i=j-1;i>=0;i--) {
    l->a = intcons(syms[i],l->a);
    /*    if(l->a == 1 && l->tl == 1) { printf("BINGO!!!\n"); exit(1); } */
  }

  nOfAtoms += 1;

  if(nOfAtoms >= maxAtoms) {
    maxAtoms = maxAtoms * 3 / 2;
    atomtable = (intlist **)realloc(atomtable,maxAtoms * sizeof(intlist *));
  }

  atomtable[nOfAtoms-1] = l->a;

#ifdef DEBUG
  printf("CREATED ATOM %i:",l->index); printatomi(l->index); printf("\n");
#endif

  return l->index;
  
}

int printatomi(int i) {
  int len;
  intlist *a = atomtable[i];

  assert(i >= 0);
  assert(i < nOfAtoms);

  if(a == NULL) {
    fprintf(stderr,"INTERNAL ERROR: symbol table 1244\n");
    assert(1==0);
  }
  printf("%s(",symbol(a->hd));
  len = 1+strlen(symbol(a->hd));
  a = a->tl;
  while(a != NULL) {
#ifdef ASSERTS
    assert(a->hd >= 0);
#endif
    printf("%s",symbol(a->hd));
    len += strlen(symbol(a->hd));
    if(a->tl != NULL) { printf(","); len += 1; }
    a = a->tl;
  }
  printf(")"); len += 1;
  return len;
}

void renameatomtable(int nOfAtoms,int *mapping) {
  int i;
  for(i=0;i<nOfAtoms;i++) {
    if(mapping[i] != -1) atomtable[mapping[i]] = atomtable[i];
  }
}
