
/*  2012 (C) Jussi Rintanen  */

#include "intsets.h"
#include <stdio.h>
#include <stdlib.h>

int *fieldaddress(intset s) {
  return ((int *)s)+3;
}

/* BUG? There was a segmentation fault caused by the assingment to s->maxEls
   below. It is not obvious whether it was the call to statmalloc that
   has now been replaced by malloc, or something else. */

intset IScreateSize(int size) {
  intset s;
  s = (intset)malloc(sizeof(struct _intset));
  //  s = (intset)malloc(sizeof(struct _intset) + size * sizeof(int));
  s->maxEls = size;
  s->nOfEls = 0;
  //  s->elements = (int *)statmalloc(602,s->maxEls * sizeof(int));
  s->elements = (int *)malloc(s->maxEls * sizeof(int));
  //  s->elements = fieldaddress(s);
  return s;
}

intset IScreate() {
  return IScreateSize(30);
}

int IScard(intset s) {
  return s->nOfEls;
}

int ISemptyp(intset s) {
  return s->nOfEls == 0;
}

void ISmakeempty(intset s) {
  s->nOfEls = 0;
}

int *ISrealloc(intset s) {
  //  if(s->elements !=  fieldaddress(s)) {
    s->elements = (int *)realloc(s->elements,s->maxEls * sizeof(int));
    //  } else {
    //    printf("Reallocated.\n");
    //    s->elements = (int *)malloc(s->maxEls * sizeof(int));
    //  }
}


void ISinsert(int i,intset s) {
  int j;
  for(j=0;j<s->nOfEls;j++) {
    if(s->elements[j] == i) return;
  }
  if(s->nOfEls == s->maxEls) {
    s->maxEls = s->maxEls + 100;
    ISrealloc(s);
  }
  s->nOfEls += 1;
  s->elements[s->nOfEls-1] = i;
  //  if(s->nOfEls > maxcard) maxcard = s->nOfEls;
}

/* Insert new element that you know is new, without checking duplicates. */

void ISinsertNODUP(int i,intset s) {
  if(s->nOfEls == s->maxEls) {
    s->maxEls = s->maxEls + 100;
    ISrealloc(s);
  }
  s->nOfEls += 1;
  s->elements[s->nOfEls-1] = i;
  //  if(s->nOfEls > maxcard) maxcard = s->nOfEls;
}

void ISremove(int i,intset s) {
  int j;
  for(j=0;j<s->nOfEls;j++) {
    if(s->elements[j] == i) {
      s->elements[j] = s->elements[s->nOfEls-1];
      s->nOfEls -= 1;
      return;
    }
  }
}

void ISremoveSet(intset s1,intset s2) {
  int i;
  for(i=0;i<s1->nOfEls;i++) ISremove(s1->elements[i],s2);
}

void ISaddelements(intset s1,intset s2) {
  int i;
  for(i=0;i<s1->nOfEls;i++) {
    ISinsert(s1->elements[i],s2);
  }
}

int ISintersectwith(intset s1,intset s2) {
  int i;
  int change;
  change = 0;
  i = 0;
  while(i<s1->nOfEls) {
    if(ISmember(s1->elements[i],s2)) {
      i += 1;
    } else {
      change = 1;
      s1->elements[i] = s1->elements[s1->nOfEls-1];
      s1->nOfEls -= 1;
    }
  }
  return change;
}

/* Compute the intersection of first two sets and put it into the third */

void ISintersectto(intset s1,intset s2,intset s3) {
  int i;
  ISmakeempty(s3);
  for(i=0;i<s1->nOfEls;i++) {
    if(ISmember(s1->elements[i],s2)) ISinsert(s1->elements[i],s3);
  }
}

/* Compute the difference of first two sets and put it into the third */

void ISdifferenceto(intset s1,intset s2,intset s3) {
  int i;
  ISmakeempty(s3);
  for(i=0;i<s1->nOfEls;i++) {
    if(!ISmember(s1->elements[i],s2)) ISinsertNODUP(s1->elements[i],s3);
  }
}

/* Copy set to another */

void IScopyto(intset s1,intset s2) {
  int i;
  s2->nOfEls = s1->nOfEls;
  if(s1->nOfEls >= s2->maxEls) {
    s2->maxEls = s1->nOfEls + 10;
    ISrealloc(s2);
  }
  for(i=0;i<s1->nOfEls;i++) {
    s2->elements[i] = s1->elements[i];
  }
}

int ISmember(int i,intset s) {
  int j;
  for(j=0;j<s->nOfEls;j++) {
    if(s->elements[j] == i) return 1;
  }
  return 0;
}

void ISfree(intset s) {
  free(s->elements);
  free(s);
}

void ISprint(intset s) {
  int i;
  int first;
  first = 1;
  ITstart(s);
  while(ITnext(&i)) {
    if(first) printf(" ");
    printf("%i",i);
    first = 0;
  }
}

/* Iterator for going through the elements of a list */

int *ITptr;
int ITcounter;

void ITstart(intset s) {
  ITcounter = s->nOfEls;
  ITptr = s->elements;
}

int ITnext(int *i) {
  if(ITcounter <= 0) return 0;
  ITcounter -= 1;
  *i = *(ITptr++);
  return 1;
}

void printgraph(char *n,intset s) { }
