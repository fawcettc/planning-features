
/*  2012 (C) Jussi Rintanen   */

#define AATREEnot
#define AADIRECTnot

#ifndef AATREE
#ifndef AADIRECT
typedef struct _intset {
  int maxEls;
  int nOfEls;
  int *elements;
} *intset;
#endif
#endif

#ifdef AATREE
typedef struct _intsetel {
  int el;
  short level;
  short c1;
  short c2;
} intsetel;

typedef struct _intset {
  int root;
  int maxEls;
  int nOfEls;
  int lastEl;
  int freed;
  intsetel *elements;
} *intset;
#endif

#ifdef AADIRECT
typedef struct _intsetel {
  int el;
  short level;
  struct _intsetel *c1;
  struct _intsetel *c2;
} *intsetel;

typedef struct _intset {
  intsetel root;
  int nOfEls;
} *intset;
#endif

intset IScreate();
intset IScreateSize(int);
int IScard(intset);
int ISemptyp(intset);
void ISmakeempty();
void ISinsertNODUP(int,intset);
void ISinsert(int,intset);
void ISremove(int,intset);
void ISremoveSet(intset,intset);
void ISaddelements(intset,intset);
/* int ISintersectwith(intset,intset); */
/* void ISintersectto(intset,intset,intset); */
void ISdifferenceto(intset,intset,intset);
void ISadddifferenceto(intset,intset,intset);
void IScopyto(intset,intset);
int ISmember(int,intset);

void ISprint(intset);

/* Iterator */

void ITstart(intset);
int ITnext(int *);

/* Debugging */

void printgraph(char *,intset);
