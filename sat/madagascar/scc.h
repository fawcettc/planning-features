
/*  2010 (C) Jussi Rintanen  */

typedef struct _scc {
  int NofEls;
  int *els;
  struct _scc *next;
} *sccs;

int scc(int);

sccs SCCS;
