
/* 2012 (C) Jussi Rintanen, jrintanen.jr@gmail.com */

#include <stdio.h>
#include <stdlib.h>

#include <assert.h>

#include "main.h"

#include "interface.h"
#include "clausedb.h"
#include "clausesets.h"
#include "printplan.h"
#include "asyntax.h"
#include "ordintsets.h"
#include "operators.h"
#include "translate2sat.h"

#define noDEBUG
#define noASSERTS
#define noALIGNMENT /* There is a problem: the padding is not handled by GC! */

typedef struct _clausedblist {
  int *block;
  int permanent;
  int blockptr;
  struct _clausedblist *nextblock;
} clausedblist;

#if defined(__LP64__)
#define BLOCKSIZE 1024*1024*8
#else
#define BLOCKSIZE 1024*1024*2
#endif

clausedblist *cdb;
int CDBclauses;

  /* Given an int *, calculate the number of sizeof(int) to the
     next 64 byte alignment boundary. This is to align data structures
     with cache line boundaries.
   */

int ptr2intpad(int *ptr) {
  int alignment = (((int)ptr)&63) >> 2;
  if(alignment) return 16-alignment;
  else return 0;
}

void check_malloc_success(void *ptr,int i) {
  if(ptr == NULL) {
    fprintf(stderr,"ERROR: Could not allocate more memory %i.\n",i);
    exit(1);
  }
}

/* Clauses in the clause data base:
location   content
      -3   activity
      -2   SAT instance number
      -1   # of literals in clause
       0   1st literal
       1   2nd literal
       .   .
       .   .
     n-1   last literal
       n   -1

WARNING: These should always be accessed with the indices PREFIX_xxxx
defined in clausedb.h.

*/

void initclausedb() {
  cdb = (clausedblist *)malloc(sizeof(struct _clausedblist));
  check_malloc_success(cdb,1);

  cdb->block = (int *)malloc(BLOCKSIZE*sizeof(int));
  check_malloc_success(cdb->block,2);

  allocatedbyCDB = BLOCKSIZE*sizeof(int);

  cdb->blockptr = 0;
  cdb->permanent = 1;
  cdb->nextblock = NULL;
#ifdef DEBUG
  printf("FIRST CBD BLOCK %i\n",(int)cdb);
#endif
  CDBclauses = 0;
  clausecount = 0;
  GCaggressiveness = 0; /* Remove only very old clauses. */
}


/* Update clause activity counter. The pointer is to the first literal. */

void updateactivity(int *c,int act) {
  c[PREFIX_ACTIVITY] = act;
}

/* Set the LBD field of a clause. */

void setLBD(int *c,int lbd) {
  c[PREFIX_LBD] = lbd;
}


/* Allocate a clause. If permflag is 1, space allocated for
   the clause won't be freed or reused. */

int *allocc(int inst,int len,int permflag) {
  clausedblist *cls,*temp;
  int *ptr;
#ifdef ALIGNMENT
  int alignment;
#endif

#ifdef MULTICORE
#pragma omp critical
#endif
  {
    CDBclauses += 1;
    clausecount += 1;

    cls = cdb;
    while(cls != NULL
	  && (cls->permanent != permflag
	      || cls->blockptr+len+PREFIXWORDS+5 > BLOCKSIZE))
      {
	cls = cls->nextblock;
      }

    if(cls == NULL) {	/* Allocate a new block. */

#ifdef DEBUG
      printf("NEW CDB BLOCK (total of %i clauses now).\n",CDBclauses);
#endif
      temp = cdb;

      cdb = (clausedblist *)malloc(sizeof(struct _clausedblist));
      check_malloc_success(cdb,3);

      cdb->block = (int *)malloc(BLOCKSIZE*sizeof(int));
      check_malloc_success(cdb->block,4);

      allocatedbyCDB += BLOCKSIZE*sizeof(int);

      cdb->permanent = permflag;
      cdb->nextblock = temp;
      cdb->blockptr = 0;

      cls = cdb;

      printf("\t\t\t\tAllocated %i MB %s(total %i MB)\n",
	     BLOCKSIZE/1024/1024*sizeof(int),
	     (permflag ? "permanent " : ""),
	     (int)(memoryused()));

    }

#ifdef DEBUG
    printf("Allocating clause %i of length %i\n",cdb->blockptr,len);
#endif

  /* Allocate it from an existing block. */

#ifdef DEBUG
    printf("Allocating clause %i of length %i\n",cls->blockptr,len);
#endif

  /* Clauses should be aligned with cache line boundaries (16x4Bs?).
     Add something to cls->blockptr to make it align.
   */

#ifdef ALIGNMENT
    cls->blockptr += ptr2intpad(&(cls->block[cls->blockptr]));
#endif

    ptr = &(cls->block[cls->blockptr+PREFIXWORDS]);
  }
  
  cls->block[cls->blockptr+PREFIXWORDS+PREFIX_ACTIVITY] = 0;
  cls->block[cls->blockptr+PREFIXWORDS+PREFIX_LBD] = 0;
  cls->block[cls->blockptr+PREFIXWORDS+PREFIX_INSTANCE] = inst;
  cls->block[cls->blockptr+PREFIXWORDS+PREFIX_CLAUSELEN] = len;
  cls->block[cls->blockptr+len+PREFIXWORDS] = -1;
  cls->blockptr += len+1+PREFIXWORDS;

  return ptr;
}


/* Extract information from a clause pointed to by ptr (the first literal.) */

int clauselen(int *ptr) {
  return ptr[PREFIX_CLAUSELEN];
}


int SATinstance(int *ptr) {
  return ptr[PREFIX_INSTANCE];
}


/* Allocate space for a non-permanent clause. */

int *allocpermclause(int inst,int len) { return allocc(inst,len,1); }

int *allocclause(int inst,int len) { return allocc(inst,len,0); }


/* The following has not been tested after the -2 and -3 fields were added. */

void showclauses(satinstance sati) {
  clausedblist *cls;
  int i,j,b;
  printf("All clauses in clause db:\n");

  cls = cdb;
  b=0;
  while(cls != NULL) {
    i = 0;
    while(i < cls->blockptr) {
      printf("Clause at %i.%i:",b,i);
      for(j=i+PREFIXWORDS;j<i+PREFIXWORDS+(cls->block[i+PREFIXWORDS+PREFIX_CLAUSELEN]);j++) {
	printf(" [%i]:",cls->block[j]); printTlit(sati,cls->block[j]);
      }
      printf("\n");
      i = i+(cls->block[i+PREFIXWORDS+PREFIX_CLAUSELEN])+PREFIXWORDS+1;
    }
    cls = cls->nextblock;
    b += 1;
  }
}

#ifdef LBD
int nofclausesinblock(clausedblist *block) {
  int n = 0;
  int i = 0;
  while(i < block->blockptr) {
    n++;
    i = i+(block->block[i+PREFIXWORDS+PREFIX_CLAUSELEN])+PREFIXWORDS+1;
  }
  return n;
}

int nofnoninputclauses() {
  clausedblist *block = cdb;
  int n = 0;
  while(block) {
    if(block->permanent == 0) n += nofclausesinblock(block);
    block = block->nextblock;
  }
  return n;
}

int intCmp0(int *a,int *b) {
  if(*a > *b) return 1;
  else return 0;
}

int medianLBD() {
  int n = nofnoninputclauses();
  {
    int i,j;
    int tmp[n];
    clausedblist *block = cdb;
    j = 0;
    while(block != NULL) {
      if(block->permanent == 0) {
	i = 0;
	while(i < block->blockptr) {
	  tmp[j++] = block->block[i+PREFIXWORDS+PREFIX_LBD];
	  i = i+(block->block[i+PREFIXWORDS+PREFIX_CLAUSELEN])+PREFIXWORDS+1;
	}
      }
      block = block->nextblock;
    }
    qsort(tmp,j,sizeof(int),intCmp0);
    return tmp[j >> 1];
  }
}
#endif


/***********************************************************************/
/*** Garbage collection: reclaim space used by useless clauses.      ***/
/***********************************************************************/

int uselessp(satinstance sati,int *c,int lbdbound) {
  int len,age,lbd;

  len = c[PREFIXWORDS+PREFIX_CLAUSELEN];
  lbd = c[PREFIXWORDS+PREFIX_LBD];
  age = sati->conflicts - c[PREFIXWORDS+PREFIX_ACTIVITY];

  if(len <= 5) return 0;

  if(age > 200000) return 1;

  if(lbd < lbdbound) return 0;

  if(lbd == lbdbound && age < 500) return 0;

  return 1;
}


PTRINT *nextwlelement(satinstance sati,int lit,int *ls) {
  if(ls[0] == lit) return &(ls[PREFIX_WATCHA]);
  else {
#ifdef ASSERTS
    assert(ls[1] == lit);
#endif
    return &(ls[PREFIX_WATCHB]);
  }
}


void findinlist(satinstance sati,int lit,int *c) {
  int *ls;

  if(sati->value == 0) return; /* Instance is not used any more. */

  ls = sati->lits[lit].watches;
  do {
    if(ls == c) {
      printf("Clause %ld found in the list of %i.\n",(PTRINT)c,lit);
      return;
    }
    
    ls = *(nextwlelement(sati,lit,ls));
  } while(ls != NULL);
  printf("Clause not found!!!\n");
}


/* Remove a clause from the list of clauses in which a literal is watched. */

void removefromwlist(satinstance sati,int lit,int *c) {
  int *ls;
  int **prev;

  if(sati->value == 0) return; /* Instance is not used any more. */

  ls = sati->lits[lit].watches;
  prev = &(sati->lits[lit].watches);
  do {
    if(ls == c) {
      *prev = *(nextwlelement(sati,lit,ls));
      return;
    }
    prev = nextwlelement(sati,lit,ls);
    ls = *prev;
#ifdef ASSERTS
    assert(ls != NULL);
#endif
  } while(1==1);
}


/* Replace a clause by another one in the list of clauses. */

void replaceinwlist(satinstance sati,int lit,int *c1,int *c2) {
  int *ls;

  if(sati->value == 0) return; /* Instance is not used any more. */

  ls = sati->lits[lit].watches;

  if(ls==c1) {
    sati->lits[lit].watches = c2;
    return;
  }

  do {
    if(ls[0] == lit) {
      if(c1 == lsACCESS_WATCHA) {
	lsASSIGN_WATCHA = c2;
	return;
      }
      ls = lsACCESS_WATCHA;
    } else {
#ifdef ASSERTS
      assert(ls[1] == lit);
#endif
      if(c1 == lsACCESS_WATCHB) {
	lsASSIGN_WATCHB = c2;
	return;
      }
      ls = lsACCESS_WATCHB;
    }
#ifdef ASSERTS
    assert(ls != NULL);
#endif
  } while(1==1);
}


/* Delete useless clauses and free the space used by them. */

int garbagecollection() {
  int i;
  int freed,inst;
  int ptr,fill,bytes;
  clausedblist *blocks;
  float freedMB;
#ifdef LBD
  int lbdbound = medianLBD();
#endif

#ifdef LBD
  /*  printf("\t\t\t\t\t\tMedian LBD: %i\n",lbdbound); */
#endif
  printf("\t\t\t\t\t\tGC:"); fflush(stdout);

  freed = 0;	/* Number of bytes freed. */

  blocks = cdb;
  while(blocks != NULL) {

    ptr = 0;

    fill = 0;	/* Where to move clauses when compacting. */

#ifdef DEBUG
    printf("Fill factor %i/%i (%.2f %, %.2f MB)",blocks->blockptr,BLOCKSIZE,((double)blocks->blockptr)*100.0/((double)BLOCKSIZE),((double)blocks->blockptr)*4.0/1024.0/1024.0);
#endif

    while(ptr < blocks->blockptr) {

      inst = blocks->block[ptr+PREFIXWORDS+PREFIX_INSTANCE];

      bytes = blocks->block[ptr+PREFIXWORDS+PREFIX_CLAUSELEN]+PREFIXWORDS+1;

      /* Test integrity */
      //	findinlist(seqs[inst].sati,
      //		   blocks->block[ptr+PREFIXWORDS],
      //		   &(blocks->block[ptr+PREFIXWORDS]));
      //	findinlist(seqs[inst].sati,
      //		   blocks->block[ptr+PREFIXWORDS+1],
      //		   &(blocks->block[ptr+PREFIXWORDS]));

      if((seqs[inst].sati->value == 0)
	 || (!blocks->permanent && (uselessp(seqs[inst].sati,blocks->block+ptr,lbdbound)))) { /* Useless clause? */
	removefromwlist(seqs[inst].sati,
			blocks->block[ptr+PREFIXWORDS],
			blocks->block+ptr+PREFIXWORDS);
	removefromwlist(seqs[inst].sati,
			blocks->block[ptr+PREFIXWORDS+1],
			blocks->block+ptr+PREFIXWORDS);
	freed += bytes;
	
      } else { /* Otherwise shift it. */

	if(fill < ptr) {
	  replaceinwlist(seqs[inst].sati,
			 blocks->block[ptr+PREFIXWORDS],
			 blocks->block+ptr+PREFIXWORDS,
			 blocks->block+fill+PREFIXWORDS);
	  replaceinwlist(seqs[inst].sati,
			 blocks->block[ptr+PREFIXWORDS+1],
			 blocks->block+ptr+PREFIXWORDS,
			 blocks->block+fill+PREFIXWORDS);
	  
	  for(i=0;i<bytes;i++) blocks->block[fill+i] = blocks->block[ptr+i];
	}
	fill += bytes;
      }
      
      ptr += bytes;	/* Next clause */
      
    }

#ifdef DEBUG
    printf(" -> (%.2f %, %.2f MB).\n",
	   ((double)fill)*100/((double)BLOCKSIZE),
	   ((double)fill)*4.0/1024.0/1024.0);
#endif
      
    blocks->blockptr = fill;

    blocks = blocks->nextblock;
  }

  freedMB = ((float)freed) / (1024.0*256.0);
  printf(" %.2f MB\n",freedMB); fflush(stdout);

  return (int)freedMB;
}
