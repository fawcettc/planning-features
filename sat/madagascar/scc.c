
/*  2012 (C) Jussi Rintanen, jrintanen.jr@gmail.com  */

#include <stdio.h>
#include <malloc.h>
#include <assert.h>

#include "asyntax.h"
#include "ordintsets.h"
#include "operators.h"

#include "main.h"

#include "scc.h"

/**********************************************************************/
/*  Strong components of a graph                                      */
/**********************************************************************/

/* Compute strong components  of the disabling graph. The arcs are not
   constructed explicitly, as computing them is expensive and most arcs
   would never be followed.
   The starting node is node number 0. The set of all nodes is
   {0,...,nOfNodes-1}. */

#define noDEBUG

int *NNdfnumber;
int *NNstack;
unsigned char *NNinstack;
int *NNlowlink;

int NNptr,NNdf;
int NNsingletons;

int maxSCCsize;

int nodecounter;

#define min(a,b) (((a)<(b))?(a):(b))

#define likely(expr) (__builtin_expect((expr),1))
#define unlikely(expr) (__builtin_expect((expr),0))

inline int getnext(int *el,eff **efs,int **e,int **as1,int **as2) {

 getfromas:

  if(**as1 != -1) {
    *el = **as1;
    (*as1)++;
    return 1;
  }

  if(**as2 != -1) {
    *el = **as2;
    (*as2)++;
    return 1;
  }

 getfrompene:

  if(**e != -1) {
    if((**e)&1) {
      *as1 = ApreconoccP[feVAR(**e)];
    } else {
      *as1 = ApreconoccN[feVAR(**e)];
    }
    *as2 = Acondocc[feVAR(**e)];
    *e = *e + 1;
    goto getfromas;
  }

  if(*efs != NULL) {
    *e = (*efs)->effectlits;
    *efs = (*efs)->tl;
    goto getfrompene;
  }

  return 0;
}

sccs NNtraverse(int i,sccs ac) {
  int j,current;

  eff *efs;
  int *e;
  int *as1,*as2;
  int dummy;
  int el;

  nodecounter = nodecounter + 1;

  if((10*nodecounter / nOfActions) != (10*(nodecounter-1) / nOfActions)) {
    printf(" %i",(nodecounter * 10 / nOfActions)*10); fflush(stdout);
  }

  NNdfnumber[i] = ++NNdf;
  NNlowlink[i] = NNdf;

  NNstack[++NNptr] = i;
  NNinstack[i] = 1;

  current = NNptr;

  efs = &(actions[i].effects);

  dummy = -1;

  e = &dummy;

  as1 = &dummy;
  as2 = &dummy;

  /* Go through all neighbor CANDIDATES. */

  while(getnext(&el,&efs,&e,&as1,&as2)) {
    
    if(NNdfnumber[el] == -1 && parallel(i,el)) {
      ac = NNtraverse(el,ac);
      NNlowlink[i] = min(NNlowlink[i],NNlowlink[el]);
    } else {
      if(NNinstack[el] == 1 && NNlowlink[i] > NNdfnumber[el] && parallel(i,el)) {
	NNlowlink[i] = NNdfnumber[el];
      }
    }
  }

  if(NNlowlink[i] == NNdfnumber[i]) { /* Found an SCC */
    sccs oldac;
    oldac = ac;
    ac = (sccs)statmalloc(405,sizeof(struct _scc));
    ac->NofEls = NNptr-current+1;
    ac->next = oldac;
    ac->els = (int *)statmalloc(406,ac->NofEls * sizeof(int));

    if(ac->NofEls > maxSCCsize) maxSCCsize = ac->NofEls;

    if(NNptr == current) NNsingletons += 1;

    for(j=current;j<=NNptr;j++) ac->els[j-current] = NNstack[j];

    if(flagShowInput) {
      printf("new SCC %i:",ac->NofEls);
      for(j=current;j<=NNptr;j++) printactionname(NNstack[j]); // printf(" %i",NNstack[j]);
      printf("\n");
    } else {
      if(debugOutput > 0 && NNptr != current) printf(" %i",NNptr-current+1);
    }
    
    for(j=current;j<=NNptr;j++) NNinstack[NNstack[j]] = 0;
    NNptr = current-1;
  }
  return ac;
}
    
int scc(int nOfNodes) {
  int i;
  sccs ac;
  
  nodecounter = 0;

  NNdf = -1;
  NNptr = -1;

  if(debugOutput > 0) printf("Finding SCCs for %i nodes.\n",nOfNodes);

  NNdfnumber = (int *)statmalloc(407,nOfNodes * sizeof(int));
  NNstack = (int *)statmalloc(408,nOfNodes * sizeof(int));
  NNinstack = (unsigned char *)statmalloc(409,nOfNodes * sizeof(unsigned char));
  NNlowlink = (int *)statmalloc(410,nOfNodes * sizeof(int));

  NNsingletons = 0;

  maxSCCsize = 0;

  for(i=0;i<nOfNodes;i++) {
    NNdfnumber[i] = -1;
    NNinstack[i] = 0;
  }

  ac = NULL;

  printf("Disabling graph %c:",'%');

  for(i=0;i<nOfNodes;i++)
    if(NNdfnumber[i] == -1) {
      ac = NNtraverse(i,ac);
    }

  if(debugOutput > 0) printf(", %i singleton components\n",NNsingletons);

  SCCS = ac;

  free(NNdfnumber);
  free(NNstack);
  free(NNinstack);
  free(NNlowlink);

  return maxSCCsize;
}
