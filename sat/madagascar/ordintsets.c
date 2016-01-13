
/*  2010 (C) Jussi Rintanen  */

#include "asyntax.h"
#include "ordintsets.h"

#include <stdio.h>
#include <assert.h>

intlist *freeels = NULL;

inline intlist *OScons(int v,intlist *l) {
  intlist *tmp;
  if(freeels != NULL) {
    tmp = freeels;
    freeels = (intlist *)(freeels->tl);
  } else {
    tmp = (intlist *)malloc(sizeof(struct _intlist));
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

ordintset OScreate() {
  ordintset tmp;
  tmp = (ordintset)malloc(sizeof(struct _ordintset));
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

inline int OSmember(int v,ordintset s) {
  intlist *l;
  l = s->elements;
  while(l != NULL) {
    if(l->hd < v) {
      l = l->tl;
    } else {
      if(l->hd == v) return 1;
      return 0;
    }
  }
  return 0;
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
