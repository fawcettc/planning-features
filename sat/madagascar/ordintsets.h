
/*  2010 (C) Jussi Rintanen  */

typedef struct _ordintset {
  int nOfEls;
  intlist *elements;
} *ordintset;

ordintset OScreate();
ordintset OScreateSize(int);
int OScard(ordintset);
int OSemptyp(ordintset);
void OSmakeempty();
void OSinsert(int,ordintset);
void OSremove(int,ordintset);
void OSremoveSet(ordintset,ordintset);
void OS2removeSet(ordintset,ordintset);
void OSaddelements(ordintset,ordintset); /* Add the elements of 1st to 2nd. */
void OSintersect(ordintset,ordintset);
int OSmember(int,ordintset);
void OSreleasefree();

void OSstart(ordintset,intlist **);
int OSnext(int *,intlist **);

void OSprint(ordintset);
