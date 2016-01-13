
/* 2012 (C) Jussi Rintanen, jrintanen.jr@gmail.com */

float memoryused();
void initclausedb(); /* This must be called once before adding any clauses. */
int *allocpermclause(int,int);
int *allocclause(int,int);
int clauselen(int *);
int SATinstance(int *);
void showclauses(satinstance);
void updateactivity(int *,int);
void setLBD(int *,int);

void free_clauses(int);

int GCaggressiveness;
double collectgarbage();

double allocatedbyCDB;

int clausecount;

void check_malloc_success(void *,int);

int ptr2intpad(int *); /* Calculate number of sizeof(int) to align. */

void falsifiedsomeclause(satinstance);

/* The pointers to the next clauses in which the watched literals occur
   are respectively either 4 or 8 bytes (1 or 2 sizeof(int)s), depending
   on whether we are in a 32 or 64 bit processor. This affects the indices
   of the different fields in the clause data structure. */

#if defined(__LP64__)
#define PREFIXWORDS 8
#else
#define PREFIXWORDS 6
#endif



#if defined(__LP64__)
#define PREFIX_WATCHA -8
#define PREFIX_WATCHB -6
#else
#define PREFIX_WATCHA -6
#define PREFIX_WATCHB -5
#endif


#define PREFIX_ACTIVITY -4
#define PREFIX_LBD -3
#define PREFIX_INSTANCE -2
#define PREFIX_CLAUSELEN -1

/* Clauses in the clause data base:
location   content
      -6   watched literal watched clauses link 1
      -5   watched literal watched clauses link 2
      -4   activity
      -3   LBD
      -2   SAT instance number
      -1   # of literals in clause
       0   1st literal
       1   2nd literal
       .   .
       .   .
     n-1   last literal
       n   -1

WARNING: These fields should always be accessed with the PREFIX_xxx macros.
*/

/* Macros for accessing the pointers at c[PREFIX_WATCHA] and c[PREFIX_WATCHB].
The issue is that c[] is an integer (4 byte) array, and in 64-bit
architectures pointers are twice as long. */


#define ASSIGN_WATCHA *((PTRINT *)(c+PREFIX_WATCHA))
#define ACCESS_WATCHA *((PTRINT *)(c+PREFIX_WATCHA))
#define ADDRESS_WATCHA ((PTRINT *)(c+PREFIX_WATCHA))

#define ASSIGN_WATCHB *((PTRINT *)(c+PREFIX_WATCHB))
#define ACCESS_WATCHB *((PTRINT *)(c+PREFIX_WATCHB))
#define ADDRESS_WATCHB ((PTRINT *)(c+PREFIX_WATCHB))

#define lsASSIGN_WATCHA *((PTRINT *)(ls+PREFIX_WATCHA))
#define lsACCESS_WATCHA *((PTRINT *)(ls+PREFIX_WATCHA))

#define lsASSIGN_WATCHB *((PTRINT *)(ls+PREFIX_WATCHB))
#define lsACCESS_WATCHB *((PTRINT *)(ls+PREFIX_WATCHB))
