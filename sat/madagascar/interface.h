
/* 2012 (C) Jussi Rintanen, jrintanen.jr@gmail.com */

#if defined(__LP64__)
#define PTRINT long
#else
#define PTRINT int
#endif

typedef struct _thread {
  int cround;	/* Counter which is incremented for new conflict clauses */
  int maxwasseen;
  int *wasseen;	/* Counter when literal was last encountered */
#define MAXCCLENGTH 10000000
  int cc[MAXCCLENGTH];	/* Conflict clause which is being constructed */
#ifndef FUIP
  int stck[MAXCCLENGTH];	/* The stack used during computing the conflict clause */
#endif

} thread;

thread *threads;

#define SVAR(v) (v)
#define ACTVAR(a) ((a)+(sati->nOfSVars))
#define TVAR(v,t) ((v)+(t)*(sati->nOfVarsPerTime))
#define TLIT(l,t) ((l)+2*(t)*(sati->nOfVarsPerTime))
#define TACT(a,t) ((ACTVAR(a))+(t)*(sati->nOfVarsPerTime))

typedef struct _nintlist { int hd; struct _nintlist *tl; } nintlist;


/*********************** VARIABLES *******************/

#define STATUSTYPE char

/************* LITERALS & WATCH LISTS *****************/

/* The watch list has the watch list EMBEDDED in the clause data structure
  (Biere et al. ???)
*/

#define LITWATCHES(l) (sati->lits[(l)].watches)

typedef struct _literal {
  int *watches;
#ifdef WEIGHTS
  short score;		/* Scores for choosing decision variables */
#endif
} literal;

/********************** HEAP *********************/

/* Heap for keeping track of the highest score variables.
   Each element in the heap has two components:
   k: key, i.e. the index of the variable
   v: value, i.e. the current VSIDS score/weight
 */

typedef struct {
  int k;
  short v;
} pair;

typedef struct _heap {
  int els;
  int maxels;
  pair *array;
} *heap;


/******************* SAT INSTANCE *******************/

#define REASONDLEVEL

#ifdef REASONDLEVEL
typedef struct {
  PTRINT reason;
  int dlevel;
} RD;
#endif

typedef struct _satinstance {
  short id;	/* Unique integer id for the instance */
  int thread;	/* The thread this is run in. */

  short value;	/* The truth-value of the instance, -1 = unknown */
  int nOfVars;	/* Number of propositional variables */
  int nOfVarsPerTime;	/* Number of vars per time point */
  short nOfTPoints;	/* Number of time points */

  nintlist **l2its;	/* Array for 2-literal clauses (for all time points), non-changing */
  int **al2its;		/* Array for 2-literal clauses (for all time points), non-changing */

  literal *lits;	/* Data structure for literals */

  int *declevels;
#ifdef COSTS
  int declevelscost;
#endif

#if defined REPRTWO || defined REPRFOUR
#define VALTYPE int
#else
#define VALTYPE char
#endif

  VALTYPE *variableval;

  int dlevel;		/* Current decision level of the SAT instance. */

  int decisions;	/* How many decision made */
  int conflicts;	/* How many conflicts */
  int decaysteps;	/* Counter for variable weight decays */

  int conflicttype2lit;
  int *conflictclause;	/* Clause that was falsified */
  int conflictl1;	/* Following four set when empty clause derived. */
  int conflictl2;

#ifndef MULTICORE
  int cc[MAXCCLENGTH];	/* Conflict clause which is being constructed */
#ifndef FUIP
  int stck[MAXCCLENGTH];	/* The stack used during computing the conflict clause */
#endif
#endif

#ifdef VSIDS
  STATUSTYPE *variablestatus;
	/* These are the status bits.
           bit 0      is phase there?
           bit 1      phase
           bit 2      dirty? (whether inferred with the goal clauses)
	*/
#define VARSTATUS(v) (sati->variablestatus[(v)])
#endif

#ifndef REASONDLEVEL

  PTRINT *variablereason;
  int *variabledlevel;
#define LITREASON(l) (sati->variablereason[VAR(l)])
#define LITDLEVEL(l) (sati->variabledlevel[VAR(l)])

#else

  RD *variablerd;

#define LITREASON(l) (sati->variablerd[VAR(l)].reason)
#define LITDLEVEL(l) (sati->variablerd[VAR(l)].dlevel)

#endif


#ifdef VSIDS
  int *hindex;		/* Index of each variable in the heap. */
  heap scoreheap;	/* Literals ordered according to their score */
#endif

  int *initialunittable;	/* Table for the unit clauses in the input */
  int maxinitialunits;		/* The size of the table */
  int initialunits;		/* Number of unit clauses in the table */

  int *unitstack;	/* Stack of assignments made */
  int endunitstack,startunitstack;	/* Unprocessed part of the stack */

  int nOfSVars;		/* Planning: number of state variables (per time) */
  int nOfActions;	/* Planning number of actions (per time) */

  int complete;		/* true if all input clauses have been added */
  int notcalledbefore;	/* true if solve0 not called yet. */

  /* Fields for the heuristics */
  int pheuristic;	/* Which planning-based heuristic to use. */
  int heuristic;	/* Which branching heuristic to use. */
  /* Unit clauses that have been learned */
#define MAXUCC 10000
  int NofUCClauses;
  int UCC[MAXUCC];

  /* Variables for the planning heuristic */
  int heuristic_mode;	/* This is 0 for actions, 1 for inertia, 2 for noops. */
  int heuristic_time;	/* The next two are for inertia and noops. */
  int heuristic_index;
#ifdef COSTS
  int costbound;	/* Cost bound */
  int currentcost;	/* Cost of current (partial) assignment */
  int *costs;		/* Costs all (untimed) state variables  */
#endif


#ifdef GOALWEIGHTS
  int *supportsg;	/* Which subgoal action supports. */
  int *supportsa;	/* Which action (previous decision) action supports. */
#endif

#ifdef LBD
  int LBDcounter;
  int *LBDflag;
#endif

} *satinstance;

typedef enum { InitC, FinalC, TransC } clausetype;

float estimateinstancesize(int,int,int);

satinstance newinstance(int,int,int,int,int);
void freeinstance(satinstance);

void addnewclause(satinstance,int,clausetype); /* Number of literals in the clause (> 2) */
void addliteral(satinstance,int,int); /* Put literal to the given loc in the clause */
void finishclause(satinstance); /* Finish adding the clause */

int add1clause(satinstance,int,clausetype); /* Add a 1-literal clause */
void add2clause(satinstance,int,int,clausetype); /* Add a 2-literal clause */

void instancecomplete();

void planningparameters(satinstance,int,int);
void setheuristic(satinstance,int);
void setpheuristic(satinstance,int);

int solve(satinstance);
int solve0(satinstance,int,int);

int noT2clauses;

void addtimedvarcost(satinstance,int,int);

int varvalue(satinstance,int);
int vartruep(satinstance,int);
int tvarvalue(satinstance,int,int);
int tvarvar(satinstance,int);
int tvartime(satinstance,int);

int VALUE(int);
int NEG(int);
int VAR(int);
int PLIT(int);
int NLIT(int);
int LIT(int);

#define UNASS -1

int propagate(satinstance);

void init_clausesets(int);

double allocatedbyCL;
float memoryused();

int flagShortCutHorizon;

void shortcuts(satinstance sati);

typedef struct _shortcutclause {
  int l1,l2,tdiff;
} shortcutclause;

shortcutclause *shortcutclauses;
int nofshortcutclauses;
int maxshortcutclauses;

void nextround(satinstance sati);
