
/*  2010 (C) Jussi Rintanen  */

int SATheuristic;
int PLANheuristic;
int planFrontend;
int flagShowInput;
int flagRestartInterval;
int flagRestartScheme;
int flagTimeout;
int flagRealTimeout;
int debugOutput;
int flagPDDLadddel;
int flagPreprocessing;
int flagIPCplans;
int flagCEvariables;	/* Create a variable for each conditional effect. */
int flagRandomSeedTime; /* Use the time as a random seed (instead of 0). */
int flagNoInvariants;
int flagEliminateConverses; /* Eliminate redundant converse literals. */
int flagExternalPreprocessor;
float flagMemoryLimit; /* Max. MB of memory allowed to allocate. */

long TIMEstartReal,TIMEstart,TIMEpreprocess,TIMEdisabling,TIMEdisaprepro,TIMEinvariants;

#ifdef MULTICORE
int nOfThreads;
#endif

float timefromstart();

double allocatedbyFE;

typedef enum { Sequ, EStep, EStepOgata, AStep } semantics;

semantics planSemantics;

int currentInputFile;
int nOfInputFiles;
char *inputfiles[10];
char *outputfile;

int flagOutputDIMACS;

void *statmalloc(int,int);
//#define statmalloc(a,b) malloc(b)

int firstTimePoint;
int lastTimePoint;
int outputTimeStep;

char *filenamebase;

int evalAlgorithm;	/* 0 = A, 1 = B, 2 = C */
int paramA;
float paramB;
float paramC;
int paramM; /* Max. processes for algorithm B. */

/* Heuristics */

int HEURordmode; /* 0 = earliest, 1 = latest, 2 = difference */
int HEURordmin; /* 0 = smaller is better, 1 = bigger is better */
int HEURordrnd; /* 1 = randomly shuffle (to break ties) */
int HEURtime; /* 0 = earliest, 1 = latest, 2 = all */
int HEURops; /* 0 = first, 1 = all */
int HEURchoice; /* 0 = random, 1 = weight */
int HEURactions; /* How many suggested actions found? */
int HEURactionchoice; /* choose action 0 = randomly, 1 = minimal time stamp */
int HEURactiondepthlimit;

int stats_longest_learned;
