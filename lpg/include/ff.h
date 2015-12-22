/*********************************************************************
 * (C) Copyright 2000 Albert Ludwigs University Freiburg
 *     Institute of Computer Science
 *
 * All rights reserved. Use of this software is permitted for 
 * non-commercial research purposes, and it may be copied only 
 * for that use.  All copies must include this copyright message.
 * This software is made available AS IS, and neither the authors
 * nor the  Albert Ludwigs University Freiburg make any warranty
 * about the software or its performance. 
 *********************************************************************/


/**
   The following parts of this file have been modified by the 
   LPG developers (DEA - University of Brescia):

   New costants:
   - YYMAXDEPTH
   - MAX_NUM_VALUE
   - MAX_PLAN_LENGTH
   - MAX_R_VALS

   New variables and data struntures:
   - _NumVar
   - _SpecialFacts
   - _DescNumEff
   - MIN_ARRAY
   - gparse_functions;
   - gmetric_exp
   - glob_start_time
   - tms glob_end_time
   - _command_line gcmdline
   - gtempl_time
   - greach_time
   - grelev_time
   - gconn_time
   - gnum_time
   - gmutex_total_time
   - gmutex_ft_time
   - gmutex_ops_time
   - gmutex_num_time
   - gsearch_time
   - gtotal_time
   - gcomm_line[MAX_LENGTH * 2]
   - gops_file[MAX_LENGTH]
   - gfct_file
   
   Modified variables and data structures:
   - _command_line
   - _Connective
   - _PlNode
   - _WffNode
   - _NormOperator
   - _EfConn
   - _FtConn
   - _State
**/









/*********************************************************************
 * File: ff.h
 * Description: Types and structures for the FastForward planner.
 *
 *        --------- ADL  VERSION  v 1.0 --------------
 *
 * Author: Joerg Hoffmann 2000
 * Contact: hoffmann@informatik.uni-freiburg.de
 *
 *********************************************************************/ 








#ifndef __FF_H
#define __FF_H






#include <stdlib.h>
#include <stdio.h>
#include <strings.h>
#include <ctype.h>
#include <sys/types.h>
#include <sys/timeb.h>
#include <sys/times.h>


#include <string.h>
#include <assert.h>







/*
 *  ------------------------------------ DEFINES ----------------------------
 */











/***********************
 * MEANINGLESS HELPERS *
 ***********************/




/* strcmp returns 0 if two strings are equal, which is not nice */
#define SAME 0









/****************
 * PARSING ETC. *
 ****************/


/**
#define __RUNTIME_YYMAXDEPTH
#define YYINCREMENT 10000
**/



/* various defines used in parsing
 */
#define EQ_STR "EQ"
#define HIDDEN_STR "#"
#define AXIOM_STR "AXIOM"
#define NAME_STR "name\0"
#define VARIABLE_STR "variable\0"
#define STANDARD_TYPE "OBJECT\0"
#define EITHER_STR "EITHER"
#define STR_NOT_MINUS "NOT-"








/***************************
 * SOME ARBITRARY SETTINGS *
 ***************************/







/* maximal string length
 */
#define MAX_LENGTH 256


/* marks border between connected items 
 */
#define CONNECTOR "~"


/* first size of goals_at array in 1P extraction
 */
#define RELAXED_STEPS_DEFAULT 25


/* size of hash table for repeated states checking
 * during EHC breadth first search
 */
#define EHC_HASH_SIZE 8192
#define EHC_HASH_BITS 8191


/* size of hash table for repeated states checking
 * in plan construction
 */
#define PLAN_HASH_SIZE 1024
#define PLAN_HASH_BITS 1023


/* size of hash table for repeated states checking
 * during BFS search
 */
#define BFS_HASH_SIZE 65536
#define BFS_HASH_BITS 65535


/* cut random values of facts off modulo this value,
 * to make state sums fit into a single integer
 */
#define BIG_INT 1500000







/************************
 * INSTANTIATION LIMITS *
 ************************/



#define MAX_CONSTANTS 2000
#define MAX_PREDICATES 10000
#define MAX_TYPES 50
#define MAX_ARITY 5
#define MAX_VARS 15


#define MAX_TYPE 2000


#define MAX_INITIAL 10000


#define MAX_OPERATORS 10000


/* in DNF: AND with OR - sons - collect 'hitting set':
 * one son of each OR node.
 *
 * this here is initial max number of such son s that can be collected
 * (grows dynamically, if required)
 */
#define MAX_HITTING_SET_DEFAULT 1000


#define MAX_TYPE_INTERSECTIONS 10


#define MAX_RELEVANT_FACTS 30000

/* derived predicates
 */

#define MAX_DERIVED_PREDICATES 20000
 


/******************************************
 * DOMAIN STRUCTURE AND SEARCHING LIMITS *
 ******************************************/






#define MAX_STATE 10000


/*
 * DEA - University of Brescia
 */

#ifdef __LOW_MEM__

   #define MAX_PLAN_LENGTH 200
#else

   #define MAX_PLAN_LENGTH 3000
#endif

#define MAX_R_VALS 100

#define MAX_NUM_INITIAL 1000

/*
 * End of DEA
 */






/****************
 * CODE DEFINES *
 ****************/









/* not a real 'code' define; used in relax and search to encode
 * infinite level number / plan length
 */
#ifndef INFINITY
#define INFINITY -1
#endif







/* define boolean types if not allready defined
 */
#ifndef Bool
typedef unsigned char Bool;
#ifndef TRUE /* we assume that FALSE is also not defined */
#define TRUE 1
#define FALSE 0
#endif /* TRUE */
#endif /* Bool */


/* code a param number into a negative number and vice versa
 */
#define ENCODE_VAR( val ) (val * (-1)) - 1
#define DECODE_VAR( val ) (val + 1) * (-1)

#define GET_CONSTANT( val, pointer ) ( val >= 0 ) ? val : pointer->inst_table[DECODE_VAR( val )]


/* Check allocated memory
 */
#define CHECK_PTR(p) if (NULL == (p)) { \
  fprintf(stdout, "\n\aNO MEMORY in file %s:%d\n\n", __FILE__, __LINE__); \
  exit(1);}


#ifndef __WINLPG__

/* add elapsed time from main local time vars to specified val
 */
#define TIME( val ) val += ( float ) ( ( end.tms_utime - start.tms_utime + \
					 end.tms_stime - start.tms_stime  ) / 100.0 )

#else

#define times(x) (wintime(x))
#define TIME( val ) val += DeltaTime(start, end)

#endif










/*
 *  ------------------------------ DATA STRUCTURES ----------------------------
 */











/*******************
 * GENERAL HELPERS *
 *******************/








/* all command switches
 */
struct _command_line {

  char path[MAX_LENGTH];
  char ops_file_name[MAX_LENGTH];
  char fct_file_name[MAX_LENGTH];
  int display_info;
  int debug;
  /*
   * DEA - University of Brescia
   */
  int max_plan_ops;
  float max_cpu_time;
  char out_file_name[MAX_LENGTH];
  char sol_file_name[MAX_LENGTH];
  /*
   * End of DEA
   */
 
};


typedef char *Token;












/***********
 * PARSING *
 ***********/


typedef struct _IntList
{
  int item;
  struct _IntList *next;
}
IntList;


/* A list of strings
 */
typedef struct _TokenList {

  char *item;
  struct _TokenList *next;

} TokenList;

/* list of string lists
 */
typedef struct _FactList {

  TokenList *item;
  struct _FactList *next;

} FactList;



/* structure to store  typed-list-of <name>/<variable>,
 * as they are declared in PDDL files
 */
typedef struct _TypedList {

  char *name;

  /* each item in this list is the name of a type which
   * our type is the union of (EITHER - types ...)
   *
   * usually, this will default to a single-item TokenList.
   */
  TokenList *type;
  /* after first sweep, this will contain the number in type table
   */
  int n;

  struct _TypedList *next;

} TypedList;



/* only needed to parse in the predicates and their arg
 * definitions
 */
typedef struct _TypedListList {

  char *predicate;

  TypedList *args;

  struct _TypedListList *next;

} TypedListList;



/* This type indicates whether a node in the pddl tree stands for
 * an atomic expression, a junctor or a quantor. 
 */
typedef enum _Connective{TRU,
			   FAL,
			   ATOM, 
			   NOT,
			   AND, 
			   OR, 
			   ALL, 
			   EX, 
/**
 * DEA - University of Brescia
 **/
			 NUM_EXP,
			 F_EXP,
			 F_EXP_T,
			 TIME_VAR,
			 DURATION_CONSTRAINT_CONN,
			 FN_ATOM,
			 FN_HEAD,
			 DURATION_VAR_ATOM,
			 BIN_COMP,
			 LESS_THAN_CONN,
			 LESS_THAN_OR_EQUAL_CONN,
			 EQUAL_CONN,
			 GREATER_THAN_CONN,
			 GREATER_OR_EQUAL_CONN,
			 MUL_CONN,
			 DIV_CONN,
			 MINUS_CONN,
			 UMINUS_CONN,
			 PLUS_CONN,
			 NUMBER_CONN,
			 ASSIGN_CONN,
			 INCREASE_CONN,
			 DECREASE_CONN,
			 SCALE_UP_CONN,
			 SCALE_DOWN_CONN,
			 AT_START_CONN,
			 AT_END_CONN,
			 OVER_ALL_CONN,
			 MINIMIZE_CONN,
			 MAXIMIZE_CONN,
			 METRIC_CONN,
			 TOTAL_TIME_CONN,
/**
 * End of DEA
 **/
			 WHEN,
			 /* aggiunta per i Timed Initial Facts PDDL2.2*/
			 TIMED_FACT} Connective;



/*
 * This is a node in the tree to parse PDDL files
 */
typedef struct _PlNode {

  /* type of the node
   */
  Connective connective;

  /* only for parsing: the var args in quantifiers
   */
  TypedList *parse_vars;

  /* AND, OR, NOT, WHEN => NULL
   * ALL, EX            => the quantified variable with its type
   * ATOM               => the atom as predicate->param1->param2->...
   */
  TokenList *atom;

  /* (a) for AND, OR this is the list of sons(a AND b AND c...),
   * (b) for the rest this is the son, e.g. a subtree that is negated
   * (c) for WHEN, the first son is the condition and the next son
   * is the effect
   */
  struct _PlNode *sons;

  /* if you have a list of sons, they are connected by next
   */
  struct _PlNode *next;

  /**
   * DEA - University of Brescia
   **/

  float value;

  short is_start_end_ovr;

  /**
   * End of DEA
   **/

} PlNode;


/*
 * This resembles an uninstantiated PDDL operator
 */
typedef struct _PlOperator {

  char *name;

  /* only important for PDDL where :VARS may be added to the param list
   * which must be hidden when writing the plan to an output file
   */
  int number_of_real_params; 

  /* the params, as they are declared in domain file
   */
  TypedList *parse_params;

  /* params is a list of variable/type pairs, such that:
   * factlist->item = [variable] -> [type]
   */
  FactList *params;
  PlNode *preconds;
  PlNode *effects;

  struct _PlOperator *next;

  /**
   * DEA - University of Brescia
   **/

  Bool is_odd;
  int num_numeric_preconds_start;
  int num_preconds_overall;
  int num_preconds_end;
  int num_effects_start;
  int num_deleffects_start;
  int num_numeric_effects_end;

  PlNode *duration;

  int ops_type;

  /**
   * End of DEA
   **/

} PlOperator;















/***************** 
 * INSTANTIATION *
 *****************/









/* helpers
 */

typedef int TypeArray[MAX_TYPE_INTERSECTIONS];

typedef int *int_pointer;




/* first step structures: parsing & preprocessing
 */

typedef struct _Fact {

  Bool added_implicit;

  int predicate, args[MAX_ARITY];

} Fact;



typedef struct _Facts {

  Fact *fact;

  struct _Facts *next;

} Facts;



/**
 * DEA - University of Brescia
 **/


typedef struct _NumVar
{
  int function, args[MAX_ARITY];
  float value;
  int gcomp_var_index;
}
NumVar;

/**
 * End of DEA
 **/


typedef struct _WffNode {

  Connective connective;

  /* in ALL/EX s
   */
  int var, var_type;
  char *var_name;

  /* in AND/OR s
   */
  struct _WffNode *sons;
  /* sons are doubly connected linear list
   */
  struct _WffNode *next;
  struct _WffNode *prev;

  /* in ATOMs
   */
  Fact *fact;
  /* after translation: mark NOT-p s for efficiency
   */
  int NOT_p;

  /* in ALL/EX/NOT
   */
  struct _WffNode *son;

  /* for expansion speedup
   */
  Bool visited;

  /* no WHEN s here... use Pl Connectives anyway for simplicity
   */

  /**
   * DEA - University of Brescia
   **/

  NumVar *numvar;

  short is_start_end_ovr;

  /**
   * End of DEA
   **/


} WffNode, *WffNode_pointer;



typedef struct _Literal {

  Bool negated;

  Fact fact;

  struct _Literal *next;
  struct _Literal *prev;

  short is_start_end_ovr;

} Literal;



typedef struct _Effect {

  int num_vars, var_types[MAX_VARS];
  char *var_names[MAX_VARS];

  WffNode *conditions;

  Literal *effects;

  struct _Effect *next;
  struct _Effect *prev;

} Effect;



typedef struct _Operator {

  char *name, *var_names[MAX_VARS];
  int number_of_real_params; 

  int num_vars, var_types[MAX_VARS];
  Bool removed[MAX_VARS];

  WffNode *preconds;

  Effect *effects;

  Bool hard;

} Operator, *Operator_pointer;




/* second step: structures that keep already normalized
 * operators
 */




typedef struct _NormEffect {

  int num_vars, var_types[MAX_VARS];
  int inst_table[MAX_VARS];

  Fact *conditions;
  int num_conditions;

  Fact *adds;
  int num_adds;
  Fact *dels;
  int num_dels;

  struct _NormEffect *prev;
  struct _NormEffect *next;

} NormEffect;



typedef struct _NormOperator {
  
  Operator *operator;

  int num_vars, var_types[MAX_VARS];
  int inst_table[MAX_VARS];
  int removed_vars[MAX_VARS], num_removed_vars, type_removed_vars[MAX_VARS];

  Fact *preconds;
  int num_preconds;

  NormEffect *effects;

  Bool out;

  /**
   * DEA - University of Brescia
   **/

  int num_numeric_preconds;
  int num_numeric_effects;

  Facts *inequals_constr;

  Bool suspected;

  /**
   * End of DEA
   **/

} NormOperator, *NormOperator_pointer;
  


/* minimal info for a fully instantiated easy operator;
 * yields one action when expanded
 */
typedef struct _EasyTemplate {

  NormOperator *op;
  int inst_table[MAX_VARS];

  struct _EasyTemplate *prev;
  struct _EasyTemplate *next;

  Bool suspected;

} EasyTemplate;






/* structures for hard ops
 */





/* intermediate step: structure for keeping hard ops
 * with normalized precondition, but arbitrary
 * effect conditions
 */
typedef struct _MixedOperator {
  
  Operator *operator;

  int inst_table[MAX_VARS];

  Fact *preconds;
  int num_preconds;

  Effect *effects;

  struct _MixedOperator *next;

} MixedOperator;





/* last hard step: everything is action - like, except that
 * facts are not yet integer coded
 */  

typedef struct _PseudoActionEffect {

  Fact *conditions;
  int num_conditions;

  Fact *adds;
  int num_adds;
  Fact *dels;
  int num_dels;

  struct _PseudoActionEffect *next;

} PseudoActionEffect;



typedef struct _PseudoAction {

  Operator *operator;

  int inst_table[MAX_VARS];

  Fact *preconds;
  int num_preconds;

  PseudoActionEffect *effects;
  int num_effects;

} PseudoAction, *PseudoAction_pointer;




/* final domain representation structure
 */




typedef struct _ActionEffect {

  int *conditions;
  int num_conditions;

  int *adds;
  int num_adds;
  int *dels;
  int num_dels;

  int ef_conn_pos;
  int condef_conn_pos;

} ActionEffect;



typedef struct _Action {

  NormOperator *norm_operator;
  PseudoAction *pseudo_action;

  char *name;
  int num_name_vars;
  int name_inst_table[MAX_VARS];

  int inst_table[MAX_VARS];

  int *preconds;
  int num_preconds;

  ActionEffect *effects;
  int num_effects;

  struct _Action *next;

  Bool suspected;

} Action;











/*****************************************************
 * BASIC OP AND FT STRUCTURES FOR CONNECTIVITY GRAPH *
 *****************************************************/










typedef struct MIN_ARRAY
{
  short int uid_block;
  int uid_mask;
}
min_array, *min_array_list;

typedef struct {
  int	num_cef;
  int	*cef;
  int	fact;
} reverse_bit_array;

typedef struct _OpConn {

  /* to get name
   */
  Action *action;

  /* effects
   */
  int *E;
  int num_E;

  /* implied effects
   */
  int *I;
  int num_I;

  /* member for applicable actions extraction
   */
  Bool is_in_A;

  /* members for 1Ph - H(S) extraction
   */
  int is_used;
  Bool is_in_H;

  min_array *bit_condition;
  int num_condition;
  reverse_bit_array *reverse_bit_condition;


} OpConn;


/**
 * DEA - University of Brescia
 **/

typedef struct _SpecialFacts
{

  /*array per le precondizioni che devono valere su tutto l'intervallo */
  int *PC_overall;
  /*non c'e' ordinamento tra bool e numeriche */
  int num_PC_overall;
  /*array per le precondizioni che devono valere alla fine */
  int *PC_end;
  /*non c'e' ordinamento tra bool e numeriche */
  int num_PC_end;

  /*array per gli effetti che si realizzano all'inizio */
  int *A_start;
  int num_A_start;

  /*effetti booleani che hanno luogo all'inizio */
  int *D_start;
  int num_D_start;

}
SpecialFacts;




typedef struct _TimedPrecs {

  int *PC_start;
  int num_PC_start;

  int *PC_overall;
  int num_PC_overall;
  
  int *PC_end;
  int num_PC_end;

} 
TimedPrecs;


typedef struct _DescNumEff
{
  int index;
  int lval;
  int rvals[MAX_R_VALS];
  int num_rvals;
  Bool is_at_start;
}
DescNumEff;


/**
 * End of DEA
 **/


typedef struct _EfConn {

  int op;

  /* op preconds + conds
   */
  int *PC;
  int num_PC;

  int *A;
  int num_A;

  int *D;
  int num_D;

  /* implied effects
   */
  int *I;
  int num_I;

  /* members for relaxed fixpoint computation
   */
  int level;
  Bool in_E;
  int num_active_PCs;
  Bool ch;

  /* in search: which ef is ``in plan''
   */
  Bool in_plan;

  /**
   * DEA - University of Brescia
   **/

  /* puntatore all'operatore che lo descrive */
  PlOperator *plop;

  /* costo e durata dell'azione */
  float cost;
  float duration;


  //Precondizioni at end, over all, ed effetti at start
  SpecialFacts *sf;

  Bool is_numeric;
  Bool has_numeric_precs;

#ifdef __TEST__
  char *name;
#endif

  int position;

  short int action_fact;
  unsigned short int num_precond, num_add_effect;

  min_array *bit_precond, *bit_add_effect;

  int *ft_exclusive_vect;	/* Exclusive bit vector between this action and facts (noop) */

  int *ef_exclusive_vect;	/* Exclusive bit vector between  actions */

  int num_numeric_effects;
  DescNumEff *numeric_effects;

  short flag_decr_lm;

  float lamda_prec, lamda_me;	// parameters for the lagrange multipliers
  int last_lm_prec, last_lm_me;	// Index of the last  local minima update
  int step;

  int dur_var_index;

  IntList *metric_vars;

  //bit array che indica quali variabili influenzano la durata in un'azione a durata variabile
  int *duration_rvals;
  int num_duration_rvals;

  // Per distingure un'azione vera da una fittizia
  int act_type;

  TimedPrecs *timed_PC;

  int start_ef, end_ef;

  Bool suspected;

  /**
   * End of DEA
   **/

} EfConn;


typedef struct _CondEfConn {	// gestione degli effetti condizionali

  int op;	// riferimento all'operatore
  int ef;	// riferimento all'effetto di base dell'operatore

  int *PC;	// precondizioni dell'effetto condizionale
  int num_PC;

  int *A;	// effetti additivi
  int num_A;

  int *D;	// effetti cancellanti
  int num_D;


  PlOperator *plop;	// puntatore all'operatore che lo descrive
  float cost;		// costo e durata dell'azione

  //Precondizioni at end, over all, ed effetti at start
  SpecialFacts *sf;

} CondEfConn;




typedef struct _FtConn {

  int step;
  int numR;

  /* effects it is union conds, pres element of
   */
  int *PC;
  int num_PC;

  /* efs that add or del it
   */
  int *A;
  int num_A;

  int *D;
  int num_D;

  /* members for orderings preprocessing
   */
  int *False;
  int num_False;

  /* members for relaxed fixpoint computation
   */
  int level;
  Bool in_F;

  /* members for 1Ph extraction
   */
  int is_goal;
  int is_true;
  Bool ch;

  /* search
   */
  int rand;/* for hashing */
  Bool is_global_goal;/* fast goal add finding */

  /**
   * DEA - University of Brescia
   **/

#ifdef __TEST__
  char *name;
#endif

  int position;

  int *ft_exclusive_vect;	/* Exclusive bit vector between this action and facts (noop) */
  int *ef_exclusive_vect;	/* Exclusive bit vector between  actions */

  short int action_fact;
  unsigned short int num_precond, num_add_effect;

  float lamda_prec, lamda_me;	// parameters for the lagrange multipliers
  int last_lm_prec, last_lm_me;	// Index of the last  local minima update

  /* Predicati derivati di cui il fatto è precondizione */
  int num_dp_PC;
  int *dp_PC;
  /* Predicati derivati di cui il fatto è effetto positivo */
  int num_dp_A;
  int *dp_A;
  /* Predicati derivati di cui il fatto è effetto negativo */
  int num_dp_D;
  int *dp_D;

  int fact_type;

  /**
   * End of DEA
   **/

  int *tmd_facts_array;
  int num_tmd_facts_array;

} FtConn;

typedef struct _CondFtConn {

  // effects it is union conds, pres element of
  int *PC;
  int num_PC;

  // efs that add or del it
  int *A;
  int num_A;

  int *D;
  int num_D;

} CondFtConn;











/****************************
 * STRUCTURES FOR SEARCHING *
 ****************************/









typedef struct _State {
  
  int *F;
  int num_F;

  /**
   * DEA - University of Brescia
   **/

  float *V;

  /**
   * End of DEA
   **/

} State, *State_pointer;



typedef struct _EhcNode {
  
  State S;

  int op;
  int depth;

  int num_sons;
  int dead_sons;

  struct _EhcNode *father;
  struct _EhcNode *next;

  /* for Goal Added Deletion Heuristic:
   * number of new goal that came in into S;
   *
   * if no such goal --> == -1
   */
  int new_goal;

} EhcNode;



typedef struct _EhcHashEntry {

  int sum;

  EhcNode *ehc_node;

  struct _EhcHashEntry *next;

} EhcHashEntry, *EhcHashEntry_pointer;



typedef struct _PlanHashEntry {

  int sum;
  State S;

  /* step is number of op that is EXECUTED in S;
   * -1 means that this state is no longer contained in plan
   */
  int step;
  struct _PlanHashEntry *next_step;

  struct _PlanHashEntry *next;

} PlanHashEntry, *PlanHashEntry_pointer;



typedef struct _BfsNode {
  
  State S;

  int op;
  int h;

  struct _BfsNode *father;

  struct _BfsNode *next;
  struct _BfsNode *prev;

} BfsNode;



typedef struct _BfsHashEntry {

  int sum;

  BfsNode *bfs_node;

  struct _BfsHashEntry *next;

} BfsHashEntry, *BfsHashEntry_pointer;

/* PREDICATI DERIVATI */




typedef struct _DpConn {

  int op;

  int *PC;
  int num_PC;

  int add, del;
  
} DpConn;













/*
 *  -------------------------------- MAIN FN HEADERS ----------------------------
 */












void output_planner_info( void );
void ff_usage( void );
Bool process_command_line( int argc, char *argv[] );









/*
 *  ----------------------------- GLOBAL VARIABLES ----------------------------
 */












/*******************
 * GENERAL HELPERS *
 *******************/










/* used to time the different stages of the planner
 */
extern float gtempl_time, greach_time, grelev_time, gconn_time;
extern float gsearch_time;

/* the command line inputs
 */
extern struct _command_line gcmd_line;

/* number of states that got heuristically evaluated
 */
extern int gevaluated_states;

/* maximal depth of breadth first search
 */
extern int gmax_search_depth;









/***********
 * PARSING *
 ***********/











/* used for pddl parsing, flex only allows global variables
 */
extern int gbracket_count;
extern char *gproblem_name;

/* The current input line number
 */
extern int lineno;

/* The current input filename
 */
extern char *gact_filename;

/* The pddl domain name
 */
extern char *gdomain_name;

/* loaded, uninstantiated operators
 */
extern PlOperator *gloaded_ops;

/*--PDDL2.2*/
/* loaded, uninstantiated derived predicates
 */
extern PlOperator *gderived_predicates;
extern PlOperator *gderived_pl2predicates;
/*PDDL2.2--*/

/* stores initials as fact_list 
 */
extern PlNode *gorig_initial_facts;

/* not yet preprocessed goal facts
 */
extern PlNode *gorig_goal_facts;

/* the types, as defined in the domain file
 */
extern TypedList *gparse_types;

/* the constants, as defined in domain file
 */
extern TypedList *gparse_constants;

/* the predicates and their arg types, as defined in the domain file
 */
extern TypedListList *gparse_predicates;

/* the objects, declared in the problem file
 */
extern TypedList *gparse_objects;



/* connection to instantiation ( except ops, goal, initial )
 */

/* all typed objects 
 */
extern FactList *gorig_constant_list;

/* the predicates and their types
 */
extern FactList *gpredicates_and_types;



/*
 * DEA - University of Brescia
 */

extern TypedListList *gparse_functions;

/* metric for the plan*/
extern PlNode *gmetric_exp;

/*
 * End of DEA
 */








/*****************
 * INSTANTIATING *
 *****************/










/* global arrays of constant names,
 *               type names (with their constants),
 *               predicate names,
 *               predicate aritys,
 *               defined types of predicate args
 */
extern Token gconstants[MAX_CONSTANTS];
extern int gnum_constants;
extern Token gtype_names[MAX_TYPES];
extern int gtype_consts[MAX_TYPES][MAX_TYPE];
extern Bool gis_member[MAX_CONSTANTS][MAX_TYPES];
extern int gtype_size[MAX_TYPES];
extern int gnum_types;
extern Token gpredicates[MAX_PREDICATES];
extern int garity[MAX_PREDICATES];
extern int gpredicates_args_type[MAX_PREDICATES][MAX_ARITY];
extern int gnum_predicates;

/*--PDDL2.2*/
extern int gnum_derived_predicates;
extern int gpredicates_type[MAX_PREDICATES];
/*PDDL2.2--*/




/* the domain in first step integer representation
 */
extern Operator_pointer goperators[MAX_OPERATORS];

/* derived predicates
 */
extern Operator_pointer gderivedpred[MAX_DERIVED_PREDICATES];

extern int gnum_operators;
extern Fact gfull_initial[MAX_INITIAL];
extern int gnum_full_initial;
extern WffNode *ggoal;


/* stores inertia - information: is any occurence of the predicate
 * added / deleted in the uninstantiated ops ?
 */
extern Bool gis_added[MAX_PREDICATES];
extern Bool gis_deleted[MAX_PREDICATES];



/* splitted initial state:
 * initial non static facts,
 * initial static facts, divided into predicates
 * (will be two dimensional array, allocated directly before need)
 */
extern Facts *ginitial;
extern int gnum_initial;
extern Fact **ginitial_predicate;
extern int *gnum_initial_predicate;



/* the type numbers corresponding to any unary inertia
 */
extern int gtype_to_predicate[MAX_PREDICATES];
extern int gpredicate_to_type[MAX_TYPES];

/* (ordered) numbers of types that new type is intersection of
 */
extern TypeArray gintersected_types[MAX_TYPES];
extern int gnum_intersected_types[MAX_TYPES];



/* splitted domain: hard n easy ops
 */
extern Operator_pointer *ghard_operators;
extern int gnum_hard_operators;
extern NormOperator_pointer *geasy_operators;
extern int gnum_easy_operators;

/* derived predicates
 */
extern Operator_pointer *ghard_derivedpred;
extern int gnum_hard_derivedpred;
extern NormOperator_pointer *geasy_derivedpred;
extern int gnum_easy_derivedpred;


/* so called Templates for easy ops: possible inertia constrained
 * instantiation constants
 */
extern EasyTemplate *geasy_templates;
extern int gnum_easy_templates;

extern EasyTemplate *gsuspected_easy_templates;
extern int gnum_suspected_easy_templates;


/* Templates per i Predicati derivati
 */
extern EasyTemplate *geasy_dp_templates;
extern int gnum_easy_dp_templates;


/* first step for hard ops: create mixed operators, with conjunctive
 * precondition and arbitrary effects
 */
extern MixedOperator *ghard_mixed_operators;
extern int gnum_hard_mixed_operators;



/* hard ''templates'' : pseudo actions
 */
extern PseudoAction_pointer *ghard_templates;
extern int gnum_hard_templates;

/* hard templates per i Predicati derivati
 */
extern PseudoAction_pointer *ghard_dp_templates;
extern int gnum_hard_dp_templates;


/* store the final "relevant facts"
 */
extern Fact grelevant_facts[MAX_RELEVANT_FACTS];
extern int gnum_relevant_facts;
extern int gnum_pp_facts;



/* the final actions and problem representation
 */
extern Action *gactions;
extern int gnum_actions;
extern State ginitial_state;
extern State ggoal_state;





/* Predicati derivati
 */
extern Action *gdpactions;
extern int gnum_dp_actions;





/*********************
 * CONNECTIVITY GRAPH *
 **********************/





/* one ops (actions) array ...
 */
extern OpConn *gop_conn;
extern int gnum_op_conn;



/* one effects array ...
 */
extern EfConn *gef_conn;
extern int gnum_ef_conn;

extern int gfirst_suspected_ef_conn;

/* one conditional effects array ...
 */
extern CondEfConn *gcondef_conn;
extern int gnum_condef_conn;

/* Array di Predicati derivati
 */
extern DpConn *gdp_conn;
extern int gnum_dp_conn;


/* one facts array.
 */
extern FtConn *gft_conn;
extern int gnum_ft_conn;

/* one facts array in conditional action.
 */
CondFtConn *gcondft_conn;
int gnum_condft_conn;









/*******************
 * SEARCHING NEEDS *
 *******************/







/* the goal state, divided into subsets
 */
extern State *ggoal_agenda;
extern int gnum_goal_agenda;



/* applicable actions
 */
extern int *gA;
extern int gnum_A;



/* communication from extract 1.P. to search engine:
 * 1P action choice
 */
extern int *gH;
extern int gnum_H;



/* the effects that are considered true in relaxed plan
 */
extern int *gin_plan_E;
extern int gnum_in_plan_E;



/* always stores (current) serial plan
 */
extern int gplan_ops[MAX_PLAN_LENGTH];
extern int gnum_plan_ops;



/* stores the states that the current plan goes through
 */
extern State gplan_states[MAX_PLAN_LENGTH + 1];


/*
 * DEA - University of Brescia
 */

#ifndef __WINLPG__
extern struct tms glob_start_time;
extern struct tms glob_end_time;
#else
extern clock_t glob_start_time;
extern clock_t glob_end_time;
#endif

extern struct _command_line gcmdline;

extern float gtempl_time;
extern float greach_time;
extern float grelev_time;
extern float gconn_time;
extern float gnum_time;
extern float gmutex_total_time;
extern float gmutex_ft_time;
extern float gmutex_ops_time;
extern float gmutex_num_time;
extern float gsearch_time;

extern float gtotal_time;
extern char gcomm_line[MAX_LENGTH * 2];

extern char gops_file_name[MAX_LENGTH];
extern char gfct_file_name[MAX_LENGTH];
extern char gpath_sol_file_name[MAX_LENGTH];

extern int max_state_facts;
/*
 * End of DEA
 */

#endif // __FF_H
