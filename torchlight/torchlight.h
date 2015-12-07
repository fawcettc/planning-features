


/*********************************************************************
 * (C) Copyright 2010 INRIA, France
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 * 
 *********************************************************************/


/*
 * THIS SOURCE CODE IS SUPPLIED  ``AS IS'' WITHOUT WARRANTY OF ANY KIND, 
 * AND ITS AUTHOR AND THE JOURNAL OF ARTIFICIAL INTELLIGENCE RESEARCH 
 * (JAIR) AND JAIR'S PUBLISHERS AND DISTRIBUTORS, DISCLAIM ANY AND ALL 
 * WARRANTIES, INCLUDING BUT NOT LIMITED TO ANY IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, AND
 * ANY WARRANTIES OR NON INFRINGEMENT.  THE USER ASSUMES ALL LIABILITY AND
 * RESPONSIBILITY FOR USE OF THIS SOURCE CODE, AND NEITHER THE AUTHOR NOR
 * JAIR, NOR JAIR'S PUBLISHERS AND DISTRIBUTORS, WILL BE LIABLE FOR 
 * DAMAGES OF ANY KIND RESULTING FROM ITS USE.  Without limiting the 
 * generality of the foregoing, neither the author, nor JAIR, nor JAIR's
 * publishers and distributors, warrant that the Source Code will be 
 * error-free, will operate without interruption, or will meet the needs 
 * of the user.
 */





/*********************************************************************
 * File: torchlight.h
 * Description: Types and structures for FF-based TorchLight
 *
 * Author: Joerg Hoffmann 2010
 * Contact: joerg.hoffmann@inria.fr
 *
 *********************************************************************/ 








#ifndef __TORCHLIGHT_H
#define __TORCHLIGHT_H






#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <strings.h>
#include <ctype.h>
#include <sys/types.h>
#include <sys/timeb.h>
#include <sys/times.h>









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









/* various defines used in parsing
 */
#define HIDDEN_STR "#"
#define AXIOM_STR "AXIOM"
#define NAME_STR "name\0"
#define VARIABLE_STR "variable\0"
#define STANDARD_TYPE "OBJECT\0"
#define EITHER_STR "EITHER"









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








#define MAX_CONSTANTS 20000
#define MAX_PREDICATES 20000
#define MAX_TYPES 100
#define MAX_ARITY 5
#define MAX_VARS 15


#define MAX_TYPE 2000


#define MAX_OPERATORS 50000


/* in DNF: AND with OR - sons - collect 'hitting set':
 * one son of each OR node. 
 *
 * this here is initial max number of such son s that can be collected
 * (grows dynamically, if required)
 */
#define MAX_HITTING_SET_DEFAULT 1000


#define MAX_TYPE_INTERSECTIONS 10


#define MAX_RELEVANT_FACTS 100000






/******************************************
 * DOMAIN STRUCTURE AND SEARCHING LIMITS *
 ******************************************/







#define MAX_PLAN_LENGTH 2000







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


/* add elapsed time from main local time vars to specified val
 */
#define TIME( val ) val += ( float ) ( ( end.tms_utime - start.tms_utime + \
					 end.tms_stime - start.tms_stime  ) / 100.0 )












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

  Bool do_gDG;
  Bool do_lDG;
  Bool do_SG_root;
  Bool optimize_over_op0var0;
  Bool prune_useless_var0;
  int replacement_level;
/*   Bool do_replace_op0_to_reduce_R; */
/*   Bool do_replace_P0plus_to_reduce_R; */
/*   Bool do_replace_for_recoverRFC; */
  Bool do_recoverer_only_relevant;

  Bool do_diagnose;
  Bool do_diagnose_gDG_successrate;
  Bool diagnose_prune_useless_var0;
  Bool do_diagnose_invertop0;
  Bool do_diagnose_ignore_exchangedvars;
  Bool negative_diagnose_all;
  int num_samples;
  int depth_samples;

  Bool output_file;
  Bool show_case_weight;

  Bool run_EHCanalyze;
  Bool run_only_EHCanalyze;

  Bool run_FF;
  Bool run_only_FF;

  int random_seed;

};


typedef char *Token;












/***********
 * PARSING *
 ***********/










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
			   WHEN} Connective;



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

  int predicate, args[MAX_ARITY];

} Fact;



typedef struct _Facts {

  Fact *fact;

  struct _Facts *next;

} Facts;



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

} WffNode, *WffNode_pointer;



typedef struct _Literal {

  Bool negated;

  Fact fact;

  struct _Literal *next;
  struct _Literal *prev;

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

} NormOperator, *NormOperator_pointer;
  


/* minimal info for a fully instantiated easy operator;
 * yields one action when expanded
 */
typedef struct _EasyTemplate {

  NormOperator *op;
  int inst_table[MAX_VARS];

  struct _EasyTemplate *prev;
  struct _EasyTemplate *next;

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

} Action;











/*****************************************************
 * BASIC OP AND FT STRUCTURES FOR CONNECTIVITY GRAPH *
 *****************************************************/












/* CG-->H+ analysis: more convenience for saying which
 * var-value we're referring to here.
 */
typedef struct _VarVal {

  int var;
  int val;

} VarVal, *VarVal_pointer;

/* also: insert DTG transitions for direct reference.
 */
typedef struct _DTGTransition DTGTransition, *DTGTransition_pointer;



typedef struct _OpConn {

  /* to get name
   */
  Action *action;

  /* effects
   */
  int *E;
  int num_E;

  /* member for applicable actions extraction
   */
  Bool is_in_A;

  /* members for 1Ph - H(S) extraction
   */
  int is_used;
  Bool is_in_H;

  /* CG-->H+ analysis
   *
   * The pre/eff in form of variable-value pairs!
   *
   * NOTE that we assume STRIPS here ie no cond effs!
   */
  VarVal *pre;
  int num_pre;
  VarVal *eff;
  int num_eff;
  /* the DTG transition (s, plural, iff no prec on effvar) for each
   * effect var
   */
  DTGTransition_pointer **eff_DTG_transitions;
  int *num_eff_DTG_transitions;

  /* for convenient access to pre/eff OF VAR
   * is -1 if none.
   */
  int *pre_on_var;
  int *eff_on_var;

  /* a stupid helper...
   */
  Bool is_recoverer;

} OpConn;



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

  Bool removed;

  /* members for relaxed fixpoint computation
   */
  int level;
  Bool in_E;
  int num_active_PCs;
  Bool ch;

  /* in search: which ef is ``in plan''
   */
  Bool in_plan;

} EfConn;



typedef struct _FtConn {

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

  /* CG-->H+ analysis
   */
  int var;
  int val;
  /* does it occur in any op pre or the goal?
   */
  Bool is_relevant;
  /* if it occurs in a single op pre, which op is it? else, -1
   */
  int is_relevant_only_for;

  /* this does not occur in FD's output. must be non-reachable?
   * anyway, simply mark this fact as being such, and don't try to
   * find its variable value.
   */
  Bool notFD;

} FtConn;












/****************************
 * STRUCTURES FOR SEARCHING *
 ****************************/









typedef struct _State {
  
  int *F;
  int num_F;

  int max_F;

} State, *State_pointer;



typedef struct _EhcNode {
  
  State S;

  int op;
  int depth;

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





















/***********************************
 * STRUCTURES FOR CG-->H+ ANALYSIS *
 ***********************************/








typedef struct _Variable {

  /* for ease of printing infos: somewhat fancy name-thingy, trying to
   * find common onjects/predicates
   */
  char *name;

  /* here are the actual values! ie the indices into gft_conn if
   * "real" value, else -1 for OTHER
   */
  int *vals;
  int num_vals;

} Variable, *Variable_pointer;



typedef struct _SGNode SGNode, *SGNode_pointer;
typedef struct _SGEdge SGEdge, *SGEdge_pointer;


struct _SGEdge {

  SGNode *start;
  SGNode *end;

  /* helper for looking at sub-graphs!
   */
  Bool IN;

};

struct _SGNode {
  
  int var;

  SGEdge_pointer *pred;
  SGEdge_pointer *succ;
  int num_pred, num_succ;

  /* helper for looking at sub-graphs!
   */
  Bool IN;

  /* helpers for computing Dcost, dcost
   */
  int ownDcost;
  int owndcost;

};

typedef struct _SG {
  
  SGNode *nodes;
  int num_nodes; /* redundant, = gnum_variables */

  SGEdge *edges;
  int num_edges;

  /* this will be the adjacency matrix, ie a 2-dimensional table where
   * x,y=1 iff x has an edge to y... convenient for some computations
   * (eg whether or not the guy is acyclic)
   */
  Bool **adj_matrix;
  /* DISABLED! Was runtime critical in some benchmarks and, finally,
   * is used for NOTHING with the single exception of identifying
   * non-leaf goal vars for x0 in lDGs... which seems a rather useless
   * occupation anyhow...
   */
/*   /\* this will be the same for the transitive hull */
/*    *\/ */
/*   Bool **trans_adj_matrix; */

  /* static properties
   */
  Bool is_acyclic;

  /* a helper for sub-graph acyclicity checking
   */
  Bool **IN_adj_matrix;

} SG, *SG_pointer;



typedef struct _DTGNode DTGNode, *DTGNode_pointer;

struct _DTGTransition {

  DTGNode *start;
  DTGNode *end;

  int rop;

  DTGNode_pointer *conditions;
  DTGNode_pointer *side_effects;
  int num_conditions, num_side_effects;

  /* static properties
   */
  Bool no_side_effects;/* == (num_side_effects==0); just for cleanliness */
  Bool invertible;
  /* one possible inverter, if exists; will be w/o side effects if
   * possible
   */
  DTGTransition *inverted_by;
  Bool irrelevant;
  Bool irrelevant_own_delete;
  /* the next three aren't actually tested if there are no side
   * effects at all.  ... just set them to TRUE -- this is implied per
   * definition anyhow.
   */
  Bool self_irrelevant_side_effect_deletes;
  Bool irrelevant_side_effect_deletes;
  Bool replacable_side_effect_deletes;
  Bool irrelevant_side_effects;
  /* this one isn't tested if irrelevant_side_effect_deletes --
   * implied as special case of def.  
   */
  Bool recoverable_side_effect_deletes;
  /* this final test is only done in unison with recoverable_side_effect_deletes
   */
  Bool recoverer_only_relevant_side_effects;

  /* being induced is a dynamic property...
   */
  Bool induced;

  /* helpers
   */
  DTGNode_pointer **context;/* for each side effect var, array of context facts */
  int *num_context;/* number of context facts within each array */
  int num_contexts;/* redundant, will be = num_side_effects */

  /* helper for looking at sub-graphs!
   */
  Bool IN;

};

struct _DTGNode {
  
  int var;
  int val;

  DTGTransition_pointer *in;
  DTGTransition_pointer *out;
  int num_in, num_out;

  /* helper for looking at sub-graphs!
   */
  Bool IN;

};

typedef struct _DTG {
  
  int var;

  DTGNode *nodes;
  int num_nodes; /* redundant, = num vals of var */

  DTGTransition *transitions;
  int num_transitions;


  /* static properties
   */

  /* the easy guys
   */
  Bool all_invertible;
  Bool all_no_side_effects;
  Bool all_irrelevant_side_effect_deletes;

  /* the condition we'll impose on non-leafs in lDGs and gDGs:
   *
   * OUTDATED! Now the test for invertible is "irrelevant side effect
   * deletes and no side effects on V \setminus {x0}. The latter part
   * is dynamic so we cannot test this once and for all. However, if
   * this bool here is true then we don't need to bother going into
   * further detail, since this implies the new criterion. So it's
   * still in use.
   */
  Bool NONLEAF_irrelevant_or_invertiblenoseff_or_irrelevantdeletes;

  /* a necessary condition we'll impose on leafs in gDGs:
   * (only if this holds does it make sense to look any further)
   *
   * NOTE: this is OUTDATED and not used! It was useful in the first
   * place only for non-gDG formulation of global analysis, which is
   * now switched off.
   */
  Bool LEAF_irrelevant_or_irrelevantseffdel_or_irrelevantseffrecoverableseffdel;

  int diameter;
  int maxdiameter;

  /* these here are not, strictly speaking, properties of the DTG. But
   * it is convenient to have them here.
   */
  Bool var_is_SG_leaf;
  Bool var_is_goal;

} DTG, *DTG_pointer;






















/*
 *  -------------------------------- MAIN FN HEADERS ----------------------------
 */








void print_official_result( void );/* AIPS 2002 output routine */
void print_official_op_name( int index );





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
extern float gsearch_time, gSG_DTG_time, gSG_DTG_static_analyze_time, ganalyze_global_time;
extern float ganalyze_local_ini_lDG_time, ganalyze_local_ini_oDGplus_time;
extern float ganalyze_local_sample_lDG_time, ganalyze_local_sample_oDGplus_time;
extern float gsampling_time, grelaxed_plan_time, gFDvariables_time;
extern float ganalyze_local_sample_monotoneEHC_time;

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








/* resulting name for ops file
 */
extern char gops_file[MAX_LENGTH];
/* same for fct file 
 */
extern char gfct_file[MAX_LENGTH];



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
extern int gmember_nr[MAX_CONSTANTS][MAX_TYPES];/* nr of object within a type */
extern int gtype_size[MAX_TYPES];
extern int gnum_types;
extern Token gpredicates[MAX_PREDICATES];
extern int garity[MAX_PREDICATES];
extern int gpredicates_args_type[MAX_PREDICATES][MAX_ARITY];
extern int gnum_predicates;




/* the domain in first step integer representation
 */
extern Operator_pointer goperators[MAX_OPERATORS];
extern int gnum_operators;
extern Fact *gfull_initial;
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



/* so called Templates for easy ops: possible inertia constrained
 * instantiation constants
 */
extern EasyTemplate *geasy_templates;
extern int gnum_easy_templates;



/* first step for hard ops: create mixed operators, with conjunctive
 * precondition and arbitrary effects
 */
extern MixedOperator *ghard_mixed_operators;
extern int gnum_hard_mixed_operators;



/* hard ''templates'' : pseudo actions
 */
extern PseudoAction_pointer *ghard_templates;
extern int gnum_hard_templates;



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








/**********************
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



/* one facts array.
 */
extern FtConn *gft_conn;
extern int gnum_ft_conn;










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













/************************************
 * GLOBAL VARS FOR CG-->H+ ANALYSIS *
 ************************************/





/* the vars, parsed from FD
 */
extern Variable *gvariables;
extern int gnum_variables;



/* the support graph
 */
extern SG gSG;



/* the DTG for each var
 */
extern DTG *gDTGs;



/* just a helper...
 */
extern int *ggoal_on_var;



/* must communicate relaxed plan to oDGplus analysis.
 */
extern int *grplan;
extern int gnum_rplan;



/* to communicate back analysis results
 */
extern Bool gsuccess;
extern int ged_bound;
extern Bool gdead_end;

extern float gsuccess_percentage;
extern int gmin_ed_bound;
extern float gmean_ed_bound;
extern int gmax_ed_bound;
extern float gdead_end_percentage;



/* the sample states.
 */
extern State *gsample_states;



/* the data output file, if wanted.
 */
extern FILE *goutput_file;



/* for diagnosis!
 *
 * First of all, a flag whether we're actually diagnosing the reasons
 * for negative outcome -- on option, we want to do this diagnosis
 * only for those states for which actually had this outcome. The
 * outcome will be known only posthum so have to run analysis two
 * times.
 */
extern Bool gdo_negative_diagnosis;

/* counts of how many successful/failed analysis attempts
 */
extern int ggDG_num_graphs;/* for gDG, also need to count number of graphs considered */
extern int ggDG_num_successes;
extern int glDG_num_successes; /* here num trials is simply number of samples */
extern int goDGplus_num_successes;
extern int goDGplus_num_failures;

/* The first guy here will be the union of success var0s in gDG
 * analysis.
 */
extern int *ggDG_responsible_var0s;
extern int *ggDG_responsible_op0s;/* index into goperators array! */
extern int *ggDG_responsible_op0var0s_weights;/* how many times this guy? */
extern int ggDG_num_responsible_op0var0s;

/* The next guy will be the union of success var0s in lDG analysis.
 */
extern int *glDG_responsible_var0s;
extern int *glDG_responsible_var0s_weights;/* how many times this guy? */
extern int glDG_num_responsible_var0s;

/* These here will be the pairs of (successful t0-eff-pred, op0-actionname) for oDG+
 * analysis.
 */
extern int *goDGplus_responsible_pred0s;
extern int *goDGplus_responsible_op0s;/* index into goperators array! */
extern int *goDGplus_responsible_op0pred0s_weights;
extern int goDGplus_num_responsible_op0pred0s;

/* Here are the variables that appeared on a cycle in oDG+ analysis.
 */
extern int *goDGplus_cycle_vars;
extern int *goDGplus_cycle_vars_weights;
extern int goDGplus_num_cycle_vars;

/* /\* Here are all facts that were in non-recovered RFC_intersect */
/*  *\/ */
/* extern int *goDGplus_nonrecovered_RFC_intersect; */
/* extern int goDGplus_num_nonrecovered_RFC_intersect; */

/* Instead, collect pair of op0-actionname and ft-pred of RFS Intersect.
 */
extern int *goDGplus_nonrecovered_RFC_intersect_preds;
extern int *goDGplus_nonrecovered_RFC_intersect_op0s;/* index into goperators array! */
extern int *goDGplus_nonrecovered_RFC_intersects_weights;
extern int goDGplus_num_nonrecovered_RFC_intersects;
extern int goDGplus_nonrecovered_RFC_intersects_totalweight;

/* for comparison, here's the alternative previously used, recording
 * op0/var instead.
 */
extern int *gOLD_oDGplus_nonrecovered_RFC_intersect_vars;
extern int *gOLD_oDGplus_nonrecovered_RFC_intersect_op0s;/* index into goperators array! */
extern int *gOLD_oDGplus_nonrecovered_RFC_intersects_weights;
extern int gOLD_oDGplus_num_nonrecovered_RFC_intersects;
extern int gOLD_oDGplus_nonrecovered_RFC_intersects_totalweight;

/* For any non-leaf transition that was invertible/induced but had
 * side effects, here is the pair of responsible rop-actionname and
 * side-effect variable.
 */
extern int *goDGplus_nonleafbadtrans_seffvars;
extern int *goDGplus_nonleafbadtrans_rops;/* index into goperators array! */
extern int *goDGplus_nonleafbadtranss_weights;
extern int goDGplus_num_nonleafbadtranss;

/* flag so that SG cycle check knows who he is working for.
 * 1 = gDG, 2 = lDG, 3 = oDG+
 */
extern int gchecking_acyclic_for;



/* for EHC run, checking the "predictive quality" of the sampling.
 */
extern int gEHC_success;
extern int gEHC_max_search_depth;
extern float gEHC_time;
extern Bool doing_EHC; /* flag indicating that we're now no longer in analysis mode */ 



/* signal to EHC that we're not actually doing search but local-EHC
 * analysis
 */
extern Bool gdoing_EHCanalyze;





#endif
