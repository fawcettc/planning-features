/*********************************************************************
 * (C) Copyright 2002  Universita' degli Studi di Brescia
 *     Dipartimento di Elettronica per l'Automazione
 *     Via Branze 38, 25123 Brescia, Italy
 *
 * All rights reserved. Use of this software is permitted ONLY for
 * non-commercial research purposes, and it may be copied only
 * for that use only. All copies must include this copyright message.
 * This software is made available AS IS, and neither the authors
 * nor the University of Brescia make any warranty about the
 * software or its performance.
 *
 *********************************************************************/



/********************************************************************
 * File: main.c 
 * Description:  Main routins of LPG.
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/ 



#include <math.h>
#include <string.h>

#include <sys/time.h>

#ifdef __WINLPG__
#include <time.h>
#endif

#include "lpg.h"
#include "parse.h"
#include "inst_easy.h"
#include "inst_hard.h"
#include "inst_pre.h"
#include "inst_final.h"
#include "inst_utils.h"
#include "check.h"
#include "utilities.h"
#include "numeric.h"
#include "LpgOutput.h"
#include "LpgTime.h"
#include "output.h"
#include "mutex.h"
#include "LocalSearch.h"
#include "ActionSubgraph.h"
#include "ComputeReachInf.h"
#include "search.h"
#include "relax.h"
#include "memory.h"
#include "mutex.h"

/******************************************************************************
 *                             GLOBAL VARIABLES                               *
 ******************************************************************************/

/**
 * PARSING
 **/

/* used for pddl parsing, flex only allows global variables */
int gbracket_count;
char *gproblem_name;

/* The current input line number */
int lineno = 1;

/* The current input filename */
char *gact_filename;

/* The pddl domain name */
char *gdomain_name = NULL;

/* loaded, uninstantiated operators */
PlOperator *gloaded_ops = NULL;
PlOperator *gloaded_pl2ops = NULL;

/* loaded, uninstantiated derived predicates */
PlOperator *gderived_predicates = NULL;
PlOperator *gderived_pl2predicates = NULL;

/* stores initials as fact_list */
PlNode *gorig_initial_facts = NULL;

/* not yet preprocessed goal facts  */

PlNode *gorig_goal_facts = NULL;

/* metric for the plan*/
PlNode *gmetric_exp = NULL;

/* axioms as in UCPOP before being changed to ops */
PlOperator *gloaded_axioms = NULL;

/* the types, as defined in the domain file */
TypedList *gparse_types = NULL;

/* the constants, as defined in domain file */
TypedList *gparse_constants = NULL;

/* the predicates and their arg types, as defined in the domain file */
TypedListList *gparse_predicates = NULL;

/* PDDL2--*/
TypedListList *gparse_functions = NULL;

/* the objects, declared in the problem file */
TypedList *gparse_objects = NULL;

/* connection to instantiation ( except ops, goal, initial ) */

/* all typed objects  */
FactList *gorig_constant_list = NULL;

/* the predicates and their types */
FactList *gpredicates_and_types = NULL;

FactList *gfunctions_and_types = NULL;



/**
 * INSTANTIATING
 **/

/* global arrays of constant names,
 *               type names (with their constants),
 *               predicate names,
 *               predicate aritys,
 *               defined types of predicate args
 */
Token gconstants[MAX_CONSTANTS];
int gnum_constants = 0;
Token gtype_names[MAX_TYPES];
int gtype_consts[MAX_TYPES][MAX_TYPE];
Bool gis_member[MAX_CONSTANTS][MAX_TYPES];
int gtype_size[MAX_TYPES];
int gnum_types = 0;

Token gpredicates[MAX_PREDICATES];
int garity[MAX_PREDICATES];
int gpredicates_args_type[MAX_PREDICATES][MAX_ARITY];
int gnum_predicates = 0;

int gnum_derived_predicates = 0;
int gpredicates_type[MAX_PREDICATES];

/*miamod per functions*/
Token gfunctions[MAX_FUNCTIONS];
int gfunarity[MAX_FUNCTIONS];
int gfunctions_args_type[MAX_FUNCTIONS][MAX_ARITY];
int gnum_functions = 0;
/*finemiamod per functions*/


/* the domain in integer (Fact) representation
 */
Operator_pointer goperators[MAX_OPERATORS];

Operator_pointer gderivedpred[MAX_DERIVED_PREDICATES];

int gnum_operators = 0;
Fact gfull_initial[MAX_INITIAL];
int gnum_full_initial = 0;

/* Timed initial facts
 */
// Conta i timed initial facts 
int gnum_tmd_init_fcts = 0;
// Indici dei timed facts in gef_conn
int *gtimed_facts_idx = NULL;
/* Intervalli associati ai timed facts
 */

int *gnum_tmd_interval = NULL;
Timed_fct **gtimed_fct_vect = NULL;
int *ginterval_idx = NULL;
int gnum_timed_facts = 0;

int *temp_PC_int = NULL;

neighb shifted_act[MAX_SHIFTED];
int num_shifted_act = 0; 

//NumVar *gfullnum_initial[MAX_NUM_INITIAL];
NumVar **gfullnum_initial = NULL;
int gnum_fullnum_initial = 0;
int gnum_fullnum_blocks;

int max_num_value = MAX_NUM_INITIAL;
int max_fullnum_initial = MAX_NUM_INITIAL;

int gnum_comp_var = 0;
int gnum_comp_var_effects = 0;
int gnum_block_compvar;
int *gis_inertial = NULL;
int goptimization_exp = -1;
int *gis_not_appliable;

float gmax_cpu_time_for_quality_mode;

WffNode *ggoal = NULL;


/* stores inertial - information: is any occurence of the predicate
 * added / deleted in the uninstantiated ops ?
 */
Bool gis_added[MAX_PREDICATES];
Bool gis_deleted[MAX_PREDICATES];



/* splitted initial state:
 * initial non static facts,
 * initial static facts, divided into predicates
 * (will be two dimensional arrays, allocated directly before need)
 */
Facts *ginitial = NULL;
int gnum_initial = 0;
Fact **ginitial_predicate;
int *gnum_initial_predicate;



/* the type numbers corresponding to any unary inertia
 */
int gtype_to_predicate[MAX_PREDICATES];
int gpredicate_to_type[MAX_TYPES];

/* (ordered) numbers of types that new type is intersection of
 */
TypeArray gintersected_types[MAX_TYPES];
int gnum_intersected_types[MAX_TYPES];



/* splitted domain: hard n easy ops
 */
Operator_pointer *ghard_operators;
int gnum_hard_operators;
NormOperator_pointer *geasy_operators;
int gnum_easy_operators;

/* derived predicates
 */
Operator_pointer *ghard_derivedpred;
int gnum_hard_derivedpred;
NormOperator_pointer *geasy_derivedpred;
int gnum_easy_derivedpred;



/* so called Templates for easy ops: possible inertia constrained
 * instantiation constants
 */
EasyTemplate *geasy_templates = NULL;
int gnum_easy_templates = 0;

EasyTemplate *gsuspected_easy_templates = NULL;
int gnum_suspected_easy_templates = 0;

/* templates per i Predicati derivati
 */
EasyTemplate *geasy_dp_templates = NULL;
int gnum_easy_dp_templates = 0;


/* first step for hard ops: create mixed operators, with conjunctive
 * precondition and arbitrary effects
 */
MixedOperator *ghard_mixed_operators;
int gnum_hard_mixed_operators;



/* hard ''templates'' : pseudo actions
 */
PseudoAction_pointer *ghard_templates;
int gnum_hard_templates;

/* hard templates per i Predicati derivati
 */
PseudoAction_pointer *ghard_dp_templates;
int gnum_hard_dp_templates;

/* store the final "relevant facts"
 */
Fact grelevant_facts[MAX_RELEVANT_FACTS];
int gnum_relevant_facts;
int gnum_pp_facts;



/* the final actions and problem representation
 */
Action *gactions;
int gnum_actions;
State ginitial_state;
State ggoal_state;

/* Predicati derivati
 */
Action *gdpactions;
int gnum_dp_actions;

path_set  gdp_path;

indexed_int_list *numvar_hash_table[HASH_SIZE];
int cvar_hash_table[HASH_SIZE];
int cvar_hash_table_effects[HASH_SIZE];
int tot = 0, compl = 0;
CompositeNumVar *gcomp_var_effects;

char *lvar_names[MAX_VARS];
int lvar_types[MAX_VARS];
bit_table l_vals, lstar_vals, r_vals, tested_vars;

/* for facts and mutex
*/
int *F;			/*[MAX_RELEVANT_FACTS/32+1]; */

/* Variabili per il calcolo delle mutex */
dme *deleted_me;
int num_dme = 0;
int max_dme = 500;

/*  Gestione delle azioni spezzate */
int max_num_efconn = 0;
int gextended_ef_conn = 0;
int gextended_ef_block = 0;
int max_num_ftconn = 0;
int gextended_ft_conn = 0;

int max_state_facts = 0;

const char *goperator_table[] = {
  "MUL_OP",
  "DIV_OP",
  "MINUS_OP",
  "UMINUS_OP",
  "PLUS_OP",

  "FIX_NUMBER",
  "VARIABLE_OP",

  "INCREASE_OP",
  "DECREASE_OP",
  "SCALE_UP_OP",
  "SCALE_DOWN_OP",
  "ASSIGN_OP",

  "LESS_THAN_OP",
  "LESS_THAN_OR_EQUAL_OP",
  "EQUAL_OP",
  "GREATER_THAN_OP",
  "GREATER_OR_EQUAL_OP",

  "MINIMIZE_OP",
  "MAXIMIZE_OP"
};




/**
 * CONNECTIVITY GRAPH
 **/


/* one ops (actions) array ... */
OpConn *gop_conn;
int gnum_op_conn;



/* one effects array ... */
EfConn *gef_conn;
int gnum_ef_conn;

int gfirst_suspected_ef_conn;

/* one conditional effects array ... */
CondEfConn * gcondef_conn;
int gnum_condef_conn;



/* one facts array. */
FtConn *gft_conn;
int gnum_ft_conn;

/* one facts array in conditional action. */
CondFtConn *gcondft_conn;
int gnum_condft_conn;

/* Derived predicates (op) final representation */
DpConn *gdp_conn;
int gnum_dp_conn;

FtConn *gnoop_conn;

int gnum_ft_block;
int gnum_ef_block;

int gnum_dp_block;

int gnum_base_ft_conn = 0;
int gnum_base_ft_block = 0;



/**
 * FF SEARCHING NEEDS
 **/


/* byproduct of fixpoint: applicable actions */
int *gA;
int gnum_A;



/* communication from extract 1.P. to search engines:
 * 1P action choice */
int *gH;
int gnum_H;



/* the effects that are considered true in relaxed plan */
int *gin_plan_E;
int gnum_in_plan_E;


/* always stores (current) serial plan */
int gplan_ops[MAX_PLAN_LENGTH];
int gnum_plan_ops = 0;
int gtot_plan_ops = 0;


/* stores the states that the current plan goes through
 * ( for knowing where new agenda entry starts from ) */
State gplan_states[MAX_PLAN_LENGTH + 1];

PlanAction *subplan_actions = NULL;



/**
 * LPG LOCAL SEARCH
 **/

last_cost_list last_best_act_cost = NULL;

int num_try;
int return_count;
unsigned int seed;


constraints_list treated_c_l[MAX_FALSE];
constraints_list unsup_fact[MAX_FALSE];
constraints_list unsup_num_fact[MAX_FALSE];
constraints_list unsup_tmd_facts[MAX_FALSE];

neighb_list neighb_vect[MAX_MAX_NODES];
int num_neighborhood;

/* final sort of actions in temp_vect */  
int *pos_temp_vect;//[MAX_MAX_NODES];

def_level * vectlevel[MAX_PLAN_LENGTH + 1];
def_level * temp_vectlevel[MAX_PLAN_LENGTH + 1];


ActNode_list *remove_act_chain; //[MAX_PLAN_LENGTH];
ActNode_list *remove_act_chain_next_step;
int ind_remove_act_chain;
int ind_remove_act_chain_next_step;

/* Used for action <--> noop mutex
 */
noop_not_in *noop_free_list; 

unsigned long tot_alloc_mem_size;

char fct_file[MAX_LENGTH];

/* Statistical data about Lagrange multipliers
*/
#ifdef __STATISTIC_LM__

 /* global variables used to compute average, total maximum value, minimum value of
   Lagrange multipliers for preconditions and mutex 
  */
 
 float average_prec_final = 0.0;
 float average_me_final = 0.0;
 float var_prec_final = 0.0;
 float var_me_final = 0.0;

 float lm_prec_min_final,lm_prec_max_final,lm_me_min_final,lm_me_max_final;
 
/*Vars used for files
 */

 FILE *file_average_prec;
 FILE *file_var_prec;
 FILE *file_average_me;
 FILE *file_var_me;

#endif // end __STATISTIC_LM__



/**
 * COMPUTE MUTEX
 **/


/* Number of set mutex and level
 */
int gnum_mutex;
int gmutex_level;
/* Total number of fact-action mutex, action-fact mutex, 
   action-action mutex, fact-fact mutex 
 */
int total_ft_ef_mutex = 0;
int total_ef_ft_mutex = 0;
int total_ef_ef_mutex = 0;
int total_ft_ft_mutex = 0;

/* fact-fact mutex matrix
 */
int **FT_FT_mutex = NULL;
/* fact-action mutex matrix
 */
int **FT_EF_mutex = NULL;
/* action-action mutex matrix
 */
int **EF_EF_mutex = NULL;
/* action-fact mutex matrix
 */
int **EF_FT_mutex = NULL;


/**
 * NUMERIC PLANNING
 **/

/* Structure for numeric vars
 */

CompositeNumVar *gcomp_var;
float  *gcomp_var_value;
float  *gcomp_var_value_before;


/**
 * TEMPORAL PLANNING
 **/

char **mat_ord;
ActNode_list *act_ord_vect;
int num_act_ord;
short *prop_level_index;

float slack_vect[MAX_PLAN_LENGTH + 1];

int *splitted_level;


/**
 * CPU TIME MANAGEMENT
 **/

#ifndef __WINLPG__
struct tms start_time;
struct tms glob_start_time;
struct tms glob_end_time;
struct tms search_start;
struct tms search_end;
#else
clock_t start_time;
clock_t glob_start_time;
clock_t glob_end_time;
clock_t search_start;
clock_t search_end;
#endif

float gtotal_time;
char gcomm_line[MAX_LENGTH * 2];
char gops_file_name[MAX_LENGTH];
char gfct_file_name[MAX_LENGTH];
char gpath_sol_file_name[MAX_LENGTH];
char glpg_path[MAX_LENGTH];


/**
 * MISCELLANEUS
 **/

/* used to time the different stages of the planner
 */
float gtempl_time = 0, greach_time = 0, grelev_time = 0, gconn_time = 0, 
  gnum_time = 0, gmutex_total_time = 0, gmutex_ft_time = 0, 
  gmutex_ops_time = 0, gmutex_num_time = 0;
float gsearch_time = 0;

float build_ad_time, fixpoint_time;

/* the command line inputs
 */
struct _command_line gcmd_line;

/* number of states that got heuristically evaluated
 */
int gevaluated_states = 0;

/* maximal depth of breadth first search
 */
int gmax_search_depth = 0;

char temp_name[256];

char temp_name2[256];

node_cost *fact_costs; //[MAX_MAX_NODES];
/* Bitvector used by remove_temp_action to find facts that 
   become TRUE after it is removed
*/
int *new_true_facts;
/* Bitvector used by remove_temp_action to find facts that 
   become FALSE after it is removed
*/
int *new_false_facts;	

/* TRUE if termination condition is reached
 */
Bool is_terminated=FALSE;



/********************************************************************
 *                           HEADERS FOR PARSING                    *
 ********************************************************************/

void load_ops_file (char *filename);
void load_fct_file (char *filename);



/*****************************************************************
 *                          MAIN ROUTINE                         *
 *****************************************************************/










int main (int argc, char *argv[])
{
 
  /* resulting name for ops file */
  char ops_file[MAX_LENGTH] = "";
  /* same for fct file */
  char fct_file[MAX_LENGTH] = "";

  char sol_file[MAX_LENGTH] = "";
  float plan_time = 0.0; 

#ifndef __WINLPG__
  struct tms start, end;
#else
  clock_t start, end;
#endif


  struct timeval tv;
  struct timezone tz;

  State current_start, current_end;
  int i, j, k, optimize;
  Bool found_plan=0;


#ifdef __EFENCE__
  extern int EF_ALLOW_MALLOC_0;
  EF_ALLOW_MALLOC_0 = 1;
#endif

#ifndef __SUN__
#ifndef __WINLPG__
  so_signal_management();
#endif
#endif

  /* Init global State variables */
  ginitial_state.F = (int *)calloc(MAX_STATE, sizeof(int));
  ggoal_state.F = (int *)calloc(MAX_STATE, sizeof(int));
  current_start.F = (int *)calloc(MAX_STATE, sizeof(int));
  current_end.F =  (int *)calloc(MAX_STATE, sizeof(int));
  ginitial_state.num_F = ggoal_state.num_F =  current_start.num_F = current_end.num_F = 0;

  for (i = 0; i <= MAX_PLAN_LENGTH; i++)
    {
      gplan_states[i].F = (int *)calloc(MAX_STATE, sizeof(int));
      gplan_states[i].num_F = 0;
    }

  strcpy (gcomm_line, "");
  for (i = 0; i < argc; i++)
    {
      strcat (gcomm_line, argv[i]);
      strcat (gcomm_line, " ");
    }
  get_path (*argv, glpg_path);
  initialize_preset_values ();

//  init_statistic è la funzione che ha il compito di aprire tutti i file per la media e la varianza

#ifdef __STATISTIC_LM__
  init_statistic();
#endif

  /*Reset  hash-table
   */
  reset_cvar_hash_table();
  reset_cvar_hash_table_effects();
  
  /* Initialize random seed
   */
  gettimeofday (&tv, &tz);
  seed = ((tv.tv_sec & 0177) * 1000000) + tv.tv_usec;


  /* command line treatment
   */
  if (argc == 1 || (argc == 2 && *++argv[0] == '?'))
    {
      lpg_usage ();
      exit (1);
    }
  if (!process_command_line (argc, argv))
    {
      lpg_usage ();
      exit (1);
    }

  /* make file names
   */

  /* one input name missing
   */
  if (!gcmd_line.ops_file_name || !gcmd_line.fct_file_name)
    {
      fprintf (stdout, "\n%s: two input files needed\n\n", NAMEPRG);
      lpg_usage ();
      exit (1);
    }
  /* add path info, complete file names will be stored in
   * ops_file and fct_file
   */

#ifndef __WINLPG__
  sprintf (ops_file, "%s%s", gcmd_line.path, gcmd_line.ops_file_name);
  sprintf (fct_file, "%s%s", gcmd_line.path, gcmd_line.fct_file_name);

  strcpy (gops_file_name, ops_file);
  strcpy (gfct_file_name, fct_file);
  sprintf (sol_file, "%s%s", gcmd_line.path, gcmd_line.sol_file_name);
#else
  sprintf (ops_file, "%s", gcmd_line.ops_file_name);
  sprintf (fct_file, "%s", gcmd_line.fct_file_name);

  /**
  if (strchr(ops_file,'/') || ops_file[0] == '/')
    strcpy(gops_file_name, (strrchr(ops_file, '/')+sizeof(char)));
  else
    strcpy(gops_file_name,ops_file);

  if (strchr(fct_file,'/') || fct_file[0] == '/')
    strcpy(gfct_file_name, (strrchr(fct_file, '/')+sizeof(char)));
  else
    strcpy(gfct_file_name,fct_file);

  if(gpath_sol_file_name[strlen(gpath_sol_file_name)-1] != '/' && gpath_sol_file_name[0]!='\0')
    strcat(gpath_sol_file_name, "/");
  **/


  if (strchr(ops_file,'\\') || ops_file[0] == '\\')
    strcpy(gops_file_name, (strrchr(ops_file, '\\')+sizeof(char)));
  else
    strcpy(gops_file_name,ops_file);

  if (strchr(fct_file,'\\') || fct_file[0] == '\\')
    strcpy(gfct_file_name, (strrchr(fct_file, '\\')+sizeof(char)));
  else
    strcpy(gfct_file_name,fct_file);

  if(gpath_sol_file_name[strlen(gpath_sol_file_name)-1] != '\\' && gpath_sol_file_name[0]!='\0')
    strcat(gpath_sol_file_name, "\\");
#endif



  if(DEBUG1)
    {
     printf ("\n\n; Command line: %s  \n\n", gcomm_line);

    }

  /* parse the input files
   */

  /* start parse & instantiation timing
   */
  times (&glob_start_time);
  times (&start);
  /* domain file (ops)
   */

  printf ("\nParsing domain file: ");

  /* it is important for the pddl language to define the domain before
   * reading the problem
   */

  load_ops_file (ops_file);

 /*dirty trick to get another copy of gloaded_ops */
  gloaded_pl2ops = gloaded_ops;
  gloaded_ops = NULL;
  gdomain_name = NULL;
  gorig_initial_facts = NULL;
  gorig_goal_facts = NULL;
  gmetric_exp = NULL;
  gloaded_axioms = NULL;
  gparse_types = NULL;
  gparse_constants = NULL;
  gparse_predicates = NULL;
  gparse_functions = NULL;
  gparse_objects = NULL;
  gorig_constant_list = NULL;
  gpredicates_and_types = NULL;
  gfunctions_and_types = NULL;

  //free_PlOperator(gderived_predicates);
  gderived_pl2predicates = gderived_predicates;
  gderived_predicates = NULL;
  gnum_derived_predicates = 0;
  load_ops_file (ops_file);

  /* problem file (facts)
   */
  if (gcmd_line.display_info >= 1)
    {
      printf (" ... done.\nParsing problem file: ");
    }

  load_fct_file (fct_file);

  GpG.has_timed_preconds = NULL;
  GpG.fact_is_timed = NULL;

  /* instanzio i timed initial facts come operatori */
  if (gnum_tmd_init_fcts) {
    add_Timed_Facts_to_ops(&gloaded_ops);
    add_Timed_Facts_to_ops(&gloaded_pl2ops);
    GpG.timed_facts_present = TRUE;
    GpG.temporal_plan = TRUE;
  }
  /* Fine */

  if (gnum_derived_predicates) 
    GpG.derived_predicates = TRUE;

  /*add dummy effect to operators without boolean effects */
  add_dummy_effects (gloaded_ops);
  add_dummy_effects (gloaded_pl2ops);
  if (GpG.derived_predicates) {
    add_dummy_effects(gderived_predicates);
    add_dummy_effects(gderived_pl2predicates);
  }
  add_and_effect(gloaded_ops);
  add_and_effect(gloaded_pl2ops);

  /*counts numeric preconds and effects */
  count_num_preconds_and_effects ();
  GpG.gplan_actions = NULL;
  GpG.plan_actions_for_quality_mode = NULL;
  GpG.fixpoint_plan_length = 0;

  /* Elimino i timed facts dai fatti iniziali perchè li ho instanz come operatori */
  if (GpG.timed_facts_present)
    clear_Timed_Fact_Nodes();

  if (gcmd_line.display_info >= 1)
    printf (" ... done.\n\n");

  allocate_after_parser();

  /* now we have PlOperators and PlNodes */
  reduce_pddl2_to_pddl1 ();

  /* This is needed to get all types.
   */
  build_orig_constant_list ();

  /* last step of parsing: see if it's an ADL domain!
   */

  if (!make_adl_domain ())
    {
      printf ("\n%s: this is an ADL problem!", NAMEPRG);
      printf ("\n     can't be handled by this version.\n\n");
      exit (1);
    }

  /* now instantiate operators;
   */
  

  /**************************
   * first do PREPROCESSING *
   **************************/


  /* start by collecting all strings and thereby encoding
   * the domain in integers.
   */
  encode_domain_in_integers ();

  /* inertia preprocessing, first step:
   *   - collect inertia information
   *   - split initial state into
   *        _ arrays for individual predicates
   *        - arrays for all static relations
   *        - array containing non - static relations
   */
  do_inertia_preprocessing_step_1 ();

  /* normalize all PL1 formulae in domain description:
   * (goal, preconds and effect conditions)
   *   - simplify formula
   *   - expand quantifiers
   *   - NOTs down
   */
  normalize_all_wffs ();

  /* translate negative preconds: introduce symmetric new predicate
   * NOT-p(..) (e.g., not-in(?ob) in briefcaseworld)
   */
  translate_negative_preconds ();

  /* split domain in easy (disjunction of conjunctive preconds)
   * and hard (non DNF preconds) part, to apply
   * different instantiation algorithms
   */
  split_domain ();


  /***********************************************
   * PREPROCESSING FINISHED                      *
   *                                             *
   * NOW MULTIPLY PARAMETERS IN EFFECTIVE MANNER *
   ***********************************************/

  build_easy_action_templates ();

  /* PREDICATI DERIVATI*/
  if (GpG.derived_predicates)
    build_easy_derived_predicates_templates();
  /* END*/

  build_hard_action_templates ();

  /* PREDICATI DERIVATI*/
  if (GpG.derived_predicates)
    build_hard_derived_predicates_templates();
  /* END*/

  
  times (&end);
  TIME (gtempl_time);
  times (&start);


  check_time_and_length (0);	/* con zero non controlla la lunghezza */

  srandom(seed);

#ifdef __MY_OUTPUT__
  printf ("\nSeed %d  \n", seed);
#endif

  if (GpG.mode == INCREMENTAL)
    printf("\n\nModality: Incremental Planner\n\n");
  else
    if (GpG.mode == SPEED)
      printf("\n\nModality: Fast Planner\n\n");
    else
      if (GpG.mode == QUALITY)
	printf("\n\nModality: Quality Planner\n\n");


  /* perform reachability analysis in terms of relaxed
   * fixpoint
   */

  perform_reachability_analysis ();

  times (&end);
  TIME (greach_time);
  times (&start);

  check_time_and_length (0);	/* con zero non controlla la lunghezza */


  /* collect the relevant facts and build final domain
   * and problem representations.
   */

  collect_relevant_facts ();

  times (&end);
  TIME (grelev_time);
  times (&start);

  check_time_and_length (0);	/* con zero non controlla la lunghezza */


  /* now build globally accessable connectivity graph
   */
  build_connectivity_graph ();

  /* PREDICATI DERIVATI */
  if (GpG.derived_predicates) 
    create_final_derived_predicates();
  /* END */

  times (&end);
  TIME (gconn_time);
  times (&start);

  check_time_and_length (0);	/* con zero non controlla la lunghezza */

  /* associa ad ogni gef_conn[i] il ploperator completo corrispondente */
  associate_PlOperator_with_EfConn ();

  /* aggiunge le grandezze numeriche composte */
  add_composite_vars (0, gfirst_suspected_ef_conn);

  /* elimina le azioni inutili */
  check_actions_utility();

  make_numgoal_state(GpG.numeric_goal_PlNode);

  //rende costantemente falsi i confronti tra grandezze numeriche non inizializzate
  //serve per quei casi tipo zenotravel in cui le connessioni vengono fissate dalla presenza o meno dell'inizializzazione di 'distance'
  make_false_all_checks_on_not_init ();

  /* Semplification for inertial vars
   */
  propagate_inertias ();

#ifdef __MY_OUTPUT__
  if (DEBUG0)
    if (GpG.non_strips_domain)
      {
	//printf("\nThis is a non-strips domain");
	if (GpG.variable_duration)
	  printf ("\n\nAction durations have been computed");
	else
	  printf ("\n\nThere is no action duration to compute\n");
      }
#endif
  
  /* Set vars orig_weight_cost and orig_weight_time according with plan evaluation metric
   */
  if (goptimization_exp != -1)
    set_cost_and_time_coeffs ();

  /* Make numeric effects structure
   */
  create_descnumeff_of_efconns ();

  /* Sets flag is_numeric for each action (efconn)
   */
  set_numeric_flag ();

  /* Copy initial state in  initial_state
   */
  /*
    for (i = 0; i < gnum_comp_var; i++)
    ginitial_state.V[i] = GCOMP_VAR_VALUE(i);
  */
  
  ginitial_state.V = calloc(max_num_value, sizeof(float));
  memcpy(ginitial_state.V, gcomp_var_value, gnum_comp_var * sizeof(float));
  
  /* split actions */
  if (GpG.durative_actions_in_domain) {

    EfConn *contraddicting_ef_conns = NULL;
    int num = gnum_ef_conn -  gfirst_suspected_ef_conn;
    
    // Se ci sono azioni con effetti contraddittori le tolgo momentaneamente del gef_conn
    if (num > 0)
      {
	contraddicting_ef_conns = (EfConn *)calloc((num + 1), sizeof(EfConn));
	memcpy(contraddicting_ef_conns, &gef_conn[gfirst_suspected_ef_conn], num * sizeof(EfConn));
	gnum_ef_conn = gfirst_suspected_ef_conn;
      }
    
    split_actions();
    
    if (GpG.splitted_actions) {

      gnum_ef_conn = gextended_ef_conn;
      gnum_ft_conn = gextended_ft_conn;
      gnum_ef_block = gextended_ef_block;
      gnum_ft_block = (gnum_ft_conn >> 5) + 1;
      gfirst_suspected_ef_conn = gnum_ef_conn;

      // reinserisco le eventuali azioni con effetti contraddittori in coda al gef_con
      if (num > 0)
	{
	  if ((gnum_ef_conn + num) >= max_num_efconn) 
	    {
	      max_num_efconn += MAX_EF_FT_INCREASE;
	      gef_conn = (EfConn *)realloc(gef_conn, max_num_efconn * sizeof(EfConn));
	      memset(&gef_conn[gnum_ef_conn], 0, max_num_efconn - gnum_ef_conn);
	    }
	  
	  memcpy(&gef_conn[gnum_ef_conn], contraddicting_ef_conns,  num * sizeof(EfConn));
	}
    }
    
    gnum_ef_conn += num;
    
  }

  /* cerca i timed facts in gef_conn e salva gli indici in gtimed_facts_idx */
  if (GpG.timed_facts_present) {
    search_timed_facts_idx();
    make_timed_fct_vector();
    extract_timed_preconditions();

    if (!GpG.timed_preconditions) {
#ifdef __MY_OUTPUT__
      printf("\n\nNo timed in preconditions : disable timed");
#endif
      GpG.timed_facts_present = FALSE;
    }

  }


  set_continuous_effects();


  if (DEBUG0)
    {
      printf ("\n\n\nAnalyzing Planning Problem:");
      printf ("\n\tTemporal Planning Problem: %s", GpG.temporal_plan ? "YES" : "NO");
      printf("\n\tNumeric Planning Problem: %s", (GpG.is_domain_numeric)?"YES":"NO");
      printf("\n\tProblem with Timed Initial Litearals: %s", GpG.timed_preconditions ? "YES" : "NO");
      //      printf("\n\tProblem with Timed Initial Litearals: %s", GpG.timed_facts_present ? "YES" : "NO");
      printf("\n\tProblem with Derived Predicates: %s", (GpG.derived_predicates)?"YES":"NO");
      printf("\n\nEvaluation function weights:\n     Action duration %.2f; Action cost %.2f\n\n", GpG.orig_weight_time, GpG.orig_weight_cost);
    }

  if(DEBUG1) {
    printf("\n\tSplitted actions: %s\n", (GpG.splitted_actions)?"YES":"NO");
    if (GpG.splitted_actions)
      printf("\nNum extended actions (normal + splitted): %d (%d actions have been splitted)\n", gextended_ef_conn, (gextended_ef_conn - gnum_ef_conn)/2); 
  }



  times (&end);
  TIME (gnum_time);
  times (&start);

  /* Print information about action istantiation
   */
  print_parser_info_for_debug();

  //  if (GpG.numrestart > 0 && GpG.numtry > 0) {

    if (DEBUG0 && !DEBUG1) {
      printf ("\nComputing mutex... ");
      fflush (stdout);
    }
    if (DEBUG1)
      printf ("\n\n--- COMPUTE MUTEX BETWEEN FACTS ---\n");

    if (GpG.accurate_cost >= 0)
    {	
      allocate_reachability_information_data();


      allocate_reachability_compvar_information_data();
     }

    /* Comute mutex between facts
    */

    calc_mutex (&ginitial_state);

    //  }


  times (&end);
  TIME (gmutex_ft_time);

  if (DEBUG2)
    printf ("\n");
  if (DEBUG1)
    printf ("\n   --> Compute mutex between facts TOTAL TIME: %12.2f",gmutex_ft_time);

  times (&start);
  //  if (GpG.numrestart > 0 && GpG.numtry > 0) {
    if (DEBUG1)
      printf ("\n\n--- COMPUTE MUTEX BETWEEN ACTIONS ---\n");
    /*Compute action-action, action_fact, fact-action mutex
     */
    calc_mutex_ops ();
 
   //}

  printf ("\n\n");
  exit (0);

}
