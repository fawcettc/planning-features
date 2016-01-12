
/*********************************************************************
 * (C) Copyright 2014 Saarland University
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




/*********************************************************************
 * File: main.c
 * Description: TorchLight main routine, modified for feature collection
 *
 * Author: Joerg Hoffmann 2014
 * 
 *********************************************************************/ 








#include "torchlight.h"

#include "memory.h"
#include "output.h"

#include "parse.h"

#include "inst_pre.h"
#include "inst_easy.h"
#include "inst_hard.h"
#include "inst_final.h"

#include "relax.h"
#include "search.h"

#include "SG-DTGs.h"
#include "gDGs-lDGs.h"
#include "oDGplus.h"
#include "lEHC.h"


















/*
 *  ----------------------------- GLOBAL VARIABLES ----------------------------
 */












/*******************
 * GENERAL HELPERS *
 *******************/








/* used to time the different stages of the planner
 */
float gtempl_time = 0, greach_time = 0, grelev_time = 0, gconn_time = 0;
float gsearch_time = 0, gSG_DTG_time = 0, gSG_DTG_static_analyze_time = 0, ganalyze_global_time = 0;
float ganalyze_local_ini_lDG_time = 0, ganalyze_local_ini_oDGplus_time = 0;
float ganalyze_local_sample_lDG_time = 0, ganalyze_local_sample_oDGplus_time = 0;
float gsampling_time = 0, grelaxed_plan_time = 0, gFDvariables_time = 0;
float ganalyze_local_sample_monotoneEHC_time = 0;


/* the command line inputs
 */
struct _command_line gcmd_line;

/* number of states that got heuristically evaluated
 */
int gevaluated_states = 0;

/* maximal depth of breadth first search
 */
int gmax_search_depth = 0;





/***********
 * PARSING *
 ***********/





/* resulting name for ops file
 */
char gops_file[MAX_LENGTH] = "";
/* same for fct file 
 */
char gfct_file[MAX_LENGTH] = "";


/* used for pddl parsing, flex only allows global variables
 */
int gbracket_count;
char *gproblem_name;

/* The current input line number
 */
int lineno = 1;

/* The current input filename
 */
char *gact_filename;

/* The pddl domain name
 */
char *gdomain_name = NULL;

/* loaded, uninstantiated operators
 */
PlOperator *gloaded_ops = NULL;

/* stores initials as fact_list 
 */
PlNode *gorig_initial_facts = NULL;

/* not yet preprocessed goal facts
 */
PlNode *gorig_goal_facts = NULL;

/* axioms as in UCPOP before being changed to ops
 */
PlOperator *gloaded_axioms = NULL;

/* the types, as defined in the domain file
 */
TypedList *gparse_types = NULL;

/* the constants, as defined in domain file
 */
TypedList *gparse_constants = NULL;

/* the predicates and their arg types, as defined in the domain file
 */
TypedListList *gparse_predicates = NULL;

/* the objects, declared in the problem file
 */
TypedList *gparse_objects = NULL;


/* connection to instantiation ( except ops, goal, initial )
 */

/* all typed objects 
 */
FactList *gorig_constant_list = NULL;

/* the predicates and their types
 */
FactList *gpredicates_and_types = NULL;












/*****************
 * INSTANTIATING *
 *****************/









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
int gmember_nr[MAX_CONSTANTS][MAX_TYPES];/* nr of object within a type */
int gtype_size[MAX_TYPES];
int gnum_types = 0;
Token gpredicates[MAX_PREDICATES];
int garity[MAX_PREDICATES];
int gpredicates_args_type[MAX_PREDICATES][MAX_ARITY];
int gnum_predicates = 0;





/* the domain in integer (Fact) representation
 */
Operator_pointer goperators[MAX_OPERATORS];
int gnum_operators = 0;
Fact *gfull_initial;
int gnum_full_initial = 0;
WffNode *ggoal = NULL;




/* stores inertia - information: is any occurence of the predicate
 * added / deleted in the uninstantiated ops ?
 */
Bool gis_added[MAX_PREDICATES];
Bool gis_deleted[MAX_PREDICATES];



/* splitted initial state:
 * initial non static facts,
 * initial static facts, divided into predicates
 * (will be two dimensional array, allocated directly before need)
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



/* so called Templates for easy ops: possible inertia constrained
 * instantiation constants
 */
EasyTemplate *geasy_templates;
int gnum_easy_templates;



/* first step for hard ops: create mixed operators, with conjunctive
 * precondition and arbitrary effects
 */
MixedOperator *ghard_mixed_operators;
int gnum_hard_mixed_operators;



/* hard ''templates'' : pseudo actions
 */
PseudoAction_pointer *ghard_templates;
int gnum_hard_templates;



/* store the final "relevant facts"
 */
Fact grelevant_facts[MAX_RELEVANT_FACTS];
int gnum_relevant_facts = 0;
int gnum_pp_facts = 0;



/* the final actions and problem representation
 */
Action *gactions;
int gnum_actions;
State ginitial_state;
State ggoal_state;









/**********************
 * CONNECTIVITY GRAPH *
 **********************/







/* one ops (actions) array ...
 */
OpConn *gop_conn;
int gnum_op_conn;



/* one effects array ...
 */
EfConn *gef_conn;
int gnum_ef_conn;



/* one facts array.
 */
FtConn *gft_conn;
int gnum_ft_conn;









/*******************
 * SEARCHING NEEDS *
 *******************/








/* the goal state, divided into subsets
 */
State *ggoal_agenda;
int gnum_goal_agenda;



/* byproduct of fixpoint: applicable actions
 */
int *gA;
int gnum_A;



/* communication from extract 1.P. to search engines:
 * 1P action choice
 */
int *gH;
int gnum_H;



/* the effects that are considered true in relaxed plan
 */
int *gin_plan_E;
int gnum_in_plan_E;



/* always stores (current) serial plan
 */
int gplan_ops[MAX_PLAN_LENGTH];
int gnum_plan_ops = 0;



/* stores the states that the current plan goes through
 * ( for knowing where new agenda entry starts from )
 */
State gplan_states[MAX_PLAN_LENGTH + 1];










/************************************
 * GLOBAL VARS FOR CG-->H+ ANALYSIS *
 ************************************/




/* the vars, parsed from FD
 */
Variable *gvariables;
int gnum_variables;



/* the support graph
 */
SG gSG;



/* the DTG for each var
 */
DTG *gDTGs;



/* just a helper...
 */
int *ggoal_on_var;



/* must communicate relaxed plan to oDGplus analysis.
 */
int *grplan;
int gnum_rplan;



/* to communicate back analysis results
 */
Bool gsuccess;
int ged_bound;
Bool gdead_end;

float gsuccess_percentage;
int gmin_ed_bound;
float gmean_ed_bound;
int gmax_ed_bound;
float gdead_end_percentage;



/* the sample states.
 */
State *gsample_states;



/* the data output file, if wanted.
 */
FILE *goutput_file;


/* Joerg2014: global vars needed for new features introduced in this
   version of TorchLight
 */

/* global analysis: features here simply count the number of gDGs that
   fail due to a particular reason (sum may be > 100%, each possible
   reason is tested independently)
 */
int ggDG_num_fail_cyclic;
int ggDG_num_fail_t0notadequate;
int ggDG_num_fail_nonleavesnotadequate;

/* approximate local analysis
 */
/* same as for global analysis
 */
int goDGplus_num_fail_cyclic;
int goDGplus_num_fail_t0notadequate;
int goDGplus_num_fail_nonleavesnotadequate;
/* Joerg2014: new count, to measure stats at attempt-level as
   opposed to sample-state level 
*/    
int goDGplus_num_graphs; 
/* positive features ie from success
 */
int goDGplus_num_succ_t0;
int goDGplus_num_succ_t0adequateRFCempty;
int goDGplus_num_succ_t0adequateRFCrecovered;
int goDGplus_num_succ_nonleavesDTGt;
int goDGplus_num_succ_nonleavesDTGtnoseff;
int goDGplus_num_succ_nonleavesDTGtirrdel;
int goDGplus_num_succ_nonleavesDTGtirrseffdel;


/* for diagnosis!
 *
 * First of all, a flag whether we're actually diagnosing the reasons
 * for negative outcome -- on option, we want to do this diagnosis
 * only for those states for which actually had this outcome. The
 * outcome will be known only posthum so have to run analysis two
 * times.
 */
Bool gdo_negative_diagnosis;

/* counts of how many successful/failed analysis attempts
 */
int ggDG_num_graphs;/* for gDG, also need to count number of graphs considered */
int ggDG_num_successes;
int glDG_num_successes; /* here num trials is simply number of samples */
int goDGplus_num_successes;

/* collect pair of op0-actionname and ft-pred of RFS Intersect.
 */
int *goDGplus_nonrecovered_RFC_intersect_preds;
int *goDGplus_nonrecovered_RFC_intersect_op0s;/* index into goperators array! */
int *goDGplus_nonrecovered_RFC_intersects_weights;
int goDGplus_num_nonrecovered_RFC_intersects;
int goDGplus_nonrecovered_RFC_intersects_totalweight;
/* Joerg2014: new count in order to be able to give back a meaningful
   feature: number of delete effect predicates considered to be
   harmful (according to previous diagnosis).
 */
int gnum_delete_predicates;

/* for EHC run, checking the "predictive quality" of the sampling.
 */
int gEHC_success;
int gEHC_max_search_depth;
float gEHC_time = 0;
Bool doing_EHC = FALSE; /* flag indicating that we're now no longer in analysis mode */ 



/* signal to EHC that we're not actually doing search but local-EHC
 * analysis
 */
Bool gdoing_EHCanalyze = FALSE;






















/*
 *  ----------------------------- HEADERS FOR PARSING ----------------------------
 * ( fns defined in the scan-* files )
 */







void get_fct_file_name( char *filename );
void load_ops_file( char *filename );
void load_fct_file( char *filename );











/*
 *  ----------------------------- MAIN ROUTINE ----------------------------
 */











int main( int argc, char *argv[] )

{

  struct tms start, end;
  int i, j, op;

  int maxw;
  int maxi;
  Bool gotone;
  float oDGsuccessrate;

  int N1, N2, N3, N4, N5, N6, N7, N8, N9, N10, N11, N12, N13;

  Effect *e;
  Literal *l;
  Bool *have_predicate;

  /* command line treatment
   */
  gcmd_line.use_FD = TRUE;

  gcmd_line.num_samples = 10;
  gcmd_line.depth_samples = 5;

  gcmd_line.do_gDG = TRUE;
  gcmd_line.do_lDG = FALSE;
  gcmd_line.do_SG_root = TRUE;
  /* Joerg2014: This was FALSE by default. FALSE means that, given a
     sample state s, as soon as we find a succeeding oDGplus for s, we
     stop ie we do not generate any further oDG+ for s. TRUE mans that
     we keep generating oDGplus, and "optimize" over the exit distance
     bounds delivered. I opted to do this now as (a) it seems more
     faithful for staistics, as extracted now, over the set of all
     oDGplus generated as opposed to over the set of sample states; as
     (b) it may also be somewhat more informative reg exit distance
     bounds; (c) I don't expect this to take significan runtime
     anyhow.
   */
  gcmd_line.optimize_over_op0var0 = TRUE;
  /* Joerg2014: This was FALSE by default but I really don't see a point in that 
   */
  gcmd_line.prune_useless_var0 = TRUE;
  gcmd_line.replacement_level = 2;
  gcmd_line.do_recoverer_only_relevant = TRUE;

  gcmd_line.do_diagnose = TRUE; 
  gcmd_line.do_diagnose_gDG_successrate = TRUE;
  gcmd_line.do_diagnose_invertop0 = TRUE;
  gcmd_line.do_diagnose_ignore_exchangedvars = TRUE;
  gcmd_line.diagnose_prune_useless_var0 = TRUE;
  gcmd_line.show_case_weight = TRUE;

  gcmd_line.run_FF = FALSE;
  gcmd_line.run_only_FF = FALSE;
  gcmd_line.run_EHCanalyze = FALSE;
  gcmd_line.run_only_EHCanalyze = FALSE;

  gcmd_line.output_file = FALSE;

  gcmd_line.display_info = 1;
  gcmd_line.debug = 0;

  memset(gcmd_line.ops_file_name, 0, MAX_LENGTH);
  memset(gcmd_line.fct_file_name, 0, MAX_LENGTH);
  memset(gcmd_line.path, 0, MAX_LENGTH);
  memset(gcmd_line.fdr_path, 0, MAX_LENGTH);

  strncpy(gcmd_line.fdr_path, "./GENERATE-VARS/VARIABLES.txt", MAX_LENGTH);

  if ( argc == 1 || ( argc == 2 && *++argv[0] == '?' ) ) {
    ff_usage();
    exit( 1 );
  }
  if ( !process_command_line( argc, argv ) ) {
    ff_usage();
    exit( 1 );
  }


  /* make file names
   */

  /* one input name missing
   */
  if ( !gcmd_line.ops_file_name || 
       !gcmd_line.fct_file_name ) {
    fprintf(stdout, "\nTorchLight: two input files needed\n\n");
    ff_usage();      
    exit( 1 );
  }
  /* add path info, complete file names will be stored in
   * ops_file and fct_file 
   */
  sprintf(gops_file, "%s%s", gcmd_line.path, gcmd_line.ops_file_name);
  sprintf(gfct_file, "%s%s", gcmd_line.path, gcmd_line.fct_file_name);


  /* parse the input files
   */

  /* start parse & instantiation timing
   */
  times( &start );
  /* domain file (ops)
   */
  if ( gcmd_line.display_info >= 1 ) {
    printf("\nTorchLight: parsing domain file");
  } 
  /* it is important for the pddl language to define the domain before 
   * reading the problem 
   */
  load_ops_file( gops_file );
  /* problem file (facts)
   */  
  if ( gcmd_line.display_info >= 1 ) {
    printf(" ... done.\nTorchLight: parsing problem file"); 
  }
  load_fct_file( gfct_file );
  if ( gcmd_line.display_info >= 1 ) {
    printf(" ... done.\n\n");
  }

  /* This is needed to get all types.
   */
  build_orig_constant_list();

  /* last step of parsing: see if it's an ADL domain!
   */
  if ( !make_adl_domain() ) {
    printf("\nTorchLight: this is not a STRIPS problem!");
    printf("\n            can't be handled by this version.\n\n");
    exit( 1 );
  }


  /* now instantiate operators;
   */


  /**************************
   * first do PREPROCESSING * 
   **************************/


  /* start by collecting all strings and thereby encoding 
   * the domain in integers.
   */
  encode_domain_in_integers();

  /* inertia preprocessing, first step:
   *   - collect inertia information
   *   - split initial state into
   *        _ arrays for individual predicates
   *        - arrays for all static relations
   *        - array containing non - static relations
   */
  do_inertia_preprocessing_step_1();

  /* normalize all PL1 formulae in domain description:
   * (goal, preconds and effect conditions)
   *   - simplify formula
   *   - expand quantifiers
   *   - NOTs down
   */
  normalize_all_wffs();

  /* translate negative preconds: introduce symmetric new predicate
   * NOT-p(..) (e.g., not-in(?ob) in briefcaseworld)
   */
  translate_negative_preconds();

  /* split domain in easy (disjunction of conjunctive preconds)
   * and hard (non DNF preconds) part, to apply 
   * different instantiation algorithms
   */
  split_domain();


  /***********************************************
   * PREPROCESSING FINISHED                      *
   *                                             *
   * NOW MULTIPLY PARAMETERS IN EFFECTIVE MANNER *
   ***********************************************/

  build_easy_action_templates();
  build_hard_action_templates();

  times( &end );
  TIME( gtempl_time );

  times( &start );

  /* perform reachability analysis in terms of relaxed 
   * fixpoint
   */
  perform_reachability_analysis();

  times( &end );
  TIME( greach_time );

  times( &start );

  /* collect the relevant facts and build final domain
   * and problem representations.
   */
  collect_relevant_facts();

  times( &end );
  TIME( grelev_time );

  times( &start );

  /* now build globally accessable connectivity graph
   */
  build_connectivity_graph();

  /*  will use heuristic hence need to run this step.
   */
  initialize_relax();

  times( &end );
  TIME( gconn_time );
  



  /***********************************************************
   * SG-->H+ ANALYSIS! 
   ***********************************************************/

  /* Joerg2014: Modified the below to fix all default configuration
     parameters, and remove stuff that won't be called anyway given
     this fix. Also, reduced to a single output file, in readable
     format collecting all new features. And of course added the code
     spitting out those features.
  */

  /* first of all, let downward's preprocessor generate the multi-valued vars,
   * and parse them!
   */
  if ( gcmd_line.use_FD ) {
    if ( gcmd_line.display_info >= 1 ) {
      printf("\nTorchLight: running Fast-Downward translator to generate variables"); 
      fflush(stdout);
    }
  } else {
    if ( gcmd_line.display_info >= 1 ) {
      printf("\nTorchLight: reading finite-domain variables"); 
      fflush(stdout);
    }
  }
  times( &start );
  
  create_and_parse_variables();
  
  times( &end );
  TIME( gFDvariables_time );
  if ( gcmd_line.display_info >= 1 ) {
    printf(" ... done.");
    fflush(stdout);
  }



  if ( gcmd_line.display_info >= 1 ) {
    printf("\nTorchLight: creating SG and DTG structures"); 
    fflush(stdout);
  }
  times( &start );
  
  /* now create the varval linking in fts, and the pre/eff in ops!
   */
  create_ft_op_indices();
  
  /* now create the support graph and the DTGs!
   */
  create_SG_DTG();
  
  if ( gcmd_line.display_info >= 1 ) {
    printf(" ... done.");
    fflush(stdout);
  }
  
  times( &end );
  TIME( gSG_DTG_time );





  if ( gcmd_line.display_info >= 1 ) {
    printf("\nTorchLight: static examination of SG and DTG structures"); 
    fflush(stdout);
  }
  times( &start );
  
  /* determine SG and DTG static properties -- acylic, t invertible, etc.
   */
  determine_SG_DTG_static_properties();
  
  if ( gcmd_line.display_info >= 1 ) {
    printf(" ... done.\n\n");
    fflush(stdout);
  }
  
  times( &end );
  TIME( gSG_DTG_static_analyze_time );
  
  if ( gcmd_line.display_info > 1 ) {
    printf("\n\n========================VARIABLES:\n");
    for ( i = 0; i < gnum_variables; i++ ) {
      printf("\nVariable %d: ", i);
      print_Variable(i);
      printf("\n");
      for ( j = 0; j < gvariables[i].num_vals; j++) {
	print_Variable_Value(i, j, FALSE);
	printf("\n");
      }
      printf("Goal: ");
      if ( ggoal_on_var[i] == -1 ) {
	printf(" (no goal on this)");
      } else {
	print_Variable_Value(i, ggoal_on_var[i], FALSE);
      }
      printf("\n");
    }
    
    printf("\n\n========================OPs using Variables:\n");
    for ( op = 0; op < gnum_op_conn; op++ ) {
      if ( gop_conn[op].num_E == 0 ) {
	continue;
      }
      print_op_name(op);
      printf(": ");
      for ( i = 0; i < gop_conn[op].num_pre; i++ ) {
	print_Variable_Value(gop_conn[op].pre[i].var, gop_conn[op].pre[i].val, TRUE);
	if ( i < gop_conn[op].num_pre - 1 ) {
	  printf(", ");
	}
      }
      printf(" --> ");
      for ( i = 0; i < gop_conn[op].num_eff; i++ ) {
	print_Variable_Value(gop_conn[op].eff[i].var, gop_conn[op].eff[i].val, TRUE);
	if ( i < gop_conn[op].num_eff - 1 ) {
	  printf(", ");
	}
      }
      printf("\n");
    }
    
    printf("\n\n========================SUPPORT GRAPH:\n");
    print_SG();
    
    printf("\n\n========================DOMAIN TRANSITION GRAPHS:\n");
    for ( i = 0; i < gnum_variables; i++ ) {
      printf("\nVariable %d: ", i);
      print_Variable(i);
      printf("\n");
      print_DTG(i);
    }
  }





  printf("\n\nSTART-------------------------------------------------------------------------\n");
  printf("---META-INFORMATION---------------------------------------------------------------\n");
  printf("Input domain                    : %s\n", gops_file);
  printf("Input problem instance          : %s\n", gfct_file);
  printf("Number of sample states         : %d\n", gcmd_line.num_samples);
  fflush(stdout);

  /* we will always immediately close the output file, so that in case
   * the analysis fails somewhere we still have all the other data!
   */
  if ( gcmd_line.output_file ) {
    if ( (goutput_file = fopen( "TorchLight.txt", "w")) == NULL ) {
      printf("\nCan't open TorchLight.txt output file!\n\n");
      exit(1);
    }
    fprintf(goutput_file, "START-----------------------------------------------------------------------------\n");
    fprintf(goutput_file, "---META-INFORMATION---------------------------------------------------------------\n");
    fprintf(goutput_file, "Input domain                    : %s\n", gops_file);
    fprintf(goutput_file, "Input problem instance          : %s\n", gfct_file);
    fprintf(goutput_file, "Number of sample states         : %d\n", gcmd_line.num_samples);
    fclose(goutput_file);
  }




  /* Joerg2014: first, spit out features from static analysis.

     NOTE: I decided to NOT distinguish separate features for
     "replacability" and "recoverability"; these are things that were
     originally mainly motivated by particular benchmarks (simpletsp
     and rovers respectively), and my feeling is that such features
     would be more a "domain-recognizer" than make any generalizable
     statement about the structure of the domain. I follow the same
     strategy below, in both global analysis and approximate local
     analysis I do not include features giving stats on how often
     these two criteria were successful (as opposed to the standard
     criterion reasoning about the nature of the deletes of t0).
   */
  N1 = 0; N2 = 0; N3 = 0; N4 = 0; N5 = 0; N6 = 0; N7 = 0; N8 = 0; N9 = 0; N10 = 0; N11 = 0; N12 = 0; N13 = 0;
  for ( i = 0; i < gnum_variables; i++ ) {
    if ( gDTGs[i].all_invertible ) N1++;
    if ( gDTGs[i].all_no_side_effects ) N2++;
    if ( gDTGs[i].all_irrelevant_side_effect_deletes ) N3++;
    if ( gDTGs[i].var_is_SG_leaf ) {
      N4++;
      if ( gDTGs[i].LEAF_irrelevant_or_irrelevantseffdel_or_irrelevantseffrecoverableseffdel ) N5++;
    }
    if ( !gDTGs[i].var_is_SG_leaf ) {
      N6++;
      if ( gDTGs[i].NONLEAF_irrelevant_or_invertiblenoseff_or_irrelevantdeletes ) N7++;
    }
    for ( j = 0; j < gDTGs[i].num_transitions; j++ ) {
      N8++;
      if ( gDTGs[i].transitions[j].invertible ) N9++;
      if ( gDTGs[i].transitions[j].no_side_effects ) N10++;
      if ( gDTGs[i].transitions[j].irrelevant_side_effect_deletes ) N11++;
      if ( gDTGs[i].transitions[j].self_irrelevant_side_effect_deletes ) N12++;
      if ( gDTGs[i].transitions[j].irrelevant_own_delete ) N13++;
    }
  }

  printf("\n\n----------------------------------------------------------------------------------\n");
  printf("---DOMAIN TRANSITION GRAPHS (DTG-t: DTG transition)-------------------------------\n");
  /* Joerg2014: Actually this is disabled. was runtime critical in
     some benchmarks. Presumably of limited usefulness anyhow given we
     already consider the std causal graph in other features.
  */
  /* printf("Support graph is acyclic        : %3d /\* 1 : yes; 0: no *\/\n",  */
  /* 	  gSG.is_acyclic); */
  printf("Perc vars all DTG-t invertible  : %3d\n", 
	 (int) (((float) N1) / ((float) gnum_variables) * 100.0));
  printf("Perc vars all DTG-t no side-eff : %3d /* all no side effects */\n",  
	 (int) (((float) N2) / ((float) gnum_variables) * 100.0));
  printf("Perc vars all DTG-t irr side-eff: %3d /* all side effect deletes irrelevant */\n",  
	 (int) (((float) N3) / ((float) gnum_variables) * 100.0));
  printf("Perc well-behaved leaf vars     : %3d /* support graph leaf vars satisfying global TorchLight criterion */\n", 
	 N4 == 0 ? 0 : (int) (((float) N5) / ((float) N4) * 100.0));
  printf("Perc well-behaved nonleaf vars  : %3d /* support graph nonleaf vars satisfying global TorchLight criterion */\n", 
	 N6 == 0 ? 0 : (int) (((float) N7) / ((float) N6) * 100.0));
  printf("Perc DTG-t invertible           : %3d\n", 
	 (int) (((float) N9) / ((float) N8) * 100.0));
  printf("Perc DTG-t no side-ef f         : %3d /* no side effects */\n", 
	 (int) (((float) N10) / ((float) N8) * 100.0));
  printf("Perc DTG-t irr side-eff         : %3d /* all side effect deletes irrelevant */\n", 
	 (int) (((float) N11) / ((float) N8) * 100.0));
  printf("Perc DTG-t self-irr side-eff    : %3d /* all side effect deletes irrelevant, except for own precond */\n", 
	 (int) (((float) N12) / ((float) N8) * 100.0));
  printf("Perc DTG-t irr own-delete       : %3d /* start value of transition is irrelevant */\n", 
	 (int) (((float) N13) / ((float) N8) * 100.0));  
  fflush(stdout);

  if ( gcmd_line.output_file ) {
    if ( (goutput_file = fopen( "TorchLight.txt", "a")) == NULL ) {
      printf("\nCan't open TorchLight.txt output file!\n\n");
      exit(1);
    }
    fprintf(goutput_file, "----------------------------------------------------------------------------------\n");
    fprintf(goutput_file, "---DOMAIN TRANSITION GRAPHS (DTG-t: DTG transition)-------------------------------\n");
    /* Joerg2014: Actually this is disabled. was runtime critical in
       some benchmarks. Presumably of limited usefulness anyhow given
       we already consider the std causal graph in other features.
    */
    /* fprintf(goutput_file, "Support graph is acyclic        : %3d /\* 1 : yes; 0: no *\/\n",  */
    /* 	    gSG.is_acyclic); */
    fprintf(goutput_file, "Perc vars all DTG-t invertible  : %3d\n", 
	    (int) (((float) N1) / ((float) gnum_variables) * 100.0));
    fprintf(goutput_file, "Perc vars all DTG-t no side-eff : %3d /* all no side effects */\n",  
	    (int) (((float) N2) / ((float) gnum_variables) * 100.0));
    fprintf(goutput_file, "Perc vars all DTG-t irr side-eff: %3d /* all side effect deletes irrelevant */\n",  
	    (int) (((float) N3) / ((float) gnum_variables) * 100.0));
    fprintf(goutput_file, "Perc well-behaved leaf vars     : %3d /* support graph leaf vars satisfying global TorchLight criterion */\n", 
	    N4 == 0 ? 0 : (int) (((float) N5) / ((float) N4) * 100.0));
    fprintf(goutput_file, "Perc well-behaved nonleaf vars  : %3d /* support graph nonleaf vars satisfying global TorchLight criterion */\n", 
	    N6 == 0 ? 0 : (int) (((float) N7) / ((float) N6) * 100.0));
    fprintf(goutput_file, "Perc DTG-t invertible           : %3d\n", 
	    (int) (((float) N9) / ((float) N8) * 100.0));
    fprintf(goutput_file, "Perc DTG-t no side-eff          : %3d /* no side effects */\n", 
	    (int) (((float) N10) / ((float) N8) * 100.0));
    fprintf(goutput_file, "Perc DTG-t irr side-eff         : %3d /* all side effect deletes irrelevant */\n", 
	    (int) (((float) N11) / ((float) N8) * 100.0));
    fprintf(goutput_file, "Perc DTG-t self-irr side-eff    : %3d /* all side effect deletes irrelevant, except for own precond */\n", 
	    (int) (((float) N12) / ((float) N8) * 100.0));
    fprintf(goutput_file, "Perc DTG-t irr own-delete       : %3d /* start value of transition is irrelevant */\n", 
	    (int) (((float) N13) / ((float) N8) * 100.0));  
    fclose(goutput_file);
  }






  /* now do global analysis
   */
  times( &start );
  
  analyze_global();
  
  times( &end );
  TIME( ganalyze_global_time );
  
  printf("\n\n----------------------------------------------------------------------------------\n");
  printf("---GUARANTEED GLOBAL ANALYSIS (USES GLOBAL DEPENDENCY GRAPHS gDG)-----------------\n");
  printf("Perc successful gDG             : %3d /* = 100 ==> provably no local minima under h+ */\n", 
	 (int) (((float) ggDG_num_successes) / ((float) ggDG_num_graphs) * 100.0));
  printf("h+ exit distance bound          : %3d, %6.2f, %3d /* min, mean, max over successful gDGs (-1 if perc successful gDG = 0); perc successful gDG = 100 ==> max is a provable upper bound on exit distance under h+ */\n", 
	 ggDG_num_successes > 0 ? gmin_ed_bound : -1,
	 ggDG_num_successes > 0 ? gmean_ed_bound : -1,
	 ggDG_num_successes > 0 ? gmax_ed_bound : -1);
  printf("Perc gDG cyclic                 : %3d /* perc gDG cannot be successful because cyclic */\n", 
	 (int) (((float) ggDG_num_fail_cyclic) / ((float) ggDG_num_graphs) * 100.0));
  printf("Perc gDG t0 not Ok              : %3d /* perc gDG cannot be successful because deletes of t0 harmful */\n", 
	 (int) (((float) ggDG_num_fail_t0notadequate) / ((float) ggDG_num_graphs) * 100.0));
  printf("Perc gDG support not Ok         : %3d /* perc gDG cannot be successful because supporting var DTGs not suitable */\n", 
	 (int) (((float) ggDG_num_fail_nonleavesnotadequate) / ((float) ggDG_num_graphs) * 100.0));
  fflush(stdout);
    
  if ( gcmd_line.output_file ) {
    if ( (goutput_file = fopen( "TorchLight.txt", "a")) == NULL ) {
      printf("\nCan't open TorchLight.txt output file!\n\n");
      exit(1);
    }
    fprintf(goutput_file, "----------------------------------------------------------------------------------\n");
    fprintf(goutput_file, "---GUARANTEED GLOBAL ANALYSIS (USES GLOBAL DEPENDENCY GRAPHS gDG)-----------------\n");
    fprintf(goutput_file, "Perc successful gDG             : %3d /* = 100 ==> provably no local minima under h+ */\n", 
	    (int) (((float) ggDG_num_successes) / ((float) ggDG_num_graphs) * 100.0));
    fprintf(goutput_file, "h+ exit distance bound          : %3d, %6.2f, %3d /* min, mean, max over successful gDGs (-1 if perc successful gDG = 0); perc successful gDG = 100 ==> max is a provable upper bound on exit distance under h+ */\n", 
	    ggDG_num_successes > 0 ? gmin_ed_bound : -1,
	    ggDG_num_successes > 0 ? gmean_ed_bound : -1,
	    ggDG_num_successes > 0 ? gmax_ed_bound : -1);
    fprintf(goutput_file, "Perc gDG cyclic                 : %3d /* perc gDG cannot be successful because cyclic */\n", 
	    (int) (((float) ggDG_num_fail_cyclic) / ((float) ggDG_num_graphs) * 100.0));
    fprintf(goutput_file, "Perc gDG t0 not Ok              : %3d /* perc gDG cannot be successful because deletes of t0 harmful */\n", 
	    (int) (((float) ggDG_num_fail_t0notadequate) / ((float) ggDG_num_graphs) * 100.0));
    fprintf(goutput_file, "Perc gDG support not Ok         : %3d /* perc gDG cannot be successful because supporting var DTGs not suitable */\n", 
	    (int) (((float) ggDG_num_fail_nonleavesnotadequate) / ((float) ggDG_num_graphs) * 100.0));
    fclose(goutput_file);
  }






  /* now sample states for local analysis. First generate an array of
   * the states, so that we can use the same states in lDG and oDG+.
   */
  if ( gcmd_line.display_info >= 1 ) {
    printf("\n\nTorchLight: sampling random states"); 
      fflush(stdout);
  }
  times( &start );
  
  sample_states();
  
  times( &end );
  TIME( gsampling_time );
  if ( gcmd_line.display_info >= 1 ) {
    printf(" ... done.\n");
    fflush(stdout);
  }





   
  /* now analyze the samples using oDG+.
   */
  times( &start );
  
  analyze_samples_local_oDGplus();
  
  times( &end );
  TIME( ganalyze_local_sample_oDGplus_time );
  oDGsuccessrate = gsuccess_percentage;
  
  printf("\n\n----------------------------------------------------------------------------------\n");
  printf("---APPROXIMATE LOCAL ANALYSIS (USES OPTIMAL RPLAN DEPENDENCY GRAPHS oDG+)---------\n");
  printf("Perc dead end states            : %3d /* perc sample states where hFF = infty */\n", 
	 (int) gdead_end_percentage);
  printf("Perc successful states          : %3d /* perc sample states presumed not local minimum (ie, at least one oDG+ for the state succeeds) */\n", 
	 (int) gsuccess_percentage);
  printf("h+ exit distance bound          : %3d, %6.2f, %3d /* min, mean, max over those states presumed not local minimum */\n", 
	 gsuccess_percentage > 0 ? gmin_ed_bound : -1,
	 gsuccess_percentage > 0 ? gmean_ed_bound : -1,
	 gsuccess_percentage > 0 ? gmax_ed_bound : -1);
  printf("Perc successful oDG+            : %3d\n", 
	 goDGplus_num_graphs == 0 ? 0 : (int) (((float) goDGplus_num_successes) / ((float) goDGplus_num_graphs) * 100.0));
  printf("Perc succ oDG+ t0 RFCempty      : %3d /* no critical t0 deletes */\n", 
	 goDGplus_num_succ_t0 == 0 ? 0 : (int) (((float) goDGplus_num_succ_t0adequateRFCempty) / ((float) goDGplus_num_succ_t0) * 100.0));
  printf("Perc succ oDG+ t0 RFCrecovered  : %3d /* critical t0 deletes recovered inside relaxed plan */\n", 
	 goDGplus_num_succ_t0 == 0 ? 0 : (int) (((float) goDGplus_num_succ_t0adequateRFCrecovered) / ((float) goDGplus_num_succ_t0) * 100.0));
  printf("Perc succ oDG+-DTG-t no side-eff: %3d /* non-leaf DTG transitions with no side effects */\n", 
	 goDGplus_num_succ_nonleavesDTGt == 0 ? 0 : (int) (((float) goDGplus_num_succ_nonleavesDTGtnoseff) / ((float) goDGplus_num_succ_nonleavesDTGt) * 100.0));
  printf("Perc succ oDG+-DTG-t irr del    : %3d /* non-leaf DTG transitions with irrelevant deletes */\n", 
	 goDGplus_num_succ_nonleavesDTGt == 0 ? 0 : (int) (((float) goDGplus_num_succ_nonleavesDTGtirrdel) / ((float) goDGplus_num_succ_nonleavesDTGt) * 100.0));
  printf("Perc succ oDG+-DTG-t irr seffdel: %3d /* non-leaf DTG transitions with irrelevant side effect deletes */\n", 
	 goDGplus_num_succ_nonleavesDTGt == 0 ? 0 : (int) (((float) goDGplus_num_succ_nonleavesDTGtirrseffdel) / ((float) goDGplus_num_succ_nonleavesDTGt) * 100.0));
  printf("Perc oDG+ cyclic                : %3d /* perc oDG+ cannot be successful because cyclic */\n", 
	 goDGplus_num_graphs == 0 ? 0 : (int) (((float) goDGplus_num_fail_cyclic) / ((float) goDGplus_num_graphs) * 100.0));
  printf("Perc oDG+ t0 not Ok             : %3d /* perc oDG+ cannot be successful because deletes of t0 harmful */\n", 
	 goDGplus_num_graphs == 0 ? 0 : (int) (((float) goDGplus_num_fail_t0notadequate) / ((float) goDGplus_num_graphs) * 100.0));
  printf("Perc oDG+ support not Ok        : %3d /* perc oDG+ cannot be successful because supporting var DTGs not suitable */\n", 
	 goDGplus_num_graphs == 0 ? 0 : (int) (((float) goDGplus_num_fail_nonleavesnotadequate) / ((float) goDGplus_num_graphs) * 100.0));
  fflush(stdout);
  
  if ( gcmd_line.output_file ) {
    if ( (goutput_file = fopen( "TorchLight.txt", "a")) == NULL ) {
      printf("\nCan't open TorchLight.txt output file!\n\n");
      exit(1);
    }
    fprintf(goutput_file, "----------------------------------------------------------------------------------\n");
    fprintf(goutput_file, "---APPROXIMATE LOCAL ANALYSIS (USES OPTIMAL RPLAN DEPENDENCY GRAPHS oDG+)---------\n");
    fprintf(goutput_file, "Perc dead end states            : %3d /* perc sample states where hFF = infty */\n", 
	    (int) gdead_end_percentage);
    fprintf(goutput_file, "Perc successful states          : %3d /* perc sample states presumed not local minimum (ie, at least one oDG+ for the state succeeds) */\n", 
	    (int) gsuccess_percentage);
    fprintf(goutput_file, "h+ exit distance bound          : %3d, %6.2f, %3d /* min, mean, max over those states presumed not local minimum */\n", 
	    gsuccess_percentage > 0 ? gmin_ed_bound : -1,
	    gsuccess_percentage > 0 ? gmean_ed_bound : -1,
	    gsuccess_percentage > 0 ? gmax_ed_bound : -1);
    fprintf(goutput_file, "Perc successful oDG+            : %3d\n", 
	    goDGplus_num_graphs == 0 ? 0 : (int) (((float) goDGplus_num_successes) / ((float) goDGplus_num_graphs) * 100.0));
    fprintf(goutput_file, "Perc succ oDG+ t0 RFCempty      : %3d /* no critical t0 deletes */\n", 
	    goDGplus_num_succ_t0 == 0 ? 0 : (int) (((float) goDGplus_num_succ_t0adequateRFCempty) / ((float) goDGplus_num_succ_t0) * 100.0));
    fprintf(goutput_file, "Perc succ oDG+ t0 RFCrecovered  : %3d /* critical t0 deletes recovered inside relaxed plan */\n", 
	    goDGplus_num_succ_t0 == 0 ? 0 : (int) (((float) goDGplus_num_succ_t0adequateRFCrecovered) / ((float) goDGplus_num_succ_t0) * 100.0));
    fprintf(goutput_file, "Perc succ oDG+-DTG-t no side-eff: %3d /* non-leaf DTG transitions with no side effects */\n", 
	    goDGplus_num_succ_nonleavesDTGt == 0 ? 0 : (int) (((float) goDGplus_num_succ_nonleavesDTGtnoseff) / ((float) goDGplus_num_succ_nonleavesDTGt) * 100.0));
    fprintf(goutput_file, "Perc succ oDG+-DTG-t irr del    : %3d /* non-leaf DTG transitions with irrelevant deletes */\n", 
	    goDGplus_num_succ_nonleavesDTGt == 0 ? 0 : (int) (((float) goDGplus_num_succ_nonleavesDTGtirrdel) / ((float) goDGplus_num_succ_nonleavesDTGt) * 100.0));
    fprintf(goutput_file, "Perc succ oDG+-DTG-t irr seffdel: %3d /* non-leaf DTG transitions with irrelevant side effect deletes */\n", 
	    goDGplus_num_succ_nonleavesDTGt == 0 ? 0 : (int) (((float) goDGplus_num_succ_nonleavesDTGtirrseffdel) / ((float) goDGplus_num_succ_nonleavesDTGt) * 100.0));
    fprintf(goutput_file, "Perc oDG+ cyclic                : %3d /* perc oDG+ cannot be successful because cyclic */\n", 
	    goDGplus_num_graphs == 0 ? 0 : (int) (((float) goDGplus_num_fail_cyclic) / ((float) goDGplus_num_graphs) * 100.0));
    fprintf(goutput_file, "Perc oDG+ t0 not Ok             : %3d /* perc oDG+ cannot be successful because deletes of t0 harmful */\n", 
	    goDGplus_num_graphs == 0 ? 0 : (int) (((float) goDGplus_num_fail_t0notadequate) / ((float) goDGplus_num_graphs) * 100.0));
    fprintf(goutput_file, "Perc oDG+ support not Ok        : %3d /* perc oDG+ cannot be successful because supporting var DTGs not suitable */\n", 
	    goDGplus_num_graphs == 0 ? 0 : (int) (((float) goDGplus_num_fail_nonleavesnotadequate) / ((float) goDGplus_num_graphs) * 100.0));
    fclose(goutput_file);
  }

  /* now output "harmful effects" of t_0 which made oDGplus fail in
     approximate local analysis. we have to count the same predicate
     at most once for each operator
   */

  have_predicate = ( Bool * ) calloc( gnum_predicates, sizeof( Bool ) );
  gnum_delete_predicates = 0;
  for ( i = 0; i < gnum_operators; i++ ) {
    for ( j = 0; j < gnum_predicates; j++ ) {
      have_predicate[j] = FALSE;
    }
    for ( e = goperators[i]->effects; e; e = e->next ) {
      for ( l = e->effects; l; l = l->next ) {
	if ( l->negated && !have_predicate[l->fact.predicate] ) {
	  gnum_delete_predicates++;
	  have_predicate[l->fact.predicate] = TRUE;
	}
      }
    }
  }

  printf("\n\n----------------------------------------------------------------------------------\n");
  printf("---DIAGNOSIS----------------------------------------------------------------------\n");
  printf("Perc harmful delete effects     : %3d /* perc action effect delete predicates harmful to t0; (may be 0 even if ``Perc oDG+ t0 not Ok''>0: diagnosis does not consider strange cases) */\n",
	  (int) (((float) goDGplus_num_nonrecovered_RFC_intersects) / ((float) gnum_delete_predicates) * 100.0));
  fflush(stdout);
         
  if ( gcmd_line.output_file ) {
    if ( (goutput_file = fopen( "TorchLight.txt", "a")) == NULL ) {
      printf("\nCan't open TorchLight.txt output file!\n\n");
      exit(1);
    }
    fprintf(goutput_file, "----------------------------------------------------------------------------------\n");
    fprintf(goutput_file, "---DIAGNOSIS----------------------------------------------------------------------\n");
    fprintf(goutput_file, "Perc harmful delete effects     : %3d /* perc action effect delete predicates harmful to t0; (may be 0 even if ``Perc oDG+ t0 not Ok''>0: diagnosis does not consider strange cases) */\n",
	    (int) (((float) goDGplus_num_nonrecovered_RFC_intersects) / ((float) gnum_delete_predicates) * 100.0));
  }

  if ( goDGplus_num_nonrecovered_RFC_intersects > 0 ) {
    printf("----------------------------------------------------------------------------------\n");
    printf("Ranked list of harmful effects (op-name, pred-name, frequency):\n");

    if ( gcmd_line.output_file ) {
      fprintf(goutput_file, "----------------------------------------------------------------------------------\n");
      fprintf(goutput_file, "Ranked list of harmful effects (op-name, pred-name, frequency):\n");
    }

    gotone = TRUE;
    while ( gotone ) {
      gotone = FALSE;
      maxw = -1;
      maxi = -1;
      for ( i = 0; i < goDGplus_num_nonrecovered_RFC_intersects; i++ ) {	  
	if ( maxw == -1 || goDGplus_nonrecovered_RFC_intersects_weights[i] > maxw ) {
	  maxw = goDGplus_nonrecovered_RFC_intersects_weights[i];
	  maxi = i;
	}
      }
      if ( maxi != -1 ) {
	gotone = TRUE;

	printf("%s ", goperators[goDGplus_nonrecovered_RFC_intersect_op0s[maxi]]->name);
	printf("%s ", gpredicates[goDGplus_nonrecovered_RFC_intersect_preds[maxi]]);
	printf("%6.2f\n",
	       ((float) goDGplus_nonrecovered_RFC_intersects_weights[maxi]) /
	       ((float) goDGplus_nonrecovered_RFC_intersects_totalweight) * 100.0);	    
	
	if ( gcmd_line.output_file ) {
	  fprintf(goutput_file, "%s ", goperators[goDGplus_nonrecovered_RFC_intersect_op0s[maxi]]->name);
	  fprintf(goutput_file, "%s ", gpredicates[goDGplus_nonrecovered_RFC_intersect_preds[maxi]]);
	  fprintf(goutput_file, "%6.2f\n",
		  ((float) goDGplus_nonrecovered_RFC_intersects_weights[maxi]) /
		  ((float) goDGplus_nonrecovered_RFC_intersects_totalweight) * 100.0);	    
	}
	
	for ( j = maxi; j < goDGplus_num_nonrecovered_RFC_intersects-1; j++ ) {
	  goDGplus_nonrecovered_RFC_intersects_weights[j] = goDGplus_nonrecovered_RFC_intersects_weights[j+1];
	  goDGplus_nonrecovered_RFC_intersect_op0s[j] = goDGplus_nonrecovered_RFC_intersect_op0s[j+1];
	  goDGplus_nonrecovered_RFC_intersect_preds[j] = goDGplus_nonrecovered_RFC_intersect_preds[j+1];
	}
	  goDGplus_num_nonrecovered_RFC_intersects--;
      }
    }
  }

  printf("----------------------------------------------------------------------------------\n");
  printf("-------------------------------------------------------------------------------END\n");
  fflush(stdout);

  if ( gcmd_line.output_file ) {
    fprintf(goutput_file, "----------------------------------------------------------------------------------\n");
    fprintf(goutput_file, "-------------------------------------------------------------------------------END\n");
    fclose(goutput_file);
  }
  


  output_planner_info();



  printf("\n\n");
  exit( 0 );

}











/*
 *  ----------------------------- HELPING FUNCTIONS ----------------------------
 */












void output_planner_info( void )

{

  printf( "\n\nTime spent: %7.2f seconds instantiating %d easy, %d hard action templates", 
	  gtempl_time, gnum_easy_templates, gnum_hard_mixed_operators );
  printf( "\n            %7.2f seconds reachability analysis, yielding %d facts and %d actions", 
	  greach_time, gnum_pp_facts, gnum_actions );
  printf( "\n            %7.2f seconds creating final representation with %d relevant facts", 
	  grelev_time, gnum_relevant_facts );
  printf( "\n            %7.2f seconds building connectivity graph",
	  gconn_time );
  if ( gcmd_line.use_FD ) {
    printf( "\n            %7.2f seconds in FD translator generating variables", 
	    gFDvariables_time );
  } else {
    printf( "\n            %7.2f seconds reading variables",
	    gFDvariables_time );
  }
  printf( "\n            %7.2f seconds preparing support graph and DTGs", 
	  gSG_DTG_time );
  printf( "\n            %7.2f seconds statically analyzing support graph and DTGs", 
	  gSG_DTG_static_analyze_time );
  printf( "\n            %7.2f seconds in guaranteed global analysis", 
	  ganalyze_global_time );
  if ( gcmd_line.num_samples > 0 ) {
    printf( "\n            %7.2f seconds sampling states", 
	    gsampling_time );
    printf( "\n            %7.2f seconds in approximate local analysis of sample states", 
	    ganalyze_local_sample_oDGplus_time );
  }
  printf( "\nTL TOTAL TIME: %7.2f seconds, of which %7.2f were spent computing relaxed plans for analysis.",
	  gtempl_time + greach_time + grelev_time + gconn_time + gFDvariables_time + gSG_DTG_time + gSG_DTG_static_analyze_time + ganalyze_global_time + ganalyze_local_ini_lDG_time + ganalyze_local_ini_oDGplus_time + ganalyze_local_sample_lDG_time + ganalyze_local_sample_oDGplus_time, grelaxed_plan_time );

}



void ff_usage( void )

{

  printf("\nUsage of TorchLight:\n");

  printf("\nOPTIONS   DESCRIPTIONS\n\n");
  printf("-p <str>    path for operator and fact file\n");
  printf("-o <str>    operator file name\n");
  printf("-f <str>    fact file name\n");
  printf("-v <str>    path to finite-domain representation (use with -V, default is \"./GENERATE-VARS/VARIABLES.txt\"\n\n");

  printf("-F          produce output data File\n");
  printf("-V          do NOT use Fast Downward, put finite-domain vars into \"GENERATE-VARS/VARIABLES.txt\"\n");
  printf("-r <num>    random seed (preset: %d)\n\n",
	 gcmd_line.random_seed);

  printf("-s <num>    number of states to be sampled (preset: %d)\n\n",
	 gcmd_line.num_samples); 

  printf("-i <num>    run-time information level (preset: %d)\n",
	 gcmd_line.display_info);
  printf("      0     nothing\n");
  printf("      1     basic output and processing infos\n");
  printf("      2     + detailed analysis infos\n");
  printf("   > 100    various FF debugging infos\n\n");

  if ( 0 ) {
    printf("-i <num>    run-time information level( preset: 1 )\n");
    printf("      0     only times\n");
    printf("      1     problem name, planning process infos\n");
    printf("    101     parsed problem data\n");
    printf("    102     cleaned up ADL problem\n");
    printf("    103     collected string tables\n");
    printf("    104     encoded domain\n");
    printf("    105     predicates inertia info\n");
    printf("    106     splitted initial state\n");
    printf("    107     domain with Wff s normalized\n");
    printf("    108     domain with NOT conds translated\n");
    printf("    109     splitted domain\n");
    printf("    110     cleaned up easy domain\n");
    printf("    111     unaries encoded easy domain\n");
    printf("    112     effects multiplied easy domain\n");
    printf("    113     inertia removed easy domain\n");
    printf("    114     easy action templates\n");
    printf("    115     cleaned up hard domain representation\n");
    printf("    116     mixed hard domain representation\n");
    printf("    117     final hard domain representation\n");
    printf("    118     reachability analysis results\n");
    printf("    119     facts selected as relevant\n");
    printf("    120     final domain and problem representations\n");
    printf("    121     connectivity graph\n");
    printf("    122     fixpoint result on each evaluated state\n");
    printf("    123     1P extracted on each evaluated state\n");
    printf("    124     H set collected for each evaluated state\n");
    printf("    125     False sets of goals <GAM>\n");
    printf("    126     detected ordering constraints leq_h <GAM>\n");
    printf("    127     the Goal Agenda <GAM>\n");

  }

}



Bool process_command_line( int argc, char *argv[] )

{

  char option;

  while ( --argc && ++argv ) {
    if ( *argv[0] != '-' || strlen(*argv) != 2 ) {
      return FALSE;
    }
    option = *++argv[0];

    switch ( option ) {
    case 'V':
      gcmd_line.use_FD = FALSE;
      break;
    case 'F':
      gcmd_line.output_file = TRUE;
      break;
    default:
      if ( --argc && ++argv ) {
	switch ( option ) {
	case 'p':
	  strncpy( gcmd_line.path, *argv, MAX_LENGTH );
	  break;
	case 'o':
	  strncpy( gcmd_line.ops_file_name, *argv, MAX_LENGTH );
	  break;
	case 'f':
	  strncpy( gcmd_line.fct_file_name, *argv, MAX_LENGTH );
	  break;
    case 'v':
      strncpy( gcmd_line.fdr_path, *argv, MAX_LENGTH );
      break;
	case 'i':
	  sscanf( *argv, "%d", &gcmd_line.display_info );
	  break;
	case 'd':
	  sscanf( *argv, "%d", &gcmd_line.depth_samples );
	  break;
	case 's':
	  sscanf( *argv, "%d", &gcmd_line.num_samples );
	  break;
	case 'r':
	  sscanf( *argv, "%d", &gcmd_line.random_seed );
	  break;
	default:
	  printf( "\nff: unknown option: %c entered\n\n", option );
	  return FALSE;
	}
      } else {
	return FALSE;
      }
    }
  }


  if ( gcmd_line.num_samples < 0 ) {
    printf("\nNumber of samples (now %d) must be >= 1", gcmd_line.num_samples);
    return FALSE;
  }


  return TRUE;

}

