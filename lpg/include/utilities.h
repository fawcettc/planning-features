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
 * File: utilities.h
 * Description: header file for utility functions.
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/ 



#ifndef _UTILITIES_H
#define _UTILITIES_H

void insert_extended_unsupported_facts_for_action(int action, int level);

void print_act_eff_prec(int action, int level);

void forward_propagation (int from_level, int to_level);

void vectlevel_to_planops (int from_level, int to_level);

void add_planactions_to_planactions (PlanAction * plan_to_add, PlanAction * first_plan);

void create_all_min_array ();

void allocate_data_for_local_search();

int load_pddl2_plan (char *plan_file, PlanAction ** plan_actions, int start_level);

void store_temporal_action_vect (PlanAction ** plan_actions, int act_pos, float start_time, float duration);

void restore_empty_action_graph(State * start_state, State * end_state);
void load_quasi_sol();

void reset_bitarray (register int *vector, register int dim);

Bool is_term_condition_reached();
void remove_mutex_facts_in_bitvect (int fact, int *bit_vect);
void remove_action_mutex_facts_in_bitvect (int action, int *bit_vect);
void update_threated_facts_in_bitvect (int act_pos, int *bit_vect);

int is_fact_in_additive_effects (int act_pos, int fact_pos);
int is_fact_in_delete_effects (int act_pos, int fact_pos);
int is_fact_in_additive_effects_start (int act_pos, int fact_pos);
int is_fact_in_delete_effects_start (int act_pos, int fact_pos);
int is_fact_in_preconditions (int act_pos, int fact_pos);
int is_fact_in_preconditions_overall (int act_pos, int fact_pos);
int is_fact_in_preconditions_end (int act_pos, int fact_pos);
int fact_is_supported (int Fact_position, int Fact_level);
int is_fact_supported_in_relaxed_plan (int Fact_position, int Fact_level);

int is_fact_in_additive_effects_of_cond (int act_pos, int fact_pos);
int is_fact_in_delete_effects_of_cond (int act_pos, int fact_pos);
int is_fact_in_additive_effects_start_of_cond (int act_pos, int fact_pos);
int is_fact_in_delete_effects_start_of_cond (int act_pos, int fact_pos);
int is_fact_in_preconditions_of_cond (int act_pos, int fact_pos);
int is_fact_in_preconditions_overall_of_cond (int act_pos, int fact_pos);
int is_fact_in_preconditions_end_of_cond (int act_pos, int fact_pos);
int is_cond_action_applicable (int level, int pos);


int get_index_of_constant (char *arg);
float get_action_cost (int pos, int level, int *nullcost);
float get_cond_action_cost (int pos, int *nullcost);
float get_action_time (int pos, int level);
float get_fact_cost (int Fact_pos, int level, node_cost_list n_cost);
void set_fact_cost (FctNode_list Fact, node_cost_list n_cost);
float weight_cost (node_cost_list n_cost);

inline int count_bit1 (register int mask);

int check_mutex_noop_durative (register int position, int level);
int check_mutex_action (register int act_position, int level);
int check_mutex_noop (register int position, int level);
int count_mutex_noop (int noop_pos, int level);
int count_mutex_noop_at_start (int act_pos, int level);
inline int count_mutex_action (int act_pos, int level);

void insert_element_in_neighb (neighb_list n_elem);

void insert_treated_noop_chain (ActNode_list act, unsigned int pos);

void reset_neighborhood ();

int random_for_debug();

int is_plan_better ();
int is_quasi_sol_better ();

void reset_heuristic_parameters ();
void set_heuristic_parameters (int num_restart, int num_run);
int set_param (int num_unsat);
void reset_plan_param (int level, PlanAction ** plan_actions);

#ifndef __WINLPG__
float DeltaTime (struct tms start, struct tms end);
#else
void wintime(clock_t *t);
float DeltaTime (clock_t start, clock_t end);
#endif

void free_gplan_actions (PlanAction * gplan_actions);

void get_path (char *full_file_name, char *result);
void initialize_preset_values (void);

void lpg_usage (void);
void allocate_after_parser();



#ifdef __SUN__
float fabsf(float f);
#endif

void so_signal_management();

int cond_eff_is_enabled();

int count_mutex_facts (int act_pos, int level);

void reorder_fact_vect(int *facts, int numf);

void reorder_action_preconditions( void );

void intial_heuristic_param (void);

#endif
