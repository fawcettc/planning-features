/********************************************************************
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
 * File: H_relaxed.h
 * Description: header file for the "relaxed plan" heuristic (ICAPS-02)
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/ 




#ifndef _HRELAXED_H
#define _HRELAXED_H

struct _DG_ACT * calloc_dg_inform();

Bool update_dg_fact_list(int fact_pos, int *level_ptr, int num_actions, int best_act, float duration, float cost,int related_fact);
void delete_dg_fact_list(int fact_pos, int *level);


dg_num_inform_list update_num_dg_fact_list(int fact_pos, int *level_ptr, int num_actions, int best_increase,int best_decrease, int best_assign, float duration, float cost);

struct _DG_ACT_NUM * calloc_dg_num_inform();

void free_dg_num_inform(dg_num_inform_list dg_node);

int get_dg_fact_cost (int fact_pos,  int level, dg_inform_list * loc_dg_cost);

void build_relaxed_plan_for_next_goals( int level );
void build_relaxed_plan_from_action_for_next_goals(neighb_list neighb_act, node_cost_list n_cost );

int get_dg_num_fact_cost (register int fact_pos, register int level, dg_num_inform_list * loc_dg_num_cost);

float compute_constr_fact (int constraint, int fact_pos, int level, int initialize, int orig_level, float *cost, float *end_time);

inline float compute_relaxed_fact_cost (int Fact_position, int level, node_cost_list n_cost, int action_level, float max_time_for_timed_fact);

int insert_action_inlist (int pos, int fact);

int build_fast_relaxed_plan_for_fact ( int fact_pos, int level, int orig_level );

int choose_best_action_for_unsup_num_fact (int Fact_position, int level,
					   int *best_action, int *best_level, int action_level, float max_time_for_timed_fac);

float dg_action_cost (neighb_list neighb_act);

void ls_insert_fact_inlist (int pos);

float dg_insertion_action_cost (int act_pos, int level, node_cost_list n_cost, float max_time_for_timed_fac);

float max_neighborhood_evaluationd (int act_pos, int level, node_cost_list n_cost, float max_time_for_timed_fac);

float relaxed_neighborhood_evaluation (int act_pos, int level, node_cost_list n_cost, float max_time_for_timed_fac);

float best_action_evaluation ( int act_pos, int level, node_cost_list n_cost,  float max_time_for_timed_fact, node_cost_list max_n_cost);
void verify_cri_until_level(int level);

float search_for_pc_intervals(float t, int act_pos, int lev, int *num_Timed_Prec);
int num_action_for_unsup_num_precondition(int fact_pos, int level);


void build_relaxed_plan_for_next_goals( int level );
void build_relaxed_plan_from_action_for_next_goals(neighb_list neighb_act, node_cost_list n_cost );
void reset_supported_preconds();
void insert_supported_preconds(int fact);
void update_supported_precond_for_action(int action);



int fast_relaxed_plan_for_inconsistence ( int fact_pos, int level, int initialize);
void define_supported_fact_for_relaxed_plan_of_inconsistences(constraints_list const_fact, int initialize);
void search_step_check_supported_fact_in_relaxed_plan_for_inconsistences();
void build_total_supported_facts_relaxed_plan_bit_vector(int action, int level);
void verify_supported_fact_in_relaxed_plan_for_inconsistences(int action, int level, int* bit_vect_supp_fact);


void evaluate_mutex_in_relaxed_plan(int action, int level);

int compute_relaxed_plan_for_inconsistence ( int fact_pos,int constraint, int level, int orig_level, int initialize);

#endif
