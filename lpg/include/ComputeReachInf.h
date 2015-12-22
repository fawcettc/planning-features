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
 * Description: header file for computing reachability information
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/ 



#ifndef _COMPUTEREACHINFO_H
#define _COMPUTEREACHINFO_H




void allocate_reachability_information_data();

void allocate_reachability_compvar_information_data(void);

void reset_computed_dg_costs (int level);
void set_computed_dg_costs (int level);

void  cri_compute_fact_cost (int pos);
int   cri_compute_action_cost (int pos,int times);

int cri_get_best_action_for_fct (int fact_pos);

void reset_cri_list();

void cri_insert_ftcost (int fact_pos, float cost, float duration, int num_actions,int best_ef);


float cri_predict_cost_relaxed (int action, float *duration_act, int *num_actions);
float cri_predict_cost_sum (int action, int *num_actions);
float cri_predict_cost_max (int action, int *num_actions);
float cri_predict_duration (int action, float *duration_act);

float cri_activate_distgraph_ef (int index, int *fact_vect, int *derived_prec, int level, Bool *changed);

inline void cri_heuristic_for_action (int action, int level);

void set_init_computed_dg_costs ();

void remove_mutex_facts_in_bitvect_and_update_num_actions (int fact, int *bit_vect);

void ri_sub_tested_vars_for_cvar (int ncvar, int * num_tested_positive,int * num_tested_negative,int *bitarray, Bool Sign);

void ri_add_tested_vars_for_cvar (int ncvar, int * num_tested_positive,int * num_tested_negative,int *bitarray, Bool Sign);

void ri_refresh_max_min_value (int * modifieds);

void ri_apply_action_effects_to_max_min_value(int action_number, int times);


float ri_eval_comp_var (CompositeNumVar * cv, int index ,float *max_values,float *min_values,Bool Sign);

Bool ri_set_best_for_compvar(int i, int * True_num,float *vmax, float *vmin,int *num_prec_vector);


void cri_insert_numeric_ftcost (int fact_pos, int action, int num_eff, int OPERATOR);

void  cri_update_for_fact (int orig_fact, int level);

void compute_reachability(State * initial_state);


int get_intermediate_reachab_inform(int fact, int level, dg_inform_list * loc_dg_cost  );

void update_intermediate_reachab_inform(int fact, int best_act,  int num_actions, float cost, float duration, int *level);
#endif
