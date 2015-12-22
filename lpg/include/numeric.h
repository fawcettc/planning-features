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
 * File: numeric.h
 * Description: header file for numerical quantity management
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/ 





#ifndef _NUMERIC_H
#define _NUMERIC_H

int is_var_in_cvar(int var, int cvar_index);
int is_var_in_prec_cvar(int var, int cvar_index);
int is_var_in_eff_cvar(int var, int cvar_index);

Bool is_num_prec_satisfied (int cvar, int level);
Bool is_num_prec_satisfied_after_start (int cvar, int level);
int is_num_prec_unsatisfied_applying_action(int cvar, TimeSpec prec_time, int level, int act); 

void set_numeric_flag ();

void create_descnumeff_of_efconns (void);
void create_descnumeff_of_efconn (int index);

void make_false_all_checks_on_not_init (void);

int define_neighborhood_for_numeric_actions (constraints_list unsup_numeric_fact, int initialize);
int choose_min_cost_unsup_num_fact ();

void eval_comp_var_non_recursive (int cv_index, float *in_vect, float *out_vect, int in_level, int out_level);

void refresh_cvars (int level);
void refresh_cvars_at_start (int level);
void propagate_cvars (int level_from, int level_to);

void copy_num_values_from_level_to_level (int level_from, int level_to, Bool check_variations);
void insert_values_unsup_num_fact (int status, int fact, int level);

float try_num_eff_in_level (int cv_index, float *in_vect, float *out_vect,Bool effect);

Bool is_num_prec_satisfied_in_common_level (int cvar);
Bool is_num_prec_satisfied (int cvar, int level);
Bool is_num_prec_satisfied_after_start (int cvar, int level);

void apply_numeric_effect_in_common_level (int num_eff,int times);
void apply_numeric_effects_of_action (int act_pos, int level);

void insert_unsup_numeric_fact (int cv_index, int level);

int fix_unsup_num_fact (constraints_list unsup_numeric_fact, int num);

void clean_unsup_num_fact ();

void remove_unsup_num_fact (int position);
void remove_numeric_effects_of_action (int act_pos, int level);

void remove_unappliable_actions ();
void reset_cvar_hash_table_effects();
void eval_comp_var_non_recursive_effects (int cv_index, float *in_vect, float *out_vect, int in_level, int out_level);

void sub_affects_list (int cv_index, int *bitarray);

void add_affects_list (int cv_index, int *bitarray);

int count_unsatisfied_preconds(int action_number,int *fact_vector); 

int  count_unsatisfied_num_preconds(int action_number,int *num_fact_vector);

Bool does_action_support_numeric_precond_in_down_level(int index,int action_pos, int level, int down_level);

int is_var_in_cvar(int var_index, int cvar_index);

int numprec_not_satisfied_after_action(int cvar, TimeSpec prec_time, int level, int act);

int is_var_in_cvar_effects(int var, int cvar_index);

#endif
