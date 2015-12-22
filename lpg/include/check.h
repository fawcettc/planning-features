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
 * File: check.h
 * Description: header for the check functions
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/ 



#ifndef _CHECK_H
#define _CHECK_H

void check_prev_and_next_links(void);

int check_ft_ft_mutex(int **temp_ft_ft_mutex);

int check_time_and_length (int plan_ops_num);

int check_plan (int max_time);
void check_temporal_plan ();

void check_consistency (int level);

void check_num_prec();

void refresh_cvars_bet (float *input_vector);

void control_numeric_of_plan();
void eval_comp_var_non_recursive_bet (int cv_index, float *in_vect, float *out_vect);

void test_cond_effect();

Bool check_cpu_time(float *plan_time);

#endif
