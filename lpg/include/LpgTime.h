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
 * File: LpgTime.h
 * Description: header file for temporal information management
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/ 




#ifndef __TIME_H 
#define __TIME_H       

void insert_time (ActNode_list infAction);
void update_time (ActNode_list infAction);

void compress_plan ();
void compress_numeric_plan();

void build_temporal_plan ();

int insert_propagation_list (ActNode_list infAction);

void forward_noop_propagation_time (NoopNode_list infNoop);
void forward_noop_remotion_time (NoopNode_list infNoop);
void noop_remotion_time (NoopNode_list infNoop);

void temporal_constraints (ActNode_list infAction);
void remove_temporal_constraints (int posAction);
int Econstraint_type(int posA, int levA, int posB, int levB);
int Econstraint_type_numeric(int posA, int posB);
int Accurate_Econstraint_type_numeric(int posA, int posB, int levA, int levB);

void get_total_time_plan ();
int get_causal_constraint_type(int posA, int levA, int posB, int levB, int ordering);
int get_constraint_type(int posA, int levA, int posB, int levB);

void reset_constraint_matrix ();
void reset_propagation_vect ();

/**
 * Funzioni aggiunte per la gestione dei timed facts
 **/
float find_temporal_interval(float t, ActNode_list infact, int *first_moved);
void update_timed_vect_data(int *PC_int, int *level, int ins_rem);

void insert_unsup_timed_fact(int fact_pos, int level);
void remove_unsup_timed_fact(FctNode_list false_tmd);

float check_time_interval(float tprec, ActNode_list infact);
void remove_all_unsup_tmd_of_act(ActNode_list infact);

int fix_unsup_timed_fact(constraints_list unsup_tmd_fct, int num, float new_time);

int choose_min_cost_unsup_tmd_fact ();
int define_neighborhood_for_timed_fact (register FctNode_list tofix, float *new_time, int initialize);

int check_unsup_tmd(void);

void slack_fact_from_act (constraints_list fix);

void insert_initial_timed_actions( void );

#endif
