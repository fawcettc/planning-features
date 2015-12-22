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
 * File: ActionSubgraph.h
 * Description: header file for the action subgraph management 
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/ 




#ifndef __ACTSUBGRH_H 
#define __ACTSUBGRH_H  

int get_next(int level);
int get_prev(int level);

void free_noop_not_in (ActNode_list act);

void remove_false_fact (register FctNode_list inf_address);
void remove_treated_noop (register NoopNode_list inf_address); 

void insert_unsup_fact (register FctNode_list inf_address);

int insert_remove_action (int act_pos, int act_level, int ins_rem, int propagation);
void insert_treated_fact (register ActNode_list act_address, int noop_pos);

void restart_MetricMinimizeCost ();

void forward_noop_propagation (int position_fact, int curr_level);
int backward_precond_propagation (FctNode_list fact);
int backward_precond_remotion (FctNode_list fact, int propagation);

void restart_search ();

void compress_vectlevel();

int initialize (State * start_state, State * end_state, int num_restart);

def_level_list create_vectlevel (int fixpoint);

void insert_timed_facts_in_vectlevel( void );

void reset_plan (int max_time);

#endif

