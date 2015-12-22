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
 * File: inst_utils.h
 * Description: header file for instanciating functions
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/ 




#ifndef _INST_UTILS_H
#define _INST_UTILS_H


#define BIT_COL_SIZE(table, size) ((size >> table.n_bit) + 1)

int insert_ef_in_efconn(EfConn *ef);

/**
 * Bit tables for facts and actions instantiation
 **/
int init_bit_table_const(unsigned long int max_size, int *n_bit, int *base, int *bit_row_size);
int init_bit_table_row(bit_table table, int row, unsigned long int size);
void insert_bit_in_bit_table(bit_table table, int op, unsigned long int adr);
void delete_bit_from_bit_table(bit_table table, int op, unsigned long int adr);
Bool check_bit_in_bit_table(bit_table table, int op, unsigned long int adr);
int get_bit_table_block(bit_table table, int op, int pos);

/**
 * Hash table for NumVar instantiation
 **/
void reset_numvar_hash_table();
int numvar_adress(NumVar * v);
void insert_numvar_in_hash_table(NumVar *v, int item);
int retrieve_numvar_position(NumVar *v);

void initialize_vals_tables(void);

void add_implicit_preconds(Operator *op);


void associate_PlOperator_with_EfConn (void);

PlOperator *search_name_in_plops (char *plop_name);

void add_composite_vars (int from_ef_conn, int to_ef_conn);

int index_in_cvars_of_expression (PlNode * pln, int ind);

int get_numvar_index_of_fn_head (PlNode * p, int index);

void create_numvar_from_fn_head (NumVar * ret, PlNode * plnvar, int i);
void create_neighborhood_for_compvar (int index, Bool Sign, Bool MulOrDiv, action_set * neighbors, int start, int level);

int index_in_function_table_of (char *funct_name);

int get_index_of_arg (char *arg, PlOperator *plop);

void copy_compvar (CompositeNumVar * dest, CompositeNumVar * src);

int search_cvar_in_cvars (CompositeNumVar * cv, float cv_value);

OPERATOR_TYPE op_from_conn (Connective c);

float eval_comp_var (CompositeNumVar * cv, int index);
int get_num_of_effects_of (int index, TimeSpec ts, Bool is_additive);
int get_condeffect_pln_pos(CondEfConn *cef);
int is_bool_fact(PlNode *pln);

int get_num_of_preconds_of (int index, TimeSpec ts);
void add_index_to_affect_list_of (int affected_cvar, int affecting_var);

void add_effects_to_comp_vars (int from_ef_conn, int to_ef_conn);
void add_preconds_to_comp_vars (int from_ef_conn, int to_ef_conn);
void add_cond_effects_to_comp_vars(void);

void calc_duration_of_actions (int from_ef_conn, int to_ef_conn);

void calc_cost_of_actions (int from_ef_conn, int to_ef_conn);

void calc_cost_of_cond_actions (void);

void apply_numeric_effects_of_efconn (int index);
void apply_numeric_effects_of_condefconn (int index);

void reorder_conds_and_effects (void);

int get_fct_pos_from_plnode (PlNode * pln, PlOperator *plop, int op, int *start, int max);
void add_efconn_to_increase_list_of (int n_ef, int cvar);
void add_efconn_to_decrease_list_of (int n_ef, int cvar);
void add_condefconn_to_increase_list_of (int n_cef, int cvar);
void add_condefconn_to_decrease_list_of (int n_cef, int cvar);

void insert_cvar_in_hash (CompositeNumVar * cv);

Bool is_cvar_in_hash (CompositeNumVar * cv);

void set (int *start, int nbit);
void reset (int *start, int nbit);

int get (int *start, int nbit);

void reset_all (int *start, int length_in_bits);

int **alloc_matrix (int rows, int cols);

int **alloc_tri_matrix(int l);

int *alloc_vect (int n_els);

void set_rvals_for_cvar (int ef, int ncvar);
void set_lvals_and_rvals (void);

void propagate_inertias (void);

int are_mutex_ops (int a, int b);

int index_in_objects_table_of (char *obj_name);
void index_duration_exps (int from_ef_conn, int to_ef_conn);

int cvar_hash_index (CompositeNumVar * cv);

int position_in_functions_table (char *str);

NumVar *new_NumVar (void);
CompositeNumVar *new_CompositeNumVar (OPERATOR_TYPE op);
IntList *new_IntList (void);
SpecialFacts *new_SpecialFacts (void);

PlNode *cp_PlNode (PlNode *pln);

void cp_PlNode2list (PlNode *pln, PlNode **list );

void make_NumVar (NumVar * f, PlNode * n, int num_vars);
void make_VarAssign (NumVar * f, PlNode * n, int num_vars);
void make_compvar (CompositeNumVar * c, int c_index, NumVar * nv, int nv_index);

float evaluate_exp (PlNode * n);

void add_dummy_effects (PlOperator * operators);
void add_dummy (PlNode * pln);
void add_and_effect(PlOperator *operators);

void reset_cvar_hash_table();

void make_numgoal_state(PlNode *list);

void set_cost_and_time_coeffs (void);

int search_cvar_in_cvars_effects (CompositeNumVar * cv, float cv_value);

void insert_cvar_in_hash_effects (CompositeNumVar * cv);

int cvar_hash_index_effects (CompositeNumVar * cv);

void extract_timed_preconditions( void );

void check_actions_utility( void );

void split_actions( void );

void add_suspected_ef_conns_effects( void );

void set_continuous_effects(void);

#endif /* _INST_UTILS_H */

