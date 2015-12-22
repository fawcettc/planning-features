/**
 * File : derivedpred.h
 *
 * Funzioni per il calcolo dei Predicati derivati
 **/


//Flag per decidere se aggiungere o rimuovere un fatto
#define ADD_FACT 1
#define DEL_FACT -1
//Abilita (ON) o disabilita (OFF) il reset dei predicati derivati nella funzione calc_all_derived_predicates()
#define RESET_ON 1
#define RESET_OFF 0

#define MAX_NEW_DERIVED 10

int calc_all_derived_predicates(int level, int reset, int **result);

int calc_new_derived_predicates(int fct, int level, int add_del, int **result);

int calc_new_derived_predicates_from(int fct, int *my_precs, int *my_facts, int add_del, int **result);

int calc_all_derived_predicates_from(int *my_precs, int *my_facts, int reset, int **result);

void initialize_dp_num_prec_vector(int **precs);

int  search_for_base_preconds(int dp_fct, int index, int *tabu, int level, IntList *append, path_set *path, int call);

void create_gdp_path_for(int pd_fct, int level, path_set *path); 

indexed_vect_list *choose_best_facts_set(path_set *path, int *num_pc, int level, int to_level, float *best_cost, int *max_depth);

indexed_vect_list *choose_best_facts_set_fast(path_set *path, int *num_pc, int level, int to_level, float *best_cost, int *max_depth);

indexed_vect_list *dg_choose_best_facts_set(path_set *path, int *num_pc, int level);

indexed_vect_list *choose_best_tuple_and_level(path_set *path, int *num_facts, int level, int *best_level);

int choose_fact_to_support(indexed_vect_list *tuple, int num_f, int level);

void print_derived(int level);

int test_preconds_propagation(int from_level, int to_level, int *precs, int num);

float set_time_for_derived_predicates(int fct, int level, float fct_time);

void reset_gdp_path(path_set *path);

int compare_neighbors(neighb **A, neighb **B);

void trash_tuple(indexed_vect_list *tuple, int num);

int create_min_tuple_neighborhood(path_set *path, int pd_fct, int level);

int choose_best_action_for_derived_predicate(path_set *path, int pd_fct, int level, int *best_action, int *best_level, int action_level);
extern int *temp_dp_precs;

/* END */
