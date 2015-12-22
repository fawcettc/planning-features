/**
 * File : derivedpred.c
 * 
 * Funzioni per il calcolo dei predicati derivati
 **/

#include <values.h>
#include "ff.h"
#include "lpg.h"
#include "output.h"
#include "LpgOutput.h"
#include "derivedpred.h" 
#include "utilities.h"
#include "memory.h"
#include "ActionSubgraph.h"
#include "inst_utils.h"
#include "H_max.h"
#include "H_relaxed.h"





/**
   Variabili globali utilizzate per il calcolo dei predicati derivati
   **
   Global variables used for computing derived predicates truth value
**/




/* table of visited  predicate
 */
int *table = NULL;
            
/* Number of unsatisfied preconditions for each rule
 */        
int *gnum_dp_precs = NULL;            
 
/* bit vector of facts of the given state for the rule computation
 */                                       
int *facts = NULL;                     

/* rules used for each derived predicate that becames true
 */
int *used_rules =NULL;

/* bit vector of rules that becames not appliable.
 * It is used during the back propagation of w_is_goal remotion
 */
int *prop_dp_index = NULL;            

/* temporary tuples of facts needed to support a derivation path
 */
int *temp_pc_vect = NULL;   

/* temporary vector of preconditions for a rule: used in H_relaxed.c 
 */          
int *temp_dp_precs = NULL;

/* Actions already inserted in neighborhood
 */
int *neighb_actions = NULL; 

/* List of derived predicates to review after a propagation (they are false
 * but should be supported by some other rule)
 */
IntList *review_list = NULL;


indexed_vect_list  **trash = NULL;  
IntList *old_list = NULL, *aux_list = NULL;
int *changed_dp = NULL;




/********** Funzioni di utilità e debug *****  Utilities and debug functions **********/

/**
 * Resetta il bitvector usato per propagare correttamente w_is_goal
 * sui predicati derivati
 *
 * Reset the bitvector used for w_is_goal propagation 
 **/
void reset_prop_index() {

  if (!prop_dp_index) 
    prop_dp_index = (int *)calloc(gnum_dp_block, sizeof(int));

  memset(prop_dp_index, 0, gnum_dp_block * sizeof(int));
}


/**
 * Inizializza un vettore usato per calcolare senza ripetizioni i predicati derivati
 *
 * Initialize a table used to avoid repetitions during the rules evaluation
 **/
void init_table() {

  if (!table)
    table = (int *)calloc(gnum_ft_conn, sizeof(int));
   
  memset(table, -1, gnum_ft_conn * sizeof(int));

}


void free_table() {
  
  free(table);

}



#ifdef __DP_TYPE_CHECK__ 
/**
 * Ritorna 1 se l'operatore di derivazione dp non ha precondizioni false sia di base che derivate  
 **/
int check_dp_preconds(int dp) {
  
  int i, type = 0;

  for (i = 0; i < gdp_conn[dp].num_PC; i++) 
    if (!GET_BIT(facts, gdp_conn[dp].PC[i])) {
      type = gft_conn[gdp_conn[dp].PC[i]].fact_type;
      break;
    }
    
  for (i = i + 1; i < gdp_conn[dp].num_PC; i++)
    if (!GET_BIT(facts, gdp_conn[dp].PC[i])
	&& (type != gft_conn[gdp_conn[dp].PC[i]].fact_type))
      return 0;

  return 1;
  
}
#endif


int check_list(IntList *l, IntList *p) {
  IntList *t;
  for (t = l; t; t = t->next)
    if (t == p) {
      printf("\n\nOCIO");
      fflush(stdout);
    }

  return 0;
}


/**
 * Stampa una regola di derivazione
 *
 * Print a rule
 **/
void print_derived(int level) {
  int i, j;

  facts = vectlevel[level] -> fact_vect;
  gnum_dp_precs = vectlevel[level] -> gnum_dp_precs;

  for (i = 0; i < gnum_dp_conn; i++) {
    printf("\nEFFECT :");
    print_ft_name(gdp_conn[i].add);
    printf(" : %s", (GET_BIT(facts, gdp_conn[i].add))?"TRUE":"FALSE");
    printf("\n PRECONDITIONS : %d :", gnum_dp_precs[i]);
    for (j = 0; j < gdp_conn[i].num_PC; j++) {
      print_ft_name(gdp_conn[i].PC[j]);
      printf(" : %s", (GET_BIT(facts, gdp_conn[i].PC[j]))?"TRUE":"FALSE");
    }
  }

}


/**
 * Stampa la lista dei predicati derivati da rivedere
 *
 * Print the review list
 **/
void print_review(void) {
  IntList *tmp;
  printf("\nREVIEW: ");
  for (tmp = review_list; tmp; tmp = tmp->next)
    printf("-%d", tmp->item);
}


IntList *get_IntList( void ) {

  IntList *tmp;

  if (old_list) {
    tmp = old_list;
    old_list = tmp->next;
    tmp->next = NULL;
  }
  else
    tmp = new_IntList();

  return tmp;

}


void trash_tuple(indexed_vect_list *tuple, int num) {

  tuple -> next = trash[num];
  trash[num] = tuple;

}


void trash_tuple_lists(path_set *path) {

  indexed_vect_list *tmp = NULL;
  int i;
 
  for (i = 0; i <= path->size; i++) {
  
    for (tmp = path->tuple_set[i]; (tmp) && (tmp->next); tmp = tmp->next);
   
    if (tmp) {
      tmp->next = trash[i];
      trash[i] = path->tuple_set[i];
      path->tuple_set[i] = NULL;
    }
  
  }

}


/**
 * Inserisce un predicato derivato da rimuovere nella lista dei fatti da 
 * rivedere 
 *  
 * Insert a derived predicate that will be removed in the list of 
 * predicates to review after the propagation.
 **/
void insert_in_review_list(int fct) {

  IntList *tmp;

  if (DEBUG5)
    printf("\n\nTemporary false fact (%d) %s - will be reviewed later -", fct, print_ft_name_string(fct, temp_name));

  tmp = get_IntList();

  tmp->item = fct;
  tmp->next = review_list;
  review_list = tmp;

}





/**
 * valuta l'istante temporale per i predicati derivati (per ora non è usata)
 * 
 * Evaluate the time for a derived predicates (not used)
 **/
float set_time_for_derived_predicates(int fct, int level, float fct_time) {

  int i, j, dp;
  float t, time = MAXFLOAT;

  for (i = 0; i < gft_conn[fct].num_dp_PC; i++) {
    
    dp = gft_conn[fct].dp_PC[i];
    t = fct_time;

    for (j = 0; j < gdp_conn[dp].num_PC; j++) {
      t = MAX(t, CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level) -> time_f);
      if (t >= time)
	break;
    }
    
    time = MIN(t, time);
    
    CONVERT_FACT_TO_NODE(gdp_conn[dp].add, level) -> time_f = time;

  }
    
  return time;

}




/*********************************************************************************************************/


/** 
 * Nome: bw_derived_preconds_propagation
 * Scopo:  Propaga ricorsivamente w_is_goal per i predicati derivati
 *         evitando i cicli attraverso un bitarray tabu dei predicati già visitati
 * Tipo: void
 * Input: int derived_fct, int level, int *tabu
 * Output: nessuno
 * Strutture dati principali: vectlevel
 *                            FactNode
 *                           
 * Funzioni principali utilizzate: backward_precond_propagation
 * Chiamata da: update_derived_preds
 *              bw_derived_preconds_propagation
**
* Name: bw_derived_preconds_propagation
* Objective: Recursive backward propagation of w_is_goal for derived predicate, avoid cycles
* Type: void
* Input: int derived_fct, int level, int *tabu
* Output: nessuno
* Main Data Structures: vectlevel
*                        FactNode
*                           
* Main Functions Used: backward_precond_propagation
* Call gives: update_derived_preds
*             bw_derived_preconds_propagation
**/
void bw_derived_preconds_propagation(int derived_fct, int level, int *tabu) {

  int i, j, dp;
  int root = 0;

  if (num_try == INITIALIZE_STEP)
    return;

  if (derived_fct < 0)
    return;

  if (gft_conn[derived_fct].fact_type != IS_DERIVED)
    return;

  if (!tabu) {
    /**
       Questa è la prima chiamata alla funzione
       ** 
       This is the first call
    **/
    root = 1;
    tabu = (int *)calloc(gnum_ft_block, sizeof(int));
    memset(tabu, 0, gnum_ft_block * sizeof(int));
  }

  if (GET_BIT(tabu, derived_fct)) {
    if (root)
      free(tabu);
    return;
  }

  SET_BIT(tabu, derived_fct);

  /**
     Per tutti gli operatori derivati di cui il fatto derived_fct è un effetto
     **
     For all rules that have derived_fct as effect
  **/
  for (i = 0; i < gft_conn[derived_fct].num_dp_A; i++) {

    dp = gft_conn[derived_fct].dp_A[i];

    /**
       Se l'operatore derivato è applicato
       ** 
       If the rule is appliable
    **/
    if ((!gnum_dp_precs[dp]) 
	&& GET_BIT(vectlevel[level]->active_rules, dp)) {
 
      /**
	 Per tutte le sue precondizioni
	 **
	 For all its preconditions
      **/
      for (j = 0; j < gdp_conn[dp].num_PC; j++) {

	/**
	   Se la precondizione in esame è un fatto di base
	   **
	   If this precondition is a base fact
	**/
	if (gft_conn[gdp_conn[dp].PC[j]].fact_type == IS_BASE) {

	  /**
	     Setto w_is_goal per questo fatto nel livello corrente e aggiorno i bitarray
	     **
	     Set w_is_goal for this fact in the current level and update the bitarrays
	  **/
#ifdef __TEST_PD__
	  printf("\nw_is_goal propagation for : %s at level %d", 
		 print_ft_name_string(gdp_conn[dp].PC[j], temp_name), level);
#endif

	  CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level) -> w_is_goal++;
	  CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level) -> w_is_derived_goal++;
	  SET_BIT(vectlevel[level] -> prec_vect, gdp_conn[dp].PC[j]);	  
	  
	  if (CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level) -> w_is_true == 1)
	    SET_BIT(vectlevel[level] -> true_crit_vect, gdp_conn[dp].PC[j]);
	  else if (CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level) -> w_is_true <= 0) 
	    SET_BIT(vectlevel[level] -> false_crit_vect, gdp_conn[dp].PC[j]);	  
	  
	  /**
	     Propago all'indietro w_is_goal
	     **
	     Bacward propagation of w_is_goal
	  **/
	  backward_precond_propagation(CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level));
	}
	else {
	  /**
	     Se la precondizione è un fatto derivato chiamo ricorsivamente la propagazione
	     **
	     If the precondition si a derived predicate call recursively this function
	  **/
	  bw_derived_preconds_propagation(gdp_conn[dp].PC[j], level, tabu);
	}
      }
    }
  }

  if (root)
    free(tabu);
}







/** 
 * Nome: bw_derived_preconds_remotion
 * Scopo:   Rimuove ricorsivamente w_is_goal per il predicati derivati
 *          evitando i cicli attraverso il bitarray tabu dei predicati già visitati
 * Tipo: void
 * Input: int derived_fct, int level, int *tabu
 * Output: nessuno
 * Strutture dati principali: vectlevel
 *                            FactNode
 *                           
 * Funzioni principali utilizzate: backward_precond_remotion
 * Chiamata da: calc_new_derived_predicates
 *              bw_derived_preconds_remotion
**
* Name: bw_derived_preconds_remotion
* Objective: Backward w_is_goal remotion for derived predicates, avoid cycles
* Type: void
* Input: int derived_fct, int level, int *tabu
* Output: nessuno
* Main Data Structures: vectlevel
*                       FactNode
*                           
* Main Functions Used: backward_precond_remotion
* Call gives: calc_new_derived_predicates
*             bw_derived_preconds_remotion
**/
void bw_derived_preconds_remotion(int derived_fct, int level, int *tabu) {

  int i, j, dp;
  int root = 0;

  if (num_try == INITIALIZE_STEP)
    return;
  
  if (derived_fct<0)
    return;
  
  if (gft_conn[derived_fct].fact_type != IS_DERIVED)
    return;
  
  if (!tabu) {
    /**
       Questa è la prima chiamata alla funzione
       **
       This is the first call
    **/
    root = 1; 
    tabu = (int *)calloc(gnum_ft_block, sizeof(int));
    memset(tabu, 0, gnum_ft_block * sizeof(int));
  }

  if (GET_BIT(tabu, derived_fct)) {
    if (root)
      free(tabu);
    return;
  }

  SET_BIT(tabu, derived_fct);
  
  /**
     Per tutti gli operatori derivati di cui derived_fct è un effetto
     **
     Fall all rules that have derived_fct as an effect
  **/
  for (i = 0; i < gft_conn[derived_fct].num_dp_A; i++) {
    dp = gft_conn[derived_fct].dp_A[i];

    /**
       Se il bit corrispondente in prop_dp_index è settato,
       ovvero l'operatore derivato è stato rimosso ma faceva parte 
       di una catena di regole che supportava un predicato derivato goal
       **
       If the correspondent bit in prop_dp_index is setted,
       so the rule have been removed but war part of a derivation chain
       that supported a derived goal, then
    **/
    if (GET_BIT(prop_dp_index, dp)) {

      /**
	 Per tutte le sue precondizioni
	 **
	 For all its preconditions
      **/
      for (j = 0; j < gdp_conn[dp].num_PC; j++) {

	/**
	   Se la precondizione in esame è un fatto di base
	   **
	   If the precondition is a base fact
	**/
	if (gft_conn[gdp_conn[dp].PC[j]].fact_type == IS_BASE) {

#ifdef __TEST_PD__
	  printf("\nw_is_goal remotion for : %s at level %d", 
		 print_ft_name_string(gdp_conn[dp].PC[j], temp_name), level);
#endif

	  /**
	     Aggiorno w_is_goal e i bitarray al livello corrente
	     **
	     Update w_is_goal and the bitarrays in the current level
	  **/
	  if ((CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level) -> w_is_derived_goal > 0)
	      && (CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level) -> w_is_goal > 0)) {
	    CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level) -> w_is_goal--;
	    if (CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level) -> w_is_derived_goal > 0)
	      CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level) -> w_is_derived_goal--;
	    if (CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level) -> w_is_goal <= 0) {
	      RESET_BIT(vectlevel[level] -> prec_vect, gdp_conn[dp].PC[j]);
	      RESET_BIT(vectlevel[level] -> true_crit_vect, gdp_conn[dp].PC[j]);
	      RESET_BIT(vectlevel[level] -> false_crit_vect, gdp_conn[dp].PC[j]);
	    }
	  }

	  /**
	     Propago nei livelli precedenti
	     **
	     Backward propagation of w_is_goal remotion
	  **/
	  backward_precond_remotion(CONVERT_FACT_TO_NODE(gdp_conn[dp].PC[j], level), 1);
	}
	else {
	  /**
	     Resetto il bit per evitare cicli
	     **
	     Reset the rule bit in prop_dp_index to avoid cycles
	  **/
	  RESET_BIT(prop_dp_index, dp);

	  /**
	     Se il fatto in esame è derivato chiamo ricorsivamente la propagazione
	     **
	     If the precondition is a derived predicate call recursively this function
	  **/
	  bw_derived_preconds_remotion(gdp_conn[dp].PC[j], level, tabu);
	}
      }
    }
  } 

  if (root)
    free(tabu);
}








/**
 * Nome: update_derived_preds
 * Scopo: Aggiorna ricorsivamente il numero di precondizioni non soddisfatte 
 *        dei predicati derivati e il loro valore di verità dato il fatto fct 
 *        da aggiungere (add_del == ADD_FACT) o togliere (add_del == DEL_FACT)
 * Tipo: Bool
 * Input: int fct, int level, int add_del, int rule, 
 *        int *goal_idx, int *goal_level, int *tabu
 * Output: TRUE se è cambiato il valore di verità di qualche predicato
 * Strutture dati principali: gdp_conn
 *                            FactNode 
 *                           
 * Funzioni principali utilizzate: bw_derived_preconds_propagation
 *                                 insert_unsup_fact
 *                                 update_derived_preds
 * Chiamata da: calc_new_derived_predicates
**
* Name: update_derived_preds
* Objective:  Update recursively the number of unsatisfied preconditions of
*             derivation rules and the truth value of derived facts, given a 
*             new base fact to be added (add_del == ADD_FACT) or removed
*             (add_del == DEL_FACT)
* Type: Bool
* Input: int fct, int level, int add_del, int rule, 
*	 int *goal_idx, int *goal_level, int *tabu
* Output: TRUE if some derived predicates have been changed
* Main Data Structures: gdp_conn
*                       FactNode 
*                           
* Main Functions Used: bw_derived_preconds_propagation
*                      insert_unsup_fact
*                      update_derived_preds
* Call gives: calc_new_derived_predicates
**/
Bool update_derived_preds(int fct, int level, int add_del, int rule, 
			  int *goal_idx, int *goal_level, int *tabu) {
  int i;
  Bool res;

  res = FALSE;

  /**
     Non considero i fatti numerici
     **
     Skip numerical facts
  **/
  if (fct < 0) 
    return res;

#ifdef __TEST_PD__
  printf("\n UPDATING DERIVED PREDICATES FROM FACT %s (%s)", print_ft_name_string(fct, temp_name), (add_del==ADD_FACT)?"ADDED":"REMOVED");
  printf("\n LEVEL : %d", level);
#endif

  /**
     Se sto aggiungendo il fatto
     **
     If the new fact has to be added
  **/ 
  if (add_del == ADD_FACT) {
    
    if (gft_conn[fct].fact_type == IS_DERIVED)
      {
	if (level >= 0)
	  SET_BIT(vectlevel[level]->active_rules, rule);
	else if (!GET_BIT(facts, fct))
	  used_rules[fct] = rule;
      }

    if (GET_BIT(facts, fct) != 0) {
      
      if ((level >= 0) && (gft_conn[fct].fact_type == IS_DERIVED)) 
	CONVERT_FACT_TO_NODE(fct, level) -> w_is_derived_true++;

      return res;
    }

    if ((level >= 0) && (gft_conn[fct].fact_type == IS_DERIVED)) {
     
      if (CONVERT_FACT_TO_NODE(fct, level) -> w_is_goal) {

#ifdef __TEST_PD__
	printf("\nBackward propagation of w_is_goal for %s from level %d", print_ft_name_string(fct, temp_name), level);
#endif
        /**
	   Se ho raggiunto un goal propago all'indietro w_is_goal lungo il percorso di derivazione
	   NB: viene fatto solo per il primo percorso che permette di raggiungere il goal 
	   (perchè se il goal è già vero ritorno senza far nulla al controllo precedente)
	   ==> se ci sono più percorsi di derivazione che permettono di raggiungere il goal
	   solo uno avrà gli w_is_goal settati.
	  **
	  If a goal has been reached propagate w_is_goal in the derivation path.
	  This is made only for the first path that reach the goal, in fact if the
	  goal is already true this function skip it.
	**/
	bw_derived_preconds_propagation(fct, level, tabu);
      }
      
      /**
	 Sto rendendo vero il fatto per la prima volta ==> setto w_is_true
	 **
	 The fact becames true for the first time ==> set w_is_true
      **/
      CONVERT_FACT_TO_NODE(fct, level) -> w_is_true = 1;
      CONVERT_FACT_TO_NODE(fct, level) -> w_is_derived_true = 1;

      /**
	 Aggiorno i bitarray : il fatto non è più falso => nn è più in false_critic_vect
	 **
	 Update bitarrays: the fact is no more false => reset false_critic_vect
      **/
      RESET_BIT(vectlevel[level] ->false_crit_vect, fct);
      
      if ( CONVERT_FACT_TO_NODE(fct, level) -> w_is_goal > 0)
	SET_BIT(vectlevel[level]->true_crit_vect, fct);
      
      /**
	 Se il predicato derivato era nella lista delle inconsistenze lo rimuovo
	 **
	 If the derived predicate was an inconsistence remove it from inconsistence list
      **/
      if (vectlevel[level]->fact[fct].false_position >= 0)
        remove_false_fact(CONVERT_FACT_TO_NODE(fct, level));
      
      vectlevel[level]->num_fact++;
      res = TRUE;
    }

    /**
       Setto il bit corrispondente in facts per continuare la propagazione
       **
       Set the derived predicate as true in the bitarray "facts" and go on whith
       the propagation
    **/
    if (gft_conn[fct].fact_type == IS_DERIVED)
      SET_BIT(facts, fct);
    
    /**
       Decremento il numero di precondizioni nn soddisfatte per gli operatori derivati che 
       hanno questo fatto come precondizione
       **
       Decrease the number of unsatisfied preconditions for rules that
       have this fact in their preconditions
    **/
    for (i = 0; i < gft_conn[fct].num_dp_PC; i++) { 
      gnum_dp_precs[gft_conn[fct].dp_PC[i]]--;
      if (gnum_dp_precs[gft_conn[fct].dp_PC[i]] == 0)
	SET_BIT(changed_dp, gft_conn[fct].dp_PC[i]);
    }
    
    for (i = 0; i < gft_conn[fct].num_dp_PC; i++) {
      /**
	 Se dp diventa applicabile faccio forward dei suoi effetti
	 **
	 If the rule becames appliable propagate its effect
      **/
      if (GET_BIT(changed_dp, gft_conn[fct].dp_PC[i])) {

	res = TRUE;
	
	update_derived_preds(gdp_conn[gft_conn[fct].dp_PC[i]].del, level, DEL_FACT, 
			     gft_conn[fct].dp_PC[i], goal_idx, goal_level, tabu);

	update_derived_preds(gdp_conn[gft_conn[fct].dp_PC[i]].add, level, ADD_FACT, 
			     gft_conn[fct].dp_PC[i], goal_idx, goal_level, tabu);	
	
	RESET_BIT(changed_dp, gft_conn[fct].dp_PC[i]);
	
      }
    }
  }
  
  /**
     Se sto eliminando il fatto
     **
     If the fact has to be removed
  **/
  else {
    
    if (!GET_BIT(facts, fct)) {
      
      if ((level >= 0) && (gft_conn[fct].fact_type == IS_DERIVED)) {
	CONVERT_FACT_TO_NODE(fct, level) -> w_is_derived_true =
	  CONVERT_FACT_TO_NODE(fct, level) -> w_is_true = 0;
      	RESET_BIT(vectlevel[level]->active_rules, rule);
      }
      
      return res;
    }
       
    if ((level >=0) && (gft_conn[fct].fact_type == IS_DERIVED)) {      
     
      RESET_BIT(vectlevel[level]->active_rules, rule);
      CONVERT_FACT_TO_NODE(fct, level) -> w_is_derived_true--;
     
      //if (CONVERT_FACT_TO_NODE(fct, level) -> w_is_derived_true > 0) 
      insert_in_review_list(fct);
      
      CONVERT_FACT_TO_NODE(fct, level) -> w_is_derived_true = 0;
      CONVERT_FACT_TO_NODE(fct, level) -> w_is_true = 0;
            
      /**
	 Il fatto non è più vero => non è più in true_crit_vect
	 **
	 The fact becames false => remove it from true_crit_vect
      **/
      RESET_BIT(vectlevel[level] -> true_crit_vect, fct);    

      if (CONVERT_FACT_TO_NODE(fct, level) -> w_is_goal > 0)
	SET_BIT(vectlevel[level]->false_crit_vect, fct);
      
      vectlevel[level]->num_fact--;
      
      /**
	 Se sto rimuovendo un goal aggiorno indice e livello del goal
	 ==> alla fine della propagazione conterranno indice e livello del predicato
         derivato goal che sta più in alto nella catena di derivazione
	 **
	 If the fact to be removed is marked as a goal update goal number and level
	 ==> at the end of the propagation I want to have number and level of the
	 higher derived goal in the derivation path 
      **/
      if (CONVERT_FACT_TO_NODE(fct, level) -> w_is_used) {
	(*goal_idx) =  fct;
	(*goal_level) = level;  

	/**
	   Se il fatto era un goal o era precondizione di un'azione ora diventa un'inconsistenza
	   **
	   If the fact was a goal or an action's precondition it becames an inconsistence
	**/ 
	if (vectlevel[level]->fact[fct].false_position < 0)
	  insert_unsup_fact(CONVERT_FACT_TO_NODE(fct, level));
      }
      
      res = TRUE;
    }
    
    /**
       Aggiorno il bitarray facts per poter continuare la propagazione
       **
       Remove the fact from the bitarry and go on with the propagation
    **/
    if (gft_conn[fct].fact_type == IS_DERIVED)
      RESET_BIT(facts, fct);

    /**
       Incremento il numero di preconds non soddisfatte per gli operatori derivati 
       che hanno questo fatto nelle precondizioni
       **
       Increase the number of unsatisfied preconditions for rules that have this
       fact in their preconditions
    **/
    for (i = 0; i < gft_conn[fct].num_dp_PC; i++) { 
      gnum_dp_precs[gft_conn[fct].dp_PC[i]]++;
      if (gnum_dp_precs[gft_conn[fct].dp_PC[i]] == 1)
	SET_BIT(changed_dp, gft_conn[fct].dp_PC[i]);
    }
    
    for (i = 0; i < gft_conn[fct].num_dp_PC; i++) { 
      /**
	 Se dp nn è più applicabile
	 **
	 If the rule becames not appliable
      **/
      if (GET_BIT(changed_dp, gft_conn[fct].dp_PC[i])) {
	res = TRUE;
	/**
	   Setto il bit corrispondente in prop_dp_index
	   ==> se durante la propagazione mi imbatto in un goal dovrò rimuovere
	   w_is_goal dei fatti che sono preconds degli operatori derivati marcati
	   **
	   Set the correspondent bit in prop_dp_index
	   ==> id during the propagation I reach a goal to be removed, I need
	   to remove w_is_goal for facts that are preconditions of the marked
	   rules.
	**/
	SET_BIT(prop_dp_index, gft_conn[fct].dp_PC[i]);
	
	/**
	   Se rendo falso un predicato derivato che non era già falso,
	   utilizzando l'operatore derivato gdp_conn[...]
	   propago la rimozione dei suoi effetti
	   **
	   If a rule becames not appliable, propagate the remotion of 
	   its effects.
	**/
	update_derived_preds(gdp_conn[gft_conn[fct].dp_PC[i]].add, level, DEL_FACT, 
			     gft_conn[fct].dp_PC[i], goal_idx, goal_level, tabu);
	update_derived_preds(gdp_conn[gft_conn[fct].dp_PC[i]].del, level, ADD_FACT, 
			     gft_conn[fct].dp_PC[i], goal_idx, goal_level, tabu);
	
	RESET_BIT(changed_dp, gft_conn[fct].dp_PC[i]);

      }
    }
  }
  
  return res;
}









/**
 * Nome:  calc_new_derived_predicates
 * Scopo: Dato il fatto fct che viene reso vero/falso al livello level
 *        calcola tutti i fatti da aggiungere/togliere in seguito
 *        all'applicazione dei predicati derivati.
 * Tipo: int
 * Input: int fct, int level, int add_del
 * Output: - il numero di predicati derivati il cui valore di verità è cambiato (lunghezza del vettore result)
 *         - un vettore (result) dei predicati derivati che sono diventati
 *           1. veri se k >= 0
 *           2. falsi se k < 0 (in questo caso l'indice del fatto è -k-1)                       
 * Funzioni principali utilizzate: update_derived_preds
 * Chiamata da: calc_new_derived_predicates_from
 *              initialize
 *              insert_action_in_vectlevel
 *              remove_action_from_vectlevel
 *              forward_noop_propagation
 *              forward_noop_remotion
 *              compute_relaxed_fact_cost
 *              dg_action_cost
 *              cri_activate_distgraph_ef
 *              cri_heuristic_for_action
**
* Name: calc_new_derived_predicates 
* Objective: Given a fact F to set true/false at a certain level
*            compute the truth value of facts that can be derived
*            from some derivation rules, starting from F. 
* Type: int 
* Input: int fct, int level, int add_del
* Output: - The number of derived facts whose truth value is changed
*         - A vector (result) of indexes of these facts. Indexes in "result" are:
*	   1. k >= 0 if the fact is now true
*	   2. k < 0 if the fact is now false (the index of the fact has to be evaluated as -k-1)
* Main Functions Used: update_derived_preds
* Call gives: calc_new_derived_predicates_from
*             initialize
*             insert_action_in_vectlevel
*             remove_action_from_vectlevel
*             forward_noop_propagation
*             forward_noop_remotion
*             compute_relaxed_fact_cost
*             dg_action_cost
*             cri_activate_distgraph_ef
*             cri_heuristic_for_action
**/
int calc_new_derived_predicates(int fct, int level, int add_del, int **result) {
  int i, max, num, fact;
  int *tmp = NULL;
  int goal_idx = -1, goal_level = -1;
  int *tabu = NULL;
  int num_rules;
  IntList *aux = NULL, *last = NULL;
  Bool changed;
  Bool fixed;
  
  if (!GpG.derived_predicates)
    return 0;

  if (fct < 0)
    return 0;

  reset_prop_index();

#ifdef __TEST_PD__

  printf("\n********** %s **********\n", (add_del == ADD_FACT)?"ADD":"DEL");
  print_ft_name(fct);
  printf("\n*************************\n");

#endif

  max = MAX_NEW_DERIVED;
  
  num = 0;

  if (level >= 0) {
 
    if (!GpG.derived_pred_in_preconds && (level < GpG.curr_plan_length))
      return 0;

    facts = vectlevel[level] -> fact_vect;
    gnum_dp_precs = vectlevel[level] -> gnum_dp_precs;
  }

  if ((add_del == ADD_FACT) == (GET_BIT(facts, fct) != 0))
    return 0;

  /**
     Faccio una copia temporanea dello stato dei fatti di questo livello
     **
     Make a temporary copy of the state of this level
  **/
  if (result) {
    tmp = (int *) calloc (gnum_ft_block, sizeof(int));
    memcpy(tmp, facts, gnum_ft_block * sizeof(int));
  }

  if (!changed_dp)
    changed_dp = alloc_vect(gnum_dp_block);
  
  reset_bitarray(changed_dp, gnum_dp_block);

  changed = update_derived_preds(fct, level, add_del, -1, &goal_idx, &goal_level, tabu);
  
  /**
     Rivisito i fatti temporaneamente falsi (inseriti in review) perchè
     potrebbero essere resi veri da altre regole non considerate durante 
     la rimozione
     **
     Review the facts that have been inserted in the review list (temporary 
     false facts). They shoul be supported by some rules.
  **/
  if (review_list) {
    fixed = FALSE;
    while (!fixed) {
      fixed = TRUE;
      for (aux = review_list; aux; aux = aux->next) {
	
	if (!aux->next)
	  last = aux;
	
        fact = aux->item;
	
	if (DEBUG5)
	  printf("\n\nReview fact (%d): %s ", fact, print_ft_name_string(fact, temp_name));
	
	num_rules = 0;
        for (i = 0; i < gft_conn[fact].num_dp_A; i++)
	  num_rules += (!gnum_dp_precs[gft_conn[fact].dp_A[i]]);
	
	if (num_rules)
	  for (i = 0; i < gft_conn[fact].num_dp_A; i++) {

	    /**
	       Se esiste una regola che supporta ancora questo fatto, allora
	       non doveva essere rimosso. Lo rendo vero e lo propago.
	       **
	       If does exist a rule that support this fact it can not be 
	       false: change its truth value in TRUE and propagate it.
	     **/

	    if ((!gnum_dp_precs[gft_conn[fact].dp_A[i]]) && (!GET_BIT(facts, fact))) {
	      changed = update_derived_preds(fact, level, ADD_FACT, gft_conn[fact].dp_A[i], 
					     &goal_idx, &goal_level, tabu) || changed;
	      if (level >= 0)
		CONVERT_FACT_TO_NODE(fact, level) -> w_is_derived_true = num_rules;
	  
	      if (DEBUG5)
		printf("\nFIXED %d", GET_BIT(facts, fact));
	      
	      fixed = FALSE;
	      break;
	    }
	  }
      }	
    }
   
    last->next = old_list;
    old_list = review_list;
    review_list = NULL;
  }
  
  /**
     Se è cambiato il valore di verità di qualche fatto costruisco l'output
     **
     If something is changed and output is needed build the output vector
  **/
  if (changed && result) {
    
      (*result) = (int *)calloc(max, sizeof(int));
      memset((*result), 0, max * sizeof(int)); 
      
      for (i = 0; i < gnum_ft_conn; i++) {
	if ((GET_BIT(tmp, i) != 0) != (GET_BIT(facts, i) != 0)) {
	  if (GET_BIT(facts, i) != 0)
	    (*result)[num++] = i;
	  else
	    (*result)[num++] = -i - 1;
	}
	
	if (num >= max) {
	  max += MAX_NEW_DERIVED;
	  (*result) = (int *)realloc((*result), max * sizeof(int));
	}
	
      }

  } 


#ifdef __TEST_PD__
  if (result && (*result) && num) {
    printf("\n**** PREDICATI DERIVATI ****\n");
    for (i = 0; i < num; i++)
      if ((*result)[i] >= 0) {
	printf("\nADD : ");
	print_ft_name((*result)[i]);
      }
      else {
	printf("\nDEL :");
	print_ft_name(-(*result)[i]-1);
      }
    printf("\n************ END ***********\n");
  }
#endif

  if (goal_idx >= 0) {

#ifdef __TEST_PD__
    printf("\nBackward remotion of w_is_goal for %s from level %d", print_ft_name_string(goal_idx, temp_name), goal_level);
#endif
    
    if (level >= 0)
      bw_derived_preconds_remotion(goal_idx, goal_level, tabu);
  }
  
  if (result)
    free(tmp);

  if (tabu)
    free(tabu);

  return num;
}






/**
 * Nome:  calc_all_derived_predicates
 * Scopo: Calcola tutti i predicati derivati a partire da un vettore di preconds nn soddisfatte
 *        e da un bitarray dei fatti già veri. Se level >= 0 questi vettori vangono presi dal vectlevel.
 *        Ritorna il numero di predicati derivati per cui è cambiato il valore di verità e il
 *        vettore degli indici di questi predicati (result). (>= 0 se resi veri, < 0 se resi falsi)
 * Tipo: int
 * Input: int level, int reset
 * Output: - il numero di predicati derivati il cui valore di verità è cambiato (lunghezza del vettore result)
 *         - un vettore (result) dei predicati derivati che sono diventati
 *           1. veri se k >= 0
 *           2. falsi se k < 0 (in questo caso l'indice del fatto è -k-1)  
 * Strutture Dati Principali: gdp_conn       
 * Chiamata da: calc_all_derived_predicates_from
 *              calc_mutex
 *              check_plan 
 *
**
* Name: calc_all_derived_predicates
* Objective:  Compute the truth value of all the derived predicate beginning from a vector of
*             unsatistfied preconditions and a fact bitarray. If level is >= 0 then this values are in
*             the vectlevel. Return the number of changed derived predicates and their indexes
*             (indexes are >= 0 for predicates that became true, < 0 for predicates that became false)
* Type: int 
* Input:  int level, int reset
* Output:  - The number of derived facts whose truth value is changed
*          - A vector (result) of indexes of these facts. Indexes in "result" are:
*	    1. k >= 0 if the fact is now true
*	    2. k < 0 if the fact is now false (the index of the fact has to be evaluated as -k-1)
* Main Data Structures: gdp_conn    
* Call gives:  calc_all_derived_predicates_from
*              calc_mutex
*              check_plan 
*
**/
int calc_all_derived_predicates(int level, int reset, int **result) {
  int i, j, k, count, max,  num;
  Bool fixpoint;
  
  if (!GpG.derived_predicates)
    return 0;

  reset_prop_index();

  max = MAX_NEW_DERIVED;
  
  (*result) = (int *)calloc(max, sizeof(int));
  memset((*result), 0 , max * sizeof(int));

  if (level >= 0) {

    if (!GpG.derived_pred_in_preconds && (level < GpG.curr_plan_length))
      return 0;

    facts = vectlevel[level] -> fact_vect;
    gnum_dp_precs = vectlevel[level] -> gnum_dp_precs;
  }
  
  if (reset == RESET_ON) {
  
    /**
       Setto come falsi i predicati derivati
       **
       Reset derived predicates truth values
    **/
    for (i = 0; i < gnum_ft_conn; i++) {
      if (gft_conn[i].fact_type == IS_DERIVED)
	RESET_BIT(facts, i);
    }
    
    /**
       Inizializzo il vettore delle precondizioni nn soddisfatte
       **
       Initialize unsatisfied preconditions vector
    **/
    initialize_dp_num_prec_vector(&gnum_dp_precs);
  }

  /**
     Inizializzo una tabella dei predicati derivati già visitati
     **
     Init table for visited predicates
  **/
  init_table();

  num = 0;
  
  /**
     Calcolo il fixpoint
     **
     Compute a fixpoint
  **/
  fixpoint = FALSE;
  
  while (!fixpoint) {  
	  
    fixpoint = TRUE;
    
    for (i = 0; i < gnum_dp_conn; i++) {
      count = gdp_conn[i].num_PC;
     
      for (j = 0; j < gdp_conn[i].num_PC; j++) {
	if (GET_BIT(facts, gdp_conn[i].PC[j])) 
	  count--;
      }
      gnum_dp_precs[i] = count;

      /**
	 Se il predicato diventa vero (ha le precondizioni soddisfatte e nn era già vero)
	 **
	 If this predicate becames true
      **/
      if (!count && !GET_BIT(facts, gdp_conn[i].add)) {
	SET_BIT(facts, gdp_conn[i].add);

#ifdef __TEST_PD__
	printf("\n[%d]-add TRUE DERIVED PREDICATE %s", i, print_ft_name_string( gdp_conn[i].add, temp_name));
#endif

	/**
	   Se in precedenza avevo reso falso il predicato lo elimino.
	   Vuol dire che inizialmente era vero, l'ho tolto e adesso lo sto 
	   nuovamente aggiungendo ==> torno al punto di partenza 
	   **
	   If the fact was previously marked as false, remove it frome
	   the output (it means that the fact was true, I changed
	   it in FALSE and now I found it has to be true again)
	**/
	if ((table[gdp_conn[i].add] >= 0) 
	    && ((*result)[table[gdp_conn[i].add]] < 0)) {
	  
	  /**
	     Aggiorno la tabella: nella posizione relativa all'ultimo
	     fatto aggiunto metto l'indice che era associato al fatto 
	     che sto togliendo
	     **
	     Update the table: put the index of the fact I am removing
	     in the position of the last fact added
	  **/
	  table[(*result)[num - 1]] = table[gdp_conn[i].add];
	  

	  /**
	     Aggiorno i risultati: nella posizione del fatto da togliere
	     metto il fatto che è in fondo alla lista
	     **
	     Update the result vector: put the last fact in the vector
	     in the position of the fact to be removed 
	  **/
	  (*result)[table[gdp_conn[i].add]] = (*result)[--num];

	  /**
	    NB. Adesso table[indice dell'ultimo fatto aggiunto] è = alla
	    posizione di questo fatto nel vettore result (quella che prima 
	    era occupata dal fatto che ho eliminato)
	    **	
	    Now the value of table[index of last fact added] is the right
	    position of this fact in the result vector (the same that was
	    previously occupied by the fact removed)
	  **/

	  /**
	     Invalido il contenuto della tabella nella posizione
	     del fatto eliminato
	     **
	     Reset the value of the table in the position of the
	     fact removed
	  **/
	  table[gdp_conn[i].add] = -1;
	}
	/**
	   Se invece è la prima volta che lo visito lo aggiungo alla lista 
	   **
	   If this is the first time I see this fact, add it to the result
	   vector and update the table
	**/
	else {
	  (*result)[num++] = gdp_conn[i].add;
	  table[gdp_conn[i].add] = num - 1;
	}
	
	/**
	   Stesso procedimento per l'effetto cancellante
	   **
	   Do the same for the deleting effect
	**/
	if ((gdp_conn[i].del >= 0) && (GET_BIT(facts, gdp_conn[i].del))) {
	  RESET_BIT(facts, gdp_conn[i].del);

#ifdef __TEST_PD__	  
	  printf("\n[%d]-del FALSE DERIVED PREDICATE %s", i, print_ft_name_string( gdp_conn[i].del, temp_name));
#endif
	  
	  if ((table[gdp_conn[i].del] >= 0) 
	      && ((*result)[table[gdp_conn[i].del]] >= 0)) {
	    
	    /**
	       Aggiorno tabella e risultati come prima
	       **
	       Update table and results
	    **/
	    table[(*result)[num - 1]] = table[gdp_conn[i].del];
	    (*result)[table[gdp_conn[i].del]] = (*result)[--num];
	    table[gdp_conn[i].del] = -1;
	  }
	  else {
	    (*result)[num++] = -gdp_conn[i].del - 1;
	    table[gdp_conn[i].del] = num - 1;
	  }
	}
	
	fixpoint = FALSE;
      }

      /**
	 Se il predicato ha delle preconds nn soddisfatte e nn è falso
	 **
	 If the predicate has some unsatisfied preconditions and it is not false
      **/
      else if (count && GET_BIT(facts, gdp_conn[i].add)) {
	for (k = 0; (k < gft_conn[gdp_conn[i].add].num_dp_A)
	       && (gnum_dp_precs[gft_conn[gdp_conn[i].add].dp_A[k]]); k++);

	/**
	   Se nessun operatore di derivazione è in grado di renderlo vero, allora lo cancello
	   **
	   If there's no rules that can support this fact I remove it
	**/
	if (k == gft_conn[gdp_conn[i].add].num_dp_A) {
	  RESET_BIT(facts, gdp_conn[i].add);

#ifdef __TEST_PD__
	  printf("\n[%d]-add FALSE DERIVED PREDICATE %s", i, print_ft_name_string( gdp_conn[i].add, temp_name));
#endif
	
	  if ((table[gdp_conn[i].add] >= 0) 
	      && ((*result)[table[gdp_conn[i].add]] >= 0)) {
	  
	    /**
	       Aggiorno tabella e risultati  
	       **
	       Update table and results
	    **/
	    table[(*result)[num - 1]] = table[gdp_conn[i].add];
	    (*result)[table[gdp_conn[i].add]] = (*result)[--num];
	    table[gdp_conn[i].add] = -1;
	  }
	  else {
	    (*result)[num++] = -gdp_conn[i].add - 1;
	    table[gdp_conn[i].add] = num - 1;
	  }

	  if ((gdp_conn[i].del >= 0) && (!GET_BIT(facts, gdp_conn[i].del))) {
	    SET_BIT(facts, gdp_conn[i].del);

#ifdef __TEST_PD__
	    printf("\n[%d]-del TRUE DERIVED PREDICATE %s", i, print_ft_name_string( gdp_conn[i].del, temp_name));
#endif

	    if ((table[gdp_conn[i].del] >= 0) 
		&& ((*result)[table[gdp_conn[i].del]] < 0)) {
	      table[(*result)[num - 1]] = table[gdp_conn[i].del];
	      (*result)[table[gdp_conn[i].del]] = (*result)[--num];
	      table[gdp_conn[i].del] = -1;
	    }
	    else {
	      (*result)[num++] = gdp_conn[i].del;
	      table[gdp_conn[i].del] = num - 1;
	    }
	  }
	  
	  fixpoint = FALSE;
	}
	
      }
      
      /**
	 Rialloco il vettore dei risultati se ho superato la dimensione massima
	 **
	 Realloc the results vector if it exceed the max length
      **/
      if (num >= max) {
	max += MAX_NEW_DERIVED;
	(*result) = (int *)realloc((*result), max * sizeof(int));
      }
      
    }
    
  }

#ifdef __TEST_PD__
  if (result && (*result) && num) {
    printf("\n**** PREDICATI DERIVATI ****\n");
    for (i = 0; i < num; i++)
      if ((*result)[i] >= 0) {
	printf("\nADD : ");
	print_ft_name((*result)[i]);
      }
      else {
	printf("\nDEL :");
	print_ft_name(-(*result)[i]-1);
      }
    printf("\n************ END ***********\n");
  }
#endif

  return num;
  
}






/**
 * Nome: calc_new_derived_predicates_from
 * Scopo: Calcola i nuovi predicati derivati a partire da un fatto (fct)
 *        da aggiungere/togliere, dal numero di precondizioni
 *        nn soddisfatte per ogni predicato derivato (my_precs) e
 *        da un bitvector di fatti da considerare veri in partenza (my_facts) 
 * Funzioni principale utilizzate: calc_new_derived_predicates
**
* Name: calc_new_derived_predicates_from
* Objective: Compute the truth value of derived predicates
*            starting ftom a fact (fct) to be added/removed, the number of
*            unsatisfied precondition for each rule (my_precs) and the bit
*            vector of true facts (my_facts)
* Main Functions Used: calc_new_derived_predicates
**/
int calc_new_derived_predicates_from(int fct, int *my_precs, int *my_facts, int add_del, int **result) {
 
  if (!GpG.derived_predicates)
    return 0;

  gnum_dp_precs = my_precs;
  facts = my_facts;
  
  if (!used_rules)
    used_rules = alloc_vect(gnum_ft_conn);

  return calc_new_derived_predicates(fct, -1, add_del, result);

}




/**
 * Nome: calc_all_derived_predicates_from
 * Scopo: Calcola tutti i nuovi predicati derivati a partire dal numero di precondizioni
 *        nn soddisfatte per ogni predicato derivato (my_precs) e
 *        da un bitvector di fatti da considerare veri in partenza (my_facts) 
 * Funzioni principali utilizzate: calc_all_derived_predicates
**
* Name: calc_all_derived_predicates_from
* Objective: Compute the truth value of derived predicates starting ftom the number of
*            unsatisfied precondition for each rule (my_precs) and the bit
*            vector of true facts (my_facts)
* Main Functions Used: calc_all_derived_predicates
**/
int calc_all_derived_predicates_from(int *my_precs, int *my_facts, int reset, int **result) {
   
  int *tmp = NULL;
  int res;

  if (!GpG.derived_predicates)
    return 0;

  gnum_dp_precs = my_precs;
  facts = my_facts;

  res = calc_all_derived_predicates(-1, reset, &tmp);

  if (result)
    (*result) = tmp;
  else if (tmp) free(tmp);
  
  return res;

}






/**
 * Alloca (se serve) e inizializza il vettore del numero di preconds
 * nn soddisfatte per i predicati derivati
**
* Initialize a vector of the number of unsatisfied preconditions
* for each derivation rule
**/
void initialize_dp_num_prec_vector(int **precs) {
  int i;

  if (!GpG.derived_predicates)
    return;

  if (!(*precs)) {
    (*precs) = (int *)calloc(gnum_dp_conn, sizeof(int));
    assert(*precs);
  }
  
  /**
     Inizializzo il numero di preconds nn soddisfatte x ogni operatore derivato
     **
     Initialize the number of preconditions for each rule
  **/
  for (i = 0; i < gnum_dp_conn; i++) 
    (*precs)[i] = gdp_conn[i].num_PC;
}






/**
 * Resetta la matrice usata per memorizzare le precondizioni
 * necessarie a supportare un predicato derivato
**
* Reset the matrix used to save the sets of facts needed
* to support a derived predicate
**/
void reset_gdp_path(path_set *path) {
  
  /**
     Se non è ancora stato fatto alloco le matrici gdp_path e trash
     **
     Allocate the matrix and the trash
  **/
  if (!path->tuple_set)
    path->tuple_set = (indexed_vect_list **)calloc(gnum_ft_conn + 1, sizeof(indexed_vect_list *));
  else
    trash_tuple_lists(path);
  
  if (!trash)
    trash = (indexed_vect_list **)calloc(gnum_ft_conn + 1, sizeof(indexed_vect_list *));   

  /**
     Resetto path
     **
     Reset the matrix
  **/
  memset(path->tuple_set, 0, (gnum_ft_conn + 1) * sizeof(indexed_vect_list *));
  path->size = 0;

}

void free_gdp_path(path_set *l) {
  
  int i;
  indexed_vect_list *tmp, *next;

  for (i = 0; i < (gnum_ft_conn + 1); i++) {
    tmp = l->tuple_set[i];
    while (tmp) {
      next = tmp -> next;
      free(tmp -> item);
      free(tmp);
      tmp = next;
    }
  }

  free(l);
  
}







/**
 * Salva le precondizioni trovate lungo un percorso di derivazione
 * nella struttura path
**
* Save the set of facts found in a derivation path in
* the matrix path
**/
void save_list(int n, int depth, path_set *path) {
  
  indexed_vect_list *aux;

  /**
     Se non ho un elemento utilizzabile in trash ne alloco uno
     **
     Create a new fact set or get it from the trash
  **/
  if (!trash[n]) {
    aux =  (indexed_vect_list *)malloc(sizeof(indexed_vect_list));
    aux -> item = (int *)calloc(n, sizeof(int));
  }
  else {
    aux = trash[n];
    trash[n] = aux -> next; 
  }

  /**
     Salvo la tupla: in op metto la profondità della tupla
     (la profondità nel rule graph del fatto più profondo della tupla)
     **
     Save the fact set: put in "op" the depth of the set
     (the depth in the rule graph of the deeper fact of this set)
  **/
  aux -> op = depth;
  memcpy(aux -> item, temp_pc_vect, n * sizeof(int));
  aux -> next =  path->tuple_set[n];
  path->tuple_set[n] = aux;
  
  reorder_fact_vect(aux->item, n);
  
  if (n > path->size)
    path->size = n;
}




/** 
 * Nome: search_for_base_preconds
 * Scopo:  Cerco le tuple di precondizioni di base necessarie a supportarer un predicato derivato
 * Tipo: int
 * Input: int dp_fct, int index, int *tabu, int level, IntList *append, int call
 * Output: Numero di fatti della più lunga tupla trovata
 *         path_set *path = matrice delle tuple trovate in cui in ogni riga i sono
 *                          memorizzate le tuple di lunghezza i.
 * Strutture dati principali: gdp_conn
 *                            gft_conn
 * Funzioni principali utilizzate: search_for_base_preconds
 * Chiamata da: create_gdp_path_for
**
* Name: search_for_base_preconds
* Objective: Search the sets of facts needed to support a derived predicate
* Type: int
* Input: int dp_fct, int index, int *tabu, int level, IntList *append, int call
* Output: Number of facts in the longest set found
*         path_set *path = matrix of the found sets: in each line i there are sets
*                          that contain i facts.
* Main Data Structures: gdp_conn
*                       gft_conn                         
* Main Functions Used: search_for_base_preconds
* Call gives: create_gdp_path_for
**/
int  search_for_base_preconds(int dp_fct, int index, int *tabu, int level, IntList *append, path_set *path, int call) {

  int i, j, k, dp, pc, end = 1;
  int tmp_idx = index;
  IntList *tmp, *add = NULL, *additional = NULL;
 
  if (gft_conn[dp_fct].fact_type != IS_DERIVED)
    return 0;

  /**
     Prima chiamata: il parametro call deve valere 0
     **
     First call: call has to be 0
  **/
  if (!call) {
    tabu = (int *)calloc(gnum_ft_block, sizeof(int));
    memset(tabu, 0, gnum_ft_block * sizeof(int));
    gnum_dp_precs = vectlevel[level] -> gnum_dp_precs;
    facts = vectlevel[level] -> fact_vect;
    path->size = 0;
  }
  
  /**
     controllo per evitare cicli
     **
     This check is needed to avoid cycles
  **/
  if (GET_BIT(tabu, dp_fct)) 
    return 0;
  
  if (DEBUG4)
    printf("\n         SET_BIT %d", dp_fct);
  /**
     Setto il il bit corrispondente al fatto in esame
     nel bitarray tabu, in modo da non riconsiderarlo
     durante le chiamate ricorsive (entrerei in ciclo)
     **
     Set the bit of the current fact in the tabu bitarray
     to avoid cycles in recursive calls
  **/
  SET_BIT(tabu, dp_fct);

  if (DEBUG4)
    printf("\nSearching preconds for %s", print_ft_name_string(dp_fct, temp_name));

  for (i = 0; i < gft_conn[dp_fct].num_dp_A; i++) {
    dp = gft_conn[dp_fct].dp_A[i];

    additional = append;

    /** Check **/
#ifdef __DP_TYPE_CHECK__
    if (!check_dp_preconds(dp))
      continue;
#endif
    /***********/

    end = 1;
    /**
       Salvo l'indice per poter riprendere da qui
       al ritorno delle chiamate ricorsive
    **/
    tmp_idx = index;

    for (j = 0; j < gdp_conn[dp].num_PC; j++) {

      pc = gdp_conn[dp].PC[j];

      if (DEBUG4)
	printf("\nAnalize prec : %s", print_ft_name_string(pc, temp_name));
      /**
	Se questa precondizione è già supportata non la considero
	**
	If this precondition is already supported skip it
      **/
      if (GET_BIT(facts, pc))
	continue;
      
      if (gft_conn[pc].fact_type == IS_BASE) {
	
	/**
	   Memorizzo temporaneamente la precondizione
	   **
	   Save temporary the precondition
	**/
	for (k = 0; (k < index) && (temp_pc_vect[k] != pc); k++);
	if (k < index)
	  continue;

	temp_pc_vect[index++] = pc;
	
	if (DEBUG4)
	  printf("\n --- Prec found : %s", print_ft_name_string(pc, temp_name));
	
      }
      else {
	
	if (DEBUG4)
	  printf("\n ------X Recursive... ");
	
	for (k = j + 1; k < gdp_conn[dp].num_PC; k++) {
	  
	  for (tmp = additional; (tmp) && (tmp->item != gdp_conn[dp].PC[k]); tmp = tmp->next);
	  if (tmp) 
	    continue;
	  
	  if (GET_BIT(facts, gdp_conn[dp].PC[k]) || GET_BIT(tabu, gdp_conn[dp].PC[k]))
	    continue;
	  
	  aux_list = get_IntList();
		  
	  aux_list->item = gdp_conn[dp].PC[k];
	  aux_list->next = additional;
	  additional = aux_list;
	  
	}

	add = additional;

	/**
	   Se la precondizione è a sua volta derivabile
	   scendo ricorsivamente
	   **
	   If the precondition is a derived fact, call this
	   function recursively
	**/
	
	search_for_base_preconds(pc, index, tabu, level, additional, path, call+1);
	additional = NULL;
	end = 0;
	break;
      }
    } 

    /**
       Controllo le precondizioni addizionali, passate come parametro 
       durante le ricorsioni
       **
       Check the additional preconditions, passed as a parameter during
       the recursion
    **/
    while (additional) { 
      
      pc = additional->item;
   
      additional = additional->next;
      
      if (DEBUG4)
	printf("\nAnalize prec : %s", print_ft_name_string(pc, temp_name));
      /**
	 Se questa precondizione è già supportata non la considero
	 **
	 Skip the precondition if it is already supported
      **/
      if (GET_BIT(facts, pc))
	continue;
            
      if (gft_conn[pc].fact_type == IS_BASE) {
	
	/**
	   Memorizzo temporaneamente la precondizione
	   **
	   Temporary save the precondition
	**/
	for (k = 0; (k < index) && (temp_pc_vect[k] != pc); k++);
	if (k < index)
	  continue;
	
	temp_pc_vect[index++] = pc;
	
	if (DEBUG4)
	  printf("\n --- Prec found : %s", print_ft_name_string(pc, temp_name));
	
      }
      else {
	
	if (DEBUG4)
	  printf("\n ------X Recursive... ");
	
	/**
	   Se la precondizione è a sua volta derivabile
	   scendo ricorsivamente
	   **
	   If the precondition is a derived fact, call this
	   function recursively
	**/
	search_for_base_preconds(pc, index, tabu, level, additional, path, call+1);
	additional = NULL;
	end = 0;
	break;
      }
    }
  
    
    /**
       Se sono arrivato alla fine di un percorso salvo la lista
       di precondizioni che ho incontrato e il primo operatore applicabile
       **
       If there are no more preconditions to check save the list of
       the basic facts found 
    **/
    if (end) { 
      save_list(index, call, path);
    }
    
    index = tmp_idx;
    
    if (add) {
      for (aux_list=add; aux_list && (aux_list->next != append); aux_list = aux_list->next);
      if (aux_list) {
	aux_list->next = old_list;
	old_list = add;
	add = NULL;
      }
    }
    
  }
  
  if (DEBUG4)
    printf("\n         RESET_BIT %d", dp_fct);

  /**
     Resetto il bit del fatto considerato nel bitarray tabu
     in modo da poterlo riconsiderare su altri percorsi
     **
     Reset the bit of the current fact, because I want to
     examine it in different paths
  **/
  RESET_BIT(tabu, dp_fct);
  
  if (!call) 
    free(tabu);
  
  return path->size;
}













/**
 * Cerco le azioni in grado di supportare tutti i fatti nella lista bfct
 * e le metto in acts
 **/
void search_for_act_to_supp(int *precs, int num_pc, action_set *acts, int level) {
  
  int k, i, fct, act = -1;

  acts -> num_A = 0;

  // Se la lista dei fatti da supportare è vuota
  // significa che sto esaminando un operatore di derivazione
  // che non sarà utilizzabile (ad esempio se sono entrato in ciclo cercando le precond di base)
  if (DEBUG4)
    printf("\n num precs : %d", num_pc);

  for (k = 0; k < num_pc; k++) {
    fct = precs[k];

    if (DEBUG4)
      printf("\nFact to support : %s", print_ft_name_string(fct, temp_name));

    // Per ogni azione in grado di supportare fct
    for (i = 0; i < gft_conn[fct].num_A; i++) {
      // Scarto le azioni non applicabili al livello level
      if (!CHECK_ACTION_POS(gft_conn[fct].A[i], level))
	continue;
      act = gft_conn[fct].A[i];
      
      if (DEBUG4)
	printf("\naction : %s", print_op_name_string(act, temp_name));
    }

    if (act >= 0) 
      acts->A[acts->num_A++] = act;
  }
}






indexed_vect_list *choose_random_facts_set(path_set *path, int *num_facts) 
{

  int i;
  indexed_vect_list *tmp = NULL, *idx = NULL;

  for (i = 0; i <= path->size; i++)
    {
      for (tmp = path->tuple_set[i]; tmp; tmp = tmp->next)
	{

	  if (!idx && tmp)
	    idx = tmp;

	  if ((tmp->op >=0) && (MY_RANDOM & 1))
	    {
	      (*num_facts) = i;
	      idx = tmp;
	    }
	}
    }
  
  return idx;
  
}











/** 
 * Nome: choose_best_facts_set
 * Scopo:  Sceglie l'insieme di precondizioni più facile per supportare un predicato derivato
 * Tipo: indexed_vect_list*
 * Input: path_set *path, int *num_pc, int level, int to_level, float *best_cost, int *max_depth
 * Output: La miglior tupla per supportare un predicato derivato, tra quelle memorizzate in path
 * Strutture dati principali: path_set
 * Funzioni principali utilizzate: compute_relaxed_fact_cost
 *                                 test_preconds_propagation
 * Chiamata da: choose_best_tuple_and_level
**
* Name: choose_best_facts_set
* Objective: Choose the easiest set of facts to support a derived predicate 
* Type: indexed_vect_list*
* Input: path_set *path, int *num_pc, int level, int to_level, float *best_cost, int *max_depth
* Output: The best tuple in "path" for supporting a derived predicate
* Main Data Structures: path_set               
* Main Functions Used: compute_relaxed_fact_cost
*                      test_preconds_propagation
* Call gives: choose_best_tuple_and_level
**/
indexed_vect_list *choose_best_facts_set(path_set *path, int *num_pc, int level, int to_level, float *best_cost, int *max_depth) {

  int i, j, penalize;
  float temp_cost;
  indexed_vect_list *tmp = NULL, *idx = NULL;
  node_cost loc_n_cost;
  int depth;
  
  penalize=GpG.penalize_inconsistence_in_relaxed_plan;
  GpG.penalize_inconsistence_in_relaxed_plan=FALSE;
  
  if (DEBUG3)
    printf("\n\nTUPLE Search best tuple (level %d)", level);

  local_search.max_act_incons = MAXFLOAT;
  local_search.max_act_cost = 0.0;
  local_search.max_act_time = 0.0;

  for (i = 1; i <= path->size; i++) {

    for (tmp = path->tuple_set[i]; tmp; tmp = tmp -> next) {

      if (tmp -> op < 0)
	continue;

      if ((level < to_level)
	  && (!test_preconds_propagation(level, to_level, tmp->item, i))) {
	tmp -> op = -1;
	continue;
      }

      /**
	 Azzero ed imposto variabili per compute_relaxed_fact_cost 
	 **
	 Reset euristic info used in compute_relaxed_fact_cost
      **/
      
      Hvar.cost_actions_define_cost = 0.0;
      Hvar.time_actions_define_cost = 0.0;
      Hvar.num_actions_define_cost = 0;
      Hvar.num_facts_define_cost = 0;
      Hvar.weight_facts_define_cost = 0.0;
      Hvar.timed_facts_define_cost = 0.0;
      
      reset_bitarray (Hvar.bit_vect_facts, gnum_ft_block);
      reset_bitarray (Hvar.bit_vect_actions, gnum_ef_block);
      reset_bitarray (Hvar.threated_bit_vect_facts, gnum_ft_block);
      
      memcpy(Hvar.initial_relaxed_bit_vect_facts, vectlevel[level] -> fact_vect, gnum_ft_block * sizeof(int));	  
      memcpy(Hvar.relaxed_bit_vect_preconds, vectlevel[level] -> prec_vect, gnum_ft_block * sizeof(int));
      
      local_search.ls_continue = TRUE;
      
      if (GpG.derived_predicates && GpG.derived_pred_in_preconds) {
	if (!temp_dp_precs)
	  temp_dp_precs = (int *)calloc(gnum_dp_conn, sizeof(int));
	memcpy(temp_dp_precs, vectlevel[level] -> gnum_dp_precs, gnum_dp_conn * sizeof(int));
      }  
      
      /**
	 setto gli elementi tupla nel Hvar.relaxed_bit_vect_preconds 
	 **
	 Put the facts to evaluate in the Hvar.relaxed_bit_vect_preconds
      **/
      for (j = 0; j < i; j++)
	SET_BIT(Hvar.relaxed_bit_vect_preconds, tmp->item[j]);
      
      Hvar.temp_removed_act = -1;
      
      if (DEBUG3) {
	printf("\n\nTUPLE [%d]: ", i);
	for (j = 0; j < i; j++) {
	  printf(" (%d) %s [depth : %d]", tmp->item[j], print_ft_name_string(tmp->item[j], temp_name), tmp->op);
	}
      }
      
      temp_cost = 0.0;

      /**
	 Per ogni elemento della tupla costruisco il piano rilassato per 
	 valutarne il costo
	 **
	 For each fact to support build the relaxed plan to evaluate
	 its cost
      **/
      for (j = 0; j < i; j++) {
	if (!fact_is_supported(tmp->item[j], level))
	  {
	    loc_n_cost.weight = 0.0;
	    loc_n_cost.act_cost = 0.0;
	    loc_n_cost.act_time = 0.0;
	    compute_relaxed_fact_cost ( tmp->item[j],  level, &loc_n_cost, level, MAXFLOAT);

	    if (DEBUG5)
	      printf("\n\nHvar.weight_facts_define_cost: %f Hvar.num_actions_define_cost: %d", Hvar.weight_facts_define_cost,  Hvar.num_actions_define_cost);

	    /**
	       Il costo di una tupla è dato dalla somma dei costi di ogni fatto che la
	       compone
	       **
	       The cost of a set of facts is the sum of the cost of each fact
	     **/
	    temp_cost = Hvar.weight_facts_define_cost + Hvar.num_actions_define_cost;
	    
	    if (temp_cost > (*best_cost))
	      break;
	    
	  }
      }
      
      if (DEBUG3)
	printf("\n\nTUPLE => COST : %.2f\n", temp_cost);

      depth = tmp->op;
      
      /**
	 Se la tupla corrente ha costo minore della migliore trovata fino ad ora
	 essa diviene la migliore
	 **
	 If the cost of the current set of facts is less than the cost of the best
	 set found, the current set become the best
      **/
      if (temp_cost < (*best_cost)) 
	{
	  (*best_cost) = temp_cost;
	  local_search.max_act_incons = temp_cost;
	  idx = tmp;
	  (*num_pc) = i;
	  (*max_depth) = depth;
	}
      /**
	 Se il costo è lo stesso prediligo le tuple a profondità
	 maggiore nel grafo delle regole
	 **
	 If the cost is the same I prefer the deeper set in the
	 rule graph
      **/
      else if (temp_cost == (*best_cost)) 
	{
	  if ((MY_RANDOM % GpG.denominator) < GpG.numerator)
	    {
	      if (MY_RANDOM & 1)
		{
		  idx = tmp;
		  (*num_pc) = i;
		  (*max_depth) = depth;
		}
	    }
	  else 
	    {
	      if (depth > (*max_depth))
		{
		  idx = tmp;
		  (*num_pc) = i;
		  (*max_depth) = depth;
		}
	      else if ((depth == (*max_depth)) && (MY_RANDOM & 1)) 
		{
		  idx = tmp;
		  (*num_pc) = i;
		} 
	    }
	}
      
    }
    
  }
  
  GpG.penalize_inconsistence_in_relaxed_plan=penalize;
  
  if (DEBUG5)
    {
      printf("\n\nBest tuple at level %d : ", level);
      if (idx)
	for (i = 0; i < (*num_pc); i++) 
	  {
	    printf("\n    Fact: %s", print_ft_name_string(idx->item[i], temp_name));
	  }
    }
  
  return idx;
}





/** 
 * Nome: choose_best_tuple_and_level
 * Scopo:  Sceglie la miglior tupla e il miglior livello per
 *         supportare un predicato derivato
 * Tipo: indexed_vect_list*
 * Input: path_set *path, int *num_facts, int level, int *best_level
 * Output: La miglior tupla per supportare un predicato derivato
 *         (e in best_level il miglior livello)
 * Strutture dati principali: path_set
 * Funzioni principali utilizzate: choose_best_facts_set
 * Chiamata da: define_restricted_neighborhood
**
* Name: choose_best_tuple_and_level
* Objective: Choose the easiest set of facts and the best level
*            to support a derived predicate 
* Type: indexed_vect_list*
* Input: path_set *path, int *num_facts, int level, int *best_level
* Output: The best tuple in "path" for supporting a derived predicate
*         (and the best_level)
* Main Data Structures: path_set               
* Main Functions Used: choose_best_facts_set
* Call gives: define_restricted_neighborhood
**/
indexed_vect_list *choose_best_tuple_and_level(path_set *path, int *num_facts, int level, int *best_level) {

  int indlevel, temp_num, i, max_depth, depth;
  float cost, temp_cost;
  indexed_vect_list *tmp, *idx;
 
  if (DEBUG5)
    printf("\n\nCHOOSE BEST TUPLE AND LEVEL");
  
  cost = MAXFLOAT;
  max_depth = -1;

  (*best_level) = level;

  idx = choose_best_facts_set(path, num_facts, level, level, &cost, &max_depth);

  /**
     Per ogni livello precedente a quello in cui si vuole 
     supportare il predicato derivato
     **
     For each level below "level"
   **/
  for (indlevel = get_prev(level); indlevel >= 0; indlevel = get_prev(indlevel)) {

    temp_cost = cost;
    depth = max_depth;

    if (DEBUG5)
      printf("\n\n|==== TUPLE ====| Evaluation at level %d (to level %d)", indlevel, level);
	  
    tmp = NULL;

    /**
       Sceglie la tupla migliore a questo livello, se ne esiste almeno una con 
       costo minore della migliore scelta per il livello precedente
       **
       Choose the best fact set at this level, if there are sets whose
       cost is less than the best choosed for the previous level
     **/
    tmp = choose_best_facts_set(path, &temp_num, indlevel, level, &temp_cost, &depth);

    /**
       Salva la miglior tupla e il miglior livello
       **
       Save the best fact set and the best level
     **/
    if (tmp) {
      (*best_level) = indlevel;
      idx = tmp;
      (*num_facts) = temp_num;
      max_depth = depth;
      cost = temp_cost;
    }

    level = indlevel;
  }

  if (DEBUG3) {
    printf("\n\nBEST TUPLE : ");
    for (i = 0; i < (*num_facts); i++) 
      {
	printf("\n    Fact [num_A : %d] : %s",gft_conn[idx->item[i]].num_A, print_ft_name_string(idx->item[i], temp_name));
      }
  }

  if (DEBUG5)
    printf("\n\nEND CBTAL");

  return idx;
  
}





/** 
 * Nome: test_preconds_propagation
 * Scopo: Controlla se i fatti scelti per supportare un predicato derivato pd
 *        possono essere propagate da from_level a to_level
 *        NB. Dato che ho cercato queste precondizioni al livello to_level
 *            (vedi la chiamata di search_for_base... in create_neighborhood... )
 *            tenendo conto del valore di verità dei predicati derivati a quel livello,
 *            la propagazione di queste precondizioni è sufficiente a garantire
 *            che il pd possa effettivamente essere derivato a questo livello
 * Tipo: int
 * Input: int from_level, int to_level, int *precs, int num
 * Output: TRUE sel'insieme di fatti in *precs può essere propagato da from_level a to_level 
 * Strutture dati principali: ActNode
 *                            FactNode
 * Funzioni principali utilizzate: 
 * Chiamata da: choose_best_facts_set
**
* Name: test_preconds_propagation
* Objective: Check if the set of facts "precs" can be propagated from from_level
*            to to_level
* Type: int 
* Input: int from_level, int to_level, int *precs, int num
* Output: TRUE if precs can be propagated
* Main Data Structures:  ActNode
*                       FactNode             
* Main Functions Used: 
* Call gives: choose_best_facts_set
**/
int test_preconds_propagation(int from_level, int to_level, int *precs, int num) {
  
  int indlevel, j;
  ActNode_list infAction;
  FctNode_list infFact;

  if ((from_level > GpG.curr_plan_length) || (to_level > GpG.curr_plan_length)) {

#ifdef __MY_OUTPUT__
    printf("\nWarning (derived_remain_true): level is greater than plan length (from_level %d to_level %d - plan length %d).", from_level, to_level, GpG.curr_plan_length);
#endif

    return FALSE;
  }
 
  if ((from_level < 0) || (to_level < 0)) {

#ifdef __MY_OUTPUT__
    printf("\nWarning (derived_remain_true): negative level (from_level %d to_level %d).", from_level, to_level);
#endif

    return FALSE;
  }

  /*
  for (j = 0; j < num; j++) {
    if (!CHECK_FACT_POS(precs[j], from_level))
      return FALSE;
  }
  */

  /**
     Controllo la propagazione dei fatti di base
     **
     Check the propagation of basic facts
  **/
  for (indlevel = from_level; indlevel < to_level; indlevel++) {
    
    infAction = GET_ACTION_OF_LEVEL(indlevel);
    
    /**
       Se il livello è vuoto passo al successivo.
       **
       Skip void levels
    **/
    if (infAction -> position < 0)
      continue;

    /**
       Per ogni fatto in precs
       **
       For each fact in precs
    **/
    for (j = 0; j < num; j++) {
    
      infFact = CONVERT_FACT_TO_NODE(precs[j], indlevel);

      /**
	 Se la precondizione è mutuamente esclusiva con l'azione a questo livello
	 allora non potrà essere propagata fino a to_level => è inutile renderla
	 vera a un livello sottostante
	 **
	 If the fact is mutex with the action in this level it can not be
	 propagated to to_level ==> return FALSE.
      **/
      if (GET_BIT(gft_conn[infFact -> position].ef_exclusive_vect, infAction -> position))
	return FALSE;
	
    }
  }

  return TRUE;

}





/** 
 * Nome: create_gdp_path_for
 * Scopo: Costruisce la matrice delle tuple per supportare un predicato derivato
 * Tipo: void
 * Input: int pd_fct, int level
 * Output: path_set *path
 * Strutture dati principali:
 * Funzioni principali utilizzate: search_for_base_preconds
 * Chiamata da: define_restricted_neighborhood
 *              compute_relaxed_fact_cost 
**
* Name: create_gdp_path_for
* Objective: Build the matrix of fact sets to support a derived predicate
* Type: void
* Input: int pd_fct, int level
* Output: path_set *path
* Main Data Structures:         
* Main Functions Used: search_for_base_preconds
* Call gives: define_restricted_neighborhood
*             compute_relaxed_fact_cost 
**/
void create_gdp_path_for(int pd_fct, int level, path_set *path) {

  reset_gdp_path(path);

  gnum_dp_precs = vectlevel[level] -> gnum_dp_precs;
  facts = vectlevel[level] -> fact_vect;
  
  if (!temp_pc_vect) 
    temp_pc_vect = (int *)calloc(gnum_ft_conn, sizeof(int));
  
  memset(temp_pc_vect, 0, gnum_ft_conn * sizeof(int));
  
  search_for_base_preconds(pd_fct, 0, NULL, level, NULL, path, 0);

}






/********** Altre funzioni per la definizione del vicinato  *****  Other functions tested for neighborhood definition  **********/


/**
 * Sceglie l'insieme di precondizioni più facile da supportare in base
 * ai costi di inserimento delle azioni (dg_insertion_action_cost) per
 * supportare ciascun fatto.
 **/ 
indexed_vect_list *choose_best_facts_set_fast(path_set *path, int *num_pc, int level, int to_level, float *best_cost, int *max_depth) {

  int i, j, k;
  float temp_cost;
  int depth;
  indexed_vect_list *tmp = NULL, *idx = NULL;

  if (DEBUG3)
    printf("\n\nTUPLE Search best tuple (level %d)", level);

  temp_cost = MAXINT;

  for (i = 1; i <= path->size; i++) {
    
    for (tmp = path->tuple_set[i]; tmp; tmp = tmp -> next) {

      if (tmp->op < 0)
	continue;

      if ((level < to_level)
	  && (!test_preconds_propagation(level, to_level, tmp->item, i)))
	continue;
    
      if (!idx && (level == to_level)) {
      	idx = tmp;
	(*num_pc) = i;
      }
            
      if (DEBUG3) {
	printf("\n\nTUPLE [%d]: ", i);
	for (j = 0; j < i; j++) {
	  printf(" (%d) %s", tmp->item[j], print_ft_name_string(tmp->item[j], temp_name));
	}
      }


      if ((MY_RANDOM % GpG.denominator) < GpG.numerator)
	{
	  idx = tmp;
	  (*num_pc) = i;
	  (*max_depth) = tmp->op;
	  continue;
	}

      
      for (j = 0; j < i; j++) {
	if (!fact_is_supported(tmp->item[j], level))
	  temp_cost = compute_relaxed_plan_for_inconsistence ( tmp->item[j], tmp->item[j], level, level, (j!=0));
      }

      //temp_cost = Hvar.num_actions_define_cost;
      
      for (k = 0; k < Hvar.num_actions_define_cost; k++) {
	
	if(GpG.mutex_and_additive_effects)
	  temp_cost += (float) count_mutex_noop_at_start (Hvar.list_ef_define_cost[k], level);
	else
	  temp_cost += (float) count_mutex_facts (Hvar.list_ef_define_cost[k], level);
      }
      
      if (DEBUG3)
	printf("\n\nTUPLE => COST : %.2f\n", temp_cost);

      depth = tmp->op;      

      if (temp_cost < (*best_cost)) 
	{
	  (*best_cost) = temp_cost;
	  idx = tmp;
	  (*num_pc) = i;
	  (*max_depth) = depth;
	}
      else if (temp_cost == (*best_cost)) 
	{
	  if (MY_RANDOM & 1)
	    {
	      idx = tmp;
	      (*num_pc) = i;
	      (*max_depth) = depth;
	    }
	  else 
	    {
	      if (depth > (*max_depth))
		{
		  idx = tmp;
		  (*num_pc) = i;
		  (*max_depth) = depth;
		}
	      else if ((depth == (*max_depth)) && (MY_RANDOM & 1)) 
		{
		  idx = tmp;
		  (*num_pc) = i;
		} 
	    }
	}

    }
    
  }
  
  return idx;
}








indexed_vect_list *dg_choose_best_facts_set_2(path_set *path, int *num_pc, int level) {

  int i, j, k;
  float cost, c, d;
  node_cost loc_dg_cost, best_dg_cost;
  indexed_vect_list *tmp = NULL, *idx = NULL;

  cost = MAXFLOAT;

  for (i = 0; i <= path->size; i++) {
    
    for (tmp = path->tuple_set[i]; tmp; tmp = tmp -> next) {
      
      if (!idx) {
	idx = tmp;
	(*num_pc) = i; 
      }

      d = 0;
      for (j = 0; j < i; j++) {
	c = MAXFLOAT;
	best_dg_cost.weight = MAX_COST;
	best_dg_cost.act_cost = MAX_COST;
	best_dg_cost.act_time = MAX_COST;

	for (k = 0; k < gft_conn[tmp->item[j]].num_A; k++) {
	  if (dg_insertion_action_cost(gft_conn[tmp->item[j]].A[k], level, &loc_dg_cost,0.0) < c) {
	    c = loc_dg_cost.weight;
	    best_dg_cost = loc_dg_cost;
	  }	
	}
	
	d = MAX(d, c);
      }
      
      if (d <= 0) {
	(*num_pc) = i;

	return tmp;
      }
      
      if (d < cost) {
	cost = d;
	idx = tmp;
	(*num_pc) = i;
      }
      else if (((d - cost) < MAX_APPROX)
	       && (MY_RANDOM & 1)) {
	idx = tmp;
	(*num_pc) = i;
      }
    }

  }

  return idx;
}





indexed_vect_list *dg_choose_best_facts_set(path_set *path, int *num_pc, int level) {

  int j, i;
  float cost, c;
  int max_depth, depth;
  dg_inform_list loc_dg_cost;
  indexed_vect_list *tmp = NULL, *idx = NULL;
    
  cost = MAXFLOAT;
  max_depth = -1;

  for (i = 0; i <= path->size; i++)
    for (tmp = path->tuple_set[i]; tmp; tmp = tmp->next) {
      
      if (!idx) {
	idx = tmp;
	(*num_pc) = i;
	max_depth = idx->op;
      }
           
      c = 0.0;
    
      for (j = 0; j < i; j++) {

	if (TRUE || GpG.penalize_inconsistence_in_relaxed_plan)
	  { 
	    if (Hvar.constr->constraint_type == C_T_UNSUP_FACT
		&& tmp->item[j] == Hvar.constr->fact)
	      {

		/*
		  Penalizzo le tuple che contengono l'inconsistenza
		  in modo che nn vengano scelte per supportarla nel
		  piano rilassato.
		*/

		c = MAX_COST;
		break;
	      }
	  }

	get_dg_fact_cost(tmp->item[j], level, &loc_dg_cost);
	c = MAX(c, loc_dg_cost->cost);
      
	if (c > cost)
	  break;
	
      }
    
      if (c <= 0) {
	(*num_pc) = i;
	return tmp;
      }
      
      depth = tmp->op;

      if (c < cost) 
	{
	  cost = c;
	  idx = tmp;
	  (*num_pc) = i;
	  max_depth = depth;
	}
      else if (c == cost) 
	{
	  if (TRUE || (MY_RANDOM % GpG.denominator) < GpG.numerator)
	    {
	      if (MY_RANDOM & 1)
		{
		  idx = tmp;
		  (*num_pc) = i;
		  max_depth = depth;
		}
	    }
	  else
	    {
	      if (depth > max_depth) 
		{
		  idx = tmp;
		  (*num_pc) = i;
		  max_depth = depth;
		}
	      else if ((depth == max_depth) && (MY_RANDOM & 1))
		{
		  idx = tmp;
		  (*num_pc) = i;
		}
	    }
	}
    }
  
  return idx;
  
}




int choose_fact_to_support(indexed_vect_list *tuple, int num_f, int level) {

  int choice;
  int i;
  int numA;

  choice = -1;
  numA = MAXINT;

  if (GpG.choose_random_fact_from_tuple 
      || ((MY_RANDOM % GpG.denominator) < GpG.numerator))
    {
      choice = MY_RANDOM % num_f;
    }
  else
    {
      for (i = 0; i < num_f; i++)
	{
	  if (gft_conn[tuple->item[i]].num_A < numA)
	    {
	      numA = gft_conn[tuple->item[i]].num_A;
	      choice = i;
	    }
	}
    }
  

  return tuple->item[choice];
}






/**
 * Valuta il costo di inserimento degli elementi del vicinato
 **/
void evaluate_insertion_neighbors_costs( void ) {

  int i;
  float cost;
  node_cost best_n_cost;

  cost=MAX_COST;
  best_n_cost.weight = MAX_COST;
  best_n_cost.act_cost = MAX_COST;
  best_n_cost.act_time = MAX_COST;

  for (i = 0; i < num_neighborhood; i++) {
    cost  = dg_insertion_action_cost (neighb_vect[i]->act_pos, neighb_vect[i]->act_level, &neighb_vect[i]->cost, 0);
    if (cost < best_n_cost.weight)
      best_n_cost = neighb_vect[i]->cost;
  }
  
}






/**
 * Crea il vicinato per supportare un predicato derivato
 **/
int create_min_tuple_neighborhood(path_set *path, int pd_fct, int level) 
{
  
  int indlevel, i, k, max_depth; 
  float best_cost;
  neighb temp_act;
  indexed_vect_list *tmp;
  action_set acts;
  int ins_actions[gnum_ef_block];

  // Search min size tuple...
  for (i = 0; i <= path->size; i++)
    if (path->tuple_set[i]) break;
  
  if (!path->tuple_set[i])
    return 0;

  best_cost = MAXFLOAT;
  max_depth = -1;

  /*
    NB. Scelgo la tupla migliore al livello level, poi però inserisco
        nel vicinato le azioni per supportare TUTTE le tuple di lunghezza i
  */
  tmp = choose_best_facts_set_fast(path, &i, level, level, &best_cost, &max_depth);

  // For all levels before level...
  for (indlevel = level; indlevel >= 0; indlevel = get_prev(indlevel)) 
    {

      memset(ins_actions, 0, gnum_ef_block * sizeof(int));
      
      // For all tuples...
      for (tmp = path->tuple_set[i]; tmp; tmp = tmp -> next) 
	{ 
	  if (tmp->op < 0)
	    return num_neighborhood;
	  
	  if (!test_preconds_propagation(indlevel, level, tmp->item, i))
	    {
	      tmp->op = -1;
	      break;
	    }
	  
	  search_for_act_to_supp(tmp -> item, i, &acts, indlevel);
	  
	  for (k = 0; k < acts.num_A; k++)
	    {
	      if (GET_BIT(ins_actions, acts.A[k]))
		continue;

	      temp_act.act_pos = acts.A[k];;
	      temp_act.act_level = indlevel;
	      temp_act.constraint_type = C_T_INSERT_ACTION;
	      temp_act.unsup_fact = pd_fct;   
	      insert_element_in_neighb(&temp_act);

	      SET_BIT(ins_actions, acts.A[k]);
	    }
	}
      
    }
  
  return num_neighborhood;
  
}







int choose_best_action_for_derived_predicate(path_set *path, int pd_fct, int level, int *best_action, int *best_level, int action_level) {
  
  int indlevel, cut, i, res;
  indexed_vect_list *tmp;
  action_set neighbors;
  int best_act = -1, best_lev = 0, cel;
  float cost;
  
  node_cost loc_n_cost, best_n_cost;

  res = -1;
  best_act = -1;
  cost=MAX_COST;
  best_n_cost.weight = MAX_COST;
  best_n_cost.act_cost = MAX_COST;
  best_n_cost.act_time = MAX_COST;

  // Search min size tuple...
  for (cut = 0; cut <= path->size; i++)
    if (path->tuple_set[cut]) break;
    
  // Per tutti i livelli da 0 a level
  for (indlevel = level; indlevel >= 0; indlevel--) {
    
    if ((indlevel < level) && !CHECK_ACTION_OF_LEVEL(indlevel))
      continue;
    
    for (tmp = path->tuple_set[cut]; tmp; tmp = tmp -> next) {

      if (!test_preconds_propagation(indlevel, level, tmp->item, cut))
	continue;
  
      /*
	Cerco delle azioni in grado di supportare i fatti di base
      */
      search_for_act_to_supp(tmp -> item, 1, &neighbors, indlevel);

      if (neighbors.num_A > 0)
	res = 1;
      
      /*
	Valuto le azioni trovate per scegliere la best action
      */
      for (i = 0; i < neighbors.num_A; i++) {

	cel = neighbors.A[i];
	
	if (GpG.accurate_cost <= COMPUTE_ADD_COST)
	  {
	    cost = fast_insertion_action_cost (cel, indlevel, action_level); 
	    loc_n_cost.act_cost = get_action_cost (cel, indlevel, NULL);
	    loc_n_cost.act_time = get_action_time (cel, indlevel);
	  }
	else
	  cost = best_action_evaluation  (cel, indlevel,  &loc_n_cost, 0, &best_n_cost);
	
	if (best_n_cost.weight >= cost)
	  {
	    if (best_n_cost.weight == cost
		&& weight_cost (&best_n_cost) <= weight_cost (&loc_n_cost))
	      continue;
	    best_act = cel;
	    best_lev = indlevel;
	    best_n_cost.weight = loc_n_cost.weight;

	    best_n_cost.act_cost = loc_n_cost.act_cost;
	    best_n_cost.act_time = loc_n_cost.act_time;

	    if (best_n_cost.weight <= 0)
	      break;	
	  }

      } 
      
    }
  }

  *best_action = best_act;
  *best_level = best_lev;
  
  return res;
  
}







