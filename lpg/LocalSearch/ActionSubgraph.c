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
 * File: ActionSubgraph.c
 * Description: Action subgraph management 
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti,
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/






#include <math.h>
#include "lpg.h"
#include "inst_utils.h"
#include "LocalSearch.h"
#include "ActionSubgraph.h"
#include "ComputeReachInf.h"
#include "LpgOutput.h"
#include "output.h"
#include "utilities.h"
#include "numeric.h"
#include "H_relaxed.h"
#include "check.h"
#include "LpgTime.h"
#include "derivedpred.h"


/***************************************
            BUILD VECTLEVEL
 ***************************************/



/**  OK 26-07-04
 * Name: update_num_condition_of_cond_ef
 * Scopo: Aggiorna numero di condizioni non supportate dagli effetti condizionali dell'azione del livello
 * Tipo: void
 * Input: int level
 *        int fact
 *        int value
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: update_num_condition_of_cond_ef
*  Objective: Updates the number of conditions not supported by the conditional effects of the action of the level
*  Type: void
*  Input: int level
*         int fact
*         int value
*  Output:
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
void update_num_condition_of_cond_ef(int level, int fact, int value)
{
	CondInform	*info;
	int		cef;
	int		ef;
	int		i;

	fprintf(stderr, "update_num_condition_of_cond_ef in ActionSubgrapc.c mai stata testata!");
	exit(1);

	if (!cond_eff_is_enabled())
		return;

	info = &vectlevel[level]->condinform;
	ef = vectlevel[level]->action.position;
	for (cef = gef_conn[ef].I[0], i = 0;
		i < gef_conn[ef].num_I;
		cef++, i++) {
		if (is_fact_in_preconditions_of_cond(cef, fact) ||
			is_fact_in_preconditions_overall_of_cond(cef, fact) ||
			is_fact_in_preconditions_end_of_cond(cef, fact)) {
			if (value)
				info->non_supp_of_cond_ef[i]--;
			else
				info->non_supp_of_cond_ef[i]++;
		}
	}
}




/**  OK 26-07-04
 * Name: get_next
 * Scopo: ritorna il livello  successivo non vuoto
 * Tipo: int
 * Input: int level
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: get_next
*  Objective: Return next not empty level
*  Type:  int
*  Input: int level
*  Output:
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
int get_next(int level) {

  if ((level == GpG.curr_plan_length) || (level < 0))
    return GpG.max_plan_length;

  if (vectlevel[level]) {
      if (vectlevel[level] -> next)
	return *(vectlevel[level] -> next);
      else
	return GpG.curr_plan_length;
  }
  else if (level > 0) 
    return get_next(level-1);
  else return 0;
}


/**  OK 26-07-04
 * Name: get_prev
 * Scopo: Ritorna il livello successivo non vuoto
 * Tipo: int
 * Input: int level
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: get_prev
*  Objective: Return next not empty level
*  Type: int
*  Input: int level
*  Output:
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
int get_prev(int level) {
 register int i;

  if (level == 0 || (level < 0))
    return -1;

  if (vectlevel[level]) {
      if ( vectlevel[level] -> prev)
	return *(vectlevel[level] -> prev);
      else 
	return 0;
  }
  else 
    if (level < GpG.max_plan_length)
    {
      for(i=level-1; level>=0; level--)
	if (vectlevel[i])
	  break;
      return i;
    }
  else return GpG.curr_plan_length;
}


/**  OK 26-07-04
 * Name: init_num_condition_of_cond_ef
 * Scopo: Inizializzazione numero di condizioni non supportate degli effetti condizionali
 * Tipo: void
 * Input: int level
 *        int e
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: init_num_condition_of_cond_ef
*  Objective: Initialization of the number of conditions not supported of the conditional effects
*  Type: void
*  Input: int level
*         int e
*  Output:
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
void init_num_condition_of_cond_ef(int level, int e)
{
	CondInform	*info;
	EfConn		*ef;
	int		*p;
	int		*q;

	if (!cond_eff_is_enabled())
		return;

	ef = &gef_conn[e];
	if (ef->num_I == 0)
		return;

	info = &vectlevel[level]->condinform;
	info->num_prec = ef->num_I;
	info->non_supp_of_cond_ef = (int *) calloc (ef->num_I, sizeof (int)); // numero di prec. non soddisfatte

	for (p = info->non_supp_of_cond_ef, q = ef->I;
		q < &ef->I[ef->num_I];
		p++, q++)
		*p = gcondef_conn[*q].num_PC;
}



/**  OK 26-07-04
 * Name: print_next_prev
 * Scopo:
 * Tipo: void
 * Input: int level
 *        int ins_rem
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: print_next_prev
*  Objective:
*  Type: void
*  Input: int level
*         int ins_rem
*  Output:
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
void print_next_prev(int level, int ins_rem) {
  int i;
  printf("\n*************************************************************************************************");
  for (i = 0; i < GpG.max_plan_length; i++)
    if (vectlevel[i]) {
      printf("\nL : %d P : %d S : %d A : ", i, get_prev(i), get_next(i));
      if ((CHECK_ACTION_OF_LEVEL(i) && !(i == level && ins_rem == C_T_REMOVE_ACTION))  
	  || ((i == level) && (ins_rem == C_T_INSERT_ACTION)))
	printf("SI");
      else
	printf("NO");
    }
}


/**  OK 26-07-04
 * Name: update_next_and_prev
 * Scopo: Aggiorna il prossimo e il precedente collegamento tra i livelli
 * Tipo: void
 * Input: int level
 *        int ins_rem
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: update_next_and_prev
*  Objective: Update "next" and "previous" link among levels
*  Type: void
*  Input: int level
*         int ins_rem
*  Output:
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
void update_next_and_prev(int level, int ins_rem) {
  int next, prev, i;

  //printf("\nUpdate next and prev ...\n********************");
  
  if (ins_rem == C_T_INSERT_ACTION) {
    /**
       Aggiorno prev e next di questo livello
       **
       Updating prev and next of this level
    **/
    if (level > 0)
      next = get_next(level - 1);
    else
      for (next = level+1; (next < GpG.curr_plan_length)  && (!vectlevel[next]); next++);
    if (level < GpG.curr_plan_length)
      prev = get_prev(level + 1);
    else 
      for (prev = level-1; (prev > 0) && (!vectlevel[prev]); prev--);
    
    if (prev >= 0) {
      if (prev != level) 
	vectlevel[level] -> prev = &(vectlevel[prev] -> level);
    }
    else 
      vectlevel[level] -> prev = NULL;
    
    if (next < GpG.max_plan_length) {
      if (next != level)
	vectlevel[level] -> next = &(vectlevel[next] -> level);
    }
    else
      vectlevel[level] -> next = NULL; 
    /**
       Aggiorno prev e next degli altri livelli
       **
       Updating prev and next of the others levels
    **/
    for (i = level + 1; i < GpG.max_plan_length; i++)
      if ((vectlevel[i]) && ((!vectlevel[i] -> prev) || (*(vectlevel[i] -> prev) < level)) && (i > 0))
	vectlevel[i] -> prev = &(vectlevel[level] -> level);
      else /*if (!vectlevel[i])*/ continue;
    //else break;
    
    for (i = level - 1; i >= 0; i--)
      if ((vectlevel[i]) && ((!vectlevel[i] -> next) || (*(vectlevel[i] -> next) > level)) /*&& ((i < GpG.curr_plan_length) || (i < GpG.fixpoint_plan_length))*/)
	vectlevel[i] -> next = &(vectlevel[level] -> level);
      else /*if (!vectlevel[i])*/ continue;
    //else break;

    vectlevel[0] -> prev = NULL;
    if (GpG.curr_plan_length != 0)
      vectlevel[GpG.curr_plan_length] -> next = NULL;
  }
  else {
    //if (((level < (GpG.fixpoint_plan_length - 2)) || (level >= (GpG.fixpoint_plan_length))) && (level < GpG.curr_plan_length) ) {
      
    if (level > 0)
      for (i = level + 1; (i > 0) && (i < GpG.max_plan_length); i++)
	if ((vectlevel[i]) && (*(vectlevel[i] -> prev) == level))
	  vectlevel[i] -> prev = vectlevel[level] -> prev;
    if (level < GpG.curr_plan_length)
      for (i = level - 1; (i >= 0) && (i < GpG.curr_plan_length); i--)
	if ((vectlevel[i]) && (*(vectlevel[i] -> next) == level))
	  vectlevel[i] -> next = vectlevel[level] -> next;
    //}
  }
  // print_next_prev(level, ins_rem);
}

/**  OK 26-07-04
 * Name: allocate_data_level
 * Scopo:
 * Tipo: static void
 * Input: register int level
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: allocate_data_level
*  Objective:
*  Type: static void
*  Input: register int level
*  Output:
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
static void allocate_data_level (register int level)
{
  unsigned int i;
  FctNode supp_fct;
  NoopNode supp_noop;

  FctNode_list next_fct;
  NoopNode_list next_noop;

  /**
     setto la struttura di supporto
     **
     setting the support structure
  **/
  memset (&supp_fct, 0, sizeof (supp_fct));
  supp_fct.false_position = -1;
  supp_fct.level = &vectlevel[level]->level;

  /**
     le copio tutte
     **
     copy of all 
  **/
  next_fct = vectlevel[level]->fact;
  for (i = 0; i <= GpG.max_num_facts; i++)
    {
      supp_fct.position = i;
      memcpy (next_fct, &supp_fct, sizeof (FctNode));
      next_fct++;
    }

  /**
     setto la struttura di supporto noop 
     **
     setting the noop support structure
  **/
  memset (&supp_noop, 0, sizeof (supp_noop));
  supp_noop.false_position = -1;
  supp_noop.level = &vectlevel[level]->level;

  /**
     le copio tutte
     **
     copy of all 
  **/
  next_noop = vectlevel[level]->noop_act;
  for (i = 0; i <= GpG.max_num_facts; i++)
    {
      supp_noop.position = i;
      memcpy (next_noop, &supp_noop, sizeof (NoopNode));
      next_noop++;
    }

  /**
     setto la struttura di supporto
     **
     setting the support structure
  **/
  vectlevel[level]->action.position = -1;
  vectlevel[level]->action.level = &vectlevel[level]->level;

  if (GpG.derived_predicates)
    vectlevel[level]->active_rules = alloc_vect(gnum_dp_block);

#ifdef	__TEST__
  for (i = 0; i <= GpG.max_num_facts; i++)
    {
      if (vectlevel[level]->fact[i].position != i)
	printf ("Error 1: %d %d\n\r", vectlevel[level]->fact[i].position, i);
      if (vectlevel[level]->fact[i].false_position != -1)
	printf ("Error 2:\n\r");
      if (vectlevel[level]->fact[i].level != &vectlevel[level]->level)
	printf ("Error 5\n\r");
    }
#endif


#ifdef TES_GR
  for (i = 0; i <= GpG.max_num_actions; i++)
    {
      if (vectlevel[level]->actions[i].position != i)
	printf ("Error 10");
      if (vectlevel[level]->actions[i].false_position != -1)
	printf ("Error 11");
      if (vectlevel[level]->actions[i].lev_false_position != -1)
	printf ("Error 12");
      if (vectlevel[level]->actions[i].level != &vectlevel[level]->level)
	printf ("Error 14");
      if (vectlevel[level]->actions[i].preco != NULL)
	printf ("Error 19");
      if (vectlevel[level]->actions[i].add != NULL)
	printf ("Error 20");
    }
#endif
}


/**  OK 26-07-04
 * Name: allocate_level
 * Scopo: alloca un livello dinamicamente
 * Tipo: def_level_list
 * Input: none
 * Output: il puntatore alla struttura appena allocata
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: allocate_level
*  Objective: allocates dinamically a level
*  Type: def_level_list
*  Input: none
*  Output: the pointer to the structure now allocated
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
def_level_list allocate_level (void)
{
  def_level_list vect;		/**
				   puntatore nuova struttura level
				   **
				   pointer to the new level structure
				**/

  int aux;
#ifdef __TEST__
  int cont;
#endif

  /**
     alloco la struttura LEVEL
     **
     allocating the structure LEVEL
  **/
  vect = (def_level_list) malloc (sizeof (struct LEVEL));
  memset (vect, 0, sizeof (struct LEVEL));

  /**
     alloco i fatti
     **
     allocating the facts
  **/
  if (GpG.max_num_facts != 0) {
    vect->fact = (FctNode *) calloc (GpG.max_num_facts + 1, sizeof (FctNode));
    if (vect->fact == NULL){ 
      MSG_ERROR ( WAR_NO_MEMORY );
      exit(1);
    }
  }

  else
    {
      MSG_ERROR (" No facts \r\n");
    }

  /**
     alloco noop 
     **
     allocating noop
  **/
  if (GpG.max_num_facts != 0) {
    vect->noop_act =
      (NoopNode *) calloc (GpG.max_num_facts + 1, sizeof (NoopNode));
    if (vect->noop_act == NULL){
      MSG_ERROR ( WAR_NO_MEMORY );
      exit(1);
    }
  }

  else
    {
      MSG_ERROR (" No noops \r\n");
    }

  /**
     Allocazione degli array lambda_prec e lambda_me.
     **
     Allocating lambda_prec and lambda_me arrays
  **/
  if (GpG.lm_multilevel)
    {
      vect->lambda_prec = (float *) calloc (gnum_ef_conn, sizeof(float));
      vect->lambda_me = (float *) calloc (gnum_ef_conn, sizeof(float));
    }
  /**
     alloco tutti i bit array
     **
     allocating all of the bit array
  **/
  vect->prec_vect = (int *) calloc (gnum_ft_block, sizeof (int));
  vect->fact_vect = (int *) calloc (gnum_ft_block, sizeof (int));
  memset(vect -> fact_vect, 0, gnum_ft_block * sizeof(int));
  vect->true_crit_vect = (int *) calloc (gnum_ft_block, sizeof (int));
  vect->false_crit_vect = (int *) calloc (gnum_ft_block, sizeof (int));
  vect->noop_act_vect = (int *) calloc (gnum_ft_block, sizeof (int));
  vect->noop_prec_act_vect = (int *) calloc (gnum_ft_block, sizeof (int));

  vect->numeric = (NumInfo *) calloc (1, sizeof (NumInfo));

  vect->numeric->values = (float *) calloc (gnum_comp_var, sizeof (float));	// XYZ
  vect->numeric->values_after_start =   (float *) calloc (gnum_comp_var, sizeof (float));
  vect->numeric->modified_vars_start = (int *) calloc (gnum_block_compvar, sizeof (int));	// XYZ

  vect->numeric->modified_vars_end =  (int *) calloc (gnum_block_compvar, sizeof (int));
  vect->numeric->used_vars =  (int *) calloc (gnum_block_compvar, sizeof (int));
  vect->numeric->w_is_goal = (short *) calloc (gnum_comp_var, sizeof (short));
  vect->numeric->w_is_used = (short *) calloc (gnum_comp_var, sizeof (short));
  vect->numeric->false_position =  (int *) calloc (gnum_comp_var, sizeof (int));

  vect -> gnum_dp_precs = NULL;
 
  /*
    LA
  */
  if (GpG.lm_multilevel)
    for(aux=0;aux<gnum_ef_conn;aux++)  {
      vect->lambda_prec[aux]=1.0;
      vect->lambda_me[aux]=1.0;
    }

  /**
     Azzeramento
     **
     Setting to zero
  **/
  memset (vect->numeric->values, 0, gnum_comp_var * sizeof (float));
  memset (vect->numeric->values_after_start, 0,  gnum_comp_var * sizeof (float));
  memset (vect->numeric->modified_vars_start, 0,  gnum_block_compvar * sizeof (int));
  memset (vect->numeric->modified_vars_end, 0,  gnum_block_compvar * sizeof (int));
  memset (vect->numeric->used_vars, 0, gnum_block_compvar * sizeof (int));
  memset (vect->numeric->w_is_goal, 0, gnum_comp_var * sizeof (short));
  memset (vect->numeric->w_is_used, 0, gnum_comp_var * sizeof (short));
  memset (vect->numeric->false_position, -1, gnum_comp_var * sizeof (int));

  vect -> next = vect -> prev = NULL;
 
  return (vect);
}


/**  OK 26-07-04
 * Name: create_vectlevel
 * Scopo:
 * Tipo: def_level_list
 * Input: int fixpoint
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: create_vectlevel
*  Objective:
*  Type: def_level_list
*  Input: int fixpoint
*  Output: 
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
def_level_list create_vectlevel (int fixpoint)
{
  static int time = 0;
  def_level_list vect;

#ifdef __TEST__
  if(GpG.max_temp_vect+GpG.max_plan_length!=time)
    printf("\n Error create_number  ");
#endif

  GpG.max_plan_length++;

  if (GpG.max_plan_length >= MAX_PLAN_LENGTH) {
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_MAX_PLAN_LENGTH );
#else
    printf( WAR_MAX_PLAN_LENGTH );
#endif
    exit (1);
  }

  vect = allocate_level ();

  vectlevel[time] = vect;
  vectlevel[time]->level = time;
  vectlevel[time]->is_cri_computed=FALSE;

  /* PREDICATI DERIVATI*/
  if (GpG.derived_predicates)
    initialize_dp_num_prec_vector(&vectlevel[time] -> gnum_dp_precs);
  /* END*/

  allocate_data_level (time);

  if (time >= MAX_PLAN_LENGTH + 1) {
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_MAX_PLAN_LENGTH );
#else
    printf( WAR_MAX_PLAN_LENGTH );
#endif
    exit (1);
  }

  if (time == 0)
    {
      tot_alloc_mem_size = 0;
    }

  tot_alloc_mem_size += sizeof (struct LEVEL);
  tot_alloc_mem_size += (1 + GpG.max_num_facts) * (sizeof (FctNode) + sizeof(NoopNode));	// 1 azione + fatti + noop 
  tot_alloc_mem_size += (sizeof (int) * (gnum_ft_block + 1)) * 14;

  if (GpG.lm_multilevel) 
    tot_alloc_mem_size += (gnum_ef_conn * sizeof(float)) * 2;  

  time++;

  return vect;
}



/***************************************
            INSERT LEVEL
 ***************************************/

/**  OK 26-07-04
 * Name: reset_level
 * Scopo:
 * Tipo: void
 * Input: int time
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: reset_level
*  Objective:
*  Type: void
*  Input: int time
*  Output: 
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
void reset_level(int time)
{
  FctNode_list inf_f;
  NoopNode_list inf_n;
  ActNode_list inf_a;
  int i;


  if (vectlevel[time] == NULL)
    return;
  
  vectlevel[time] -> next = vectlevel[time] -> prev = NULL;
 
  /**
     per sicurezza resetto le false_position e w_is_goal
     **
     for security I reset false_position and W_is_goal
  **/
  memset (vectlevel[time]->numeric->false_position, -1,
	  gnum_comp_var * sizeof (int));
  memset (vectlevel[time]->numeric->w_is_goal, 0,
	  gnum_comp_var * sizeof (short));

  if (time != 0)
    copy_num_values_from_level_to_level (0, time, FALSE);
  vectlevel[time]->level = time;
  vectlevel[time]->num_actions = 0;
  vectlevel[time]->modified = 0;

  reset_bitarray (vectlevel[time]->prec_vect, gnum_ft_block);
  vectlevel[time]->num_prec = 0;
  reset_bitarray (vectlevel[time]->fact_vect, gnum_ft_block);
  if (GpG.derived_predicates)
    initialize_dp_num_prec_vector(&vectlevel[time] -> gnum_dp_precs);

  vectlevel[time]->num_fact = 0;
  reset_bitarray (vectlevel[time]->true_crit_vect, gnum_ft_block);
  vectlevel[time]->num_true_crit = 0;
  reset_bitarray (vectlevel[time]->false_crit_vect, gnum_ft_block);
  vectlevel[time]->num_false_crit = 0;

  reset_bitarray (vectlevel[time]->noop_act_vect, gnum_ft_block);
  reset_bitarray (vectlevel[time]->noop_prec_act_vect, gnum_ft_block);
  if (GpG.derived_predicates)
    reset_bitarray (vectlevel[time]->active_rules, gnum_dp_block);

  for (i = 0; i < GpG.max_num_facts; i++) {
    inf_f = &vectlevel[time]->fact[i];
    inf_f->w_is_goal = 0;
    inf_f->w_is_derived_goal = 0;
    inf_f->w_is_derived_true = 0;
    inf_f->w_is_used = 0;
    inf_f->w_is_true = 0;
    inf_f->false_position = -1;
    CONVERT_FACT_TO_VERTEX (i)->lamda_prec = CONVERT_FACT_TO_VERTEX (i)->lamda_me = 1.0;	//  LM
    CONVERT_FACT_TO_VERTEX (i)->last_lm_me = CONVERT_FACT_TO_VERTEX (i)->last_lm_prec = 0;	//  LM
    
    inf_f->time_f = NOTIME;
    inf_f->action_f = NULL;
    
    // NOOPS
    inf_n = &vectlevel[time]->noop_act[i];
    inf_n->w_is_goal = 0;
    inf_n->w_is_used = 0;
    inf_n->w_is_true = 0;
    inf_n->w_is_overall = 0;
    inf_n->false_position = -1;
    
    inf_n->time_f = NOTIME;
    inf_n->action_f = NULL;
  }

  inf_a = &vectlevel[time]->action;

  inf_a->w_is_goal = 0;
  inf_a->w_is_used = 0;
  inf_a->w_is_true = 0;
  inf_a->false_position = -1;
  
  inf_a->position = -1;
  inf_a->being_removed = 0;
  free_noop_not_in (inf_a);
  vectlevel[time]->max_action_time = 0.0;
  
  inf_a->time_f = 0.0;
  inf_a->action_f = NULL;
  inf_a->ord_pos = 0;

  reset_computed_dg_costs (time);
}



/**  OK 27-07-04
 * Name: compress_vectlevel
 * Scopo: Toglie i livelli vuoti
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: compress_vectlevel
*  Objective: Remove empty levels
*  Type: void
*  Input: none
*  Output: 
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
//  DA COMPLETARE!!!
void compress_vectlevel()
{
  int i,j, level, last_used, last_free=-1;
  int start_free=0;

  printf("\n Start compress: GpG.curr_plan_length %d  Action %d",GpG.curr_plan_length,GpG.num_actions); 
  print_actions_in_subgraph();
  check_plan (GpG.curr_plan_length);
  printf("\n -> Compress...\n");

  last_used = GpG.fixpoint_plan_length-1;
  
  for(level=GpG.fixpoint_plan_length; level<GpG.curr_plan_length; level++) {
   
    if(GET_ACTION_POSITION_OF_LEVEL(level)>=0) {
      
      /**
	 E' la prima azione inserita
	 **
	 It is the first action inserted
      **/
      if(last_used==GpG.fixpoint_plan_length-1){
	
	/**
	   Devo spostarla se sono a un livello maggiore di GpG.fixpoint_plan_length
	   **
	   I must to move it if I am at a bigger level of GpG.fixpoint_plan_length
	**/
	if(level>++last_used){

	  vectlevel[last_used]=vectlevel[level];
	  vectlevel[last_used]->level=last_used;

	  if(GpG.max_temp_vect>0){	  
	    for (i = 0; i < GpG.max_num_facts; i++){
	      if((vectlevel[last_used-1]->noop_act[i].w_is_goal==1) && (temp_vectlevel[GpG.max_temp_vect-1]->noop_act[i].w_is_goal==2))
		vectlevel[last_used-1]->noop_act[i].w_is_goal=2;

	     if((vectlevel[last_used]->fact[i].w_is_true==1) && (temp_vectlevel[start_free]->fact[i].w_is_true==2))    
	      vectlevel[last_used]->fact[i].w_is_true=2;
	
	    if (GpG.temporal_plan)
	      if(vectlevel[last_used]->fact[i].w_is_true>0)    
		vectlevel[last_used]->fact[i].action_f=temp_vectlevel[start_free]->fact[i].action_f;
    
	    } // end for sui fatti
	  }
	  else {
	    MSG_ERROR(" Error ");
	    printf("\n level %d  last_used %d  fixpoint %d",level,last_used,GpG.fixpoint_plan_length);
	  }
	
	}
	
      }
      
      else{
	/**
	   non e' la prima azione spostata
	   **
	   it is not the first action moved
	**/

      if(last_free<level-1){

	vectlevel[last_used+1]=vectlevel[level];
	vectlevel[last_used+1]->level=last_used+1;
      }

	else{
	  vectlevel[last_used+1]=vectlevel[level];
	  vectlevel[last_used+1]->level=last_used+1;

	  /**
	     Sincronizzazione con i livelli tolti
	     **
	     Sincronization with the removed levels
	  **/	  
	  for (i = 0; i < GpG.max_num_facts; i++){
	    
	    if((vectlevel[last_used+1]->fact[i].w_is_true==1) && (temp_vectlevel[start_free]->fact[i].w_is_true==2))    
	      vectlevel[last_used+1]->fact[i].w_is_true=2;
	
	    if (GpG.temporal_plan)
	      if(vectlevel[last_used+1]->fact[i].w_is_true>0)    
		vectlevel[last_used+1]->fact[i].action_f=temp_vectlevel[start_free]->fact[i].action_f;
	    
	    if((vectlevel[last_used]->noop_act[i].w_is_goal==1) && (temp_vectlevel[GpG.max_temp_vect-1]->noop_act[i].w_is_goal==2))
	      vectlevel[last_used]->noop_act[i].w_is_goal=2;
	  } // end for sui fatti
	  
	  memcpy (vectlevel[last_used+1]->true_crit_vect, temp_vectlevel[start_free]->true_crit_vect, sizeof (int) * gnum_ft_block);
	  
	  // End sincronizzazione
	}
      last_used++;
      }
    } //end if GET_ACTION_POSITION
    else {


      if(last_free<level-1)
	start_free=GpG.max_temp_vect;
      
      temp_vectlevel[GpG.max_temp_vect++] = vectlevel[level];
      
      last_free=level;  
    } // end else
  }// end for level

  /**
     livello dei goal
     **
     goal level
  **/
  vectlevel[last_used+1]=vectlevel[level];
  vectlevel[last_used+1]->level=last_used+1;
  
if(last_free==level-1){
  
    for (i = 0; i < GpG.max_num_facts; i++){
      
     if((vectlevel[last_used+1]->fact[i].w_is_true==1) && (temp_vectlevel[start_free]->fact[i].w_is_true==2))    
	vectlevel[last_used+1]->fact[i].w_is_true=2;
     
     if (GpG.temporal_plan)
       if(vectlevel[last_used+1]->fact[i].w_is_true>0)
	 vectlevel[last_used+1]->fact[i].action_f=temp_vectlevel[start_free]->fact[i].action_f;
     
    } // end for sui fatti

    memcpy (vectlevel[last_used+1]->true_crit_vect, temp_vectlevel[start_free]->true_crit_vect, sizeof (int) * gnum_ft_block);
    }

  for(i=GpG.curr_plan_length+1;i<GpG.max_plan_length;i++)
       temp_vectlevel[GpG.max_temp_vect++] = vectlevel[i];

  GpG.curr_plan_length=last_used+1;
  GpG.max_plan_length=GpG.curr_plan_length+1;

  for(i=0;i< GpG.max_plan_length;i++)
    for(j=i;j< GpG.max_plan_length;j++)
      if(vectlevel[i]==vectlevel[j] && i!=j)
	printf("\n\n XXXX vectlevel %d  temp_vect %d  plan %d  max %d",i,j,GpG.curr_plan_length, GpG.max_plan_length );

#ifdef __TEST__
    print_actions_in_subgraph();
    check_plan (GpG.curr_plan_length);
    if (GpG.temporal_plan)
      check_temporal_plan();
    printf("\n End compress: new GpG.curr_plan_length %d\n",GpG.curr_plan_length);  
    
#endif
}



/**  OK 27-07-04
 * Name: up_vectlevel
 * Scopo: Crea un livello vuoto in cui inserire un'azione
 * Tipo: void
 * Input: int level
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: up_vectlevel
*  Objective: Make an empty level in which we insert an acion
*  Type: void
*  Input: int level
*  Output: 
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
void up_vectlevel (int level)
{
  int i, k, j, noop_pos, l1;
  def_level_list temp_level, temp_level_2, max_temp_level;
  
  if(GpG.curr_plan_length+1>=MAX_PLAN_LENGTH)
    compress_vectlevel();
  
if (GpG.curr_plan_length >= (GpG.max_plan_length - 1) )
    {
    /*****************************************************************************************/
    /*       BMVM controllare perche' non siamo sicuri del secondo parametro passato         */
    /*****************************************************************************************/
     

  /**
     Se ci sono elementi nella lista temporanea li prendo
     **
     If there are elements in the temporary list i take them
  **/
  if(GpG.max_temp_vect>0){
    GpG.curr_plan_length++;
    vectlevel[GpG.curr_plan_length]=temp_vectlevel[GpG.max_temp_vect-1];
    reset_level(GpG.curr_plan_length);
    temp_vectlevel[GpG.max_temp_vect-1]=NULL;
    GpG.curr_plan_length--;
    GpG.max_temp_vect--;
    GpG.max_plan_length++;
  }
  else {
    create_vectlevel (1);
  }

#ifdef __TEST__
      if (level >= GpG.curr_plan_length || level <= 0)
	printf ("\n  Upvectlevel %d", level);
#endif
    }
   GpG.curr_plan_length++;
   
   
#ifdef __TEST___
  check_plan (GpG.curr_plan_length);
#endif

  if (DEBUG2)
    printf ("\n    insert action => increase level %d ", level);

  /**
     Ultimo elemento del vettore: e' il livello che stiamo inserendo
     **
     Last elemnt of the array: is the level that we are inserting
  **/
  max_temp_level = vectlevel[GpG.curr_plan_length];

  /**
     Spostiamo tutti i livelli in su di una posizione
     **
     We move all levels up of one position
  **/
  temp_level = vectlevel[level];
  for (i = level; i < GpG.curr_plan_length; i++)
    {
      temp_level_2 = vectlevel[i + 1];
      vectlevel[i + 1] = temp_level;
      temp_level->level += 1;
      temp_level = temp_level_2;
    }

  vectlevel[level] = max_temp_level;
  vectlevel[level]->level = level;
  vectlevel[level]->modified = 0;

 
  // Insert a nooplevel at "level" 

  l1 = level + 1;

  if (GpG.derived_predicates) {
    memcpy(vectlevel[level] -> gnum_dp_precs, vectlevel[l1] -> gnum_dp_precs, gnum_dp_conn * sizeof(int));
    memcpy(vectlevel[level]->active_rules, vectlevel[l1]->active_rules, gnum_dp_block * sizeof(int));
  }

  /**
     copia i vettori delle precondizioni, fatti, noop
     **
     it copies the preconditions, fact and noop arrays
  **/
  memcpy (vectlevel[level]->prec_vect, vectlevel[l1]->prec_vect,
	  sizeof (int) * gnum_ft_block);
  memcpy (vectlevel[level]->fact_vect, vectlevel[l1]->fact_vect,
	  sizeof (int) * gnum_ft_block);
  memcpy (vectlevel[level]->true_crit_vect, vectlevel[l1]->true_crit_vect,
	  sizeof (int) * gnum_ft_block);
  memcpy (vectlevel[level]->false_crit_vect, vectlevel[l1]->false_crit_vect,
	  sizeof (int) * gnum_ft_block);
  memset (vectlevel[level]->noop_prec_act_vect, 0,
	  sizeof (int) * gnum_ft_block);
  memset (vectlevel[level]->noop_act_vect, 0, sizeof (int) * gnum_ft_block);

  /**
     inizializza vettore delle corrispondenze azioni - timed literals
     **
     it initialize the array of the correspondence actions
  **/
 if ((GpG.timed_facts_present) && (vectlevel[level] -> action.PC_interval != NULL))
   memset (vectlevel[level] -> action.PC_interval, -1, gnum_timed_facts * sizeof (int));

  /**
     Aggiorna i vettori critici 
     **
     Updating the critical arrays
  **/
  for (k = 0; k < gnum_ft_block; k++)
    {
      vectlevel[l1]->true_crit_vect[k] =
	vectlevel[l1]->prec_vect[k] & vectlevel[l1]->fact_vect[k];
      vectlevel[l1]->false_crit_vect[k] =
	vectlevel[l1]->prec_vect[k] & (~vectlevel[l1]->fact_vect[k]);
    }

  /** 
     nessuna azione nel livello
     **
     none action in the level
  **/
  vectlevel[level]->action.w_is_used = 0;
  vectlevel[level]->action.w_is_goal = 0;
  vectlevel[level]->action.false_position = -1;

  /**
     Copia valori numerici
     **
     Copying numerical values
  **/
  memcpy (vectlevel[level]->numeric->values, vectlevel[l1]->numeric->values,
	  sizeof (float) * gnum_comp_var);
  memcpy (vectlevel[level]->numeric->values_after_start,
	  vectlevel[l1]->numeric->values_after_start,
	  sizeof (int) * gnum_comp_var);
  memcpy (vectlevel[level]->numeric->w_is_goal,
	  vectlevel[l1]->numeric->w_is_goal, sizeof (short) * gnum_comp_var);
  memcpy (vectlevel[level]->numeric->w_is_used,
	  vectlevel[l1]->numeric->w_is_used, sizeof (short) * gnum_comp_var);
  memset (vectlevel[level]->numeric->false_position, -1,
	  sizeof (int) * gnum_comp_var);
  memset (vectlevel[level]->numeric->w_is_goal, 0,
	  sizeof (short) * gnum_comp_var);
  memcpy (vectlevel[level]->numeric->modified_vars_start,
	  vectlevel[l1]->numeric->modified_vars_start,
	  sizeof (int) * gnum_block_compvar);
  memcpy (vectlevel[level]->numeric->modified_vars_end,
	  vectlevel[l1]->numeric->modified_vars_end,
	  sizeof (int) * gnum_block_compvar);
  memcpy (vectlevel[level]->numeric->used_vars,
	  vectlevel[l1]->numeric->used_vars,
	  sizeof (int) * gnum_block_compvar);

  for (i = 0; i < GpG.max_num_facts; i++)
    {

      /**
	 Copia degli istanti temporali dei fatti
	 **
	 Copying of the temporal instant of the fact
      **/
      if(vectlevel[l1]->fact[i].w_is_true>=1)
	{
	  vectlevel[level]->fact[i].time_f = vectlevel[l1]->fact[i].time_f;
	  vectlevel[level]->fact[i].action_f = vectlevel[l1]->fact[i].action_f;
	}
      else
	{
	  vectlevel[level]->fact[i].time_f=NOTIME;
	  vectlevel[level]->fact[i].action_f=NULL;
	}
      // insert a noop precond     
      if (vectlevel[l1]->fact[i].w_is_goal && CHECK_NOOP_POS (i, level))
	{
	  noop_pos = i;

#ifdef TEST_GR
	  if (CHECK_NOOP_POS (noop_pos, level) == 0)
	    {
	      MSG_ERROR (" noop_pos");
	      exit (1);
	    }
#endif

	  /**
	     La noop e il fatto sono precondizione
	     **
	     noop and fact are preconditions
	  **/
	  vectlevel[level]->noop_act[noop_pos].w_is_goal = TRUE;
	  vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (noop_pos)] |=
	    GUID_MASK (noop_pos);
	  vectlevel[level]->fact[i].w_is_goal = TRUE;
	}
      else
	vectlevel[level]->fact[i].w_is_goal = FALSE;

      /**
	 Se il fatto e' vero allora la noop e' inserita e il fatto al livello successivo e' supportato
	 **
	 If the fact is true then the noop is inserted and the fact at the successive level is supported 
      **/
      if (vectlevel[l1]->fact[i].w_is_true)
	{
	  noop_pos = i;

#ifdef __TEST__
	  if (!CHECK_NOOP_POS (noop_pos, l1))
	    {
	      MSG_ERROR (" noop_pos");
	      exit (1);
	    }
#endif

	  vectlevel[level]->noop_act[noop_pos].w_is_used = TRUE;

	  /**
	     Copia degli istanti temporali della noop e settiamo gli action_f
	     **
	     Copying of the temporal instants of the noop and setting of action_f
	  **/
	  if (GpG.temporal_plan)
	    {
	      vectlevel[level]->noop_act[noop_pos].time_f = vectlevel[l1]->fact[i].time_f;
	      
	      
	      //	      if (level > 0)
	      //		vectlevel[level]->fact[i].action_f = vectlevel[l1]->fact[i].action_f;
	      
	      vectlevel[level]->noop_act[noop_pos].action_f = vectlevel[l1]->fact[i].action_f;
	    }

	  vectlevel[level]->noop_act_vect[GUID_BLOCK (noop_pos)] |=
	    GUID_MASK (noop_pos);
	  vectlevel[level]->fact[i].w_is_true =
	    vectlevel[l1]->fact[i].w_is_true;
	  vectlevel[l1]->fact[i].w_is_true = TRUE;
	}

      else
	{
	  /**
	     Il fatto e' falso
	     **
	     The fact is false
	  **/
	  vectlevel[level]->fact[i].w_is_true = FALSE;
	  vectlevel[level]->noop_act[i].time_f = NOTIME;
	}
      vectlevel[level]->fact[i].w_is_used = FALSE;
      vectlevel[level]->fact[i].false_position = -1;

      if (GpG.derived_predicates) {
	vectlevel[level]->fact[i].w_is_derived_goal = 
	  vectlevel[l1]->fact[i].w_is_derived_goal;
	vectlevel[level]->fact[i].w_is_derived_true =
	  vectlevel[l1]->fact[i].w_is_derived_true;
      }

    }				/* end for sui fatti */

  // vectlevel[level]->action.false_position=-1;

  vectlevel[level]->num_prec = vectlevel[l1]->num_prec;
  vectlevel[level]->num_fact = vectlevel[l1]->num_fact;
  vectlevel[level]->num_true_crit = vectlevel[l1]->num_true_crit;
  vectlevel[level]->num_false_crit = vectlevel[l1]->num_false_crit;

  // Insert noops
  for (i = level; i < GpG.curr_plan_length; i++)
    {
      // insert noop at level i 
      for (j = 0; j < GpG.max_num_facts; j++)
	if (gft_conn[j].level == i && vectlevel[i + 1]->fact[j].w_is_goal)
	  backward_precond_propagation (&vectlevel[i + 1]->fact[j]);
    }

#ifdef __TEST___
  check_plan (GpG.curr_plan_length);
#endif
}



/***************************************
            PRECONDITION CHAIN
 ***************************************/

/**  OK 27-07-04
 * Name: insert_prec_act
 * Scopo:
 * Tipo: void
 * Input: ActNode_list infAction
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: insert_prec_act
*  Objective:
*  Type: void
*  Input: ActNode_list infAction
*  Output: 
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
void insert_prec_act (ActNode_list infAction)
{
  FctNode_list infEl;
  NoopNode_list infNoop = NULL;
  int el;
  EfConn *act;
  int level, j;


  /**
     Alcuni controlli aggiuntivi 
     **
     Some additive controls
  **/
  if (infAction->w_is_used <= 0 || infAction->w_is_goal > 0)
    return;
  level = *infAction->level;
  act = CONVERT_ACTION_TO_VERTEX (infAction->position);

#ifdef __TEST__
  printf ("\n Insert w_is_goal for action %s level %d",
	  print_op_name_string (infAction->position, temp_name), level);
#endif

  infAction->w_is_goal++;
  /**
     Aggiorno le precondizioni ed i bit array 
     **
     Updating the precondition and the bit array
  **/

  for (j = 0; j < gef_conn[act->position].num_PC; j++)
    {
      el = gef_conn[act->position].PC[j];
      if (el < 0)
	continue;

      if (CHECK_FACT_POS (el, level))
	{
	  // Points to the Node struct of the current fact 
	  infEl = CONVERT_FACT_TO_NODE (el, level);

	  if (infEl->w_is_goal <= 0)
	    {
	      vectlevel[level]->prec_vect[GUID_BLOCK (el)] |= GUID_MASK (el);

	      if (!infEl->w_is_true)	// Update the bit array of the false critical facts 
		vectlevel[level]->false_crit_vect[GUID_BLOCK (el)] |=
		  GUID_MASK (el);
	      else if (infEl->w_is_true == 1)	// Update the bit array of the false critical facts 
		vectlevel[level]->true_crit_vect[GUID_BLOCK (el)] |=
		  GUID_MASK (el);

	    }
	  infEl->w_is_goal++;
	  backward_precond_propagation (infEl);


	}
    }

  /**
     azioni durative
     **
     durative actions
  **/
  /**
     Precondizioni overall
     **
     Overall preconditions
  **/
  if (gef_conn[act->position].sf != NULL)
    {
      for (j = 0; j < gef_conn[act->position].sf->num_PC_overall; j++)
	{
	  el = gef_conn[act->position].sf->PC_overall[j];

	  if (el < 0)
	    continue;

	  if (CHECK_FACT_POS (el, level))
	    {
	      // Points to the Node struct of the current fact 
	      infEl = CONVERT_FACT_TO_NODE (el, level);

	      infNoop = CONVERT_NOOP_TO_NODE (el, level);

	      if (infNoop->w_is_overall != ADD_DEL
		  && infNoop->w_is_overall != ADD_NDEL)
		{
		  if (infEl->w_is_goal <= 0)
		    {
		      vectlevel[level]->prec_vect[GUID_BLOCK (el)] |=
			GUID_MASK (el);

		      if (!infNoop->w_is_true)	// Update the bit array of the false critical facts 
			vectlevel[level]->false_crit_vect[GUID_BLOCK (el)] |=
			  GUID_MASK (el);
		      else if (infEl->w_is_true == 1)	// Update the bit array of the false critical facts 
			vectlevel[level]->true_crit_vect[GUID_BLOCK (el)] |=
			  GUID_MASK (el);

		    }

		  infEl->w_is_goal++;
		  backward_precond_propagation (infEl);

		}
	    }

	}

      /**
	 Precondizioni at end
	 **
	 AT END precondition
      **/
      for (j = 0; j < gef_conn[act->position].sf->num_PC_end; j++)
	{
	  el = gef_conn[act->position].sf->PC_end[j];
	  if (el < 0)
	    continue;

	  // PREC_END FIX
	  //	  if (CHECK_FACT_POS (el, level + 1))
	  if (CHECK_FACT_POS (el, level ))
	    {
	      // Points to the Node struct of the current fact 
	      // PREC_END FIX
	      //	      infEl = CONVERT_FACT_TO_NODE (el, level + 1);

	      infEl = CONVERT_FACT_TO_NODE (el, level);
	      
	      if (infNoop->w_is_overall != ADD_DEL && infNoop->w_is_overall != ADD_NDEL)

		// PREC_END FIX
		/*
	      if (infNoop->w_is_overall != DEL_ADD && infNoop->w_is_overall != ADD_NDEL
	      && !is_fact_in_additive_effects (act->position, el))
		*/
		{
		  if (infEl->w_is_goal <= 0)
		    {
		      // PREC_END FIX
		      //		      vectlevel[level + 1]->prec_vect[GUID_BLOCK (el)] |= GUID_MASK (el);
		      vectlevel[level]->prec_vect[GUID_BLOCK (el)] |= GUID_MASK (el);

		      if (!infEl->w_is_true)	// Update the bit array of the false critical facts 
			// PREC_END FIX
			//			vectlevel[level + 1]->false_crit_vect[GUID_BLOCK (el)] |=  GUID_MASK (el);
			vectlevel[level]->false_crit_vect[GUID_BLOCK (el)] |=  GUID_MASK (el);

		      else if (infEl->w_is_true == 1)	// Update the bit array of the false critical facts 
			// PREC_END FIX
			//			vectlevel[level + 1]->true_crit_vect[GUID_BLOCK (el)] |=  GUID_MASK (el);
			vectlevel[level]->true_crit_vect[GUID_BLOCK (el)] |=  GUID_MASK (el);
		    }

		  infEl->w_is_goal++;
		  backward_precond_propagation (infEl);
		}

	    }
	}
    }
  /**
     end azioni durative
     **
     end of durative actions
  **/
}


/**  OK 27-07-04
 * Name: remove_prec_act
 * Scopo:
 * Tipo: void
 * Input: ActNode_list infAction
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: remove_prec_act
*  Objective:
*  Type: void
*  Input: ActNode_list infAction
*  Output: 
*  Main Data Structures:
*  Main Used Functions:
*  Call gives:
**/
void remove_prec_act (ActNode_list infAction)
{
  int i;

  /**
     Alcuni controlli aggiuntivi 
     **
     Some additive controls
  **/
  if (infAction->w_is_goal <= 0)
    return;

  if ( GpG.remove_actions_in_next_step ) {
    for (i = 0; i < ind_remove_act_chain_next_step; i++)
      if (remove_act_chain_next_step[i] == infAction)
	break;

    if (i == ind_remove_act_chain_next_step)
      {
	remove_act_chain_next_step[ind_remove_act_chain_next_step] = infAction;
	ind_remove_act_chain_next_step++;
	
	//      printf("\nInserisco azione in remove_act_chain_next_step: %s a livello %d", print_op_name_string(infAction->position,temp_name), *infAction->level);
	
	if (ind_remove_act_chain_next_step >= MAX_PLAN_LENGTH) {
#ifdef __MY_OUTPUT__
	  MSG_ERROR( WAR_MAX_PLAN_LENGTH );
#else
	  printf( WAR_MAX_PLAN_LENGTH );
#endif    
	  exit (1);
	}
      }
  }
  else {
    for (i = 0; i < ind_remove_act_chain; i++)
      if (remove_act_chain[i] == infAction)
	break;

  if (i == ind_remove_act_chain)
    {
      remove_act_chain[ind_remove_act_chain] = infAction;
      ind_remove_act_chain++;

      if (ind_remove_act_chain >= MAX_PLAN_LENGTH) {
#ifdef __MY_OUTPUT__
	MSG_ERROR( WAR_MAX_PLAN_LENGTH );
#else
 	printf( WAR_MAX_PLAN_LENGTH );
#endif    
	exit (1);
      }
    }
  }

  infAction->w_is_goal--;
 
}





/***************************************
            NOOP CHAIN
 ***************************************/



/**  OK 20-07-04
 * Name: noop_add_not_in_add
 * Scopo: inserisce la posizione di una noop mutuamente esclusiva con un'azione (act) nella 
 *        lista delle noop mutuamente esclusive per la propagazione in avanti
 * Tipo: void
 * Input: inform *act
 *        unsigned int pos
 * Output: nessuno
 * Strutture dati principali: noop_not_in
 *                            inform
 *                            noop_free_list
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: forward_noop_propagation
 *              remove_noop
**
*  Name:  noop_add_not_in_add
*  Objective: it inserts the position of one noop mutually exclusive with an action (act) in
*             list of the noop mutually exclusive for the propagation in ahead
*  Type:  void
*  Input: inform * act
*         unsigned int pos
*  Output: noone
*  Main Data Structures: noop_not_in
*                        inform
*                        noop_free_list
*  Main Used Functions:  none
*  Call gives: forward_noop_propagation
*              remove_noop
**/
void noop_add_not_in_add (ActNode_list act, unsigned int pos)
{
  /** 
    new è di tipo noop_not_in che è una struttura che contiene la posizione di una noop mutuamente 
    esclusiva con una azione 
  **
    new is noop_not_in type that is a structure that contains the position of one mutually noop
    exclusive with one action
  **/
  noop_not_in *new;

  /** 
    se la lista degli elementi liberi e' vuota alloco nuovo spazio altrimenti prendo il primo della 
    lista 
  **
    if the list of the free elements is empty I set new space otherwise I take the first one of
    list
  **/
  if (noop_free_list == NULL)
    new = (noop_not_in *) calloc (1, sizeof (noop_not_in));

  else
    {
      new = noop_free_list;
      noop_free_list = noop_free_list->next;
    }
  /** 
    associamo a position il valore pos passato in ingresso corrispondente alla posizione della noop
  **
    we associate to position the value pos passed in income correspondent to the position of the noop
  **/
  new->position = pos;
  /** 
    se la lista delle noop act->add e' vuota anche la lista new sara' vuota 
    **
    if the list of noop act->add is empty then also the list new will be empty
  **/
  if (act->add == NULL)		//init list
    new->next = NULL;

  else
    /** 
      nel caso che la lista act->add non e' vuota la pongo a new->next 
    **
      in the case that the list act->add is not empty I set it to new->next
    **/
    new->next = act->add;	//update list
  /** 
    associo a new la lista delle noop mutuamente esclusive con l'azione act->add uguale a new 
  **
    I associate to new the list of the noop mutually exclusive with the action act->add equal to new
  **/
  act->add = new;

#ifdef __TEST__
  if (DEBUG3)
    {
      printf ("\n\n Insert noop_add_not_in_add  ");
      print_noop_name_string (pos, temp_name);
      printf (" action  ");
      print_op_name (act->position);
      printf (" time %d", *act->level);
    }

#endif
}


/** OK 22-07-04
 * Name: noop_prec_not_in_add
 * Scopo: inserisce la posizione di una noop mutuamente esclusiva con una azione nella lista delle 
 *        noop non inserite per la propagazione all'indietro
 * Tipo: void
 * Input: inform *act
 *        unsigned int pos
 * Output: nessuno
 * Strutture dati principali: noop_not_in
 *                            inform
 *                            noop_free_list
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: backward_precond_propagation
 *              remove_backward_noop_chain
**
*  Name:  noop_prec_not_in_add
*  Objective: inserts the position of one noop mutually exclusive with one action in the list of
*         noop not inserted for the propagation to behind
*  Type: void
*  Input: inform * act
* unsigned int pos
*  Output: none
*  Main Data Structures: noop_not_in
*                        inform
*                        noop_free_list
*  Main Used Functions:  none
*  Call gives:  backward_precond_propagation
* remove_backward_noop_chain
**/
void noop_prec_not_in_add (ActNode_list act, unsigned int pos)
{
  noop_not_in *new;

  /** 
    se la lista degli elementi liberi e' vuota alloco nuovo spazio altrimenti prendo il primo 
    della lista 
  **
    if the list of the free elements is empty I set new space otherwise I take the first one
    of the list
  **/
  if (noop_free_list == NULL)
    new = (noop_not_in *) calloc (1, sizeof (noop_not_in));

  else
    {
      new = noop_free_list;
      noop_free_list = noop_free_list->next;
    }
  /** 
    associamo a position il valore pos passato in ingresso corrispondente alla posizione della noop 
  **
    we associate to position the value pos passed in input correspondent to the position of the noop
  **/
  new->position = pos;
  /** 
    se la lista delle noop mutuamente esclusive act->preco e' vuota allora anche la lista new sara' 
    vuota 
  **
    if the list of the noop mutually exclusive act->preco is empty then also the list new will be
    empty
  **/
  if (act->preco == NULL)	//initlist
    new->next = NULL;

  else
    new->next = act->preco;	//update list
  /** 
    assegno a act->preco la lista new 
  **
    I assign to act->preco the list new
  **/
  act->preco = new;
}


/** OK 22/07/04
 * Name: free_noop_not_in
 * Scopo: cancella le liste delle noop non inserite dell'azione perchè mutuamente esclusive 
 *        con questa
 * Tipo: void
 * Input: inform *act
 * Output: nessuno
 * Strutture dati principali: noop_not_in
 *                            inform
 *                            noop_free_list
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: check_prec_add_list
 *              reset_plan
**
*  Name: free_noop_not_in
*  Objective: it cancels perch?mutuamente exclusive the not inserted lists of the noop of the action
*         with this
*  Type: void
*  Input: inform * act
*  Output: none
*  Main Data Structure: noop_not_in
*                       inform
*                       noop_free_list
*  Main Used functions:  none
*  Call gives: check_prec_add_list
*              reset_plan
**/
void free_noop_not_in (ActNode_list act)
{
  /** 
    temp e temp_noop sono liste di appoggio 
    **
    temp and temp_noop are support lists
  **/
  register noop_not_in *temp;
  noop_not_in *temp_noop;
  temp_noop = noop_free_list;
  temp = noop_free_list = act->preco;

  /**
     NOOP non inserite per le precondizioni
     **
     NOOP not inserted for the preconditions
  **/
  /** 
    se la lista act->preco (lista di noop per la propagazione all'indietro) non e' vuota 
  **
    if the list act->preco (list of noop for the propagation to the behind) is not empty
  **/
  while (act->preco != NULL)
    {
      temp = act->preco;
      act->preco = act->preco->next;
    }
  if (temp != NULL)
    temp->next = act->add;

  /** 
    se la lista act->add (lista di noop per la propagazione in avanti) non e' vuota 
  **
    if the list act->add (list of noop for the propagation in ahead) is not empty
  **/
  /**
     NOOP non inserite per gli effetti addititvi
     **
     NOOP not inserted for the additive effects
  **/
  while (act->add != NULL)
    {
      temp = act->add;
      act->add = act->add->next;
    }
  if (temp != NULL)
    temp->next = act->treated;

  /** 
    NOOP non inserite per mutua esclusione
  **
    NOOP not inserted for the mutual exclusion
  **/
  while (act->treated != NULL)
    {
      temp = act->treated;
      act->treated = act->treated->next;
    }
  if (temp != NULL)
    temp->next = temp_noop;
}


/** OK 22/07/04
 * Name: forward_noop_propagation
 * Scopo: propaga in avanti le noop fino quando non sono ME con una azione, e in tale caso aggiorna 
 *        le lista delle noop non inserite
 * Tipo: void
 * Input: int position_fact (intero corrispondente alla posizione del fatto)
 *        int curr_level (intero corrispondente al livello)
 * Output: nessuno
 * Strutture dati principali: inf_noop
 *                            vectlevel
 *                            geff_conn
 *                            remove_act_chain
 *                            GpG
 * Funzioni principali utilizzate: is_fact_in_additive_effects_start
 *                                 is_fact_in_preconditions
 *                                 is_fact_in_preconditions_overall
 *                                 insert_propagation_list
 * Chiamata da: check_prec_add_list
 *              forward_noop_remotion_time
 *              insert_time
 *              initialize
 *              propagation_time
**
*  Name:  forward_noop_propagation
*  Objective: It propagates in ahead the noop until are not ME with an action, and in that case it dawns
*             the list of the noop not inserted
*  Type: void
*  Input: int position_fact (entire correspondent to the position of the fact)
*         int curr_level (entire correspondent to the level)
*  Output: none
*  Main Data Structures: inf_noop
*                        vectlevel
*                        geff_conn
*                        remove_act_chain
*                        GpG
*  Main Used Functions: is_fact_in_additive_effects_start
*                       is_fact_in_preconditions
*                       is_fact_in_preconditions_overall
*                       insert_propagation_list
*  Call gives: check_prec_add_list
*              forward_noop_remotion_time
*              insert_time
*              initialize
*              propagation_time
**/
void forward_noop_propagation (int position_fact, int curr_level)
{
  /** 
    position_noop corrisponde alla posizione della noop
    position_me_action intero utilizzato per osservare la mutua esclusione tra una noop durativa e l'azione 
    *infnoop puntatore inform per la noop 
  **
    position_noop corresponds to the position of the noop
    position_me_action integer used to observe the mutual exclusion between a durative noop and the action
    *infnoop gunlayer inform for the noop
  **/
  int position_noop, position_me_action, i, cel;
  short save_action;
  NoopNode_list infnoop;

  /** 
    Se il livello curr_level è maggiore della lunghezza del piano esce 
  **
    If the level curr_level is greater than the length of the plan it exits
  **/
  if (gft_conn[position_fact].fact_type == IS_DERIVED)
    return;

  if (curr_level >= GpG.curr_plan_length)
    return;
  position_noop = position_fact;
  /** 
    la posizione della noop del livello curr_level corrisponde a quella del fatto 
  **
    the position of the noop of the curr_level level is the same of that one of the fact
  **/
  infnoop = &vectlevel[curr_level]->noop_act[position_fact];
  /** 
    trova le posizioni della noop, del fatto passato, dell'azione me con la noop (se c'è) e il livello 
  **
    it finds the positions of the noop, the past fact, the action me with the noop (if c '?  and the level
  **/
  /** 
    se la noop è inserita esce 
  **
    if the noop is inserted it exits
  **/
  if (infnoop->w_is_used)
    return;
  /** 
    position_me_action e' la posizione dell'azione (al livello curr_level) mutuamente esclusiva con la noop 
    durativa -1 se non c'e' mutex 
  **
    position_me_action is the position of the action (to the level curr_level) mutually exclusive with the noop
    durative -1 if there is not mutex
  **/
  position_me_action = check_mutex_noop_durative (position_noop, curr_level);

  /** 
    se c'è me tra l'azione e la noop aggiorna la lista e esce 
  **
    if there is me between the action and the noop it updates the list and exits
  **/
  if (position_me_action != -1)
    {
      /** 
	inserisce la posizione di una noop nella lista delle noop non inserite per la propagazione in avanti 
	**
	it inserts the position of one noop in the list of the noop not inserted for the propagation in ahead
      **/
      if (vectlevel[curr_level]->noop_act[position_fact].w_is_overall == 0)
	noop_add_not_in_add (&vectlevel[curr_level]->action, position_noop);

      /**
	 aggiorna LM in caso di mutex
	 **
	 It updates LM in case of mutex
      **/
      if (GpG.lm_multilevel)
	update_mutex_multilevel (curr_level,position_me_action); 
      else 
	update_mutex(position_me_action);
      
      return;
    }
  
  /** 
    non c'è me e quindi inserisce noop,propaga fatto e continua 
    **
    there is not me and thene it inserts noop, propagates the fact and continues
  **/
  vectlevel[curr_level]->noop_act[position_noop].w_is_used++;

  /** 
    pone a 1 il bit nel act_vect, relativo alla noop inserita 
    **
    set to 1 the bit in the act_vect, relative to the noop inserted
  **/
  vectlevel[curr_level]->noop_act_vect[GUID_BLOCK (position_noop)] |=
    GUID_MASK (position_noop);

  /** 
    C'e' un effetto additivo che rende supportato il fatto per cui non propago 
    **
    There is an additive effect that renders supported the fact for which i don't propagate
  **/
  if (vectlevel[curr_level]->noop_act[position_noop].w_is_overall ==
      NADD_DEL
      || vectlevel[curr_level]->noop_act[position_noop].w_is_overall ==
      ADD_DEL)
    return;

  /**
    Ciclo che agisce come prima per la propagazione delle noop. Si ferma quando c'è una ME o quando 
    raggiunge il numero massimo di livelli 
  **
    Cycle that acts like before for the propagation of the noop. It stop when there is a ME or when
    it catches up the maximum number of levels
  **/
  while (curr_level < GpG.curr_plan_length)
    {
      /** 
	livello successivo 
	**
	successive level
      **/
      cri_update_for_fact(position_fact, curr_level);

      curr_level++;
      vectlevel[curr_level]->fact[position_fact].w_is_true++;
      /** 
	se l'azione al livello curr_level serve solo per rendere vero un fatto che è già vero la eliminiamo 
      **
	if the action to the level curr_level needs only to make true a fact that is already true we eliminate it
      **/
      if (vectlevel[curr_level]->fact[position_fact].w_is_true >= 2 
	  && CHECK_ACTION_OF_LEVEL (curr_level-1)) {

	// controlliamo che l'azione serva solo per rendere vero questo fatto
	// e in tal caso la eliminiamo
	save_action = FALSE;
	
	/** 
	  effetti additivi at-end 
	**
	  additive effects at-end
	**/
	for (i = 0;i <gef_conn[vectlevel[curr_level - 1]->action.position].num_A;i++){
	  cel = gef_conn[vectlevel[curr_level - 1]->action.position].A[i];
	  if (cel < 0) {
	    /** 
	      se ci sono effetti numerici tengo l'azione 
	    **
	      if there are numerical effects I hold the action
	    **/
	    save_action = TRUE;
	    break;
	  }
	  
	  if (cel == position_fact)
	    continue;
	  
	  /** 
	    se il numero di azioni di cui è precondizione nei livelli superiori è maggiore di 1 ed è 
	    precondizione dell'azione al livello curr_level allora save_action=TRUE 
	    **
	    if the number of actions of which is precondition in the supèerior levels is greater than 1 and is
	    precondition of the action to the level curr_level then save_action=TRUE
	  **/
	  if (vectlevel[curr_level]->fact[cel].w_is_goal >= 1 && vectlevel[curr_level]->fact[cel].w_is_true == 1) {
	    save_action = TRUE;
	    break;
	  }
	}
	
	/** 
	  effetti additivi at-start per azioni durative 
	  **
	  additive effects at-start for durative actions
	**/
	if (gef_conn[vectlevel[curr_level - 1]->action.position].sf != NULL) {
	  for (i = 0;i <gef_conn[vectlevel[curr_level - 1]->action.position].sf->num_A_start; i++) {
	    cel = gef_conn[vectlevel[curr_level - 1]->action.position].sf->A_start[i];
	    if (cel < 0){
	      save_action = TRUE;
	      break;
	    }
	    
	    /** 
	      se il fatto è negli effetti cancellanti del livello precedente continuo
	      **
	      if the fact is in the cancelling effects of the previous level i continue
	    **/
	    if (is_fact_in_delete_effects(GET_ACTION_POSITION_OF_LEVEL (curr_level - 1), cel))
	      continue;

	    if (cel == position_fact)
	      continue;
	    
	    /** 
	      se il numero di azioni di cui è precondizione nei livelli superiori è maggiore di 1 ed è 
	      precondizione dell'azione al livello curr_level allora save_action=TRUE 
	      **
	      if the number of actions of which?precondizione in the advanced levels?maggiore of 1 and
	      precondition of the action to the level curr_level then save_action=TRUE
	    **/
	    if (vectlevel[curr_level]->fact[cel].w_is_goal >= 1 && vectlevel[curr_level]->fact[cel].w_is_true == 1) {
	      save_action = TRUE;
	      break;
	    }
	  }
	}
	
	/** 
	  rimozione dell'azione al livello curr_level-1 se è inutile (save_action=FALSE) 
	**
	  removal of the action to the level curr_level-1 if is not useful (save_action=FALSE)
	**/
	if (save_action == FALSE) {
	  if ( GpG.remove_actions_in_next_step )
	    {
	      for (i = 0; i < ind_remove_act_chain_next_step; i++)
		if (remove_act_chain_next_step[i] == &vectlevel[curr_level - 1]->action)
		  break;
	      if (i == ind_remove_act_chain_next_step) {
		remove_act_chain_next_step[ind_remove_act_chain_next_step] =
		  &vectlevel[curr_level - 1]->action;
		ind_remove_act_chain_next_step++;
		
		//	    printf("\nInserisco azione in remove_act_chain_next_step: %s a livello %d", print_op_name_string(vectlevel[curr_level - 1]->action.position,temp_name),curr_level - 1 );
		
		if (ind_remove_act_chain_next_step >= MAX_PLAN_LENGTH) {
#ifdef __MY_OUTPUT__
		  MSG_ERROR ( WAR_MAX_PLAN_LENGTH );
#else
		  printf( WAR_MAX_PLAN_LENGTH );
#endif    
		  exit (1);
		}
		
	      }
	    }
	  else
	    {
	      for (i = 0; i < ind_remove_act_chain; i++)
		if (remove_act_chain[i] == &vectlevel[curr_level - 1]->action)
		  break;
	      if (i == ind_remove_act_chain) {
		remove_act_chain[ind_remove_act_chain] =
		  &vectlevel[curr_level - 1]->action;
		ind_remove_act_chain++;
		
		
		if (ind_remove_act_chain >= MAX_PLAN_LENGTH) {
#ifdef __MY_OUTPUT__
		  MSG_ERROR ( WAR_MAX_PLAN_LENGTH );
#else
		  printf( WAR_MAX_PLAN_LENGTH );
#endif    
		  exit (1);
		}
		
	      }
	    }
	}
      }

      /** 
	Aggiornamento dei predicati derivati 
      **
	Updating of the derived predicates
      **/
      calc_new_derived_predicates(position_fact, curr_level, ADD_FACT, NULL);
      // Update the fact vect with the added effect of the inserted action
      // fact_vect is a negated bit array
      vectlevel[curr_level]->fact_vect[GUID_BLOCK (position_fact)] |= GUID_MASK (position_fact);
      vectlevel[curr_level]->false_crit_vect[GUID_BLOCK (position_fact)] &=
	~(GUID_MASK (position_fact));
      if (vectlevel[curr_level]->fact[position_fact].w_is_goal)
	{
	  if (vectlevel[curr_level]->fact[position_fact].w_is_true == 1)
	    vectlevel[curr_level]->
	      true_crit_vect[GUID_BLOCK (position_fact)] |=
	      GUID_MASK (position_fact);

	  else if (vectlevel[curr_level]->fact[position_fact].w_is_true > 1)
	    vectlevel[curr_level]->
	      true_crit_vect[GUID_BLOCK (position_fact)] &=
	      ~(GUID_MASK (position_fact));
	}

      /** 
	Controllo se il fatto era falso e ora non lo e' piu' 
      **
	Control if the fact were false and now it is not
      **/
      if (vectlevel[curr_level]->fact[position_fact].false_position >= 0)
	remove_false_fact (&vectlevel[curr_level]->fact[position_fact]);

      /** 
	Aumentiamo il numero di fatti veri nel livello curr_level 
      **
	We increase the number of true facts in the level curr_level
      **/
      vectlevel[curr_level]->num_fact++;
      if (curr_level >= GpG.curr_plan_length
	  || vectlevel[curr_level]->noop_act[position_noop].w_is_used)
	return;
      /** 
	Aggiorniamo position_me_action con il nuovo livello curr_level 
	**
	We update position_me_action with the new level curr_level
      **/
      position_me_action =
	check_mutex_noop_durative (position_noop, curr_level);

      /** 
	si entra nell'if se la noop è me con una azione e se il fatto al livello dopo non è già vero.
	**
	it enter in the if if the noop is me with one action and if the fact to the level sucessive is not already true
      **/
      if (position_me_action != -1)
	{
	  if (vectlevel[curr_level]->noop_act[position_fact].w_is_overall ==
	      0)
	    /** 
	      inserisce la posizione di una noop nella lista delle noop non inserite per 
	      gli effetti additivi 
            **
	      it inserts the position of one noop in the list of the noop not inserted for
	      the additive effects
	    **/
	    noop_add_not_in_add (&vectlevel[curr_level]->action,
				 position_noop);
	  /**
	     aggiorna LM in caso di mutex
	     **
	     It updates LM in case of mutex
	  **/
	  if (GpG.lm_multilevel) 
            update_mutex_multilevel (curr_level,position_me_action); 
	  else 
            update_mutex(position_me_action);
	  

	  return;
	}
      vectlevel[curr_level]->noop_act[position_noop].w_is_used++;

      /** 
	pone a 1 il bit nel act_vect, relativo alla noop inserita 
	**
	set to 1 the bit in the act_vect, relative to the noop inserted
      **/
      vectlevel[curr_level]->noop_act_vect[GUID_BLOCK (position_noop)] |=
	GUID_MASK (position_noop);

      /** 
	C'e' un effetto del end per cui non propago 
	**
	There is an effect del end for which i don't propagate
      **/
      if (vectlevel[curr_level]->noop_act[position_noop].w_is_overall ==
	  NADD_DEL
	  || vectlevel[curr_level]->noop_act[position_noop].w_is_overall ==
	  ADD_DEL)
	return;
    }

}


/** OK 22-07-04
 * Name: forward_noop_remotion
 * Scopo: rimuovere la noop relativa ad un fatto ad un dato livello dal piano
 * Tipo: int
 * Input: int position_fact (intero corrispondente alla posizione del fatto)
 *        int curr_level (intero corrispondente al livello)
 * Output: nessuno
 * Strutture dati principali: inf_noop
 *                            vectlevel
 *                            GpG
 * Funzioni principali utilizzate: forward_noop_remotion_time
 *                                 insert_unsup_fact
 * Chiamata da: remove_action_from_vectlevel
 *              remove_noop
 *              insert_action_in_vectlevel
**
*  Name: forward_noop_remotion
*  Objective: to remove noop relative to a fact to a data the level from the plan
*  Type: int
*  Input: int position_fact (entire correspondent to the position of the fact)
*         int curr_level (entire correspondent to the level)
*  Output: none
*  Main Data Structures: inf_noop
*                        vectlevel
*                        GpG
*  Main Used Functions: forward_noop_remotion_time
*                       insert_unsup_fact
*  Call gives: remove_action_from_vectlevel
*              remove_noop
*              insert_action_in_vectlevel
 **/
/* propaga in avanti le noop fino quando non sono ME con una azione, e in tale caso aggiorna le lista delle noop non inserite */
int forward_noop_remotion (int position_fact, int curr_level)
{
  /** 
    position_noop corrisponde alla posizione della noop
    *infnoop puntatore inform che corrisponde alla noop(*infnoop) e il fatto(*fact) 
  **
    position_noop corresponds to the position of the noop
    *infnoop inform pointer that corresponds to the noop(*infnoop) and the fatto(*fact)
  **/ 
  int position_noop;
  NoopNode_list infnoop;
  FctNode_list fact;

  /** 
    Se il livello è maggiore della lunghezza totale del piano in esame esce restituendo 0 
    **
    If the level is greater than the total length of the plan in examination exits giving back 0
  **/
  if (curr_level < GpG.curr_plan_length)
    {
      /** 
	Assegniamo alla posizione della noop quella del fatto passata in ingresso 
      **
	We assign to the position of the noop that one of the last fact in input
      **/
      position_noop = position_fact;
      /** 
	Dato il livello e la posizione otteniamo il fatto 
	**
	Given the level and the position we obtain the fact
      **/
      fact = CONVERT_FACT_TO_NODE (position_fact, curr_level);
      /** 
	Dalla posizione del fatto (o noop) nella struttura vectlevel otteniamo la nostra noop 
	in forma inform (contenente tutte le caratteristiche della noop) 
	**
	From the position of the fact (or noop) in the structure vectlevel we obtain ours noop
	in shape inform (containing all the characteristics of the noop)
      **/ 
      infnoop = &vectlevel[curr_level]->noop_act[position_fact];
      /** 
	The position of fact and the position of noop are the same 
	**
	The position of fact and the position of noop are the same
      **/
      /** 
	se non c'è la sua noop successiva non c'è niente da rimuovere!
	**
	if there is not its successive noop there are nothing to remove!
      **/
      /** 
	Se la noop non è inserita esce e retituisce 0 
	**
	If the noop is not inserted it exit and give back 0
      **/
      if (infnoop->w_is_used <= 0)
	return (0);
      if (GpG.temporal_plan && GpG.forward_time)
	forward_noop_remotion_time (infnoop);
      /** 
	Ciclo che va dal livello corrente (curr_level) fino alla fine del piano 
	**
	Cycle that goes from the current level (curr_level) until the end of the plan
      **/
      while (curr_level < GpG.curr_plan_length)
	{
	  /** 
	    C'e' un effetto ADD START per cui non cancello la noop 
	    **
	    There is an ADD START effect for which I not delete the noop
	  **/
	  if (vectlevel[curr_level]->noop_act[position_noop].w_is_overall ==
	      ADD_DEL
	      || vectlevel[curr_level]->noop_act[position_noop].
	      w_is_overall == ADD_NDEL)
	    return (0);

	  /** 
	    rimuovo la noop 
	    **
	    I remove the noop
	  **/
	  vectlevel[curr_level]->noop_act[position_noop].w_is_used--;
	  if (vectlevel[curr_level]->noop_act[position_noop].w_is_used <= 0)
	    vectlevel[curr_level]->
	      noop_act_vect[GUID_BLOCK (position_noop)] &=
	      ~(GUID_MASK (position_noop));

	  /** 
	    C'e' un effetto DEL END per cui non propago 
	    **
	    There is a DEL END effect for which I propagate
	  **/
	  if (vectlevel[curr_level]->noop_act[position_noop].w_is_overall ==
	      NADD_DEL)
	    return (0);

	  /** 
	    salgo di livello 
	    **
	    I go up of level
	  **/
	  curr_level++;

	  /** 
	    se il fatto a questo livello è supportato da una sola azione allora questa è 
	    la mia noop e proseguo nella catena di rimozione 
	  **
	    if the fact to this level is supported by one single action then this is
	    mine noop and I continue in the removal chain
	  **/
	  /** 
	    se al contrario è supportato da almeno un'altra azione allora decremento 
	    w_is_true ed esco 
	  **
	    if to the contrary is supported from at least an other action then decrement
	    w_is_true and I exit
	  **/
	  vectlevel[curr_level]->fact[position_fact].w_is_true--;
	  if (vectlevel[curr_level]->fact[position_fact].w_is_true == 1)
	    {

	      /**
		inserisco tru_crit_vect
	      **
		I insert tru_crit_vect
	      **/
	      if (vectlevel[curr_level]->fact[position_fact].w_is_goal)
		vectlevel[curr_level]->
		  true_crit_vect[GUID_BLOCK (position_fact)] |=
		  (GUID_MASK (position_fact));
	    }
	  if (vectlevel[curr_level]->fact[position_fact].w_is_true > 0)
	    return (0);

	  else
	    {
	      /** 
		aggiorno i predicati derivati
		**
		I update the derivates predicates
	      **/
	      calc_new_derived_predicates(position_fact, curr_level, DEL_FACT, NULL);
	      /**
		posso rimuovere il fatto dal bit_vector
	      **
		I can remove the fact from the bit_vector
	      **/
	      vectlevel[curr_level]->fact_vect[GUID_BLOCK (position_fact)] &=
		~(GUID_MASK (position_fact));
	      vectlevel[curr_level]->num_fact--;
	      vectlevel[curr_level]->
		true_crit_vect[GUID_BLOCK (position_fact)] &=
		~(GUID_MASK (position_fact));
	      if (vectlevel[curr_level]->fact[position_fact].w_is_used)
		insert_unsup_fact (&vectlevel[curr_level]->
				   fact[position_fact]);
	      if (vectlevel[curr_level]->fact[position_fact].w_is_goal > 0)
		{
		  vectlevel[curr_level]->
		    false_crit_vect[GUID_BLOCK (position_fact)] |=
		    GUID_MASK (position_fact);
		}
	    }

	  /** 
	    se la noop non è inserita esco 
	  **
	    if the noop is inserted I exit
	  **/
	  if (vectlevel[curr_level]->noop_act[position_noop].w_is_used == 0)
	    return (0);
	}
    }

  return (0);
}


/** OK 22-07-04
 * Name: remove_noop
 * Scopo: rimuovere solo la NOOP del livello e eventualmente quelle dei livelli successivi 
 *        con forward_noop_remotion
 * Tipo: int
 * Input: inform *act (tipo inform contenente le informazioni relative all'azione)
 *        unsigned int pos (posizione dell'azione)
 * Output: nessuno
 * Strutture dati principali: vectlevel
 *                            GpG
 *                            inform
 * Funzioni principali utilizzate: forward_noop_remotion
 *                                 noop_remotion_time
 *                                 noop_add_not_in_add
 *                                 insert_unsup_fact
 * Chiamata da: insert_action_in_vectlevel
**
*  Name: remove_noop
*  Objective: to eventually remove only the NOOP of the level and those of the levels succeeded to you
*             with forward_noop_remotion
*  Type: int
*  Input: inform * act (containing type inform the relative information to the action)
*         unsigned int pos (position of the action)
*  Output: none
*  Main Data Structure: vectlevel
*                       GpG
*                       inform
*  Main Used Functions: forward_noop_remotion
*                       noop_remotion_time
*                       noop_add_not_in_add
*                       insert_unsup_fact
*  Call gives: insert_action_in_vectlevel
 **/
int remove_noop (ActNode_list act, unsigned int pos)
{
  /**
    act e' l'inform dell'azione e pos e' la posizione della noop me con l'azione
    **
    act is the inform of the action and pos is the position of the noop me with the action
  **/

  /** 
    fact relativo al fatto supportato dalla noop
    curr_level intero che corrisponde ad un livello del piano
    **
    fact relative to the fact supported from the noop
    curr_level integer that corresponde to a level of the plan
  **/
  FctNode_list fact;		//inform del fatto supportato dalla noop
  int curr_level;
  unsigned int f_uid_block, f_uid_mask;

  /** 
    assegnamo a curr_level il livello a cui è collocata l'azione act 
    **
    we assign to curr_level the level to which is collocated the action act
  **/
  curr_level = *act->level;

  /** 
    toglie la noop dalla catena al livello curr_level 
    **
    it removes the noop from the chain to the level curr_level
  **/
  vectlevel[curr_level]->noop_act[pos].w_is_used--;
  vectlevel[curr_level]->noop_act_vect[GUID_BLOCK (pos)] &=
    ~(GUID_MASK (pos));

  /** 
    mettiamo la noop nella lista delle noop rimosse dell'azione 
    **
    we put the noop in the list of the noop removed of the action
  **/
  noop_add_not_in_add (act, pos);

  /** 
    ottengo l'inform del fatto generato dalla noop 
    **
    I obtain the inform of the fact generated from the noop
  **/
  fact = &vectlevel[curr_level + 1]->fact[pos];

  /** 
    decremento w_is_true del fatto (corrispondente al numero di azioni che supportano il fatto) 
    **
    I decrement w_is_true of the fact (correspondent to the number of actions that support the fact)
  **/
  fact->w_is_true--;
  if (GpG.temporal_plan)
    noop_remotion_time (&vectlevel[curr_level]->noop_act[pos]);

  /** 
    se il fatto è falso faccio la sua rimozione e la rimozione della catena delle noop, 
    se no niente 
    **
    if the fact is false I make its removal and the removal of the chain of the noop,
    if not nothing
  **/
  if (fact->w_is_true == 0)
    {
      f_uid_block = GUID_BLOCK (pos);
      f_uid_mask = GUID_MASK (pos);
      /**
	Aggiorno i predicati derivati con la rimozione del fatto
	**
	I update the derivates predicates with the removal of the fact
      **/
      calc_new_derived_predicates(pos, curr_level + 1, DEL_FACT, NULL);
      vectlevel[curr_level + 1]->fact_vect[f_uid_block] &= ~(f_uid_mask);
      vectlevel[curr_level + 1]->true_crit_vect[f_uid_block] &= ~f_uid_mask;
      if (fact->w_is_goal <= 0)
	vectlevel[curr_level + 1]->false_crit_vect[f_uid_block] &=
	  ~f_uid_mask;

      else
	vectlevel[curr_level + 1]->false_crit_vect[f_uid_block] |= f_uid_mask;
      vectlevel[curr_level + 1]->num_fact--;

#ifdef __TEST__
      printf ("\n Remove noop: %s lev %d",
	      print_noop_name_string (pos, temp_name), curr_level);
#endif
      
      /** 
	se il fatto è precondizione di una azione al medesimo livello 
	**
	if the fact is precondition of one action to the same level
      **/
      if (fact->w_is_used)
	insert_unsup_fact (&vectlevel[curr_level + 1]->fact[pos]);
      /** 
	rimozione della noop nei livelli successivi 
	**
	removal of the noop in the successive levels
      **/
      forward_noop_remotion (pos, curr_level + 1);
  
    }
  
  else if (fact->w_is_true == 1)
    {
      f_uid_block = GUID_BLOCK (pos);
      f_uid_mask = GUID_MASK (pos);
      vectlevel[curr_level + 1]->false_crit_vect[f_uid_block] &= ~f_uid_mask;
      if (fact->w_is_goal > 0)
	vectlevel[curr_level + 1]->true_crit_vect[f_uid_block] |= f_uid_mask;
    }

  if (GpG.temporal_plan)
    /** 
      E' settato da noop_remotion_time e indica se il tempo di noop dei livelli successivi 
      deve essere rimosso 
      **
      It is set by noop_remotion_time and indicates if the time of noop of the successive levels
      must be removed
    **/
    GpG.forward_time = 1;
  return (0);
}


/** OK 22-07-04
 * Name: remove_backward_noop_chain
 * Scopo: rimuovere la catena informativa partendo da una NOOP che e' stata minacciata
 * Tipo: void
 * Input: inform *act (tipo inform contenente le informazioni relative all'azione)
 *        int noop_pos (posizione della noop)
 * Output: nessuno
 * Strutture dati principali: vectlevel
 *                            geff_con
 *                            inform
 * Funzioni principali utilizzate: noop_prec_not_in_add
 *                                 action_eff_cost
 *                                 is_fact_in_delete_effects
 * Chiamata da: insert_action_in_vectlevel
**
*  Name: remove_backward_noop_chain
*  Objective: to remove the informative chain leaving from one NOOP that is been threatened
*  Type: void
*  Input: inform *act (containing type inform the relative information to the action)
*         int noop_pos (position of the noop)
*  Output: none
*  Main Data Structures: vectlevel
*                        geff_con
*                        inform
*  Main Used Functions: noop_prec_not_in_add
*                       action_eff_cost
*                       is_fact_in_delete_effects
*  Call gives: insert_action_in_vectlevel
**/
/* Rimuove la catena informativa partendo da una NOOP che e' stata minacciata */
void remove_backward_noop_chain (ActNode_list act, int noop_pos)
{
  register NoopNode_list noop;
  register FctNode_list fact;
  /** 
    int level intero corrispondente al livello
    int fact_pos intero corrispondente alla posizione della noop 
    **
    int level integer correspondent to the level
    int fact_pos integer correspondent to the position of the noop
  **/
  int level, fact_pos, j;
  /** 
    unsigned int interi utilizzati come appoggio 
    **
    unsigned int integer used like support
  **/
  unsigned int uid_block, uid_mask, fact_uid_block, fact_uid_mask;
  int el;
  ActNode_list inf_act;
  /** 
    Associo a level il livello dell'azione passata in ingresso 
    **
    I associate to level the level of the last action in input
  **/
  level = *act->level;
  /** 
    Se la noop e' mutuamente esclusiva con l'azione viene inserite nella lista delle noop non 
    inserite per la propagazione all'indietro 
    **
    If the noop is mutually exclusive with the action it is inserted in the list of the noop not
    inserted for the propagation to behind
  **/
  if (vectlevel[level]->noop_act[noop_pos].w_is_overall == 0)
    noop_prec_not_in_add (act, noop_pos);
  noop = &vectlevel[level]->noop_act[noop_pos];
  fact_uid_block = uid_block = GUID_BLOCK (noop_pos);
  fact_uid_mask = uid_mask = GUID_MASK (noop_pos);

  /** 
    Aggiorno i bit dell'array delle noop minacciate per le precondizioni 
    **
    I update the bit of the array of the noop threatened for the preconditions
  **/
  vectlevel[level]->noop_prec_act_vect[uid_block] &= ~uid_mask;
  /** 
    Decremento w_is_goal siccome il numero di azioni supportate dalla noop è diminuito 
    **
    Decrement w_is_goal because the number of actions supported from the noop is decreased
  **/
  noop->w_is_goal--;
  /** 
    Dalla struttura vectlevel ricavo il fatto corrispondente alla posizione della noop 
    **
    From the structure vectlevel revenue the fact correspondent to the position of the noop
  **/
  fact = &vectlevel[level]->fact[noop_pos];
  /** 
    La posizione del fatto deve essere uguale a quella della noop 
    **
    The position of the fact must be equal to that one of the noop
  **/
  fact_pos = noop_pos;
  /** 
    Se il fatto supporta azioni nei livelli successivi decremento il numero di fatti supportati 
    causa la ME 
    **
    If the fact supports actions in the successive levels I decrement the number of facts supported
    cause ME
  **/
  if (fact->w_is_goal)
    fact->w_is_goal--;

  /** 
    Ora rimuovo all'indietro la catena informativa 
    **
    Now I remove backward the noop chain
  **/
  while (fact->w_is_goal == 0)
    {

      /** 
	Azzero per sicurezza i bit vector del fatto 
	**
	I annul for emergency the bit vector of the fact
      **/
      vectlevel[level]->prec_vect[fact_uid_block] &= ~fact_uid_mask;
      vectlevel[level]->true_crit_vect[fact_uid_block] &= ~fact_uid_mask;
      vectlevel[level]->false_crit_vect[fact_uid_block] &= ~fact_uid_mask;
      /** 
	Scendo di livello 
	**
	I come down of level
      **/
      level--;
      
      if (level < 0) {
#ifdef __MY_OUTPUT__
	MSG_ERROR( WAR_BUG );
#else
	printf( WAR_BUG );
#endif
	exit (0);
      }
      
      /** 
	Ottengo l'azione dal livello corrente 
	**
	I obtain the action from the running level
      **/
      inf_act = GET_ACTION_OF_LEVEL (level);
      /** 
	Se l'azione e' inserita nell'action subgraph 
	**
	If the inserted action is in the action subgraph
      **/
      if (inf_act->position >= 0)
	{

	  /** 
	    Controllo se fact_pos (fatto) e' tra gli effetti additivi at_end  di inf_act (azione) 
	    **
	    Control if fact_pos (fact) is between the additive effects at_end of inf_act (action)
	  **/
	  for (j = 0; j < gef_conn[inf_act->position].num_A; j++)
	    {
	      /** 
		Associo a el l'intero corrispondente agli effetti additivi 
		**
		I associate to el the integer correspondent to the additive effects
	      **/
	      el = gef_conn[inf_act->position].A[j];
	      if (el < 0)
		break;
	      /** 
		se il fatto era reso vero dall'azione e questa non ha altri effetti utili la rimuovo 
		**
		if the fact were rendered true by the action and this does has not other useful effects I remove it
	      **/
	      if (el == fact_pos && action_eff_cost (inf_act) <= 0.0)
		{

		  // se il fatto era reso vero dall'azione e questa non ha altri effetti utili la rimuovo 
		  remove_prec_act (inf_act);
		  break;
		}
	    }

	  /** 
	    Controllo se fact_pos (fatto) e' tra gli effetti additivi at_start di inf_act (azione) 
	    **
	    Control if fact_pos (fact) is between the additive at_start effects of inf_act (action)
	  **/
	  if (gef_conn[inf_act->position].sf != NULL)
	    {
	      for (j = 0; j < gef_conn[inf_act->position].sf->num_A_start;
		   j++)
		{
		  /** 
		    Associo a el l'intero corrispondente agli effetti additivi 
		    **
		    I associate to el the integer correspondent to the additive effects
		  **/
		  el = gef_conn[inf_act->position].sf->A_start[j];
		  if (el < 0)
		    break;
		  /** 
		    Se il fatto e' negli effetti cancellanti continuo 
		    **
		    If the fact is in the cancelling effects I continue
		  **/
		  if (is_fact_in_delete_effects (inf_act->position, el))
		    continue;
		  /** 
		    Se il fatto era reso vero dall'azione e questa non ha altri effetti 
		    utili la rimuovo 
		    **
		    If the fact was rendered true from the action and this have not other useful effects
		    I remove it
		  **/
		  if (el == fact_pos && action_eff_cost (inf_act) <= 0.0)
		    {

		      /**
			se il fatto era reso vero dall'azione e questa non ha altri effetti utili la rimuovo
			**
			if the fact was rendered tru by the action and this has not other useful effects, I remove it
		      **/
		      remove_prec_act (inf_act);
		      break;
		    }
		}
	    }
	}
      if (level <= 0 || CHECK_FACT_POS (fact->position, level) == FALSE
	  || (vectlevel[level]->noop_prec_act_vect[uid_block] & uid_mask) ==
	  0)
	break;

#ifdef __TEST__
      printf ("\n Remove w_is_goal for action %s and fact %s level %d ",
	      print_noop_name_string (noop_pos, temp_name),
	      print_ft_name_string (noop_pos, temp_name), level);

#endif
      /** 
	Aggiorno i bit dei vettori corrispondenti al fatto 
	**
	I update the bit of the arrays correspondents to the fact
      **/
      vectlevel[level]->noop_prec_act_vect[uid_block] &= ~uid_mask;
      vectlevel[level]->noop_act[noop_pos].w_is_goal--;
      /** 
	Ricavo il nuovo fatto 
	**
	Revenue the new fact
      **/
      fact = &vectlevel[level]->fact[fact_pos];
      /** 
	Se il fatto supporta azioni al livello successivo decremento w_is_goal 
	**
	If the fact supports actions to the successive level I decrement w_is_goal
      **/
      if (fact->w_is_goal)
	fact->w_is_goal--;

#ifdef __TEST__
      printf (" w_is_goal %d", fact->w_is_goal);

#endif
    }
}


/** OK 22-07-04
 * Nome: backward_precond_propagation
 * Scopo: inserisce la catena informativa all'indietro
 * Tipo: int
 * Input: inform *fact (tipo inform contenente le informazioni relative ad un fatto)
 * Output: 1 se vi e' qualche problema nella propagazione
 *         0 se e' tutto andato a buon fine
 * Strutture dati principali: vectlevel
 *                            geff_con
 *                            inform
 *                            GpG
 * Funzioni principali utilizzate: is_fact_in_additive_effects_start
 *                                 check_mutex_noop_durative
 *                                 is_fact_in_additive_effects
 *                                 noop_prec_not_in_add
 *                                 insert_prec_act
 * Chiamata da: check_prec_add_list
 *              initialize
 *              insert_action_in_vectlevel
**
*  Name: backward_precond_propagation
*  Objective: it inserts the informative chain to behind
*  Type: int
*  Input: inform * fact (containing type inform the relative information to a fact)
*  Output: 1 if you e' some problem in the propagation
*          0 if e' all going to good aim
*  Main Data Structures: vectlevel
*                        geff_con
*                        inform
*                        GpG
*  Main Functions Used: is_fact_in_additive_effects_start
*                       check_mutex_noop_durative
*                       is_fact_in_additive_effects
*                       noop_prec_not_in_add
*                       insert_prec_act
*  Call gives: check_prec_add_list
*              initialize
*              insert_action_in_vectlevel
**/
int backward_precond_propagation (FctNode_list fact)
{
  /** 
    Interi di appoggio 
    **
    Integer of support
  **/
  int curr_level, position_fact, position_noop, position_me_action, back_prop;
  /** 
    Unsigned int utilizzati per l'aggiornamento dei vettori di vectlevel 
    **
    Unsigned int used for the updating of the arrays of vectlevel
  **/
  unsigned int f_uid_block, f_uid_mask, uid_block, uid_mask;
  ActNode_list inf_act;
  /** 
    Assegno a position_fact la posizione del fatto passato in ingresso 
    **
    I assign to position_fact the position of the passed fact in input
  **/
  position_fact = fact->position;
  /** 
    Ottengo il livello sempre dal fatto passato in ingresso 
    **
    I always obtain the level from the fact passed in input
  **/
  curr_level = *fact->level;
  /** 
    Controllo che il livello corrente ovvero quello del fatto non sia maggiore 
    della lunghezza del piano 
    **
    I control that the current level, that is that one of the fact, is not greater
    of the length of the plan
  **/
  if (curr_level > GpG.curr_plan_length)
    return 1;
  back_prop = 0;
  /** 
    Assegno a position_noop la posizione del fatto 
    **
    I assign to position_noop the position of the fact
  **/ 
  position_noop = position_fact;
  if (position_noop < 0)
    return 1;
  /** 
    Dalla posizione della noop (uguale a quella del fatto) ottengo i blocchi di bit corrispondenti 
    che utilizzero' per l'aggiornamento dei vettori corrispondenti 
    **
    From the position of the noop (equal to that one of the fact) I obtain the corresponding blocks of bit
    that I will use for the updating of the corresponding arrays
  **/
  f_uid_block = uid_block = GUID_BLOCK (position_noop);
  f_uid_mask = uid_mask = GUID_MASK (position_noop);
  /** 
    Ciclo all'indietro che scorre il piano all'indietro 
    **
    Cycle to behind that slides the plan to behind
  **/
  while (curr_level > 0)
    {
      /** 
	Scendo al livello inferiore 
	**
	I come down to the inferior level
      **/
      curr_level--;
      /** 
	Ottengo l'azione presente nel livello inferiore 
	**
	I obtain the action present in the inferior level
      **/
      inf_act = GET_ACTION_OF_LEVEL (curr_level);
      /** 
	Dalla posizione della noop (fatto) osservo se vi e' ME tra il fatto e l'azione nel 
	presente livello 
	**
	From the position of the noop (fact) I observe if there is ME between the fact and the action in
	present level
      **/
      position_me_action =
	check_mutex_noop_durative (position_noop, curr_level);
      /** 
	Se il fatto è precondizione dell'azione nel livello 
	**
	If the fact is precondition of the action in the level
      **/
      if (inf_act->w_is_used)
	{
	  /** 
	    Controllo che il fatto sia negli effetti additivi dell'azione 
	    **
	    Control that the fact is in the additive effects of the action
	  **/
	  if (is_fact_in_additive_effects (inf_act->position, position_fact))
	    {
	      /** 
		L'azione e' utile in quanto il fatto appartenente alla catena informativa e' reso vero 
		dall'azione inf_act 
		**
		The action is useful because the fact of the informative chain is rendered true
		from the action inf_act
	      **/
	      insert_prec_act (inf_act);
	      /** 
		Se la noop e' mutuamente esclusiva con l'azione la inserisco nella lista delle noop non 
		inserite per le precondizioni 
		**
		If the noop is mutually exclusive with the action I insert it in the list of the noop not
		inserted for the precondition
	      **/
	      if (position_me_action >= 0)
		noop_prec_not_in_add (&vectlevel[curr_level]->action,
				      position_noop);
	      break;
	    }
	  /** 
	    Controllo se la noop sia negli effetti additivi AT-START e non negli effetti cancellanti 
	    **
	    Control if the noop is in the additive AT_START effects and not in the cancelling effects
	  **/
	  if (is_fact_in_additive_effects_start
	      (inf_act->position, position_fact)
	      && !is_fact_in_delete_effects (inf_act->position,
					     position_fact))
	    {
	      /** 
		L'azione e' utile in quanto il fatto appartenente alla catena informativa e' reso vero 
		dall'azione inf_act 
		**
		The useful action e' in how much the fact pertaining to the informative chain e' rendered true
		from the action inf_act
	      **/
	      insert_prec_act (inf_act);
	      /** 
		Se la noop e' mutuamente esclusiva con l'azione la inserisco nella lista delle noop non 
		inserite per le precondizioni 
		**
		If the noop is mutually exclusive with the action I insert it in the list of the noop not
		inserted for the precondition
	      **/
	      if (position_me_action >= 0)
		noop_prec_not_in_add (&vectlevel[curr_level]->action,
				      position_noop);
	      break;
	    }
	}
      if (!CHECK_NOOP_POS (position_noop, curr_level)
	  || vectlevel[curr_level]->noop_act[position_noop].w_is_goal)
	return 0;

#ifdef __TEST__
      printf ("\n Insert w_is_goal for action %s and fact %s level %d ",
	      print_noop_name_string (position_noop, temp_name),
	      print_ft_name_string (position_fact, temp_name), curr_level);
#endif

      /** 
	Se la noop e' negli effetti cancellanti  AT-START e non negli effetti additivi AT-END o negli 
	effetti cancellanti AT-START e non negli effetti additivi AT-END o negli effetti additivi AT_START 
	e negli effetti cancellanti AT-END o non negli effetti additivi AT_START e negli effetti
	cancellanti AT-END e back_prop(intero) è vero restituisce 0 
	**
	If the noop is in the cancelling effects AT_START and not in the additive AT_END effects or in
	cancelling effects AT_START and not in the additive AT_END effects or in the additive AT_START
	and in the cancelling AT_END effects or in the additive AT_START effects and in the
	AT_END cancelling effects and back_prop(integer) is true gives back 0
      **/
      if ((vectlevel[curr_level]->noop_act[position_noop].w_is_overall ==
	   DEL_ADD
	   || vectlevel[curr_level]->noop_act[position_noop].
	   w_is_overall == DEL_NADD
	   || vectlevel[curr_level]->noop_act[position_noop].
	   w_is_overall == ADD_DEL
	   || vectlevel[curr_level]->noop_act[position_noop].
	   w_is_overall == NADD_DEL) && back_prop)
	return (0);

      /** 
	se c'è la noop o non e' ME con l'azione 
	**
	if there is noop or is not ME with the action
      **/
      if (vectlevel[curr_level]->noop_act[position_noop].w_is_used == 1
	  || position_me_action < 0)
	{
	  /** 
	    Aggiorno i campi relativi alla noop e al fatto contenuto in essa 
	    **
	    I update the fields of the noop and the fact contained in it
	  **/
	  vectlevel[curr_level]->noop_act[position_noop].w_is_goal++;
	  vectlevel[curr_level]->noop_prec_act_vect[uid_block] |= uid_mask;
	  vectlevel[curr_level]->fact[position_fact].w_is_goal++;
	  vectlevel[curr_level]->prec_vect[f_uid_block] |= f_uid_mask;
	  /** 
	    Se il fatto e' critico vero (supportato da una sola azione nei livelli inferiori 
	    **
	    If the critical fact is true (supported from one single action in the inferior levels
	  **/
	  if (vectlevel[curr_level]->fact[position_fact].w_is_true == 1)
	    {
	      /** 
		Imposto i bit nei vettori relativi ai fatti critici 
		**
		I set the bit in the arrays relatives to the critical facts
	      **/
	      vectlevel[curr_level]->true_crit_vect[f_uid_block] |=
		f_uid_mask;
	      vectlevel[curr_level]->false_crit_vect[f_uid_block] &=
		~f_uid_mask;
	    }

	  /** 
	    Se il fatto e' critico falso (non e' supportato da alcuna azione nei livelli 
	    inferiori (w_is_true=0)) 
	    **
	    If the critical fact is false (is not supported from some action in the levels
	    inferiors (w_is_true=0))
	  **/
	  else if (vectlevel[curr_level]->fact[position_fact].w_is_true <= 0)
	    {

	      /** 
		Imposto i bit nei vettori relkativi ai fatti critici 
		**
		I set the bit in the arrays relatives to the critical facts
	      **/
	      vectlevel[curr_level]->true_crit_vect[f_uid_block] &=
		~f_uid_mask;
	      vectlevel[curr_level]->false_crit_vect[f_uid_block] |=
		f_uid_mask;
	    }

	  else
	    {
	      /** 
		Imposto i bit nei vettori relativi ai fatti critici 
		**
		I set the bit in the arrays relatives to the critical facts
	      **/
	      vectlevel[curr_level]->true_crit_vect[f_uid_block] &=
		~f_uid_mask;
	      vectlevel[curr_level]->false_crit_vect[f_uid_block] &=
		~f_uid_mask;
	    }
	}

      /** 
	Se invece la noop non e' inserita 
	**
	If instead the noop is not inserted
      **/
      else
	{
	  /**  
	    se la potenziale noop è me con una azione allora non faccio niente e aggiungo 
	    la noop nel vettore noop non inserite della azione 
	    **
	    if thge potential noop is me with an action then I do nothing and I add
	    the noop in the noop not inserted array of the action
	  **/
	  if (position_me_action >= 0)
	    {
	      noop_prec_not_in_add (&vectlevel[curr_level]->action,
				    position_noop);
	      return (0);
	    }


	  else {

#ifdef __MY_OUTPUT__
	    MSG_ERROR( WAR_BUG );
#else
	    printf( WAR_BUG );
#endif
	    exit (0);
	  }

	}
      /** 
	Aggiorno back propagation 
	**
	I update back propagation
      **/
      back_prop = 1;
    }				//in ogni caso scendo di livello
  if (curr_level <= 0
      || vectlevel[curr_level - 1]->fact[position_fact].w_is_goal > 1)
    return (1);			//se un fatto era gia' precondizione mi fermo nella discesa
  return 0;
}


/** OK 22-07-04
 * Name: backward_precond_remotion
 * Scopo: rimuove la catena informativa all'indietro
 * Tipo: int
 * Input: inform *fact (tipo inform contenente le informazioni relative ad un fatto)
 *        int propagation
 * Output: 0
 *         1
 * Strutture dati principali: vectlevel
 *                            geff_con
 *                            inform
 *                            GpG
 * Funzioni principali utilizzate: remove_prec_act
 * Chiamata da: remove_action_from_vectlevel
**
*  Name: backward_precond_remotion
*  Objective: it removes the informative chain to behind
*  Type: int
*  Input: inform *fact (containing type inform the relative information to a fact)
*         int propagation
*  Output: 0
*          1
*  Main Data Structures: vectlevel
*                        geff_con
*                        inform
*                        GpG
*  Main Functions Used: remove_prec_act
*  Call gives: remove_action_from_vectlevel
**/
int backward_precond_remotion (FctNode_list fact, int propagation)
{
  /** 
    Interi di appoggio 
    **
    Integer of support
  **/
  int curr_level, position_fact, noop_position, j;
  /** 
    Unsigned int di appoggio per aggiornare i vettori corrispondenti ai fatti critici 
    **
    Unsigned int of support to update the arrays correspondents to the critical facts
  **/
  unsigned int uid_block, uid_mask, f_uid_block, f_uid_mask;
  /** 
    int el intero di appoggio per ricavare il tipo di precondizione da geff_conn 
    **
    int el integer of support to gain the type of precondition from geff_conn
  **/
  int el;
  ActNode_list inf_act;

#ifdef __TEST__
  if (propagation == 0)
    printf ("\n PROPAGATION=0!!");

#endif
  /** 
    Ricavo il livello dalla struttura inform relativa al fatto passato in ingresso 
    **
    Revenue the level from the structure inform relative to the fact passed in input
  **/
  curr_level = *fact->level;
  /** 
    Associo a position_fact la posizione del fatto 
    **
    I associate to position_fact the position of the fact
  **/
  position_fact = fact->position;
  /** 
    Se il livello e' maggiore di 0 e e' presente il fatto nel livello inferiore associo 
    alla position_noop (posizione relativa alla noop) la posizione corrispondente al fatto 
    **
    If the level is greater than 0 and is present the fact in the inferior level I associate
    to position_noop (the relative position to noop) the position correspondent to the fact
  **/
  if (curr_level > 0 && CHECK_FACT_POS (position_fact, curr_level - 1))
    noop_position = position_fact;

  else
    return 1;
  /** 
    Da posizione della noop ricavo il blocco di bit corrispondente e la maschera 
    **
    From position of noop I revenue the block of corresponding bit and the mask
  **/
  f_uid_block = uid_block = GUID_BLOCK (noop_position);
  f_uid_mask = uid_mask = GUID_MASK (noop_position);
  /** 
    Ciclo che scorre il piano a ritroso 
    **
    Cycle that slides the plan
  **/
  while (curr_level > 0)
    {
      /** 
	Scendo di livello 
	**
	I come down of level
      **/
      curr_level--;

      if (propagation)
	{
	  /** 
	    Associo a inf_act l'azione nel livello 
	    **
	    I associate to inf_act the action in the level
	  **/
	  inf_act = &vectlevel[curr_level]->action;
	  /** 
	    Se l'azione e' inserita nell'action subgraph 
	    **
	    If the inserted action is in the action subgraph
	  **/
	  if (inf_act->w_is_used)
	    {
	      /** 
		Scorro gli effetti additivi dell'azione 
		**
		I slide the additive effects of the action
	      **/
	      for (j = 0; j < gef_conn[inf_act->position].num_A; j++)
		/** 
		  Se il fatto e' negli effetti additivi dell'azione e questa non ha 
		  altri effetti utili 
		  **
		  If the fact is in the additive effects of the action and this not have
		  other useful effects
		**/
		if ((el = gef_conn[inf_act->position].A[j]) == position_fact
		    && action_eff_cost (inf_act) <= 0.0)
		  {

#ifdef __TEST__
		    printf ("\n PROPAGATION==1!!");
#endif
		    remove_prec_act (inf_act);
		    break;
		  }

	      /** 
		Se il fatto e' negli effetti additivi dell'azione nel caso di azione durative 
		**
		If the fact is in the additive effects of the action in the case of durative action
	      **/
	      if (gef_conn[inf_act->position].sf != NULL)
		{
		  /**
		    Scorro gli effetti additivi dell'azione 
		    **
		    I slide the additive effects of the action
		  **/
		  for (j = 0;
		       j < gef_conn[inf_act->position].sf->num_A_start; j++)
		    {
		      el = gef_conn[inf_act->position].sf->A_start[j];
		      if (el < 0)
			continue;
		      /** 
			Se il fatto e' negli effetti cancellanti dell'azione non fa nulla 
			**
			If the fact is in the cancelling effects of the action it does nothing
		      **/
		      if (is_fact_in_delete_effects (inf_act->position, el))
			continue;
		      /** 
			Se il fatto e' negli effetti additivi dell'azione e questa non ha 
			altri effetti utili 
			**
			If the fact is in the additive effects of the action and this not have
			other useful effects
		      **/
		      if (el == position_fact
			  && action_eff_cost (inf_act) <= 0.0)
			{
			  remove_prec_act (inf_act);	// se il fatto era reso vero dall'azione e questa non ha altri effetti utili la rimuovo
			  break;
			}
		    }
		}
	    }
	}

#ifdef __TEST__
      printf ("\n Remove w_is_goal from action %s and fact %s level %d ",
	      print_noop_name_string (noop_position, temp_name),
	      print_ft_name_string (position_fact, temp_name), curr_level);

#endif
      /** 
	Se propagation e' uguale a zero lo pongo ad 1 
	**
	If propagation is equal to zero I place it to 1
      **/
      if (propagation == 0)
	propagation = 1;
      /** 
	Controllo la presenza della noop 
	**
	I control the presence of the noop
      **/
      if (!CHECK_NOOP_POS (noop_position, curr_level))
	return 0;
       /** 
	 Aggiornamento dei campi relativi ai bit della noop e del fatto 
	 **
	 Updating of the fields relatives to the bit of the noop and the fact
       **/
      if (vectlevel[curr_level]->noop_prec_act_vect[uid_block] & uid_mask)
	{
	  vectlevel[curr_level]->noop_prec_act_vect[uid_block] &= ~uid_mask;
	  vectlevel[curr_level]->noop_act[noop_position].w_is_goal--;
	  vectlevel[curr_level]->fact[position_fact].w_is_goal--;
	}

      else
	return 0;

      /** 
	se il fatto sotto non è w_is_goal non cè nessuna catena da rimuovere 
	**
	if the following fact is not w_is_goal there are not anything chain to remove
      **/
      if (vectlevel[curr_level]->fact[position_fact].w_is_goal != 0)
	return (0);

      /** 
	Azzero per sicurezza entrambi i bit vector del fatto 
	**
	I annul for emergency both the bit vector of the fact
      **/
      vectlevel[curr_level]->true_crit_vect[f_uid_block] &= ~f_uid_mask;
      vectlevel[curr_level]->false_crit_vect[f_uid_block] &= ~f_uid_mask;
      vectlevel[curr_level]->prec_vect[f_uid_block] &= ~f_uid_mask;

      //aggiungere controllo se c' e' noop se non c'e' mi devo fermare

    }
  return (0);
}

/** 
 * Name: check_prec_add_list
 * Scopo: E' chiamata durante la rimozione di un azione per inserire le NOOP bloccate
 * Tipo: void
 * Input: inform *act (tipo inform contenente le informazioni relative ad una azione)
 * Output:
 * Strutture dati principali: vectlevel
 *                            inform
 *                            GpG
 * Funzioni principali utilizzate: backward_precond_propagation
 *                                 forward_noop_propagation_time
 *                                 forward_noop_propagation
 *                                 free_noop_not_in
 * Chiamata da: remove_action_from_vectlevel
**
*  Name: check_prec_add_list
*  Objective: Is called during the removal of an action in order to insert the blocked NOOP
*  Type: void
*  Input: inform * act (containing type inform the relative information to one action)
*  Output:
*  Main Data Structures: vectlevel
*                        inform
*                        GpG
*  Used main functions: backward_precond_propagation
*                       forward_noop_propagation_time
*                       forward_noop_propagation
*                       free_noop_not_in
*  Call gives: remove_action_from_vectlevel
**/
void check_prec_add_list (ActNode_list act)
{
  /** 
    Struttura utilizzata per memorizzare la posizione di una noop (ad
    un determinato livello) non inserita poiche' mutuamente esclusiva
    con un'azione
    **
    Used structure to memorize the position of one noop (to a done level)
    not inserted because mutually exclusive with an action
  **/
  noop_not_in *temp;
  /** 
    Intero di appoggio a cui verra' assegnato un valore corrispondente
    al livello
    **
    Integer of support to which verra' assigned to a value
    correspondent to the level
  **/
  int level;
  NoopNode_list inf_noop;
  /** 
    Assegno a level il livello di partenza ricavato dall' inform relativo all'azione 
    **
    I assign to level the level of starting gained from the inform relative to the action
  **/
  level = *act->level;

  /** 
    NOOP non inserite per le precondizioni 
    **
    NOOP not inserted of the preconditions
  **/
  temp = act->preco;
  /** 
    Scorro la lista delle noop non inserite per le precondizioni 
    **
    I slide the list of the noop not inserted for the preconditions
  **/
  while (temp != NULL)
    {
     /** 
	Associo la noop mutuamente esclusiva con l'azione nel livello a inf_noop 
	**
	I associate the noop mutually exclusive with the action in the level to inf_noop
      **/
      inf_noop = &vectlevel[level]->noop_act[temp->position];
      /** 
	Se la noop e' presente nel livello ed il fatto e' precondizione per azioni 
	nei livelli superiori 
	**
	If noop is in the level and the fact is precondition for actions
	in the advanced levels
      **/
      if (CHECK_NOOP_POS (temp->position, level)
	  && vectlevel[level + 1]->fact[temp->position].w_is_goal
	  && vectlevel[level]->fact[temp->position].w_is_goal == 0)
	backward_precond_propagation (&vectlevel[level + 1]->
				      fact[temp->position]);
      /** 
	Se il fatto e' precondizione per l'azione nel livello successivo e la noop non 
	e' precondizione dell'azione nel livello 
	**
	If the fact is precondition for the action in the successive level and the noop is not
	precondition of the action in the level
      **/
      if (vectlevel[level + 1]->fact[temp->position].w_is_goal > 0
	  && vectlevel[level]->noop_act[temp->position].w_is_goal == 0
	  && vectlevel[level]->fact[temp->position].w_is_goal > 0)
	{
	  /** 
	     Significa che l'inserimento non ha interrotta la catena informativa 
	     **
	     It means that the insertion has not interrupted the informative chain
	  **/
	  /** 
	     Aggiorno i campi relativi alla noop 
	     **
	     I update the fields relative to the noop
	  **/
	  vectlevel[level]->noop_act[temp->position].w_is_goal++;
	  vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (temp->position)] |=
	    GUID_MASK (temp->position);
	}
      /** 
	Scorro la lista di noop non inserite per le precondizioni 
	**
	I slide the list of noop not inserted for the preconditions
      **/
      temp = temp->next;
    }

  /** 
    NOOP non inserite per gli effetti additivi 
    **
    NOOP not inserted for the additive effects
  **/
  /** 
    Assegno a temp la lista di noop non inserite per gli effetti additivi 
    **
    I assign to temp the list of noop not inserted for the additive effects
  **/
  temp = act->add;
  /** 
    Scorro la lista delle noop non inserite per gli effetti additivi 
    **
    I slide the list of the noop inserted for the effects does not point out to you
  **/
  while (temp != NULL)
    {
      /** 
	Associo la noop mutuamente esclusiva con l'azione nel livello a inf_noop 
	**
	I associate the mutually exclusive noop with the action in the level to inf_noop
      **/
      inf_noop = &vectlevel[level]->noop_act[temp->position];
      /** 
	Se la noop e' presente nel livello e il fatto ad essa associato e' presente nel livello 
	propago in avanti gli effetti della noop (sia di fatti che temporali) 
	**
	If the noop is in the level and the associated fact is in the level
	I propagate in ahead the effects of the noop (both facts that temporal)
      **/
      if (CHECK_NOOP_POS (temp->position, level)
	  && vectlevel[level]->fact[temp->position].w_is_true)
	{
	  /** 
	    Propaga in avanti le noop me con l'azione 
	    **
	    Propagate in ahead the noop me with the action
	  **/ 
	  forward_noop_propagation (temp->position, level);
	  
	  if (GpG.temporal_plan)
	    forward_noop_propagation_time (&vectlevel[level]->
					   noop_act[temp->position]);
	}
      /** 
	Scorro la lista delle noop non inserite per gli effetti additivi 
	**
	I slide the list of the noop not inserted for the additive effects
      **/
      temp = temp->next;
    }

  /** 
    NOOP non inserite per mutua esclusione con l'azione 
    **
    NOOP not inserted of mutual exclusion with the action
  **/
  temp = act->treated;
  /** 
    Scorro la lista delle noop 
    **
    I slide the list of the noop
  **/
  while (temp != NULL)
    {
      inf_noop = &vectlevel[level]->noop_act[temp->position];
      if (CHECK_NOOP_POS (temp->position, level)
	  && vectlevel[level + 1]->noop_act[temp->position].false_position)
	/** 
	  Rimuove le noop dalla lista delle inconsistenze 
	  **
	  It removes the noop from the list of the inconsistenze
	**/
	remove_treated_noop (inf_noop);
      temp = temp->next;
    }
  free_noop_not_in (act);
}



/*********************************************
          INCONSISTENCE LIST  
**********************************************/




/** OK 22-07-04
 * Name: remove_false_fact
 * Scopo: rimuovere un nodo dall'array delle inconsistenze (unsup_fact[]) per i fatti
 * Tipo: void
 * Input: register inform_list inf_address
 * Output: nessuno
 * Strutture dati principali: GpG
 *                            gef_conn
 *                            FtConn
 *                            constraint_list unsup_fact[]
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: remove_action_from_vectlevel
 *              forward_noop_propagation
 *              insert_action_in_vectlevel
**
*  Name: remove_false_fact
*  Objective: to remove a node from the Array of the inconsistenze (unsup_fact[ ]) for the facts
*  Type: void
*  Input: register inform_list inf_address
*  Output: none
*  Main Data Structures: GpG
*                        gef_conn
*                        FtConn
*                        constraint_list unsup_fact[ ]
*  Main Functions Used: none
*  Call gives: remove_action_from_vectlevel
*              forward_noop_propagation
*              insert_action_in_vectlevel
**/
void remove_false_fact (register FctNode_list inf_address)
{
  /** 
    Variabili di appoggio 
    **
    Variable of support
  **/
  /** 
    constraint_list unsup_fact variabile contenete le informazioni relative al fatto non supportato 
    da rimuovere 
    **
    constraint_list unsup_fact variable that contain the relative information to the fact not supported
    to remove
  **/
  constraints_list unsup_f;
  /** 
    int level intero utilizzato per scorrere il piano 
    **
    int level integer used to slide the plan
  **/
  register int temp, level, j, el;
  /** 
    Ftconn *go_address variabile contenente informazioni relative al fatto da rimuovere dal vettore 
    delle inconsistenze 
    **
    Ftconn *go_address variable containing information of the fact to remove from the array
    of the inconsistenze
  **/
  FtConn *go_address = NULL;

#ifdef __TEST__
  char *name = NULL;
#endif

  /** 
    Assegna a go_address (struttura FtConn) le caratteristiche del fatto 
    **
    It assigns go_address (FtConn structure) the characteristics of the fact
  **/
  go_address = CONVERT_FACT_TO_VERTEX (inf_address->position);

#ifdef __TEST__
  name = (char *) print_ft_name_string (go_address->position, temp_name);
#endif
  
  temp = 0;
  /** 
    Assegna a level il livello del fatto 
    **
    It assigns to level the level of the fact
  **/
  level = *inf_address->level;
  /** 
    Controllo che il fatto sia inserito nel vettore delle inconsistenze (false_position>0), in caso 
    ocntrario esce 
    **
    Control that the fact is inserted in the carrier of the inconsistence (false_position>0), in case
    contrary exits
  **/
  if (inf_address->false_position < 0) {
    
#ifdef __TEST__
    if (DEBUG3)
      printf ("\n FALSE POSITION <0 %s position %d level %d", name,
	      inf_address->position, level);
#endif
    
    return;
  }

  /**
     ulteriore controllo
     **
     additional check
  **/

#ifdef __TEST__
  if (GpG.num_false_fa <= 0){
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else
    printf( WAR_BUG );
#endif
    return;   
  }
  
#endif
 
  if (inf_address->position >=0 && gft_conn[inf_address -> position].fact_type != IS_DERIVED) { 
    
  /** 
    Se il fatto e' precondizione di azioni nei livelli superiori e il livello e' maggiore di zero  
    **
    If the fact is precondition of actions in the advanced levels and the level is greater than zero
  **/
    if (inf_address->w_is_used && level > 0)
      {
	temp = 0;
	
      /** 
	Se il fatto e' negli effetti additivi dell'azione nel livello inferiore aumento temp 
	**
	If the fact is in the additive effects of the action in the inferior level I increase temp
      **/
	
	if (GET_ACTION_OF_LEVEL (level - 1)->w_is_used)
	/** 
	  Scorro gli effetti additivi dell'azione nel livello inferiore 
	  **
	  I slide the additive effects of the action in the inferior level
	**/
	  for (j = 0;
	       j < gef_conn[GET_ACTION_OF_LEVEL (level - 1)->position].num_A;
	       j++)
	    if ((el =
		 gef_conn[GET_ACTION_OF_LEVEL (level - 1)->position].A[j]) ==
		inf_address->position)
	      {
		temp++;
		break;
	      }
      /** 
	Se il fatto fa parte di noop nel livello inferiore aumento temp ed esco 
	**
	If the fact is part of noop in the inferior level I increase temp and exits
      **/
	if (CONVERT_NOOP_TO_NODE (inf_address->position, level - 1)->
	    w_is_used)
	  temp++;
      /** 
	Se temp e' uguale a zero vuol dire che l'azione nel livello inferiore non la supporta e 
	non appartiene alla catena di noop quindi segnala un errore con un messaggio 
	**
	If temp is equal to zero it means that the action in the inferior level does not support it and
	it does not belong to the chain of noop therefore it marks an error with a message
      **/
	if (temp == 0)
	  {
	    
#ifdef __TEST__
#ifdef __MY_OUTPUT__
	    MSG_ERROR( WAR_BUG );
#else
	    printf( WAR_BUG );
#endif
#endif
	    return;
	}
    }

  }
 
  /** 
    Decrementa il campo relativo al numero di fatti falsi associato a GpG 
    **
    Decrements the relative field to the number of facts associated to GpG
  **/
  GpG.num_false_fa--;

#ifdef __TEST__
  printf ("\n RIMUOVO fact %s,  level %d, false pos %d", name,
	  *inf_address->level, inf_address->false_position);

#endif

  /** 
    Rimozione del fatto dalla lista  
    **
    Removal of the fact from the list
  **/
  /** 
    Assegno ad unsup_f il fatto da rimuovere dal vettore delle inconsistenze 
    **
    I assign to unsup_f the fact to remove from the array of the inconsistenze
  **/
  unsup_f = unsup_fact[inf_address->false_position];
  /** 
    Aggiorno il vettore delle inconsistenze 
    **
    I update the carrier of the inconsistence
  **/
  unsup_fact[inf_address->false_position] = unsup_fact[GpG.num_false_fa];
  CONVERT_FACT_TO_NODE (unsup_fact[GpG.num_false_fa]->fact,
			  *unsup_fact[GpG.num_false_fa]->level)->
    false_position = inf_address->false_position;
  /** 
    Pongo a -1 il campo false position (l'azione non e' piu' nel vettore delle inconsistenze) 
    **
    I place to -1 the field false position (the action is not more the array of the inconsistenze)
  **/
  inf_address->false_position = -1;
  /** 
    Aggiornamento del vettore unsup_fact 
    **
    Updating the array unsup_fact
  **/
  unsup_fact[GpG.num_false_fa] = unsup_f;
  unsup_fact[GpG.num_false_fa]->fact = unsup_fact[GpG.num_false_fa]->action = unsup_fact[GpG.num_false_fa]->constraint_type = -1;
  if (DEBUG3 && num_try > 0)
    printf ("\n New True Fact: %s   Level %d ",
	    print_ft_name_string (inf_address->position, temp_name),
	    *inf_address->level);

#ifdef __TEST__
  printf ("\n REMOVE FALSE fact %s, false_act %d false_fact %d level %d",
	  name, GpG.num_false_act, GpG.num_false_fa, *inf_address->level);
  printf ("\n Remove false end  %d", level);

#endif
}

// OGGI 22/07/04  CVS CVS CVS CVS CVS

/** OK 23-07-04
 * Name: remove_treated_noop
 * Scopo: rimuovere una noop dall'array delle inconsistenze (treated_c_l) per le noop.
 *        Si vuole consentire la risoluzione delle minacce
 * Tipo: void
 * Input: register NoopNode_list inf_address
 * Output:
 * Strutture dati principali: GpG
 *                            gef_conn
 *                            FtConn
 *                            constraint_list treated_c_l[]
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: fix
 *              choose_actions_treated_fact
**
*  Name: remove_treated_noop
*  Objective: to remove one noop from the Array of the inconsistenze (treated_c_l) for the noop.
*  Type: void
*  Input: register NoopNode_list inf_address
*  Output:
*  Main Data Structures: GpG
*                        gef_conn
*                        FtConn
*                        constraint_list treated_c_l[ ]
*  Used main functions: none
*  Call gives: fix
*              choose_actions_treated_fact
**/
void remove_treated_noop (register NoopNode_list inf_address)
{
  /** 
    Variabili di appoggio 
    **
    Variable of support
  **/
  /** 
    constraint_list t_c_l contiene informazioni raletive alla noop da rimuovere 
    **
    constraint_list t_c_l contains raletive information to the noop to remove
  **/
  constraints_list t_c_l;
  register int temp, level;
  FtConn *go_address;

#ifdef __TEST__
  char *name;
#endif

  /** 
    Associa a go_address (struttura Ftconn) le caratteristiche della noop passata in ingresso 
    **
    It associates to go_address (Ftconn structure) the characteristics of the noop in input
  **/
  go_address = CONVERT_NOOP_TO_VERTEX (inf_address->position);

#ifdef __TEST__
  name = (char *) print_noop_name_string (inf_address->position, temp_name);
#endif

  temp = 0;
  /** 
    Ottengo il livello corrispondente 
    **
    I obtain the corresponding level
  **/
  level = *inf_address->level;
  
  /** 
    Controllo che la noop sia inserita nel vettore delle inconsistenze (false_position>0), 
    in caso contrario esce 
    **
    Control that the noop is inserted in the array of the inconsistence (false_position>0),
    otherwise it exits
  **/
  if (inf_address->false_position < 0) {
#ifdef __TEST__
    if (DEBUG3)
      printf ("\n FALSE POSITION <0 position %d level %d",inf_address->position, level);
#endif
    return;
  }
  
  /**
     controllo aggiuntivo
     **
     addictional check 
  **/
  if (GpG.num_false_act <= 0)
    {

#ifdef __MY_OUTPUT__
      MSG_ERROR( WAR_BUG );
#else
      printf( WAR_BUG );
#endif

      return;
    }

#ifdef __TEST__
  printf ("\n Remove treated fact %s  lev %d",
	  print_noop_name_string (inf_address->position, temp_name), level);

#endif

  /** 
    rimuove l'indirizzo dell'azione dal vettore false_act e aggiorna il contatore num_false_act
    **
    remove the action address from the false_act array and update the num_false_act counter
  **/
  GpG.num_false_act--;
  if (DEBUG3 && num_try > 0)
    printf ("\n New Not Treated Noop: %s   Level %d ",
	    print_noop_name_string (treated_c_l[GpG.num_false_act]->fact,
				    temp_name),
	    *treated_c_l[GpG.num_false_act]->level);
  /** 
    Assegno t_c_l le caratteristiche della noop 
    **
    Assigning to t_c_l the characteristics of the noop
  **/
  t_c_l = treated_c_l[inf_address->false_position];
  /** 
    Aggiorno il vettore treated_c_l 
    **
    Updating the treated_c_l array
  **/
  treated_c_l[inf_address->false_position] = treated_c_l[GpG.num_false_act];

  /** 
    Aggiorno l'inform relativo alla noop 
    **
    Updating the inform relative to the noop
  **/
  CONVERT_NOOP_TO_NODE (treated_c_l[GpG.num_false_act]->fact,
			  *treated_c_l[GpG.num_false_act]->level)->
    false_position = inf_address->false_position;
  /** 
    Assegno a false_position -1 (vuol dire che la noop non e' piu' nel vettore delle inconsistenze) 
    **
    Assigning to false_position -1 (it means that the noop is not more in the array of the inconsistences)
  **/
  inf_address->false_position = -1;
  treated_c_l[GpG.num_false_act] = t_c_l;
  treated_c_l[GpG.num_false_act]->fact =
    treated_c_l[GpG.num_false_act]->action =
    treated_c_l[GpG.num_false_act]->constraint_type = -1;

#ifdef __TEST__
  printf ("\n REMOVE FALSE  %s, false_act %d false_fact %d level %d", name,
	  GpG.num_false_act, GpG.num_false_fa, *inf_address->level);

  printf ("\n Remove false end B %d", level);

#endif
}


/** OK 23-07-04
 * Name: insert_unsup_fact
 * Scopo: inserire un fatto nell'array delle inconsistenze (unsup_fact[]) per i fatti
 * Tipo: void
 * Input: register  FctNode_list inf_address
 * Output: nessuno
 * Strutture dati principali: GpG
 *                            gef_conn
 *                            FtConn
 *                            constraint_list unsup_fact[]
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: forward_noop_remotion
 *              remove_noop
 *              remove_action_from_vectlevel
 *              initialize
 *              insert_action_in_vectlevel
**
*  Name: insert_unsup_fact
*  Objective: to insert a fact in the Array of the inconsistenze (unsup_fact[ ]) for the facts
*  Type: void
*  Input: register  FctNode_list inf_address
*  Output: none
*  Main Data Structures: GpG
*                        gef_conn
*                        FtConn
*                        constraint_list unsup_fact[ ]
*  Main Function Used: none
*  Call gives: forward_noop_remotion
*              remove_noop
*              remove_action_from_vectlevel
*              initialize
*              insert_action_in_vectlevel
 **/
void insert_unsup_fact (register FctNode_list inf_address)
{
  /** 
    Variabili di appoggio 
    **
    Variable of support
  **/
  int level;

#ifdef __TEST__
  char *name = NULL;
#endif

  /**
    Finte precondizioni per azioni spezzate 
    **
    Dummy precondition per splitted actions
  **/
  if (gft_conn[inf_address->position].fact_type == IS_SPL_PREC )
    return;

  level = *inf_address->level;
  if (inf_address->false_position >= 0)
    {

#ifdef __TEST__
      printf ("\nError FALSE NOT INSERT   ");
      print_ft_name (inf_address->position);
      printf (", pos %d, false_pos %d, false_act %d false_fact %d",
	      inf_address->position, inf_address->false_position,
	      GpG.num_false_act, GpG.num_false_fa);
#endif

      return;
    }

  if (inf_address->position >= 0 && gft_conn[inf_address->position].fact_type == IS_TIMED)
    return;

  if (unsup_fact[GpG.num_false_fa] == NULL)
    unsup_fact[GpG.num_false_fa] =
      (constraints_list) calloc (1, sizeof (constraints));

  if (GpG.num_false_fa >= MAX_FALSE) {	
#ifdef __MY_OUTPUT__
    MSG_ERROR ( WAR_MAX_FALSE );
#else
    printf( WAR_MAX_FALSE );
#endif    
    exit (1);
  }

  /** 
    Aggiornamento dei campi del vettore unsup_fact 
    **
    Updating of the fields of the unsup_fact array
  **/

  /** 
    Assegno all'ultimo elemento del vettore quello passato in ingresso
    **
    I assign to the last element of the array that one in input
  **/
  unsup_fact[GpG.num_false_fa]->fact = inf_address->position;
  /** 
    Assegno al campo action del vettore unsup_fact nella posizione del fatto inserito a -1 
    **
    I assign to the action field of the unsup_fact array in the position of the fact inserted to -1
  **/
  unsup_fact[GpG.num_false_fa]->action = -1;
  /** 
    Assegno al campo relativo al tipo di vincolo la mancanza di verita' per il fatto 
    **
    I assign to the field relative to the type of tie the lack of truth for the fact
  **/
  unsup_fact[GpG.num_false_fa]->constraint_type = C_T_UNSUP_FACT;
  /** 
    Assegno al campo level della struttura unsup_fact nella posizione ralativa al fatto 
    inserito il livello a cui questo si trovava quando non era piu' supportato 
    **
    I assign to the field level of the unsup_fact structure in the position relative to the fact
    inserted the level to which was this one when it was not more supported
  **/
  unsup_fact[GpG.num_false_fa]->level = inf_address->level;
  unsup_fact[GpG.num_false_fa]->supported_facts_relaxed_plan_bit_vector=NULL;
  unsup_fact[GpG.num_false_fa]->relaxed_plan_actions_bit_vector=NULL;

  define_supported_fact_for_relaxed_plan_of_inconsistences(unsup_fact[GpG.num_false_fa], TRUE);


  /** 
    Assegno ad inf_address (inform relativo al fatto) la posizione che questo fatto non 
    supportato ha nel vettore dei fatto non supportati 
    **
    I assign to inf_address (inform relative to the fact) the position that this fact not
    supported has in the array of the facts not supported
  **/
  inf_address->false_position = GpG.num_false_fa++;
  if (DEBUG3 && num_try > 0)
    printf ("\n New False Fact: %s   Level %d ",
	    print_ft_name_string (inf_address->position, temp_name),
	    *inf_address->level);

  /** 
    Esegue un controllo sul numero massimo di fatti non supportati 
    **
    It executes a control on the maximum number of facts not supported
  **/
  if (GpG.num_false_fa >= MAX_FALSE) {	
#ifdef __MY_OUTPUT__
    MSG_ERROR ( WAR_MAX_FALSE );
#else
    printf( WAR_MAX_FALSE );
#endif    
    exit (1);
  }
    
#ifdef __TEST__
  printf
    ("\n INSERT FALSE  fact %s, false_actions %d false_fact %d level %d pos %d",
     name, GpG.num_false_act, GpG.num_false_fa, *inf_address->level,
     GpG.num_false_fa - 1);

#endif

}

/**  OK 23-07-04
 * Name: insert_treated_fact
 * Scopo: inserire un nodo nell'array delle inconsistenze (unsup_fact[]) per le noop
 * Tipo: void
 * Input: register ActNode_list act_address
 *        int      noop_pos
 * Output:
 * Strutture dati principali: GpG
 *                            gef_conn
 *                            FtConn
 *                            constraint_list trated_c_l[]
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: insert_treated_noop_chain
**
*  Name: insert_treated_fact
*  Objective: to insert a node in the Array of the inconsistenze (unsup_fact[ ]) for the noop
*  Type: void
*  Input: register ActNode_list act_address
*         int      noop_pos
*  Output:
*  Main Data Structures: GpG
*                        gef_conn
*                        FtConn
*                        constraint_list trated_c_l[ ]
*  Main Functions Used: none
*  Call gives: insert_treated_noop_chain
**/
void insert_treated_fact (register ActNode_list act_address, int noop_pos)
{
  /** 
    Variabili di appoggio 
    **
    Variables of support
  **/
  EfConn *op_address;
  int level;
  NoopNode_list inf_address;

#ifdef __TEST__
  char *name;
#endif

  /** 
    Assegno a op_aggress (tipo Ftconn) le caratteristiche della noop passata in ingresso 
    **
    I assign to op_aggress (Ftconn type) the characteristics of the noop last in input
  **/
  op_address = CONVERT_ACTION_TO_VERTEX (act_address->position);

#ifdef __TEST__
  name = op_address->name;
#endif

  /** 
    Ricavo il livello nel piano della struttura act_address 
    **
    Revenue the level in the plan of the structure act_address
  **/
  level = *act_address->level;
  /** 
    Ricavo l'inform relativo alla mia noop dalla posizione associata ad essa e al livello 
    in cui e' situata 
    **
    Revenue the inform relative to mine noop from the position associated to it and to the level
    in which is situated
  **/
  inf_address = CONVERT_NOOP_TO_NODE (noop_pos, level);
  /** 
    Controllo che la noop non sia gia' inserita nel vettore delle non non supportate (treated_c_l) 
    **
    Control that the noop is not alrewdy inserted in the array of not supported (treated_c_l)
  **/
  if (inf_address->false_position >= 0) {
    
#ifdef __TEST__
    printf ("\nError FALSE NOT INSERT   ");
    printf ("%s    false pos %d, false_acts %d false_facts %d noop_pos %d",
	    print_op_name_string (inf_address->position, temp_name),
	    inf_address->false_position, GpG.num_false_act,
	    GpG.num_false_fa, noop_pos);
#endif
    return;
  }
  
  /** 
    Se il vettore treated_c_l e' vuoto lo creo associandogli spazio in memoria 
    **
    If the treated_c_l array is empty I create it whith some space in memory
  **/
  if (treated_c_l[GpG.num_false_act] == NULL)
    treated_c_l[GpG.num_false_act] =
      (constraints_list) malloc (sizeof (constraints));
  /** 
    Associo al campo action del vettore treated_c_l (relativo alla noop inserita) l'azione 
    che ha causato la falsita' della noop 
    **
    I associate to the action field of the treated_c_l array (relative to the noop inserted) the action
    that has caused the falsity of the noop
  **/
  treated_c_l[GpG.num_false_act]->action = act_address->position;
  /** 
    Associo al campo fact il fatto associato alla noop 
    **
    I associate to the field fact the fact associated to the noop
  **/
  treated_c_l[GpG.num_false_act]->fact = noop_pos;
  /** 
    Associo al campo constraint_type il tipo di vincolo 
    **
    I associate to the field constraint_type the type of tie
  **/
  treated_c_l[GpG.num_false_act]->constraint_type = C_T_TREATED_CL;
  /** 
    Associo al campo level il livello dell'azione che ha causato l'esclusione della noop 
    **
    I associate to the field level the level of the action that has caused the exclusion of the noop
  **/
  treated_c_l[GpG.num_false_act]->level = act_address->level;
  treated_c_l[GpG.num_false_act]->supported_facts_relaxed_plan_bit_vector=NULL;
  treated_c_l[GpG.num_false_act]->relaxed_plan_actions_bit_vector=NULL;

  act_address->false_position = GpG.num_false_act;

  define_supported_fact_for_relaxed_plan_of_inconsistences(treated_c_l[GpG.num_false_act], TRUE);


  /** 
    Aggiorno il campo false position dell'inform relativo all noop 
    **
    I update the field false position of the inform relative all noop
  **/
  CONVERT_NOOP_TO_NODE (noop_pos, *inf_address->level)->false_position =    GpG.num_false_act++;
  if (DEBUG3 && num_try > 0)
    printf ("\n New Treated Noop: %s   Level %d ",
	    print_noop_name_string (noop_pos, temp_name), level);

  /** 
    Controllo sul numero massimo di treated noop 
    **
    Control on the maximum number of treated noop
  **/
  if (GpG.num_false_act >= MAX_FALSE) {	
#ifdef __MY_OUTPUT__
   MSG_ERROR ( WAR_MAX_FALSE );
#else
    printf( WAR_MAX_FALSE );
#endif    
    exit (1);
  }
  
#ifdef __TEST__
  printf
    ("\n INSERT FALSE  action %s, noop %s, false_actions %d false_fact %d level %d",
     name, print_noop_name_string (noop_pos, temp_name), GpG.num_false_act,
     GpG.num_false_fa, *inf_address->level);
  printf ("\n Insert false end %d", level);

#endif

}





/*********************************************
            ACTION SUBGRAPH
**********************************************/


/** OK 23-07-04
 * Name: insert_action_in_vectlevel
 * Scopo: inserire una azione nell'action subgraph
 * Tipo: int
 * Input: int act_pos (posizione dell'azione)
 *        int level (livello a cui dovrebbe essere inserita l'azione)
 * Output: nessuno
 * Strutture dati principali: inform
 *                            geff_conn
 *                            EfConn
 *                            GpG
 *                            vectlevel
 *                            unsup_fact (viene modificata tramite chiamata da funzione)
 *                            treated_c_l (viene modificata tramite chiamata da funzione)
 * Funzioni principali utilizzate: apply_numeric_effects_of_action
 *                                 compute_dg_heuristic_for_action
 *                                 up_vectlevel
 *                                 insert_time
 *                                 get_action_time
 *                                 is_fact_in_delete_effects_start
 *                                 backward_precond_propagation
 *                                 check_value
 *                                 is_fact_in_preconditions
 *                                 is_fact_in_preconditions_overall
 *                                 remove_backward_noop_chain
 *                                 get_action_cost
 *                                 get_total_time_plan
 *                                 set_computed_dg_costs
 *                                 clean_unsup_num_fact
 *                                 forward_noop_propagation
 *                                 is_fact_in_additive_effects
 *                                 remove_false_fact
 *                                 remove_noop
 *                                 insert_unsup_fact
 *                                 is_num_prec_satisfied
 *                                 noop_remotion_time
 *                                 forward_noop_remotion
 *                                 insert_unsup_numeric_fact
 *                                 insert_treated_noop_chain
 * Chiamata da: insert_remove_action
**
*  Name: insert_action_in_vectlevel
*  Objective: to insert one action in the action subgraph
*  Type: int
*  Input: int act_pos (position of the action)
*         int level (level to which the action would have to be inserted)
*  Output: none
*  Main Data Structures: inform
*                        geff_conn
*                        EfConn
*                        GpG
*                        vectlevel
*                        unsup_fact (it comes modified through call from function)
*                        treated_c_l (it comes modified through call from function)
* Main Functions Used: apply_numeric_effects_of_action
*                      compute_dg_heuristic_for_action
*                      up_vectlevel
*                      insert_time
*                      get_action_time
*                      is_fact_in_delete_effects_start
*                      backward_precond_propagation
*                      check_value
*                      is_fact_in_preconditions
*                      is_fact_in_preconditions_overall
*                      remove_backward_noop_chain
*                      get_action_cost
*                      get_total_time_plan
*                      set_computed_dg_costs
*                      clean_unsup_num_fact
*                      forward_noop_propagation
*                      is_fact_in_additive_effects
*                      remove_false_fact
*                      remove_noop
*                      insert_unsup_fact
*                      is_num_prec_satisfied
*                      noop_remotion_time
*                      forward_noop_remotion
*                      insert_unsup_numeric_fact
*                      insert_treated_noop_chain
* Call gives: insert_remove_action
**/
int insert_action_in_vectlevel (int act_pos, int level)
{
  /** 
    Variabili di appoggio 
    **
    Variable of support
  **/
  register int temp, k, count;
  /** 
    el,cel sono interi usati per determinare il tipo di fatti della nostra azione 
    **
    el, cel integer they are used to determine the type of facts of our action
  **/
  int el, cel, next_level, i, j, jk;
  int nullcost;

  FctNode_list infEl;
  FctNode_list add_effect;
  ActNode_list infAction;
  NoopNode_list infNoop = NULL;

  /** 
    act struttura che portera' le informazioni relative all'azione che vogliamo inserire 
    nell'action subgraph 
    **
    act structure that will carry the relative information to the action that we want to insert
    in the action subgraph
  **/
  EfConn *act;
  /** 
    float di appoggio che useremo per aggiornare il costo del piano dovuto all'inserimento 
    dell'azione nell'action subgraph 
    **
    float of support that we will use to update the cost of the which had plan to the insertion
    of the action in the action subgraph
  **/
  float temp_cost;

  if (FALSE && !CHECK_ACTION_POS(act_pos, level))
    {
#ifdef __MY_OUTPUT__
      printf("\nWarnig : action %s cannot be inserted at level %d (min level = %d)", print_op_name_string(act_pos, temp_name), level, gef_conn[act_pos].level);
#endif
      return 0;
    }

  if (DEBUG6 && num_try > -2000)
    print_actions_in_subgraph ();
  if (DEBUG6 && num_try > -2000)
    {
      print_unsup_fact_vect ();
      print_unsup_num_facts ();
      print_unsup_timed_fact ();
    }
  /** 
    Se il livello e' maggiore di zero, il livello e' occupato da una azione, il livello precedente 
    e' vuoto, il livello precedente puo' contenere l'azione act_pos inserisco l'azione nel livello precedente 
    **
    If the level is greater than zero, the level is occupied from one action, the previous level
    is empty, the previous level can contain the action act_pos I insert the action in the previous level
  **/
  if (level > 0 && vectlevel[level]->action.position >= 0
      && vectlevel[level - 1]->action.position < 0
      && CHECK_ACTION_POS (act_pos, level - 1)
      && (level - 1) > gef_conn[act_pos].level)
    {
      level--;	/**
		   inserisco l'azione nel livello precedente
		   **
		   I insert the action in the previous level
		**/
    }
  else
    if (vectlevel[level]->action.position >= 0
	|| level == GpG.curr_plan_length)
      {
	if (level >= MAX_PLAN_LENGTH) {	

#ifdef __MY_OUTPUT__
	  MSG_ERROR ( WAR_MAX_PLAN_LENGTH );
#else
	  printf( WAR_MAX_PLAN_LENGTH );
#endif    
	  exit (0);
	}
	
	up_vectlevel (level);	/**
				  Espando di livello ed inserisco in level
				  **
				  I expand of level and I insert in level
				**/
      }
  


  vectlevel[level]->action.being_removed = TRUE;
  vectlevel[level]->action.position = act_pos;
  /** 
    Dalla posizione (act_pos) ricaviamo l'EfConn *act e dal livello (level) ricaviamo 
    l'inform relativo all'azione 
    **
    From the position (act_pos) we gain the EfConn *act and from the level (level) we gain
    the inform relative to the action
  **/
  act = CONVERT_ACTION_TO_VERTEX (act_pos);
  infAction = GET_ACTION_OF_LEVEL (level);
  /** 
    Se il livello level e' piu' lungo della lunghezza del piano visualizza messaggio d'errore 
    **
    If the level level is more long of the length of the plan it gives an error message
  **/
  if (level >= GpG.curr_plan_length){

#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else
    printf( WAR_BUG );
#endif

  }


  /**
     Aggiorno le info sul prossimo/precedente livello non vuoto
     **
     I update the infos of the next/previous not empty level
   **/
  update_next_and_prev(level, C_T_INSERT_ACTION);

  /**
    Se l'azione è nel subgraph, la rimuoviamo, altrimenti se non è nel subgraph, la inseriamo
    **
    If the action is in the subgraph, we want to remove it,
    else if the action is not in the subgraph, we want to insert it.  
  **/
  if ((DEBUG1 && num_try > -2000) || DEBUG2)
    {

      printf ("\n\n %d *** INSERT ACTION: level %d   action %d : ",GpG.count_num_try, level,act->position );
      print_op_name (act->position);
      printf(" duration %.2f ", get_action_time(act->position,level));

      if (DEBUG1 && !DEBUG2 && num_try > 0)
	printf ("  num_try %d total_num_try %d", num_try,GpG.count_num_try );

#ifdef __TEST__
      printf ("\nIRA--IA  is_used %d time %d pos %d num_try %d action :",
	      infAction->w_is_used, level, infAction->position, num_try);
      print_op_name (act->position);

#endif
    }

#ifdef __TEST__
  fprintf (stderr, "\nIRA--IA %s is_used %d time %d pos %d  num_try %d",
	   print_op_name_string (act->position, temp_name),
	   infAction->w_is_used, level, infAction->position,
	   GpG.count_num_try);

#endif

  /** 
    Inseriamo l'azione nell'Action_Subgraph 
    **
    We insert the action in the Action_Subgraph
  **/
  /** 
    Aumenta il numero di azioni presenti nel piano aumentando il campo num_actions in GpG e vectlevel 
    **
    It increases to the number of actions in the plan increasing the field num_actions in GpG and vectlevel
  **/
  GpG.num_actions++;
  vectlevel[level]->num_actions++;

  /** 
    Aggiorniamo il costo totale del piano 
    **
    We update to the total cost of the plan
  **/
  temp_cost = get_action_cost (infAction->position, *infAction->level, &nullcost);
  GpG.total_cost += temp_cost;
  if (!nullcost)
    GpG.total_cost_from_metric += temp_cost; 

  /** 
    Aggiorno w_is_used a 1, rappresentante l'inserimento dell'azione nell'action subgraph 
    **
    I update w_is_used to 1, representing the insertion of the action in the action subgraph
  **/
  infAction->w_is_used = 1;	// boolean: the action is in the planning graph now

  /** 
    Aggiorno w_is_goal a 1, che rappresenta la presenza di un effetto additivo che e' anche 
    precondizione 
    **
    I update w_is_goal to 1, that represents the presence of an additive effect that is also
    precondition
  **/
  infAction->w_is_goal = 1;  /** 
			      La utilizzo per identificare le azioni che appartengono 
			      ad una catena di link causali
			      **
			      I use it to identify the actions that belong
			      to one chain of link motives
			   **/

  /** 
    Effetti additivi 
    **
    Additive effects
  **/
  /** 
    Aggiorniamo gli effetti additivi dovuti all'inserimento dell'azione nel livello successivo 
    **
    We update the additive effects due to the insertion of the action in the successive level
  **/
  next_level = level + 1;
  if (gef_conn[act_pos].sf != NULL)
    {

      /** 
	Effetti Additivi A_START 
	**
	Additive AT_START Effects
      **/
      for (j = 0; j < gef_conn[act_pos].sf->num_A_start; j++)
	{
	  /** 
	    cel riceve l'intero corrispondente al tipo di effetto additivo presente nella 
	    struttura geff_conn 
	    **
	    cel receives the correspondent integer to the type of additive effect in the
	    structure geff_conn
	  **/
	  cel = gef_conn[act_pos].sf->A_start[j];
	  /** 
	    gli effetti numerici verranno considerati successivamente
	    **
	    the numerical effects will be considered subsequently
	  **/
	  if (cel < 0)
	    continue;
	  /** 
	    add_effect e' l'effetto additivo posto in forma inform descrivente le proprie caratteristiche 
	    **
	    add_effect is the effect additive placed to inform form describing the own characteristics
	  **/
	  add_effect = CONVERT_FACT_TO_NODE (cel, next_level);
	  /** 
	    se il fatto e' negli effetti cancellanti 
	    **
	    if the fact is in the cancelling effects
	  **/
	  if (is_fact_in_delete_effects (act_pos, cel))
	    {

	      /* ADD_START - DEL_END */
	      vectlevel[level]->noop_act[cel].w_is_overall = ADD_DEL;

	      /** 
		Se il fatto e' precondizione allora viene minacciato 
		**
		If the fact is precondition then comes threatened
	      **/
	      if (vectlevel[level]->fact_vect[GUID_BLOCK (cel)] & vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		insert_treated_noop_chain (infAction, cel);

	      
	      /** 
		Se il fatto non e' precondizione allora togliamo la catena informativa 
		**
		If the fact is not precondition then we remove the informative chain
	      **/
	      if (vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		{
		  if (!is_fact_in_preconditions(GET_ACTION_POSITION_OF_LEVEL (level), cel)
		      && !is_fact_in_preconditions_overall(GET_ACTION_POSITION_OF_LEVEL (level), cel)
		      && !is_fact_in_preconditions_end(GET_ACTION_POSITION_OF_LEVEL (level), cel) )
		    /** 
		      propagation = 0 per evitare di cancellare l'azione che stiamo inserendo
		      **
		      propagation = 0 to avoid to cancel the action that we are inserting
		    **/
		    backward_precond_remotion (add_effect, 0);

		  else
		    {
		      /** 
			se il fatto e' nelle precondizioni non stiamo a togliere e rimettere la catena informativa.
			Correggiamo solo w_is_goal del livello che sta a significare il numero di azioni di cui is precondizione 
			**
			if the fact is in the preconditions we do not remove and replace the informative chain.
			We only correct w_is_goal of the level that means the number of actions of which is precondition
		      **/
		      vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] &=	~GUID_MASK (cel);
		      vectlevel[level]->noop_act[cel].w_is_goal--;
		      vectlevel[level]->fact[cel].w_is_overall = PREC_DEL;
		    }
		}

	      /** 
		Se la NOOP non e' nel piano parziale allora viene inserita 
		**
		If the NOOP is not in the partial plan then it is inserted
	      **/
	      if (!vectlevel[level]->noop_act[cel].w_is_used)
		{
		  vectlevel[level]->noop_act[cel].w_is_used++;
		  vectlevel[level]->noop_act_vect[GUID_BLOCK (cel)] |= GUID_MASK (cel);
		}

	      else
		{/** 
		   Noop inserita 
		   **
		   Inserted Noop
		 **/
		  /** 
		    Decremento i contatori del fatto 
		    **
		    I decrement the counters of the fact
		  **/
		  add_effect->w_is_true--;
		  
		  /** 
		    Se il fatto e' diventato falso (non supportato) 
		    **
		    If the fact is become false (not supported)
		  **/
		  if (add_effect->w_is_true == 0)
		    {
		      /**
			Aggiorno i predicati derivati
			**
			Updating the derivates predicates
		      **/
		      calc_new_derived_predicates(cel, level + 1, DEL_FACT, NULL);
		      vectlevel[level + 1]->fact_vect[GUID_BLOCK (cel)] &= ~(GUID_MASK (cel));
		      vectlevel[level + 1]->true_crit_vect[GUID_BLOCK (cel)] &= ~GUID_MASK (cel);
		      if (add_effect->w_is_goal <= 0)
			vectlevel[level + 1]->false_crit_vect[GUID_BLOCK (cel)] &=  ~GUID_MASK (cel);

		      else
			vectlevel[level +
				  1]->false_crit_vect[GUID_BLOCK (cel)] |=
			  GUID_MASK (cel);
		      vectlevel[level + 1]->num_fact--;
		      if (add_effect->w_is_used)
			insert_unsup_fact (add_effect);
		    }
		  /** 
		    Aggiorniamo il tempo relativo alla noop 
		    **
		    We update the relative time to the noop
		  **/
		  noop_remotion_time (CONVERT_NOOP_TO_NODE (cel, level));
		  /** 
		    Rimuoviamo la noop dal livello successivo 
		    **
		    We remove the noop from the successive level
		  **/
		  forward_noop_remotion (cel, level + 1);
		  
		}
	    }

	  else
	    {	/** 
		  Non esiste l'effeto cancellante AT_END 
		  **
		  The AT_END does not exist effeto cancelling
		**/

	      /** 
		  ADD_START - NOT DEL_END 
	      **/
	      vectlevel[level]->noop_act[cel].w_is_overall = ADD_NDEL;
	      /** 
		se il fatto e' mutuamente esclusivo 
		**
		if the fact is mutually exclusive
	      **/
	      if (check_mutex_noop (cel, level) >= 0
		  && vectlevel[level]->
		  noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		{
		  /** 
		    Se il fatto e' precondizione allora viene minacciato 
		    **
		    If the fact is precondition then comes threatened
		  **/
		  if (vectlevel[level]->fact_vect[GUID_BLOCK (cel)] & vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		    insert_treated_noop_chain (infAction, cel);
		  if (vectlevel[level]->
		      noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		    {
		      /** 
			Se il fatto non e' precondizione allora togliamo la catena informativa 
			**
			If the fact is not precondition then we remove the informative chain
		      **/
		      if (!is_fact_in_preconditions (GET_ACTION_POSITION_OF_LEVEL (level), cel) && 
			  !is_fact_in_preconditions_overall(GET_ACTION_POSITION_OF_LEVEL (level), cel) &&
			  !is_fact_in_preconditions_end(GET_ACTION_POSITION_OF_LEVEL (level), cel))
			backward_precond_remotion (add_effect, 0);

		      else
			{
			  /** 
			    se il fatto e' nelle precondizioni non stiamo a togliere e rimettere la catena informativa.
			    Correggiamo solo w_is_goal del livello 
			    **
			    if the fact is in the preconditions we do not remove and replace the informative chain.
			    We only correct w_is_goal of the level
			  **/
			  vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] &= ~GUID_MASK (cel);
			  vectlevel[level]->noop_act[cel].w_is_goal--;
			  vectlevel[level]->fact[cel].w_is_overall = PREC_DEL;
			}
		    }
		}
	      /** 
		Se la NOOP non e' nel piano parziale allora viene inserita 
		**
		If the NOOP is not in the partial plan then it is inserted
	      **/
	      if (!vectlevel[level]->noop_act[cel].w_is_used)
		{
		  vectlevel[level]->noop_act[cel].w_is_used++;
		  vectlevel[level]->noop_act_vect[GUID_BLOCK (cel)] |=
		    GUID_MASK (cel);
		  add_effect->w_is_true++;
		}
	      /** 
		se solo una azione supporta il fatto 
		**
		if only an action supports the fact
	      **/
	      if (add_effect->w_is_true <= 2)
		{
		  /**
		    Aggiorno i predicati derivati
		    **
		    Updating the derivates predicates
		  **/
		  calc_new_derived_predicates(cel, next_level, ADD_FACT, NULL);
		  vectlevel[next_level]->fact_vect[GUID_BLOCK (cel)] |= GUID_MASK (cel);
		  vectlevel[next_level]->num_fact++;
		  if (add_effect->w_is_goal)
		    {
		      /** 
			se il fatto e' supportato da una sola azione 
			**
			if the fact is supported from one single action
		      **/
		      if (add_effect->w_is_true == 1)
			{
			  /** 
			    rimozione del fatto falso 
			    **
			    removal of the false fact
			  **/
			  remove_false_fact (add_effect);
			  /** 
			    decremento del numero delle precondizioni soddisfatte 
			    **
			    decrement of the number of the satisfied preconditions
			  **/
			  GpG.num_prec -= add_effect->w_is_goal;
			  vectlevel[next_level]->
			    false_crit_vect[GUID_BLOCK (cel)] &=
			    ~(GUID_MASK (cel));
			  vectlevel[next_level]->
			    true_crit_vect[GUID_BLOCK (cel)] |=
			    GUID_MASK (cel);
			}

		      else
			/** 
			  rimozione del fatto dal vettore true_critic_vect siccome non e' piu' critico 
			  **
			  removal of the fact from the array true_critic_vect because it is not more critical
			**/
			vectlevel[next_level]->
			  true_crit_vect[GUID_BLOCK (cel)] &=
			  ~(GUID_MASK (cel));
		    }
		}
	      if (add_effect->w_is_true == 1) {

		/** 
		  per ogni effetto additivo "nuovo" propaghiamo la noop da esso generato 
		  **
		  for every "new" additive effect we propagate the noop it generated
		**/
		forward_noop_propagation (cel, next_level);
	
	      }
	    }
	}			//end for

      /** 
	Effetti Cancellanti AT_START 
	**
	Cancelling Effects AT_START
      **/
      for (j = 0; j < gef_conn[act_pos].sf->num_D_start; j++)
	{
	  /** 
	    cel riceve l'intero corrispondente al tipo di effetto cancellante presente nella struttura geff_conn 
	    **
	    cel receives the integer correspondent to the type of cancelling effect in the structure geff_conn
	  **/
	  cel = gef_conn[act_pos].sf->D_start[j];
	  /** 
	    gli effetti numerici verranno considerati successivamente
	    **
	    the numerical effects will be considered subsequently
	  **/
	  if (cel < 0)
	    continue;
	  add_effect = CONVERT_FACT_TO_NODE (cel, next_level);
	  /** 
	    add_effect e' l'effetto cancellante posto in forma inform descrivente le proprie caratteristiche 
	    **
	    add_effect is the cancelling effect placed in inform form describing the own characteristics
	  **/
	  if (is_fact_in_additive_effects (act_pos, cel))
	    {

	      /* DEL_START - ADD_END */
	      vectlevel[level]->noop_act[cel].w_is_overall = DEL_ADD;
	      /** 
		Se il fatto e' precondizione allora togliamo la catena informativa 
		**
		If the fact is precondition then we remove the informative chain
	      **/
	      if (vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		{
		  if (!is_fact_in_preconditions(GET_ACTION_POSITION_OF_LEVEL (level), cel))
		    backward_precond_remotion (add_effect, 0);

		  else
		    {
		      /** 
			se il fatto e' nelle precondizioni non stiamo a togliere e rimettere la catena informativa.
			Correggiamo solo w_is_goal del livello che sta a significare il numero di azioni di cui e' precondizione 
			**
			if the fact is in the preconditions we do not remove and replace the informative chain.
			We only correct w_is_goal of the level that means the number of actions of which is precondition
		      **/
		      vectlevel[level]-> noop_prec_act_vect[GUID_BLOCK (cel)] &= ~GUID_MASK (cel);
		      vectlevel[level]->noop_act[cel].w_is_goal--;
		      vectlevel[level]->fact[cel].w_is_overall = PREC_DEL;
		    }
		}

	      /** 
		Se la NOOP e' inserita allora deve essere tolta 
		**
		If the NOOP is inserted then must be removed
	      **/
	      if (vectlevel[level]->noop_act[cel].w_is_used > 0)
		{
		  vectlevel[level]->noop_act[cel].w_is_used--;
		  vectlevel[level]->noop_act_vect[GUID_BLOCK (cel)] &=
		    ~(GUID_MASK (cel));
		}

	      else
		{  /**
		     la noop non e' inserita
		     **
		     the noop is not inserted
		   **/
		  /** 
		    se l'effetto cancellante non e' supportato da alcuna azione 
		    **
		    if the cancelling effect is not supported by some action
		  **/
		  if (add_effect->w_is_true++ <= 1)
		    {
		      /** 
			Aggiorno i predicati derivati
			**
			I update the derivates predicates
		      **/ 
		      calc_new_derived_predicates(cel, next_level, ADD_FACT, NULL);
		      /** 
			aggiorniamo in fact_vect con gli effetti additivi dell'azione inserita 
			**
			we dawn in fact_vect with the effects points out you of the inserted action
		      **/ 
		      vectlevel[next_level]->fact_vect[GUID_BLOCK (cel)] |= GUID_MASK (cel);

		      /** 
			aumentiamo il numero di fatti veri nel livello successivo 
			**
			we increase the number of true facts in the successive level
		      **/
		      vectlevel[next_level]->num_fact++;
		      /** 
			se il fatto supporta azioni nei livelli successivi 
			**
			if the fact supports actions in the levels succeeded to you
		      **/
		      if (add_effect->w_is_goal)
			{

			  /** 
			    se il fatto e' critico (supportato da una sola azione) 
			    **
			    if the fact is critical (supported from one single action)
			  **/
			  if (add_effect->w_is_true == 1)
			    {
			      /** 
				rimuovo il fatto falso 
				**
				I remove the false fact
			      **/
			      remove_false_fact (add_effect);
			      /** 
				decremento del numero delle precondizioni soddisfatte 
				**
				decrement of the number of the satisfied preconditions
			      **/
			      GpG.num_prec -= add_effect->w_is_goal;
			      vectlevel[next_level]->
				false_crit_vect[GUID_BLOCK (cel)] &=
				~(GUID_MASK (cel));
			      vectlevel[next_level]->
				true_crit_vect[GUID_BLOCK (cel)] |=
				GUID_MASK (cel);
			    }

			  else
			    /** 
			      rimozione del fatto dal vettore true_critic_vect siccome non e' piu' critico 
			      **
			      removal of the fact from the true_critic_vect array because it is not critical yet
			    **/
			    vectlevel[next_level]->
			      true_crit_vect[GUID_BLOCK (cel)] &=
			      ~(GUID_MASK (cel));
			}

		      /** 
			per ogni effetto cancellante "nuovo" propaghiamo la noop da esso generato 
			**
			for every "new" cancelling effect we propagate the noop generated by it
		      **/
		      forward_noop_propagation (cel, next_level);
		      
		    }
		}
	    }			// end if DEL_START - ADD_END

	  else
	    {

	      /* DEL_START - NOT ADD_END */
	      vectlevel[level]->noop_act[cel].w_is_overall = DEL_NADD;

	      /** 
		Se il fatto e' precondizione allora viene minacciato 
		**
		If the fact is precondition then it is threatened
	      **/
	      if (vectlevel[level]->fact_vect[GUID_BLOCK (cel)] & vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		insert_treated_noop_chain (infAction, cel);
	      if (vectlevel[level]->
		  noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		{

		  /** 
		    Se il fatto non e' precondizione allora togliamo la catena informativa 
		    **
		    If the fact is precondition then we do not remove the informative chain
		  **/
		  if (!is_fact_in_preconditions (GET_ACTION_POSITION_OF_LEVEL (level), cel))
		    backward_precond_remotion (add_effect, 0);

		  else
		    {

		      /** 
			se il fatto e' nelle precondizioni non stiamo a togliere e rimettere la catena informativa.
			Correggiamo solo w_is_goal del livello che sta a significare il numero di azioni di cui e' precondizione 
			**
			if the fact is in the preconditions we do not remove and replace the informative chain.
			We only correct w_is_goal of level that means the number of actions of which is precondition
		      **/
		      vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] &=	~GUID_MASK (cel);
		      vectlevel[level]->noop_act[cel].w_is_goal--;
		      vectlevel[level]->fact[cel].w_is_overall = PREC_DEL;
		    }
		}

	      /** 
		Noop inserita 
		**
		Inserted Noop
	      **/
	      if (vectlevel[level]->noop_act[cel].w_is_used)
		{
		  vectlevel[level]->noop_act[cel].w_is_used--;
		  vectlevel[level]->noop_act_vect[GUID_BLOCK (cel)] &=
		    ~(GUID_MASK (cel));

		  /** 
		    decremento i contatori del fatto 
		    **
		    decrement the fact counters
		  **/
		  add_effect->w_is_true--;
		  if (add_effect->w_is_true == 0)
		    {
		      /**
			Aggiorno i predicati derivati
			**
			Updating the derivates predicates
		      **/
		      calc_new_derived_predicates(cel, level + 1, DEL_FACT, NULL);
		      vectlevel[level + 1]->fact_vect[GUID_BLOCK (cel)] &=
			~(GUID_MASK (cel));
		      vectlevel[level +
				1]->true_crit_vect[GUID_BLOCK (cel)] &=
			~GUID_MASK (cel);
		      if (add_effect->w_is_goal <= 0)
			vectlevel[level +
				  1]->false_crit_vect[GUID_BLOCK (cel)] &=
			  ~GUID_MASK (cel);

		      else
			vectlevel[level +
				  1]->false_crit_vect[GUID_BLOCK (cel)] |=
			  GUID_MASK (cel);
		      vectlevel[level + 1]->num_fact--;
		      if (add_effect->w_is_used)
			insert_unsup_fact (&vectlevel[level + 1]->fact[cel]);
		    }
		  /** 
		    Aggiorniamo il tempo relativo alla noop 
		    **
		    We update the relative time to the noop
		  **/
		  noop_remotion_time (CONVERT_NOOP_TO_NODE (cel, level));
		  /** 
		    Rimuoviamo la noop dal livello successivo 
		    **
		    We remove the noop from the successive level
		  **/
		  forward_noop_remotion (cel, level + 1);
		}
	    }			//end else
	}			// end for
    } //end if(sf)


  
  /** 
    Effetti Cancellanti AT_END 
    **
    Cancelling AT_END Effects
  **/
  for (j = 0; j < gef_conn[act_pos].num_D; j++)
    {
      /** 
	cel riceve l'intero corrispondente al tipo di effetto cancellante presente nella struttura geff_conn 
	**
	cel receives the integer correspondent to the type of cancelling effect in the structure geff_conn
      **/
      cel = gef_conn[act_pos].D[j];
      if (cel < 0)
	continue;

      /** 
	add_effect e' l'effetto cancellante posto in forma inform descrivente le proprie caratteristiche 
	**
	add_effect is the cancelling effect placed in inform form describing the own characteristics
      **/
      add_effect = CONVERT_FACT_TO_NODE (cel, next_level);
      /** 
	se il fatto non e' negli effetti additivi AT_START 
	**
	if the fact is not in the additive effects AT_START effects
      **/
      if (!is_fact_in_additive_effects_start (act_pos, cel))
	{

	  /* DEL_END - NOT ADD_START */
	  vectlevel[level]->noop_act[cel].w_is_overall = NADD_DEL;

	  /** 
	    Se il fatto e' precondizione allora viene minacciato 
	    **
	    If the fact is precondition then it is threatened
	  **/
	  if (vectlevel[level]->fact_vect[GUID_BLOCK (cel)] & vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
	    insert_treated_noop_chain (infAction, cel);

	  if (vectlevel[next_level]->
	      prec_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
	    {
	      
	      /** 
		Se il fatto non e' precondizione allora togliamo la catena informativa 
		**
		If the fact is precondition then we do not remove the informative chain
	      **/
	      if (!is_fact_in_preconditions(GET_ACTION_POSITION_OF_LEVEL (level), cel) &&
		  !is_fact_in_preconditions_overall(GET_ACTION_POSITION_OF_LEVEL (level), cel) &&
		  !is_fact_in_preconditions_end(GET_ACTION_POSITION_OF_LEVEL (level), cel))
		backward_precond_remotion (add_effect, 0);
	      
	      else
		{
		  
		  /** 
		    se il fatto e' nelle precondizioni non stiamo a togliere e rimettere la catena informativa.
		    Correggiamo solo w_is_goal del livello che sta a significare il numero di azioni di cui e' precondizione 
		    **
		    if the fact is in the preconditions we do not remove and replace the informative chain. 
		    We only correct w_is_goal of the level that means the number of actions of which is precondition
		  **/
		  vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] &=	~GUID_MASK (cel);
		  vectlevel[level]->noop_act[cel].w_is_goal--;
		  vectlevel[level]->fact[cel].w_is_overall = PREC_DEL;
		}
	    }
	  /** 
	    Se la noop non e' inserita nell'action_subgraph 
	    **
	    If the noop is not inserted in the action_subgraph
	  **/
	  if (vectlevel[level]->noop_act[cel].w_is_used)
	    
	    /** 
	      Noop inserita
	      **
	      Inserted Noop
	    **/
	    if (add_effect->w_is_true)
	      {
		
		/** 
		  decremento i contatori del fatto che rappresentano il numero di azioni che lo supportano 
		  **
		  I decrement the counters of the fact that represent the number of actions that they support it
		**/
		add_effect->w_is_true--;
		/** 
		  se il fatto non e' piu' supportato 
		  **
		  if the fact is not more supported
		**/
		if (add_effect->w_is_true == 0)
		  {
		    /**
		      Aggiorno i predicati derivati
		      **
		      Updating the derivates predicates
		    **/
		    calc_new_derived_predicates(cel, level + 1, DEL_FACT, NULL);
			vectlevel[level + 1]->fact_vect[GUID_BLOCK (cel)] &=
			  ~(GUID_MASK (cel));
			vectlevel[level +
				  1]->true_crit_vect[GUID_BLOCK (cel)] &=
			  ~GUID_MASK (cel);
			if (add_effect->w_is_goal <= 0)
			  vectlevel[level +
				    1]->false_crit_vect[GUID_BLOCK (cel)] &=
			    ~GUID_MASK (cel);

			else
			  vectlevel[level +
				    1]->false_crit_vect[GUID_BLOCK (cel)] |=
			    GUID_MASK (cel);
			vectlevel[level + 1]->num_fact--;
			if (add_effect->w_is_used)
			  insert_unsup_fact (&vectlevel[level + 1]->
					     fact[cel]);
		  }
		/** 
		  Aggiorniamo il tempo relativo alla noop 
		  **
		  We update the relative time to the noop
		**/
		noop_remotion_time (CONVERT_NOOP_TO_NODE (cel, level));
		forward_noop_remotion (cel, level + 1);
	      }
	}
    }


  /** 
    Effetti additivi AT_END 
    **
    Additive AT_END effects
  **/
  for (j = 0; j < gef_conn[act_pos].num_A; j++)
    {
      /** 
	cel riceve l'intero corrispondente al tipo di effetto additivo presente nella struttura geff_conn 
	**
	cel receives the integer correspondent to the type of additive effect present in the geff_conn structure
      **/
      cel = gef_conn[act_pos].A[j];
      /** 
	Se l'azione e' duratva e il fatto e' un effetto cancellante 
	**
	If the action is duratve and the fact is a cancelling effect
      **/
      if (gef_conn[act_pos].sf
	  && is_fact_in_delete_effects_start (act_pos, cel))
	continue;
      /** 
	gli effetti numerici verranno considerati successivamente
	**
	the numerical effects will be considered subsequently
      **/
      if (cel < 0)
	continue;

#ifdef __TEST__
      if (!CHECK_FACT_POS ((cel = gef_conn[act_pos].A[j]), next_level)){
#ifdef __MY_OUTPUT__
	MSG_ERROR( WAR_BUG );
#else
	printf( WAR_BUG );
#endif
      }
      else
#endif
	
	{
	  /** 
	      Converte il fatto in forma inform 
	      **
	      It converts the fact in inform form
	  **/ 
	  add_effect = CONVERT_FACT_TO_NODE (cel, next_level);
	  /** 
	    se il fatto non e' supportato nei livelli precedenti 
	    **
	    if the fact is not supported in the previous levels
	  **/
	  if (add_effect->w_is_true++ <= 1)
	    {
	      /**
		 Aggiorno i predicati derivati
		 **
		 I update the derivates predicates
	      **/
	      calc_new_derived_predicates(cel, next_level, ADD_FACT, NULL);
	      /** 
		Aggiorna il vettore dei fatti con l'effetto additivo generato dall'azione inserita 
		**
		It updates the array of the facts with the additive effect generated by the inserted action
	      **/
	      vectlevel[next_level]->fact_vect[GUID_BLOCK (cel)] |=
		GUID_MASK (cel);
	      /** 
		Aggiorna il numero di fatti veri nel livello successivo 
		**
		It updates the number of true facts in the successive level
	      **/
	      vectlevel[next_level]->num_fact++;
	      /** 
		Se vi sono azioni di cui il fatto è precondizione 
		**
		If there are actions of which the fact is precondition
	      **/
	      if (add_effect->w_is_goal)
		{
		  /** 
		    Se si tratta di un fatto critico siccome è supportato da una sola azione 
		    **
		    If it is a critical fact because it is supported by a single action
		  **/
		  if (add_effect->w_is_true == 1)
		    {
		      /** 
			Rimozione del fatto falso 
			**
			Removal of the false fact
		      **/
		      remove_false_fact (add_effect);
		      /** 
			Decrementa il numero di precondizioni non soddisfatte 
			**
			It decrements the number of preconditions not satisfied
		      **/
		      GpG.num_prec -= add_effect->w_is_goal;
		      /** 
			Aggiorna il vettore dei fatti critici 
			**
			It updates the array of the critical facts
		      **/
		      vectlevel[next_level]->false_crit_vect[GUID_BLOCK (cel)] &=~(GUID_MASK (cel));
		      vectlevel[next_level]->true_crit_vect[GUID_BLOCK (cel)] |= GUID_MASK (cel);
		    }
		  
		  else
		    {
		      /** 
			Se non si tratta di un fatto critico lo si rimuove dal vettore di fatti critici 
			**
			If it is not a critical fact it is removed from the array of critical facts
		      **/
		      vectlevel[next_level]->
			true_crit_vect[GUID_BLOCK (cel)] &=
			~(GUID_MASK (cel));
		    }
		}
	      /** 
		Per ogni effetto additivo "nuovo" (cioe' fatto reso vero dall'inserimento dell'azione) 
		lo propago in avanti tramite noop 
		**
		For every "new" additive effect (i.e. a fact rendered true from the insertion of the action)
		I propagate in ahead through noop
	      **/
	      if (add_effect->w_is_true == 1) {
		  forward_noop_propagation (cel, next_level);
	      }
	    }
	}
    }
  count = 0;
  
  // ME RELATIONS: set action array
  /** 
    Le mutue esclusioni ci sono solo tra l'azione che stiamo inserendo e le NOOP presenti nel piano parziale 
    **
    The mutual exclusions are only between the action we are inserting and the NOOP in the partial plan
  **/
  /** 
    Inserisco l'azione ed il fatto nella lista delle inconsistenze
    **
    I insert the action and the fact in the list of the inconsistences
  **/
  /**
    Per tutti i fatti, valutiamo lo stato della rispettiva NOOP nel livello... Esistono 3 casi  
    **
    For every fact, we estimate the state of the respective NOOP in the level...  3 cases exist
  **/
  for (i = 0, j = 0, count = 0; j < gnum_ft_conn; i++, j += 32)
    {
     /** 
	1) La NOOP e' precondizione dell'azione e il fatto e' supportato: link causale minacciato  
	**
	1) the NOOP is precondition of the action and the fact is supported: causal link threatened
      **/
      temp =act->ft_exclusive_vect[i] & vectlevel[level]->noop_prec_act_vect[i] & vectlevel[level]->noop_act_vect[i];
      k = 32;
      while (temp)
	{
	  k--;
	  if (temp & FIRST_1
	      && !vectlevel[level]->noop_act[j + k].w_is_overall)
	    {

	      /**
		Se l'azione e' mutex con un timed fact, non si fa nulla
		**
		If the underlying action is mutex with a timed fact, 
		then do not anything
	      **/
	      if(GpG.timed_facts_present)
		if (gft_conn[j+k].fact_type == IS_TIMED)
		{ 
		  temp <<= 1;
		  continue;
		}
	      

	      insert_treated_noop_chain (infAction, j + k);

	      /* 
		 aggiorna LM in caso di mutex
	      */
	      if (GpG.lm_multilevel) 
		update_mutex_multilevel (level,act_pos); 
	      else 
		update_mutex(act_pos);

	    }
	  temp <<= 1;
	}
      
      /** 
	2) La NOOP non e' precondizione dell'azione e il fatto e' supportato: rimuoviamo la NOOP  
	**
	2) the NOOP is not precondition of the action and the fact is supported: we remove the NOOP
      **/
      temp = act->ft_exclusive_vect[i] & vectlevel[level]->noop_act_vect[i];
      k = 32;
      while (temp)
	{
	  k--;
	  if (temp & FIRST_1)
	    {
	      /** 
		se la Me è con una noop, toglie la noop. Chiamo la funzione remove_noop 
		**
		if the Me is with a noop, it removes the noop. I call the function remove_noop
	      **/
	      if(GpG.timed_facts_present)
		if (gft_conn[j+k].fact_type == IS_TIMED)
		{
		    temp <<= 1;
		    continue;
		}
	      


	      //se la Me e' con una noop toglie la noop chiamo la funzione remove_noop

#ifdef __TEST__
	      if (vectlevel[level]->noop_act[j + k].w_is_used <= 0) {
		MSG_ERROR ("Check mutex");
		printf ("\n ERROR: %s act %s ",
			print_op_name_string (act->position, temp_name),
			print_noop_name_string (j + k, temp_name));
	      }
	      
	      else
#endif
		if (!vectlevel[level]->noop_act[j + k].w_is_overall)
		  remove_noop (infAction, j + k);
	    }
	  temp <<= 1;
	}
      
      /** 
	3) La NOOP e' precondizione e la NOOP non  e' inserita: rimuoviamo la catena informativa  
	**
	3) the NOOP is precondition and the NOOP is not inserted: we remove the informative chain
      **/
      temp =act->ft_exclusive_vect[i] & vectlevel[level]->noop_prec_act_vect[i];
      k = 32;
      while (temp)
	{
	  k--;
	  if (temp & FIRST_1 && !vectlevel[level]->noop_act[j + k].w_is_overall)
	    {
	      /* 
		 Se l'azione e' mutex con un timed fact, non si fa nulla
		 *
		 If the underlying action is mutex with a timed fact, 
		 then do not anything
	      */
	      if(GpG.timed_facts_present)
		if (gft_conn[j+k].fact_type == IS_TIMED)
		  {
		    temp <<= 1;
		    continue;
		  }
	      

	      if (!is_fact_in_preconditions (GET_ACTION_POSITION_OF_LEVEL (level), j + k) &&
		  !is_fact_in_preconditions_overall (GET_ACTION_POSITION_OF_LEVEL (level), j + k) &&
		  !is_fact_in_preconditions_end (GET_ACTION_POSITION_OF_LEVEL (level), j + k) )
		remove_backward_noop_chain (infAction, j + k);

	      else
		{
		  jk = j + k;
		  noop_prec_not_in_add (infAction, jk);
		  vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (jk)] &= ~GUID_MASK (jk);
		  vectlevel[level]->noop_act[jk].w_is_goal--;
		  vectlevel[level]->fact[jk].w_is_overall = PREC_DEL;
		}
	    }
	  temp <<= 1;
	}
    }				// end for su tutti i fatti   

  /** 
    Aggiorna il numero di mutue esclusioni 
    **
    It updates the number of mutual exclusions
  **/
  GpG.num_m_e += count;

  // VERIFY PRECONDITIONS
  /** 
    Precondizioni AT_START 
    **
    AT_START preconditions
  **/
  for (j = 0; j < gef_conn[act_pos].num_PC; j++)
    {
       /** 
	 el riceve l'intero corrispondente al tipo di precondizione presente nella struttura geff_conn 
	 **
	 el receives the integer correspondent to the type of precondition in the structure geff_conn
       **/
      el = gef_conn[act_pos].PC[j];
      if (el < 0)
	{
	  /** 
	    segnala che questa precondizione numerica è "rilevante" 
	    **
	    it marks that this numerical precondition is "relevant"
	  **/
	  vectlevel[level]->numeric->w_is_goal[-el] = 1;

	  //cvar, livello
	  if (!is_num_prec_satisfied (-el, level))
	    {

#ifdef __TEST__
	      if (DEBUG3)
		{
		  printf ("\nAction ");
		  print_op_name (act_pos);
		  printf (" level %d", level);
		}
#endif
	      insert_unsup_numeric_fact (-el, level);
	    }
	  continue;
	}


#ifdef __MY_OUTPUT__
      /** 
	Controllo sul tipo di precondizione 
	**
	Control on the type of precondition
      **/

      if (CHECK_FACT_POS (el, level) == FALSE)
	{
	  printf ("\n Error fact_pos %d fact_lev %d, act_pos %d level %d \n", el,gft_conn[el].level, act_pos, level);
	  print_op_name(act_pos);
	  printf(" action level: %d",gef_conn[act_pos].level);
	}
#endif
      
      
      // for each fact that is precondition of this action do...
      // el points to the node of the list of facts that are precond. of 
      // this action.

       /** 
	Converte il fatto (precondizione) in inform 
	**
	Converts the fact (precondition) into inform
      **/
      infEl = CONVERT_FACT_TO_NODE (el, level);

      /** 
	Se il fatto è sia precondizione dell'azione ma non e' effetto cancellante di questa 
	aumento di 1 w_is_goal che rappresenta il numero di azioni di cui il fatto e' precondizione 
	**
	If the fact is both precondition of the action but is not cancelling effect of this
	I increase of 1 w_is_goal that it represents the number of actions of which the fact is precondition
      **/
      if (infEl->w_is_overall != PREC_DEL)
	infEl->w_is_goal++;

      /** 
	Se il fatto è precondizione dell'azione al livello o è precondizione di un'altra azione 
	**
	If the fact is precondition of the action to the level or is precondition of another action
      **/
      if (infEl->w_is_used++ == 0 || infEl->w_is_goal == 1)
	{

	  // Used for the noop  propagation
	  // Update the bit (min)array that stores the precondition of the actions 
	  // in this level of the planning graph.
	  // Set to 1 the facts that are precondition for the inserted action
	  /** 
	    Aggiorna il bit corrispondente nel vettore delle precondizioni per il fatto che 
	    supporta l'azione inserita 
	    **
	    It updates the corresponding bit in the array of the preconditions for the fact that
	    supports the inserted action
	  **/
	  vectlevel[level]->prec_vect[GUID_BLOCK (el)] |= GUID_MASK (el);

	  /** 
	    Se si tratta di un fatto falso (non supportato da azioni nei livelli precedenti)
	    **
	    If it is a false fact (not supported by actions in the previous levels)
	  **/ 
	  if (!infEl->w_is_true)
	    {

	      /** 
		Aggiorna il bit corrispondente al fatto falso critico nel false_vect_critic_vect 
		per l'azione inserita 
		**
		It updates the bit correspondent to the critical false fact in the false_vect_critic_vect
		for the inserted action
	      **/
	      vectlevel[level]->false_crit_vect[GUID_BLOCK (el)] |=
		GUID_MASK (el);

	      /** 
		Siccome si tratta di un fatto falso, viene inserito nell'array dei fatti falsi
		**
		Becaus it is a false fact, it is inserted in the array of the false facts
	      **/
	      insert_unsup_fact (CONVERT_FACT_TO_NODE (el, level));
	    }

	  else
	    /** 
	      Se si tratta di un fatto critico (supportato da una sola azione nei livelli precedenti) 
	      **
	      If it is a critical fact (supported by a single action in the previous levels)
	    **/
	  if (infEl->w_is_true == 1)

	    /** 
	      Aggiorno il vettore dei fatti critici veri per l'azione inserita 
	      **
	      I update the array of the true critical facts for the inserted action
	    **/
	    vectlevel[level]->true_crit_vect[GUID_BLOCK (el)] |=
	      GUID_MASK (el);
	}
      /** 
	Se il fatto è precondizione e effetto cancellante dall'azione inserisco la catena informativa 
	**
	If the fact is precondition and cancelling effect by the action I insert the informative chain
      **/ 
      if (infEl->w_is_overall != PREC_DEL)
	backward_precond_propagation (infEl);

      else
	infEl->w_is_overall = 0;

      /** 
	Se la precondizione non è supportata incremento il numero di precondizioni non supportate
	(GpG.num_prec) e il numero di precondizioni inconsistenti relative all'azione (count) 
	**
	If the precondition is not supported I increment the number of preconditions not supported
	(GpG.num_prec) and the number of relative inconsistent preconditions to the action (count)
      **/
      if (!infEl->w_is_true)
	{
	  count++;
	  GpG.num_prec++;
	}

      // LM  Tengo aggiornato il valore di lamda_prec di fatti precondizione
      CONVERT_FACT_TO_VERTEX (el)->lamda_prec =
	check_value (CONVERT_FACT_TO_VERTEX (el)->lamda_prec +
		     CONVERT_ACTION_TO_VERTEX (act_pos)->lamda_prec);
    }

  /** 
    Azioni durative 
    **
    Durative actions
  **/
  if (gef_conn[act_pos].sf != NULL)
    {

      /**
         Precondizioni OVER_ALL
	 **
	 OVER_ALL preconditions
      **/
      for (j = 0; j < gef_conn[act_pos].sf->num_PC_overall; j++)
	{
	  /** 
	      el riceve l'intero corrispondente al tipo di precondizione presente nella struttura geff_conn 
	      **
	      el receives the integer correspondent to the type of precondition in the structure geff_conn
	  **/
	  el = gef_conn[act_pos].sf->PC_overall[j];
	  if (el < 0)
	    {
	      /** 
		segnala che questa precondizione numerica è "rilevante"
		**
		it marks that this numerical precondition is "relevant"
	      **/
	      vectlevel[level]->numeric->w_is_goal[-el] = 1;

	      //cvar, livello
	      if (!is_num_prec_satisfied (-el, level))
		{

#ifdef _NUM_PREC_
		  printf ("Azione ");
		  print_op_name (act_pos);

#endif
		  insert_unsup_numeric_fact (-el, level);
		}
	      continue;
	    }

	  if(GpG.timed_facts_present)
	    {
	      if (gft_conn[el].fact_type == IS_TIMED)
		continue;
	    }


#ifdef __MY_OUTPUT__
	  /** 
	    Controllo sul tipo di precondizione 
	    **
	    Control on the type of precondition
	  **/

	  if (CHECK_FACT_POS (el, level) == FALSE)
	    printf("\n Error fact_OVERALL_pos %d fact_lev %d, act_pos %d level %d num_try %d ",el, gft_conn[el].level, act_pos, level, GpG.count_num_try);
#endif
	  	
	  infEl = CONVERT_FACT_TO_NODE (el, level);
	  infNoop = CONVERT_NOOP_TO_NODE (el, level);

	  /** 
	    Se la precondizione OVERALL e' un effetto additivo AT_START della stessa azione allora non è un'inconsistenza 
	    **
	    If the OVERALL precondition is an additive AT_START effect of the same action, then it is not an inconsistence
	  **/
	  if (infNoop->w_is_overall != ADD_DEL
	      && infNoop->w_is_overall != ADD_NDEL)
	    {
	      /** 
		Se la precondizione OVERALL non è un effetto cancellante dell'azione allora aumento 
		il numero di azioni di cui questo fatto e' precondizione 
		**
		If th OVERALL precondition is not a cancelling effect of the action, then I increase
		the number of actions of which this fact is precondition
	      **/
	      if (infEl->w_is_overall != PREC_DEL)
		infEl->w_is_goal++;
	      /** 
		Se il fatto è precondizione dello stesso livello o supporta una azione 
		nei livelli successivi
		**
		If the fact is precondition of the same level or supports one action
		in the successive levels
	      **/
	      if (infEl->w_is_used++ == 0 || infEl->w_is_goal == 1)
		{
		  /** 
		    Aggiorno il vettore delle precondizioni non soddisfatte 
		    **
		    I update the array of the preconditions not satisfied
		  **/ 
		  vectlevel[level]->prec_vect[GUID_BLOCK (el)] |=
		    GUID_MASK (el);

		  /** 
		    Se il fatto è un fatto critico falso aggiorno il vettore dei fatti falsi 
		    critici e lo inserisco nel'array dei fatti falsi
		    **
		    If the fact is critical I update the array of the false facts
		    critics and I insert it in the array of the false facts
		  **/ 
		  if (!infNoop->w_is_used)
		    {
		      /** 
			Aggiornamento del vettore dei fatti falsi critici 
			**
			Updating of the array of the false critics facts
		      **/
		      vectlevel[level]->false_crit_vect[GUID_BLOCK (el)] |=
			GUID_MASK (el);
		      /** 
			Inserimento del fatto falso nell'array dei fatti falsi 
			**
			Insertion of the false fact in the array of the false facts
		      **/
		      insert_unsup_fact (CONVERT_FACT_TO_NODE (el, level));
		    }

		  else
		  /** 
		    Se il fatto e' un fatto critico vero aggiorno il vettore dei fatti critici veri 
		    **
		    If the fact is a true critical fact I update the array of the critical true facts
		  **/  
		  if (infEl->w_is_true == 1)

		    // Update the bit array of the false critical facts
		    vectlevel[level]->true_crit_vect[GUID_BLOCK (el)] |=
		      GUID_MASK (el);
		}		// if infEl->w_is_used
	      /** 
		Se il fatto è precondizione e effetto cancellante dell'azione inserisco la catena informativa  
		**
		If the fact is precondition and cancelling effect of the action I insert the informative chain
	      **/
	      if (infEl->w_is_overall != PREC_DEL)
		backward_precond_propagation (infEl);

	      else
		infEl->w_is_overall = 0;
	      /** 
		Se la precondizione non è supportata incremento il numero di precondizioni non 
		supportate (GpG.num_prec) e il numero di precondizioni inconsistenti relative all'azione (count) 
		**
		If the precondition is not supported I increment the number of preconditions not
		supported (GpG.num_prec) and the number of relative inconsistent preconditions to the action (count)
	      **/
	      if (!infEl->w_is_true)
		{
		  count++;
		  GpG.num_prec++;
		}

	      // LM  Tengo aggiornato il valore di lamda_prec di fatti precondizione
	      CONVERT_FACT_TO_VERTEX (el)->lamda_prec =
		check_value (CONVERT_FACT_TO_VERTEX (el)->lamda_prec +
			     CONVERT_ACTION_TO_VERTEX (act_pos)->lamda_prec);
	    }
	} // end for OVERALL

      /**
        Precondizione AT_END
	**
	AT_END precondition
       **/
      for (j = 0; j < gef_conn[act_pos].sf->num_PC_end; j++)
	{
	  /** 
	    el riceve l'intero corrispondente al tipo di precondizione presente nella struttura geff_conn 
	    **
	    el receives the integer correspondent to the type of precondition in the structure geff_conn
	  **/
	  el = gef_conn[act_pos].sf->PC_end[j];

	  if (el < 0)
	    {
	      /** 
		segnala che questa precondizione numerica è "rilevante" 
		**
		it marks that this numerical precondition is "relevant"
	      **/
	      vectlevel[level]->numeric->w_is_goal[-el] = 1;

	      //cvar, livello
	      if (!is_num_prec_satisfied (-el, level))
		{

#ifdef _NUM_PREC_
		  printf ("Azione ");
		  print_op_name (act_pos);

#endif
		  insert_unsup_numeric_fact (-el, level);
		}
	      continue;
	    }

	  if(GpG.timed_facts_present)
	    {
	      if (gft_conn[el].fact_type == IS_TIMED)
		continue;
	    }

	  // PREC_END FIX
	  //	  if (CHECK_FACT_POS (el, next_level) == FALSE)
	  //	    printf("\n Error fact_AT_END__pos %d fact_lev %d, act_pos %d level %d ",el, gft_conn[el].level, act_pos, next_level);

#ifdef __MY_OUTPUT__
	  if (CHECK_FACT_POS (el, level) == FALSE)
	    printf("\n Error fact_AT_END__pos %d fact_lev %d, act_pos %d level %d ",el, gft_conn[el].level, act_pos, level);
#endif
	  
	  /** 
	    Converte il fatto in inform 
	    **
	    It converts the fact in inform
	  **/
	  infEl = CONVERT_FACT_TO_NODE (el, level);
	  infNoop = CONVERT_NOOP_TO_NODE (el, level);

	  /** 
	    Se la prec AT_END e' un effetto additivo AT_END della stessa azione oppure e' un effetto 
	    additivo AT_START ma non e' cancellato AT_END dalla stessa azione allora non e' un inconsistenza 
	    **
	    If the AT_END precondition is an additive AT_END effect of the same action or is an effect
	    additive AT_START but is not cancelled AT_END from the same action then is not an inconsistence
	  **/
	  if (infNoop->w_is_overall != ADD_DEL && infNoop->w_is_overall != ADD_NDEL)
	    {
	     /** 
	       Se il fatto e' precondizione e non e' cancellato dall'azione incremento il numero di 
	       azioni che supporta (rappresentato da w_is_goal) 
	       **
	       If the fact is precondition and is not cancelled from the action increment the number of
	       actions that it supports (represented from w_is_goal)
	     **/
	      if (infEl->w_is_overall != PREC_DEL)
		infEl->w_is_goal++;
	      /** 
		  Se il fatto non è precondizione dell'azione ma e' precondizione di una azione nei 
		  livelli successivi 
		  **
		  If the fact is not precondition of the action but is precondition of one action in the
		  levels succeeded
	      **/
	      if (infEl->w_is_used++ == 0 || infEl->w_is_goal == 1)
		{
		  /** 
		    Aggiorno il vettore delle precondizioni non soddisfatte 
		    **
		    I update the array of the preconditions not satisfied
		  **/
		  vectlevel[level]->prec_vect[GUID_BLOCK (el)] |= GUID_MASK (el);
		  /** 
		    Se e' un fatto critico falso 
		    **
		    If is a false critical fact
		  **/
		  if (!infEl->w_is_true)
		    {
		      /** 
			Aggiorno il vettore dei fatti critici falsi 
			**
			I update the array of the critical facts is made us
		      **/
		      vectlevel[level]->false_crit_vect[GUID_BLOCK (el)] |= GUID_MASK (el);

		      // False fact precondition of an action; put it in the false array

		      /** 
			Inserisco il fatto (precondizione) nei fatti non supportati 
			**
			I insert the fact (precondition) in the facts not supported
		      **/
		      insert_unsup_fact (CONVERT_FACT_TO_NODE (el, level));
		    }

		  else
		  /** 
		    Se il fatto e' un fatto critico vero 
		    **
		    If the fact is a true critical fact
		  **/
		  if (infEl->w_is_true == 1)
		    /** 
		      Aggiorno il vettore dei fatti critici veri 
		      **
		      I update to the array of the critical true facts
		    **/
		    vectlevel[level]->true_crit_vect[GUID_BLOCK (el)] |= GUID_MASK (el);

		}
	      /** 
		Se il fatto è precondizione e effetto cancellante dell'azione inserisco la catena informativa  
		**
		If the fact is precondition and cancelling effect of the action I insert the informative chain
	      **/
	      if (infEl->w_is_overall != PREC_DEL)
		backward_precond_propagation (infEl);

	      else
		infEl->w_is_overall = 0;
	      /** 
		Se la precondizione non è supportata incremento il numero di precondizioni non supportate 
		(GpG.num_prec) e il numero di precondizioni inconsistenti relative all'azione (count) 
		**
		If the precondition is not supported I increment the number of preconditions not supported
		(GpG.num_prec) and the number of relative inconsistent preconditions to the action (count)
	      **/
	      if (!infEl->w_is_true)
		{
		  count++;
		  GpG.num_prec++;
		}

	      // LM  Tengo aggiornato il valore di lamda_prec di fatti precondizione
	      CONVERT_FACT_TO_VERTEX (el)->lamda_prec =
		check_value (CONVERT_FACT_TO_VERTEX (el)->lamda_prec +
			     CONVERT_ACTION_TO_VERTEX (act_pos)->lamda_prec);
	    }
	}			// for precondizioni AT_END
    }				// end if azioni durative

  /** 
    Associo a prec il numero delle precondizioni non supportate 
    **
    I associate to prec the number of the preconditions not supported
  **/
  vectlevel[level]->action.being_removed = FALSE;
  apply_numeric_effects_of_action (act_pos, level);
  vectlevel[level]->action.being_removed = TRUE;

  /** 
    Gestione temporale 
    **
    Temporal management
  **/
  if (GpG.temporal_plan)
    {
      if (DEBUG4)
	printf ("\n\n -+- TEMPORAL -+-\n");
      /** 
	Inserimento temporale dell'azione 
	**
	Temporal insertion of the action
      **/
      insert_time (infAction);
    }
  if (((GpG.accurate_cost == COMPUTE_MAX_COST || GpG.accurate_cost == COMPUTE_FAST_COST)
       && GpG.inc_choice_type >= MIN_COST_INC)
      || GpG.accurate_cost >= COMPUTE_DG_SUM_COST)
    {
      if (GpG.orig_weight_time)
	get_total_time_plan ();

      /****************
Definisco informaz di raggiungibilita' solo quando necessario


#ifdef __TEST_REACH__
	cri_heuristic_for_action_numeric_reach(act_pos, level);
#else
	cri_heuristic_for_action(act_pos, level);
#endif
      set_computed_dg_costs (level);	// memorizza nel livello i costi calcolati
      **************/

    }

#ifdef __TEST__
  printf ("\n End IRA %s lev %d is_used %d", act->name, *infAction->level,
	  infAction->w_is_used);
printf ("\n End IRA ");
if (DEBUG3)
  {
    print_unsup_fact_vect ();
    print_unsup_num_facts ();
    print_unsup_timed_fact ();
  }
#endif
  vectlevel[level]->action.being_removed = FALSE;

  /**
    rimuove le false incosistenze dalla lista(necessario, perchè quando nella propagazione 
    effettuo una copia del livello, le inconsistenze risolte in questo modo non vengono rimosse
    **
    it removes the false incosistences from the list (needed, because when in the propagation
    I carry out a copy of the level, the resolved inconsistenze in this way do not come removed
  **/
  clean_unsup_num_fact ();

#ifdef _TEST_PROPAG_
  printf ("\n%%%%%%%%%%%%%%%%\n  IIIOOO Dopo aver inserito l'azione ");
  print_op_name (act_pos);
  printf (", livello %d, num_try %d", level, num_try);
  print_num_levels_and_actions ();

#endif
  if (DEBUG6 && num_try > -2000)
    {
      print_num_levels_and_actions ();
      print_actions_in_subgraph ();
    }

#ifdef __TEST__
if (DEBUG3)
  {
    print_unsup_fact_vect ();
    print_unsup_num_facts ();
    print_unsup_timed_fact ();
    printf ("\n End IRA ");
  }
#endif
  return (TRUE);
}


/** ACTION SUBGRAPH OK 27-02-04
 * Name: remove_action_from_vectlevel
 * Scopo: rimuovere un azione dall'action subgraph
 * Tipo: int
 * Input: int act_pos (posizione dell'azione)
 *        int level (livello da cui dovrebbe essere rimossa l'azione)
 *        int propagation
 * Output: nessuno
 * Strutture dati principali: inform
 *                            geff_conn
 *                            EfConn
 *                            GpG
 *                            vectlevel
 *                            unsup_fact (viene modificata tramite chiamata da funzione)
 *                            treated_c_l (viene modificata tramite chiamata da funzione)
 * Funzioni principali utilizzate: remove_numeric_effects_of_action
 *                                 update_time
 *                                 get_action_time
 *                                 backward_precond_remotion
 *                                 is_fact_in_delete_effects_start
 *                                 get_action_cost
 *                                 is_fact_in_additive_effects
 *                                 forward_noop_propagation
 *                                 forward_noop_remotion
 *                                 check_prec_add_list
 *                                 clean_unsup_num_fact
 *                                 reset_computed_dg_costs
 *                                 remove_unsup_num_fact
 *                                 remove_false_fact
 *                                 insert_unsup_fact
 * Chiamata da: insert_remove_action
**
*  Name: remove_action_from_vectlevel
*  Objective: to remove an action from the action subgraph
*  Type: int
*  Input: int act_pos (position of the action)
*         int level (level from which the action would have to be removed)
*         int propagation
*  Output: none
*  Main Data Structures: inform
*                        geff_conn
*                        EfConn
*                        GpG
*                        vectlevel
*                        unsup_fact (it comes modified through call from function)
*                        treated_c_l (it comes modified through call from function)
*  Main Functions Used: remove_numeric_effects_of_action
*                       update_time
*                       get_action_time
*                       backward_precond_remotion
*                       is_fact_in_delete_effects_start
*                       get_action_cost
*                       is_fact_in_additive_effects
*                       forward_noop_propagation
*                       forward_noop_remotion
*                       check_prec_add_list
*                       clean_unsup_num_fact
*                       reset_computed_dg_costs
*                       remove_unsup_num_fact
*                       remove_false_fact
*                       insert_unsup_fact
*  Call gives: insert_remove_action
**/
int remove_action_from_vectlevel (int act_pos, int level, int propagation)
{
  /** 
    Variabili di appoggio
    **
    Variable of support
  **/
  int el, cel, next_level, j, nullcost;
  /** 
    Variabili locali destinate a contenere informazioni relative a azioni, fatti e noop 
    **
    Local variables destined to contain relative information to actions, facts and noop
  **/
  ActNode_list infAction;
  FctNode_list add_effect, precond_fact;
  NoopNode_list infNoop = NULL;
  /** 
    Efconn *act conterra' informazioni relative all'azione 
    **
    Efconn *act will contain relative information to the action
  **/
  EfConn *act;
  /** 
    float temp_cost variabile locale utilizzata per aggiornare i costi dovuti alla rimozione dell'azione 
    **
    float temp_cost variable used to update the costs of the removal of the action
  **/
  float temp_cost;
  if (DEBUG6 && num_try > 1)
    print_actions_in_subgraph ();
  if (DEBUG6 && num_try > 1)
    {
      print_unsup_fact_vect ();
      print_unsup_num_facts ();
      print_unsup_timed_fact ();
    }
  
  if (vectlevel[level]->action.position != act_pos){

#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else
    printf( WAR_BUG );
#endif
    return 0;
    }
  /** 
    Dalla posizione relativa all'azione ricavo le informazioni relative all'azione da rimuovere contenute 
    nella variabile Efconn *act 
    **
    From the relative position to the action revenue the relative information to the action to remove contained
    in the variable Efconn *act
  **/
  act = CONVERT_ACTION_TO_VERTEX (act_pos);
  /** 
    Dalla posizione ricavo l'inform della azione da rimuovere 
    **
    From the position I revenue the inform of the action to remove
  **/
  infAction = GET_ACTION_OF_LEVEL (level);

#ifdef __TEST__
  if (infAction->position != act_pos
      || (infAction->action_fact == IS_FACT && DEBUG1))
    printf ("ERROR \n");
  
  if (level >= GpG.curr_plan_length){
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else
    printf( WAR_BUG );
#endif
  }
#endif

  /**
     Aggiorno le info sul prossimo/precedente livello non vuoto
     **
     I update the info on the next non empty level
  **/
  update_next_and_prev(level, C_T_REMOVE_ACTION);
  
  /** 
    Aggiorno il campo action.being_removed del vettore vectlevel (al livello level da cui rimuovo la mia azione) 
    ponendolo a TRUE, che afferma che da questo livello e' stata rimossa una azione. Serve per la propagazione 
    dei fatti numerici.
    **
    I update to the action.being_removed field of the vectlevel array (to the level level from which I remove my action)
    placing it to TRUE, that it asserts that from this level has been removed one action.  It needs for the propagation
    of the numerical facts.
  **/
  vectlevel[level]->action.being_removed = TRUE;

  // If the action is in the subgraph, we want to remove it,
  // else if the action is not in the subgraph, we want to insert it.  
  if ((DEBUG1 && num_try > 1) || DEBUG2)
    {

      printf ("\n\n %d *** REMOVE ACTION: level %d   action %d : ",GpG.count_num_try, level,act->position);
      print_op_name (act->position);
      if (DEBUG1 && !DEBUG2 && num_try > 0)
	printf ("  num_try %d total_num_try %d", num_try,GpG.count_num_try );

#ifdef __TEST__
      printf ("\nIRA--RA is_used %d time %d pos %d num_try %d action :",
	      infAction->w_is_used, level, infAction->position, num_try);
      print_op_name (act->position);
#endif
    }

#ifdef __TEST__
  fprintf (stderr, "\nIRA---RA %s is_used %d time %d pos %d num_try %d",
	   print_op_name_string (act->position, temp_name),
	   infAction->w_is_used, level, infAction->position,
	   GpG.count_num_try);
#endif

  /** 
    Decremento num_action siccome e' stata rimossa una azione 
    **
    I decrement num_action because has been removed one action
  **/
  vectlevel[*infAction->level]->num_actions--;
  GpG.num_actions--;
  

  /** 
    Aggiorno il costo del mio action subgraph togliendo il costo della azione che si va a rimuovere 
    **
    I update the cost of mine action subgraph removing the cost of the action that we are removing
  **/
  temp_cost = get_action_cost (infAction->position, *infAction->level, &nullcost);
  GpG.total_cost -= temp_cost;
  if (!nullcost)
    GpG.total_cost_from_metric -= temp_cost; 



  if(GpG.num_solutions == 0 && !GpG.restart_search && GpG.tabu_length > 0 )
    act->step = GpG.count_num_try;

  // Scan preconditions:
  // - If it was a false critic fact, now it is no more, and remove 
  //   from false critic facts (minarray and list)
  // - Else, if it was a true critic fact, now it isn't, because it isn't precondition 
  /** 
    Associo alla variabile locale next_level l'intero successivo di level: next_level rappresenta il livello successivo 
    **
    I associate to the next_level local variables the successive integer of level: next_level represents the successive level
  **/
  next_level = level + 1;

  /** 
    Precondizioni 
    **
    Preconditions 
  **/
  if (GpG.timed_facts_present) {
    remove_all_unsup_tmd_of_act(infAction);
  }

  for (j = 0; j < gef_conn[infAction->position].num_PC; j++)
    {
      /** 
	Associo a el l'intero associato alla precondizione 
	**
	I associate to el the associated integer to the precondition
      **/
      el = gef_conn[infAction->position].PC[j];

      if (el < 0)
	{
	  /** 
	    Pongo a zero il numero di azioni supportate dalla preconzizione 
	    **
	    I place to zero the number of actions supported from the preconzizione
	  **/
	  vectlevel[level]->numeric->w_is_goal[-el] = 0;

	  /**
	    Rimuovo il fatto dall'array dei fatti numerici non supportati
	    **
	    Removing the fact to the array of not supported numerical facts
	  **/
	  remove_unsup_num_fact (vectlevel[level]->numeric->
				 false_position[-el]);
	  continue;
	}

#ifdef __TEST__
      if (CHECK_FACT_POS ((el = gef_conn[infAction->position].PC[j]), level)== FALSE){
	
	
#ifdef __MY_OUTPUT__
	MSG_ERROR( WAR_BUG );
#else
	printf( WAR_BUG );
#endif
      }

      else
#endif
	
	{
	  /** 
	    Associo a precond_fact (tipo inform) le caratteristiche della precondizione 
	    **
	    I associate to precond_fact (inform type) the characteristics of the precondition
	  **/
	  precond_fact = CONVERT_FACT_TO_NODE (el, level);
	  /** 
	    Decremento il campo w_is_used (il fatto e' precondizione (1) non e' precondizione (0) 
	    dell'azione nel livello) 
	    **
	    I decrement the w_is_used field (the fact is precondition (1) not is precondition (0)
	    of the action in the level)
	  **/
	  precond_fact->w_is_used--;
	  /** 
	    Se il fatto non e' precondizione nel livello successivo o l'effetto della noop associata 
	    al fatto e' precondizione nei livelli successivi 
	    **
	    If the fact is not precondition in the successive level or the effect of the associated noop
	    to the fact is precondition in the successive levels
	  **/
	  if (!vectlevel[next_level]->fact[el].w_is_goal > 0 || !vectlevel[level]->noop_act[el].w_is_goal == 0)	/** 
														  significa che l'inserimento non ha
														  interrotto la catena informativa
														  **
														  it means that the insertion has not
														  interrupted the informative chain
														**/
	    if(precond_fact->w_is_goal)
	      /** 
		Decremento il contatore associato al fatto che e' precondizione dell'azione che andiamo a 
		rimuovere corrispondente al numero di azioni di cui e 'precondizione nei livelli superiori 
		**
		I decrement the counter associated to the fact that is precondition of the action that we are
		removing correspondent to the number of actions of which is precondition in the advanced levels
	      **/
	      precond_fact->w_is_goal--;
	  
	  if (!precond_fact->w_is_used)
	    remove_false_fact (precond_fact);

	  /** 
	    Se il fatto non e' precondizione nei livelli successivi 
	    **
	    If the fact is not precondition in the successive levels
	  **/
	  if (precond_fact->w_is_goal < 1)
	    {			// Used for the noop propagation
	      vectlevel[level]->prec_vect[GUID_BLOCK (el)] &=
		~(GUID_MASK (el));
	      /** 
		Se si tratta di un fatto critico falso 
		**
		If it is a false critical fact
	      **/
	      if (!precond_fact->w_is_true)
		{
		  /** 
		    Aggiorno la maschera corrispondente al vettore dei fatti critici falsi appartenente a 
		    vetlevel[] 
		    **
		    I update to the mask correspondent to the array of the critical facts of vetlevel[ ]
		  **/
		  vectlevel[level]->false_crit_vect[GUID_BLOCK (el)] &=
		    ~(GUID_MASK (el));

		  /* false Fact precondition of an action: remove from false array */
		  //		  remove_false_fact (precond_fact);
		}

	      /** 
		Se si tratta di un fatto critico vero 
		**
		If it is a true critical fact
	      **/
	      else if (precond_fact->w_is_true == 1)
	        /** 
		  Aggiorno la maschera corrispondente al vettore dei fatti critici veri appartenente a vectlevel[] 
		  **
		  I update the mask correspondent to the array of the true facts critics of to vectlevel[ ]
		**/
		vectlevel[level]->true_crit_vect[GUID_BLOCK (el)] &= ~(GUID_MASK (el));

	      /**
		per i fatti non più precondizione chiamo la rimozione della catena di precond
		**
		for the facts not more precondition I call the removal of the chain of precond
	      **/
	      if (!vectlevel[next_level]->fact[el].w_is_goal > 0 || !vectlevel[level]->noop_act[el].w_is_goal == 0) /** 
														      Significa che l'inserimento non 
														      ha interrotta la catena informativa
														      **
														      It means that the insertion not
														      has interrupted the informative chain
														    **/
		backward_precond_remotion (precond_fact, propagation);
	    }
	  /** 
	      Se non e' piu' precondizione decremento il contatore di GpG corrispondente al numero 
	      di precondizioni dell'action subgraph 
	      **
	      If it is not more precondition I decrement the counter of GpG correspondent to the number
	      of preconditions of the action subgraph
	  **/
	  if (!precond_fact->w_is_true)
	    GpG.num_prec--;

	  // LM  Tengo aggiornato il valore di lamda_prec di fatti precondizione      precond_fact->lamda_prec=check_value(precond_fact->lamda_prec - infAction->lamda_prec);
	}
    }

  /** 
    Azioni durative 
    **
    Durative actions
  **/
  if (gef_conn[act_pos].sf != NULL)
    {
      /**
        Precondizioni OVER_ALL
	**
	OVER_ALL preconditions
      **/
      for (j = 0; j < gef_conn[infAction->position].sf->num_PC_overall; j++)
	{
	  /** 
	    Associo a el l'intero corrispondente alla precondizione overall 
	    **
	    I associate to el the integer correspondent to the precondition overall
	  **/
	  el = gef_conn[infAction->position].sf->PC_overall[j];
	  /** 
	    Associo a infNoop (tipo inform) le caratteristiche della precondizione 
	    **
	    I associate to infNoop (type inform) the characteristics of the precondition
	  **/
	  infNoop = CONVERT_NOOP_TO_NODE (el, level);

	  if (el < 0)
	    {
	      /** 
		Pongo a zero il numero di azioni supportate dalla preconzizione 
		**
		I place to zero the number of actions supported from the preconzizione
	      **/
	      vectlevel[level]->numeric->w_is_goal[-el] = 0;
	      /**
		rimuovo il fatto dall'array dei fatti numerici non supportati
		**
		I remove the fact from the Array of the numerical facts not supported
	      **/
	      remove_unsup_num_fact (vectlevel[level]->numeric->
				     false_position[-el]);
	      continue;
	    }

#ifdef __TEST__
	  if (CHECK_FACT_POS (el, level) == FALSE){
	   
#ifdef __MY_OUTPUT__
	    MSG_ERROR( WAR_BUG );
#else
	    printf( WAR_BUG );
#endif
	  }
	  else
#endif

	  /** 
	    Se il fatto e' un effetto additivo AT_START dell'azione allora non e' un' inconsistenza 
	    **
	    If the fact is an additive AT_START effect of the action then it is not an inconsistence
	  **/
	  if (infNoop->w_is_overall != ADD_DEL
		&& infNoop->w_is_overall != ADD_NDEL)
	    {
	      /** 
		Ricavo l'inform del fatto 
		**
		Revenue the inform of the fact
	      **/
	      precond_fact = CONVERT_FACT_TO_NODE (el, level);
	      /** 
		Decremento il contatore w_is_used corrispondente al numero di azioni che 
		supporta il fatto 
		**
		Decrement the w_is_used counter correspondent to the number of actions that
		supports the fact
	      **/
	      precond_fact->w_is_used--;	// ATTENZIONE
	      /** 
		Se il fatto non e' precondizione nel livello successivo o l'effetto della noop 
		associata al fatto e' precondizione nei livelli successivi 
		**
		If the fact is not precondition in the successive level or the effect of the noop
		associated to the fact is precondition in the successive levels
	      **/
	      if (!vectlevel[next_level]->fact[el].w_is_goal > 0 || !vectlevel[level]->noop_act[el].w_is_goal == 0)/** 
														       significa che l'inserimento non ha 
														       interrotto la catena informativa
														       **
														       it means that the insertion does not have
														       interrupted the informative chain
														   **/
	        /** 
		    Se l'azione ha un effetto additivo che e' precondizione nei livelli successivi 
		    **
		    If the action has an effect additive that is precondition in the levels succeeded to you
		**/
		if (precond_fact->w_is_goal) //  I've already decremented precond_fact->w_is_goal  if infAction->w_is_goal==0 
		  /** 
		    Decremento il contatore associato al fatto che e' precondizione dell'azione che andiamo 
		    a rimuovere corrispondente al numero di azioni di cui e 'precondizione nei livelli superiori 
		    **
		    Decrement the contatore associated to the fact that is precondition of the action that we go
		    to remove correspondent to the number of actions of which and ' precondition in the advanced levels
		  **/
		  precond_fact->w_is_goal--;

	      if (!precond_fact->w_is_used)
		remove_false_fact (precond_fact);

	      /** 
		Se il fatto non e' precondizione di alcuna azione nei livelli successivi 
		**
		If the fact is not precondition of some action in the successive levels
	      **/
	      if (precond_fact->w_is_goal < 1)
		{

		  /**
		     Usato per la prtopagazione delle noop 
		     **
		     Used for the noop propagation
		  **/
		  vectlevel[level]->prec_vect[GUID_BLOCK (el)] &=
		    ~(GUID_MASK (el));
		  /** 
		    Se si tratta di un fatto critico falso 
		    **
		    If it is a false critical fact
		  **/
		  if (!precond_fact->w_is_true)
		    {
		      /** 
			Aggiorno la maschera corrispondente al vettore dei fatti critici falsi appartenente a vetlevel[] 
			**
			I update to the mask correspondent to the array of the critical facts of to vetlevel[ ]
		      **/
		      vectlevel[level]->false_crit_vect[GUID_BLOCK (el)] &= ~(GUID_MASK (el));
		      /** 
			Rimuovo il fatto critico falso dall'array dei fatti critici false 
			**
			I remove the false critical fact from the Array of the critical false facts
		      **/
		      remove_false_fact (precond_fact);
		    }
		  /** 
		    Se si tratta di un fatto critico vero 
		    **
		    If it is a true critical fact
		  **/
		  else if (precond_fact->w_is_true == 1)
		    /** 
		      Aggiorno la maschera corrispondente al vettore dei fatti critici veri appartenente a vetlevel[] 
		      **
		      I update the mask correspondent to the array of the critical true facts of vetlevel[ ]
		    **/
		    vectlevel[level]->true_crit_vect[GUID_BLOCK (el)] &= ~(GUID_MASK (el));

		  /** 
		    per i fatti non più precondizione chiamo la rimozione della catena di precond: significa 
		    che l'inserimento non ha interrotto la catena informativa 
		    **
		    for the facts not more precondition I call the removal of the chain of precond: it means
		    that the insertion has not interrupted the informative chain
		  **/
		  if (!vectlevel[next_level]->fact[el].w_is_goal > 0 || !vectlevel[level]->noop_act[el].w_is_goal == 0)
		    backward_precond_remotion (precond_fact, propagation);
		}
	      /** 
		Se non e' piu' precondizione decremento il contatore di GpG corrispondente al numero 
		di precondizioni dell'action subgraph 
		**
		If it is not more precondition I decrement the counter of GpG correspondent to the number
		of preconditions of the action subgraph
	      **/
	      if (!precond_fact->w_is_true)
		GpG.num_prec--;

	      // LM  Tengo aggiornato il valore di lamda_prec di fatti precondizione      precond_fact->lamda_prec=check_value(precond_fact->lamda_prec - infAction->lamda_prec);
	    }
	}

      /**
        Precondizioni AT_END
	**
        AT_END Precondizioni
      **/
      for (j = 0; j < gef_conn[infAction->position].sf->num_PC_end; j++)
	{
	  /** 
	    Associo a el l'intero corrispondente alla precondizione at_end 
	    **
	    I associate to el the integer correspondent to the at_end precondition
	  **/
	  el = gef_conn[infAction->position].sf->PC_end[j];
	  infNoop = CONVERT_NOOP_TO_NODE (el, level);


	  if (el < 0)
	    {
	      /** 
		Pongo a zero il numero di azioni supportate dalla precondizione 
		**
		I place to zero the number of actions supported from the precondition
	      **/
	      vectlevel[level]->numeric->w_is_goal[-el] = 0;
	      /**
		rimuovo il fatto dall'array dei fatti numerici non supportati
		**
		I remove the fact from the array of the numerical facts not supported
	      **/
	      remove_unsup_num_fact (vectlevel[level]->numeric->false_position[-el]);	//, level);
	      continue;
	    }

#ifdef __TEST__
	  if (CHECK_FACT_POS (el, next_level) == FALSE) {
	    
	    
#ifdef __MY_OUTPUT__
	    MSG_ERROR( WAR_BUG );
#else
	    printf( WAR_BUG );
#endif
	  }

	  else
#endif


	    // PREC_END FIX
	    /*
	      if (infNoop->w_is_overall != DEL_ADD
	      && infNoop->w_is_overall != ADD_NDEL
	      && !is_fact_in_additive_effects (act_pos, el))
	    */



	  if (infNoop->w_is_overall != ADD_DEL && infNoop->w_is_overall != ADD_NDEL)
	    {
	      /** 
		Ricavo l'inform del fatto 
		**
		I revenue the inform of the fact
	      **/
	      precond_fact = CONVERT_FACT_TO_NODE (el, level);
	      
	      precond_fact->w_is_used--;
	      /** 
		Se il fatto non e' precondizione nel livello successivo o l'effetto della noop 
		associata al fatto is precondizione nei livelli successivi 
		**
		If the fact is not precondition in the successive level or the effect of the noop
		associated to the fact is precondition in the successive levels
	      **/
	      if (!vectlevel[next_level]->fact[el].w_is_goal > 0 || !vectlevel[level]->noop_act[el].w_is_goal == 0) /** 
														      significa che l'inserimento non ha 
														      interrotta la catena informativa
														      **
														      it means that the insertion not have
														      interrupted the informative chain
														    **/	
	      if (!precond_fact->w_is_used)
		remove_false_fact (precond_fact);
		  /** 
		    Decremento il contatore associato al fatto che e' precondizione dell'azione che 
		    andiamo a rimuovere corrispondente al numero di azioni di cui e' precondizione 
		    nei livelli superiori 
		    **
		    Decrement the counter associated to the fact that is precondition of the action that
		    we are removing correspondent to the number of actions of which is precondition
		    in the advanced levels
		  **/
		if(precond_fact->w_is_goal)
		  // PREC END FIX
		  //		if (infAction->w_is_goal)	//  I've already decremented precond_fact->w_is_goal  if infAction->w_is_goal==0
		  precond_fact->w_is_goal--;

	      /** 
		Se il fatto non e' precondizione di alcuna azione nei livelli successivi 
		**
		If the fact is not precondition of some action in the successive levels
	      **/
	      if (precond_fact->w_is_goal < 1)
		{
		  // PREC END FIX
		  //		  vectlevel[next_level]->prec_vect[GUID_BLOCK (el)] &= ~(GUID_MASK (el));
		  vectlevel[level]->prec_vect[GUID_BLOCK (el)] &= ~(GUID_MASK (el));
	          /** 
		    Se si tratta di un fatto critico falso 
		    **
		    If it is a false critical fact
		  **/
		  if (!precond_fact->w_is_true)
		    {		/* was a FALSE critic fact */
		      /** 
			Aggiorno la maschera corrispondente al vettore dei fatti critici falsi appartenente a vetlevel[] 
			**
			I update to the mask correspondent to the array of the critical false facts of vetlevel[ ]
		      **/
		      vectlevel[level]->false_crit_vect[GUID_BLOCK (el)] &= ~(GUID_MASK (el));
		      /** 
			Rimuovo il fatto critico falso dall'array dei fatti critici false 
			**
			I remove the false critical fact from the array of the critical false facts
		      **/
		      remove_false_fact (precond_fact);
		    }
		  /** 
		    Se si tratta di un fatto critico vero 
		    **
		    If it is a true critical fact
		  **/
		  else if (precond_fact->w_is_true == 1)
		    /** 
		      Aggiorno la maschera corrispondente al vettore dei fatti critici veri 
		      appartenente a vetlevel[] 
		      **
		      I update to the mask correspondent to the array of the critical true facts of pertaining to vetlevel[ ]
		    **/
		    vectlevel[level]->true_crit_vect[GUID_BLOCK (el)] &= ~(GUID_MASK (el));

		  /** 
		    per i fatti non più precondizione chiamo la rimozione della catena di 
		    precond: significa che l'inserimento non ha interrotta la catena informativa 
		    **
		    for the facts not more precondition I call the removal of the chain of
		    precond: it means that the insertion has not interrupted the informative chain
		  **/
		  if (!vectlevel[next_level]->fact[el].w_is_goal > 0 || !vectlevel[level]->noop_act[el].w_is_goal == 0)
		    backward_precond_remotion (precond_fact, propagation);
		}
	      /**
		Se non e' piu' precondizione decremento il contatore di GpG corrispondente 
		al numero di precondizioni dell'action subgraph 
		**
		If it is not more precondition I decrement the counter of corresponding GpG
		to the number of preconditions of the action subgraph
	      **/
	      if (!precond_fact->w_is_true)
		GpG.num_prec--;

	      // LM  Tengo aggiornato il valore di lamda_prec di fatti precondizione      precond_fact->lamda_prec=check_value(precond_fact->lamda_prec - infAction->lamda_prec);
	    }
	}
    }				//end azioni durative



  // Action isn't used
  infAction->w_is_used = 0;

  /** 
    Pongo a zero w_is_goal che afferma se un suo effetto additivo e' precondizione di azioni 
    nei livelli superiori perche' l'azione viene rimossa 
    **
    I place to zero w_is_goal that it asserts if an its additive effect is precondition of actions
    in the advanced levels because the action comes removed
  **/
  infAction->w_is_goal = 0;




  /**
    Effetti additivi
    **
    Additive effects
  **/
  /** 
    L'azione che abbiamo rimosso dall'action subgraph ha degli effetti additivi i quali 
    possono non essere piu' supportati.
    **
    The action that we have removed from the action subgraph has some additive effects which
    can not be supported more
  **/

  /** 
    Azioni durative 
    **
    Durative actions
  **/
  if (gef_conn[act_pos].sf != NULL)
    {

      /** 
	Effetti Additivi A_START 
	**
	AT_START additive effects
      **/
      for (j = 0; j < gef_conn[act_pos].sf->num_A_start; j++)
	{
	  /** 
	    Associo a cel l'intero corrispondente all'effetto additivo 
	    **
	    I associate to cel the correspondent integer to the additive effect 
	  **/
	  cel = gef_conn[act_pos].sf->A_start[j];
	  if (cel < 0)
	    continue;
	  /** 
	    Ricavo l'inform corrispondente all'effetto additivo 
	    **
	    I obtain the inform correspondent to the additive effect
	  **/
	  add_effect = CONVERT_FACT_TO_NODE (cel, next_level);
	  /** 
	    Pongo a zero il campo corrispondente al numero di azioni di cui e' precondizione 
	    **
	    I place to zero the field correspondent to the number of actions of which is precondition
	  **/
	  vectlevel[level]->noop_act[cel].w_is_overall = 0;
	  /** 
	    Se il fatto e' negli effetti cancellanti 
	    **
	    If the fact is in the cancelling effects
	  **/
	  if (is_fact_in_delete_effects (act_pos, cel))
	    {

	      /* ADD_START - DEL_END */
	      if (vectlevel[next_level]->fact[cel].w_is_goal > 0
		  && vectlevel[level]->noop_act[cel].w_is_goal == 0
		  && vectlevel[level]->fact[cel].w_is_goal > 0)
		{

		  /** 
		    significa che l'inserimento non ha interrotta la catena informativa
		    **
		    it means that the insertion has not interrupted the informative chain
		  **/
		  /** 
		    Incremento w_is_goal della noop 
		    **
		    Increment w_is_goal of the noop
		  **/
		  vectlevel[level]->noop_act[cel].w_is_goal++;
		  /** 
		    Aggiorno i bit corrispondenti alla noop del fatto 
		    **
		    I update the bit correspondents to the noop of the fact
		  **/
		  vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] |=
		    GUID_MASK (cel);
		}

	      /** 
		Se il fatto al prossimo livello e' precondizione e non e' precondizione a questo 
		livello allora costruisco la catena informativa 
		**
		If the fact to the next level is precondition and not is precondition to this
		level then I construct the informative chain
	      **/
	      if (vectlevel[next_level]->fact[cel].w_is_goal
		  && vectlevel[level]->fact[cel].w_is_goal == 0)
		backward_precond_propagation (add_effect);

	      /** 
		Se la NOOP e' precondizione allora non e' piu' minacciata e la rimuovo dal vettore delle noop minacciate 
		**
		If the NOOP is precondition then it is not threatened more and I do not remove it from the array of the threatened noop
	      **/
	      if (vectlevel[level]->
		  noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		remove_treated_noop (CONVERT_NOOP_TO_NODE (cel, level));
	      /** 
		Se il fatto non e' piu' supportato 
		**
		If the fact is not more supported
	      **/
	      if (!vectlevel[level]->fact[cel].w_is_true)
		{
		  /**
		    Elimino la noop dall'action subgraph 
		    **
		    I delete the noop from the action subgraph
		  **/
		  vectlevel[level]->noop_act[cel].w_is_used--;
		  vectlevel[level]->noop_act_vect[GUID_BLOCK (cel)] &=
		    ~(GUID_MASK (cel));
		}

	      else
		{
		  /** 
		    Aumento w_is_true che corrisponde al numero di azioni che supportano il fatto 
		    **
		    I increase w_is_true that it corresponds to the number of actions that support the fact
		  **/
		  vectlevel[next_level]->fact[cel].w_is_true++;
		  /**
		    Aggiorno i predicati derivati
		    **
		    I update the derivates predicates
		  **/
		  calc_new_derived_predicates(cel, next_level, ADD_FACT, NULL);
		  // Update the fact vect with the added effect of the inserted action
		  // fact_vect is a negated bit array
		  vectlevel[next_level]->fact_vect[GUID_BLOCK (cel)] |=
		    GUID_MASK (cel);
		  vectlevel[next_level]->
		    false_crit_vect[GUID_BLOCK (cel)] &= ~(GUID_MASK (cel));
		  /** 
		    Se il fatto e' precondizione di azioni nei livelli successivi 
		    **
		    If the fact is precondition of actions in the successive levels
		  **/
		  if (vectlevel[next_level]->fact[cel].w_is_goal)
		    {
		      /** 
			Se il fatto e' supportato da una sola azione nel livello successivo 
			**
			If the fact is supported from one single action in the successive level
		      **/
		      if (vectlevel[next_level]->fact[cel].w_is_true == 1)
		        /** 
			  Aggiorno i bit del vettore true_critic_vect (fatti critici) 
			  **
			  I update the bit of the array true_critic_vect (critics facts)
			**/
			vectlevel[next_level]->true_crit_vect[GUID_BLOCK (cel)] |= GUID_MASK (cel);
		      /** 
			Se il fatto e' supportato da piu' azioni nel livello successivo 
			**
			If the fact is supported from more action in the successive level
		      **/
		      else if (vectlevel[next_level]->fact[cel].w_is_true > 1)
			/** 
			  Aggiorno i bit del vettore true_critic_vect (fatti critici) visto che il 
			  fatto non e' piu' critico 
			  **
			  I update the bit of the array true_critic_vect (critics facts) because the
			  fact is not more critical
			**/
			vectlevel[next_level]->true_crit_vect[GUID_BLOCK (cel)] &=~(GUID_MASK (cel));
		    }
		  /** 
		    Controllo se il fatto era falso ora non lo e' piu' (false_position>0 il fatto e' 
		    inserito nella lista dei fatti falsi) 
		    **
		    Control if the fact were false now not it is not more (false_position>0 the fact is
		    inserted in the list of the false facts)
		  **/
		  if (vectlevel[next_level]->fact[cel].false_position >= 0)
		    /** 
		      Elimino il fatto dalla lista dei fatti falsi 
		      **
		      I remove the fact from the list of the false facts
		    **/
		    remove_false_fact (&vectlevel[next_level]->fact[cel]);

		  /** 
		    Aumento il contatore corrispondente al numero di fatti veri 
		    **
		    Increase the counter correspondent to the number of true facts
		  **/
		  vectlevel[next_level]->num_fact++;
		  /** 
		    Propago in avanti la noop corrispondente al fatto 
		    **
		    I propagate in ahead the noop the correspondent to the fact
		  **/
		  forward_noop_propagation (cel, next_level);
		}
	    }
	  else
	    {
	      /* ADD_START - NOT DEL_END */
	      if (check_mutex_noop (cel, level) >= 0
		  && vectlevel[next_level]->fact[cel].w_is_goal
		  && vectlevel[level]->fact[cel].w_is_goal == 0)
		{
		  if (vectlevel[next_level]->fact[cel].w_is_goal > 0
		      && vectlevel[level]->noop_act[cel].w_is_goal == 0
		      && vectlevel[level]->fact[cel].w_is_goal > 0)
		    {
		      /** 
			 Significa che l'inserimento non ha interrotta la catena informativa
			 **
			 it means that the insertion has not interrupted the informative chain
		      **/
		      vectlevel[level]->noop_act[cel].w_is_goal++;
		      vectlevel[level]->
			noop_prec_act_vect[GUID_BLOCK (cel)] |=
			GUID_MASK (cel);
		    }

		  /** 
		    Costruisce la catena informativa 
		    **
		    It constructs the informative chain
		  **/
		  backward_precond_propagation (add_effect);
		  /** 
		    La NOOP non e' piu' minacciata. La rimuovo dalla lista delle noop minacciate (treated_c_l) 
		    **
		    The NOOP is not more threatened. I remove it from the list of the noop threatened (treated_c_l)
		  **/
		}
	      /** 
		Se il fatto non e' supportato da azioni nel livello level 
		**
		If the fact is not supported by actions in the level level
	      **/
	      if (!vectlevel[level]->fact[cel].w_is_true)
		{
		  /** 
		    Elimino la noop dall'action subgraph 
		    **
		    I eliminate the noop from the action subgraph
		  **/
		  vectlevel[level]->noop_act[cel].w_is_used--;
		  /**		  
		    Aggiorno il vettore noop_act_vect 
		    **
		    I update the array noop_act_vect
		  **/
		  vectlevel[level]->noop_act_vect[GUID_BLOCK (cel)] &=~(GUID_MASK (cel));
		  /** 
		    Decremento w_is_true corrispondente all'effetto additivo visto che non e' piu' supportato 
		    **
		    I decrement w_is_true correspondent to the additive effect because it is not more supported
		  **/
		  add_effect->w_is_true--;
		  /** 
		    Decremento il numero di precondizioni (num_prec) di un numero pari al numero di 
		    azioni di cui i fatto e' precondizione 
		    **
		    I decrement the number of preconditions (num_prec) of an number equal to the number of
		    actions of which the fact is precondition
		  **/
		  GpG.num_prec -= add_effect->w_is_goal;
		  /**
		    Aggiorno i predicati derivati
		    **
		    I update the derivates predicates
		  **/
		  calc_new_derived_predicates(cel, next_level, DEL_FACT, NULL);
		  /** 
		    Aggiorno il vettore dei fatti 
		    **
		    I update the array of the facts
		  **/
		  vectlevel[next_level]->fact_vect[GUID_BLOCK (cel)] &= ~(GUID_MASK (cel));
		  vectlevel[next_level]->num_fact--;
		  /** 
		    Se il fatto (dato dall'effetto additivo) e'  precondizione per azioni nei livelli successivi 
		    **
		    If the fact (given by the additive effect) is precondition for actions in the successive levels
		  **/
		  if (add_effect->w_is_goal)
		    {		/* the fact wasn't critic ... */
		      /** 
			Se il fatto e' precondizione nel medesimo livello (level) viene inserito 
			nella lista dei fatti non supportati 
			**
			If the fact is precondition in the same level (level) it is inserted
			in the list of the facts not supported
		      **/
		      if (add_effect->w_is_used)
		        /** 
			  Inserimento nella lista dei fatti non supportati 
			  **
			  Insertion in the list of the facts not supported
			**/
			insert_unsup_fact (add_effect);	/* and now became critic */
		      vectlevel[next_level]->
			false_crit_vect[GUID_BLOCK (cel)] |= GUID_MASK (cel);
		      vectlevel[next_level]->
			true_crit_vect[GUID_BLOCK (cel)] &=
			~(GUID_MASK (cel));
		    }
		  /** 
		    Il fatto non e' piu' supportato 
		    **
		    The fact is not supported more
		  **/
		  /** 
		    Rimuovo la noop corrispondente al fatto (non piu' supportato) dalla catena di noop 
		    **
		    I remove the noop correspondent to the fact (not more supported) from the chain of noop
		  **/
		  forward_noop_remotion (cel, next_level);
		}
	    }
	}

       /** 
	Effetti Cancellanti A_START 
	**
	Cancelling AT_START Effects
      **/
      for (j = 0; j < gef_conn[act_pos].sf->num_D_start; j++)
	{
	  /** 
	    Associo a cel l'intero corrispondente all'effetto cancellante 
	    **
	    I associate to cel the integer correspondent to the cancelling effect
	  **/
	  cel = gef_conn[act_pos].sf->D_start[j];
	  if (cel < 0)
	    continue;
	  /** 
	    Ricavo l'inform corrispondente all'effetto cancellante 
	    **
	    I obtain the inform correspondent to the cancelling effect
	  **/
	  add_effect = CONVERT_FACT_TO_NODE (cel, next_level);
	  vectlevel[level]->noop_act[cel].w_is_overall = 0;
	  /** 
	    Se il fatto e' negli effetti additivi 
	    **
	    If the fact is in the additive effects
	  **/
	  if (is_fact_in_additive_effects (act_pos, cel))
	    {
	      /* DEL_START - ADD_END */
	      /** 
		Se il fatto e' precondizione nei livelli successivi e non e' nella catena di noop 
		**
		If the fact is precondition in the successive levels and is not in the chain of noop
	      **/
	      if (vectlevel[next_level]->fact[cel].w_is_goal > 0
		  && vectlevel[level]->noop_act[cel].w_is_goal == 0
		  && vectlevel[level]->fact[cel].w_is_goal > 0)
		{
		  /** 
		    significa che l'inserimento non ha interrotta la catena informativa
		    **
		    it means that the insertion has not interrupted the informative chain
		  **/
		  /** 
		    Aumento il campo w_is_goal della noop (portera' il suo effetto nei livelli successivi) 
		    **
		    I increase the field w_is_goal of noop (it will carry its effect in the successive levels)
		  **/
		  vectlevel[level]->noop_act[cel].w_is_goal++;
		  /** 
		    Aggiorno il vettore corrispondente alla noop 
		    **
		    I update the array correspondent to the noop
		  **/
		  vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] |=
		    GUID_MASK (cel);
		}

	      /** 
		Se il fatto al prossimo livello e' precondizione e non e' precondizione a questo 
		livello allora costruisco la catena informativa 
		**
		If the fact to the next level is precondition and is not precondition to this
		level then I construct the informative chain
	      **/
	      if (!vectlevel[next_level]->fact[cel].w_is_goal
		  && vectlevel[level]->fact[cel].w_is_goal == 0)
		/** 
		  Costruzione della catena informativa 
		  **
		  Construction of the informative chain
		**/
		backward_precond_propagation (add_effect);

	      /** 
		Se la NOOP e' precondizione allora non e' piu' minacciata 
		**
		If the NOOP is precondition then it is not more threatened
	      **/
	      if (vectlevel[level]->
		  noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		/** 
		  Rimuovo la noop dalla catena delle noop minacciate (treated_c_l) 
		  **
		  I remove the noop from the chain of the threatened noop (treated_c_l)
		**/
		remove_treated_noop (CONVERT_NOOP_TO_NODE (cel, level));
	      /** 
		Se il fatto e' supportato da azioni 
		**
		If the fact is supported by actions
	      **/
	      if (vectlevel[level]->fact[cel].w_is_true)
		{
		  /** 
		    Inserisco la noop nell'action subgraph 
		    **
		    I insert the noop in the action subgraph
		  **/
		  vectlevel[level]->noop_act[cel].w_is_used++;
		  /** 
		    Aggiorno il vettore corrispondente alla noop al livello level 
		    **
		    I update the array correspondent to the noop to the level level
		  **/
		  vectlevel[level]->noop_act_vect[GUID_BLOCK (cel)] |=
		    GUID_MASK (cel);
		}

	      else
		{   /** 
		       il fatto al livello level non e' vero
		       **
		       the fact to the true level level not is
		    **/
		  /** 
		    Azzero il contatore w_is_true (numero di azioni che supportano il fatto) 
		    **
		    I annul the counter w_is_true (number of actions that support the fact)
		  **/
		  add_effect->w_is_true--;
		  /** 
		    Decremento il contatore (della variabile globale GpG) di precondizioni (vere) di una 
		    quantita' pari al numero di azioni che il fatto supporta 
		    **
		    Decrement the contatore (of variable the total GpG) of preconditions (true) of one
		    quantita' equal to the number of actions that the fact supports
		  **/
		  GpG.num_prec -= add_effect->w_is_goal;
		  /**
		     Aggiorno i predicati derivati
		     **
		     I update the derivates predicates
		  **/
		  calc_new_derived_predicates(cel, next_level, DEL_FACT, NULL);
		  /** 
		    Aggiorno il vettore del fatto al livello successivo 
		    **
		    I update the array of the fact to the successive level
		  **/
		  vectlevel[next_level]->fact_vect[GUID_BLOCK (cel)] &=~(GUID_MASK (cel));
		  /** 
		    Decremento il contatore num_fact (numero di fatti veri in un livello) nel livello 
		    next_level di uno 
		    **
		    I decrement the counter num_fact (number of true facts in a level) in the level
		    next_level of one
		  **/
		  vectlevel[next_level]->num_fact--;
		  /** 
		    Se il fatto e' precondizione nei livelli successivi 
		    **
		    If the fact is precondition in the successive levels
		  **/
		  if (add_effect->w_is_goal)
		    {		/* the fact wasn't critic ... */
		      /** 
			Se il fatto e' precondizione nel medesimo livello (level) 
			**
			If the fact is precondition in the same level (level)
		      **/
		      if (add_effect->w_is_used)
		        /** 
			  Lo inserisco nella lista dei fatti non supportati (fatto critico falso) 
			  **
			  I insert it in the list of the facts not supported (critical false fact)
			**/
			insert_unsup_fact (add_effect);
		      /** 
			Il fatto da critico vero e' passato a critico falso, quindi vengono aggiornati i 
			vettori true_critic_vect e false_critic_vect 
			**
			The fact from true critic is became false critic, therefore I update the
			arrays true_critic_vect and false_critic_vect
		      **/
		      vectlevel[next_level]->false_crit_vect[GUID_BLOCK (cel)] |= GUID_MASK (cel);
		      vectlevel[next_level]->
			true_crit_vect[GUID_BLOCK (cel)] &=
			~(GUID_MASK (cel));
		    }
		  /** 
		    Rimuovo la noop dal livello successivo 
		    **
		    I remove the noop from the successive level
		  **/
		  forward_noop_remotion (cel, next_level);
		}
	    }
	  else
	    {

	      /* DEL_START - NOT ADD_END */
	      /** 
		Se il fatto is precondizione nei livelli successivi e non e' nella catena di noop 
		**
		If the fact is precondition in the successive levels and is not in the chain of noop
	      **/
	      if (vectlevel[next_level]->fact[cel].w_is_goal > 0
		  && vectlevel[level]->noop_act[cel].w_is_goal == 0
		  && vectlevel[level]->fact[cel].w_is_goal > 0)
		{
		  /**
		    significa che l'inserimento non ha interrotta la catena informativa
		    **
		    it means that the insertion has not interrupted the informative chain
		  **/
		  /** 
		    Aumento il campo w_is_goal della noop (portera' il suo effetto nei livelli succevi) 
		    **
		    Increase the field w_is_goal of noop (portera' the its effect in the levels succevi)
		  **/
		  vectlevel[level]->noop_act[cel].w_is_goal++;
		  /** 
		    Aggiorno il vettore corrispondente alla noop 
		    **
		    I update to the array correspondent to the noop
		  **/
		  vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] |= GUID_MASK (cel);
		}

	      /** 
		Se il fatto al prossimo livello e' precondizione e non e' precondizione a questo livello 
		allora costruisco la catena informativa 
		**
		If the fact to the next level is precondition and not is precondition to this level
		then I construct the informative chain
	      **/
	      if (vectlevel[next_level]->fact[cel].w_is_goal
		  && vectlevel[level]->fact[cel].w_is_goal == 0)
		/** 
		  Costruisco la catena informativa 
		  **
		  I construct the informative chain
		**/
		backward_precond_propagation (add_effect);

	      /** 
		Se la NOOP e' precondizione allora non e' piu' minacciata 
		**
		If the NOOP is precondition then it is not more threatened
	      **/
	      if (vectlevel[level]->
		  noop_prec_act_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		/** 
		  Siccome la noop non e' piu' minacciata la rimuovo dalla lista delle noop minacciate (treated_c_l) 
		  **
		  Threatened Siccome the noop is piu' I do not remove it from the list of the noop threatened (treated_c_l)
		**/
		remove_treated_noop (CONVERT_NOOP_TO_NODE (cel, level));

	      /** 
		Se il fatto e' supportato 
		**
		If the fact is supported
	      **/
	      if (vectlevel[level]->fact[cel].w_is_true) { 
		/** 
		  Propago in avanti la noop relativa al fatto 
		  **
		  I propagate in ahead the noop relative to the fact
		**/
		forward_noop_propagation (cel, level);
	      }
	    }			//end else DEL_START - NOT ADD_END
	}			//end for
    }				// end if sf

      /** 
	Effetti Cancellanti AT_END 
	**
	Cancelling AT_END Effects
      **/
      for (j = 0; j < gef_conn[act_pos].num_D; j++)
	{
	  /** 
	    Associo a cel l'intero corrispondente all'effetto cancellante 
	    **
	    I associate to cel the correspondent integer to the cancelling effect
	  **/
	  cel = gef_conn[act_pos].D[j];
	  if (cel < 0)
	    continue;
	  /** 
	    Ricavo l'inform corrispondente all'effetto cancellante 
	    **
	    I obtain the inform correspondent to the cancelling effect
	  **/
	  add_effect = CONVERT_FACT_TO_NODE (cel, next_level);

	  /** 
	    Se il fatto e' negli effetti additivi AT_START 
	    **
	    If the fact is in the additive effects AT_START
	  **/
	  if (!is_fact_in_additive_effects_start (act_pos, cel))
	    {

	      /* DEL_END - NOT ADD_START */
	      vectlevel[level]->noop_act[cel].w_is_overall = 0;
	      /** 
		Se il fatto e' precondizione nei livelli successivi e non e' nella catena di noop 
		**
		If the fact is precondition in the successive levels and is not in the chain of noop
	      **/
	      if (vectlevel[next_level]->fact[cel].w_is_goal > 0
		  && vectlevel[level]->noop_act[cel].w_is_goal == 0
		  && vectlevel[level]->fact[cel].w_is_goal > 0)
		{
		  /** 
		    significa che l'inserimento non ha interrotta la catena informativa
		    **
		    it means that the insertion has not interrupted the informative chain
		  **/
		  /** 
		    Aumento il campo w_is_goal della noop (portera' il suo effetto nei livelli successivi) 
		    **
		    I increase the field w_is_goal of noop (it will carry its effect in the successive levels)
		  **/
		  vectlevel[level]->noop_act[cel].w_is_goal++;
		  /** 
		    Aggiorno il vettore corrispondente alla noop 
		    **
		    I update the array correspondent to the noop
		  **/
		  vectlevel[level]->noop_prec_act_vect[GUID_BLOCK (cel)] |=
		    GUID_MASK (cel);
		}

	      /** 
		Se il fatto al prossimo livello e' precondizione e non e' precondizione a questo livello 
		allora costruisco la catena informativa 
		**
		If the fact to the next level is precondition and is not precondition to this level
		then I construct the informative chain
	      **/
	      if (vectlevel[next_level]->fact[cel].w_is_goal
		  && vectlevel[level]->fact[cel].w_is_goal == 0)
		/** 
		  Costruisco la catena informativa 
		  **
		  I construct the informative chain
		**/
		backward_precond_propagation (add_effect);
	      /** 
		Se la NOOP e' precondizione allora non e' piu' minacciata 
		**
		If the NOOP is precondition then it is not more threatened
	      **/
	      if (vectlevel[next_level]->
		  prec_vect[GUID_BLOCK (cel)] & GUID_MASK (cel))
		/** 
		  Siccome la noop non e' piu' minacciata la rimuovo dalla lista delle noop minacciate 
		  (treated_c_l) 
		  **
		  Because the noop is not more threatened I remove it from the list of the threatened noop
		**/
		remove_treated_noop (CONVERT_NOOP_TO_NODE (cel, level));
	      /** 
		la noop is inserita
		**
		the noop is inserted
	      **/
	      if (vectlevel[level]->noop_act[cel].w_is_used)
		{
		  /** 
		    Aumento il numero di azioni (w_is_true) che supportano il fatto 
		    **
		    I increase the number of actions (w_is_true) that they support the fact
		  **/
		  vectlevel[next_level]->fact[cel].w_is_true++;

		  /**
		    Aggiorno i predicati derivati
		    **
		    I update the derivates predicates
		  **/
		  calc_new_derived_predicates(cel, next_level, ADD_FACT, NULL);
		  // Update the fact vect with the added effect of the inserted action
		  // fact_vect is a negated bit array
		  vectlevel[next_level]->fact_vect[GUID_BLOCK (cel)] |= GUID_MASK (cel);
		  vectlevel[next_level]->false_crit_vect[GUID_BLOCK (cel)] &= ~(GUID_MASK (cel));
		  /** 
		    Se il fatto e' precondizione nei livelli successivi 
		    **
		    If the fact is precondition in the successive levels
		  **/
		  if (vectlevel[next_level]->fact[cel].w_is_goal)
		    {
		      /** 
			Se il fatto e' un fatto critico vero (prima era falso) 
			**
			If the fact is a true critical fact (before was false)
		      **/
		      if (vectlevel[next_level]->fact[cel].w_is_true == 1)
			/** 
			  Aggiorno true_critic_vect 
			  **
			  I update true_critic_vect
			**/
			vectlevel[next_level]->true_crit_vect[GUID_BLOCK (cel)] |= GUID_MASK (cel);
		      /** 
			Se il fatto non e' piu' critico (prima era critico vero) 
			**
			If the fact is not more critical (before was true critical)
		      **/
		      else if (vectlevel[next_level]->fact[cel].w_is_true > 1)
			/** 
			  Aggiorno true_critic_vect 
			  **
			  I update true_critic_vect
			**/
			vectlevel[next_level]->
			  true_crit_vect[GUID_BLOCK (cel)] &=
			  ~(GUID_MASK (cel));
		    }

		  /** 
		    Se il fatto era falso (false_position>0) ora non lo e' piu' 
		    **
		    If the fact were false (false_position>0) now it is not more
		  **/
		  if (vectlevel[next_level]->fact[cel].false_position >= 0)
		    /** 
		      Rimuovo il fatto che prima era falso dalla lista dei fatti falsi (unsup_fact) 
		      **
		      I remove the fact that before was false from the list of the false facts (unsup_fact)
		    **/
		    remove_false_fact (&vectlevel[next_level]->fact[cel]);

		  /** 
		    Aumento nel livello successivo il numero di fatti veri 
		    **
		    Increase in the successive level the number of true facts
		  **/
		  vectlevel[next_level]->num_fact++;
		  /** 
		    Propago in avanti la noop corrispondente al fatto 
		    **
		    I propagate in ahead the noop correspondent to the fact
		  **/
		  forward_noop_propagation (cel, next_level);
		}		// end if
	    }			// end if DEL_END - NOT ADD_START
	}


  /**  
    Effetti  additivi AT_END 
    **
    Additive AT_END effects
  **/
  for (j = 0; j < gef_conn[act->position].num_A; j++)
    {
      /** 
	Associo a cel l'intero corrispondente all'effetto additivo 
	**
	I associate to cel the correspondent integer to the additive effect
      **/
      cel = gef_conn[act->position].A[j];

      /** 
	Se l'azione e' durativa e il fatto non e' negli effetti cancellanti AT_START 
	**
	If the action is durative and the fact is not in the cancelling AT_START effects
      **/
      if (gef_conn[act_pos].sf
	  && is_fact_in_delete_effects_start (act_pos, cel))
	continue;
      /** 
	gli effetti numerici verranno considerati successivamente
	**
	the numerical effects will be considered subsequently
      **/
      if (cel < 0)
	continue;
      /** 
	Controllo sul fatto 
	**
	Control on the fact
      **/
      if (CHECK_FACT_POS (cel, next_level) || GpG.is_domain_numeric)
	{
	  /** 
	    Ricavo l'inform corrispondente all'effetto additivo 
	    **
	    I obtain the inform correspondent to the effect additive
	  **/
	  add_effect = CONVERT_FACT_TO_NODE (cel, next_level);
	  /** 
	    Se il fatto e' supportato da una sola azione nei livelli precedenti 
	    **
	    If the fact is supported from one single action in the previous levels
	  **/
	  if (--add_effect->w_is_true <= 1)
	    {
	      /** 
		Se il fatto non e' supportato da alcuna azione 
		**
		If the fact is not supported by some action
	      **/
	      if (add_effect->w_is_true < 1)
		{
		  /** 
		    Decremento il numero di precondizioni vere (num_prec) di una quantita' pari al numero 
		    di azioni di cui il fatto e' precondizione nei livelli successivi 
		    **
		    I decrement the number of true preconditions (num_prec) of one quantity equal to the number
		    of actions of which the fact is precondition in the successive levels
		  **/
		  GpG.num_prec -= add_effect->w_is_goal;
		  calc_new_derived_predicates(cel, next_level, DEL_FACT, NULL);
		  /** 
		    Aggiorno il vettore corrispondente al fatto 
		    **
		    I update the array correspondent to the fact
		  **/
		  vectlevel[next_level]->fact_vect[GUID_BLOCK (cel)] &=
		    ~(GUID_MASK (cel));
		  /** 
		    Decremento il numero di fatto veri (num_fact) nel livello superiore 
		    **
		    I decrement the number of true fact (num_fact) in the advanced level
		  **/
		  vectlevel[next_level]->num_fact--;
		  /** 
		    Rimuovo la noop corrispondente al fatto 
		    **
		    I remove the noop correspondent to the fact
		  **/
		  forward_noop_remotion (cel, next_level);
		  /** 
		    Se il fatto e' precondizione nei livelli successivi 
		    **
		    If the fact is precondition in the successive levels
		  **/
		  if (add_effect->w_is_goal)
		    {	  /** 
			      il fatto non era critico...
			      **
			      the fact wasn' t critic...
			  **/
		      /** 
			Se il fatto e' precondizione nel medesimo livello 
			**
			If the fact is precondition in the same level
		      **/
		      if (add_effect->w_is_used)
		        /** 
			  Inserisci il fatto nella lista dei fatti non supportati (false_fact) 
			  **
			  Insert the fact in the list of the facts not supported (false_fact)
			**/
			insert_unsup_fact (add_effect);	/* and now became critic */
		      /** 
			Aggiorno il vettore corrispondente ai fatti critici falsi (non supportati da alcuna 
			azioni) visto che il fatto e' diventato falso 
			**
			I update to the array correspondent to the critical false facts (not supported by some
			action) inasmuch as the fact is become false
		      **/
		      vectlevel[next_level]->false_crit_vect[GUID_BLOCK (cel)] |= GUID_MASK (cel);
		      /** 
			Aggiorno il vettore dei fatti critici veri (supportati da una sola azione) visto 
			che il fatto e' diventato falso 
			**
			I update to the array of the critical true facts (supported by one single action) because
			the fact is become false
		      **/
		      vectlevel[next_level]->true_crit_vect[GUID_BLOCK (cel)] &=~(GUID_MASK (cel));
		    }
		}
	      /** 
		Se il fatto e' precondizione nei livelli successivi 
		**
		If the fact is precondition in the successive levels
	      **/
	      else if (add_effect->w_is_goal)
	        /** 
		  Aggiorno il vettore dei fatti critici veri 
		  **
		  I update the array of the critical true facts
		**/
		vectlevel[next_level]->true_crit_vect[GUID_BLOCK (cel)] |=
		  GUID_MASK (cel);
	    }
	}
#ifdef __MY_OUTPUT__
      else
	printf ("\n Error fact position %s (fact %d) level %d",
		print_ft_name_string (cel, temp_name), cel, next_level);
#endif      
    }
  /** 
    Associo a j (variabile locale di tipo int) la posizione corrispondente all'azione 
    **
    I associate to j (local variable of int type) the position correspondent to the action
  **/
  j = vectlevel[level]->action.position;
  /**
    Pongo uguale a -1 action.position (l'azione non e' piu' inserita nell'action subgraph) 
    **
    I place equal to the -1 action.position (the action is not more inserted in the action subgraph)
  **/
  vectlevel[level]->action.position = -1;

  // Now, remove the ME relations with the action removed 
  check_prec_add_list (infAction);
  vectlevel[level]->action.being_removed = FALSE;
  remove_numeric_effects_of_action (act_pos, level);

  /**
    rimuove le false incosistenze dalla lista (necessario, perchè quando nella propagazione effettuo 
    una copia del livello, le inconsistenze risolte in questo modo non vengono rimosse
    **
    it removes the false incosistences from the list (necessary, because when in the propagation I make
    a copy of the level, the resolved inconsistences in this way do not be removed
  **/
  clean_unsup_num_fact ();

#ifdef _TEST_PROPAG_
  printf ("\n&&&&&&&&&&&&&&&&\n IIIOOO Dopo aver rimosso l'azione ");
  print_op_name (act_pos);
  printf (", livello %d", level);
  print_num_levels_and_actions ();

#endif
  if (GpG.temporal_plan)
    {
      vectlevel[level]->action.position = j;
      if (DEBUG4)
	printf ("\n\n -+- TEMPORAL -+-\n");
      update_time (infAction);

#ifdef __TEST__
      check_prop_level_index ();
      check_matrix ();
      check_act_ord_vect ();

#endif
    }
  vectlevel[level]->action.position = -1;

  reset_computed_dg_costs (level);

#ifdef __TEST__
  printf ("\n End IRA %s lev %d is_used %d", act->name, *infAction->level,
	  infAction->w_is_used);
  printf ("\n End IRA ");
  if (DEBUG4)
    {
      print_unsup_fact_vect ();
      print_unsup_num_facts ();
      print_unsup_timed_fact ();
    }
#endif

  if (DEBUG6 && num_try > 1)
    {
      print_num_levels_and_actions ();
      print_actions_in_subgraph ();
    }

  if (infAction -> PC_interval)
    free(infAction -> PC_interval);
  infAction -> PC_interval = NULL;

  return (TRUE);
}


/**  OK 23-07-04
 * Name: insert_remove_action
 * Scopo: inserire o rimuovere un azione del vicinato
 * Tipo: int
 * Input: int act_pos (posizione dell'azione)
 *        int act_level (livello da cui dovrebbe essere rimossa l'azione)
 *        int propagation
 *        int ins_rem
 * Output: 0 se la rimozione e' andata a buon fine
 * Strutture dati principali: GpG
 * Funzioni principali utilizzate: insert_action_in_vectlevel
 *                                 remove_action_from_vectlevel
 * Chiamata da: fix_unsup_num_fact
 *              fix_unsup_fact
 *              fix
 *              choose_actions
 *              iniz_random
 *              initialize
**
*  Name: insert_remove_action
*  Objective: to insert or to remove an action of environs
*  Type: int
*  Input: int act_pos (position of the action)
*         int act_level (level from which the action would have to be removed)
*         int propagation
*         int ins_rem
*  Output: 0 if the gone removal e' to good aim
*  Main Data Structures: GpG
*  Main Functions Used: insert_action_in_vectlevel
*                       remove_action_from_vectlevel
*  Call gives: fix_unsup_num_fact
*              fix_unsup_fact
*              fix
*              choose_actions
*              iniz_random
*              initialize
**/
int insert_remove_action (int act_pos, int act_level, int ins_rem, int propagation)
{
  /** 
    Variabili di appoggio 
    **
    Variable of support
  **/
  int i;

  //  check_plan (GpG.curr_plan_length);

#ifdef __TEST__
  {
    printf("\n--I1/R2 %d -- act %d  level %d  Numtry %d",ins_rem,act_pos,act_level,GpG.count_num_try);
    check_plan (GpG.curr_plan_length);
    if (GpG.temporal_plan)
      {
	check_prop_level_index ();
	check_matrix ();
	check_act_ord_vect ();
	check_temporal_plan ();
      }
    fflush(stdout);
  }
#endif

  //  my_print_plan_all (GpG.curr_plan_length);

  ind_remove_act_chain = 0;

  if ( GpG.remove_actions_in_next_step )
    {
      if(ind_remove_act_chain_next_step)
	memcpy (remove_act_chain, remove_act_chain_next_step, sizeof(int) * ind_remove_act_chain_next_step);
      
      ind_remove_act_chain =  ind_remove_act_chain_next_step;
      
      ind_remove_act_chain_next_step = 0;

      if (DEBUG2 && ind_remove_act_chain)
	{
	  printf("\n\nAzioni in remove_act_chain:");
	  for (i= 0 ; i < ind_remove_act_chain; i++ )
	    printf("\n%s",print_op_name_string(remove_act_chain[i]->position,temp_name));
	}
      
    }

  if (ins_rem == C_T_REMOVE_ACTION)
    remove_action_from_vectlevel (act_pos, act_level, propagation);
  /** 
    Se ins_rem!=C_T_REMOVE_ACTION viene inserita l'azione determinata da act_pos e act_level 
    **
    If ins_rem!=C_T_REMOVE_ACTION is inserted the action determined from act_pos and act_level
  **/
  else
    insert_action_in_vectlevel (act_pos, act_level);

  /**  
    cancelliamo le catene di azioni che supportano un solo fatto utile: 
    **
    we cancel the chains of actions that support a single useful fact:
  **/
  if (DEBUG2 && ind_remove_act_chain > 0 && num_try > 1)
    printf ("\nxXx Remove action in precondition chain:");

  for (i = 0; i < ind_remove_act_chain; i++)
    {

#ifdef __TEST__
      if (DEBUG6)
	print_num_levels_and_actions ();

#endif

      
      if(remove_act_chain[i]->w_is_goal > 0)
	continue;

      if(remove_act_chain[i]->position < 0)
	continue;


      remove_action_from_vectlevel (remove_act_chain[i]->position,
				      *remove_act_chain[i]->level, 1);

      //      check_plan (GpG.curr_plan_length);

#ifdef __TEST__
      check_plan (GpG.curr_plan_length);
      if (GpG.temporal_plan)
	{
	  check_prop_level_index ();
	  check_matrix ();
	  check_act_ord_vect ();
	  check_temporal_plan ();
	}

#endif
      remove_act_chain[i] = NULL;
    }

  //  my_print_plan_all (GpG.curr_plan_length);

  //  //  check_temporal_plan ();

#ifdef __TEST__
  check_plan (GpG.curr_plan_length);
  if (GpG.temporal_plan)
    {
      check_prop_level_index ();
      check_matrix ();
      check_act_ord_vect ();
      check_temporal_plan ();
      
      check_prev_and_next_links();
    }
  
  if (GpG.timed_facts_present)
     check_unsup_tmd();

#endif

  if (DEBUG5)
    {
      printf("\nUNSUP FACTS");
      print_unsup_fact_vect ();
      print_unsup_num_facts ();
      print_unsup_timed_fact ();
    }

  return 0;
}



/*********************************************
             INITIALIZATION
**********************************************/

/** ACTION SUBGRAPH OK 01-03-04
 * Name: reset_plan
 * Scopo: azzerare il piano (sia azioni che fatti)
 * Tipo: void
 * Input: int max_time
 * Output: nessuno
 * Strutture dati principali: GpG
 *                            vectlevel[]
 *                            inform
 * Funzioni principali utilizzate: reset_bitarray
 *                                 free_noop_not_in
 *                                 reset_computed_dg_costs
 *                                 copy_num_values_from_level_to_level
 *                                 reset_constraint_matrix
 *                                 reset_propagation_vect
 * Chiamata da: initialize
**
*  Name: reset_plan
*  Objective: to annul the plan (is actions that made)
*  Type: void
*  Input: int max_time
*  Output: none
*  Main Data Structures: GpG
*                        vectlevel[ ]
*                        inform
*  Main Functions Used: reset_bitarray
*                       free_noop_not_in
*                       reset_computed_dg_costs
*                       copy_num_values_from_level_to_level
*                       reset_constraint_matrix
*                       reset_propagation_vect
*  Call gives: initialize
**/
void reset_plan (int max_time)
{
  /** 
    Variabili di appoggio 
    **
    Variable of support
  **/
  FctNode_list inf_f;
  NoopNode_list inf_n;
  ActNode_list inf_a;

  int i, j, time;
  /** 
    Assegno a max_time la lunghezza del piano 
    **
    I assign to max_time the length of the plan
  **/
  max_time = GpG.max_plan_length;	// non occorre passare max_time come parametro
  /** 
    Azzeramento dei campi di GpG riferiti ai fatti 
    **
    Setting to zero the fields of GpG referenced to the facts
  **/
  GpG.num_false_fa = 0;
  GpG.num_false_act = 0;

  /**
    Azzero l'array dei fatti numerici non supportati
    **
    I annul the array of the numerical facts not supported
  **/
  for (i = 0; i < GpG.num_false_num_fa; i++)

    {
      vectlevel[*(unsup_num_fact[i]->level)]->numeric->
	false_position[unsup_num_fact[i]->fact] = -1;
    }
  /**
    Azzero i timed fact inconsistenti
    **
    I annul the inconsistent timed fact
  **/
  if(GpG.timed_facts_present)
    for (i = 0; i < GpG.num_false_tmd_fa; i++) {
      vectlevel[*(unsup_tmd_facts[i]->level)]->
	fact[unsup_tmd_facts[i]->fact].false_position = -1;
    }

  GpG.num_false_tmd_fa = 0;
  GpG.num_false_num_fa = 0;
  GpG.num_false_tot = 0;
  GpG.num_prec = 0;
  GpG.num_m_e = 0;
  GpG.num_actions = 0;
  GpG.total_cost = GpG.total_time = 0.0;
  GpG.total_cost_from_metric = 0.0;

  //  GpG.weight_cost = GpG.orig_weight_cost;
  //  GpG.weight_time = GpG.orig_weight_time;
  GpG.current_lm = 0;		// LM


 for (i = 0; i < gnum_comp_var; i++)
   {
    vectlevel[0]->numeric->values[i] = ginitial_state.V[i];
    vectlevel[0]->numeric->values_after_start[i]= ginitial_state.V[i];
   }

  /* GpG.min_inc=10;  Now set the minimum number of inconsistence after which we can store a quasi-solution */
  for (time = 0; time < max_time; time++)

    {

      if (vectlevel[time] == NULL)
	continue;

      //per sicurezza resetto le false_position e w_is_goal
      memset (vectlevel[time]->numeric->false_position, -1,  gnum_comp_var * sizeof (int));
      memset (vectlevel[time]->numeric->w_is_goal, 0,   gnum_comp_var * sizeof (short));

      if ((GpG.timed_facts_present) && (vectlevel[time] -> action.PC_interval != NULL))
	memset (vectlevel[time] -> action.PC_interval, -1, gnum_timed_facts * sizeof (int));

      if (time != 0)
	copy_num_values_from_level_to_level (0, time, FALSE);
      vectlevel[time]->level = time;
      vectlevel[time]->num_actions = 0;
      vectlevel[time]->modified = 0;

      reset_bitarray (vectlevel[time]->prec_vect, gnum_ft_block);
      vectlevel[time]->num_prec = 0;
      reset_bitarray (vectlevel[time]->fact_vect, gnum_ft_block);

      if (GpG.derived_predicates)
	initialize_dp_num_prec_vector(&vectlevel[time] -> gnum_dp_precs);

      vectlevel[time]->num_fact = 0;
      reset_bitarray (vectlevel[time]->true_crit_vect, gnum_ft_block);
      vectlevel[time]->num_true_crit = 0;
      reset_bitarray (vectlevel[time]->false_crit_vect, gnum_ft_block);
      vectlevel[time]->num_false_crit = 0;

      reset_bitarray (vectlevel[time]->noop_act_vect, gnum_ft_block);
      reset_bitarray (vectlevel[time]->noop_prec_act_vect, gnum_ft_block);
      if (GpG.derived_predicates)
	reset_bitarray (vectlevel[time]->active_rules, gnum_dp_block);

      for (i = 0; i < GpG.max_num_facts; i++)

	{
	  CONVERT_FACT_TO_VERTEX (i)->step = -2000;
	  CONVERT_FACT_TO_VERTEX (i)->numR = -2000;

	  inf_f = &vectlevel[time]->fact[i];
	  inf_f->w_is_goal = 0;
	  inf_f->w_is_derived_goal = 0;
	  inf_f->w_is_derived_true = 0;
	  inf_f->w_is_used = 0;
	  inf_f->w_is_true = 0;
	  inf_f->false_position = -1;

          /**
	    Pone a 1.0 i moltiplicatori di Lagrange fissi nel gef_conn se e' non impostata la modalita' multilevel
	    **
	    It set to 1.0 the Lagrange multiplyer fixed in the gef_conn if is not set the multilevel modality
	  **/
	  if (!GpG.lm_multilevel)
	    { 
	      CONVERT_FACT_TO_VERTEX (i)->lamda_prec   = 1.0; 
	      CONVERT_FACT_TO_VERTEX (i)->lamda_me     = 1.0;	
	      CONVERT_FACT_TO_VERTEX (i)->last_lm_me   =   0;
	      CONVERT_FACT_TO_VERTEX (i)->last_lm_prec =   0;	
	    }

	  inf_f->time_f = NOTIME;
	  inf_f->action_f = NULL;
	  
	  // NOOPS
	  inf_n = &vectlevel[time]->noop_act[i];
	  inf_n->w_is_goal = 0;
	  inf_n->w_is_used = 0;
	  inf_n->w_is_true = 0;
	  inf_n->w_is_overall = 0;
	  inf_n->false_position = -1;

	  inf_n->time_f = NOTIME;
	  inf_n->action_f = NULL;
	}

      inf_a = &vectlevel[time]->action;

      inf_a->w_is_goal = 0;
      inf_a->w_is_used = 0;
      inf_a->w_is_true = 0;
      inf_a->false_position = -1;

      inf_a->position = -1;
      inf_a->being_removed = 0;
      free_noop_not_in (inf_a);
      vectlevel[time]->max_action_time = 0.0;

      inf_a->time_f = NOTIME;
      inf_a->action_f = NULL;
      inf_a->ord_pos = 0;

      
      reset_computed_dg_costs (time);

      /**
	 Pone a 1.0 i moltiplicatori di Lagrange posizionati nei vari livelli se e' impostata la modalita' multilevel
	 **
	 It set to 1.0 the Lagrange multiplyer posted in the levels if is set the multilevel modality
      **/
      if (GpG.lm_multilevel)
	for (i = 0; i < GpG.max_num_actions; i++) { 
	  vectlevel[time]->lambda_prec[i]= 1.0;
	  vectlevel[time]->lambda_me[i]  = 1.0;
	  vectlevel[time]->flag_decr_lm=0;      
	}  

      vectlevel[time] -> next = vectlevel[time] -> prev = NULL;
      vectlevel[time] -> num_actions_for_next_goals=0;
      vectlevel[time] ->seach_cost_for_next_goals=0.0;
      vectlevel[time] -> cost_actions_for_next_goals=0.0;
      vectlevel[time] -> step_computed_actions_for_next_goals=-2000;
    }
  
  vectlevel[0] -> next = &vectlevel[GpG.curr_plan_length] -> level;
  vectlevel[GpG.curr_plan_length] -> prev = &vectlevel[0] -> level;

  /**
     Pone a 1.0 i moltiplicatori di Lagrange fissi nel gef_conn se e' non impostata la modalita' multilevel
     **
     It set to 1.0 the Lagrange multiplyer fixed in the gef_conn if is not set the multilevel modality
  **/
  if (!GpG.lm_multilevel)
    for (i = 0; i < GpG.max_num_actions; i++){
      CONVERT_ACTION_TO_VERTEX (i)->lamda_prec   = 1.0;      
      CONVERT_ACTION_TO_VERTEX (i)->lamda_me     = 1.0;	
      CONVERT_ACTION_TO_VERTEX (i)->last_lm_me   =   0;
      CONVERT_ACTION_TO_VERTEX (i)->last_lm_prec =   0;	
      CONVERT_ACTION_TO_VERTEX (i)->step =       -2000;
      CONVERT_ACTION_TO_VERTEX (i)->flag_decr_lm = 0;;
    }

  for (i = 0; i < MAX_PLAN_LENGTH; i++)
    {
      remove_act_chain[i] = NULL;
      if ( GpG.remove_actions_in_next_step )
	remove_act_chain_next_step[i] = NULL;
    }

  ind_remove_act_chain = 0;
  if ( GpG.remove_actions_in_next_step )
    ind_remove_act_chain_next_step = 0;

  reset_constraint_matrix ();
  reset_propagation_vect ();


  if(GpG.timed_facts_present)
    {
      for (i=0; i < gnum_timed_facts; i++)
	for (j=0; j < gnum_tmd_interval[i]; j++)
	  {
	    gtimed_fct_vect[i][j].num_act_PC = 0;
	  }

      //      insert_initial_timed_actions();
      
    }
}


/** ACTION SUBGRAPH OK 26-07-04
 * Name: iniz_random
 * Scopo: inserire azioni casualmente nell'action subgraph
 * Tipo: void
 * Input: int max_time
 * Output: nessuno
 * Strutture dati principali: GpG
 * Funzioni principali utilizzate: insert_remove_action
 * Chiamata da: initialize
**
*  Name: iniz_random
*  Objective: to random insert actions in the action subgraph
*  Type: void
*  Input: int max_time
*  Output: none
*  Main Data Structures: GpG
*  Main Functions Used: insert_remove_action
*  Call gives: initialize
**/
void iniz_random (int max_time)
{
  /** 
    Variabili di appoggio 
    **
    Variable of support
  **/
  int i, time;
  for (time = 0; time < max_time; time++)
    for (i = 0; i < GpG.max_num_actions; i++)
      if (CHECK_ACTION_POS (i, time) && (MY_RANDOM % 200) == 0)
	{
	  /** 
	    Inserimento di azioni 
	    **
	    Insertion of actions
	  **/
	  insert_remove_action (i, time, C_T_INSERT_ACTION,
				GpG.approximation_level);
	}
}


void insert_timed_facts_in_vectlevel( void ) {
  int i, j, tf;
  Bool found;
  if (gtimed_facts_idx) {
    for (i = 0; i < gnum_tmd_init_fcts; i++) {
      tf = gtimed_facts_idx[i];
      found = FALSE;
      for (j = 0; vectlevel[j]; j++)
	if (vectlevel[j] -> action.position == tf) {
	  found = TRUE;
	  break;
	}
      if (!found)
	insert_action_in_vectlevel (tf, gef_conn[tf].level);
    }
  }
  else {
    printf("\nerror : search for timed init facts first!");
    exit(1);
  }
}


/** OK 26-07-04
 * Name: initialize
 * Scopo: Inizializzare la struttura TA-graph, inserendo azioni
 * Tipo: int
 * Input: State *start_state
 *        State *end_state
 *        int num_run
 * Output: TRUE se tutto e' andato a buon fine
 * Strutture dati principali: GpG
 *                            vectlevel[]
 *                            State
 *                            geff_conn[]
 *                            treated_c_l[]
 * Funzioni principali utilizzate: reset_plan
 *                                 forward_noop_propagation
 *                                 forward_noop_propagation_time
 *                                 insert_unsup_fact
 *                                 backward_precond_propagation
 * Chiamata da: main
 *              LocalSearch
**
* Name: initialize
* Objective: initialize the TA-graph structure, inserting actions
* Type: int
* Input: State *start_state
*        State *end_state
*        int num_run
* Output: TRUE if all is gone to good aim
* Main Data Structures: GpG
*                       vectlevel[ ]
*                       State
*                       geff_conn[ ]
*                       treated_c_l[ ]
* Main Functions Used: reset_plan
*                      forward_noop_propagation
*                      forward_noop_propagation_time
*                      insert_unsup_fact
*                      backward_precond_propagation
* Call gives: main
*             LocalSearch
**/
int initialize (State * start_state, State * end_state, int num_restart)
{
  /** 
    Variabili di appoggio 
    **
    Variable of support
  **/
  /** 
    time verra' utilizzata per scorrere i livelli del piano 
    **
    Time will be used to slide the levels of the plan
  **/
  /** 
    num_unsupported per determinare il numero di fatti non supportati 
    **
    num_unsupported to determinate the number of facts not supported
  **/
  int time, i, num, num_act, num_false_act, num_unsupported, num_min;
  int num_neg, choice, j, el;
 
  /** 
    Strutura FtConn *vertex_ft che sara' utilizzata per contenere informazioni sui fatti 
    **
    Strutura FtConn *vertex_ft that will be used to contain informations of the facts
  **/
  FtConn *vertex_ft;
  /** 
    Strutture inform utilizzate per contenere informazioni relative a fatti 
    **
    Inform structures used to contain information relative to facts
  **/
  FctNode_list fa, inf_fact, infEl;
  NoopNode_list tofix;
  /** 
    Vettore di tipo inform che conterra i fatti non soppertati
    **
    Array of inform type that will contain the facts not soppertati
  **/
  FctNode_list false_init_facts[MAX_FALSE];
  
  PlanAction *temp_act;
  if (DEBUG1)
    printf ("\n INITIALIZE: ");
  //  num_restart++;

  /** 
    Assegno all'intero time la lunghezza del piano 
    **
    I assign to the integer Time the length of the plan
  **/
  time = GpG.curr_plan_length = GpG.fixpoint_plan_length;
  num_try = INITIALIZE_STEP;


  GpG.restart_search = TRUE;

 
  if ((GpG.num_solutions || 
       (GpG.timed_facts_present && GpG.num_quasi_solution)) 
      && ((num_restart % 3) ))
    {
      time = GpG.input_plan_lenght;
      GpG.curr_plan_length = GpG.input_plan_lenght;
    }

  /* setup the goal array at max time: lookup global 
   * goal strings from fact_table[max time]
   */ 
  if(time+1<GpG.max_plan_length)
    for(i=time+1;i<GpG.max_plan_length;i++)
      temp_vectlevel[GpG.max_temp_vect++] = vectlevel[i];
  
  if(time>=GpG.max_plan_length)
    for(i=GpG.max_plan_length;i<=time;i++)
      vectlevel[i]=temp_vectlevel[--GpG.max_temp_vect];
  
  GpG.max_plan_length=time+1;
  reset_plan (GpG.max_plan_length); 
 
  if (DEBUG6)
		{
		  printf("\n After Reset plan Lev %d",GpG.curr_plan_length);
		  print_num_levels_and_actions ();
		  if (GpG.temporal_plan)
		    print_temporal_plan (GpG.curr_plan_length);
		}

  /** 
    Inizializzo la variabile num_unsupported (numero dei fatti non supportati) con il valore 0 
    **
    I initialize the num_unsupported variable (number of the facts not supported) with value 0
  **/
  num_unsupported = 0;
  /** 
    Scorro i fatti (sia numerici che non) associati end_state 
    **
    I slide the facts (both numerical and not) associateed to end_state
  **/
  for (i = 0; i < end_state->num_F; i++)
    /** 
      Se e' presente un fatto 
      **
      If is present a fact
    **/
    if(end_state->F[i]>=0)
    {
      /** 
	Assegno a vertex_ft le caratteristiche del fatto 
	**
	I assign to vertex_ft the characteristics of the fact
      **/
      vertex_ft = &gft_conn[end_state->F[i]];
      CONVERT_FACT_TO_VERTEX (end_state->F[i])->lamda_prec = CONVERT_FACT_TO_VERTEX (end_state->F[i])->lamda_me = 1.0;	//  LM
      /** 
	Assegno al campo w_is_true dell'inform corrispondente al fatto TRUE (il fatto e' 
	precondizione dell'azione nel livello) 
	**
	I assign to the field w_is_true of inform correspondent to the TRUE fact (the fact is
	precondition of the action in the level)
      **/
      CONVERT_FACT_TO_NODE (end_state->F[i], time)->w_is_goal = TRUE;

      /** 
	Assegno al campo w_is_goal dell'inform corrispondente al fatto TRUE (il fatto e' 
	precondizione di azione nei livelli superiori) 
	**
	I assign to the field w_is_goal of the correspondent inform to the TRUE fact (the fact is
	precondition of action in the advanced levels)
      **/
      CONVERT_FACT_TO_NODE (end_state->F[i], time)->w_is_used = TRUE;	// Used for the noop propagation
      /** 
	Inserisco il fatto nel vettore dei fatti non supportati (unsup_vect[]) 
	**
	I insert the fact in the array of the facts not supported (unsup_vect[ ])
      **/
      insert_unsup_fact (CONVERT_FACT_TO_NODE (end_state->F[i], time));
      false_init_facts[num_unsupported] =CONVERT_FACT_TO_NODE (end_state->F[i], time);
      /** 
	Aumento di uno l'intero corrispondente al numero di fatti non supportati 
	**
	I increase of one the integer correspondent to the number of facts not supported
      **/
      num_unsupported++;
      /** 
	Aggiorno il campo prec_vect delle precondizioni (di vectlevel) 
	**
	I update the field prec_vect of the preconditions (of vectlevel)
      **/
      vectlevel[time]->prec_vect[GUID_BLOCK (vertex_ft->position)] |=GUID_MASK (vertex_ft->position);
      /** 
	Aggiorno il campo false_critic_vect dei fatti falsi (di vectlevel) 
	**
	I update the field false_critic_vect of the false facts (of vectlevel)
      **/
      vectlevel[time]->false_crit_vect[GUID_BLOCK (vertex_ft->position)] |=GUID_MASK (vertex_ft->position);
      /** 
	Propagazione indietro delle precondizioni 
	**
	Backward propagation of the preconditions
      **/
      backward_precond_propagation (CONVERT_FACT_TO_NODE(end_state->F[i], time));
      /** 
	Se il numero di precondizioni non supportate e' maggiore di MAX_GOAL esce 
	**
	If the number of preconditions not supported is greater of MAX_GOAL it exits
      **/
      if (num_unsupported > MAX_GOALS)

	{
	  printf ("\n\nipp-d: increase MAX_GOALS( preset value: %d )",
		  MAX_GOALS);
	  exit (1);
	}
    }
    else
      {
	j=-end_state->F[i];
	/** 
	  Aggiornamento di w_is_goal per fatti numerici 
	  **
	  Updating of w_is_goal for numerical facts
	**/
	vectlevel[time]->numeric->w_is_goal[j]++;
	if(!is_num_prec_satisfied (j, time))
          /** 
	    Inserimento dei fatti numerici non supportati 
	    **
	    Insertion of the numerical facts not supported
	  **/
	  insert_unsup_numeric_fact( j,time);
      }
  /** 
    Aggiorno il campo num_prec (di vectlevel[]) con il numero di precondizioni non supportate 
    **
    I update the field num_prec (of vectlevel[ ]) with the number of preconditions not supported
  **/
  vectlevel[time]->num_prec = num_unsupported;
  /** 
    Aggiorno il campo num_prec (di GpG) con il numero di precondizioni non supportate 
    **
    I update the field num_prec (of GpG) with the number of preconditions not supported
  **/
  GpG.num_prec = num_unsupported;
  if (GpG.temporal_plan)
    GpG.forward_time = 1;

  /* setup the intial facts: lookup global
   * fact strings from fact_table[0]
   */

  /** 
    Scorro i fatti (sia numerici che non) associati start_state 
    **
    I slide the facts (both numerical and not) associated to start_state
  **/
  for (num = 0, i = 0; i < start_state->num_F; i++, num++)
    {
      /** 
	Assegno a vertex_ft le caratteristiche del fatto 
	**
	I assign to vertex_ft the characteristics of the fact
      **/
      vertex_ft = &gft_conn[start_state->F[i]];
      /** 
	Assegno a fa l'inform del fatto e pongo w_is_true (precondizione di azione del livello) a TRUE 
	**
	I assign fa the inform of the fact and I place w_is_true (precondition of action of the level) to TRUE
      **/
      (fa = CONVERT_FACT_TO_NODE (start_state->F[i], 0))->w_is_true = TRUE;

      calc_new_derived_predicates(start_state->F[i], 0, ADD_FACT, NULL);

      vectlevel[0]->fact_vect[GUID_BLOCK (vertex_ft->position)] |=
	GUID_MASK (vertex_ft->position);
      /** 
	Se fa e' precondizione di azioni nei livelli superiori 
	**
	If fa is precondition of actions in the advanced levels
      **/
     if (fa->w_is_goal)
	{
	  /** 
	    Aggiorno i campi di vectlevel associati ai fatti critici veri e ai fatti critici falsi 
	    **
	    I update the fields of vectlevel associated to the critical true facts and to the critical false facts
	  **/
	  vectlevel[0]->true_crit_vect[GUID_BLOCK (vertex_ft->position)] |=
	    (GUID_MASK (vertex_ft->position));
	  vectlevel[0]->false_crit_vect[GUID_BLOCK (vertex_ft->position)] &=
	    ~(GUID_MASK (vertex_ft->position));
	}
      
      /** 
	propagazione delle noop (in avanti) dei fatti iniziali 
	**
	propagation of the noop (in ahead) of the initials facts
      **/
      if(GpG.timed_facts_present)
	{
	  if (gft_conn[start_state->F[i]].fact_type == IS_TIMED)
	    continue;
	}
      
      forward_noop_propagation (start_state->F[i], 0);
      
      {
	/** 
	   Pongo a zero il tempo di veridicita' dei fatti 
	   **
	   I place to zero the time of veridicity of the facts
        **/
	vectlevel[0]->fact[start_state->F[i]].time_f = 0.0;
	vectlevel[0]->fact[start_state->F[i]].action_f = NULL;
	/** 
	   Propagazione dei tempi delle noop associate ai fatti 
	   **
	   Propagation of the times of the noop associated to the facts
	**/
	forward_noop_propagation_time (&vectlevel[0]->
				       noop_act[start_state->F[i]]);
      }
    }

 if (DEBUG6)
		{
		  printf("\n After propagation Lev %d",GpG.curr_plan_length);
		  print_num_levels_and_actions ();
		  if (GpG.temporal_plan)
		    print_temporal_plan (GpG.curr_plan_length);
		}

#ifdef __TEST__
  if (GpG.temporal_plan)
    check_temporal_plan ();

#endif
  /** 
    Assegno a num_fact (numero dei fatti veri nel livello) num 
    **
    I assign to num_fact (number of the true facts in the level) num
  **/
  vectlevel[0]->num_fact = num;
  /** 
    Pongo num a 0 
    **
    I place num to 0
  **/
  num = 0;
  /** 
    Se il piano e' adattato o ho gia' un numero di soluzioni 
    **
    If the plan is adapted or I have already a number of solutions
  **/
  if ( (GpG.initialize == PLAN_ADAPT || 
	(GpG.num_solutions || 
	 (GpG.timed_facts_present && GpG.num_quasi_solution)) ) && 
       (num_restart % 3))
    {
      if (DEBUG0)
	if (num_restart >= 1)
	  {
	    if(GpG.mode == INCREMENTAL)
	      {
		if (GpG.num_solutions>0)
		  printf (" using stored plan\n");
		else if (GpG.timed_facts_present && GpG.num_quasi_solution>0)
		  printf (" using stored quasi-solution\n");
	      }
	    else
	      printf (".\n");

	  }

      if (DEBUG2)
	printf ("\n   ==> Insert action from stored plan in present plan\n ");

      GpG.initialize_from = PLAN_ADAPT;
      if (GpG.num_solutions)

	{
	  time = GpG.input_plan_lenght;
	}
      /** 
	Scorro il piano 
	**
	I slide the plan
      **/
      for (temp_act = GpG.gplan_actions, i = 0; temp_act;
	   temp_act = temp_act->next, i++)
	{
	  if (DEBUG2)
	    printf ("\nInitialize->insert action %s  in level %d",
		    print_op_name_string (temp_act->act_pos, temp_name), i);

	  /** 
	    Aggiorno il numero di fatti falsi 
	    **
	    I update the number of false facts
	  **/
	  GpG.num_false_tot = (GpG.num_false_act + GpG.num_false_fa + GpG.num_false_num_fa + GpG.num_false_tmd_fa);

	  /** 
	    Se i e' maggiore del livello dell'azione (in cui dovrebbe essere collocata) 
	    **
	    If i is greater than the level of the action (in which it would be placed)
	  **/
	  if(i>=gef_conn[temp_act->act_pos].level)
	    /** 
	      Inserisco l'azione nel livello 
	      **
	      I insert the action in the level
	    **/
	    insert_remove_action (temp_act->act_pos, i, C_T_INSERT_ACTION,
				  GpG.approximation_level);


	  /** 
	    Aggiorno il numero di fatti falsi 
	    **
	    I update the number of false facts
	  **/
	  GpG.num_false_tot = (GpG.num_false_act + GpG.num_false_fa + GpG.num_false_num_fa + GpG.num_false_tmd_fa);
	}
      /** 
	Fino a quando non sono stati eliminati tutti i fatti falsi 
	**
	Until have not been eliminated all the false facts
      **/
      while (GpG.num_false_act > 0)
	{
	  /** 
	    Ricavo l'inform della noop (corrispondente al fatto) minacciata dal vettore delle 
	    noop minacciate (treated_c_l) 
	    **
	    I obtain the inform of the noop (correspondent to the fact) threatened by the array of
	    noop threatened (treated_c_l)
	  **/
	  tofix = CONVERT_NOOP_TO_NODE (treated_c_l[0]->fact,
				    *treated_c_l[0]->level);
	  /** 
	    Assegno a num_false act la posizione della noop  
	    **
	    I assign to num_false act the position of the noop
	  **/
	  num_false_act = define_neighborhood_for_threats (tofix, GpG.curr_plan_length);
	  /** 
	    Rimozione della noop dal vettore delle noop minacciate (treated_c_l[]) 
	    **
	    Removal of the noop from the array of the noop threatened (treated_c_l[ ])
	  **/
	  if (num_false_act <= 0) {
	    remove_treated_noop (tofix);
	  }
	}
      /** 
	Aggiorno il numero di fatti_falsi 
	**
	I update the number of false facts
      **/
      GpG.num_false_tot =
	(GpG.num_false_act + GpG.num_false_fa + GpG.num_false_num_fa + GpG.num_false_tmd_fa);
    
    }

  else if (GpG.initialize == INIT_EMPTY_PLAN)

    {
      if (DEBUG0)
	if (num_restart >= 1)
	  {
	    if (GpG.mode == INCREMENTAL)
	      printf (" using null plan\n");
	    else
	      printf(".\n");
	  }
      GpG.initialize_from = INIT_EMPTY_PLAN;
      //return TRUE;
    }

  else

    {
      if (DEBUG1)
	printf ("\nInitialize random:  ");
      if (GpG.initialize == INIT_RANDOM)
	iniz_random (time);
      else
	/** 
	  Fino a che num e' diverso dal numero dei fatti falsi 
	  **
	  Until num is not equal to the number of the false facts
	**/
	while (num != num_unsupported)
	  {
	    /** 
	      Associo a inf_act l'inform relativo a un fatto falso 
	      **
	      I associate to inf_act the inform relative to a false fact
	    **/
	    inf_fact = false_init_facts[num];
	    /** 
	      Assegno a num_act il numero di azioni (del vicinato) che risolvono un incosistenza 
	      **
	      I assign to num_act the number of actions (of environs) that they resolve a incosistence
	    **/
	    num_act = define_neighborhood(inf_fact, -1);
	    /** 
	      Se non esistono azioni che risolvono l'inconsistenza o il fatto e' gia' supportatato 
	      **
	      If do not exist actions that resolve the inconsistence or the fact is already supported
	    **/
	    if (num_act <= 0 || inf_fact->w_is_true)
	      {
		num++;
		continue;
	      }

	    /* got an array of actions that satisfy the goal, and choose the one with minor cost */
	    if (GpG.initialize == INIT_GOAL)
	      {
		if (DEBUG1)
		  printf ("\nInitialize initial goal:  ");
		if (num_act == 1)
		  choice = 0;
		else
		  choice = MY_RANDOM % num_act;
		/** 
		  Assegno a choice il numero di una azione del vicinato con minor costo 
		  **
		  I assign to choice the number of one action of environs with minor cost
		**/
		choice = pos_temp_vect[choice];
	      }
	    else
	      {
		//messo null per togliere lo warning!
		printf ("\nWARNING: shouldnt get here!!!exiting..\n\n");
		exit (0);
		find_min (NULL /*inf_fact */ , pos_temp_vect, num_act,
			  &num_min, &num_neg);
		if (GpG.initialize == INIT_MIN_GOAL)
		  {
		    if (num_min == 1)
		      choice = 0;

		    else
		      choice = MY_RANDOM % num_min;
		    /** 
		      Assegno a choice il numero di una azione del vicinato con minor costo 
		      **
		      I assign to choice the number of one action of environs with minor cost
		    **/
		    choice = pos_temp_vect[choice];
		  }
		else
		  {
		    /** 
		      set true an action of temp_vect[pos_temp_vect[0]] because the low cost 
		      **
		      set true an action of temp_vect[pos_temp_vect[0 ] ] because the low cost
		    **/
		    choice = 0;
		    /** 
		      Assegno a choice il numero di una azione del vicinato con minor costo 
		      **
		      I assign to choice the number of one action of environs with minor cost
		    **/
		    choice = pos_temp_vect[choice];
		  }
	      }

	    // Insert unsupported fa->preconds in false_init_facts
	    for (j = 0; j < gef_conn[neighb_vect[choice]->act_pos].num_PC;
		 j++)
	      {
		/** 
		  Associo a el l'intero corrispondente alla precondizione 
		  **
		  I associate to el the correspondent integer to the precondition
		**/
		el = gef_conn[neighb_vect[choice]->act_pos].PC[j];
		if (el < 0)
		  continue;
		/** 
		  Controllo sulla posizione dell'azione 
		  **
		  Control on the position of the action
		**/
		if (CHECK_ACTION_POS (el, neighb_vect[choice]->act_level))
		  {
		    /** 
		      Associo infEl l'inform corrispondente al fatto 
		      **
		      I associate infEl the inform correspondent to the fact
		    **/
		    infEl = CONVERT_FACT_TO_NODE (el,neighb_vect[choice]->act_level);
		    /** 
		      Se il fatto non e' supportato 
		      **
		      If the fact is not supported
		    **/
		    if (infEl->w_is_true == 0)
		      /** 
			Pongo il fatto nel vettore dei fatti non supportati 
			**
			I place the fact in the array of the facts not supported
		      **/
		      false_init_facts[num_unsupported++] = infEl;
		  }
	      }
	    /** 
	      Aumento num 
	      **
	      I increase num
	    **/
	    num++;
	    /** 
	      Chiamo Insert_remove_action per risolvere l'inconsistenza 
	      **
	      I call Insert_remove_action to resolve the inconsistence
	    **/
	    insert_remove_action (neighb_vect[choice]->act_pos,
				  neighb_vect[choice]->act_level,
				  neighb_vect[choice]->constraint_type,
				  GpG.approximation_level);
	  }
    }

#ifdef __TEST__
  printf ("\n END INITIALIZE  - Memoria allocata %ld [kb]",
	  tot_alloc_mem_size / 1024);

#endif
  if (DEBUG2)
    {
      printf ("\n END INITIALIZE");
    }

  /*
  if (GpG.timed_facts_present)
    insert_timed_facts_in_vectlevel();
  */

  GpG.restart_search = FALSE;

  return (TRUE);
}


/***************************************
            MAKE INCONSISTENCES
 ***************************************/




/** 
 * Name: restart_MetricTemporalCost
 * Scopo: E' richiamata in fase di ottimizzazione e sceglie un insieme di azioni da rimuovere.
 *        Scegliamo le azioni che incidono sulla durata totale del piano
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: restart_MetricTemporalCost
* Objective: Called during optimization, she choose a set of action to remove
*            We choose the action that   the total duration of the plan
* Type: void
* Input: none
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
void restart_MetricTemporalCost ()
{
  int i, j, level = 0, posGoal, indlevel, indDelete, save_level, pos_act, numgoal = 0;
  int delete_action_level[MAX_PLAN_LENGTH];
  float num_act, sum, time, timeGoal;
  FctNode_list infGoal;

#ifdef __TEST__
  int tot_act;
  tot_act = GpG.num_actions;
#endif

  //  printf("\n\nrestart_MetricTemporalCost");

  /**
     Azzero la lista delle azioni da cancellare
     **
     I set to zero the list of the actions to remove
  **/
  memset (delete_action_level, -1, MAX_PLAN_LENGTH * sizeof (int));

  indDelete = 0;

  timeGoal = 0.0;

  /**
     Partiamo dal goal con marca temporale piu' alta e li contiamo
     **
     We start from the goal with highest temporal setting
  **/
  for (i = 0; i < GpG.curr_goal_state->num_F; i++)
    {
      infGoal =
	CONVERT_FACT_TO_NODE (GpG.curr_goal_state->F[i],
				GpG.curr_plan_length);

      if (infGoal->w_is_true)
	{

	  if (infGoal->time_f > timeGoal)
	    {
	      numgoal = 1;
	      timeGoal = infGoal->time_f;
	    }
	  else if (infGoal->time_f == timeGoal)
	    numgoal++;
	}
    }

#ifdef __TEST__
  printf ("\nMax time goal:");
#endif

  for (i = 0; i < GpG.curr_goal_state->num_F; i++)
    {
      infGoal =
	CONVERT_FACT_TO_NODE (GpG.curr_goal_state->F[i],
				GpG.curr_plan_length);

      if (infGoal->w_is_true)
	{

	  /**
	    Solo i goal con marca temporale maggiore
	    **
	    Only goals with higher temporal setting
	  **/
	  if (infGoal->time_f == timeGoal)
	    {
	      posGoal = infGoal->position;

#ifdef __TEST__
	      printf ("\n");
	      print_ft_name (GpG.curr_goal_state->F[i]);
#endif
	      time = timeGoal;

	      if (vectlevel[GpG.curr_plan_length]->fact[GpG.curr_goal_state->F[i]].action_f == NULL)
		continue;
	      else
		level = *vectlevel[GpG.curr_plan_length]->fact[GpG.curr_goal_state->F[i]].action_f->level;

	      save_level = level;

	      do
		{
		  /**
		    Se arriviamo in fondo alla catena di azioni ripartiamo dall'inizio
		    **
		    If we arrive at the end of the chain of action we restart
		  **/
		  if (time == 0.0)
		    time = infGoal->time_f;

		  /**
		    Normalizziamo rispetto all'azione di durata minore
		    **
		    Normalizing than the action of minor duration
		  **/
		  
		  if (GpG.min_action_time == 0)
		    GpG.min_action_time = 1.0;

		  time = time / GpG.min_action_time;

		  if(time<1.0)
		    time=1.0;
		  
		  /**
		    Scegliamo un istante di tempo a caso
		    **
		    We choose random a temporal instant
		  **/
		  num_act = MY_RANDOM % ((int) time);

		  num_act = num_act * GpG.min_action_time;

		  for (sum = 0.0; level >= 0;)
		    {
		      /**
			Sommiamo i tempi delle azioni fino ad ora esaminate
			**
			We sum the temps of the action examined
		      **/
		      sum +=
			get_action_time (vectlevel[level]->action.position, level);

		      /** 
			 Se si eccede il limite di tempo casuale preso precedentemente
			 **
			 If we exceed the temporal limit
		      **/
		      if (sum >= num_act)
			{
			  /**
			     Inseriamo l'azione nella lista delle azioni da rimuovere
			     **
			     We insert the action in the list of action to remove
			  **/
			  delete_action_level[level] = level;
			  indDelete++;

#ifdef __TEST__ 
			  if (vectlevel[level]->action.position < 0)
			    printf ("\nERROR: Restart for temporal plan");
#endif

			  /**
			     Consideriamo l'istante in cui inizia l'azione
			     **
			     We consider the instant when the action start
			  **/
			  time = vectlevel[level]->action.time_f -
			    get_action_time (vectlevel[level]->action.position, level);
			  
			}
  
		      if (vectlevel[level]->action.action_f == NULL)
			level = save_level;
		      else
			level = *vectlevel[level]->action.action_f->level;

		      if (sum >= num_act)
			break;

		    }  //end for 

		} // end do
	      while (indDelete < ((GpG.num_actions / 5) / numgoal));	      	     
	     
	    }
	}
    }

  /**
     Togliamo dal action-graph eventuali azioni identiche
     **
     We remove to the action-graph any possible identical action
  **/
  for (level = 0; level < GpG.curr_plan_length; level++)
    {
      if (delete_action_level[level] >= 0)
	continue;

      for (indlevel = level + 1; indlevel < GpG.curr_plan_length; indlevel++)
	{

	  if (CHECK_ACTION_OF_LEVEL (level)
	      && GET_ACTION_POSITION_OF_LEVEL (level) ==
	      GET_ACTION_POSITION_OF_LEVEL (indlevel))
	    {
	      delete_action_level[indlevel] = indlevel;
	      delete_action_level[level] = level;
	      break;
	    }

	}
    }


#ifdef __TEST__
  printf ("\nAzioni tolte:");
  for (i = 0; i < GpG.curr_plan_length; i++)
    {
      if (delete_action_level[i] < 0)
	continue;
      printf ("%s",
	      print_op_name_string (vectlevel[i]->action.position,
				    temp_name));
    }
#endif

  /**
     Rimuoviamo le azioni scelte, le azioni che hanno come precondizione gli effetti dell'azione scelta e le azioni che hanno come effetto le precondizioni dell'azione scelta 
     ** 
     We remove the selected actions, the actions that has preconditions like the effects of the selected action and effect like the preconditions of the selected action
  **/
  for (i = 0; i < GpG.curr_plan_length; i++)
    {
      if (delete_action_level[i] < 0)
	continue;

      pos_act = vectlevel[delete_action_level[i]]->action.position;
      if (pos_act < 0)
	continue;

      /**
	 Rimuoviamo le azioni che hanno come precondizione gli effetti additivi dell'azione scelta da rimuovere
	 ** 
	 We remove the actions that has preconditions like the additive effects of the selected action to remove
      **/
      for (j = 0; j < gef_conn[pos_act].num_A; j++)
	{

	  if (gef_conn[pos_act].A[j] < 0)
	    continue;

	  indlevel = delete_action_level[i] + 1;
	  while (indlevel < GpG.curr_plan_length)
	    {

	      if (GET_ACTION_OF_LEVEL (indlevel))
		{
		  if ((is_fact_in_preconditions
		       (vectlevel[indlevel]->action.position,
			gef_conn[pos_act].A[j])
		       ||
		       (is_fact_in_preconditions_overall
			(vectlevel[indlevel]->action.position,
			 gef_conn[pos_act].A[j])
			&&
			!is_fact_in_additive_effects_start (vectlevel
							    [indlevel]->
							    action.position,
							    gef_conn[pos_act].
							    A[j])))
		      && vectlevel[indlevel]->action.position > 0)
		    insert_remove_action (vectlevel[indlevel]->action.
					  position, indlevel,
					  C_T_REMOVE_ACTION,
					  GpG.approximation_level);
		}

	      if (!vectlevel[indlevel]->noop_act[gef_conn[pos_act].A[j]].
		  w_is_used)
		break;

	      indlevel++;
	    }

	}

      /**
	 Rimuoviamo le azioni che hanno come precondizione gli effetti additivi at start dell'azione scelta da rimuovere
	 **
	 We remove the actions that has preconditions like the additive at start effects of the action selected to remove
      **/
      if (gef_conn[pos_act].sf)
	for (j = 0; j < gef_conn[pos_act].sf->num_A_start; j++)
	  {
	    if (gef_conn[pos_act].sf->A_start[j] < 0)
	      continue;

	    indlevel = delete_action_level[i] + 1;
	    while (indlevel < GpG.curr_plan_length)
	      {
		if (GET_ACTION_OF_LEVEL (indlevel))
		  {
		    if ((is_fact_in_preconditions
			 (vectlevel[indlevel]->action.position,
			  gef_conn[pos_act].sf->A_start[j])
			 ||
			 (is_fact_in_preconditions_overall
			  (vectlevel[indlevel]->action.position,
			   gef_conn[pos_act].sf->A_start[j])
			  &&
			  !is_fact_in_additive_effects_start (vectlevel
							      [indlevel]->
							      action.position,
							      gef_conn
							      [pos_act].sf->
							      A_start[j])))
			&& vectlevel[indlevel]->action.position > 0)
		      insert_remove_action (vectlevel[indlevel]->action.
					    position, indlevel,
					    C_T_REMOVE_ACTION,
					    GpG.approximation_level);
		  }

		if (!vectlevel[indlevel]->
		    noop_act[gef_conn[pos_act].sf->A_start[j]].w_is_used)
		  break;
		
		indlevel++;
	      }

	  }


      /**
	 Rimuoviamo le azioni che hanno come effetti additivi le precondizioni dell'azione scelta da rimuovere
	 **
	 We remove the actions that has additive effects like the preconditions of the action selected to remove
      **/
      for (j = 0; j < gef_conn[pos_act].num_PC; j++)
	{
	  if (gef_conn[pos_act].PC[j] < 0)
	    continue;

	  indlevel = delete_action_level[i];
	  while (indlevel > 0)
	    {

	      if (CHECK_FACT_POS (gef_conn[pos_act].PC[j], indlevel) == FALSE)
		break;

	      if (GET_ACTION_OF_LEVEL (indlevel - 1)
		  &&
		  (is_fact_in_additive_effects
		   (vectlevel[indlevel - 1]->action.position,
		    gef_conn[pos_act].PC[j])
		   ||
		   is_fact_in_additive_effects_start (vectlevel
						      [indlevel -
						       1]->action.position,
						      gef_conn[pos_act].
						      PC[j]))
		  && vectlevel[indlevel - 1]->action.position > 0)
		insert_remove_action (vectlevel[indlevel - 1]->action.
				      position, indlevel - 1,
				      C_T_REMOVE_ACTION,
				      GpG.approximation_level);


	      if (CHECK_NOOP_POS (gef_conn[pos_act].PC[j], indlevel - 1) ==
		  FALSE)
		break;

	      if (!vectlevel[indlevel - 1]->noop_act[gef_conn[pos_act].PC[j]].
		  w_is_used)
		break;

	      indlevel--;
	    }
	}

      /**
	 Rimuoviamo le azioni che hanno come effetti additivi le precondizioni overall dell'azione scelta da rimuovere
	 **
	 We remove the actions that has additive effects like the overall preconditions of the action selected to remove
      **/
      if (gef_conn[pos_act].sf)
	for (j = 0; j < gef_conn[pos_act].sf->num_PC_overall; j++)
	  {

	    if (gef_conn[pos_act].sf->PC_overall[j] < 0)
	      continue;

	    indlevel = delete_action_level[i];
	    while (indlevel > 0)
	      {

		if (CHECK_FACT_POS
		    (gef_conn[pos_act].sf->PC_overall[j], indlevel) == FALSE)
		  break;

		if (GET_ACTION_OF_LEVEL (indlevel - 1)
		    &&
		    (is_fact_in_additive_effects
		     (vectlevel[indlevel - 1]->action.position,
		      gef_conn[pos_act].sf->PC_overall[j])
		     ||
		     is_fact_in_additive_effects_start (vectlevel
							[indlevel -
							 1]->action.position,
							gef_conn[pos_act].sf->
							PC_overall[j]))
		    && vectlevel[indlevel - 1]->action.position > 0)
		  insert_remove_action (vectlevel[indlevel - 1]->action.
					position, indlevel - 1,
					C_T_REMOVE_ACTION,
					GpG.approximation_level);


		if (CHECK_NOOP_POS
		    (gef_conn[pos_act].sf->PC_overall[j],
		     indlevel - 1) == FALSE)
		  break;

		if (!vectlevel[indlevel - 1]->
		    noop_act[gef_conn[pos_act].sf->PC_overall[j]].w_is_used)
		  break;

		indlevel--;
	      }
	  }

      if (vectlevel[delete_action_level[i]]->action.position > 0)
	/**
	   Rimuoviamo l'azione scelta
	   **
	   We remove the selected action
	**/
	insert_remove_action (pos_act, delete_action_level[i],
			      C_T_REMOVE_ACTION, GpG.approximation_level);

    }

#ifdef __TEST__
  printf ("\n\nAzioni tolte: %d\n", tot_act - GpG.num_actions);
#endif

#ifdef TEST_GR
  fprintf (stderr, "/ ");
#endif

  return;
}


/** 
 * Name: restart_TimedFct
 * Scopo: E' richiamata in fase di ottimizzazione e sceglie un insieme di azioni da rimuovere.
 *        Scegliamo le azioni che incidono sulla durata totale del piano
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: restart_TimedFct
* Objective: Called during optimization, she choose a set of action to remove
*            We choose the action that influence the total duration of the plan
* Type: void
* Input: none
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
void restart_TimedFct ()
{
  int i, j, level = 0, indlevel, indDelete, save_level, pos_act;
  int delete_action_level[MAX_PLAN_LENGTH];
  float num_act, sum, time;

  ActNode_list infAct;

#ifdef __TEST__
  int tot_act;
  tot_act = GpG.num_actions;
#endif

  printf("\n\nrestart_TimedFct");

  /**
     Azzero la lista delle azioni da cancellare
     **
     I set to zero the list of the action to remove
  **/
  memset (delete_action_level, -1, MAX_PLAN_LENGTH * sizeof (int));

  indDelete = 0;

  for (i = 0; i < GpG.num_false_tmd_fa; i++)
    {
      level = *unsup_tmd_facts[i]->level;

      infAct = GET_ACTION_OF_LEVEL(level);
      
      if (infAct->action_f == NULL)
	continue;
	  
      save_level = level;

      time = infAct->time_f;

      do
	{
	  /** 
	     Se arriviamo in fondo alla catena di azioni ripartiamo dall'inizio
	     **
	     If we arrive to the end of the chain of the actions we restart from the begin
	  **/
	  if (time == 0.0)
	    time = infAct->time_f;
	  
	  /** 
	      Normalizziamo rispetto all'azione di durata minore 
	      **
	      We normalize in comparison with the action of smaller duration
	  **/
	  time = time / GpG.min_action_time;
	  
	  if(time<1.0)
	    time=1.0;
	  
	  /** 
	      Scegliamo un istante di tempo a caso 
	      **
	      We choose a random temporal instant
	  **/
	  num_act = MY_RANDOM % ((int) time);
	  
	  num_act = num_act * GpG.min_action_time;
	  
	  for (sum = 0.0; level >= 0;)
	    {
	      /** 
		  Sommiamo i tempi delle azioni fino ad ora esaminate 
		  **
		  We sum the temps of the actions examined
	      **/
	      sum +=
		get_action_time (vectlevel[level]->action.position, level);
	      /** 
		 Se si eccede il limite di tempo casuale preso precedentemente
		 **
		 If we exceed the time limit
	      **/
	      if (sum >= num_act)
		{
		  /** 
		     Inseriamo l'azione nella lista delle azioni da rimuovere 
		     **
		     We insert the action in the list of the action to remove
		  **/
		  //		  printf("\nAct to remove -> level %d\n",level);
		  delete_action_level[level] = level;
		  indDelete++;
		  
#ifdef __TEST__
		  if (vectlevel[level]->action.position < 0)
		    printf ("\nERROR: Restart for temporal plan");
#endif
		  
                  /**
		     Consideriamo l'istante in cui inizia l'azione
		     **
		     We consider the instant in which the action start
		  **/
		  time = vectlevel[level]->action.time_f -
		    get_action_time (vectlevel[level]->action.position, level);
		}
	      
	      if (vectlevel[level]->action.action_f == NULL)
		level = save_level;
	      else
		level = *vectlevel[level]->action.action_f->level;
	      
	      if (sum >= num_act)
		break;
	      
	    }  //end for 
	  
	} // end do
      while (indDelete < ((GpG.num_actions / 10) / GpG.num_false_tmd_fa));
    }


  /**
     Togliamo dal action-graph eventuali azioni identiche
     **
     We remove to the action-graph any possible identical action
  **/
   for (level = 0; level < GpG.curr_plan_length; level++)
    {
      if (delete_action_level[level] >= 0)
	continue;

      for (indlevel = level + 1; indlevel < GpG.curr_plan_length; indlevel++)
	{

	  if (GET_ACTION_POSITION_OF_LEVEL (level) > 0
	      && GET_ACTION_POSITION_OF_LEVEL (level) ==
	      GET_ACTION_POSITION_OF_LEVEL (indlevel))
	    {
	      delete_action_level[indlevel] = indlevel;
	      delete_action_level[level] = level;
	      break;
	    }

	}
    }


#ifdef __TEST__
  printf ("\nAzioni tolte:");
  for (i = 0; i < GpG.curr_plan_length; i++)
    {
      if (delete_action_level[i] < 0)
	continue;
      printf ("%s",
	      print_op_name_string (vectlevel[i]->action.position,
				    temp_name));
    }
#endif

  /**
     Rimuoviamo le azioni scelte, le azioni che hanno come precondizione gli effetti dell'azione scelta e le azioni che hanno come effetto le precondizioni dell'azione scelta 
     ** 
     We remove the selected actions, the actions that has preconditions like the effects of the selected action and effect like the preconditions of the selected action
  **/
  for (i = 0; i < GpG.curr_plan_length; i++)
    {
       
      if (delete_action_level[i] < 0)
	continue;

      pos_act = vectlevel[delete_action_level[i]]->action.position;
      if (pos_act < 0)
	continue;

      /**
	 Rimuoviamo le azioni che hanno come precondizione gli effetti additivi dell'azione scelta da rimuovere
	 ** 
	 We remove the actions that has preconditions like the additive effects of the selected action to remove
      **/
      for (j = 0; j < gef_conn[pos_act].num_A; j++)
	{

	  if (gef_conn[pos_act].A[j] < 0)
	    continue;

	  indlevel = delete_action_level[i] + 1;
	  while (indlevel < GpG.curr_plan_length)
	    {

	      if (CHECK_ACTION_OF_LEVEL (indlevel))
		{
		  if ((is_fact_in_preconditions
		       (vectlevel[indlevel]->action.position,
			gef_conn[pos_act].A[j])
		       ||
		       (is_fact_in_preconditions_overall
			(vectlevel[indlevel]->action.position,
			 gef_conn[pos_act].A[j])
			&&
			!is_fact_in_additive_effects_start (vectlevel
							    [indlevel]->
							    action.position,
							    gef_conn[pos_act].
							    A[j]))))
		    insert_remove_action (vectlevel[indlevel]->action.
					  position, indlevel,
					  C_T_REMOVE_ACTION,
					  GpG.approximation_level);
		}

	      if (!vectlevel[indlevel]->noop_act[gef_conn[pos_act].A[j]].
		  w_is_used)
		break;

	      indlevel++;
	    }

	}

      /**
	 Rimuoviamo le azioni che hanno come precondizione gli effetti additivi at start dell'azione scelta da rimuovere
	 **
	 We remove the actions that has preconditions like the additive at start effects of the action selected to remove
      **/
      if (gef_conn[pos_act].sf)
	for (j = 0; j < gef_conn[pos_act].sf->num_A_start; j++)
	  {
	    if (gef_conn[pos_act].sf->A_start[j] < 0)
	      continue;

	    indlevel = delete_action_level[i] + 1;
	    while (indlevel < GpG.curr_plan_length)
	      {

		if (CHECK_ACTION_OF_LEVEL (indlevel))
		  {
		    if ((is_fact_in_preconditions
			 (vectlevel[indlevel]->action.position,
			  gef_conn[pos_act].sf->A_start[j])
			 ||
			 (is_fact_in_preconditions_overall
			  (vectlevel[indlevel]->action.position,
			   gef_conn[pos_act].sf->A_start[j])
			  &&
			  !is_fact_in_additive_effects_start (vectlevel
							      [indlevel]->
							      action.position,
							      gef_conn
							      [pos_act].sf->
							      A_start[j]))))
		      insert_remove_action (vectlevel[indlevel]->action.
					    position, indlevel,
					    C_T_REMOVE_ACTION,
					    GpG.approximation_level);
		  }

		if (!vectlevel[indlevel]->
		    noop_act[gef_conn[pos_act].sf->A_start[j]].w_is_used)
		  break;

		indlevel++;
	      }

	  }

      /**
	 Rimuoviamo le azioni che hanno come effetti additivi le precondizioni dell'azione scelta da rimuovere
	 **
	 We remove the actions that has additive effects like the preconditions of the action selected to remove
      **/
      for (j = 0; j < gef_conn[pos_act].num_PC; j++)
	{
	  if (gef_conn[pos_act].PC[j] < 0)
	    continue;

	  indlevel = delete_action_level[i];
	  while (indlevel > 0)
	    {

	      if (CHECK_FACT_POS (gef_conn[pos_act].PC[j], indlevel) == FALSE)
		break;

	      if (CHECK_ACTION_OF_LEVEL (indlevel - 1)
		  &&
		  (is_fact_in_additive_effects
		   (vectlevel[indlevel - 1]->action.position,
		    gef_conn[pos_act].PC[j])
		   ||
		   is_fact_in_additive_effects_start (vectlevel
						      [indlevel -
						       1]->action.position,
						      gef_conn[pos_act].
						      PC[j])))
		insert_remove_action (vectlevel[indlevel - 1]->action.
				      position, indlevel - 1,
				      C_T_REMOVE_ACTION,
				      GpG.approximation_level);


	      if (CHECK_NOOP_POS (gef_conn[pos_act].PC[j], indlevel - 1) ==
		  FALSE)
		break;

	      if (!vectlevel[indlevel - 1]->noop_act[gef_conn[pos_act].PC[j]].
		  w_is_used)
		break;

	      indlevel--;
	    }
	}

      /**
	 Rimuoviamo le azioni che hanno come effetti additivi le precondizioni overall dell'azione scelta da rimuovere
	 **
	 We remove the actions that has additive effects like the overall preconditions of the action selected to remove
      **/
      if (gef_conn[pos_act].sf)
	for (j = 0; j < gef_conn[pos_act].sf->num_PC_overall; j++)
	  {

	    if (gef_conn[pos_act].sf->PC_overall[j] < 0)
	      continue;

	    indlevel = delete_action_level[i];
	    while (indlevel > 0)
	      {

		if (CHECK_FACT_POS
		    (gef_conn[pos_act].sf->PC_overall[j], indlevel) == FALSE)
		  break;

		if (CHECK_ACTION_OF_LEVEL (indlevel - 1)
		    &&
		    (is_fact_in_additive_effects
		     (vectlevel[indlevel - 1]->action.position,
		      gef_conn[pos_act].sf->PC_overall[j])
		     ||
		     is_fact_in_additive_effects_start (vectlevel
							[indlevel -
							 1]->action.position,
							gef_conn[pos_act].sf->
							PC_overall[j])))
		  insert_remove_action (vectlevel[indlevel - 1]->action.
					position, indlevel - 1,
					C_T_REMOVE_ACTION,
					GpG.approximation_level);


		if (CHECK_NOOP_POS
		    (gef_conn[pos_act].sf->PC_overall[j],
		     indlevel - 1) == FALSE)
		  break;

		if (!vectlevel[indlevel - 1]->
		    noop_act[gef_conn[pos_act].sf->PC_overall[j]].w_is_used)
		  break;

		indlevel--;
	      }
	  }

      if (vectlevel[delete_action_level[i]]->action.position > 0)
	/**
	   Rimuoviamo l'azione scelta
	   **
	   We remove the selected action
	**/
	insert_remove_action (pos_act, delete_action_level[i],
			      C_T_REMOVE_ACTION, GpG.approximation_level);

    }

#ifdef __TEST__
  printf ("\n\nAzioni tolte: %d\n", tot_act - GpG.num_actions);
#endif

#ifdef TEST_GR
  fprintf (stderr, "/ ");
#endif

  return;
}


/** 
 * Name: restart_MetricMinimizeCost
 * Scopo: E' richiamata in fase di ottimizzazione e sceglie un insieme di azioni da rimuovere.
 *        Scegliamo le azioni che incidono sul costo totale del piano 
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: restart_MetricMinimizeCost
* Objective: Called during optimization, she choose a set of action to remove
*            We choose the action that influence the total cost of the plan
* Type: void
* Input: none
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
void restart_MetricMinimizeCost ()
{
  int i, j, level = 0, pos = -1, num_removed =
    0, indlevel, pos_act, delete_action_level[MAX_PLAN_LENGTH], num_act;
  float sum, num;

#ifdef __TEST__
  int tot_act = GpG.num_actions;
#endif

  memset (delete_action_level, -1, MAX_PLAN_LENGTH * sizeof (int));

  do
    {
      /** 
	  Scegliamo casualmente un costo
	  **
	  We choose a random cost
      **/
      num_act = MY_RANDOM % ((int) ceil (GpG.best_cost));

      for (sum = 0.0, num = 0, level = 0;
	   level < GpG.curr_plan_length && sum <= num_act; level++)
	if (vectlevel[level]->num_actions)
	  {
	    pos_act = vectlevel[level]->action.position;
	    sum += get_action_cost (pos_act, level, NULL);
	    /** 
		Se il costo delle azioni incontrate finora supera il costo scelto casualmente
		**
		If the cost of the actions so far exceed the choosen cost
	    **/
	    if (sum >= num_act)
	      {
		pos = vectlevel[level]->action.position;
		/**
		   Controllo aggiuntivo
		   **
		   Additional check 
		**/
		if (vectlevel[level] == NULL || pos == -1
		    || vectlevel[level]->action.w_is_used == 0)
		  break;
		else
		  {
		    if (DEBUG6)
		      {
			printf
			  ("\n__________ RANDOM CHOICE %s level %d pos %d cost %.2f time %.2f",
			   print_op_name_string (pos, temp_name), level, pos,
			   get_action_cost (pos, level, NULL), get_action_time (pos,
								   level));
		      }
		    if (vectlevel[level]->action.position >= 0)
		      {
			delete_action_level[level] = level;

			num_removed++;
		      }
		  }
	      }
	  }
    }
  while (num_removed < GpG.num_actions / 5);

  /**
     Togliamo eventuali azioni identiche
     **
     We remove any possible identical action
  **/
  for (level = 0; level < GpG.curr_plan_length; level++)
    {
      if (delete_action_level[level] >= 0)
	continue;

      for (indlevel = level + 1; indlevel < GpG.curr_plan_length; indlevel++)
	{

	  if (CHECK_ACTION_OF_LEVEL (level)
	      && GET_ACTION_POSITION_OF_LEVEL (level) ==
	      GET_ACTION_POSITION_OF_LEVEL (indlevel))
	    {
	      delete_action_level[indlevel] = indlevel;
	      delete_action_level[level] = level;
	      break;
	    }

	}
    }


#ifdef __TEST__
  printf ("\nAzioni tolte:");
  for (i = 0; i < GpG.curr_plan_length; i++)
    {
      if (delete_action_level[i] < 0)
	continue;
      printf ("%s",
	      print_op_name_string (vectlevel[i]->action.position,
				    temp_name));
    }
#endif

  /**
     Rimuoviamo le azioni scelte, le azioni che hanno come precondizione gli effetti dell'azione scelta e le azioni che hanno come effetto le precondizioni dell'azione scelta 
     ** 
     We remove the selected actions, the actions that has preconditions like the effects of the selected action and effect like the preconditions of the selected action
  **/
  for (i = 0; i < GpG.curr_plan_length; i++)
    {
      if (delete_action_level[i] < 0)
	continue;

      pos_act = vectlevel[delete_action_level[i]]->action.position;
      if (pos_act < 0)
	continue;

      /**
	 Rimuoviamo le azioni che hanno come precondizione gli effetti additivi dell'azione scelta da rimuovere
	 ** 
	 We remove the actions that has preconditions like the additive effects of the selected action to remove
      **/
      for (j = 0; j < gef_conn[pos_act].num_A; j++)
	{

	  if (gef_conn[pos_act].A[j] < 0)
	    continue;

	  indlevel = delete_action_level[i] + 1;
	  while (indlevel < GpG.curr_plan_length)
	    {

	      if (CHECK_ACTION_OF_LEVEL (indlevel))
		{
		  if ((is_fact_in_preconditions
		       (vectlevel[indlevel]->action.position,
			gef_conn[pos_act].A[j])
		       ||
		       (is_fact_in_preconditions_overall
			(vectlevel[indlevel]->action.position,
			 gef_conn[pos_act].A[j])
			&&
			!is_fact_in_additive_effects_start (vectlevel
							    [indlevel]->
							    action.position,
							    gef_conn[pos_act].
							    A[j]))))
		    insert_remove_action (vectlevel[indlevel]->action.
					  position, indlevel,
					  C_T_REMOVE_ACTION,
					  GpG.approximation_level);

		}

	      if (!vectlevel[indlevel]->noop_act[gef_conn[pos_act].A[j]].
		  w_is_used)
		break;

	      indlevel++;
	    }
	}

      /**
	 Rimuoviamo le azioni che hanno come precondizione gli effetti additivi at start dell'azione scelta da rimuovere
	 **
	 We remove the actions that has preconditions like the additive at start effects of the action selected to remove
      **/
      if (gef_conn[pos_act].sf)
	for (j = 0; j < gef_conn[pos_act].sf->num_A_start; j++)
	  {
	    if (gef_conn[pos_act].sf->A_start[j] < 0)
	      continue;

	    indlevel = delete_action_level[i] + 1;
	    while (indlevel < GpG.curr_plan_length)
	      {

		if (CHECK_ACTION_OF_LEVEL (indlevel))
		  {
		    if ((is_fact_in_preconditions
			 (vectlevel[indlevel]->action.position,
			  gef_conn[pos_act].sf->A_start[j])
			 ||
			 (is_fact_in_preconditions_overall
			  (vectlevel[indlevel]->action.position,
			   gef_conn[pos_act].sf->A_start[j])
			  &&
			  !is_fact_in_additive_effects_start (vectlevel
							      [indlevel]->
							      action.position,
							      gef_conn
							      [pos_act].sf->
							      A_start[j]))))
		      insert_remove_action (vectlevel[indlevel]->action.
					    position, indlevel,
					    C_T_REMOVE_ACTION,
					    GpG.approximation_level);

		  }

		if (!vectlevel[indlevel]->
		    noop_act[gef_conn[pos_act].sf->A_start[j]].w_is_used)
		  break;
		indlevel++;
	      }
	  }


      /**
	 Rimuoviamo le azioni che hanno come effetti additivi le
	 precondizioni dell'azione scelta da rimuovere
	 **
	 We remove the actions that has additive effects like the
	 preconditions of the action selected to remove
      **/
      for (j = 0; j < gef_conn[pos_act].num_PC; j++)
	{

	  if (gef_conn[pos_act].PC[j] < 0)
	    continue;

	  indlevel = delete_action_level[i];
	  while (indlevel > 0)
	    {

	      if (CHECK_FACT_POS (gef_conn[pos_act].PC[j], indlevel) == FALSE)
		break;

	      if (CHECK_ACTION_OF_LEVEL (indlevel - 1)
		  &&
		  (is_fact_in_additive_effects
		   (vectlevel[indlevel - 1]->action.position,
		    gef_conn[pos_act].PC[j])
		   ||
		   is_fact_in_additive_effects_start (vectlevel
						      [indlevel -
						       1]->action.position,
						      gef_conn[pos_act].
						      PC[j])))
		insert_remove_action (vectlevel[indlevel - 1]->action.
				      position, indlevel - 1,
				      C_T_REMOVE_ACTION,
				      GpG.approximation_level);

	      if (CHECK_NOOP_POS (gef_conn[pos_act].PC[j], indlevel - 1) ==
		  FALSE)
		break;

	      if (!vectlevel[indlevel - 1]->noop_act[gef_conn[pos_act].PC[j]].
		  w_is_used)
		break;

	      indlevel--;
	    }
	}

      /**
	 Rimuoviamo le azioni che hanno come effetti additivi le precondizioni overall dell'azione scelta da rimuovere
	 **
	 We remove the actions that has additive effects like the overall preconditions of the action selected to remove
      **/
      if (gef_conn[pos_act].sf)
	for (j = 0; j < gef_conn[pos_act].sf->num_PC_overall; j++)
	  {

	    if (gef_conn[pos_act].sf->PC_overall[j] < 0)
	      continue;

	    indlevel = delete_action_level[i];

	    while (indlevel > 0)
	      {

		if (CHECK_FACT_POS
		    (gef_conn[pos_act].sf->PC_overall[j], indlevel) == FALSE)
		  break;

		if (CHECK_ACTION_OF_LEVEL (indlevel - 1)
		    &&
		    (is_fact_in_additive_effects
		     (vectlevel[indlevel - 1]->action.position,
		      gef_conn[pos_act].sf->PC_overall[j])
		     ||
		     is_fact_in_additive_effects_start (vectlevel
							[indlevel -
							 1]->action.position,
							gef_conn[pos_act].sf->
							PC_overall[j])))
		  insert_remove_action (vectlevel[indlevel - 1]->action.
					position, indlevel - 1,
					C_T_REMOVE_ACTION,
					GpG.approximation_level);

		if (CHECK_NOOP_POS
		    (gef_conn[pos_act].sf->PC_overall[j],
		     indlevel - 1) == FALSE)
		  break;

		if (!vectlevel[indlevel - 1]->
		    noop_act[gef_conn[pos_act].sf->PC_overall[j]].w_is_used)
		  break;

		indlevel--;
	      }
	  }

      if (vectlevel[delete_action_level[i]]->action.position > 0)
	/**
	   Rimuoviamo l'azione scelta
	   **
	   We remove the selected action
	**/
	insert_remove_action (pos_act, delete_action_level[i],
			      C_T_REMOVE_ACTION, GpG.approximation_level);
    }

#ifdef __TEST__
  printf ("\n\nAzioni tolte: %d", tot_act - GpG.num_actions);
#endif

#ifdef TEST_GR
  fprintf (stderr, "/ ");
#endif

  return;
}



/** 
 * Name: restart_MetricMaximizeCost
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: restart_MetricMaximizeCost
* Objective:
* Type: void
* Input: none
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
void restart_MetricMaximizeCost ()
{
  static action_set neighbors;

  int i, choice;
  static Bool initialized = FALSE;
  int num_ins = 0;
  int inserted[(MAX_NUM_ACTIONS >> 5) + 1];

  if (goptimization_exp == -1)
    return;

  /**
     vuoto l'array che mi indica quali sono le azioni inserite
     **
     I empty the array that point which are the inserted actions
  **/
  memset (inserted, 0, ((MAX_NUM_ACTIONS >> 5) + 1) * sizeof (int));
  if (!initialized)
    {
      initialized = TRUE;
      /**
	 determino il vicinato del fatto numerico
	 **
	 I determine the neighborhood of the numerical fact
      **/
      neighbors.num_A = 0;
      memset (neighbors.A, 0, MAX_NUM_ACTIONS * sizeof (int));
      create_neighborhood_for_compvar (goptimization_exp, 1, 0, &neighbors, 1, -1);
    }
  if (neighbors.num_A == 0)
    {
      printf ("\nWarning: there are no maximizing actions.\n\n");
      return;
    }


  if (neighbors.num_A < 10)
    {
      num_ins = neighbors.num_A;
    }
  else if ((neighbors.num_A >= 10) && (neighbors.num_A < 30))
    {
      num_ins = 10;
    }
  else if ((neighbors.num_A >= 30) && (neighbors.num_A < 90))
    {
      num_ins = neighbors.num_A / 3;
    }
  else if (neighbors.num_A >= 90)
    {
      num_ins = 30;
    }

  if (DEBUG1)
    printf("\n\n----- Start inizialization: Insert Action for maximize plan quality");

  for (i = 0; i < num_ins; i++)
    {
      choice = MY_RANDOM % neighbors.num_A;
      //      printf("\n%s", print_op_name_string(neighbors.A[choice],temp_name));
      insert_remove_action (neighbors.A[choice], GpG.curr_plan_length,
			    C_T_INSERT_ACTION, GpG.approximation_level);
    }

  if (DEBUG1)
    printf("\n\n----- End Inizialization -----");


}


/** OK 26-07-04
 * Name: restart_TimedFct2
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: restart_TimedFct2
* Objective:
* Type: void
* Input: none
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
void  restart_TimedFct2 ()
{

  int i, j, indlevel, pos_act, indDelete, delete_action_level[MAX_PLAN_LENGTH];


  /**
     Azzero la lista delle azioni da cancellare
     **
     I set to zero the list of the action to remove
  **/
  memset (delete_action_level, -1, MAX_PLAN_LENGTH * sizeof (int));

  indDelete = 0;
  
  for (i=0; i<GpG.num_false_tmd_fa; i++ )
    {
      delete_action_level[*unsup_tmd_facts[i]->level] = *unsup_tmd_facts[i]->level;
    }

  /**
     Rimuoviamo le azioni scelte, le azioni che hanno come precondizione gli effetti dell'azione scelta e le azioni che hanno come effetto le precondizioni dell'azione scelta 
     ** 
     We remove the selected actions, the actions that has preconditions like the effects of the selected action and effect like the preconditions of the selected action
  **/
  for (i = 0; i < GpG.curr_plan_length; i++)
    {
      if (delete_action_level[i] < 0)
	continue;

      pos_act = vectlevel[delete_action_level[i]]->action.position;
      if (pos_act < 0)
	continue;

      /**
	 Rimuoviamo le azioni che hanno come precondizione gli effetti additivi dell'azione scelta da rimuovere
	 ** 
	 We remove the actions that has preconditions like the additive effects of the selected action to remove
      **/
      for (j = 0; j < gef_conn[pos_act].num_A; j++)
	{

	  if (gef_conn[pos_act].A[j] < 0)
	    continue;

	  indlevel = delete_action_level[i] + 1;
	  while (indlevel < GpG.curr_plan_length)
	    {

	      if (CHECK_ACTION_OF_LEVEL (indlevel))
		{
		  if ((is_fact_in_preconditions
		       (vectlevel[indlevel]->action.position,
			gef_conn[pos_act].A[j])
		       ||
		       (is_fact_in_preconditions_overall
			(vectlevel[indlevel]->action.position,
			 gef_conn[pos_act].A[j])
			&&
			!is_fact_in_additive_effects_start (vectlevel
							    [indlevel]->
							    action.position,
							    gef_conn[pos_act].
							    A[j]))))
		    insert_remove_action (vectlevel[indlevel]->action.
					  position, indlevel,
					  C_T_REMOVE_ACTION,
					  GpG.approximation_level);

		}

	      if (!vectlevel[indlevel]->noop_act[gef_conn[pos_act].A[j]].
		  w_is_used)
		break;

	      indlevel++;
	    }
	}

      /**
	 Rimuoviamo le azioni che hanno come precondizione gli effetti additivi at start dell'azione scelta da rimuovere
	 **
	 We remove the actions that has preconditions like the additive at start effects of the action selected to remove
      **/
      if (gef_conn[pos_act].sf)
	for (j = 0; j < gef_conn[pos_act].sf->num_A_start; j++)
	  {
	    if (gef_conn[pos_act].sf->A_start[j] < 0)
	      continue;

	    indlevel = delete_action_level[i] + 1;
	    while (indlevel < GpG.curr_plan_length)
	      {

		if (CHECK_ACTION_OF_LEVEL (indlevel))
		  {
		    if ((is_fact_in_preconditions
			 (vectlevel[indlevel]->action.position,
			  gef_conn[pos_act].sf->A_start[j])
			 ||
			 (is_fact_in_preconditions_overall
			  (vectlevel[indlevel]->action.position,
			   gef_conn[pos_act].sf->A_start[j])
			  &&
			  !is_fact_in_additive_effects_start (vectlevel
							      [indlevel]->
							      action.position,
							      gef_conn
							      [pos_act].sf->
							      A_start[j]))))
		      insert_remove_action (vectlevel[indlevel]->action.
					    position, indlevel,
					    C_T_REMOVE_ACTION,
					    GpG.approximation_level);

		  }

		if (!vectlevel[indlevel]->
		    noop_act[gef_conn[pos_act].sf->A_start[j]].w_is_used)
		  break;
		indlevel++;
	      }
	  }

      /**
	 Rimuoviamo le azioni che hanno come effetti additivi le precondizioni dell'azione scelta da rimuovere
	 **
	 We remove the actions that has additive effects like the preconditions of the action selected to remove
      **/
      for (j = 0; j < gef_conn[pos_act].num_PC; j++)
	{

	  if (gef_conn[pos_act].PC[j] < 0)
	    continue;

	  indlevel = delete_action_level[i];
	  while (indlevel > 0)
	    {

	      if (CHECK_FACT_POS (gef_conn[pos_act].PC[j], indlevel) == FALSE)
		break;

	      if (CHECK_ACTION_OF_LEVEL (indlevel - 1)
		  &&
		  (is_fact_in_additive_effects
		   (vectlevel[indlevel - 1]->action.position,
		    gef_conn[pos_act].PC[j])
		   ||
		   is_fact_in_additive_effects_start (vectlevel
						      [indlevel -
						       1]->action.position,
						      gef_conn[pos_act].
						      PC[j])))
		insert_remove_action (vectlevel[indlevel - 1]->action.
				      position, indlevel - 1,
				      C_T_REMOVE_ACTION,
				      GpG.approximation_level);

	      if (CHECK_NOOP_POS (gef_conn[pos_act].PC[j], indlevel - 1) ==
		  FALSE)
		break;

	      if (!vectlevel[indlevel - 1]->noop_act[gef_conn[pos_act].PC[j]].
		  w_is_used)
		break;

	      indlevel--;
	    }
	}

      /**
	 Rimuoviamo le azioni che hanno come effetti additivi le precondizioni overall dell'azione scelta da rimuovere
	 **
	 We remove the actions that has additive effects like the overall preconditions of the action selected to remove
      **/
      if (gef_conn[pos_act].sf)
	for (j = 0; j < gef_conn[pos_act].sf->num_PC_overall; j++)
	  {

	    if (gef_conn[pos_act].sf->PC_overall[j] < 0)
	      continue;

	    indlevel = delete_action_level[i];

	    while (indlevel > 0)
	      {

		if (CHECK_FACT_POS
		    (gef_conn[pos_act].sf->PC_overall[j], indlevel) == FALSE)
		  break;

		if (CHECK_ACTION_OF_LEVEL (indlevel - 1)
		    &&
		    (is_fact_in_additive_effects
		     (vectlevel[indlevel - 1]->action.position,
		      gef_conn[pos_act].sf->PC_overall[j])
		     ||
		     is_fact_in_additive_effects_start (vectlevel
							[indlevel -
							 1]->action.position,
							gef_conn[pos_act].sf->
							PC_overall[j])))
		  insert_remove_action (vectlevel[indlevel - 1]->action.
					position, indlevel - 1,
					C_T_REMOVE_ACTION,
					GpG.approximation_level);

		if (CHECK_NOOP_POS
		    (gef_conn[pos_act].sf->PC_overall[j],
		     indlevel - 1) == FALSE)
		  break;

		if (!vectlevel[indlevel - 1]->
		    noop_act[gef_conn[pos_act].sf->PC_overall[j]].w_is_used)
		  break;

		indlevel--;
	      }
	  }

      if (vectlevel[delete_action_level[i]]->action.position > 0)
	/**
	   Rimuoviamo l'azione scelta
	   **
	   We remove the selected action
	**/
	insert_remove_action (pos_act, delete_action_level[i],
			      C_T_REMOVE_ACTION, GpG.approximation_level);
    }

#ifdef __TEST__
  printf ("\n\nAzioni tolte: %d", tot_act - GpG.num_actions);
#endif

#ifdef TEST_GR
  fprintf (stderr, "/ ");
#endif

  return;
}



/** OK 26-07-04
 * Name: restart_search
 * Scopo: Toglie casualmente dal Planning Graph delle azioni
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: restart_search
* Objective: Remove randomly some action to the Planning Graph
* Type: void
* Input: none
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
void restart_search ()
{
  if (DEBUG2)
    printf
      ("\n\n^^^^RESTART_SEARCH: Remove/Add some actions to make inconsitence");

  GpG.restart_search = TRUE;

  if (DEBUG3)
    print_actions_in_subgraph ();


  if(GpG.neighb_with_timed_fa == 0  && GpG.num_false_tmd_fa > 0)
    {
      restart_TimedFct (); 
      //      return;
    }

  if (GpG.maximize_plan)
    restart_MetricMaximizeCost();
  else{ 
    if (GpG.weight_cost <= GpG.weight_time)
      restart_MetricTemporalCost ();
    else
      restart_MetricMinimizeCost ();
  }
  
  if (DEBUG3)
    print_actions_in_subgraph ();

  if (DEBUG2)
    printf ("\n^^^^END RESTART_SEARCH\n");

  GpG.restart_search = FALSE;

}
