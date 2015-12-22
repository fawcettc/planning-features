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



// CVS CVS CVS CVS

 
/********************************************************************
 * File: LocalSearch.c
 * Description: Local search method
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/




#include <values.h>
#include <math.h>
#include "lpg.h"
#include "LpgTime.h"
#include "check.h"
#include "numeric.h"
#include "LocalSearch.h"
#include "ActionSubgraph.h"
#include "H_relaxed.h"
#include "H_max.h"
#include "utilities.h"
#include "inst_utils.h"
#include "LpgOutput.h"
#include "output.h"
#include "derivedpred.h"


//#define __TEST_MIXED__


/*********************************************
             EVALUATION FUNCTION
**********************************************/

/** OK 27-07-04
 * Name: fast_action_cost
 * Scopo: determina il costo relativo all'inserimento o rimozione di una azione
 * Tipo: float
 * Input: neighd_list neighb_act (struttura contenente informazioni relative ad una azione)
 * Output: Il costo totale dell'azione passata in ingresso
 * Strutture dati principali: GpG
 *                            EfConn
 *                            vectlevel
 *                            gef_conn
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: action_cost
 *              choose action
**
*  Name: fast_action_cost
*  Objective: it determines the relative cost to the insertion or removal of one action
*  Type: float
*  Input: neighd_list neighb_act (containing structure relative information to one action)
*  Output: The cost total of the last action in income
*  Main Data Structures: GpG
*                        EfConn
*                        vectlevel
*                        gef_conn
*  Main Functions Used: none
*  Call gives: action_cost
*              choose action
**/
float fast_action_cost (neighb_list neighb_act)
{
  /** 
    Variabili di appoggio 
    **
    Variables of support
  **/
  register int temp = 0, temp1, i, k;
  int *ptr, level, j, diff, cel;
  register EfConn *act;
  auto float total, prec_par, excl_par, add_effect_par;
  auto float precond, mutex, effect, act_cost;	//  LM 
  /** 
      Azzero alcune variabili 
      **
      I annul some variables
  **/
  precond = mutex = effect = act_cost = 0.0;	//  LM
  level = neighb_act->act_level;
  neighb_act->cost.act_cost=0.0;	
  neighb_act->cost.act_time=0.0;
  total = 0.0;

  /** 
     Assegno a EfConn *act le caratteristiche dell'azione passata in ingresso 
     **
     I assign to EfConn *act the characteristics of the last action in input
  **/
  act = CONVERT_ACTION_TO_VERTEX (neighb_act->act_pos);
  
  /**  
    Determina i parametri alpha, beta, gamma per la rimozione dell'azione 
    **
    It determines the parameters alpha, beta, gamma for the removal of the action
  **/
  if (neighb_act->constraint_type == C_T_REMOVE_ACTION)
    {				/* ... became false */
      prec_par = GpG.used_prec_par;
      excl_par = GpG.used_excl_par;
      add_effect_par = GpG.used_add_effect_par;
    }

  /** 
    Determina i parametri alpha, beta, gamma per l'inserimento dell'azione 
    **
    It determines the parameters alpha, beta, gamma for the insertion of the action
  **/
  else
    {				/* ... became true */
      prec_par = GpG.prec_par;
      excl_par = GpG.excl_par;
      add_effect_par = GpG.add_effect_par;
    }
  if (DEBUG4)
    printf ("\n\n Evalutate action");
  if (DEBUG3)
    printf ("\nFAST_COST  Act: %s, level %d\n",
	    print_op_name_string (neighb_act->act_pos, temp_name), level);

  /** 
    Determina il numero di precondizioni non supportate 
    **
    It determines the number of preconditions not supported
  **/
  if (prec_par)
    {
      for (i = 0, temp = 0; i < act->num_precond; i++)
	temp +=
	  count_bit1 (act->bit_precond[i].uid_mask & (~vectlevel[level]->fact_vect[act->bit_precond[i].uid_block]));

      /**
	 Analisi precondizioni OVERALL e AT-END
	 **
	 Analysis of OVERALL and AT-END precondition
      **/
      if( gef_conn[neighb_act->act_pos].sf)
	{
	for (i = 0; i < gef_conn[neighb_act->act_pos].sf->num_PC_overall; i++)
	  {
	    cel=gef_conn[neighb_act->act_pos].sf->PC_overall[i];
	    if(vectlevel[level]->fact[cel].w_is_true<=0)
	      if (!is_fact_in_additive_effects_start(neighb_act->act_pos,cel))
		temp++;
	  }

	for (i = 0; i < gef_conn[neighb_act->act_pos].sf->num_PC_end ; i++)
	  {
	    cel=gef_conn[neighb_act->act_pos].sf->PC_end[i];
	    if(vectlevel[level]->fact[cel].w_is_true<=0)
	      if (!is_fact_in_additive_effects_start(neighb_act->act_pos,cel))
	      temp++;
	  }
	}
      
      total = prec_par * temp;
      precond = act->lamda_prec * total;	//  LM
      if (DEBUG3)
	printf ("  Num. P: %d", temp);
    }

  /** 
    Determina il numero di azioni ME con l'azione passata in ingresso 
    **
    It determines the number of actions ME with the last action in input
  **/
  for (i = 0; i < gnum_ft_block; i++)
    temp +=
      count_bit1 (act->ft_exclusive_vect[i] & vectlevel[level]->
		  noop_act_vect[i] & vectlevel[level]->noop_prec_act_vect[i]);
  mutex = excl_par * temp;	//  LM
  total += mutex;
  mutex *= act->lamda_me;	//  LM
  if (DEBUG3)
    printf ("  ME: %d", temp);

  /** 
    define the cost of Add_effect critics nodes 
    a fact is a true critic node if it is precondition of almost an action 
    of the next level and it's supported from only one action 
  **/
  /** 
    a fact is a false critic node if it is precondition of almost an action
    of the next level and it's not supported
    Determina il costo degli effetti additivi analizzando i vettori corrispondenti ai 
    fatti critici falsi e veri 
  **/
  if (add_effect_par)
    {
      level++;
      if (neighb_act->constraint_type == C_T_REMOVE_ACTION)
	ptr = vectlevel[level]->true_crit_vect;	/** 
						    Numero di fatti critici che possono diventare falsi						 
						    **
						    Number of critic facts that should became false 
						**/
      else
	ptr = vectlevel[level]->false_crit_vect;/** 
						    Numero di fatti critici che possono diventare veri;
						    Aspetto positivo
						    **
						    Number of critic facts that should became true;
						    positive aspect 
						**/
      if (neighb_act->constraint_type == C_T_REMOVE_ACTION
	  && !GpG.accurate_cost)
	{
	  for (i = 0, temp = 0; i < act->num_add_effect; i++)
	  {
	    k = 32;
	    j = act->bit_add_effect[i].uid_block * 32;
	    temp1 =
	      act->bit_add_effect[i].uid_mask & *(ptr + act->bit_add_effect[i].uid_block);

	    /* counts the no. of  eliminated fact's precondition actions */
	    while (temp1)
	      {
		k--;
		if ((temp1 & FIRST_1))
		  {
#ifdef __TEST__
		    if (CHECK_FACT_POS (j + k, level) == FALSE) {
		      
#ifdef __MY_OUTPUT__
		      MSG_ERROR( WAR_BUG );
#else
		      printf( WAR_BUG );
#endif
		      exit (0);
		    }
#endif		    
		    temp += vectlevel[level]->fact[j + k].w_is_goal;
		    effect += CONVERT_FACT_TO_VERTEX (j + k)->lamda_prec;	//  LM
		  }
		temp1 <<= 1;
	      }
	  }
	  /**
	     Analisi effetti additivi AT START
	     **
	     Analysis of additive AT-START effects
	  **/
	  if(gef_conn[neighb_act->act_pos].sf)
	    {
	      for (i = 0; i < gef_conn[neighb_act->act_pos].sf->num_A_start; i++)
		{
		  cel=gef_conn[neighb_act->act_pos].sf->A_start[i];
		  if(vectlevel[level]->fact[cel].w_is_goal>0 && vectlevel[level]->fact[cel].w_is_true==1)
		    temp+=vectlevel[level]->fact[cel].w_is_goal;
		}
	    }
	}
      else
	{
	  for (i = 0, temp = 0; i < act->num_add_effect; i++)
	    temp +=
	      count_bit1 (act->bit_add_effect[i].uid_mask & *(ptr + act->bit_add_effect[i].uid_block));
	  /**
	     Analisi effetti additivi AT START
	     **
	     Analysis of additive AT-START effects
	  **/
	  if(gef_conn[neighb_act->act_pos].sf)
	    {
	      for (i = 0; i < gef_conn[neighb_act->act_pos].sf->num_A_start; i++)
		{
		  cel=gef_conn[neighb_act->act_pos].sf->A_start[i];
		  if(vectlevel[level]->fact[cel].w_is_goal>0 && vectlevel[level]->fact[cel].w_is_true==1)
		    temp++;
		}
	    }
	  effect = temp;	//  LM 
	}
      total += add_effect_par * temp;
      effect *= add_effect_par;	//  LM
      if (DEBUG3)
	printf ("  Add-E: %d", temp);
    }

  // LM Sostituisco il costo ottentuto con i moltiplicatori di lagr a quello
  // standard se e' impostata la corrispondente modalita'

  if (GpG.Twalkplan && GpG.tabu_length >0 && neighb_act->constraint_type == C_T_REMOVE_ACTION)
    {				
      /* T_walkgraph: increase the cost function of act if it is in
	 the tabu list 
      */

      diff = GpG.count_num_try - CONVERT_ACTION_TO_VERTEX (neighb_act->act_pos)->step;

      if (diff < GpG.tabu_length  && (act->step + num_try == GpG.count_num_try))
	total += GpG.delta * (GpG.tabu_length - diff);
    }
  /** 
      Associo al campo cost.weight il costo totale dell'azione 
      **
      I associate to the field cost.weight the total cost of the action
  **/
  neighb_act->cost.weight = total;

#ifdef __TEST__
  if (DEBUG4)
    printf ("\n $$$ END FAST COST inc %.2f cost %.2f time %.2f ",
	    neighb_act->cost.weight, neighb_act->cost.act_cost,
	    neighb_act->cost.act_time);

#endif
  if (DEBUG3)
    printf ("\n -> tot %f", total);
  /** 
      Restituisce il costo totale dell'azione 
      **
      It gives back the total cost of the action
  **/
  return (total);
}


/** OK 27-07-04
 * Name: action_cost
 * Scopo: in base al tipo di piano determino il costo relativo all'inserimento o 
 *        rimozione di una azione
 * Tipo: float
 * Input: neighb_list Action (struttura contenente informazioni relative ad una azione)
 * Output: il costo dato dal'inserimento o rimozione di una azione
 *         0 in caso di errore
 * Strutture dati principali: GpG
 * Funzioni principali utilizzate: dg_action_cost
 *                                 max_action_cost
 *                                 fast_action_cost
 * Chiamata da: find_min
**
*  Name: action_cost
*  Objective: based on the type of plan I determine the relative cost to the insertion or
*             removal of one action
*  Type: float
*  Input: neighb_list Action (containing structure relative information to one action)
*  Output: the given cost dal' insertion or removal of one action
*          0 in error case
*  Main Data Structures: GpG
*  Main Functions Used: dg_action_cost
*                       max_action_cost
*                       fast_action_cost
*  Call gives: find_min
**/
float action_cost (neighb_list Action)
{
  /** 
      copio i valori del livello di action
      **
      I copy the values of the level of action
  **/
  memcpy (Hvar.common_max_values, vectlevel[Action->act_level]->numeric->values,
	  gnum_comp_var * sizeof (float));

  memcpy (Hvar.common_min_values, vectlevel[Action->act_level]->numeric->values,
	  gnum_comp_var * sizeof (float));

  reset_bitarray( Hvar.common_level_supported_numeric_preconditions,gnum_block_compvar);

  /** 
    In base al tipo di piano determino come calcolare il costo relativo all'inserimento o 
    rimozione di una azione 
    **
    Depending to the type of the plan I determine the mode to calculating the cost relative to the insertion or
    removal of one action
  **/
  if (GpG.accurate_cost == COMPUTE_MAX_COST)
    return max_action_cost (Action);
  
  else
    if (GpG.accurate_cost >= COMPUTE_DG_SUM_COST)
      {
	dg_action_cost (Action);
      }
      else
	return fast_action_cost (Action);
  return 0;
}


/** OK 27-07-04
 * Name: action_eff_cost
 * Scopo: determina il numero di effetti additivi critici
 * Tipo: int
 * Input: register inform_list infAction (inform dell'azione passata in ingresso)
 * Output: il numero di effetti additivi critici
 * Strutture dati principali: GpG
 *                            EfConn
 *                            inf_list
 *                            vectlevel
 *                            gef_conn
 * Funzioni principali utilizzate: is_fact_in_delete_effects
 * Chiamata da: remove_backward_noop_chain
 *              choose_action
**
*  Name: action_eff_cost
*  Objective: it determines the number of effects points out to you criti to us
*  Type: int
*  Input: register inform_list infAction (inform of the last action in income)
*  Output: the number of effects points out to you criti to us
*  Main Data Structure: GpG
*                       EfConn
*                       inf_list
*                       vectlevel
*                       gef_conn
*  Main Function Used: is_fact_in_delete_effects
*  Call gives: remove_backward_noop_chain
*              choose_action
**/
int action_eff_cost (register ActNode_list infAction)
{
  /** 
    Variabili di appoggio
    **
    Variable of support
  **/
  /** 
    register int temp e' il contatore a cui assegneremo il numero di fatti critici 
    **
    register int temp is the counter to which we will assign to the number of critical facts
  **/
  register int i, temp;
  int *ptr, level, cel;
  /** 
    Struttura di appoggio per contenere informazioni relative ad una azione 
    **
    Structure of support to contain information relative to one action
  **/
  EfConn *act;
  /** 
    Dalla struttura inf_action passata in ingresso ricavo il livello
    **
    From the structure inf_action in input revenue the level
  **/
  level = *infAction->level + 1;
  /**
    Associo ad act le caratteristiche dell'azione 
    **
    I associate to act the characteristics of the action
  **/
  act = &gef_conn[infAction->position];
  /** 
    Se l'azione e' inserita nell'action subgraph associo a ptr il numero di fatti 
    critici che possono diventare false 
    **
    If the action is inserted in the action subgraph I associate to ptr the number of facts
    critical that can become false
  **/
  if (infAction->w_is_used)
    ptr = vectlevel[level]->true_crit_vect;  /** 
						Numero di fatti critici che possono diventare falsi
						**
					        Number of critics fact that should became false 
					     **/
  /** 
    Altrimenti restituisce un messaggio d'errore 
    **
    Otherwise it gives back an error message
  **/
  else {
    
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else
    printf( WAR_BUG );
#endif
    exit (0);
  }
  /** 
    Analizza gli effetti additivi e aumenta temp di una quantita' corrispondente a quelli critici 
    **
    It analyzes the additive effects and it increases temp depending of the correspondent to those critics
  **/
  for (i = 0, temp = 0; i < act->num_add_effect; i++)
    temp +=
      count_bit1 (act->bit_add_effect[i].
		  uid_mask & *(ptr + act->bit_add_effect[i].uid_block));

  /** 
    Analizza gli effetti additivi di azioni durative 
    **
    It analyzes the additive effects of durative actions
  **/
  if (gef_conn[infAction->position].sf != NULL)
    for (i = 0; i < gef_conn[infAction->position].sf->num_A_start; i++)
      {
	cel = gef_conn[infAction->position].sf->A_start[i];
	if (cel < 0)
	  continue;
	if (is_fact_in_delete_effects (infAction->position, cel))
	  continue;
	if (vectlevel[level]->fact[cel].w_is_goal)
	  temp++;
      }
  /** 
    Ritorna il numero di fatti critici 
    **
    Returns the number of critical facts
  **/
  return (temp);
}



/*********************************************
            NEIGHBORHOOD EVALUATION
**********************************************/

/** OK 27-07-04
 * Name: insert_els_in_neighborhood
 * Scopo:
 * Tipo: void
 * Input: IntList * ilist
 *        action_set * neighbors
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: insert_els_in_neighborhood
*  Objective:
*  Type: void
*  Input: IntList * ilist
*         action_set * neighbors
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void insert_els_in_neighborhood (IntList * ilist, action_set * neighbors)
{
  IntList *el;
  for (el = ilist; el; el = el->next)
    {
      if (neighbors == NULL)
	printf ("%d%s", el->item, el->next ? ", " : " ");
      else
	{
	  if (gef_conn[el->item].level < 0)
	    {
	      if (DEBUG2)
		printf("\nWarning: trying to insert a non reachable action in neighbothood!");
	     
	      continue;
	    }
	  neighbors->A[(neighbors->num_A)++] = el->item;
	  if (neighbors->num_A >= MAX_NUM_ACTIONS)
	    {
	      printf ("\nWARNING: reached MAX_NUM_ACTIONS\n");
	      neighbors->num_A = MAX_NUM_ACTIONS - 1;
	      break;
	    }
	}
    }
}


/** OK 27-07-04
 * Name: find_min
 * Scopo: ordinare il vettore del vicinato in ordine crescente di costo
 * Tipo: float
 * Input: constraints_list inf_tofix (tipo di vincolo)
 *        int *pos_temp_vect (vettore gli elementi del vicinato)
 *        int num (numero di elementi facenti parte del vicinato)
 *	  int *num_min (numero delle azioni del vicinato aventi costo minimo)
 *        int *num_neg (numero di azioni del vicinato con costo negativo)
 * Output: Restituisce il minor costo associato ad una azione appartenente al vicinato
 * Strutture dati principali: GpG
 *                            EfConn
 *                            vectlevel
 *                            gef_conn
 * Funzioni principali utilizzate: action_cost
 * Chiamata da: fix_unsup_num_fact
 *              fix_unsup_fact
**
*  Name: find_min
*  Objective: to order the carrier of environs in increasing order of cost
*  Type: float
*  Input: constraints_list inf_tofix (type of tie)
*         int * pos_temp_vect (carrier the elements of environs)
*         int num (number of making elements part of environs)
*         int * num_min (number of the having actions of environs the minimal cost)
*         int * num_neg (number of actions of environs with cost negative)
*  Output: It gives back minor to the cost associated to one action pertaining to environs
*  Main Data Structures: GpG
*                        EfConn
*                        vectlevel
*                        gef_conn
*  Main Functions Used: action_cost
*  Call gives: fix_unsup_num_fact
*              fix_unsup_fact
**/
float find_min (constraints_list inf_tofix, int *pos_temp_vect, int num,
	  int *num_min, int *num_neg)
{
  register int i, j;
  int pos = 1, neg = 1, stop, stop1;
  float cost = 0.0, minor_cost = MAXFLOAT;
  float max_act_incons, max_act_cost, max_act_time, max_timed_fa, weight, weight_c, weight_t, weight_tf, diff;
  node_cost n_cost;

  max_act_incons = 0.0;
  max_act_cost = 0.0;
  max_act_time = 0.0;
  max_timed_fa = 0.0;

  weight = weight_c = weight_t = weight_tf = 0.0;
  
  /** 
    Pongo alcuni campi di local_search uguali a MAXFLOAT, mi servono  per limitare la 
    profondita' di ricerca 
    **
    I set some fields of local_search equal to MAXFLOAT, they need me to limit the
    depth of search
  **/
  local_search.best_cost = MAXFLOAT;
  local_search.num_actions = 0;

  /**
    Utilizzate per limitare la "profondita' di ricerca" nell esame degli elem del vicinato
    **
    Used to limit the "search depth" examining the elem of the environs
  **/
  local_search.max_act_incons = MAXFLOAT;
  local_search.max_act_cost = MAXFLOAT;
  local_search.max_act_time = MAXFLOAT;
  local_search.max_timed_fa = MAXFLOAT;

#ifdef __TEST__
  check_plan (GpG.curr_plan_length);

#endif
  local_search.best_cost = MAXFLOAT;
  /** 
    Analizzo il numero di elementi del vicinato  
    **
    I analyze the number of elements of environs
  **/
  for (i = num - 1; i >= 0; i--)
    {

      // Search for the action with lower cost
      // minor_cost is the lower action cost
      // pos contains the number of action with minor_cost
      // neg contains the number of action with negative cost
      // pos_temp_vect contains the indices of the actions with lower cost

      /** 
	Aggiorno il costo relativo all'azione trattata 
	**
	I update the relative cost to the threated action
      **/
      (*(neighb_vect + i))->cost.timed_fa = (*(neighb_vect + i))->cost.weight =
	(*(neighb_vect + i))->cost.act_cost = (*(neighb_vect + i))->cost.act_time = 0.0;
      
      action_cost (*(neighb_vect + i));

      /** 
	Se il costo di ricerca e' minore di quello massimo (max_act_incons) aggiorno questo con quello 
	dell'azione 
	**
	If the cost of search is smaller than the maximum (max_act_incons) I update this with that one
	of the action
      **/
      if (max_act_incons < (*(neighb_vect + i))->cost.weight && (*(neighb_vect + i))->cost.weight < MAX_COST)
	max_act_incons = (*(neighb_vect + i))->cost.weight;
      /** 
	Se il costo dell'inserimento o rimozione  e' minore di quello massimo (max_act_cost) aggiorno 
	questo con quello dell'azione 
	**
	If the cost of the insertion or removal is smaller than the maximum (max_act_cost) I update
	this with that one of the action
      **/
      if (max_act_cost < (*(neighb_vect + i))->cost.act_cost && (*(neighb_vect + i))->cost.act_cost < MAX_COST )
	max_act_cost = (*(neighb_vect + i))->cost.act_cost;
      /** 
	Se il costo temporale e' minore di quello massimo (max_act_time) aggiorno questo con quello 
	dell'azione 
	**
	If the temporal cost is smaller than the maximum (max_act_time) I update this with that one
	of the action
      **/
      if (max_act_time < (*(neighb_vect + i))->cost.act_time && (*(neighb_vect + i))->cost.act_time< MAX_COST)
	max_act_time = (*(neighb_vect + i))->cost.act_time;
      /** 
	Se e' la prima azione trattata aggiorno semplicemente i campi di local_search 
	**
	If is the first action threated  I simply update the fields of local_search
      **/
      if(max_timed_fa < (*(neighb_vect + i))->cost.timed_fa)
	max_timed_fa = (*(neighb_vect + i))->cost.timed_fa;

      if (i == (num - 1))
	{
	  local_search.max_act_incons = (*(neighb_vect + i))->cost.weight;
	  local_search.max_act_cost = (*(neighb_vect + i))->cost.act_cost;
	  local_search.max_act_time = (*(neighb_vect + i))->cost.act_time;
	  local_search.max_timed_fa = (*(neighb_vect + i))->cost.timed_fa;


	  if (DEBUG6)
	    printf
	      ("\n local_search.max_act_incons %.2f  local_search.max_act_cost %.2f  local_search.max_act_time %.2f ",
	       local_search.max_act_incons, local_search.max_act_cost,
	       local_search.max_act_time);
	}
      else
      if(GpG.weight_cost <= 0 && GpG.weight_time <= 0 && GpG.timed_facts_present==FALSE)
	{
	  /** 
	    Controlli sul costo di ricerca, sul costo di inserimento e sul costo temporale	  
	    **
	    Controls on the cost of search, on the cost of insertion and on the temporal cost
	  **/
	  if ((*(neighb_vect + i))->cost.weight < local_search.max_act_incons)
	    local_search.max_act_incons=(*(neighb_vect + i))->cost.weight ;
	}
      else
	{
	  stop1 = stop = 4;
	  if ((*(neighb_vect + i))->cost.weight <= local_search.max_act_incons)
	    stop--;
	  if ((*(neighb_vect + i))->cost.weight >= local_search.max_act_incons)
	    stop1--;
	  if (GpG.weight_cost <= 0 || (*(neighb_vect + i))->cost.act_cost <= local_search.max_act_cost)
	    stop--;
	  if (GpG.weight_cost <= 0 || (*(neighb_vect + i))->cost.act_cost >= local_search.max_act_cost)
	    stop1--;
	  if (GpG.weight_time <= 0 || (*(neighb_vect + i))->cost.act_time <= local_search.max_act_time)
	    stop--;
	  if (GpG.weight_time <= 0 || (*(neighb_vect + i))->cost.act_time >= local_search.max_act_time)
	    stop1--;
	  if (GpG.weight_timed_fa <= 0 || (*(neighb_vect + i))->cost.timed_fa <= local_search.max_timed_fa)
	    stop--;
	  if (GpG.weight_timed_fa <= 0 || (*(neighb_vect + i))->cost.timed_fa > local_search.max_timed_fa)
	    stop1--;

	  if (DEBUG6)
	    printf ("\n (*(neighb_vect+i))->cost.weight %.2f   (*(neighb_vect+i))->cost.act_cost %.2f   (*(neighb_vect+i))->cost.act_time %.2f ",
		    (*(neighb_vect + i))->cost.weight, (*(neighb_vect + i))->cost.act_cost, (*(neighb_vect + i))->cost.act_time);
	  /** 
	    Se il costo di ricerca e' minore di quello massimo e se il costo di inserimento e' 
	    minore di quello massimo e se il costo temporale e' minore di quello massimo: Aggiorno i 
	    campi di local_search 
	    **
	    If the cost of search is smaller than the maximum and if the insertion cost is
	    smaller of that maximum and if the temporal cost is smaller than the maximum: I update the
	    fields of local_search
	  **/
	  if (stop <= 0)
	    {
	      local_search.max_act_incons = (*(neighb_vect + i))->cost.weight;
	      local_search.max_act_cost = (*(neighb_vect + i))->cost.act_cost;
	      local_search.max_act_time = (*(neighb_vect + i))->cost.act_time;
	      local_search.max_timed_fa = (*(neighb_vect + i))->cost.timed_fa;

	      if (DEBUG6)
		printf("\n local_search.max_act_incons %.2f   local_search.max_act_cost %.2f   local_search.max_act_time %.2f ",
		       local_search.max_act_incons, local_search.max_act_cost, local_search.max_act_time);
	    }

	  /** 
	    In caso contrario analizzo le singole situazioni 
	    **
	    In contrary case I analyze the single situations
	  **/
	  else if ( stop1 > 0 && (*(neighb_vect + i))->cost.weight < MAX_COST )
	    {
	      if (local_search.max_act_incons < (*(neighb_vect + i))->cost.weight && (*(neighb_vect + i))->cost.weight < MAX_COST )
		local_search.max_act_incons = (*(neighb_vect + i))->cost.weight;
	      if (local_search.max_act_cost < (*(neighb_vect + i))->cost.act_cost && (*(neighb_vect + i))->cost.act_cost < MAX_COST  )
		local_search.max_act_cost = (*(neighb_vect + i))->cost.act_cost;
	      if (local_search.max_act_time < (*(neighb_vect + i))->cost.act_time && (*(neighb_vect + i))->cost.act_time < MAX_COST )
		local_search.max_act_time = (*(neighb_vect + i))->cost.act_time;	      if (local_search.max_timed_fa < (*(neighb_vect + i))->cost.timed_fa &&  (*(neighb_vect + i))->cost.timed_fa < MAX_COST )
		local_search.max_timed_fa = (*(neighb_vect + i))->cost.timed_fa;
	      if (DEBUG6)
		printf ("\n local_search.max_act_incons %.2f   local_search.max_act_cost %.2f   local_search.max_act_time %.2f ",
		   local_search.max_act_incons, local_search.max_act_cost, local_search.max_act_time);
	    }
	}
    }

#ifdef __TEST__
  if (DEBUG2)
    printf ("\n\n max_act_incons %.2f max_act_cost %.2f max_act_time %.2f", max_act_incons, max_act_cost, max_act_time);

#endif

  if(GpG.evaluation_function==1 || GpG.evaluation_function==2 )
    {

      if (max_act_cost && GpG.weight_cost)
	weight_c = GpG.weight_cost * max_act_cost;
      if (max_act_time && GpG.weight_time)
	weight_t = GpG.weight_time * max_act_time;
     if (max_timed_fa && GpG.weight_timed_fa)
	weight_tf = GpG.weight_timed_fa * max_timed_fa;
  
      weight = weight_c+ weight_t;
 // Peso il coefficiente considerando il numero corrente di inconsistenze

      if(GpG.num_false_tot>0 && GpG.evaluation_function==1)
	{
	  weight *=GpG.num_false_tot;
	}

      if (weight<=0.0)
	weight=1.0;;/**
		       Per evitare probl con la div per 0
		       **
		       To avoid problems with div by 0
		    **/
    }
  else
    {
      if (max_act_cost && GpG.weight_cost)
	weight_c = GpG.weight_cost / max_act_cost;
      if (max_act_time && GpG.weight_time)
        weight_t = GpG.weight_time / max_act_time;
      if (max_timed_fa && GpG.weight_timed_fa)
        weight_tf = GpG.weight_timed_fa / max_timed_fa;

      if(GpG.num_false_tot>0)
	{
	  weight_c /= GpG.num_false_tot;
	  weight_t /=GpG.num_false_tot;
	  weight_tf /=GpG.num_false_tot;
	}
      weight = weight_c+ weight_t;
  }

  if (DEBUG6)
    {
      printf ("\n \n#########################################################");
      printf ("\n ======= WEIGHT %.2f  wc %.2f wt %.2f max_inc %.2f max_cost %.2f max time %.2f",
	      weight, GpG.weight_cost, GpG.weight_time, max_act_incons, max_act_cost, max_act_time);
    }
  if (DEBUG3)
    printf ("\n\n>< EVALUTATION RESULTS ><\n");

  for (i = 0; i < num; i++)
    {
      if((*(neighb_vect + i))->cost.weight>=MAX_COST)
	cost=MAX_COST;
      else
	{
	  if(GpG.evaluation_function==0)
	    {
	      //  cost = max_act_incons * ((*(neighb_vect + i))->cost.act_cost * weight_c + (*(neighb_vect + i))->cost.act_time * weight_t) + (*(neighb_vect + i))->cost.weight;
	      cost = max_act_incons * ((*(neighb_vect + i))->cost.act_cost * weight_c + (*(neighb_vect + i))->cost.act_time * weight_t ) + (*(neighb_vect + i))->cost.weight + (*(neighb_vect + i))->cost.timed_fa * weight_tf;
	    }
	  else
	    {
	     /**
		Moltiplico la componente dei costi per max_act_incons invece che dividere la componente del costo di ricerca 
		poiche' la moltiplic e' + veloce ed evito probl di divisione per 0
		**
		I multiply the cost component per max_act_incoms instead to divide the research cost component because the multiplication is more faster
		and I avoid problem with the division by 0
	     **/
	      cost = max_act_incons*(((*(neighb_vect + i))->cost.act_cost* GpG.weight_cost + (*(neighb_vect + i))->cost.act_time * GpG.weight_time ) /  weight)  +  (*(neighb_vect + i))->cost.weight + (*(neighb_vect + i))->cost.timed_fa * 1.5;
	      //      	  cost = max_act_incons*(((*(neighb_vect + i))->cost.act_cost* GpG.orig_weight_cost + (*(neighb_vect + i))->cost.act_time * GpG.orig_weight_time) /  weight)  +  (*(neighb_vect + i))->cost.weight;
	    }
	}
     if (DEBUG3)
       {
         /** 
	     Se il costo minore e' maggiore di zero 
	     **
	     If the smaller cost is greates than zero
	 **/
	 printf("\n");
	 if((*(neighb_vect + i))->constraint_type == C_T_REMOVE_ACTION)
	   printf("\n REMOVE ");
	  if((*(neighb_vect + i))->constraint_type == C_T_INSERT_ACTION)
	   printf("\n INSERT ");
	  printf (" neighborhood Act [%d] %s, level %d \n   Incons %.2f   Cost %.2f   Time %.2f   Timed %.2f Tot weight cost %.2f ", (*(neighb_vect + i))->act_pos,
		 print_op_name_string ((*(neighb_vect + i))->act_pos, temp_name), (*(neighb_vect + i))->act_level, (*(neighb_vect + i))->cost.weight,
		 (*(neighb_vect + i))->cost.act_cost,(*(neighb_vect + i))->cost.act_time, (*(neighb_vect + i))->cost.timed_fa, cost);
       }
     if (minor_cost > 0)
	{
	  if (( minor_cost- cost) >  MIN_VALUE )
	    {
	      /** 
		 Assegno a pos il valore 1
		 **
		 I assign to pos value 1
	      **/
	      pos = 1;
	      /** 
		Pongo l'azione nel vettore del vicinato in posizione i 
		**
		I place the action in the array of environs in position i
	      **/
	      *pos_temp_vect = i;
	      /** 
		Associo a minor_cost (rappresentante il costo minore) cost 
		**
		I associate to minor_cost (representative the smaller cost) cost
	      **/
	      minor_cost = cost;
	      /** 
		Associo al campo best_cost (costo migliore) di local_search il costo dell'azione 
		**
		I associate to the field best_cost (best cost) of local_search the cost of the action
	      **/
	      local_search.best_cost = cost;	/** 
						   Utilizzata nella fase di definizione del costo delle azioni successive
						   **
						   Used in the phase of definition of the cost of the successive actions
						**/
	    }
	  else if ( fabsf( cost - minor_cost) < 0.5 )
	    {

	      /** 
		Check aggiuntivo per non inserire le azioni "simili" con lo stesso costo (cost)
		**
		Additional Check to not insert the similar actions with the same cost (cost)
	      **/
	      for (j = 0; j < pos; j++)
		{
		  if (j >= MAX_MAX_NODES) {
#ifdef __MY_OUTPUT__
		    MSG_ERROR ( WAR_MAX_MAX_NODES );
#else
		    printf( WAR_MAX_MAX_NODES );
#endif    
		    exit (1);
		  }	
		  


		  if (i >= MAX_MAX_NODES) {
#ifdef __MY_OUTPUT__
		    MSG_ERROR ( WAR_MAX_MAX_NODES );
#else
		    printf( WAR_MAX_MAX_NODES );
#endif    
		    exit (1);
		  }	
		  

		  if ((*(neighb_vect + i))->act_pos ==
		      (*(neighb_vect + *(pos_temp_vect + j)))->act_pos)
		    break;
		}
	      /** 
		Pongo le azioni (con costo uguale) nella medesima posizione nel vettore del vicinato 
		**
		I place the actions (with equal cost) in the same position in the carrier of environs
	      **/
	      if (j == pos)
		*(pos_temp_vect + pos++) = i;
	    }
	}
      /** 
	Se il costo dell'azione e' negativo 
	**
	If the cost of the action is negative
      **/
      else if (cost <= 0.0)
	{
	  /** 
	    Se l'azione ha costo inferiore a minor_cost (costo minore) 
	    **
	    If the action has an inferior cost than minor_cost (smaller cost)
	  **/
	  if (cost < minor_cost)
	    {
	      pos = 1;
	      if (neg >= MAX_MAX_NODES) {
#ifdef __MY_OUTPUT__
		MSG_ERROR ( WAR_MAX_MAX_NODES );
#else
		printf( WAR_MAX_MAX_NODES );
#endif    
		exit (1);
	      }	
	      /** 
		Aggiorno pos_temp_vect 
		**
		I update pos_temp_vect
	      **/
	      *(pos_temp_vect + neg++) = *pos_temp_vect;
	      /** 
		Pongo l'azione in posizione i nel vettore del vicinato 
		**
		I place the action in position in the array of environs
	      **/
	      *pos_temp_vect = i;
	      /** 
		Aggiorno minor_cost con cost 
		**
		I update minor_cost with cost
	      **/
	      minor_cost = cost;
	      /** 
		Aggiorno il campo relativo al costo di local search (best_cost) con il costo dell'azione 
		**
		I update the relative field to the cost of local search (best_cost) with the cost of the action
	      **/
	      local_search.best_cost = cost; /** 
						 Utilizzata nella fase di definizione del costo delle 
						 azioni successive
						 **
						 Used in the phase of definition of the cost of
						 successive action
					     **/
	    }
	  /** 
	    Se il costo dell'azione (che e' in questa situazione <0) e' uguale a minor_cost 
	    **
	    If the cost of the action (that is in this situation <0) is equal to minor_cost
	  **/
	  else if (cost == minor_cost)
	    {
	      /** 
		Check aggiuntivo per non inserire le azioni "simili" con lo stesso costo (cost)
		**
		Additional control to not insert the similar actions with the same cost (cost)
	      **/
	      for (j = 0; j < pos; j++)
		{
		  if (j >= MAX_MAX_NODES){
#ifdef __MY_OUTPUT__
		    MSG_ERROR ( WAR_MAX_MAX_NODES );
#else
		    printf( WAR_MAX_MAX_NODES );
#endif    
		    exit (1);
		  }	
		  
		  
		  if (i >= MAX_MAX_NODES) {
#ifdef __MY_OUTPUT__
		    MSG_ERROR ( WAR_MAX_MAX_NODES );
#else
		    printf( WAR_MAX_MAX_NODES );
#endif    
		    exit (1);
		  }	
		  		  
		  
		  if ((*(neighb_vect + i))->act_pos ==
		      (*(neighb_vect + *(pos_temp_vect + j)))->act_pos)
		    break;
		}
	      /** 
		Pongo le azioni (con costo uguale) nella medesima posizione nel vettore del vicinato 
		**
		I place the actions (with equal cost) in the same position in the carrier of environs
	      **/
	      if (j == pos)
		{
		  *(pos_temp_vect + neg++) = *(pos_temp_vect + pos);
		  *(pos_temp_vect + pos++) = i;
		}
	    }

	  else
	    *(pos_temp_vect + neg++) = i;
	}
    }

  *num_min = pos;		/* numerosity of actions with lower cost */

  if( *num_min >1 && minor_cost<MAXFLOAT && GpG.extended_effects_evaluation)
    {
      /**
	 Cerco di migliorare valutazione euristica
	 **
	 Trying to improve the euristic valutation
      **/
      for(i=0; i<  *num_min ; i++)
	{
	  
	  build_relaxed_plan_for_next_goals((*(neighb_vect +  pos_temp_vect[i]))->act_level);

	  build_relaxed_plan_from_action_for_next_goals(*(neighb_vect +  pos_temp_vect[i]),  &n_cost);
  
	  if( (*(neighb_vect +  pos_temp_vect[i]))->constraint_type==C_T_REMOVE_ACTION)
	    diff=(*(neighb_vect +  pos_temp_vect[i]))->cost.weight+ n_cost.weight- vectlevel[ (*(neighb_vect +  pos_temp_vect[i]))->act_level+1 ] ->seach_cost_for_next_goals;
	  else
	    diff=(*(neighb_vect +  pos_temp_vect[i]))->cost.weight+ n_cost.weight- vectlevel[ (*(neighb_vect +  pos_temp_vect[i]))->act_level ] ->seach_cost_for_next_goals;

	  if(DEBUG4)
	    printf("\nDIFF  Action %d - %s level %d diff %f",(*(neighb_vect +  pos_temp_vect[i]))->act_pos, print_op_name_string( (*(neighb_vect +  pos_temp_vect[i]))->act_pos,temp_name), (*(neighb_vect +  pos_temp_vect[i]))->act_level,diff);
	  if(diff>0.0)
	    (*(neighb_vect +  pos_temp_vect[i]))->cost.weight=diff;


	}

      if(GpG.evaluation_function==0)
	{
	  minor_cost =	  max_act_incons * ((*(neighb_vect +  pos_temp_vect[0]))->cost.act_cost * weight_c + (*(neighb_vect + pos_temp_vect[0]))->cost.act_time * weight_t ) + (*(neighb_vect +  pos_temp_vect[0]))->cost.weight + (*(neighb_vect + pos_temp_vect[0]))->cost.timed_fa * weight_tf;
	}
      else
	minor_cost = max_act_incons*(((*(neighb_vect + pos_temp_vect[0]))->cost.act_cost* GpG.weight_cost + (*(neighb_vect + pos_temp_vect[0]))->cost.act_time * GpG.weight_time ) /  weight)  +  (*(neighb_vect + pos_temp_vect[0]))->cost.weight + (*(neighb_vect + pos_temp_vect[0]))->cost.timed_fa * 1.5;


      // Attenzione: utilizziamo i dati in  pos_temp_vect e contemporaneamente andiamo ad aggiornare gli elementi precedenti del vettore stesso
      pos = 1;
      for(i=1; i<  *num_min ; i++)
	{
	  
	  if(GpG.evaluation_function==0)
	    {
	      cost =	  max_act_incons * ((*(neighb_vect +  pos_temp_vect[i]))->cost.act_cost * weight_c + (*(neighb_vect + pos_temp_vect[i]))->cost.act_time * weight_t ) + (*(neighb_vect +  pos_temp_vect[i]))->cost.weight + (*(neighb_vect + pos_temp_vect[i]))->cost.timed_fa * weight_tf;
	    }
	  else
	      cost = max_act_incons*(((*(neighb_vect + pos_temp_vect[i]))->cost.act_cost* GpG.weight_cost + (*(neighb_vect + pos_temp_vect[i]))->cost.act_time * GpG.weight_time ) /  weight)  +  (*(neighb_vect + pos_temp_vect[i]))->cost.weight + (*(neighb_vect + pos_temp_vect[i]))->cost.timed_fa * 1.5;

	  if (( minor_cost- cost) > 0.5 )
	    {
	      pos = 1;
	      pos_temp_vect[0] = pos_temp_vect[i]  ;
	      minor_cost = cost;
	      local_search.best_cost = cost;	/**
						   Utilizzata nella fase di definizione del costo delle azioni successive
						   **
						   Used in the phase of definition of the cost of the following action
						**/
	    }
	  else if ( fabsf( cost - minor_cost) < 0.5 )
	    {
	      if ( fabsf( cost - minor_cost) < 0.5 )
		{
		  *(pos_temp_vect + pos++) =pos_temp_vect[i] ;
		}
	    }
	}
    }

  *num_min = pos;		/* numerosity of actions with lower cost */
  *num_neg = neg;		/* numerosity of actions with negative cost */


#ifdef TEST_GR
  check_plan (GpG.curr_plan_length);

#endif 
  return (minor_cost);
}



/*********************************************
            LAGRANGE MULTIPLIER
**********************************************/

/** OK 27-07-04
 * Name: check_value
 * Scopo:
 * Tipo: float
 * Input: float new
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: check_value
*  Objective:
*  Type: float
*  Input: float new
*  Output:
*  Main Data Structures: GpG
*  Main Functions Used:
*  Call gives:
**/
float check_value (float new)
{
  if (new < MIN_POS_S_S)
    {
      // printf("L"); 
      return MIN_POS_S_S;
    }
  else if (new > MAX_POS_S_S)
    {
      // printf("M");
      return MAX_POS_S_S;
    }
  return new;
}


/**  OK 27-07-04
 * Name: update_precond
 * Scopo: Scandisce tutta la lista delle precodizioni non supportate e aggiorna i moltiplicatori di lagrange
 *        delle azioni che sono associate a tali precondizioni
 * Tipo: void
 * Input: nessuno
 * Output: nessuno
 * Strutture dati principali: int false_fa_pos,action_pos;
 *                            float step_prec_incr = GpG.s_s_step;
 *                            constraints_list inconsistenza;
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: update_precond
*  Objective:
*  Type: void
*  Input: int pos_action
*  Output: None
*  Main Data Structures: int false_fa_pos,action_pos;
*                        float step_prec_incr = GpG.s_s_step;
*                        constraints_list inconsistenza;
*  Main Functions Used:
*  Call gives:
 **/
void update_precond()
{
  int                false_fa_pos,action_pos;
  float              step_prec_incr = GpG.s_s_step;
  constraints_list   inconsistenza;

  /**
     Scandisce tutta la lista delle precondizioni
     **
     Scanning all list of the preconditions
  **/
  for (false_fa_pos = 0; false_fa_pos < GpG.num_false_fa; false_fa_pos++) {
         inconsistenza = unsup_fact[false_fa_pos];
	 /**
	    Se la precondizione è nell'ultimo livello, significa che è una precondizione di un goal,quindi viene aggiornato il moltiplicatore di Lagrange dell'azione
	    fittizia memorizzato in GpG.goal_lambda. Viene,poi ,richiesta il ritorno anticipato nel ciclo con continue.
	    **
	    If the precondition is in the last level, it means that is a precondition of a goal, then the Lagrange multiplier of the fictous action memorized in GpG.goal_lambda
	    is updated. Then is request the forwarding return in the continue cycle
	 **/
	 if (*inconsistenza->level==GpG.curr_plan_length){
		GpG.goal_lambda = check_value(GpG.goal_lambda+step_prec_incr);
		GpG.flag_decr_lm_goal=1;
	        continue;
	 }

	 /**
	    Nel caso in cui la precondizione si trovi in un livello sottostante a quello dei goals viene aggiornato il moltplicatore dell'azione corrispondente a quel livello,
	    sempre se tale azione è in uso
	    **
	    In case the precondition is in a lower level that the one of the goals, is updated the Lagrange multiplier of the correspondant action to that level
	 **/
         /**
	    controlla se l'azione che richiede la precondizione è in uso nel piano
	    **
	    controls if the action that request the precondition is in use in the plan
	 **/
         if (GET_ACTION_OF_LEVEL (*inconsistenza->level)->w_is_used){ 
               action_pos = GET_ACTION_POSITION_OF_LEVEL(*inconsistenza->level);  
               /**
		  *inconsistenza->level è il livello nel quale la precondizione non è supportata
		  inconsistenza->action è l'azione che ha tale precondizione
		  **
		  *inconsistenza->level is the level in which the precondition is not supported
		  inconsistenza->action is the action that has this precondition
	       **/
	       CONVERT_ACTION_TO_VERTEX (action_pos)->lamda_prec = 
                      check_value (CONVERT_ACTION_TO_VERTEX (action_pos)->lamda_prec + step_prec_incr);
	       if (CONVERT_ACTION_TO_VERTEX (action_pos)->flag_decr_lm==0) CONVERT_ACTION_TO_VERTEX (action_pos)->flag_decr_lm=1;
	       if (CONVERT_ACTION_TO_VERTEX (action_pos)->flag_decr_lm==2) CONVERT_ACTION_TO_VERTEX (action_pos)->flag_decr_lm=3;
	 }
  }
}



/** OK 27-07-04
 * Name: update_mutex
 * Scopo: Aggiornamento dei moltiplicatori di Lagrange per le mutex dell'azione act
 * Tipo: void
 * Input: int pos_action
 * Output: Nessuno
 * Strutture dati principali: float step_me_incr
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: update_mutex
*  Objective:
*  Type: void
*  Input: int pos_action
*  Output: None
*  Main Data Structures: float step_me_incr
*  Main Functions Used: none
*  Call gives:
 **/
void update_mutex (int pos_action)
{
  float step_me_incr = GpG.s_s_step;

  CONVERT_ACTION_TO_VERTEX (pos_action)->lamda_me=
	 check_value ( CONVERT_ACTION_TO_VERTEX (pos_action)->lamda_me + step_me_incr);
  if (CONVERT_ACTION_TO_VERTEX (pos_action)->flag_decr_lm==0) CONVERT_ACTION_TO_VERTEX (pos_action)->flag_decr_lm=2;
  if (CONVERT_ACTION_TO_VERTEX (pos_action)->flag_decr_lm==1) CONVERT_ACTION_TO_VERTEX (pos_action)->flag_decr_lm=3;
}

/**  OK 27-07-04
 * Name: update_decr_me_prec
 * Scopo: Decrementa i moltiplicatori di Lagrange che non sono stati incrementati nello stesso flips
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: update_decr_me_prec
*  Objective: Decrements the Lagrange multipliers that are not increased in the same flips
*  Type: void
*  Input: none
*  Output: None
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
 **/
void update_decr_me_prec()
 {
   int    pos_action;
   int   cont_level;
   float step_me_decr, step_prec_decr;
   
   step_prec_decr = GpG.sqr_s_s;
   step_me_decr = GpG.sqr_s_s;

   /**
      decrementa se necessario il moltiplicatore dell'azione fittizia
      **
      decrements if necessary the multilier of the fictitious action
   **/
   if (GpG.flag_decr_lm_goal==0) 
        GpG.goal_lambda = check_value(GpG.goal_lambda-step_prec_decr);
   else
         GpG.flag_decr_lm_goal=0;
				
   for (cont_level=0; cont_level<GpG.curr_plan_length;cont_level++) 
      {
	if(CHECK_ACTION_OF_LEVEL(cont_level)==FALSE)
	  continue;

          pos_action= GET_ACTION_POSITION_OF_LEVEL(cont_level);
        
        switch (CONVERT_ACTION_TO_VERTEX(pos_action)->flag_decr_lm) {
	 
        case 0: CONVERT_ACTION_TO_VERTEX (pos_action)->lamda_prec = 
                  check_value (CONVERT_ACTION_TO_VERTEX (pos_action)->lamda_prec - step_prec_decr);
               CONVERT_ACTION_TO_VERTEX (pos_action)->lamda_me = 
                  check_value (CONVERT_ACTION_TO_VERTEX (pos_action)->lamda_me - step_me_decr);
               break;
        case 1: CONVERT_ACTION_TO_VERTEX (pos_action)->lamda_me =  
                  check_value (CONVERT_ACTION_TO_VERTEX (pos_action)->lamda_me - step_me_decr);
               CONVERT_ACTION_TO_VERTEX (pos_action)->flag_decr_lm=0;
               break;
        case 2: CONVERT_ACTION_TO_VERTEX (pos_action)->lamda_prec = 
                  check_value (CONVERT_ACTION_TO_VERTEX (pos_action)->lamda_prec- step_prec_decr);
               CONVERT_ACTION_TO_VERTEX (pos_action)->flag_decr_lm=0;
               break;
        case 3: CONVERT_ACTION_TO_VERTEX (pos_action)-> flag_decr_lm=0;
	        break;
        }
   }
}



/**  
 * Name: update_precond_multilevel
 * Scopo: Scandisce tutta la lista delle precodizioni non supportate e aggiorna i moltiplicatori di Lagrange delle azioni che sono associate a tali precondizioni
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: update_precond_multilevel
*  Objective:
*  Type: void
*  Input: none
*  Output: None
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void update_precond_multilevel ()
{
  int false_fa_pos, action_pos;
  float step_prec_incr =  GpG.s_s_step;
  constraints_list inconsistenza;

  /**
     Scandisce tutta la lista delle precondizioni
     **
     Scan all the list of the preconditions
  **/
  for (false_fa_pos = 0; false_fa_pos < GpG.num_false_fa; false_fa_pos++){

      inconsistenza = unsup_fact[false_fa_pos];
      /**
	 Se la precondizione è nell'ultimo livello, significa che è una precondizione di un goal,quindi viene aggiornato il moltiplicatore di Lagrange dell'azione
	 fittizia memorizzato in GpG.goal_lambda. Viene,poi ,richiesta il ritorno anticipato nel ciclo con continue.
	 **
	 If the precondition is in the last level, it means that is a precondition of a goal, then is update the Lagrange multiplier of the fictious action stored in GpG.goal_lambda
	 Then is requested the forwarding return to the cycle
      **/
      if (*inconsistenza->level==GpG.curr_plan_length){
	   GpG.goal_lambda = check_value(GpG.goal_lambda+step_prec_incr);
	   GpG.flag_decr_lm_goal=1;
	   continue;
      }
      /**
	 Nel caso in cui la precondizione si trovi in un livello sottostante a quello dei goals viene aggiornato il moltplicatore dell'azione corrispondente a quel livello,
	 sempre se tale azione è in uso
	 **
	 In case the precondition is in a lower level, then is updated the multiplier of the correspondent action to that level, if this action is in use
      **/
      if (GET_ACTION_OF_LEVEL (*inconsistenza->level)->w_is_used){ //controlla se l'azione che richiede la precondizione è in uso nel piano

          //*inconsistenza->level è il livello nel quale la precondizione non è supportata
          //inconsistenza->action è l'azione che ha tale precondizione
	  action_pos = GET_ACTION_POSITION_OF_LEVEL(*inconsistenza->level);
          vectlevel[*inconsistenza->level]->lambda_prec[action_pos] = 
              check_value (vectlevel[*inconsistenza->level]->lambda_prec[action_pos] + step_prec_incr);
          if (vectlevel[*inconsistenza->level]->flag_decr_lm==0) vectlevel[*inconsistenza->level]->flag_decr_lm=1;
	  if (vectlevel[*inconsistenza->level]->flag_decr_lm==2) vectlevel[*inconsistenza->level]->flag_decr_lm=3;
      }
  }
}


/**  OK 27-07-04
 * Name: update_decr_me_prec_multilevel
 * Scopo: Decrementa i moltiplicatori di Lagrange che non sono stati incrementati nello stesso flips
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: update_decr_me_prec_multilevel
*  Objective:
*  Type: void
*  Input: none
*  Output: None
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void update_decr_me_prec_multilevel()
 {
   int pos_level;
   float step_me_decr, step_prec_decr;
   
   step_prec_decr = GpG.sqr_s_s;
   step_me_decr = GpG.sqr_s_s;

   /**
      decrementa se necessario il moltiplicatore dell'azione fittizia
      **
      decrements if necessary the multiplier of the fictitious action
   **/
   if (GpG.flag_decr_lm_goal==0) 
        GpG.goal_lambda = check_value(GpG.goal_lambda-step_prec_decr);
   else 
        GpG.flag_decr_lm_goal=0;

   for (pos_level=0;pos_level<GpG.max_plan_length;pos_level++){
     /**
	controlla se l'azione che richiede la precondizione e' in uso nel piano
	** 
	controls if the action that request the precondition is in use in the plan
     **/
	  if (!(GET_ACTION_OF_LEVEL (pos_level)->w_is_used)) continue;
	   switch (vectlevel[pos_level]->flag_decr_lm) {

	   case 0:   vectlevel[pos_level]->lambda_prec[GET_ACTION_POSITION_OF_LEVEL(pos_level)]=
		     check_value (vectlevel[pos_level]->lambda_prec[GET_ACTION_POSITION_OF_LEVEL(pos_level)] - step_prec_decr);
		     vectlevel[pos_level]->lambda_me[GET_ACTION_POSITION_OF_LEVEL(pos_level)]=
		     check_value (vectlevel[pos_level]->lambda_me[GET_ACTION_POSITION_OF_LEVEL(pos_level)] - step_me_decr);
                     break;
	   case 1:   vectlevel[pos_level]->lambda_me[GET_ACTION_POSITION_OF_LEVEL(pos_level)]=
		     check_value (vectlevel[pos_level]->lambda_me[GET_ACTION_POSITION_OF_LEVEL(pos_level)] - step_me_decr);
                     vectlevel[pos_level]->flag_decr_lm=0;
		     break;

	   case 2:   vectlevel[pos_level]->lambda_prec[GET_ACTION_POSITION_OF_LEVEL(pos_level)]=
		     check_value (vectlevel[pos_level]->lambda_prec[GET_ACTION_POSITION_OF_LEVEL(pos_level)] - step_prec_decr);
                     vectlevel[pos_level]->flag_decr_lm=0; 
                     break;

	   case 3:   vectlevel[pos_level]->flag_decr_lm=0;
		      break;
	   }
   }
}


/**  OK 27-07-04
 * Name: update_mutex_multilevel
 * Scopo: Aggiornamento dei moltiplicatori di Lagrange per le mutex
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: update_mutex_multilevel
*  Objective:
*  Type: void
*  Input: none
*  Output: None
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void update_mutex_multilevel (int level,int pos_action)
{

 float step_me_incr = GpG.s_s_step;

 vectlevel[level]->lambda_me[pos_action]=
     check_value (vectlevel[level]->lambda_me[pos_action] + step_me_incr);
 if (vectlevel[level]->flag_decr_lm==0)   vectlevel[level]->flag_decr_lm=2;
 if (vectlevel[level]->flag_decr_lm==1)   vectlevel[level]->flag_decr_lm=3;
}
  

// Funzione che realizza le statistiche sui Moltiplicatori di Lagrange.  
#ifdef __STATISTIC_LM__

/**  OK 27-07-04
 * Name: init_statistic
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: init_statistic
*  Objective:
*  Type: void
*  Input: none
*  Output: None
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void init_statistic()
{
  lm_prec_min_final = lm_me_min_final = MAX_POS_S_S;
  lm_prec_max_final = lm_me_max_final = MIN_POS_S_S;

//apertura dei file su cui verranno salvati i dati riguardanti le statistiche
  if ((file_average_prec = fopen("lambda_average_prec.tst","w")) == NULL) { printf("\nImpossibile aprire il file lm_average_prec\n"); }
  if ((file_var_prec = fopen("lambda_var_prec.tst","w")) == NULL)         { printf("\nImpossibile aprire il file lm_var_prec\n"); }
  if ((file_average_me = fopen("lambda_average_me.tst","w")) == NULL)     { printf("\nImpossibile aprire il file lm_average_me\n"); }
  if ((file_var_me = fopen("lambda_var_me.tst","w")) == NULL)             { printf("\nImpossibile aprire il file lm_var_me\n"); }
}


/**  OK 27-07-04
 * Name: close_statistic_files
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: close_statistic_files
*  Objective:
*  Type: void
*  Input: none
*  Output: None
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void close_statistic_files()
{
  /**
     chiusura file
     **
     closing file
  **/
    fclose(file_average_prec);
    fclose(file_average_me);
    fclose(file_var_prec);
    fclose(file_var_me);
}


/**  OK 27-07-04
 * Name: statistic_lm_statici
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: statistic_lm_statici
*  Objective:
*  Type: void
*  Input: none
*  Output: None
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void statistic_lm_statici()
{

int position;

float lm_prec_current;
float lm_me_current;

 /**
    Variabili statistica parziale per lm prec
    **
    Variables partial statistic for lm prec
 **/
float lm_prec_max,lm_prec_min;
float sum_prec = 0.0;
float average_prec = 0.0;
float var_prec = 0.0;

 /**
    Variabili statistica parziale per lm me
    **
    Variables partial statistic for lm me
 **/
float lm_me_max,lm_me_min;
float sum_me = 0.0;
float average_me = 0.0;
float var_me = 0.0;

int num_action_current = 0;

 /**
    Variabili statistica globale
    **
    Variables global statistic
 **/
static float sum_prec_final = 0.0;
static float sum_me_final = 0.0;

static int num_action_final = 0;
 

lm_prec_min = lm_me_min = MAX_POS_S_S;
lm_prec_max = lm_me_max = MIN_POS_S_S;

 /**
    Scandisce tutti i moltiplicatori nell'istante
    **
    Scan all thew multiplier in the instant
 **/
  for (position=0; position<gnum_ef_conn; position++){ 	
        if (gef_conn[position].in_plan) continue;
        num_action_current += 1;
        lm_prec_current = CONVERT_ACTION_TO_VERTEX(position)->lamda_prec;
        lm_me_current   = CONVERT_ACTION_TO_VERTEX(position)->lamda_me;
        /**
	   Calcolo valori statistici
	   **
	   Calculating the statistic values
	**/
	if (lm_prec_min>lm_prec_current)  lm_prec_min = lm_prec_current;
        if (lm_me_min>lm_me_current)      lm_me_min = lm_me_current;
	if (lm_prec_max<lm_prec_current)  lm_prec_max = lm_prec_current;
	if (lm_me_max<lm_me_current)      lm_me_max = lm_me_current;
				
	sum_prec += lm_prec_current;
	sum_me += lm_me_current;
  }
  /**
     Calcolo della media
     **
     Calculating the average value
  **/
  average_prec = (sum_prec/(float)gnum_ef_conn); 
  average_me = (sum_me/(float)gnum_ef_conn); 

  num_action_final += num_action_current;
	 
  /**
     Somma globale
     **
     Global sum
  **/
  sum_prec_final += sum_prec;   // somma globale precondizioni
  sum_me_final += sum_me;     // somma globale me
     
  if (lm_prec_min_final>lm_prec_min)  lm_prec_min_final = lm_prec_min;
  if (lm_me_min_final>lm_me_min)      lm_me_min_final = lm_me_min;
  if (lm_prec_max_final<lm_prec_max)  lm_prec_max_final = lm_prec_max;
  if (lm_me_max_final<lm_me_max)      lm_me_max_final = lm_me_max;
				
  /**
     Scandisce tutti i moltiplicatori nell' istante
     **
     Scan all the multipliers in the instant
  **/
  for (position=0; position<gnum_ef_conn; position++){
       lm_prec_current = CONVERT_ACTION_TO_VERTEX(position)->lamda_prec;
       lm_me_current = CONVERT_ACTION_TO_VERTEX(position)->lamda_me;
	 
       /**
	  Calcolo varianza
	  **
	  Calculating variance
       **/
       var_prec += pow(lm_prec_current-average_prec,2);
       var_me += pow(lm_me_current-average_me,2);
  }
  
  var_prec_final += var_prec;
  var_me_final += var_me;

  var_prec = var_prec/(float)num_action_current;
  var_me = var_me/(float)num_action_current;
  
  /**
     Stampa dei valori su i relativi file.
     **
     Printing values on own files
  **/
  fprintf (file_average_prec,"%d %f\n",GpG.count_num_try,average_prec);
  fprintf (file_average_me,"%d %f\n",GpG.count_num_try,average_me);
  fprintf (file_var_prec,"%d %f\n",GpG.count_num_try,var_prec);
  fprintf (file_var_me,"%d %f\n",GpG.count_num_try,var_me);
  
  /**
     Varianza Finale e Media totale
     **
     Final variance and total average
  **/
  var_prec_final = (var_prec_final/(float)num_action_final);
  var_me_final = (var_me_final/(float)num_action_final);
  average_prec_final = (sum_prec_final/(float)num_action_final);
  average_me_final = (sum_me_final/(float)num_action_final);
}     


/**  OK 27-07-04
 * Name: statistic_lm_multilevel
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: statistic_lm_multilevel
*  Objective:
*  Type: void
*  Input: none
*  Output: None
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void statistic_lm_multilevel()
{
  int   pos_level;; /**
		       numero livello
		       **
		       number of level
		    **/
  float lm_prec_current;
  float lm_me_current;
  
  /**
     Variabili statistica parziale per lm prec
     **
     Variables partial statistic for lm prec
  **/
  float lm_prec_max,lm_prec_min;
  float sum_prec = 0.0;
  float average_prec = 0.0;
  float var_prec = 0.0;
  
  /**
     Variabili statistica parziale per lm me
     **
     Variables partial statistic for lm me
  **/
  float lm_me_max,lm_me_min;
  float sum_me = 0.0;
  float average_me = 0.0;
  float var_me = 0.0;
  
  /**
     Numero di Azioni
     **
     Number of action
  **/
  int   num_action_current = 0;

  /**
     Variabili statistica globale
     **
     Variables global statistic
  **/
  static float sum_prec_final = 0.0;
  static float sum_me_final = 0.0;

  /**
     Numero Totale di Azioni
     **
     Total number of actions
  **/
  static int  num_action_final = 0; 

  lm_prec_min = lm_me_min = MAX_POS_S_S;
  lm_prec_max = lm_me_max = MIN_POS_S_S;

  /**
     Scandisce tutti i moltiplicatori nell'istante
     **
     Scan all thew multiplier in the instant
  **/
  for (pos_level=0; pos_level<GpG.max_plan_length; pos_level++){
	if (!(GET_ACTION_OF_LEVEL (pos_level)->w_is_used)) continue;
	num_action_current += 1;
        lm_prec_current= vectlevel[pos_level]->lambda_prec[GET_ACTION_POSITION_OF_LEVEL(pos_level)];
        lm_me_current  = vectlevel[pos_level]->lambda_me[GET_ACTION_POSITION_OF_LEVEL(pos_level)];

        /**
	   Calcolo valori statistici
	   **
	   Calculating the statistic values
	**/
	if (lm_prec_min>lm_prec_current) lm_prec_min = lm_prec_current;
	if (lm_me_min>lm_me_current) lm_me_min = lm_me_current;		     				 
	if (lm_prec_max<lm_prec_current) lm_prec_max = lm_prec_current;
	if (lm_me_max<lm_me_current) lm_me_max = lm_me_current;
		
        sum_prec += lm_prec_current;
	sum_me += lm_me_current;
    }
     
    /**
       Calcolo della media
       **
       Calculating the average value
    **/
    average_prec = (sum_prec/(float)num_action_current); 
    average_me = (sum_me/(float)num_action_current); 
	  
    num_action_final += num_action_current;

    /**
       Somma globale
       **
       Global sum
    **/
    sum_prec_final += sum_prec;   // somma globale precondizioni
    sum_me_final += sum_me;       // somma globale me
    
   
    if (lm_prec_min_final>lm_prec_min) lm_prec_min_final = lm_prec_min;
    if (lm_me_min_final>lm_me_min) lm_me_min_final = lm_me_min;
			     				 
    if (lm_prec_max_final<lm_prec_max) lm_prec_max_final = lm_prec_max;
    if (lm_me_max_final<lm_me_max) lm_me_max_final = lm_me_max;
	 
    /**
       Secondo ciclo necessario per il calcolo della varianza, una volta calcolata la media
       **
       Second cycle necessary for calculating variance, after calculating average value
    **/
    for (pos_level=0;pos_level<GpG.max_plan_length;pos_level++){
	 if (!(GET_ACTION_OF_LEVEL (pos_level)->w_is_used)) continue;
	 lm_prec_current = vectlevel[pos_level]->lambda_prec[GET_ACTION_POSITION_OF_LEVEL(pos_level)];
         lm_me_current = vectlevel[pos_level]->lambda_me[GET_ACTION_POSITION_OF_LEVEL(pos_level)];

         /**
	    Calcolo varianza
	    **
	    Calculating variance
	 **/
         var_prec += pow(lm_prec_current-average_prec,2);
	 var_me += pow(lm_me_current-average_me,2);
      }
    
    var_prec_final += var_prec;
    var_me_final += var_me;    

    var_prec = var_prec/(float)num_action_current;
    var_me = var_me/(float)num_action_current; 
 
    /**
       stampa valori su i relativi file
       **
       printing values on file
    **/
    fprintf (file_average_prec,"%d %f\n",GpG.count_num_try,average_prec);
    fprintf (file_average_me,"%d %f\n",GpG.count_num_try,average_me);
    fprintf (file_var_prec,"%d %f\n",GpG.count_num_try,var_prec);
    fprintf (file_var_me,"%d %f\n",GpG.count_num_try,var_me);
    
    /**
       Varianza Finale e Media totale
       **
       Final variance and total average
    **/
    var_prec_final = (var_prec_final/(float)num_action_final);
    var_me_final = (var_me_final/(float)num_action_final); 
    average_prec_final = (sum_prec_final/(float)num_action_final);
    average_me_final = (sum_me_final/(float)num_action_final);
}     
#endif //Endif riguardante __STATISTIC_LM__



/** OK 27-07-04
 * Name: not_tabu
 * Scopo: verificare che una azione non sia nella tabu_list
 * Tipo: int
 * Input: int act
 * Output: TRUE se la ricerca non e' locale o se la ricerca e' locale ma l'azione non fa 
 *         parte della tabu_list
 * Strutture dati principali: GpG
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: choose_actions_dg_list
 *              choose_actions
**
* Name: not_tabu
* Objective: to verify that an action is not in the tabu_list
* Type: int
* Input: int act
* Output: TRUE if the local search not is or if the local search is but the action it does not make
*         part of the tabu_list
* Main Data Structures: GpG
* Main Functions Used: none
* Call gives: choose_actions_dg_list
*             choose_actions
**/
int not_tabu (int act)
{
  /** 
    Variabile di appoggio 
    **
    Variable of support
  **/
  int diff;

  /** 
    Controlla che la ricerca non e' locale 
    **
    It controls that the search is not local
  **/
  if(!GpG.tabuplan_act)
    return TRUE;
  diff = GpG.count_num_try - gef_conn[act].step;

  if (diff < GpG.tabu_length)
    {
      if(DEBUG2)
	printf("\nAct in Tabu: %s previously remove at flip %d", print_op_name_string(act,temp_name), gef_conn[act].step);
      return FALSE;
    }
  else
    return TRUE;
}


/** OK 27-07-04
 * Name: is_fct_in_tabu
 * Scopo:
 * Tipo: int
 * Input: int pos
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate: nessuna
 * Chiamata da:
**
* Name: is_fct_in_tabu
* Objective:
* Type: int
* Input: int pos
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int is_fct_in_tabu (int pos)
{
  if (!GpG.tabuplan_fct)
    return(FALSE);

  if (gft_conn[pos].numR > 2 && gft_conn[pos].step + 3 > GpG.count_num_try)//(GpG.tabu_length % 2))
    {
      if(DEBUG3)
	printf("\nFact in Tabu: %s previously remove at flip %d", print_ft_name_string(pos,temp_name), gft_conn[pos].step);
      return TRUE;
    }
  else
    return FALSE;
}


/** OK 27-07-04
 * Name: ins_fct_in_tabu
 * Scopo:
 * Tipo: void
 * Input: int pos
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: ins_fct_in_tabu
* Objective:
* Type: void
* Input: int pos
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
void ins_fct_in_tabu (int pos)
{
  if (gft_conn[pos].step + 3 > GpG.count_num_try)// GpG.tabu_length > num_try)
    gft_conn[pos].numR++;
  else
    gft_conn[pos].numR = 1;

  gft_conn[pos].step = GpG.count_num_try;

  if(DEBUG1)
    printf("\nInsert Inc in tabu %d - numtry %d - numR %d", pos, num_try, gft_conn[pos].numR);
}



/*********************************************
             BUILD NEIGHBORHOOD    
**********************************************/




/** 
 * Name: define_neighborhood_for_threats 
 * Scopo:
 * Tipo:
 * Input: register NoopNode_list 
 *        node_tofix,int initialize
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: define_neighborhood_for_threats 
* Objective: Define the set of action that removes the inconsistency.
*            Associated with "tofix"
* Type:
* Input: register NoopNode_list 
*        node_tofix,int initialize
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int define_neighborhood_for_threats (register NoopNode_list node_tofix, int initialize)
{
  int i, noop_pos;
  FtConn *o_tofix;
  FctNode_list fact_node = NULL;
  neighb temp_act;


  if (initialize != 0)
    {
      reset_neighborhood ();
    }
  if (*node_tofix->level > GpG.curr_plan_length)
    return 0;

#ifdef __TEST__
  check_plan (GpG.curr_plan_length);
#endif

  o_tofix = CONVERT_NOOP_TO_VERTEX (node_tofix->position);

  noop_pos = node_tofix->position;

  /**
     rimuovo l'inconsistenza dal vettore dei constraints
     **
     removing the inconsistence from the array of the constraints
  **/
  remove_treated_noop (node_tofix);

  /**
     Controlli per verificare che l'inconsistenza sia tuttora presente
     **
     Controls to verificate that the inconsistence is now present
  **/
  if (GET_ACTION_POSITION_OF_LEVEL (*node_tofix->level) < 0)
    {

#ifdef __TEST__
      if (DEBUG2)
	printf ("\nErrore No action at level %d", *node_tofix->level);
#endif

      return 0;
    }
  /**
     Controllo che il fatto sia mutex con l'azione
     **
     Control that the fact is mutex with the action
  **/
  if (check_mutex_noop (noop_pos, *node_tofix->level) < 0)
    {
      return 0;
    }
  return 0;

  /**
     controllo se il fatto e' precondizione di almeno una azione 
     **
     control if the fact is precondition for at least an action
  **/
  if (!(vectlevel[*node_tofix->level + 1]->fact[noop_pos].w_is_goal) && !(vectlevel[*node_tofix->level]->fact[noop_pos].w_is_used) && (vectlevel[*node_tofix->level]->fact[noop_pos].w_is_true <= 0))
    {
      return 0;
    }

#ifdef __TEST__
  printf ("\n-------CHOOSE ACTIONS treated_c_l ");
#endif

  /*
  if (vectlevel[*node_tofix->level]->fact[noop_pos].w_is_true <= 0) 
    return 0;
  */

  /**
     Scelgo l'azione che rende vero il fatto 
     **
     I choose the action that makes the fact true
  **/
  for (i = *node_tofix->level; i > 0; i--)
    if (vectlevel[i]->fact[noop_pos].w_is_true
	&& is_fact_in_additive_effects (GET_ACTION_POSITION_OF_LEVEL (i - 1),
					noop_pos))
      {
	temp_act.act_pos = GET_ACTION_POSITION_OF_LEVEL (i - 1);
	temp_act.act_level = i - 1;
	temp_act.constraint_type = C_T_REMOVE_ACTION;

#ifdef __TEST__
	printf ("\n Third act %s level %d ",
		print_op_name_string (temp_act.act_pos, temp_name),
		temp_act.act_level);
#endif

	insert_element_in_neighb (&temp_act);
	break;

      }


  if (num_neighborhood <= 0)
    {
#ifdef __TEST__
      if (DEBUG2)
	printf ("\n Il fatto %s e' supportato all'instante iniziale %d",
		print_ft_name_string (noop_pos, temp_name), i);
#endif

      return num_neighborhood;
    }


  //Controllo che ci sia una azione nel livello e che questa sia mutex con la noop
  if (GET_ACTION_POSITION_OF_LEVEL (*node_tofix->level) < 0
      || check_mutex_noop (noop_pos, *node_tofix->level) < 0)
    {
#ifdef __TEST__
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else
    printf( WAR_BUG );
#endif 
#endif
   
      return 0;
    }

  temp_act.act_pos = GET_ACTION_POSITION_OF_LEVEL (*node_tofix->level);
  temp_act.act_level = *node_tofix->level;
  temp_act.constraint_type = C_T_REMOVE_ACTION;
  insert_element_in_neighb (&temp_act);
#ifdef __TEST__
  printf ("\n first act %s level %d ",
	  print_op_name_string (temp_act.act_pos, temp_name),
	  temp_act.act_level);
#endif

  /**
     Scelgo una azione che ha il fatto come precondizione e l'azione che rende supportato il fatto
     **
     I choose an action that has the fact like precondition and the action that makes supported the fact
  **/
  for (i = *node_tofix->level + 1; i < GpG.curr_plan_length; i++)
    if (vectlevel[i]->fact[noop_pos].w_is_used)
      {
	temp_act.act_pos = GET_ACTION_POSITION_OF_LEVEL (i);;
	temp_act.act_level = i;
	temp_act.constraint_type = C_T_REMOVE_ACTION;
#ifdef __TEST__
	printf ("\n second act %s level %d ",
		print_op_name_string (temp_act.act_pos, temp_name),
		temp_act.act_level);
#endif

	/**
	   Inserisco l'azione nel vicinato
	   **
	   Inserting the action in the neighborhoods
	**/


	insert_element_in_neighb (&temp_act);

	/**
	   Fatto  non supportato
	   **
	   Fact not supported
	**/
	if (CONVERT_FACT_TO_NODE (noop_pos, i)->w_is_true <= 0)
	  fact_node = CONVERT_FACT_TO_NODE (noop_pos, i);

	break;
      }
  if (fact_node == NULL)
    return 0;

  return num_neighborhood;
}

/** 
 * Name: define_neighborhood
 * Scopo:
 * Tipo:
 * Input: register FctNode_list node_tofix
 *        int initialize
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: define_neighborhood
* Objective: Define the set of action that removes the inconsistency.
*            Associated with "node_tofix"
* Type:
* Input: register FctNode_list node_tofix
*        int initialize
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int define_neighborhood (register FctNode_list node_tofix, int initialize)
{
  int i, j, level, propagation, skip;
  FtConn *tofix, *temp_tofix;
  ActNode_list inf_action;
  FctNode_list fact;
  register int el, cel;
  neighb temp_act;
  skip = 0;
  
  if (initialize != 0)
    reset_neighborhood ();
  
  if (*node_tofix->level > GpG.curr_plan_length)
    return 0;
  
  verify_cri_until_level(*node_tofix->level);

 
#ifdef __TEST__
  check_plan (GpG.curr_plan_length);
#endif
  
  
  if ((GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
      || (gft_conn[node_tofix->position].fact_type == IS_DERIVED)) {
    define_restricted_neighborhood (node_tofix, initialize);
    return (num_neighborhood);
  }

  // unsoddisfed goal: look at his add effect 
  // plan's actions with node_tofix as precondition 
  tofix = &gft_conn[node_tofix->position];
  level = *node_tofix->level;
  
#ifdef __TEST__
  printf ("\nChoose_act fact %s  time %d pos %d",
	  print_ft_name_string (node_tofix->position, temp_name),
	  level, tofix->position);
  
#endif 
  temp_tofix = tofix;
  
  while (level < GpG.curr_plan_length && initialize > 0)
    {
      /**
	 Considero le azioni che hanno questo fatto come precondizione
	 **
	 I consider the actions that has this fact like precondition
      **/
      propagation = 1;
      inf_action = GET_ACTION_OF_LEVEL (level);
      el = inf_action->position;
      
      /**
	 Precondizioni at start
	 **
	 at start preconditions
      **/
      if (is_fact_in_preconditions (el, tofix->position)
	  && inf_action->w_is_used && not_tabu (el))
	{
	  
#ifdef __TEST__
	  printf ("\n\nChoose_act act precond %s  time %d pos %d",
		  print_op_name_string (el, temp_name), level, el);
	  
#endif
	  temp_act.act_pos = el;
	  temp_act.act_level = level;
	  temp_act.constraint_type = C_T_REMOVE_ACTION;
	  temp_act.unsup_fact = node_tofix->position;
	  
	  insert_element_in_neighb (&temp_act);
	  propagation = 0;     /**
				  Considero unicamente una azione che ha questo fatto come precondizione
				  **
				  I only consider an action that has this fact like precondition
			       **/
	}
      
      if (is_fact_in_preconditions_overall (el, tofix->position)
	  && !is_fact_in_additive_effects_start (el, tofix->position)
	  && inf_action->w_is_used && not_tabu (el))
	{
	  
#ifdef __TEST__
	  printf
	    ("\n\nChoose_act act precond OVERALL %s  time %d pos %d",
	     print_op_name_string (el, temp_name), level, el);
	  
#endif
	  temp_act.act_pos = el;
	  temp_act.act_level = level;
	  temp_act.constraint_type = C_T_REMOVE_ACTION;
	  temp_act.unsup_fact=node_tofix->position;
	  
	  insert_element_in_neighb (&temp_act);
	  propagation = 0;     /**
				  Considero unicamente una azione che ha questo fatto come precondizione
				  **
				  I only consider an action that has this fact like precondition
			       **/
	}

      inf_action = GET_ACTION_OF_LEVEL (level - 1);
      if (level == 0)
	inf_action = GET_ACTION_OF_LEVEL (level);
      el = inf_action->position;
      
      /**
	 Precondizioni at end
	 **
	 at end preconditions
      **/
      if (is_fact_in_preconditions_end (el, tofix->position)
	  && !(is_fact_in_additive_effects_start (el, tofix->position))
	  && inf_action->w_is_used && not_tabu (el))
	{
	  
#ifdef __TEST__
	  printf ("\n\nChoose_act act precond %s  time %d pos %d",
		  print_op_name_string (el, temp_name), level, el);
	  
#endif
	  temp_act.act_pos = el;
	  temp_act.act_level = level - 1;
	  temp_act.constraint_type = C_T_REMOVE_ACTION;
	  temp_act.unsup_fact=node_tofix->position;
	  
	  insert_element_in_neighb (&temp_act);
	  propagation = 0;     /**
				  Considero unicamente una azione che ha questo fatto come precondizione
				  **
				  I only consider an action that has this fact like precondition
			       **/
	  skip = 1;
	}
      if (level < GpG.curr_plan_length
	  && vectlevel[level]->noop_act[node_tofix->position].
	  w_is_goal && propagation == 1)
	{
	  level++;
	}
      else
	break;
    }
  level = *node_tofix->level;
  // IS      if (GpG.num_solutions && initialize > 0 && level > 0)
  if (  initialize > 0 && level > 0)
    {
      /**
	 Inseriamo l'eventuale azione che blocca la catena di noop che supporterebbero l'inconsistenza in questione
	 **
	 We insert any possible action that blocks the chain of noop that may support the inconsistence
      **/
      for (level--; level >= 0; level--)
	if (GET_ACTION_POSITION_OF_LEVEL (level) >= 0
	    && check_mutex_noop (node_tofix->position, level) >= 0)
	  break;
      if (level >= 0)
	{
	  inf_action = GET_ACTION_OF_LEVEL (level);
	  el = inf_action->position;
	  if (vectlevel[level]->fact[node_tofix->position].w_is_true
	      && not_tabu (el))
	    {
	      
#ifdef __TEST__
	      printf ("\n\nChoose_act act precond %s  time %d pos %d",
		      print_op_name_string (el, temp_name), level, el);
	      
#endif
	      temp_act.act_pos = el;
	      temp_act.act_level = level;
	      temp_act.constraint_type = C_T_REMOVE_ACTION;
	      temp_act.unsup_fact = node_tofix->position;
	      
	      insert_element_in_neighb (&temp_act);
	      propagation = 0;     /**
				      Considero unicamente una azione che ha questo fatto come precondizione
				      **
				      I only consider an action that has this fact like precondition
				   **/
	      skip = 1;
	    }
	}
    }
  if (initialize > 0)
    {
      if (num_neighborhood == 0
	  && *node_tofix->level < GpG.curr_plan_length)
	{
	  if (!GpG.tabuplan_act  && node_tofix->w_is_goal)
	    {
	      
#ifdef __TEST__
	      if (DEBUG3)
		printf ("\n WARNING wrong w_is_goal %s %d ",
			print_ft_name_string (tofix->position,
					      temp_name), *node_tofix->level);
#endif
	      node_tofix->w_is_goal = 0;
	      vectlevel[*node_tofix->level]->
		prec_vect[GUID_BLOCK (tofix->position)] &=
		~(GUID_MASK (tofix->position));
	      vectlevel[*node_tofix->level]->
		true_crit_vect[GUID_BLOCK (tofix->position)] &=
		~(GUID_MASK (tofix->position));
	      vectlevel[*node_tofix->level]->
		false_crit_vect[GUID_BLOCK (tofix->position)] &=
		~(GUID_MASK (tofix->position));

	      return num_neighborhood;
	    }

#ifdef __TEST__
	  printf ("\n Warning num_neighborhood==0");
#endif
	}
    }
  level = *node_tofix->level;
  fact = NULL;
  
  /**
     considero le azioni del livello *inform_tofix->level che rendono vero inform_tofix poiche' e' possibile inserire anche un livello vuoto
     **
     I consider the actions of the level *inform_tofix->level that render true inform_tofix because is possible insert an empty level too
  **/
  if (GpG.consider_current_level && initialize > 0)
    {
      for (j = 0; j < gft_conn[tofix->position].num_A; j++)
	if (CHECK_ACTION_POS
	    ((cel = gft_conn[tofix->position].A[j]), level)
	    && !is_fact_in_delete_effects (cel, tofix->position))
	  {
	    temp_act.act_pos = cel;
	    temp_act.act_level = level;
	    temp_act.constraint_type = C_T_INSERT_ACTION;
	    
	    temp_act.unsup_fact=tofix->position;
	    
	    //if (not_tabu (cel))
	      
	    insert_element_in_neighb (&temp_act);
	  }
    }
  level--;
  if (level < 0)
    level = 0;
  
  if ((skip != 1 || initialize == FALSE)
      && CHECK_ACTION_OF_LEVEL (level)
      && CHECK_NOOP_POS (tofix->position, level)
      && check_mutex_noop (tofix->position, level) == -1)
    {
      /**
	 effetti add_end e add_start
	 **
	 add_end and add_start effects
      **/
      for (j = 0; j < gft_conn[tofix->position].num_A; j++)
	if (CHECK_ACTION_POS
	    ((cel = gft_conn[tofix->position].A[j]), level)
	    && !is_fact_in_delete_effects (cel, tofix->position))
	  {
	    temp_act.act_pos = cel;
	    temp_act.act_level = level;
	    temp_act.constraint_type = C_T_INSERT_ACTION;
	    temp_act.unsup_fact=tofix->position;

	    // inserire NODE per fatti
	    if (CHECK_ACTION_POSTION_OF_LEVEL (cel, level))
	      {
		
#ifdef __TEST__
		if (DEBUG3)
		  printf ("ERROR precondiction already supported\n");
		
#endif
	      }
	    else //if (not_tabu (cel))
	      {
		
#ifdef __TEST__
		printf ("\n\nChoose_act act effect %s  time %d pos %d",
			print_op_name_string (cel, temp_name), level,
			cel);

#endif
		insert_element_in_neighb (&temp_act);
	      }
	    if (num_neighborhood > GpG.num_act_cons)
	      break;
	  }
      
      /**
	 Considero le azioni del precedente livello
	 **
	 I consider the action of the previous level
      **/
      if (level > 0 && CHECK_NOOP_POS (tofix->position, level )
	  && check_mutex_noop (tofix->position, level ) == -1)
	{
	  fact = &vectlevel[level]->fact[tofix->position];
	  /**
	     Considero le azioni del precedente livello
	     **
	     I consider the action of the previous level
	  **/
	  i = define_neighborhood (fact, FALSE);
	  if (i < 0)
	    return i;
	}
    }

#ifdef __TEST__
  check_plan (GpG.curr_plan_length);
#endif
  
  return (num_neighborhood);
}


/** OK 27-07-04
 * Name: define_restricted_neighborhood
 * Scopo:
 * Tipo:
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: define_restricted_neighborhood
* Objective: Define the set of action that removes the inconsistency.
*            Associated with "tofix"
* Type:
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int define_restricted_neighborhood (register FctNode_list node_tofix, int initialize)
{
  int i, j;
  int level, curr_level, action_level, next_level;
  int propagation, skip, num_f, fact_pos;

  indexed_vect_list *tuple = NULL;

  FtConn *tofix, *temp_tofix;

  ActNode_list inf_action;

  register int el;
  register int cel;

  float cost, total;

  neighb temp_act;

  int best_action = -1, best_level = 0, best_act_type,ind_sameact_mincost, best_all_action, best_all_level, Ind, act_temp, level_temp;

  int num_neighb_act = 0;
  int max_lev_neighb_act = GpG.neighb_elements_for_level_restrict;

  node_cost loc_n_cost, best_n_cost;

  static int *elem_neighb_action = NULL;
  static int *elem_neighb_level = NULL;
  static float *elem_neighb_cost = NULL;
  static float *elem_neighb_weight_cost = NULL;

  float best_weight_cost = 0.0, loc_weight_cost = 0.0;//, mioweight; 
  float best_all_searchcost, best_all_weightcost;
  float IndCost, IndWeightCost, cost_temp, weight_temp;


  Hvar.temp_removed_act = -1;

  if (elem_neighb_action == NULL)
    elem_neighb_action = (int *) calloc (MAX_MAX_NODES, sizeof (int));

  if (elem_neighb_level == NULL)
    elem_neighb_level = (int *) calloc (MAX_MAX_NODES, sizeof (int));
  
  if (elem_neighb_cost == NULL)
    elem_neighb_cost = (float *) calloc (MAX_MAX_NODES, sizeof (float));

  if (elem_neighb_weight_cost == NULL)
    elem_neighb_weight_cost = (float *) calloc (MAX_MAX_NODES, sizeof (float));


  if(DEBUG3)
    printf("\n\n\nNEIGHBORHOOD DEFINITION:\n\n");

  skip = 0;

  if (initialize != 0)
    {
      // reset_fact_costs();
      reset_neighborhood ();
    }
  if (*node_tofix->level > GpG.curr_plan_length)
    return 0;

  verify_cri_until_level(*node_tofix->level);

#ifdef __TEST__
  check_plan (GpG.curr_plan_length);
#endif


  // unsoddisfed goal: look at his add effect 
  // plan's actions with tofix as precondition 
  tofix = &gft_conn[node_tofix->position];
  level = *node_tofix->level;
  fact_pos =  node_tofix->position;

  
#ifdef __TEST__
  printf ("\nChoose_act fact %s  time %d pos %d",
	  print_ft_name_string (fact_pos, temp_name), level,
	  fact_pos);
#endif

  temp_tofix = tofix;

  /**
     PREDICATI DERIVATI
     **
     DERIVED PREDICATES
  **/
  if (GpG.derived_predicates) 
    {
      if ((fact_pos >= 0) && (gft_conn[fact_pos].fact_type == IS_DERIVED)) {
	create_gdp_path_for(fact_pos, level, &gdp_path);

	if (GpG.derived_pred_in_preconds)
	  tuple = choose_best_tuple_and_level(&gdp_path, &num_f, level, &best_level);
      }
    }
  if(level==GpG.curr_plan_length)
    {      
      if(GpG.extended_unsupported_facts && GpG.extended_unsupported_goals )	
	insert_extended_unsupported_facts_for_action(-1, level);
    }
  else
  while (level < GpG.curr_plan_length && initialize > 0)
    {
      /**
	 Considero le azioni che hanno questo fatto come precondizione
	 **
	 I consider the actions that have this fact as a precondition
      **/
      
      propagation = 1;
      
      inf_action = GET_ACTION_OF_LEVEL (level);
      el = inf_action->position;
      
      /**
	 Precondizioni at start
	 **
	 at start preconditions
      **/
      if (is_fact_in_preconditions (el, fact_pos)
	  && inf_action->w_is_used)
	{
	  if (not_tabu (el))
	    {
	  
#ifdef __TEST__
	      printf ("\n\nChoose_act act precond %s  time %d pos %d",
		      print_op_name_string (el, temp_name), level, el);
#endif
	      temp_act.act_pos = el;
	      temp_act.act_level = level;
	      temp_act.constraint_type = C_T_REMOVE_ACTION;
	      temp_act.unsup_fact=fact_pos;;
	      
	      if(GpG.extended_unsupported_facts)
		insert_extended_unsupported_facts_for_action(el,level);
	  
	      insert_element_in_neighb (&temp_act);
	      propagation = 0;	// ATTENZIONE considero unicamente una azione che ha questo fatto come precondizione
	      
	    }
	  else
	    if(DEBUG2)
	      printf("\nSKIP %s", print_op_name_string(el,temp_name));
	}
      
      /**
	 Precondizioni overall
	 **
	 overall preconditions
      **/
      if (is_fact_in_preconditions_overall (el, fact_pos)
	  && !is_fact_in_additive_effects_start (el, fact_pos)
	  && inf_action->w_is_used)
	{
	  
	  if (not_tabu (el))
	    {
#ifdef __TEST__
	      printf ("\n\nChoose_act act precond OVERALL %s  time %d pos %d",
		      print_op_name_string (el, temp_name), level, el);
#endif
	      temp_act.act_pos = el;
	      temp_act.act_level = level;
	      temp_act.constraint_type = C_T_REMOVE_ACTION;
	      
	      temp_act.unsup_fact=fact_pos;
	      
	      if(GpG.extended_unsupported_facts)
		insert_extended_unsupported_facts_for_action(el,level);
	  
	      
	      insert_element_in_neighb (&temp_act);
	      propagation = 0;     /**
				      Considero unicamente una azione che ha questo fatto come precondizione
				      **
				      I only consider an action that has this fact like precondition
				   **/
	    }
	  else
	    if(DEBUG2)
	      printf("\nSKIP %s", print_op_name_string(el,temp_name));
	}
      
      if(level>0)
        {
	  inf_action = GET_ACTION_OF_LEVEL (level);
	  el = inf_action->position;
	  
	  /**
	     Precondizioni at end
	     **
	     at end preconditions
	  **/
	  if (is_fact_in_preconditions_end (el, fact_pos)
	      && !(is_fact_in_additive_effects_start (el, fact_pos))
	      && inf_action->w_is_used)
	    {
	      if (not_tabu (el))
		{
	      
#ifdef __TEST__
		  printf ("\n\nChoose_act act precond %s  time %d pos %d",
			  print_op_name_string (el, temp_name), level, el);
#endif
		  temp_act.act_pos = el;
		  temp_act.act_level = level;
		  temp_act.constraint_type = C_T_REMOVE_ACTION;
		  
		  temp_act.unsup_fact=fact_pos;
		  
		  if(GpG.extended_unsupported_facts)
		    insert_extended_unsupported_facts_for_action(el,level);
	  
		  
		  insert_element_in_neighb (&temp_act);
		  propagation = 0;     /**
					  Considero unicamente una azione che ha questo fatto come precondizione
					  **
					  I only consider an action that has this fact like precondition
				       **/
		  skip = 1;
		}
	      else
		if(DEBUG2)
		  printf("\nSKIP %s", print_op_name_string(el,temp_name));
	    }
	}
      
	  if (level < GpG.curr_plan_length
	      && vectlevel[level]->noop_act[fact_pos].w_is_goal
	      && propagation == 1)
	    level++;
	  else
	    break;
    }
  
  /**
     Inseriamo l'eventuale azione che blocca la catena di noop che supporterebbero l'inconsistenza in questione
     **
     Inserting the possible action that block the noop chain that may support this inconsistence
  **/
  level = *node_tofix->level;
  if (gft_conn[fact_pos].fact_type == IS_DERIVED)
    {
      if (GpG.derived_pred_in_preconds && tuple)
	{
	  fact_pos = choose_fact_to_support(tuple, num_f, level);
	  level = best_level;
	}
      else
	{
	  create_min_tuple_neighborhood(&gdp_path, fact_pos, level);
	}
    }
  
  // if (GpG.num_solutions && initialize > 0 && level > 0)
  //if (GpG.insert_threated_act_in_neighb && GpG.num_solutions && initialize > 0 && level > 0) 
  if (GpG.insert_threated_act_in_neighb  && initialize > 0 && level > 0)
    {
      for (level--; level >= 0; level--)
	if (GET_ACTION_POSITION_OF_LEVEL (level) >= 0
	    && check_mutex_noop (fact_pos, level) >= 0)
	  break;
      
      if (level >= 0)
	{
	  inf_action = GET_ACTION_OF_LEVEL (level);
	  el = inf_action->position;
	  if (vectlevel[level]->fact[fact_pos].w_is_true)
	    {
	      if (not_tabu (el))
		{

#ifdef __TEST__
		  printf ("\n\nChoose_act act precond %s  time %d pos %d",
			  print_op_name_string (el, temp_name), level, el);
#endif
		  temp_act.act_pos = el;
		  temp_act.act_level = level;
		  temp_act.constraint_type = C_T_REMOVE_ACTION;
		  
		  temp_act.unsup_fact=fact_pos;
		  
		  insert_element_in_neighb (&temp_act);
		  propagation = 0;	// ATTENZIONE considero unicamente una azione che ha questo fatto come precondizione
		  skip = 1;
		}
	      else
		if(DEBUG2)
		  printf("\nSKIP %s", print_op_name_string(el,temp_name));
	    }
	}
    }
  
  level = *node_tofix->level;

  if (initialize > 0)
    {
      if (num_neighborhood == 0
	  && *node_tofix->level < GpG.curr_plan_length)
	{

#ifdef __TEST__
	  printf ("\n Warning num_neighborhood==0");
#endif
	  
	  if (!GpG.tabuplan_act  && node_tofix->w_is_goal)
	    {
#ifdef __TEST__
	      if (DEBUG3)
		printf ("\n WARNING wrong w_is_goal %s %d ",
			print_ft_name_string (fact_pos, temp_name),
			*node_tofix->level);
#endif
	      
	      node_tofix->w_is_goal = 0;
	      vectlevel[*node_tofix->level]->
		prec_vect[GUID_BLOCK (fact_pos)] &=
		~(GUID_MASK (fact_pos));
	      vectlevel[*node_tofix->level]->
		true_crit_vect[GUID_BLOCK (fact_pos)] &=
		~(GUID_MASK (fact_pos));
	      vectlevel[*node_tofix->level]->
		false_crit_vect[GUID_BLOCK (fact_pos)] &=
		~(GUID_MASK (fact_pos));

	      return num_neighborhood;
	    }
#ifdef __TEST__
	  printf ("\n Warning num_neighborhood==0");
#endif

	}
    }
  level = *node_tofix->level;
  
  //SSSS
  action_level = level + 1;	//IV da rivedere
  
  for (next_level = level - 1; next_level >= 0; next_level--)
    if (!
	(CHECK_NOOP_POS (fact_pos, next_level)
	 && check_mutex_noop (fact_pos, next_level) < 0))
      break;		// non posso scendere ulteriormente
  
  best_action = -1;
  best_all_action = -1;
  best_all_level = -1;
  best_all_searchcost = MAXFLOAT;
  best_all_weightcost = MAXFLOAT;

  for (j = 0; j < gft_conn[fact_pos].num_A; j++)
    {
      /**
	 Scelgo il livello migliore per la corrispondente azione e la inserisco nel vicinato
	 **
	 I choose the best level for the correspondant action and I insert her in the neighborhood
      **/
      total = 0.0;
      
      best_n_cost.weight = MAXFLOAT;
      best_n_cost.act_cost = MAXFLOAT;
      best_n_cost.act_time = MAXFLOAT;
      best_weight_cost = MAXFLOAT;

      cel = gft_conn[fact_pos].A[j];
      if (!is_fact_in_delete_effects (cel, fact_pos))
	for (ind_sameact_mincost = num_neighb_act, curr_level = level;
	     curr_level > next_level; curr_level--)
	  {
	    
	    if (GET_ACTION_POSITION_OF_LEVEL (curr_level) < 0 && curr_level != (level))
	      {
#ifdef __TEST__
		printf ("\nEmpty level %d ", curr_level);
#endif
		continue;
	      }

	    if (CHECK_ACTION_POS(cel,curr_level))
	      {
#ifdef __TEST__
		printf ("\n Action of level %d pos %d :", curr_level, cel);
		print_op_name (cel);
#endif
		
		cost = dg_insertion_action_cost (cel, curr_level, &loc_n_cost,0.0);

	        /**
		   Se non si restringe VERTICALMENTE il vicinato
		   **
		   If the neighborhood is not VERTICALLY restricted
		**/
		if(GpG.level_restrict_neighb == FALSE)
		  {
		    loc_weight_cost = weight_cost (&loc_n_cost);
		    
		    if (best_n_cost.weight >= cost)
		      {
			if (best_n_cost.weight > cost || best_weight_cost > loc_weight_cost)
			  {
			    best_action = cel;
			    best_level = curr_level;
			    best_act_type = IS_ACTION;
			    best_n_cost.weight = loc_n_cost.weight;
			    best_n_cost.act_cost = loc_n_cost.act_cost;
			    best_n_cost.act_time = loc_n_cost.act_time;
			    best_weight_cost = weight_cost (&best_n_cost);
			    
			    /*
			      best_all_searchcost serve per la restrizione orizzontale del
			      vicinato (effettuata dopo avere analizzato tutte le azioni)
			    */
			    if (not_tabu(best_action) && (best_all_searchcost > best_n_cost.weight || (best_all_searchcost ==  best_n_cost.weight && best_all_weightcost > best_weight_cost)))
			      {
				best_all_searchcost = best_n_cost.weight;
				best_all_weightcost = best_weight_cost;
				best_all_action = best_action;
				best_all_level = best_level;
			      }
			  }
		      }

                    /**
		       Inseriamo tutti le azioni ai livelli inferiori in grado di supportare il fatto
		       **
		       We insert all the action at the lower level, that can support the fact
		    **/
		    if(num_neighb_act >= MAX_MAX_NODES)
		      {
			printf(WAR_MAX_MAX_NODES);
		      }
		    else
		      {
			elem_neighb_action[num_neighb_act] = cel;
			elem_neighb_level[num_neighb_act] = curr_level;
			elem_neighb_cost[num_neighb_act] = cost;
			elem_neighb_weight_cost[num_neighb_act] = loc_weight_cost;
			num_neighb_act++;
		      }
		  }
		else
		  /**
		     Stiamo restringendo VERTICALMENTE il vicinato
		     **
		     We are VERTICALLY restricting the neighborhood
		  **/
		  /**
		     Se il costo dell'azione A che stiamo esaminando e' minore o
		     uguale del costo della migliore azione di tipo cel finora esaminata
		     **
		     If the cost of the action A that we are examinming is lower or equal
		     to the cost of the best action of tipe cel so far examined
		  **/
		  if (best_n_cost.weight >= cost)
		    {
		      loc_weight_cost = weight_cost (&loc_n_cost);
		      if (best_n_cost.weight == cost)
			{
			  /**
			     A parita' di weightcost (costo di inserimento esaminiamo la combinazione di inserimento, tempo e costo di esecuzione)
			     **
			     In parity of weightcost
			  **/
			  if (best_weight_cost == loc_weight_cost)
			    {
			      /*
				ind_sameact_mincost e' un indice che serve a fare inserire al piu' max_lev_neighb_act+1 canditati di
				A1. All'inizio vale 0. Dopo avere esaminato la prima azione A1 varra' num_neighb_act(A1) ecc...
				(num_neigh_act e' l'indice del vettore degli elementi del vicinato quindi cresce sempre piu')
			      */

			      if (max_lev_neighb_act + ind_sameact_mincost > num_neighb_act)
				{
				  /**
				     inserisco l'azione nel vicinato insieme alle altre azioni di tipo A avente pari costo di inserimento e weight cost
				     **
				     Inserting the action in the neighborhood with the other actions of type A with the same cost of inserting and weight
				  **/
				  elem_neighb_action[num_neighb_act] = cel;
				  elem_neighb_level[num_neighb_act] = curr_level;
				  elem_neighb_cost[num_neighb_act] = cost;
				  elem_neighb_weight_cost[num_neighb_act] = loc_weight_cost;
				  num_neighb_act++;	
				}
#ifdef __TEST__
			      printf
				("\n INSERT_neinghb_elem  BEST ACT %s  time %d inc %.2f act_cost %.2f act_time %.2f   num_neighb_act %d ",
				 print_op_name_string (best_action,
						       temp_name), curr_level,
				 loc_n_cost.weight, loc_n_cost.act_cost,
				 loc_n_cost.act_time, num_neighb_act);
#endif
			      continue;
			      
			    }
			  /**
			     Se l'azione peggiora non la inseriamo nel vicinato
			     **
			     If the action make worse we don't insert it in the neighborhood
			  **/
			  
			  //			  if (best_weight_cost < loc_weight_cost)
			  //			    continue;
			  
			}
		      /**
			 Se l'azione migliora cancelliamo tutti gli elementi della medesima azione finora inseriti e inseriamo l'azione in questione nel vicinato
			 **
			 If the action improve, we remove all the elements of the same action so far inserted and we insert this action in the neighborhood
		      **/
		      
		      num_neighb_act = ind_sameact_mincost;
		      
		      elem_neighb_action[num_neighb_act] = cel;
		      elem_neighb_level[num_neighb_act] = curr_level;
		      elem_neighb_cost[num_neighb_act] = cost;
		      elem_neighb_weight_cost[num_neighb_act] = loc_weight_cost;
		      
		      num_neighb_act++;

		      /**
			 salviamo la migliore azione tra quelle di tipo cel per la restrizione verticale del vicinato
			 **
			 we save the best action among those of cel type for the vertical restriction of the neighborhood
		      **/
		      best_action = cel;
		      best_level = curr_level;
		      best_act_type = IS_ACTION;
		      best_n_cost.weight = loc_n_cost.weight;
		      best_n_cost.act_cost = loc_n_cost.act_cost;
		      best_n_cost.act_time = loc_n_cost.act_time;
		      best_weight_cost = weight_cost (&best_n_cost);

		      /**
			 salviamo la migliore azione tra quelle di tipo cel per la restrizione orizzontale del vicinato
			 **
			 we save the best action among those of cel type for the orizzontal restriction of the neighborhood
		      **/
		      if (not_tabu(best_action) && (best_all_searchcost > best_n_cost.weight || (best_all_searchcost ==  best_n_cost.weight && best_all_weightcost > best_weight_cost)))
			{
			  best_all_searchcost = best_n_cost.weight;
			  best_all_weightcost = best_weight_cost;
			  best_all_action = best_action;
			  best_all_level = best_level;
			}
		      
#ifdef __TEST__
		      printf
			("\n\n\n Choose_neinghb_elem  BEST ACT %s  time %d inc %.2f act_cost %.2f act_time %.2f   num_neighb_act %d ",
			 print_op_name_string (best_action, temp_name),
			 best_level, best_n_cost.weight, best_n_cost.act_cost,
			 best_n_cost.act_time, num_neighb_act);
#endif

		    }
	      }
	    else
	      break;
	    
	  } // end for level
    } //end for action
  
      /*
	printf("\n--- Neighb: step %d-------", num_try);
      for (j = 0; j < num_neighb_act; j++)
      {
      printf("\n%s | lev: %d | cost %.2f | weight %.2f",print_op_name_string (elem_neighb_action[j], temp_name), elem_neighb_level[j], elem_neighb_cost[j], elem_neighb_weight_cost[j]);
      }
      */

  if(GpG.number_restrict_neighb == TRUE)
    {
      for (j = 0; j < GpG.num_elem_neighb_restrict; j++)
	{
	  IndCost = elem_neighb_cost[j];
	  IndWeightCost = elem_neighb_weight_cost[j];
	  Ind = j;
	  
	  for (i = j + 1; i < num_neighb_act; i++)
	    {  
	      if(elem_neighb_cost[i] <= IndCost) 
		{
		  if (elem_neighb_cost[i] < IndCost || elem_neighb_weight_cost[i] < IndWeightCost)
		    {
		      Ind = i;
		      IndCost = elem_neighb_cost[i];
		      IndWeightCost = elem_neighb_weight_cost[i];
		    }
		}
	    }
	  act_temp = elem_neighb_action[j];
	  level_temp = elem_neighb_level[j];
	  cost_temp = elem_neighb_cost[j];
	  weight_temp = elem_neighb_weight_cost[j];
	  
	  elem_neighb_action[j] = elem_neighb_action[Ind];
	  elem_neighb_level[j] = elem_neighb_level[Ind];
	  elem_neighb_cost[j] = elem_neighb_cost[Ind];
	  elem_neighb_weight_cost[j] = elem_neighb_weight_cost[Ind];
	  
	  elem_neighb_action[Ind] = act_temp;
	  elem_neighb_level[Ind] = level_temp;
	  elem_neighb_cost[Ind] = cost_temp;
	  elem_neighb_weight_cost[Ind] = weight_temp;
	}
#ifdef __TEST__
      printf("\n--- RESTRICT NUM: step %d-------", num_try);
      for (j = 0; j < num_neighb_act; j++)
	{
	  printf("\n%s | lev: %d | cost %.2f | weight %.2f",print_op_name_string (elem_neighb_action[j], temp_name), elem_neighb_level[j], elem_neighb_cost[j], elem_neighb_weight_cost[j]);
	  if(j == GpG.num_elem_neighb_restrict-1)
	    printf("\n----------");
	}
      printf("\n\n\n\n");
#endif
    }
  
  if (best_action >= 0)
    {
      /**
	 esaminiamo tutti gli elementi del vicinato inseriti
	 **
	 we examine all the elemnts inserted of the neighborhood
      **/
      for (i = 0; i < num_neighb_act; i++)
	{  
	  if(GpG.number_restrict_neighb == TRUE) 
	    if (i > GpG.num_elem_neighb_restrict - 1)
	      break;
	  
	  //	      printf ("\nACT: %d LEV: %d COST: %.2f", elem_neighb_action[i], elem_neighb_level[i], elem_neighb_cost[i]);
	  /*
	    se si sta effettuando la restrizione orizzontale del vicinato
	  */
	  if(GpG.hcost_neighb == TRUE)
	    {
	      if (best_all_searchcost * GpG.high_cost_restrict_neighb < elem_neighb_cost[i] )
		{
#ifdef __TEST__
		  printf("  SKIP! COST: %.2f BESTCOST: %.2f", elem_neighb_cost[i], best_all_searchcost);
		  printf ("[skip: ACT: %d LEV: %d COST: %.2f BESTCOST: %.2f]", elem_neighb_action[i], elem_neighb_level[i], elem_neighb_cost[i], best_all_searchcost);
#endif
		  /**
		     se il costo dell'elemento supera di 3 volte il costo della migliore azione tra tutte quelle inserite nel vicinato non la inseriamo
		     **
		     if the cost of the elemnt exceed 3 times the cost of the best action among those inserted in the neighbourhood we don't remove it
		  **/
		  continue;
		}
	    }   
	  temp_act.act_pos = elem_neighb_action[i];
	  temp_act.act_level = elem_neighb_level[i];
	  temp_act.constraint_type = C_T_INSERT_ACTION;
	  
	  temp_act.unsup_fact=fact_pos;

	  /**
	     l'azione ritenuta la migliore viene inserita successivamente nel vicinato
	     **
	     the action considered the best is subsequently inserted in the neighbourhood
	  **/
	  if (!(best_all_action == temp_act.act_pos && best_all_level == temp_act.act_level))
	    insert_element_in_neighb (&temp_act);
	  
	  
#ifdef __TEST__
	  else
	    {
	      printf ("\n\n NBEST action found, level %d name ", level);
	      print_op_name (local_search.best_action);
	    }
#endif
	  
	} // end for
    }
  /**
     Inserisco come ultimo elemento del vicinato l'azione ritenuta migliore
     **
     I insert like last element of the neighbourhood the action best considered
  **/
  if (best_all_action >= 0 && CHECK_ACTION_POS (best_all_action, best_all_level))
    {
      if (!not_tabu(best_all_action))
	  printf("\nWarning %d in tabu-list in neighborhood definition", best_all_action);

      //	  printf("\n\nBESTACTION: %d, LEV: %d COST: %.2f", best_all_action, best_all_level, best_all_searchcost);
      
      temp_act.constraint_type = C_T_INSERT_ACTION;
      temp_act.act_pos = best_all_action;
      temp_act.act_level = best_all_level;
      temp_act.unsup_fact = fact_pos;
      
      insert_element_in_neighb (&temp_act);
    }
  
#ifdef __TEST__
  check_plan (GpG.curr_plan_length);
#endif
  
  GpG.tot_num_neighb+=num_neighborhood;

  return (num_neighborhood);
}


/** OK 28-07-04
 * Name: fix_threated_fact
 * Scopo:
 * Tipo:
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: fix_threated_fact
* Objective:
* Type:
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int fix_threated_fact (constraints_list treated_c_l, int num)
{
  EfConn *act;
  float best = 0.0;
  NoopNode_list node_tofix;

  int num_min, num_neg, choice, level;

  node_tofix = CONVERT_NOOP_TO_NODE (treated_c_l->fact, *treated_c_l->level);

  if (DEBUG2)
    printf ("\n### INC CHOICE:\n  Treated fact: %s, level %d\n",
	    print_noop_name_string (treated_c_l->fact, temp_name),
	    *treated_c_l->level);

#ifdef __TEST__
  if (treated_c_l->constraint_type == C_T_UNSUP_FACT){

#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else
    printf( WAR_BUG );
#endif
  }
    
  if (GpG.temporal_plan)
    check_temporal_plan ();
  
#endif
  
if (node_tofix->false_position < 0)
    {
      GpG.num_false_act--;

#ifdef __TEST__
    
      
#ifdef __MY_OUTPUT__
      MSG_ERROR( WAR_BUG );
#else
      printf( WAR_BUG );
#endif
      
#endif
      return 0;
    }
  
  if (num <= 0)
    {

#ifdef __TEST__
      printf ("\n  Warning num1==0");
      
#endif
      remove_treated_noop (node_tofix);
      
      return (FALSE);
    }

  // Find the action set from the neighborhood with lower cost and
  // insert them in pos_temp_vect.  If more than one action has
  // negative cost, insert them in pos_temp_vect.  The cost is put in
  // "best" var.
  if (DEBUG3)
    {
      printf ("\n>< NEIGHBORHOOD EVALUTATION ><  Num act: %d\n", num);
      if (num < 0)
	printf ("\n\n  ___NO ACTIONS\n");
      if (num == 1)
	printf ("\n\n  ___Only ONE action ENABLE");
    }

  choice = -1;
  if (( MY_RANDOM % GpG.denominator) < GpG.numerator)
    {
      if (DEBUG1)
	printf("\n Random choice");
      choice = MY_RANDOM % num;

      neighb_vect[choice]->cost.weight=0.0;
      neighb_vect[choice]->cost.act_cost=0.0;
      neighb_vect[choice]->cost.act_time=0.0;

    }
 
  if(choice < 0) {
  if (num > 1)
    best = find_min (treated_c_l, pos_temp_vect, num, &num_min, &num_neg);

  else
    {
      num_min = 1;
      pos_temp_vect[0] = 0;
    }
  GpG.is_lm = 0;	// LM Per default NON considero la
			// configuraz. corrente come un minimo locale
  if (num == 1)
    {
      choice = 0;	// choose_actions() sets "num" to 1 if ME
			// relations were updated

      neighb_vect[choice]->cost.weight=0.0;
      neighb_vect[choice]->cost.act_cost=0.0;
      neighb_vect[choice]->cost.act_time=0.0;
    }
  else if (best > 0)
    {
      GpG.is_lm = 1;	/**
			   LM Siamo in un minimo locale
			   **
			   LM We are in a local minimum
			**/
      if (num_min == 1)
	choice = pos_temp_vect[0];

      else
	choice = pos_temp_vect[(MY_RANDOM % num_min)];
    }
  else
    {
      if (num_neg == 1)
	choice = pos_temp_vect[0];

      else if ((  MY_RANDOM  % GpG.denominator) < GpG.numerator)
	choice = pos_temp_vect[MY_RANDOM % num_neg];

      else if (num_min == 1)
	choice = pos_temp_vect[0];

      else
	choice = pos_temp_vect[(MY_RANDOM % num_min)];
    }
  }
  act = &gef_conn[neighb_vect[choice]->act_pos];
  level = neighb_vect[choice]->act_level;
  if (DEBUG2)
    {
      printf
	("\n\n=== Action choosen treated fact: %s, num %d, level %d \n     Incons %.3f   Cost %.3f   Time %.3f ",
	 print_op_name_string (act->position, temp_name),GpG.count_num_try , level,
	 neighb_vect[choice]->cost.weight, neighb_vect[choice]->cost.act_cost,
	 neighb_vect[choice]->cost.act_time);
      if (DEBUG6)
	print_actions_in_subgraph ();
    }

#ifdef __TEST__
  printf ("\n Act choosen  %s lev %d ", act->name, level);

#endif


#ifdef __TEST_MIXED__
  printf("\n Inserisci azione da inserire/rimuovere ");
  fflush (stdout);
  scanf("%d",&choice);
#endif

  choice = insert_remove_action (neighb_vect[choice]->act_pos, level,
				 neighb_vect[choice]->constraint_type, 
				 GpG.approximation_level);

  if (DEBUG3)
    {

#ifdef __TEST__
      check_plan (max_time);
      if (GpG.temporal_plan)
	check_temporal_plan ();

#endif
    }
  return (choice);
}




/** 
 * Name: fix_unsup_fact
 * Scopo:
 * Tipo:
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: fix_unsup_fact
* Objective:
* Type:
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int fix_unsup_fact (constraints_list unsup_fact, int num)
{
  int num_min, num_neg, choice, level, i, j;
  float best = 0.0;

  EfConn *act;
  FctNode_list node_tofix;

  Timed_list timedFct;

  node_tofix = CONVERT_FACT_TO_NODE (unsup_fact->fact, *unsup_fact->level);
  
  if (DEBUG2)
    {
      printf
	("\n\n### INC CHOICE:\n  Unsupported fact: position %d, level %d fact name : ",
	 unsup_fact->fact, *unsup_fact->level);
      print_ft_name (unsup_fact->fact);
      printf ("\n");
    }

  

  if(GpG.timed_facts_present) 
    slack_fact_from_act (Hvar.constr);
  
  if(GpG.timed_facts_present && DEBUG3)
    for (i=0; i < gnum_timed_facts; i++)
      for (j=0; j < gnum_tmd_interval[i]; j++)
	{
	  timedFct = &gtimed_fct_vect[i][j];
	  printf("\nslack of %s: %.2f", print_ft_name_string(timedFct->position,temp_name),timedFct->slack);
	}


#ifdef __TEST__

  if (unsup_fact->constraint_type != C_T_UNSUP_FACT) {
    
    
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else
    printf( WAR_BUG );
#endif
  }
  
  if (GpG.temporal_plan)
    check_temporal_plan ();

#endif
  
  if (node_tofix->w_is_goal <= 0 || node_tofix->w_is_true)
    {

      // if :
      // - the node is a fact, and:
      //    - the fact isn't precondition for any actions
      //    - the fact isn't in the planning graph,   
      if (DEBUG3)
	printf ("\n Constraint removed: %s, level %d is_goal %d is_true %d",
		print_ft_name_string (unsup_fact->fact, temp_name),
		*node_tofix->level, node_tofix->w_is_goal,
		node_tofix->w_is_true);
      remove_false_fact (node_tofix);	// Remove  from false vector  
      return (0);
    }

  if (num <= 0)

    {
      if (GpG.tabuplan_act)
	{
	  if(DEBUG1)
	    printf("\nWarning: Neighborhood empty");
	  return -1;
	}


#ifdef __MY_OUTPUT__
      printf ("\n   Warning: step %d - num action for make supported fact %d ==0, level %d, name ",GpG.count_num_try, unsup_fact->fact,  *unsup_fact->level);
      print_ft_name(unsup_fact->fact);
#endif
      remove_false_fact (node_tofix);
      return (FALSE);
    }

  // Find the action set from the neighborhood with lower cost and
  // insert them in pos_temp_vect.  If more than one action has
  // negative cost, insert them in pos_temp_vect.  The cost is put in
  // "best" var.
  if (DEBUG3)
    {
      printf ("\n>< NEIGHBORHOOD EVALUTATION ><  Num act: %d\n", num);
      if (num < 0)
	printf ("\n\n  ___NO ACTIONS\n");
      if (num == 1)
	printf ("\n\n  ___Only ONE action ENABLE");
    }


  choice = -1;
  if (( MY_RANDOM % GpG.denominator) < GpG.numerator)
    {
      choice = MY_RANDOM % num;
      
      if (DEBUG1)
	printf("\n Random choice= %d",choice);
    }
  
  if(choice < 0) {
  if (num > 1)
    best = find_min (unsup_fact, pos_temp_vect, num, &num_min, &num_neg);
  else

    {
      num_min = 1;
      pos_temp_vect[0] = 0;
    }

  GpG.is_lm = 0;	/**
			   LM Per default NON considero la configuraz. corrente come un minimo locale
			   **
			   LM for default i don't consider the courrent configuration like a local minimum
			**/

  if (num == 1)
    {
      choice = 0;			// choose_actions() sets "num" to 1 if ME relations were updated
      
      neighb_vect[choice]->cost.weight=0.0;
      neighb_vect[choice]->cost.act_cost=0.0;
      neighb_vect[choice]->cost.act_time=0.0;

    }
  else if (best > 0)
    {
      GpG.is_lm = 1;	/**
			   LM Siamo in un minimo locale
			   **
			   LM we are in a local minimum
			**/

      if (num_min == 1)
	{
	choice = pos_temp_vect[0];
	if(DEBUG5)
	  printf("\n Num min=1, choice 0");
	}
      else
	{
	  choice = pos_temp_vect[(MY_RANDOM % num_min)];
	if(DEBUG5)
	  printf("\nChoice= %d ", choice);

	}
    }

  else
    {
      if (num_neg == 1)
	choice = pos_temp_vect[0];

      else if ((MY_RANDOM  % GpG.denominator) < GpG.numerator)
	choice = pos_temp_vect[MY_RANDOM % num_neg];

      else if (num_min == 1)
	choice = pos_temp_vect[0];

      else
	choice = pos_temp_vect[(MY_RANDOM % num_min)];
    }
  }
  act = CONVERT_ACTION_TO_VERTEX (neighb_vect[choice]->act_pos);
  level = neighb_vect[choice]->act_level;
  if (DEBUG2)
    {

      printf
	("\n\n=== Action choosen unsup fact: %s, num %d, level %d choice %d \n     Incons %.3f   Cost %.3f   Time %.3f ",
	 print_op_name_string (act->position, temp_name),GpG.count_num_try, level, choice,
	 neighb_vect[choice]->cost.weight, neighb_vect[choice]->cost.act_cost,
	 neighb_vect[choice]->cost.act_time);
      if (DEBUG3)
	print_actions_in_subgraph ();
    }

#ifdef __TEST__
  printf ("\n Act choosen  %s lev %d ",
	  CONVERT_ACTION_TO_VERTEX (neighb_vect[choice]->act_pos)->name,
	  neighb_vect[choice]->act_level);

#endif

#ifdef __TEST_MIXED__
  printf("\n Inserisci azione da inserire/rimuovere ");
  fflush (stdout);
  scanf("%d",&choice);
#endif


  choice =
    insert_remove_action (neighb_vect[choice]->act_pos,
			  neighb_vect[choice]->act_level,
			  neighb_vect[choice]->constraint_type,
			  GpG.approximation_level);

#ifdef __TEST__
  check_plan (GpG.curr_plan_length);
  if (DEBUG6)

    {	
      if (node_tofix->action_fact == IS_FACT)
	my_print_plan ((*node_tofix->level) - 1);
      my_print_plan (*node_tofix->level);
    }
  if (GpG.temporal_plan)
    check_temporal_plan ();
  check_plan (GpG.curr_plan_length);

#endif
  return (choice);
}



/**
 * Name:  define_neighborhood_for_compvar_in_down_level
 * Scopo: Funzione che inserisce azioni nel vicinato numerico di una
 *        precondizione numerica di indice index anche nei livelli 
 *        inferiori a quello in cui la preco risulta non supportata, 
 *        amplia di fatto il vicinato numerico 
 * Tipo: int 
 * Input: 
 * Output: 
 * Strutture dati principali: 
 * Funzioni principali utilizzate: 
 * Chiamata da:
**
* Name: define_neighborhood_for_compvar_in_down_level
* Objective:
* Type: int
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int define_neighborhood_for_compvar_in_down_level (int numeric_fact, action_set *neighbors, int level)
{
  int i, curr_level;
  int num_found = 0;
  int best_level = 0;
  int num_lev_neighb_act = 0;
  float best_weight_cost = 0.0, loc_weight_cost = 0.0, cost=0.0;
  node_cost loc_n_cost, best_n_cost;
  neighb temp_act;
  int mutex;

  if (numeric_fact < 0)
    numeric_fact = -numeric_fact;
  
  temp_act.fact_treated = numeric_fact;

  for (i = 0; i < neighbors->num_A; i++)
    {
      best_level = level;   
       
      if (GpG.numeric_neighbors_in_down_levels)
	{
	  dg_insertion_action_cost (neighbors->A[i], level, &best_n_cost, 0.0);
	  best_weight_cost = weight_cost (&best_n_cost);
	  mutex = 0;

	  for (num_lev_neighb_act = 0, curr_level = get_prev(level); curr_level > 0; curr_level = get_prev(curr_level))
	    {
	      if (are_mutex_ops(GET_ACTION_POSITION_OF_LEVEL(curr_level), neighbors->A[i]))
		mutex++;
	      
	      if(!does_action_support_numeric_precond_in_down_level(numeric_fact, neighbors->A[i], level, curr_level))
		break;
	      
	      cost = dg_insertion_action_cost (neighbors->A[i], curr_level , &loc_n_cost, 0.0);
	      loc_n_cost.weight += mutex;
	      
	      if (loc_n_cost.weight <= best_n_cost.weight)
		{
		  if (best_n_cost.weight == loc_n_cost.weight)
		    {
		      loc_weight_cost = weight_cost (&loc_n_cost);
		      
		      if (loc_weight_cost < best_weight_cost)
			{
			  if (DEBUG3)
			    printf("\n\n[wheight cost] Action %s --> new best level defined : %d [from %d]", print_op_name_string(neighbors->A[i], temp_name), curr_level, level);
			  
			  num_lev_neighb_act++;
			  
			  best_level = curr_level;
			  best_n_cost = loc_n_cost; 
			  best_weight_cost = loc_weight_cost;
			}
		    }
		  else 
		    {
		      if (DEBUG3)
			printf("\n\n[weight] Action %s --> new best level defined : %d [from %d]", print_op_name_string(neighbors->A[i], temp_name), curr_level, level);
		      
		      num_lev_neighb_act++;
		      
		      best_level = curr_level;
		      best_n_cost = loc_n_cost; 
		      best_weight_cost = weight_cost (&best_n_cost);
		    }		 
		}
	    }
	}
      num_found++;	
      temp_act.act_pos = neighbors->A[i];
      temp_act.act_level = best_level;
      temp_act.constraint_type = C_T_INSERT_ACTION;
      temp_act.unsup_fact = numeric_fact;
      insert_element_in_neighb (&temp_act);
    }
  return num_found;
}


/** 
 * Name: create_neighborhood_for_compvar
 * Scopo:
 * Tipo: void
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: create_neighborhood_for_compvar
* Objective:
* Type: void
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
void create_neighborhood_for_compvar (int index, Bool Sign, Bool MulOrDiv,action_set * neighbors, int start, int level)
{
  IntList *el;
  int i, j;
  static int *neighb_actions = NULL;
  float val_before, val_after;
  float out_vect[max_num_value];
  float *in_vect;
  float diff;

  if (neighb_actions == NULL)
    neighb_actions = calloc (gnum_ef_conn / 32 + 1, sizeof (int));
  if (index < 0)
    {
#ifdef __TEST__
      printf ("\n Cambio segno a index %d ", index);
#endif
      index = -index;
    }
  /**
     se comincio ora a creare il vicinato, azzero il bit array  
     **
     if I start now to create the neighbourhood, I set to zero the bit array
  **/
  if (start == 1 && level != -1)
    memset (neighb_actions, 0, (gnum_ef_conn / 32 + 1) * sizeof (int));

  if(level >= 0)
    in_vect = vectlevel[level]->numeric->values;
  else 
    in_vect = vectlevel[0]->numeric->values;

  /*azzerare la l'array globale del vicinato solo se non first time!! static var?? */
  /*osservazione: la equal?? */
  switch (gcomp_var[index].operator)
    {
    case EQUAL_OP:
      printf("\n\nGeneration of neighborhood for EQUAL_OP not yet implemented\n\n");
      exit (1);
      break;
    case GREATER_THAN_OP:
    case GREATER_OR_EQUAL_OP:
      /*aggiungere gli incr di sx e scendere per vedere i decr di dx! */
      create_neighborhood_for_compvar (gcomp_var[index].first_op, Sign, MulOrDiv, neighbors, 0, level);
      create_neighborhood_for_compvar (gcomp_var[index].second_op, !Sign, MulOrDiv, neighbors, 0, level);
      break;
    case LESS_THAN_OP:
    case LESS_THAN_OR_EQUAL_OP:
      /*aggiungere i decr di sx e scendere per vedere gli incr di dx! */
      create_neighborhood_for_compvar (gcomp_var[index].first_op, !Sign, MulOrDiv, neighbors, 0, level);
      create_neighborhood_for_compvar (gcomp_var[index].second_op, Sign, MulOrDiv, neighbors, 0, level);
      break;
    case MUL_OP:
      /*aggiungere gli incr di sx e di dx */
      create_neighborhood_for_compvar (gcomp_var[index].first_op, Sign, 1, neighbors, 0, level);
      create_neighborhood_for_compvar (gcomp_var[index].second_op, Sign, 1, neighbors, 0, level);
      break;
    case PLUS_OP:
      /*aggiungere gli incr di sx e di dx */
      create_neighborhood_for_compvar (gcomp_var[index].first_op, Sign, 0, neighbors, 0, level);
      create_neighborhood_for_compvar (gcomp_var[index].second_op, Sign, 0, neighbors, 0, level);
      break;
    case DIV_OP:
      /*aggiungere gli incr di sx e i decr di dx */
      create_neighborhood_for_compvar (gcomp_var[index].first_op, Sign, 1, neighbors, 0, level);
      create_neighborhood_for_compvar (gcomp_var[index].second_op, !Sign, 1, neighbors, 0, level);
      break;
    case MINUS_OP:
      /*aggiungere gli incr di sx e i decr di dx */
      create_neighborhood_for_compvar (gcomp_var[index].first_op, Sign, 0, neighbors, 0, level);
      create_neighborhood_for_compvar (gcomp_var[index].second_op, !Sign, 0, neighbors, 0, level);
      break;
    case MAXIMIZE_OP:      
      create_neighborhood_for_compvar (gcomp_var[index].first_op, Sign, 0, neighbors, -2, level);
      break;
    case UMINUS_OP:
      /*aggiungere gli incr di sx e i decr di dx */
      create_neighborhood_for_compvar (gcomp_var[index].first_op, !Sign, 0, neighbors, 0, level);
      break;
    case VARIABLE_OP:
      if (start == -2) {
	if ( Sign )
	  insert_els_in_neighborhood( gcomp_var[index].increased_by, neighbors );
	else
	  insert_els_in_neighborhood( gcomp_var[index].decreased_by, neighbors );
      }
      else
	//neighbors e' null quando chiamo per solo print a video (opzione -i 141)
	if (neighbors != NULL) {
	  if (Sign) {
	    for (el = gcomp_var[index].increased_by; el; el = el->next) {
	      SET_BIT (neighb_actions, el->item);
	    }
	  }
	  else
	    for (el = gcomp_var[index].decreased_by; el; el = el->next) {
	      SET_BIT (neighb_actions, el->item);
	    }
	}
      break;
      //non ci sono vicini per i numeri fissi
    case FIX_NUMBER:
      break;

    default:
      printf ("\n\nshouldnt get this op %d  here\n\n", gcomp_var[index].operator);
    }
  if (start == 1 && level != -1)
    {
      for (i = 0; i < gnum_ef_conn; i++)
	{
	  if (gef_conn[i].level < 0)
	    {
	      if (DEBUG2)
		printf("\nWarning: trying to insert a non reachable action in neighbothood!");
	    
	      continue;
	    }

	  // faccio passare il bit array, provando ad applicare l'azioni con bit a 1
	  if (GET_BIT (neighb_actions, i))
	    {
	      //se migliorano il confronto (increm se >,>=; decrem se <,<=)
	      //allora inserisco in neighbors->A[ ->num_A++] (analogamente a insert_els_in_neighborhood)
#ifdef __TEST__
	      if (DEBUG1)
		{
		  printf ("\n Esamino %d ", i);
		  print_op_name (i);
		}
#endif
	      /**
		 copia i valori su output
		 **
		 copies the values on output
	      **/
	      memcpy (out_vect, in_vect, gnum_comp_var * sizeof (int));
	      val_before =
		out_vect[gcomp_var[index].first_op] - out_vect[gcomp_var[index].second_op];
	      /**
		 per tutti gli eff numerici di azione
		 **
		 for every numerical effects of action
	      **/
	      for (j = 0; j < gef_conn[i].num_A; j++)
		if (gef_conn[i].A[j] < 0)
		  try_num_eff_in_level (-gef_conn[i].A[j], in_vect, out_vect,TRUE);

	      val_after = out_vect[gcomp_var[index].first_op] - out_vect[gcomp_var[index].second_op];

	      diff = val_after - val_before;
	      if (((gcomp_var[index].operator== LESS_THAN_OP) || (gcomp_var[index].operator== LESS_THAN_OR_EQUAL_OP))
		  && (diff < -MAX_APPROX))
		{
		  neighbors->A[neighbors->num_A++] = i;
		}
	      if (((gcomp_var[index].operator== GREATER_THAN_OP) || (gcomp_var[index].operator== GREATER_OR_EQUAL_OP))
		  && (diff > MAX_APPROX))
		{
		  neighbors->A[neighbors->num_A++] = i;
	
#ifdef __TEST__
		  if (DEBUG1)
		    {
		      printf ("\n Aggiungo %d", i);
		      print_op_name (i);
		    }
#endif
		}
	    }
	}

#ifdef __TEST__

      if (neighbors && neighbors->num_A <= 0 && start == 1 && level != -1)
	printf ("\n Warning: Num elem for numeric neigh of fact %d is <=0", index);

      printf ("\n\nXXX Vicinato di \n");
      print_cvar_tree (index, level);
      for (i = 0; i < neighbors->num_A; i++)
	{
	  printf ("\n");
	  print_op_name (neighbors->A[i]);
	}
#endif
    }
}



/** 
 * Name: create_remotion_neighborhood_for_compvar
 * Scopo:
 * Tipo: void
 * Input: int fct_pos
 *        int level
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: create_remotion_neighborhood_for_compvar
* Objective:
* Type: void
* Input: int fct_pos
*        int level
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
void create_remotion_neighborhood_for_compvar (int fct_pos, int level)
{
  int indlevel, var;
  float next_value;
  neighb temp_act;

  temp_act.fact_treated = fct_pos;
  temp_act.constraint_type = C_T_REMOVE_ACTION;
  temp_act.unsup_fact = fct_pos;

  /**
     se non è un goal
     **
     if it is not a goal
  **/
  if(level < GpG.curr_plan_length) {
    temp_act.act_pos = vectlevel[level]->action.position;
    temp_act.act_level = level;
    insert_element_in_neighb (&temp_act);
  }

  if (!GpG.numeric_neighbors_in_down_levels)
    return;

  var = gcomp_var[fct_pos].first_op;

  for (indlevel = get_prev(level); indlevel >= 0; indlevel = get_prev(indlevel)) {

    next_value = vectlevel[indlevel + 1]->numeric->values[var];

    switch (gcomp_var[fct_pos].operator) 
      {
      case EQUAL_OP:
	printf("\n\nGeneration of neighborhood for EQUAL_OP not yet implemented\n\n");
	exit (1);
	return;
      case GREATER_THAN_OP:
      case GREATER_OR_EQUAL_OP: 
	if (vectlevel[indlevel]->numeric->values[var] > next_value) {
	  temp_act.act_pos = vectlevel[indlevel]->action.position;
	  temp_act.act_level = indlevel;
	  insert_element_in_neighb (&temp_act);
	}
	break; 
      case LESS_THAN_OP:
      case LESS_THAN_OR_EQUAL_OP:
	if (vectlevel[indlevel]->numeric->values[var] < next_value) {
	  temp_act.act_pos = vectlevel[indlevel]->action.position;
	  temp_act.act_level = indlevel;
	  insert_element_in_neighb (&temp_act);
	}
	break;
      default:
	return;
      } 
  }
}



/*********************************************
           INCONSISTENCE SELECTION
**********************************************/


/** 
 * Name: choose_min_cost_unsup_fact
 * Scopo:
 * Tipo: int
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_min_cost_unsup_fact
* Objective:
* Type: int
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int choose_min_cost_unsup_fact ()
{
  int i, j, best = 0, min_level = 0;
  float min = 100000.0, min_constr = 100000.0, curr_min_constr = 100000.0, tot;
  float endtime = 0.0, timed, min_slack;
  dg_inform_list loc_dg_cost;
  int min_step, best_in_tabu;

  if (GpG.inc_choice_type == MIN_LEVEL_INC
      || GpG.inc_choice_type == MIN_LEVEL_COST_INC
      || GpG.inc_choice_type == MIN_LEVEL_CONSTR_INC|| GpG.inc_choice_type == MIN_LEVEL_MIN_CONSTR_INC || GpG.inc_choice_type ==MIN_LEVEL_MAX_COST || GpG.inc_choice_type == MIN_LEVEL_MIN_ADDITIVE_ACTIONS || GpG.inc_choice_type == MIN_LEVEL_MIN_TIMED_INC)
    min_level = 100000;
  else if (GpG.inc_choice_type == MAX_LEVEL_INC)
    min_level = 0;
  if (GpG.inc_choice_type == MIN_COST_INC
      || GpG.inc_choice_type == MIN_LEVEL_COST_INC || GpG.inc_choice_type == MIN_LEVEL_MIN_ADDITIVE_ACTIONS)
    min = 100000.0;
  if (GpG.inc_choice_type == MAX_COST_INC || GpG.inc_choice_type ==MIN_LEVEL_MAX_COST)
    min = 0.0;

  min_step =MAXINT;
  min_slack = MAXFLOAT;

  best = best_in_tabu = -1;

  //  for(i=0; i <  GpG.num_false_fa; i++) 
  for (i = GpG.num_false_fa - 1; i >= 0; i--)
    {
      if (GpG.inc_choice_type == MIN_LEVEL_INC)
	{
	  if ( min_level > *unsup_fact[i]->level || 
	       (min_level == *unsup_fact[i]->level && MY_RANDOM % 2) )
	    {
	      if (!is_fct_in_tabu(unsup_fact[i]->fact) )
		{
		if (DEBUG2)
		  printf("\nEsamined Inc: %d", unsup_fact[i]->fact);
		  min_level = *unsup_fact[i]->level;
		  best = i;
		}
	      else
		if (DEBUG2)
		  printf("\nSkip Inc: %d is in tabu - step %d - numtry %d - numR %d", unsup_fact[i]->fact, gft_conn[unsup_fact[i]->fact].step, GpG.count_num_try, gft_conn[unsup_fact[i]->fact].numR);
	    }
	  if (is_fct_in_tabu(unsup_fact[i]->fact) &&
	      min_step > gft_conn[unsup_fact[i]->fact].step)
	    {
	      min_step = gft_conn[unsup_fact[i]->fact].step;
	      best_in_tabu = i;
	    }
	}   
      else if (GpG.inc_choice_type == MIN_LEVEL_COST_INC)
	{
	  if (min_level > *unsup_fact[i]->level)
	    {
	      min_level = *unsup_fact[i]->level;
	      best = i;
	      get_dg_fact_cost (unsup_fact[i]->fact,
				*unsup_fact[i]->level, &loc_dg_cost);
           if(GpG.verify_inc_choice)
	              min = loc_dg_cost->num_actions;
	   else
	      min = loc_dg_cost->totcost;
	    }
	  else if (min_level == *unsup_fact[i]->level)
	    {
	      get_dg_fact_cost (unsup_fact[i]->fact,
				*unsup_fact[i]->level, &loc_dg_cost);
	     if(GpG.verify_inc_choice) 
	           tot= loc_dg_cost->num_actions;
	     else
	   	   tot= loc_dg_cost->totcost;
	      if (min > tot
		  || (min == tot && MY_RANDOM & FIRST_1))
		{
		  min = tot;
		  best = i;
		}
	    }
	}  
      else if (GpG.inc_choice_type == MIN_LEVEL_MIN_ADDITIVE_ACTIONS)
	{
	  if (min_level > *unsup_fact[i]->level)
	    {
	      min_level = *unsup_fact[i]->level;
	      best = i;
	      min = (float) gft_conn[unsup_fact[i]->fact].num_A;
	    }
	  else if (min_level == *unsup_fact[i]->level)
	    {
	           tot=  (float) gft_conn[unsup_fact[i]->fact].num_A;
	      if (min > tot
		  || (min == tot && MY_RANDOM & FIRST_1))
		{
		  min = tot;
		  best = i;
		}
	    }
	}
      else if (GpG.inc_choice_type == MIN_LEVEL_MAX_COST)
	{
	  if (min_level > *unsup_fact[i]->level)
	    {
	      min_level = *unsup_fact[i]->level;
	      best = i;
	      get_dg_fact_cost (unsup_fact[i]->fact,
				*unsup_fact[i]->level, &loc_dg_cost);
           if(GpG.verify_inc_choice)
	              min = loc_dg_cost->num_actions;
	   else
	      min = loc_dg_cost->totcost;
	    }
	  else if (min_level == *unsup_fact[i]->level)
	    {
	      get_dg_fact_cost (unsup_fact[i]->fact,
				*unsup_fact[i]->level, &loc_dg_cost);
	     if(GpG.verify_inc_choice) 
	           tot= loc_dg_cost->num_actions;
	     else
	   	   tot= loc_dg_cost->totcost;

	      if (min < tot
		  || (min == tot && MY_RANDOM & FIRST_1))
		{
		  min = tot;
		  best = i;
		}
	    }
	}
      else if (GpG.inc_choice_type == MIN_LEVEL_CONSTR_INC)
	{
	  if (min_level > *unsup_fact[i]->level)
	    {
	      min_level = *unsup_fact[i]->level;
	      best = i;

	      min_constr =
		compute_constr_fact (unsup_fact[i]->fact, unsup_fact[i]->fact,
				     *unsup_fact[i]->level, 1,*unsup_fact[i]->level, &min, &endtime);
	      // /***
	      get_dg_fact_cost (unsup_fact[i]->fact,
				*unsup_fact[i]->level, &loc_dg_cost);
              if(GpG.verify_inc_choice)
		min = loc_dg_cost->num_actions;
	      else
		min = loc_dg_cost->totcost;
	      // ***/
	    }
	  else if (min_level == *unsup_fact[i]->level)
	    {
	      curr_min_constr =
		compute_constr_fact (unsup_fact[i]->fact, unsup_fact[i]->fact,
				     *unsup_fact[i]->level, 1,*unsup_fact[i]->level,&tot, &endtime);
	      // /***
	      get_dg_fact_cost (unsup_fact[i]->fact,
				*unsup_fact[i]->level, &loc_dg_cost);
             if(GpG.verify_inc_choice) 
                tot= loc_dg_cost->num_actions;
             else
                tot= loc_dg_cost->totcost;
	     // **/
	      if (min_constr < curr_min_constr
		  || (min_constr == curr_min_constr
		      && (min > tot
			  || (min == tot
			      && (MY_RANDOM % 2)))))
		{
		  min = tot;
		  best = i;
		  min_constr = curr_min_constr;
		}
	    }
	}
      else if (GpG.inc_choice_type == MIN_LEVEL_MIN_TIMED_INC)
	{
	  if (min_level > *unsup_fact[i]->level)
	    {
	      min_level = *unsup_fact[i]->level;
	      best = i;
	      
	      timed = MAXFLOAT;
	      
	      /**
		 Calcoliamo il timed fact piu' restrittivo per l'inconsistenza in esame
		 **
		 Calculating the time fact more restrictive for the inconsistence in exam
	      **/
	      for (j = 0; j < gft_conn[unsup_fact[i]->fact].num_tmd_facts_array ; j++) 
		{
		  if (gtimed_fct_vect[TIMED_IDX(gft_conn[unsup_fact[i]->fact].tmd_facts_array[j])]->end_time < timed)
		    timed = gtimed_fct_vect[TIMED_IDX(gft_conn[unsup_fact[i]->fact].tmd_facts_array[j])]->end_time;
		}
	      endtime = 0.0;
	      /**
		 Calcoliamo quando l'inconsistenza puo' venire supportata 
		 **
		 Calculating when the inconsistence may be supported
	      **/
	      min_constr =compute_constr_fact (unsup_fact[i]->fact, unsup_fact[i]->fact,
				               *unsup_fact[i]->level, 1, *unsup_fact[i]->level, &min, &endtime);
	      /**
		 Calcoliamo lo slack dell'inconsistenza in esame
		 **
		 Calculating the slack of the inconsistence in exam
	      **/
	      min_slack = timed - endtime;
	      
	      if (DEBUG1)
		printf("\n[%d] %s lev:%d timed: %.2f endtime: %.2f slack:%.2f better than noone", unsup_fact[i]->fact, print_ft_name_string(unsup_fact[i]->fact, temp_name), *unsup_fact[i]->level, timed, endtime, timed - endtime);
	    }
	  else if (min_level == *unsup_fact[i]->level)
	    {
	      timed = MAXFLOAT;
	      /**
		 Calcoliamo il timed fact piu' restrittivo per l'inconsistenza in esame
		 **
		 Calculating the time fact more restrictive for the inconsistence in exam
	      **/
	      for (j = 0; j < gft_conn[unsup_fact[i]->fact].num_tmd_facts_array ; j++)
		{
		  if (gtimed_fct_vect[TIMED_IDX(gft_conn[unsup_fact[i]->fact].tmd_facts_array[j])]->end_time < timed)
		    timed = gtimed_fct_vect[TIMED_IDX(gft_conn[unsup_fact[i]->fact].tmd_facts_array[j])]->end_time;
		}
	      endtime = 0.0;
	      /**
		 Calcoliamo quando l'inconsistenza puo' venire supportata 
		 **
		 Calculating when the inconsistence may be supported
	      **/
	      curr_min_constr =	compute_constr_fact (unsup_fact[i]->fact, unsup_fact[i]->fact,
		                                     *unsup_fact[i]->level, 1, *unsup_fact[i]->level,&tot, &endtime);
	      /**
		 Calcoliamo lo slack dell'inconsistenza in esame
		 **
		 Calculating the slack of the inconsistence in exam
	      **/
	     if ( (timed - endtime) < min_slack || ((timed - endtime) == min_slack && MY_RANDOM % 2))
	       {
		 if (DEBUG1)
		   {
		     printf("\n[%d] %s lev:%d timed: %.2f endtime: %.2f slack:%.2f better than", unsup_fact[i]->fact, print_ft_name_string(unsup_fact[i]->fact, temp_name), *unsup_fact[i]->level, timed, endtime, timed - endtime);
		     printf("[%d] %s lev:%d slack:%.2f", unsup_fact[best]->fact, print_ft_name_string( unsup_fact[best]->fact,temp_name), min_level, min_slack);
		   }
		 min_level = *unsup_fact[i]->level;
		 min_slack = timed - endtime;
		 best = i;
	       }
	    }
	}
      else if (GpG.inc_choice_type == MIN_LEVEL_MIN_CONSTR_INC)
	{
	  
	  if (min_level > *unsup_fact[i]->level)
	    {
	      min_level = *unsup_fact[i]->level;
	      best = i;
	      min_constr =
		compute_constr_fact (unsup_fact[i]->fact, unsup_fact[i]->fact,
				     *unsup_fact[i]->level , 1, *unsup_fact[i]->level, &min, &endtime);
	      /**
	      get_dg_fact_cost (unsup_fact[i]->fact,
				*unsup_fact[i]->level , &loc_dg_cost);

              if(GpG.verify_inc_choice)
	          min = loc_dg_cost->num_actions;
              else
	          min = loc_dg_cost->totcost;	    
	    
	      min = loc_dg_cost->totcost;
	      **/

	      if(DEBUG5)
		{
		printf("\n\n BEST i_choice %d level %d cost %f constr %f  fact %d ",i,   *unsup_fact[i]->level, min,   min_constr,  unsup_fact[i]->fact);
		print_ft_name( unsup_fact[i]->fact);
		}
	    }
	  else if (min_level == *unsup_fact[i]->level)
	    {
	      curr_min_constr =
		compute_constr_fact (unsup_fact[i]->fact, unsup_fact[i]->fact,
				     *unsup_fact[i]->level , 1, *unsup_fact[i]->level, &tot, &endtime);
	      /**
	      get_dg_fact_cost (unsup_fact[i]->fact,
				*unsup_fact[i]->level , &loc_dg_cost );
	     
	     if(GpG.verify_inc_choice)
	         tot= loc_dg_cost->num_actions;
	     else
	          tot= loc_dg_cost->totcost;
	      **/
		    if (min_constr > curr_min_constr
		  || (min_constr == curr_min_constr
		      && (min > tot
			  || (min == tot
			      && (MY_RANDOM % 2)))))
		{
		  min = tot;
		  best = i;
		  min_constr = curr_min_constr;

		  if(DEBUG5)
		    {
		      printf("\n\n BEST i_choice %d level %d cost %f constr %f  fact %d ",i,   *unsup_fact[i]->level, min,   min_constr,  unsup_fact[i]->fact);
		      print_ft_name( unsup_fact[i]->fact);
		    }
		}
		    else
		      if(DEBUG5)
			{
			  printf("\n\n NO  Best i_choice %d level %d cost %f constr %f  fact %d ",i,   *unsup_fact[i]->level, tot,  curr_min_constr,  unsup_fact[i]->fact);
			  print_ft_name( unsup_fact[i]->fact);
			}
	    }
	}
      else if (GpG.inc_choice_type == MAX_LEVEL_INC)
	{

	  if (min_level < *unsup_fact[i]->level)
	    {
	      min_level = *unsup_fact[i]->level;
	      best = i;
	    }
	}
      else if (GpG.inc_choice_type == MIN_COST_INC)
	{

	  get_dg_fact_cost (unsup_fact[i]->fact, *unsup_fact[i]->level,
			    &loc_dg_cost);
         if(GpG.verify_inc_choice)
               tot= loc_dg_cost->num_actions;
         else
              tot= loc_dg_cost->totcost;
	  if (min > tot
	      || (min == tot && MY_RANDOM % 2))
	    {
	      min = tot;
	      best = i;
	    }
	}
      else if (GpG.inc_choice_type == MAX_COST_INC)
	{
	  get_dg_fact_cost (unsup_fact[i]->fact, *unsup_fact[i]->level,
			    &loc_dg_cost);
             if(GpG.verify_inc_choice)
	                   tot= loc_dg_cost->num_actions;
             else
	                tot= loc_dg_cost->totcost;

	     if (min < tot || (MY_RANDOM % 2))
	    {
	      min = tot;
	      best = i;
	    }
	}
      // printf("\n Fatto: %d Costo: %2.10f",unsup_fact[i]->fact,loc_dg_cost->totcost);
    }
  if (best >= 0)
    {
      ins_fct_in_tabu(unsup_fact[best]->fact);
      return best;
    }
  else 
    {
      ins_fct_in_tabu(unsup_fact[best_in_tabu]->fact);

      return best_in_tabu;
    }
}







/** 
 * Name: nonuniform_random
 * Scopo:
 * Tipo: int
 * Input: int num_max
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: nonuniform_random
* Objective:
* Type: int
* Input: int num_max
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int nonuniform_random(int num_max)
{
  int i;
  int choice_num = num_max;
  
  for(i = num_max - 1; i >= 0; i--)
  {  
       if (MY_RANDOM % 2) 
	 choice_num  = i;
  }
  return choice_num;
}


/** OK 28-07-04
 * Name: choose_random_inconsistence
 * Scopo:
 * Tipo: constraints_list
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_random_inconsistence
* Objective:
* Type: constraints_list
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
constraints_list choose_random_inconsistence()
{
  /* Questa funzione seleziona una inconsistenza in modo casuale da uno dei
     vettori contenenti ciascuno un tipo diverso di inconsistenza.
     La probabilità di selezione di uno dei tipi viene fatta variare  
     attraverso l'uso di pesi individuati da tali variabili: 
     GpG.k_weight_false_fa
     GpG.k_weight_false_num_fa
     GpG.k_weight_false_act	 
     GpG.k_weight_false_tmd_fa		*/
  
  int tot,choice;
  int unsup_pos;
  
  tot = (int)(GpG.num_false_fa*GpG.k_weight_false_fa)+(GpG.num_false_num_fa*GpG.k_weight_false_num_fa)+(GpG.num_false_act*GpG.k_weight_false_act)+(GpG.num_false_tmd_fa*GpG.k_weight_false_tmd_fa);
  
  if (GpG.nonuniform_random_incosistence_test) 
    choice = nonuniform_random (tot);
  else 
    choice = MY_RANDOM % tot;
  
  /**
     Caso in cui sia stata selezionata una inconsistenza logica
     **
     If a logical inconsistence is selected
  **/
  if (choice<GpG.num_false_fa*GpG.k_weight_false_fa)
    {
      unsup_pos=(int)(choice/GpG.k_weight_false_fa);
      return unsup_fact[unsup_pos];
    }
  else
    /**
       Caso in cui sia stata selezionata una inconsistenza numerica
       **
       If a numerical inconsistence is selected
    **/
    if ((choice>=GpG.num_false_fa*GpG.k_weight_false_fa)&&
	(choice<(GpG.num_false_fa*GpG.k_weight_false_fa+GpG.num_false_num_fa*GpG.k_weight_false_num_fa)))
      {
	unsup_pos=(int)((choice-(GpG.num_false_fa*GpG.k_weight_false_fa))/GpG.k_weight_false_num_fa);
        return unsup_num_fact[unsup_pos];
      }
    else
      /**
	 Caso in cui sia stata selezionata una inconsistenza azione
	 **
	 If an action inconsistence is selected
      **/
      if ((choice>=(GpG.num_false_fa*GpG.k_weight_false_fa+GpG.num_false_num_fa*GpG.k_weight_false_num_fa))&&
	   (choice<(GpG.num_false_fa*GpG.k_weight_false_fa+GpG.num_false_num_fa*GpG.k_weight_false_num_fa+GpG.num_false_act*GpG.k_weight_false_act)))
	{
	  unsup_pos=(int)((choice-(GpG.num_false_fa*GpG.k_weight_false_fa+GpG.num_false_num_fa*GpG.k_weight_false_num_fa))/GpG.k_weight_false_act);
	  return treated_c_l[unsup_pos];
	}
      /**
	 Caso in cui sia stata selezionata una inconsistenza temporale
	 **
	 If a temporal inconsistence is selected
      **/
      if (choice>=(GpG.num_false_fa*GpG.k_weight_false_fa+GpG.num_false_num_fa*GpG.k_weight_false_num_fa+GpG.num_false_act*GpG.k_weight_false_act))
	{
	  unsup_pos=(int)((choice-(GpG.num_false_fa*GpG.k_weight_false_fa+GpG.num_false_num_fa*GpG.k_weight_false_num_fa+GpG.num_false_act*GpG.k_weight_false_act))/GpG.k_weight_false_tmd_fa);
	  return unsup_tmd_facts[unsup_pos];
	}
      return NULL;
}


/** OK 28-07-04
 * Name: choose_min_level_inconsistence
 * Scopo: Seleziona una inconsistenza scegliendone una presente al livello piu basso 
 * Tipo: constraints_list
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_min_level_inconsistence
* Objective:
* Type: constraints_list
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
constraints_list choose_min_level_inconsistence()
{
  static constraints_list *same_level_inconsistence=NULL;
  int i,best;
  int num_same_level=0;
  int min_level=100000;
  static int num_max_vector_inc=MAX_VECTOR_INC;/**
						  Tiene il numero max di elementi dell'array
						  **
						  maximum number of array's elements
					       **/
  
  //Tale array di puntatori viene allocato solo la prima volta.Per mezzo
  //dell'operatore static viene conservato in memoria anche una volta
  //usciti dalla procedura
  if (same_level_inconsistence==NULL)
    if (!(same_level_inconsistence = (constraints_list *)calloc(MAX_VECTOR_INC,sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY); //out of memory
  
  //Vengono scansionate le liste contenenti i vari tipi di inconsistenze
  // e viene creata una lista: same_level_inconsistence[] nella quale sono
  //inserite le inconsistenze che si trovano al livello piu basso.
  
  /**
     Scansione delle lista delle inconsistenze logiche
     **
     Scanning of the logical inconsistence list
  **/
  for (i=0;i<GpG.num_false_fa;i++)
    {
	if (min_level > *unsup_fact[i]->level)
	  {
	    min_level=*unsup_fact[i]->level;
	    num_same_level=0;
	    same_level_inconsistence[num_same_level++] = unsup_fact[i];
	    if(DEBUG5)
	      {
		printf("\nINTIT UNSUP FACT LIST \nLevel %d Unsup Fact %d ",*unsup_fact[i]->level, unsup_fact[i]->fact );
		print_ft_name(unsup_fact[i]->fact);
	      }
	  }
	else 
	  if (min_level == *unsup_fact[i]->level)
	    {
	      same_level_inconsistence[num_same_level++] = unsup_fact[i];
	      if(DEBUG5)
	      {
		printf("\nLevel %d Unsup Fact %d ",*unsup_fact[i]->level, unsup_fact[i]->fact );
		print_ft_name(unsup_fact[i]->fact);
	      }
	      /**
		 Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
		 **
		 If the maximum limit of the array, i reallocate adding space
	      **/
	      if (num_same_level>=num_max_vector_inc){
		num_max_vector_inc+=MAX_VECTOR_INC;
		if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	    }
    }
  /**
     Scansione delle lista delle inconsistenze numeriche
     **
     Scanning of the numerical inconsitence list
  **/
  for (i=0;i<GpG.num_false_num_fa;i++)
      {
	if (min_level > *unsup_num_fact[i]->level)
	  {
	    min_level=*unsup_num_fact[i]->level;
	    num_same_level=0;
	    same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
	    if(DEBUG5)
	      {
		printf("\nINTIT UNSUP NUM FACT LIST \nLevel %d Unsup Num Fact %d ",*unsup_num_fact[i]->level, unsup_num_fact[i]->fact );
		print_ft_name(unsup_num_fact[i]->fact);
	      }
	  }
	else 
	  if (min_level == *unsup_num_fact[i]->level)
	    {
	      same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
	      
	       if(DEBUG5)
	      {
		printf("\nLevel %d Unsup Num Fact %d ",*unsup_num_fact[i]->level, unsup_num_fact[i]->fact );
		print_ft_name(unsup_num_fact[i]->fact);
	      }
	      /**
		 Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
		 **
		 If the maximum limit of the array, i reallocate adding space
	      **/
	      if (num_same_level>=num_max_vector_inc)
		{
		  num_max_vector_inc+=MAX_VECTOR_INC;
		  if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
		}
	    }
	}
    /**
       Scansione delle lista delle inconsistenze azioni
       **
       Scanning of the actions inconsitence list
    **/
    for (i=0;i<GpG.num_false_act;i++)
      {
	if (min_level > *treated_c_l[i]->level)
	  {
	    min_level=*treated_c_l[i]->level;
	    num_same_level=0;
	    same_level_inconsistence[num_same_level++]=treated_c_l[i];

	    if(DEBUG5)
	      {
		printf("\nINTIT TREATED FACT LIST \nLevel %d Treated Fact %d ",*treated_c_l[i]->level, treated_c_l[i]->fact );
		print_ft_name(treated_c_l[i]->fact);
	      }
	  }
	else 
	  if (min_level == *treated_c_l[i]->level)
	    {
	      same_level_inconsistence[num_same_level++]=treated_c_l[i];
	      
	    if(DEBUG5)
	      {
		printf("\nLevel %d Treated Fact %d ",*treated_c_l[i]->level, treated_c_l[i]->fact );
		print_ft_name(treated_c_l[i]->fact);
	      }
	      /**
		 Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
		 **
		 If the maximum limit of the array, i reallocate adding space
	      **/
	      if (num_same_level>=num_max_vector_inc)
		{
		  num_max_vector_inc+=MAX_VECTOR_INC;
		  if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
		}
	    }
      }
    /**
       Scansione delle lista delle inconsistenze azioni
       **
       Scanning of the actions inconsitence list
    **/
    for (i=0;i<GpG.num_false_tmd_fa;i++)
      {
	if (min_level > *unsup_tmd_facts[i]->level)
	  {
	    min_level=*unsup_tmd_facts[i]->level;
	    num_same_level=0;
	    same_level_inconsistence[num_same_level++]=unsup_tmd_facts[i];

	    if(DEBUG5)
	      {
		printf("\nINTIT TREATED FACT LIST \nLevel %d Treated Fact %d ",*unsup_tmd_facts[i]->level, unsup_tmd_facts[i]->fact );
		print_ft_name(unsup_tmd_facts[i]->fact);
	      }
	  }
	else 
	  if (min_level == *unsup_tmd_facts[i]->level)
	    {
	      same_level_inconsistence[num_same_level++]=unsup_tmd_facts[i];
	      
	    if(DEBUG5)
	      {
		printf("\nLevel %d Treated Fact %d ",*unsup_tmd_facts[i]->level, unsup_tmd_facts[i]->fact );
		print_ft_name(unsup_tmd_facts[i]->fact);
	      }
	      /**
		 Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
		 **
		 If the maximum limit of the array, i reallocate adding space
	      **/
	      if (num_same_level>=num_max_vector_inc)
		{
		  num_max_vector_inc+=MAX_VECTOR_INC;
		  if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
		}
	    }
      }
    /**
       Una volta trovate le inconsistenze presenti al livello più basso, casualmente se ne seleziona una
       **
       When the lower level inconsistence have been found, I randomly select one
    **/
  if (GpG.nonuniform_random_incosistence_test) 
    best = nonuniform_random (num_same_level);
  else 
    best = MY_RANDOM % num_same_level;
  
  return (same_level_inconsistence[best]);
}


/** OK 28-07-04
 * Name: choose_min_cost_inconsistence
 * Scopo: Questa funzione seleziona una inconsistenza scegliendone una casuale tra quelle che possiedono  il costo più basso
 * Tipo: constraints_list
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_min_cost_inconsistence
* Objective:
* Type: constraints_list
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
constraints_list choose_min_cost_inconsistence()
{
  static int num_max_vector_inc=MAX_VECTOR_INC;/**
						  Tiene il numero max di elementi dell'array
						  **
						  maximum number of array's elements
					       **/
  static constraints_list *same_cost_inconsistence=NULL;
  
  int i,best;
  int num_same_cost=0;
  float min_cost=100000.0;
  float cost;
  
  
  dg_inform_list loc_dg_cost;

  dg_num_inform_list loc_dg_num_cost;


  //Tale array di puntatori viene allocato solo la prima volta.Per mezzo
  //dell'operatore static viene conservata in memoria anche una volta
  //usciti dalla procedura
  if (same_cost_inconsistence==NULL)
    if (!(same_cost_inconsistence = (constraints_list *)calloc(MAX_VECTOR_INC,sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);; //out of memory
  
  //Vengono scansionati i vettori delle incosistenze logiche e numeriche
  // e viene creata una lista: same_cost_inconsistence[] nella quale sono
  //inserite le inconsistenze che possiedono un costo piu basso. 
  //A tale vettore verranno poi aggiunti i treateds
  
  /**
     Scansione delle lista delle inconsistenze logiche
     **
     Scanning of the logical inconsistence list
  **/
  for (i=0;i<GpG.num_false_fa;i++)
    {
      /**
	 Calcolo del costo
	 **
	 Calculating the cost
      **/
      get_dg_fact_cost (unsup_fact[i]->fact,*unsup_fact[i]->level,&loc_dg_cost);
      
      if(GpG.verify_inc_choice)
	cost= loc_dg_cost->num_actions;
      else
	cost= loc_dg_cost->totcost;
      /**
	 Confronto con il valore minimo
	 **
	 Comparing with the minimum value
      **/
      if (min_cost > cost){
	min_cost=cost;
	num_same_cost=0;
	same_cost_inconsistence[num_same_cost++] = unsup_fact[i];
      }
      else if (min_cost == cost){
	same_cost_inconsistence[num_same_cost++] = unsup_fact[i];
	
         /**
	    Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	    **
	    If the maximum limit of the array, i reallocate adding space
	 **/
	if (num_same_cost>=num_max_vector_inc)
	  {
	    num_max_vector_inc+=MAX_VECTOR_INC;
	    if (!(same_cost_inconsistence = (constraints_list *)realloc(same_cost_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	  }
      }
    }
  /**
     Scansione delle lista delle inconsistenze numeriche
     **
     Scanning of the numerical inconsitence list
  **/
  for (i=0;i<GpG.num_false_num_fa;i++)
    {
      /**
	 Calcolo del costo
	 **
	 Calculating the cost
      **/
      get_dg_num_fact_cost (unsup_num_fact[i]->fact,*unsup_num_fact[i]->level, &loc_dg_num_cost);
      
      if(GpG.verify_inc_choice)
	cost= loc_dg_num_cost->num_actions;
      else
	cost= loc_dg_num_cost->totcost;
      
      /**
	 Confronto con il valore minimo
	 **
	 Comparing with the minimum value
      **/
      if (min_cost > cost)
	{
	  min_cost=cost;
	  num_same_cost=0;
	  same_cost_inconsistence[num_same_cost++] = unsup_num_fact[i];
	}
      else if (min_cost == cost)
	{
	  same_cost_inconsistence[num_same_cost++] = unsup_num_fact[i];
	  
         /**
	    Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	    **
	    If the maximum limit of the array, i reallocate adding space
	 **/
	  if (num_same_cost>=num_max_vector_inc){
            num_max_vector_inc+=MAX_VECTOR_INC;
	    if (!(same_cost_inconsistence = (constraints_list *)realloc(same_cost_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	  }
	}
    }
  /** 
      Aggiungo a tale lista il vettore dei treateds
      **
      Adding the array of the treateds
  **/
  for (i=0;i<GpG.num_false_act;i++)
    {
      same_cost_inconsistence[num_same_cost++]=treated_c_l[i];
      /**
	 Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	 **
	 If the maximum limit of the array, i reallocate adding space
      **/
      if (num_same_cost>=num_max_vector_inc)
	{
	  num_max_vector_inc+=MAX_VECTOR_INC;
	  if (!(same_cost_inconsistence = (constraints_list *)realloc(same_cost_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	}
    }
  
  //DA aggiungere le inconsistenze temporali

  
  /**
     Seleziono casualmente un'inconsistenza presente in tale vettore
     **
     Randomly selection of an inconsistence
  **/
  if (GpG.nonuniform_random_incosistence_test) 
    best = nonuniform_random (num_same_cost);
  else 
    best = MY_RANDOM % num_same_cost;
  
  return (same_cost_inconsistence[best]);
}


/** OK 28-07-04
 * Name: choose_max_cost_inconsistence
 * Scopo: Questa funzione seleziona una inconsistenza scegliendone una casuale tra quelle che possiedono  il costo piu' alto
 * Tipo: constraints_list
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_max_cost_inconsistence
* Objective:
* Type: constraints_list
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
constraints_list choose_max_cost_inconsistence()
{
  static constraints_list *same_cost_inconsistence=NULL;
  static int num_max_vector_inc=MAX_VECTOR_INC;/**
						  Tiene il numero max di elementi dell'array
						  **
						  maximum number of array's elements
					       **/
  int i,best;
  int num_same_cost=0;
  float max_cost=0.0;
  float cost;
    
  dg_inform_list loc_dg_cost;

  dg_num_inform_list loc_dg_num_cost;
  
  //Tale array di puntatori viene allocato solo la prima volta.Per mezzo
  //dell'operatore static viene conservata in memoria anche una volta
  //usciti dalla procedura
  if (same_cost_inconsistence==NULL)
    if (!(same_cost_inconsistence = (constraints_list *)calloc(MAX_VECTOR_INC,sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY); //out of memory
  
  //Vengono scansionati i vettori delle incosistenze logiche e numeriche
  // e viene creata una lista: same_cost_inconsistence[] nella quale sono
  //inserite le inconsistenze che possiedono un costo piu alto. 
  //A tale vettore verranno poi aggiunti treateds presenti 
  
  /**
     Scansione delle lista delle inconsistenze logiche
     **
     Scanning of the logical inconsistence list
  **/
  for (i=0;i<GpG.num_false_fa;i++)
    {
      /**
	 Calcolo del costo
	 **
	 Calculating the cost
      **/
      get_dg_fact_cost (unsup_fact[i]->fact,*unsup_fact[i]->level,&loc_dg_cost);
      
      if(GpG.verify_inc_choice)
	cost= loc_dg_cost->num_actions;
      else
	cost= loc_dg_cost->totcost;
      /**
	 Confronto con il valore minimo
	 **
	 Comparing with the minimum value
      **/
      if (max_cost < cost)
	{
	  max_cost=cost;
	  num_same_cost=0;
	  same_cost_inconsistence[num_same_cost++] = unsup_fact[i];
	}
      else 
	if (max_cost == cost)
	  {
	    same_cost_inconsistence[num_same_cost++] = unsup_fact[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_cost>=num_max_vector_inc)
	      {
		num_max_vector_inc+=MAX_VECTOR_INC;
		if (!(same_cost_inconsistence = (constraints_list *)realloc(same_cost_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }// end for
  /**
     Scansione delle lista delle inconsistenze numeriche
     **
     Scanning of the numerical inconsitence list
  **/
  for (i=0;i<GpG.num_false_num_fa;i++)
    {
      /**
	 Calcolo del costo
	 **
	 Calculating the cost
      **/
      get_dg_num_fact_cost (unsup_num_fact[i]->fact,*unsup_num_fact[i]->level, &loc_dg_num_cost);
      if(GpG.verify_inc_choice)
	cost= loc_dg_num_cost->num_actions;
      else
	cost= loc_dg_num_cost->totcost;
      /**
	 Confronto con il valore minimo
	 **
	 Comparing with the minimum value
      **/
      if (max_cost < cost)
	{
	  max_cost=cost;
	  num_same_cost=0;
	  same_cost_inconsistence[num_same_cost++] = unsup_num_fact[i];
	}
      else 
	if (max_cost == cost)
	  {
	    same_cost_inconsistence[num_same_cost++] = unsup_num_fact[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_cost>=num_max_vector_inc)
	      {
		num_max_vector_inc+=MAX_VECTOR_INC;
		if (!(same_cost_inconsistence = (constraints_list *)realloc(same_cost_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }
  /** 
      Aggiungo a tale lista il vettore delle inconsistenze azioni
      **
      Adding the array of the actions inconsistence
  **/
  for (i=0;i<GpG.num_false_act;i++)
    {
      same_cost_inconsistence[num_same_cost++]=treated_c_l[i];
      /**
	 Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	 **
	 If the maximum limit of the array, i reallocate adding space
      **/
      if (num_same_cost>=num_max_vector_inc)
	{
	  num_max_vector_inc+=MAX_VECTOR_INC;
	  if (!(same_cost_inconsistence = (constraints_list *)realloc(same_cost_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	}
    }
  /**
     Seleziono casualmente un'inconsistenza presente in tale vettore
     **
     Randomly selection of an inconsistence
  **/
  if (GpG.nonuniform_random_incosistence_test) 
    best = nonuniform_random (num_same_cost);
  else 
    best = MY_RANDOM % num_same_cost;
  
  return (same_cost_inconsistence[best]);
}


/** OK 28-07-04
 * Name: choose_min_level_cost_inconsistence
 * Scopo: Questa funziona seleziona una inconsistenza scegliendone una presente al livello piu basso tra quelle meno costose
 * Tipo: constraints_list
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_min_level_cost_inconsistence
* Objective:
* Type: constraints_list
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
constraints_list choose_min_level_cost_inconsistence()
{
  static constraints_list *same_level_inconsistence=NULL;
  static constraints_list *same_level_same_cost_inconsistence=NULL;
  static int num_max_vector_same_level_inc=MAX_VECTOR_INC;/**
							     Tiene il numero max di elementi dell'array al livello minimo
							     **
							     maximum number of array's elements at the minimum level
							  **/
  static int num_max_vector_same_cost_inc=MAX_VECTOR_INC;/**
							    Tiene il numero max di elementi dell'array per il costo minimo
							    **
							    maximum number of array's elementsfor the minimum cost
							 **/
  int i,best;
  int num_same_level=0;
  int num_same_level_same_cost=0;
  int treated_flag;
  int min_level=100000;
  float min_cost=100000.0;
  float cost=0.0;
  
  dg_inform_list loc_dg_cost;

  dg_num_inform_list loc_dg_num_cost;

  //Tali array di puntatori vengono allocati solo la prima volta.Per mezzo
  //dell'operatore static vengono conservati in memoria anche una volta
  //usciti dalla procedura
  if (same_level_inconsistence==NULL)
    if (!(same_level_inconsistence = (constraints_list *)calloc(MAX_VECTOR_INC,sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY); //out of memory
  if (same_level_same_cost_inconsistence==NULL)
    if (!(same_level_same_cost_inconsistence = (constraints_list *)calloc(MAX_VECTOR_INC,sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
  
  //Vengono scansionate le tre liste contenenti i vari tipi di inconsistenze
  // e viene creata una lista: same_level_inconsistence[] nella quale sono
  //inserite le inconsistenze che si trovano al livello piu basso.
  
  /**
     Scansione delle lista delle inconsistenze logiche
     **
     Scanning of the logical inconsistence list
  **/
  for (i=0;i<GpG.num_false_fa;i++)
    {
      if (min_level > *unsup_fact[i]->level)
	{
	  min_level=*unsup_fact[i]->level;
	  num_same_level=0;
	  same_level_inconsistence[num_same_level++] = unsup_fact[i];
	}
      else 
	if (min_level == *unsup_fact[i]->level)
	  {
	    same_level_inconsistence[num_same_level++] = unsup_fact[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level>=num_max_vector_same_level_inc)
	      {
		num_max_vector_same_level_inc+=MAX_VECTOR_INC;
		if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_same_level_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }
  /**
     Scansione delle lista delle inconsistenze numeriche
     **
     Scanning of the numerical inconsitence list
  **/
  for (i=0;i<GpG.num_false_num_fa;i++)
    {
      if (min_level > *unsup_num_fact[i]->level)
	{
	  min_level=*unsup_num_fact[i]->level;
	  num_same_level=0;
	  same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
	}
      else 
	if (min_level == *unsup_num_fact[i]->level)
	  {
	    same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level>=num_max_vector_same_level_inc)
	      {
		num_max_vector_same_level_inc+=MAX_VECTOR_INC;
		if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_same_level_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }
  /**
     Scansione delle lista delle inconsistenze azioni
     **
     Scanning of the action inconsitence list
  **/
  for (i=0;i<GpG.num_false_act;i++)
    {
      if (min_level > *treated_c_l[i]->level)
	{
	  min_level=*treated_c_l[i]->level;
	  num_same_level=0;
	  same_level_inconsistence[num_same_level++]=treated_c_l[i];
	}
      else 
	if (min_level == *treated_c_l[i]->level)
	  {
	    same_level_inconsistence[num_same_level++]=treated_c_l[i];
	    
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level>=num_max_vector_same_level_inc)
	      {
		num_max_vector_same_level_inc+=MAX_VECTOR_INC;
		if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_same_level_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }
    /**
       Una volta trovate le inconsistenze presenti al livello più basso, casualmente si seleziona la meno costosa
       **
       When the lower level inconsistence have been found, I select the less expensive
    **/
  /**
     Azzero il flag della presenza di treateds
     **
     Setting to zero the flag of the presence of treateds
  **/
  treated_flag=0;
  /**
     Scansione delle lista delle inconsistenze che si trovano al livello piu basso
     **
     Scanning of the list of the inconsistences that are at le lower level
  **/
  for (i=0;i<num_same_level;i++)
    {
      if (same_level_inconsistence[i]->constraint_type == C_T_TREATED_CL){
	/**
	   Se si tratta di un treated, attivo il flag della presenza di treateds
	   **
	   if it is a treated, the flag of presence is activated
	**/
	treated_flag=1;
	continue;
      }
      else
	{
	  /**
	     Altrimenti si tratta di un fatto, quindi ne valuto il costo
	     **
	     else it is a fact, then the cost is valuated
	  **/
	  /**
	     Calcolo del costo
	     **
	     Calculating the cost
	  **/
	if (same_level_inconsistence[i]->constraint_type ==C_T_UNSUP_FACT) 
	  {
	  get_dg_fact_cost (same_level_inconsistence[i]->fact,
			    *same_level_inconsistence[i]->level,&loc_dg_cost);
	
	  if(GpG.verify_inc_choice)
	    cost= loc_dg_cost->num_actions;
	  else
	    cost= loc_dg_cost->totcost;
	  }
	if (same_level_inconsistence[i]->constraint_type ==C_T_UNSUP_NUM_FACT) 
	  {
	    get_dg_num_fact_cost (same_level_inconsistence[i]->fact,
				  *same_level_inconsistence[i]->level, &loc_dg_num_cost);
	    if(GpG.verify_inc_choice)
	      cost= loc_dg_num_cost->num_actions;
	    else
	      cost= loc_dg_num_cost->totcost;
	  }
	/**
	   Confronto con il valore minimo
	   **
	   Comparing with the minimum value
	**/
	if (min_cost > cost)
	  {
	    min_cost=cost;
	    num_same_level_same_cost=0;
	    same_level_same_cost_inconsistence[num_same_level_same_cost++] = same_level_inconsistence[i];
	  }
	else if (min_cost == cost)
	  {
	    same_level_same_cost_inconsistence[num_same_level_same_cost++] = same_level_inconsistence[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level_same_cost>=num_max_vector_same_cost_inc)
	      {
		num_max_vector_same_cost_inc+=MAX_VECTOR_INC;
		if (!(same_level_same_cost_inconsistence = (constraints_list *)realloc(same_level_same_cost_inconsistence,num_max_vector_same_cost_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
      }
    }
  /**
     Ora aggiungo i treateds (se presenti) in coda al vettore same_level_same_cost
     **
     Now the treateds are added (if present) in queue at the same_level_same_cost array
  **/
  if (treated_flag==1) 
    for(i=0;i<num_same_level;i++)
      {
	if (same_level_inconsistence[i]->constraint_type ==C_T_TREATED_CL)
	  {
	    same_level_same_cost_inconsistence[num_same_level_same_cost++] = same_level_inconsistence[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level_same_cost>=num_max_vector_same_cost_inc){
	      num_max_vector_same_cost_inc=+MAX_VECTOR_INC;
	      if (!(same_level_same_cost_inconsistence = (constraints_list *)realloc(same_level_same_cost_inconsistence,num_max_vector_same_cost_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	    }
	  }
	}
  if (GpG.nonuniform_random_incosistence_test) 
    best = nonuniform_random (num_same_level_same_cost);
  else 
    best = MY_RANDOM % num_same_level_same_cost;
  
  return (same_level_same_cost_inconsistence[best]);
}




/** 
 * Name: choose_max_level_inconsistence
 * Scopo: Questa funziona seleziona una inconsistenza scegliendone una presente al livello piu alto 
 * Tipo: constraints_list
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_max_level_inconsistence
* Objective:
* Type: constraints_list
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
constraints_list choose_max_level_inconsistence()
{
  static constraints_list *same_level_inconsistence=NULL;
  static int num_max_vector_inc=MAX_VECTOR_INC;/**
						  Tiene il numero max di elementi dell'array
						  **
						  maximum number of array's elements
					       **/
  int i,best;
  int num_same_level=0;
  int max_level=0;
  
  if (same_level_inconsistence==NULL)
    if (!(same_level_inconsistence=(constraints_list *)calloc(MAX_VECTOR_INC,sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY); //out of memory
  
  //Vengono scansionate le tre liste contenenti i vari tipi di inconsistenze
  // e viene creata una lista: same_level_inconsistence[] nella quale sono
  //inserite le inconsistenze che si trovano al livello piu alto.
  
  /**
     Scansione delle lista delle inconsistenze logiche
     **
     Scanning of the logical inconsistence list
  **/
  for (i=0;i<GpG.num_false_fa;i++)
    {
      if (max_level < *unsup_fact[i]->level)
	{
	  max_level=*unsup_fact[i]->level;
	  num_same_level=0;
	  same_level_inconsistence[num_same_level++] = unsup_fact[i];
	}
      else 
	if (max_level == *unsup_fact[i]->level)
	  {
	    same_level_inconsistence[num_same_level++] = unsup_fact[i];
	    //Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	    if (num_same_level>=num_max_vector_inc)
	      {
		num_max_vector_inc+=MAX_VECTOR_INC;
		if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }
  /**
     Scansione delle lista delle inconsistenze numeriche
     **
     Scanning of the numerical inconsitence list
  **/
  for (i=0;i<GpG.num_false_num_fa;i++)
    {
    if (max_level < *unsup_num_fact[i]->level)
      {
	max_level=*unsup_num_fact[i]->level;
	num_same_level=0;
	same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
      }
    else 
      if (max_level == *unsup_num_fact[i]->level)
	{
	  same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
          /**
	     Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	     **
	     If the maximum limit of the array, i reallocate adding space
	  **/
	  if (num_same_level>=num_max_vector_inc)
	    {
	      num_max_vector_inc+=MAX_VECTOR_INC;
	      if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	    }
	}
    }
    /**
       Scansione delle lista delle inconsistenze temporali
       **
       Scanning of the temporal inconsitence list
    **/
    for (i=0;i<GpG.num_false_tmd_fa;i++)
      {
	if (max_level < *unsup_tmd_facts[i]->level)
	  {
	    max_level=*unsup_tmd_facts[i]->level;
	    num_same_level=0;
	    same_level_inconsistence[num_same_level++]=unsup_tmd_facts[i];
	  }
	else 
	  if (max_level == *unsup_tmd_facts[i]->level)
	    {
	      same_level_inconsistence[num_same_level++]=unsup_tmd_facts[i];
              /**
		 Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
		 **
		 If the maximum limit of the array, i reallocate adding space
	      **/
	      if (num_same_level>=num_max_vector_inc)
		{
		  num_max_vector_inc+=MAX_VECTOR_INC;
		  if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
		}
	    }
      }
  
  /*  //Scansione delle lista delle inconsistenze azioni
  for (i=0;i<GpG.num_false_act;i++)
    {
	if (max_level < *treated_c_l[i]->level)
	  {
	    max_level=*treated_c_l[i]->level;
	    num_same_level=0;
	    same_level_inconsistence[num_same_level++]=treated_c_l[i];
	  }
	else 
	  if (max_level == *treated_c_l[i]->level)
	    {
	      same_level_inconsistence[num_same_level++]=treated_c_l[i];
	      //Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	      if (num_same_level>=num_max_vector_inc)
		{
		  num_max_vector_inc+=MAX_VECTOR_INC;
		  if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
		}
	    }

	    }*/
  //Una volta trovate le inconsistenze presenti al livello piu alto,
  //casualmente se ne seleziona una
 
 if (GpG.nonuniform_random_incosistence_test) 
    best = nonuniform_random (num_same_level);
  else 
    best = MY_RANDOM % num_same_level;

  return (same_level_inconsistence[best]);
}



/** OK 28-07-04
 * Name: choose_min_level_constr_inconsistence()
 * Scopo: Questa funziona seleziona una inconsistenza scegliendone una presente al livello piu basso tra quelle meno costose
 * Tipo:
 * Input: constraints_list
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_min_level_constr_inconsistence()
* Objective:
* Type: constraints_list
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
constraints_list choose_min_level_constr_inconsistence()
{
  static constraints_list *same_level_inconsistence=NULL;
  static constraints_list *same_level_same_constr_inconsistence=NULL;
  static int num_max_vector_same_level_inc=MAX_VECTOR_INC;/**
							     Tiene il numero max di elementi dell'array al livello minimo
							     **
							     maximum number of array's elements at the minimum level
							  **/
  static int num_max_vector_same_constr_inc=MAX_VECTOR_INC;/**
							      Tiene il numero max di elementi dell'array per il costo minimo
							      **
							      maximum number of array's elementsfor the minimum cost
							   **/
  int i,best;
  int num_same_level=0;
  int num_same_level_same_constr=0;
  int treated_flag;
  int min_level=100000;
  float min_constr=100000.0;
  float curr_constr, cost, endtime = 0.0;
  
  //Tali array di puntatori vengono allocati solo la prima volta.Per mezzo
  //dell'operatore static vengono conservati in memoria anche una volta
  //usciti dalla procedura
  if (same_level_inconsistence==NULL)
    if (!(same_level_inconsistence = (constraints_list *)calloc(MAX_VECTOR_INC,sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY); //out of memory
  if (same_level_same_constr_inconsistence==NULL)
    if (!(same_level_same_constr_inconsistence = (constraints_list *)calloc(MAX_VECTOR_INC,sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
  
  //Vengono scansionate le tre liste contenenti i vari tipi di inconsistenze
  // e viene creata una lista: same_level_inconsistence[] nella quale sono
  //inserite le inconsistenze che si trovano al livello piu basso.
  
  /**
     Scansione delle lista delle inconsistenze logiche
     **
     Scanning of the logical inconsistence list
  **/
  for (i=0;i<GpG.num_false_fa;i++)
    {
      if (min_level > *unsup_fact[i]->level)
	{
	  min_level=*unsup_fact[i]->level;
	  num_same_level=0;
	  same_level_inconsistence[num_same_level++] = unsup_fact[i];
	}
      else 
	if (min_level == *unsup_fact[i]->level)
	  {
	    same_level_inconsistence[num_same_level++] = unsup_fact[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level>=num_max_vector_same_level_inc)
	      {
		num_max_vector_same_level_inc+=MAX_VECTOR_INC;
		if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_same_level_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }
  /**
     Scansione delle lista delle inconsistenze numeriche
     **
     Scanning of the numerical inconsitence list
  **/
  for (i=0;i<GpG.num_false_num_fa;i++)
    {
      if (min_level > *unsup_num_fact[i]->level)
	{
	  min_level=*unsup_num_fact[i]->level;
	  num_same_level=0;
	  same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
	}
      else 
	if (min_level == *unsup_num_fact[i]->level)
	  {
	    same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level>=num_max_vector_same_level_inc)
	      {
		num_max_vector_same_level_inc+=MAX_VECTOR_INC;
		if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_same_level_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }
  /**
     Scansione delle lista delle inconsistenze azioni
     **
     Scanning of the action inconsitence list
  **/
  for (i=0;i<GpG.num_false_act;i++)
    {
      if (min_level > *treated_c_l[i]->level)
	{
	  min_level=*treated_c_l[i]->level;
	  num_same_level=0;
	  same_level_inconsistence[num_same_level++]=treated_c_l[i];
	}
      else 
	if (min_level == *treated_c_l[i]->level)
	  {
	    same_level_inconsistence[num_same_level++]=treated_c_l[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level>=num_max_vector_same_level_inc)
	      {
		num_max_vector_same_level_inc+=MAX_VECTOR_INC;
		if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_same_level_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }
    /**
       Una volta trovate le inconsistenze presenti al livello più basso, si seleziona la meno costosa
       **
       When the lower level inconsistence have been found, I select the less expensive
    **/
   /**
      Azzero il flag della presenza di treateds
      **
      Setting to zero the flag of the presence of treateds
   **/
  treated_flag=0;
   
   /**
      Scansione delle lista delle inconsistenze che si trovano al livello piu basso
      **
      Scanning of the list of the inconsistences that are at le lower level
   **/
   for (i=0;i<num_same_level;i++)
     {
       if (same_level_inconsistence[i]->constraint_type ==C_T_TREATED_CL){
	 /**
	    Se si tratta di un treated, attivo il flag della presenza di treateds
	    **
	    if it is a treated, the flag of presence is activated
	 **/
	 treated_flag=1;
	 continue;
       }
       else{
	 /**
	    Altrimenti si tratta di un fatto, quindi ne valuto il costo
	    **
	    else it is a fact, then the cost is valuated
	  **/
	 /**
	    Calcolo del costo
	    **
	    Calculating the cost
	 **/
	 curr_constr = compute_constr_fact (same_level_inconsistence[i]->fact, same_level_inconsistence[i]->fact,*same_level_inconsistence[i]->level, 1, *same_level_inconsistence[i]->level, &cost, &endtime);
    
	 /**
	    Confronto con il valore minimo
	    **
	    Comparing with the minimum value
	 **/
	 if (min_constr > curr_constr)
	   {
	     min_constr = curr_constr;
	     num_same_level_same_constr = 0;
	     same_level_same_constr_inconsistence[num_same_level_same_constr++] = same_level_inconsistence[i];
	     
	     if(DEBUG5)
	       {
		 printf("\n\n BEST i_choice %d level %d cost %f constr %f  fact %d ",i,   *same_level_inconsistence[i]->level, cost,   min_constr,  same_level_inconsistence[i]->fact);
		 print_ft_name(same_level_inconsistence[i]->fact );
	       }
	     
	   }
	 else if (min_constr == curr_constr)
	   {
	     same_level_same_constr_inconsistence[num_same_level_same_constr++] = same_level_inconsistence[i];

	if(DEBUG5)
	  {
		printf("\n\n ADD BEST i_choice %d level %d cost %f constr %f  fact %d ",i,   *same_level_inconsistence[i]->level, cost,   min_constr,  same_level_inconsistence[i]->fact);
		print_ft_name(same_level_inconsistence[i]->fact );
	  }
        /**
	   Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	   **
	   If the maximum limit of the array, i reallocate adding space
	**/
	if (num_same_level_same_constr>=num_max_vector_same_constr_inc)
	  {
	    num_max_vector_same_constr_inc+=MAX_VECTOR_INC;
	    if (!(same_level_same_constr_inconsistence = (constraints_list *)realloc(same_level_same_constr_inconsistence,num_max_vector_same_constr_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	  }
      }
    else
      if(DEBUG5)
	  {
		printf("\n\n No Best i_choice %d level %d cost %f constr %f  fact %d ",i,   *same_level_inconsistence[i]->level, cost,  curr_constr,  same_level_inconsistence[i]->fact);
		print_ft_name(same_level_inconsistence[i]->fact );
	  }
  }
}
    
    /**
       Ora aggiungo i treateds (se presenti) in coda al vettore same_level_same_cost
       **
       Now the treateds are added (if present) in queue at the same_level_same_cost array
    **/
    if (treated_flag==1) 
      for(i=0;i<num_same_level;i++)
	{
	  if (same_level_inconsistence[i]->constraint_type ==C_T_TREATED_CL)
	    {
	      same_level_same_constr_inconsistence[num_same_level_same_constr++] = same_level_inconsistence[i];
              /**
		 Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
		 **
		 If the maximum limit of the array, i reallocate adding space
	      **/
	      if (num_same_level_same_constr>=num_max_vector_same_constr_inc){
		num_max_vector_same_constr_inc+=MAX_VECTOR_INC;
		if (!(same_level_same_constr_inconsistence = (constraints_list *)realloc(same_level_same_constr_inconsistence,num_max_vector_same_constr_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	    }
	}
 if (GpG.nonuniform_random_incosistence_test) 
    best = nonuniform_random (num_same_level_same_constr);
  else 
    best=MY_RANDOM % num_same_level_same_constr;

    return (same_level_same_constr_inconsistence[best]);
}



/** OK 28-07-04
 * Name: choose_min_level_constr_max_cost_inconsistence
 * Scopo: Questa funziona seleziona una inconsistenza scegliendone una presente al livello piu basso tra quelle meno costose
 * Tipo:
 * Input: constraints_list
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_min_level_constr_max_cost_inconsistence
* Objective:
* Type: constraints_list
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
constraints_list choose_min_level_constr_max_cost_inconsistence()
{
  static constraints_list *same_level_inconsistence=NULL;
  static constraints_list *same_level_same_constr_inconsistence=NULL;
  static int num_max_vector_same_level_inc=MAX_VECTOR_INC;/**
							     Tiene il numero max di elementi dell'array al livello minimo
							     **
							     maximum number of array's elements at the minimum level
							  **/
  static int num_max_vector_same_constr_inc=MAX_VECTOR_INC;/**
							      Tiene il numero max di elementi dell'array per il costo minimo
							      **
							      maximum number of array's elementsfor the minimum cost
							   **/
  int i,best;
  int num_same_level=0;
  int num_same_level_same_constr=0;
  int treated_flag;
  int min_level=100000;
  float min_constr=100000.0;
  float curr_constr;
  float min_cost=0.0, cost;
  float endtime = 0.0;
  
  //Tali array di puntatori vengono allocati solo la prima volta.Per mezzo
  //dell'operatore static vengono conservati in memoria anche una volta
  //usciti dalla procedura
  if (same_level_inconsistence==NULL)
    if (!(same_level_inconsistence = (constraints_list *)calloc(MAX_VECTOR_INC,sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY); //out of memory
  if (same_level_same_constr_inconsistence==NULL)
    if (!(same_level_same_constr_inconsistence = (constraints_list *)calloc(MAX_VECTOR_INC,sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
  
  //Vengono scansionate le tre liste contenenti i vari tipi di inconsistenze
  // e viene creata una lista: same_level_inconsistence[] nella quale sono
  //inserite le inconsistenze che si trovano al livello piu basso.
  
  /**
     Scansione delle lista delle inconsistenze logiche
     **
     Scanning of the logical inconsistence list
  **/
  for (i=0;i<GpG.num_false_fa;i++)
    {
      if (min_level > *unsup_fact[i]->level)
	{
	  min_level=*unsup_fact[i]->level;
	  num_same_level=0;
	  same_level_inconsistence[num_same_level++] = unsup_fact[i];
	}
      else 
	if (min_level == *unsup_fact[i]->level)
	  {
	    same_level_inconsistence[num_same_level++] = unsup_fact[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level>=num_max_vector_same_level_inc)
	      {
		num_max_vector_same_level_inc+=MAX_VECTOR_INC;
		if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_same_level_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }
  /**
     Scansione delle lista delle inconsistenze numeriche
     **
     Scanning of the numerical inconsitence list
  **/
  for (i=0;i<GpG.num_false_num_fa;i++)
    {
      if (min_level > *unsup_num_fact[i]->level)
	{
	  min_level=*unsup_num_fact[i]->level;
	  num_same_level=0;
	  same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
	}
      else 
	if (min_level == *unsup_num_fact[i]->level)
	  {
	    same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level>=num_max_vector_same_level_inc)
	      {
		num_max_vector_same_level_inc+=MAX_VECTOR_INC;
		if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_same_level_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }
  /**
     Scansione delle lista delle inconsistenze azioni
     **
     Scanning of the action inconsitence list
  **/
  for (i=0;i<GpG.num_false_act;i++)
    {
      if (min_level > *treated_c_l[i]->level)
	{
	  min_level=*treated_c_l[i]->level;
	  num_same_level=0;
	  same_level_inconsistence[num_same_level++]=treated_c_l[i];
	}
      else 
	if (min_level == *treated_c_l[i]->level)
	  {
	    same_level_inconsistence[num_same_level++]=treated_c_l[i];
            /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level>=num_max_vector_same_level_inc)
	      {
		num_max_vector_same_level_inc+=MAX_VECTOR_INC;
		if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_same_level_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
    }
    /**
       Una volta trovate le inconsistenze presenti al livello più basso, si seleziona la meno costosa
       **
       When the lower level inconsistence have been found, I select the less expensive
    **/
   /**
      Azzero il flag della presenza di treateds
      **
      Setting to zero the flag of the presence of treateds
   **/
  treated_flag=0;
  
   /**
      Scansione delle lista delle inconsistenze che si trovano al livello piu basso
      **
      Scanning of the list of the inconsistences that are at le lower level
   **/
    for (i=0;i<num_same_level;i++)
{
  
  if (same_level_inconsistence[i]->constraint_type ==C_T_TREATED_CL){
    /**
       Se si tratta di un treated, attivo il flag della presenza di treateds
       **
       if it is a treated, the flag of presence is activated
    **/
    treated_flag=1;
    continue;
  }
  else{
    /**
       Altrimenti si tratta di un fatto, quindi ne valuto il costo
       **
       else it is a fact, then the cost is valuated
    **/
    curr_constr = compute_constr_fact ( same_level_inconsistence[i]->fact, same_level_inconsistence[i]->fact,*same_level_inconsistence[i]->level, 1, *same_level_inconsistence[i]->level, &cost, &endtime);
    
    /**
       Confronto con il valore minimo
       **
       Comparing with the minimum value
    **/
    if (min_constr > curr_constr)
      {
	min_constr = curr_constr;
	num_same_level_same_constr = 0;
	same_level_same_constr_inconsistence[num_same_level_same_constr++] = same_level_inconsistence[i];
	min_cost=cost;
	if(DEBUG4)
	  {
	    printf("\n\n BEST i_choice %d level %d cost %f constr %f  fact %d num_same_lev %d ",i,   *same_level_inconsistence[i]->level, cost,   min_constr,  same_level_inconsistence[i]->fact, num_same_level);
	    print_ft_name(same_level_inconsistence[i]->fact );
	  }
      }
    else if (min_constr == curr_constr)
      {
	if(min_cost<cost)
	  {
	    min_constr = curr_constr;
	    num_same_level_same_constr = 0;
	    same_level_same_constr_inconsistence[num_same_level_same_constr++] = same_level_inconsistence[i];
	    min_cost=cost;

	    if(DEBUG4)
	      {
		printf("\n\n BEST i_choice %d level %d cost %f constr %f  fact %d ",i,   *same_level_inconsistence[i]->level, cost,   min_constr,  same_level_inconsistence[i]->fact);
		print_ft_name(same_level_inconsistence[i]->fact );
	      }
	  }
	else
	  if(min_cost==cost)
	  {

	    same_level_same_constr_inconsistence[num_same_level_same_constr++] = same_level_inconsistence[i];
	    
	    if(DEBUG4)
	      {
		printf("\n\n ADD BEST i_choice %d level %d cost %f constr %f  fact %d ",i,   *same_level_inconsistence[i]->level, cost,   min_constr,  same_level_inconsistence[i]->fact);
		print_ft_name(same_level_inconsistence[i]->fact );
	      }
	    /**
	       Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
	       **
	       If the maximum limit of the array, i reallocate adding space
	    **/
	    if (num_same_level_same_constr>=num_max_vector_same_constr_inc)
	      {
		num_max_vector_same_constr_inc+=MAX_VECTOR_INC;
		if (!(same_level_same_constr_inconsistence = (constraints_list *)realloc(same_level_same_constr_inconsistence,num_max_vector_same_constr_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	  }
	else
	  if(DEBUG4)
	    {
	      printf("\n\n No Best i_choice %d level %d cost %f constr %f  fact %d ",i,   *same_level_inconsistence[i]->level, cost, curr_constr,  same_level_inconsistence[i]->fact);
	      print_ft_name(same_level_inconsistence[i]->fact );
	    }
      }    
    else
      if(DEBUG4)
	{
	  printf("\n\n No Best i_choice %d level %d cost %f constr %f  fact %d ",i,   *same_level_inconsistence[i]->level, cost, curr_constr,  same_level_inconsistence[i]->fact);
	  print_ft_name(same_level_inconsistence[i]->fact );
	}
  }
}
    /**
       Ora aggiungo i treateds (se presenti) in coda al vettore same_level_same_cost
       **
       Now the treateds are added (if present) in queue at the same_level_same_cost array
    **/
    if (treated_flag==1) 
      for(i=0;i<num_same_level;i++)
	{
	  if (same_level_inconsistence[i]->constraint_type ==C_T_TREATED_CL)
	    {
	      same_level_same_constr_inconsistence[num_same_level_same_constr++] = same_level_inconsistence[i];
              /**
		 Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
		 **
		 If the maximum limit of the array, i reallocate adding space
	      **/
	      if (num_same_level_same_constr>=num_max_vector_same_constr_inc){
		num_max_vector_same_constr_inc+=MAX_VECTOR_INC;
		if (!(same_level_same_constr_inconsistence = (constraints_list *)realloc(same_level_same_constr_inconsistence,num_max_vector_same_constr_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
	      }
	    }
	}
 if (GpG.nonuniform_random_incosistence_test) 
    best = nonuniform_random (num_same_level_same_constr);
  else 
    best=MY_RANDOM % num_same_level_same_constr;

    return (same_level_same_constr_inconsistence[best]);
}



/** OK 28-07-04
 * Name: choose_min_level_inconsistence_optimised
 * Scopo: Questa funziona seleziona una inconsistenza scegliendone una presente al livello piu basso
 * Tipo:
 * Input: constraints_list
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_min_level_inconsistence_optimised
* Objective:
* Type: constraints_list
* Input:
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
constraints_list choose_min_level_inconsistence_optimised()
{
  static constraints_list *same_level_inconsistence=NULL;
  int i,best;
  int num_same_level=0;
  int min_level=100000;
  int fix_num;
  float k_weight_num_bool = 1;
  static int num_max_vector_inc=MAX_VECTOR_INC;/**
						  Tiene il numero max di elementi dell'array
						  **
						  maximum number of array's elementsfor
					       **/

  //Tale array di puntatori viene allocato solo la prima volta.Per mezzo
  //dell'operatore static viene conservato in memoria anche una volta
  //usciti dalla procedura
  if (same_level_inconsistence==NULL)
    if (!(same_level_inconsistence = (constraints_list *)calloc(MAX_VECTOR_INC,sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY); //out of memory
  
  //Viene scelta la lista di quale tipo di inconsistenze da scansionare
  // e viene creata una lista: same_level_inconsistence[] nella quale sono
  //inserite le inconsistenze del tipo scelto che si trovano al livello 
  //piu basso.
  
  /**
     Risolvo prima le inconsistenze temporali
     **
     Solving first the temporal inconsistence
  **/
   if (GpG.num_false_tmd_fa > 0) { 
     /**
	Scansione delle lista delle inconsistenze logiche
	**
	Scanning of the logical inconsistence list
     **/
     for (i=0;i<GpG.num_false_tmd_fa;i++)
       {
	 if (min_level > *unsup_tmd_facts[i]->level)
	   {
	     min_level=*unsup_tmd_facts[i]->level;
	     num_same_level=0;
	     same_level_inconsistence[num_same_level++]=unsup_tmd_facts[i];
	     
	     if(DEBUG5)
	       {
		 printf("\nINTIT TMD FACT LIST \nLevel %d Tmd Fact %d ",*unsup_tmd_facts[i]->level, unsup_tmd_facts[i]->fact );
		 print_ft_name(unsup_tmd_facts[i]->fact);
	       }
	   }
	 else 
	   if (min_level == *unsup_tmd_facts[i]->level)
	     {
	       same_level_inconsistence[num_same_level++]=unsup_tmd_facts[i];
	       
	       if(DEBUG5)
		 {
		   printf("\nLevel %d Tmd Fact %d ",*unsup_tmd_facts[i]->level, unsup_tmd_facts[i]->fact );
		   print_ft_name(unsup_tmd_facts[i]->fact);
		 }
	       
	       /**
		  Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
		  **
		  If the maximum limit of the array, i reallocate adding space
	       **/
	       if (num_same_level>=num_max_vector_inc)
		 {
		   num_max_vector_inc+=MAX_VECTOR_INC;
		   if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
		 }
	     }
       }
   }
   else
     {  
       /**
	  scelgo tra un inconsistenza numerica o una logica 
	  **
	  Choosing between a numerical or logic inconsistence
       **/
       if (GpG.num_false_num_fa == 0)
	 fix_num = FALSE;
       else   
	 if (GpG.num_false_fa == 0) 
	   fix_num = TRUE;
	 else
	   fix_num = (MY_RANDOM % (int) (GpG.num_false_fa + k_weight_num_bool * GpG.num_false_num_fa) ) > (GpG.num_false_fa);
       
	 /**
	    Inconsistenza logica
	    **
	    Logical inconsistence
	 **/
       if (!(fix_num)) {

	 /**
	    Scansione delle lista delle inconsistenze logiche
	    **
	    Scanning of the logical inconsistence list
	 **/
	 for (i=0;i<GpG.num_false_fa;i++)
	   {
	     if (min_level > *unsup_fact[i]->level)
	       {
		 min_level=*unsup_fact[i]->level;
		 num_same_level=0;
		 same_level_inconsistence[num_same_level++] = unsup_fact[i];
		 if(DEBUG5)
		   {
		     printf("\nINIT UNSUP FACT LIST \nLevel %d Unsup Fact %d ",*unsup_fact[i]->level, unsup_fact[i]->fact );
		     print_ft_name(unsup_fact[i]->fact);
		   }
	       }
	     else 
	       if (min_level == *unsup_fact[i]->level)
		 {
		   same_level_inconsistence[num_same_level++] = unsup_fact[i];
		   if(DEBUG5)
		     {
		       printf("\nLevel %d Unsup Fact %d ",*unsup_fact[i]->level, unsup_fact[i]->fact );
		       print_ft_name(unsup_fact[i]->fact);
		     }
		   /**
		      Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
		      **
		      If the maximum limit of the array, i reallocate adding space
		   **/
		   if (num_same_level>=num_max_vector_inc){
		     num_max_vector_inc+=MAX_VECTOR_INC;
		     if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
		   }
		 }
	   }
       }
       else 
	 {
	   /**
	      inconsistenza numerica
	      **
	      numerical inconsistence
	   **/
	   /**
	      Scansione delle lista delle inconsistenze numeriche
	      **
	      Scanning of the numerical inconsitence list
	   **/
	   for (i=0;i<GpG.num_false_num_fa;i++)
	     {
	       if (min_level > *unsup_num_fact[i]->level)
		 {
		   min_level=*unsup_num_fact[i]->level;
		   num_same_level=0;
		   same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
		   if(DEBUG5)
		     {
		       printf("\nINIT UNSUP NUM FACT LIST \nLevel %d Unsup Num Fact %d ",*unsup_num_fact[i]->level, unsup_num_fact[i]->fact );
		       print_ft_name(unsup_num_fact[i]->fact);
		     }
		 }
	       else 
		 if (min_level == *unsup_num_fact[i]->level)
	      {
		same_level_inconsistence[num_same_level++]=unsup_num_fact[i];
		if(DEBUG5)
		  {
		    printf("\nLevel %d Unsup Num Fact %d ",*unsup_num_fact[i]->level, unsup_num_fact[i]->fact );
		    print_ft_name(unsup_num_fact[i]->fact);
		  }
		/**
		   Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
		   **
		   If the maximum limit of the array, i reallocate adding space
		**/
		if (num_same_level>=num_max_vector_inc)
		  {
		    num_max_vector_inc+=MAX_VECTOR_INC;
		    if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
		  }
	      }
	     }
	 }
     }
   /**
      Scansione delle lista delle inconsistenze azioni
      **
      Scanning of the action inconsitence list
   **/
   for (i=0;i<GpG.num_false_act;i++)
     {
       if (min_level > *treated_c_l[i]->level)
	 {
	   min_level=*treated_c_l[i]->level;
	   num_same_level=0;
	   same_level_inconsistence[num_same_level++]=treated_c_l[i];
	   
	   if(DEBUG5)
	     {
	       printf("\nINTIT TREATED FACT LIST \nLevel %d Treated Fact %d ",*treated_c_l[i]->level, treated_c_l[i]->fact );
	       print_ft_name(treated_c_l[i]->fact);
	     }
	 }
       else 
	 if (min_level == *treated_c_l[i]->level)
	   {
	     same_level_inconsistence[num_same_level++]=treated_c_l[i];
	     
	     if(DEBUG5)
	       {
		 printf("\nLevel %d Treated Fact %d ",*treated_c_l[i]->level, treated_c_l[i]->fact );
		 print_ft_name(treated_c_l[i]->fact);
	       }
	      /**
		 Se viene superato il limite massimo dell'array, rialloco aggiungendo spazio
		 **
		 If the maximum limit of the array, i reallocate adding space
	      **/
	      if (num_same_level>=num_max_vector_inc)
		{
		  num_max_vector_inc+=MAX_VECTOR_INC;
		  if (!(same_level_inconsistence = (constraints_list *)realloc(same_level_inconsistence,num_max_vector_inc*sizeof(constraints_list)))) MSG_ERROR(WAR_NO_MEMORY);//out of memory
		}
	    }
     }
    /**
       Una volta trovate le inconsistenze presenti al livello più basso, casualmente se ne seleziona una
       **
       When the lower level inconsistence have been found, I randomly select one
    **/
    if (GpG.nonuniform_random_incosistence_test) 
      best = nonuniform_random (num_same_level);
    else 
      best = MY_RANDOM % num_same_level;
    
    return (same_level_inconsistence[best]);
}


/** 
 * Name: choose_inconsistence
 * Scopo: Selezione delle inconsistenze
 * Tipo: constraints_list
 * Input: int min_time
 *        int numrestart
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_inconsistence
* Objective: Inconsistence selection
* Type: constraints_list
* Input: int min_time 
*        int numrestart
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
constraints_list choose_inconsistence (int min_time,int numrestart)
{
  int tot;
  int unsup_pos;
  int fix_num, fix_timed;
  float k_weight_num_bool = 1;
  
  /*********************
  if (GpG.num_false_fa <= 0 && GpG.num_false_act <= 0 && GpG.num_false_num_fa <= 0 && GpG.num_false_tmd_fa <= 0) {
    if (GpG.optimize == 0 || GpG.num_solutions == 0)
      return 0;
    
    else {
      // Rimuovo un azione dell'action sugraoh in modo casuale al fine di introdurre delle inconsistenze e continuare il processo di ottimizzazione
      restart_search ();
    }
    }
  *****************/

  // If the reserch type is ANYTIME, use an apposite function that works on the first levels
  if (DEBUG3)
    {
      print_unsup_fact_vect ();
      print_unsup_num_facts ();
      print_unsup_timed_fact ();
    }
  if (DEBUG6 && GpG.accurate_cost >= COMPUTE_DG_SUM_COST)
    print_cost_of_unsupported_facts ();
 
  // If the # of false fact is 0, we have to choose an action to fix
  // If the # of false act is 0, we have to choose a fact to fix 
  // In these cases, the choosing tecnique is random
  
  if (GpG.num_false_fa <= 0 && GpG.num_false_num_fa <= 0 && GpG.num_false_tmd_fa <= 0) {
  /**
     inconsistenza azione
     **
     action inconsistence
  **/
    return treated_c_l[MY_RANDOM % GpG.num_false_act];
  }
  else /**
	  inconsistenza fatto
	  **
	  fact inconsistence
       **/
    //    if (GpG.num_false_act <= 0) {
    {
      fix_timed  = (MY_RANDOM % (int) (GpG.num_false_tmd_fa + GpG.num_false_fa + k_weight_num_bool * GpG.num_false_num_fa) ) < (GpG.num_false_tmd_fa);

      if( GpG.neighb_with_timed_fa && fix_timed )
	{
	  /**
	     Risolvo prima le inconsistenze temporali
	     **
	     Resolving first temporal inconsistence
	  **/
	  if (GpG.num_false_tmd_fa > 0) {
	    //	    printf("T");
	    unsup_pos = MY_RANDOM % GpG.num_false_tmd_fa;
	    if (GpG.inc_choice_type != RANDOM_INC)	
	      unsup_pos = choose_min_cost_unsup_tmd_fact ();

	    return unsup_tmd_facts[unsup_pos];
	  }
	}
      else
	{
	  fix_num =	(MY_RANDOM % (int) (GpG.num_false_fa + k_weight_num_bool * GpG.num_false_num_fa) ) > (GpG.num_false_fa);
	  
	  if (GpG.num_false_num_fa == 0)
	    fix_num = FALSE;
	  if (GpG.num_false_fa == 0) 
	    fix_num = TRUE;

#ifdef __TEST_MIXED__
      printf("\n NUMERICO[1] /LOGICO[0] ");
      fflush (stdout);
      scanf("%d",&fix_num);
#endif
      if (fix_num) {
	/**
	   inconsistenza numerica
	   **
	   numerical inconsistence
	**/
	assert (GpG.num_false_num_fa > 0);
	unsup_pos = MY_RANDOM % GpG.num_false_num_fa;
	if (GpG.inc_choice_type != RANDOM_INC)	
	  unsup_pos = choose_min_cost_unsup_num_fact ();

#ifdef __TEST_MIXED__
	printf("\n Inserisci fatto da supportare ");
	fflush (stdout);
	scanf("%d",&unsup_pos);
#endif
	return unsup_num_fact[unsup_pos];
      }
      else {
	/**
	   inconsistenza logica
	   **
	   logical inconsistence
	**/
	assert (GpG.num_false_fa > 0);
	unsup_pos = MY_RANDOM % GpG.num_false_fa;
	if (GpG.inc_choice_type != RANDOM_INC)	
	  unsup_pos = choose_min_cost_unsup_fact ();

#ifdef __TEST_MIXED__
	printf("\n Inserisci fatto da supportare ");
	fflush (stdout);
	scanf("%d",&unsup_pos);
#endif
	return unsup_fact[unsup_pos];
      }
    }
    }

  // If the # of false actions is above than the # of ME rels, there is a mistake, then correct it
  //  if (GpG.num_m_e < GpG.num_false_act ) GpG.num_m_e = GpG.num_false_act;
  // Same as above, but control the # of precs 
  //  if (GpG.num_prec < GpG.num_false_fa ) GpG.num_prec = GpG.num_false_fa;
 
  GpG.num_m_e = GpG.num_false_act;
  GpG.num_prec = GpG.num_false_fa;

  // Here, choose between a fact and an action, giving to the facts a different weight.
  // This choose is motivated by experimental results.
  tot = (int) ceil (GpG.weight_fact * GpG.num_prec + GpG.num_m_e);

  //     check_false_position();
  // III provo a rivuovere prima le mutex
  if ( ( MY_RANDOM  % tot) < GpG.num_m_e) {
    /**
       inconsistenza azione
       **
       action inconsistence
    **/
    unsup_pos = MY_RANDOM % GpG.num_false_act;
    return treated_c_l[unsup_pos];
  }
  else { /**
	    inconsistenza fatto
	    **
	    fact inconsistence
	 **/
    /**
       scelgo tra un inconsistenza numerica o una logica
       **
       choosing between a numerical or logic inconsistence
    **/
    fix_num = (MY_RANDOM % (int) (GpG.num_false_fa + k_weight_num_bool * GpG.num_false_num_fa)) >
      (GpG.num_false_fa);
    
    if (GpG.num_false_num_fa == 0)
      fix_num = FALSE;
    if (GpG.num_false_fa == 0)
      fix_num = TRUE;
    
#ifdef __TEST_MIXED__
      printf("\n NUMERICO[1] /LOGICO[0] ");
      fflush (stdout);
      scanf("%d",&fix_num);
#endif
    if (fix_num) {
      /**
	 inconsistenza numerica
	 **
	 numerical inconsistence
      **/
      assert (GpG.num_false_num_fa > 0);
      unsup_pos = MY_RANDOM % GpG.num_false_num_fa;
      if (GpG.inc_choice_type != RANDOM_INC)	
	unsup_pos = choose_min_cost_unsup_num_fact ();

#ifdef __TEST_MIXED__
      printf("\n Inserisci fatto da supportare ");
      fflush (stdout);
      scanf("%d",&unsup_pos);
#endif
      return unsup_num_fact[unsup_pos];
    }
    else {
      /**
	 inconsistenza logica
	 **
	 logical inconsistence
      **/
      assert (GpG.num_false_fa > 0);
      unsup_pos = MY_RANDOM % GpG.num_false_fa;
      if (GpG.inc_choice_type != RANDOM_INC)	
	unsup_pos = choose_min_cost_unsup_fact ();

#ifdef __TEST_MIXED__
      printf("\n Inserisci fatto da supportare ");
      fflush (stdout);
      scanf("%d",&unsup_pos);
#endif
      return unsup_fact[unsup_pos];
    }
  }
}





/**
 * Name: choose_inconsistence_to_fix
 * Scopo:
 * Tipo: constraints_list
 * Input: int min_time
 *        int num_restart
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: choose_inconsistence_to_fix
* Objective:
* Type: constraints_list
* Input: int min_time
*        int num_restart
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
constraints_list choose_inconsistence_to_fix(int min_time, int num_restart)
{
  //Nel caso in cui ci sia almeno un inconsistenza, la variabile
  //GpG.inc_choice_type determina il metodo di selezione  e di conseguenza
  //la procedura da richiamare
  
  switch(GpG.inc_choice_type)
    {
    case RANDOM_INCONSISTENCE: 
      return (constraints_list) choose_random_inconsistence();
     
    case MIN_COST_INCONSISTENCE: 
      return(constraints_list) choose_min_cost_inconsistence();
     
    case MIN_LEVEL_COST_INCONSISTENCE:
      return (constraints_list) choose_min_level_cost_inconsistence();
     
    case MAX_LEVEL_INCONSISTENCE: 
      return(constraints_list) choose_max_level_inconsistence();
      
    case MAX_COST_INCONSISTENCE: 
      return (constraints_list) choose_max_cost_inconsistence();
      
    case MIN_LEVEL_CONSTR_INCONSISTENCE: 
      return (constraints_list) choose_min_level_constr_inconsistence();
     
    case MIN_LEVEL_CONSTR_MAX_COST_INCONSISTENCE: 
      return (constraints_list) choose_min_level_constr_max_cost_inconsistence();
      
    case MIN_LEVEL_INCONSISTENCE:       

    default:
      return (constraints_list) choose_inconsistence(min_time, num_restart);
    }
}



/** 
 * Name: define_neighborhood_for_fix
 * Scopo:
 * Tipo: int
 * Input: constraints_list unsup_fact
 *        float *new_time
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: define_neighborhood_for_fix
* Objective:
* Type: int
* Input: constraints_list unsup_fact
*        float *new_time
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int define_neighborhood_for_fix(constraints_list unsup_fact, float *new_time)
{
  switch(unsup_fact->constraint_type)
    {
    case C_T_UNSUP_FACT: 
      return define_neighborhood (CONVERT_FACT_TO_NODE(unsup_fact->fact, *unsup_fact->level), TRUE);

    case C_T_UNSUP_NUM_FACT: 
      return define_neighborhood_for_numeric_actions (unsup_fact, TRUE);
      
    case C_T_TREATED_CL: 
      return define_neighborhood_for_threats(CONVERT_NOOP_TO_NODE (unsup_fact->fact, *unsup_fact->level), GpG.curr_plan_length);
          
    case C_T_UNSUP_TMD_FACT:
      return define_neighborhood_for_timed_fact(CONVERT_FACT_TO_NODE(unsup_fact->fact, *unsup_fact->level), new_time, TRUE);
    }

  return 0;
}


/** 
 * Name: fix_inconsistence
 * Scopo:
 * Tipo: int
 * Input: constraints_list unsup_fact
 *        int num_neighbors
 *        float new_time
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: fix_inconsistence
* Objective:
* Type: int
* Input: constraints_list unsup_fact
*        int num_neighbors
*        float new_time
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int fix_inconsistence(constraints_list unsup_fact, int num_neighbors, float new_time)
{
  switch(unsup_fact->constraint_type)
    {
    case C_T_UNSUP_FACT: 
      return fix_unsup_fact (unsup_fact, num_neighbors);
          
    case C_T_UNSUP_NUM_FACT: 
      return fix_unsup_num_fact(unsup_fact, num_neighbors);
          
    case C_T_TREATED_CL: 
      return fix_threated_fact (unsup_fact, num_neighbors);
          
    case C_T_UNSUP_TMD_FACT: 
      return fix_unsup_timed_fact(unsup_fact, num_neighbors, new_time);
    }

  return 0;
}





/** 
 * Name: search_step
 * Scopo: Selezione delle inconsistenze
 * Tipo: int
 * Input: int num_try
 *        int min_time
 *        int numrestart
 *        PlanAction ** plan_actions
 *        State * start_state
 *        State * end_state
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
* Name: search_step
* Objective: Inconsistence selection
* Type: int
* Input: int num_try
*        int min_time
*        int numrestart
*        PlanAction ** plan_actions
*        State * start_state
*        State * end_state
* Output:
* Main Data Structures:
* Main Functions Used:
* Call gives:
**/
int search_step(int num_try, int min_time, int numrestart, PlanAction ** plan_actions, State * start_state, State * end_state)
{
  int better, new_level, num_neighbors;
  constraints_list choice = NULL;
  float new_time = -1.0;
  
  /** 
      Se i tre array contenenti inconsistenze sono vuoti, si controlla se si sta ottimizzando o se sono state trovate già altre soluzioni.
      
      - nel caso in cui l'ottimizzazione sia disattivata o non sia stata ancora trovata una soluzione, si esce dalla funzione ritornando 0.
      - nel caso in cui l'ottimizzazione sia attiva o siano gia' state trovate altre soluzioni,si richiama la funzione restart_search () che rimuove
        un'azione dall'action subgraph in modo casuale al fine di introdurre delle nuove inconsist. cosi da continuare il processo di ottimizzazione.
        Se non si presentano ancora delle inconsistenze, viene ritonarto 0 e si esce.
      **
      If the three array containing inconsistence are empty, we control if we are optimizing or if there are alrady other solutions

      - if the optimization is disabled or there is not a solution, we go out to the function and return 0
      - if the optimization is abled or there are already solutions, we call the restart_search() function that randomly remove an action to the action
        subgraph to introducing new inconsistences to continue the optimization process.
	If there aren't new inconsistences, we return 0 and exit
  **/
  if (DEBUG2)
    printf ("\n\n\n\n\n@@@@@ Search Step: %d (tot step: %d)", num_try, GpG.count_num_try);
  
  Hvar.num_extended_unsupported_facts=0;

  search_step_check_supported_fact_in_relaxed_plan_for_inconsistences();

  if (GpG.num_false_fa <= 0 && GpG.num_false_act <= 0 && GpG.num_false_num_fa <= 0)
    {
      
      if (GpG.optimize == 0 || GpG.num_solutions == 0)
	{
	  if(!GpG.timed_facts_present || (GpG.num_false_tmd_fa <= 0))
	    return 0;
	}
      
      if(!GpG.neighb_with_timed_fa)
	{
	  if(GpG.timed_facts_present && GpG.num_false_tmd_fa > 0)
	    //	  printf("\nFind quasi-solution plan. Remove act with timed unsupported fact");
	    printf("QS%d",GpG.num_quasi_solution);
	  if(DEBUG5)
	    print_unsup_timed_fact ();
	}
      
      if (GpG.num_false_fa <= 0 && GpG.num_false_act <= 0 && GpG.num_false_num_fa <= 0)
	//	if ( !GpG.neighb_with_timed_fa || (GpG.neighb_with_timed_fa && GpG.num_false_tmd_fa <=0 ))
	{
	  if(GpG.timed_facts_present)
	    {
	      
#ifdef __MY_OUTPUT__
	      printf("\n Found Quasi-Solution: Timed Inc. %d Num Acts %d",
		     GpG.num_false_tmd_fa, GpG.num_actions);
	      
	      printf("\nBetter solution: TimedInc %d NumActs %d", GpG.qs_best_timed_inc, GpG.qs_best_numact);
#endif
	      
	      if (GpG.num_solutions == 0)
		{
		  better = is_quasi_sol_better ();
		  
		  if (better)
		    {
#ifdef __MY_OUTPUT__
		      printf("\n\n==> SAVE");
#else
		      printf("found better quasi-solution. Restart using this quasi-solution\n");
#endif
		      
		      new_level= save_curr_plan(GpG.curr_plan_length, plan_actions);
		      
		      GpG.input_plan_lenght = GpG.curr_plan_length = new_level - 1;
		      		      
		      GpG.num_quasi_solution++;
		      
		      GpG.qs_best_timed_inc = GpG.num_false_tmd_fa;
		      
		      GpG.qs_best_numact = GpG.num_actions;
		    }
		  else 
		    {
		      
#ifndef __MY_OUTPUT__
		      printf("found worse quasi-solution. Restart using stored quasi-solution\n");
#endif
		      
		      if (numrestart == 0 || (numrestart % 3))
			{
			  restore_empty_action_graph(start_state, end_state);
			  
			  load_quasi_sol(); 
			}
		    }
		  //		  printf("num : %d", num);
		  if (GpG.num_false_tmd_fa <= 5 || numrestart >= 3)
		    GpG.neighb_with_timed_fa = TRUE;
		}
	    }
	  //	  if ( !GpG.neighb_with_timed_fa || (GpG.neighb_with_timed_fa && GpG.num_false_tmd_fa <=0 ))
	    {
	      restart_search ();
	      return  0;
	    }
	}
    }
  if(DEBUG5)
    {
      print_unsup_fact_vect ();
      print_unsup_num_facts ();
      print_unsup_timed_fact ();
    }
  
  choice = choose_inconsistence_to_fix(min_time, numrestart);

  Hvar.constr = choice;
  
  /**
     Inizializzo paramentro per limitare computazione costo prec
     **
     Initializing parameter to limit computation prec cost
  **/
  local_search.best_action = -1;
  
  num_neighbors = define_neighborhood_for_fix(choice, &new_time);

  fix_inconsistence(choice, num_neighbors, new_time);

  return 0;
}



/*********************************************
             WALKPLAN ALGORITHM    
**********************************************/


/** LOCAL SEARCH OK 01-03-04
 * Name: LocalSearch
 * Scopo: settare i parametri di ricerca (la quale verra' effettuata su un piano)
 * Tipo: int
 * Input: State * start_state
 *        State * end_state
 *        PlanAction ** plan_actions
 * Output: restituisce il numero di passi di ricerca
 * Strutture dati principali: GpG
 *                            vectlevel[]
 *                            inform
 *                            State (Struttura atta a contenere informazioni relative a fatti)
 *                            PlanAction (Struttura atta a contenere informazioni relative ad azioni)
 * Funzioni principali utilizzate: choose_act_fa
 *                                 initialize
 *                                 store_curr_plan
 *                                 set_param
 *                                 update_local_minima
 *                                 continue_to_optimize
 *                                 DeltaTime
 *                                 store_adapted_temporal_plan
 * Chiamata da: main
**
*  Name: LocalSearch
*  Objective:  to set the search parameters (which will be done on a plan)
*  Type: int
*  Input: State *start_state
*         State *end_state
*         PlanAction ** plan_actions
*  Output: it gives back the number of search steps
*  Main Data Structures: GpG
*                        vectlevel[ ]
*                        inform
*                        Sate (Structure to contain informations relative to the facts)
*                        PlanAction (Structure to contain information relative to the actions)
*  Main Functions Used: choose_act_fa
*                       initialize
*                       store_curr_plan
*                       set_param
*                       update_local_minima
*                       continue_to_optimize
*                       DeltaTime
*                       store_adapted_temporal_plan
*  Call gives: main
**/
int LocalSearch (State * start_state, State * end_state, PlanAction ** plan_actions)
{
  /** 
    Variabili di appoggio 
    **
    Variable of support
  **/
  int  newlevel=0, loc_init_time, tot_numtry, num_try_print, 
    num_restart, try_time_check, num_run = 0;

  float plan_time = 0.0; 
  int optimize = TRUE;

  GpG.count_num_try = 1;
  GpG.curr_goal_state = end_state;
  gmax_cpu_time_for_quality_mode = MAXFLOAT;

  // instanzio min array e codice che andra' spostato
  srandom (seed);
  gnoop_conn = gft_conn;
  loc_init_time = GpG.curr_plan_length = GpG.max_plan_length - 1;

  intial_heuristic_param ();
  do
    {
      num_run++;
      
      reset_heuristic_parameters ();
      
      if(end_state->num_F > 100)
	tot_numtry = 2 * GpG.numtry;
      else 
	tot_numtry =  GpG.numtry;
      
      if (GpG.numrestart <= 0 || GpG.numtry <= 0)
	return (-1);
      if (DEBUG0 && !DEBUG1)
	printf ("\n\nSearching ('.' = every 50 search steps):\n");

      for (num_restart = 0; num_restart < GpG.numrestart; num_restart++)
	{
	  //	  if(tot_numtry *= GpG.inc_restart < gnum_ef_conn * gnum_ft_conn)
	  tot_numtry = (int) (tot_numtry * GpG.inc_restart);
	  
	  GpG.curr_plan_length = loc_init_time;

#ifdef TEST_GR
	  check_plan (GpG.curr_plan_length);
#endif 

	  if (DEBUG0 && !DEBUG1 && num_restart > 0)
	    printf (" Restart");

	  initialize (start_state, end_state, num_restart);	// Set a starting condition in the plan

	  if (DEBUG6)
	    my_print_plan_all (GpG.curr_plan_length);
	
	  if (DEBUG1)
	    printf ("\n\n\n\n-----SEARCH START----- ");
	  
	  fflush (stdout);

#ifdef TEST_GR
	  fprintf (stderr, "\n\n RESEARCH PHASE");
	  check_plan (GpG.curr_plan_length);
#endif

	  /**
	     Questo è il numero totale dei fatti e delle azioni che erano false
	     **
	     This is the total number of facts and actions that are false
	  **/
	  GpG.num_false_tot = GpG.num_false_act + GpG.num_false_fa + GpG.num_false_num_fa + GpG.num_false_tmd_fa;
	  
	  //	  if(GpG.num_solutions == 0 || optimize)
	  set_heuristic_parameters (num_restart, num_run);

	  //	  if(num_run == 11)
	  //	    GpG.info_search = 6;


	  for (num_try = 1, num_try_print = 1, try_time_check = 1; num_try < tot_numtry;
	       num_try++, num_try_print++, GpG.count_num_try++, try_time_check++)
	    {
	      if(GpG.ls_max_num_flips>0 && GpG.ls_max_num_flips<GpG.count_num_try)
		{
		  printf("\n\nMax num flips reached. Stop execution.");
		  fflush(stdout);
		  exit(0);
		}
	      /**
		 ogni cinque iterazioni controllo di non aver superato max_cputime
		 **
		 every five iteration, I control to not have overtaken max_cputime
	      **/
	      if (try_time_check >= 5)	
		{
		  if (check_cpu_time(&plan_time))
		    return(0);
		  
		  try_time_check = 1;
		}
	      /* every 50 flips check plan length and step number */
	      if (num_try_print >= 50)
		{
		  if (GpG.num_actions > 20 && GpG.curr_plan_length - GpG.num_actions * 3 > GpG.curr_plan_length)
		    compress_vectlevel();
		  
		  if (DEBUG0 && !DEBUG1)
		    printf (".");
		
		  num_try_print = 1;
		}
	      
	      set_param (GpG.num_false_tot);
		  
#ifdef __TEST__
	      printf ("\nPiano parziale:");
	      if (DEBUG5)
		my_print_plan_all (GpG.curr_plan_length);
#endif
	     
	      /**
		 Search step
	      **/
	      search_step (num_try, GpG.curr_plan_length, num_restart, plan_actions, start_state, end_state);

	      GpG.num_false_tot = GpG.num_false_act + GpG.num_false_fa + GpG.num_false_num_fa + GpG.num_false_tmd_fa;
	      
	      if (GpG.num_false_tot == 0)
		{
		  tot_numtry = 500;
		}
	      if (GpG.num_false_tot == 0)
		{
		  check_num_prec();
		  
		  GpG.num_false_tot = GpG.num_false_act + GpG.num_false_fa + GpG.num_false_num_fa + GpG.num_false_tmd_fa;		  
		}
	      if (GpG.num_false_tot == 0)
		{
		  if(GpG.splitted_actions)
		    {
		      newlevel = save_temp_plan (GpG.curr_plan_length, &GpG.tempplan);
		      
		      GpG.accurate_numeric_constraint = TRUE;

		      restore_empty_action_graph (start_state, end_state);
		      
		      compress_numeric_plan();

		      GpG.accurate_numeric_constraint = FALSE;
		    }
		  else if (!GpG.temporal_plan)
		    compress_plan ();
		  
		  optimize = is_plan_better ();

		  if (!optimize)
		    {
#ifdef  __MY_OUTPUT__
		      if (GpG.mode == INCREMENTAL)
			print_solution_time_and_cost();
#endif
		    }
		  else
		    {
		      /**
			 Save features of the best plan computed
		      **/
		      GpG.last_succ_restart = num_restart;
		      GpG.best_cost = GpG.total_cost_from_metric;
		      GpG.best_time = GpG.total_time;
		      GpG.best_numact = GpG.num_actions;
		      GpG.input_plan_lenght = GpG.curr_plan_length;
		    }

		  if (GpG.splitted_actions || optimize || 
		      (num_try > 100 && GpG.initialize_from != INIT_EMPTY_PLAN ))
		    break;
		}
	      if (GpG.curr_plan_length >= MAX_PLAN_LENGTH)
		{
		  printf("\n\nWarning: Increase MAX_PLAN_LENGTH\n\n");
		  break;
		}
	      /** 
		  il modo in cui sono memorizzati i LM dipende dal valore della variabile GpG.lm_multilevel
		  **
		  memorization of LM depends by the GpG.lm_multilevel variable value
	      **/
	      if (GpG.lm_multilevel) 
		{
		  update_precond_multilevel();
		  update_decr_me_prec_multilevel();
		  
#ifdef __STATISTIC_LM__
		  statistic_lm_multilevel();
#endif 
		  
		}  
	      else  
		{
		  update_precond();
		  update_decr_me_prec();
		  
#ifdef __STATISTIC_LM__
		  statistic_lm_statici();
#endif
		}
	      
	    } // FOR NUM_TRY	
	  if (GpG.num_false_act || GpG.num_false_fa || GpG.num_false_num_fa || 
	      GpG.num_false_tmd_fa || optimize == FALSE)
	    {
	      if (DEBUG0 && !DEBUG1)
		{
		  if (GpG.num_false_tot == 0 && optimize==FALSE && GpG.mode == INCREMENTAL)
		    printf (" found solution of bad quality.");
		  else
		    printf (" search limit exceeded.");
		}
	    }
	  else 
	    {
	      if(!GpG.splitted_actions)
		newlevel = save_curr_plan (GpG.curr_plan_length, plan_actions);
	      else
		restore_temp_plan (GpG.tempplan, &GpG.gplan_actions);  

	      if(FALSE && GpG.splitted_actions)
		{
		  GpG.accurate_numeric_constraint = TRUE;
		  
		  reset_plan(GpG.curr_plan_length);
		  
		  compress_numeric_plan();

		  GpG.accurate_numeric_constraint = FALSE;
		}
	      /**
		 ricerca della migliore soluzione
		 **
		 find better solution
	      **/
	      if(GpG.store_plan)
		{
		  times (&search_end);
		  //	      GpG.do_best_first = FALSE;
		  
#ifdef __TEST__
		  check_plan (GpG.curr_plan_length);
#endif
		  plan_time = DeltaTime (search_start, search_end);
		  
#ifdef __TEST__
		  fprintf (stderr,
			   "\n Num sol %d, Num false =0, level %d, time_search %.3f, numrestart=%d, numtry= %d num actions %d plan cost %.2f  plan duration %.2f plan time %.2f gmutex_total_time %.2f",
			   GpG.num_solutions, GpG.curr_plan_length, plan_time,
			   num_restart, num_try, GpG.num_actions, 
			   GpG.total_cost_from_metric, GpG.total_time, 
			   plan_time, gmutex_total_time);
#endif

#ifdef TEST_GR
		  check_plan (GpG.curr_plan_length);
#endif
		  times (&glob_end_time);

		  gtotal_time = DeltaTime(glob_start_time, glob_end_time);


#ifdef _TEST_NUM_PREC_
		  print_num_levels_and_actions ();
		  fflush (stdout);
#endif
		  
#ifdef __STATISTIC_LM__
		  /**
		     stampa le statistiche globali a video alla fine dell'elaborazione
		     **
		     print to video the global statistics at the end of the elaboration
		  **/
		  print_statistic_info();
		  close_statistic_files();
#endif
		
		  if (DEBUG0 && !DEBUG1 && GpG.mode!=QUALITY)
		    printf (" solution found: ");
		  if (DEBUG6)
		    {
		      print_num_levels_and_actions ();
		      if (GpG.temporal_plan)
			print_temporal_plan (GpG.curr_plan_length);
		    }
		  
#ifndef __ONLY_ONE_PLANNER__
		  if (GpG.mode == QUALITY && GpG.num_solutions == 0)
#else
		  if (GpG.num_solutions == 0)
#endif
		    {
		      //		  if ( gtotal_time <= 3)
		      if ( plan_time <= 12)
			{
			  gmax_cpu_time_for_quality_mode = 25 * plan_time;
			  //		      gmax_cpu_time_for_quality_mode = 100 * gtotal_time;
			}
		      else
			{
			  //		      if ( gtotal_time <= 100)
			  if ( plan_time <= 100)
			    {
			      gmax_cpu_time_for_quality_mode = plan_time + 300;
			      //			  gmax_cpu_time_for_quality_mode = gtotal_time + 300;
			    }
			  else
			    {
			      //			  if ( gtotal_time <= 1200)
			      if ( plan_time <= 1200)
				{
				  gmax_cpu_time_for_quality_mode = plan_time + 600;
				  //			      gmax_cpu_time_for_quality_mode = gtotal_time + 600;
				}
			      else
				{
				  gmax_cpu_time_for_quality_mode = 1740;
				}
			    }
			}
		    }
		  GpG.num_solutions++;
		  if (GpG.mode != QUALITY || 
		      (GpG.mode == QUALITY && gtotal_time >= gmax_cpu_time_for_quality_mode ) )
		    {
		      store_plan(plan_time);
		    }
#ifndef __ONLY_ONE_PLANNER__
		  else
#else
		  if(gtotal_time < gmax_cpu_time_for_quality_mode )	
#endif
		    {
		      save_curr_temporal_plan(GpG.curr_plan_length, &GpG.plan_actions_for_quality_mode);
		      
		      GpG.time_lastsol = gtotal_time;
		    }
		  reset_plan_param(newlevel, plan_actions);
		  if (DEBUG0)
		    if (GpG.num_solutions >= GpG.max_num_solutions || GpG.noout)
		      {
			if(GpG.pop)
			  print_pop();
			else
			  print_actions_in_plan ();
		      }
		  
#ifndef __ONLY_ONE_PLANNER__
		    if (GpG.mode == QUALITY)
#endif
		      {
			if(GpG.maximize_plan && GpG.total_cost_from_metric < 0)
			  {
			    plan_info_for_quality_mode.num_actions = GpG.num_actions;
			    plan_info_for_quality_mode.total_cost = GpG.total_cost_from_metric * (-1);
			    plan_info_for_quality_mode.total_time = GpG.total_time; 
			    plan_info_for_quality_mode.metricvalue = GpG.total_cost_from_metric * GpG.orig_weight_cost * (-1) + GpG.total_time * GpG.orig_weight_time;
			  }
			else
			  {
			    plan_info_for_quality_mode.num_actions = GpG.num_actions;
			    plan_info_for_quality_mode.total_cost = GpG.total_cost_from_metric;
			    plan_info_for_quality_mode.total_time = GpG.total_time; 
			    plan_info_for_quality_mode.metricvalue = GpG.total_cost_from_metric * GpG.orig_weight_cost + GpG.total_time * GpG.orig_weight_time;
			  }
			// FUNZIONE DI AUTOTERMINAZIONE DIPENDENTE ANCHE DA ULTIMA SOL
			if ( gtotal_time > 0.85 * gmax_cpu_time_for_quality_mode )
			  gmax_cpu_time_for_quality_mode *= 1.1;
		      }

		  print_solution_features(plan_time, num_restart);
		  
		  if (GpG.max_num_solutions > 0
		      && GpG.num_solutions >= GpG.max_num_solutions)
		    return (0);
		  
		// Set parametri heuristic parameters
		  if ( GpG.onlysearchcostx1stsol && GpG.num_solutions == 1 )
		    {
		      //		      if (!GpG.maximize_plan)
			GpG.weight_cost = GpG.orig_weight_cost/2;
			//		      else
			//			GpG.weight_cost = GpG.orig_weight_cost;

		      //		    if (!GpG.timed_facts_present)
		      GpG.weight_time = GpG.orig_weight_time;
		      
		      if (GpG.orig_weight_time > 0)
			GpG.temporal_plan = TRUE;
		      
#ifdef __MY_OUTPUT__
		      if (DEBUG0)
			{
			  printf("\n\nForcing Evaluation function from problem metric\n\n");
			  printf("\tAction duration %.2f; Action cost %.2f\n\n", GpG.weight_time, GpG.weight_cost);
			}
#endif
		    }
		  
		  fflush (stdout);
		}
	    }
	} // NUM_RESTART
    }
  while ( (GpG.num_solutions > 0 && 
	   !(GpG.inst_duplicate_param ||  GpG.contraddictory_ef_conn) ) 
	  || num_run < GpG.numrun || GpG.timed_facts_present || GpG.numeric_precs_present || GpG.derived_predicates );
  
#ifdef __TEST__
  if (DEBUG5)
    my_print_plan_all (GpG.curr_plan_length);
  
  check_plan (GpG.curr_plan_length);
#endif
  
  return (num_try + num_restart * GpG.numtry);
}
