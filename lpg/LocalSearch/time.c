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
 * File: time.c
 * Description: Time manager for the LPG planner.
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/




#include <values.h>
#include "lpg.h"
#include "LpgTime.h"
#include "output.h"
#include "LpgOutput.h"
#include "utilities.h"
#include "LocalSearch.h"
#include "ActionSubgraph.h"
#include "H_relaxed.h"
#include "H_max.h"
#include "inst_utils.h"
#include "numeric.h"



int check_unsup_tmd() {
  int i, fct;
  ActNode_list inf_act;
  
  printf("\nCheck unsup timed facts...");
  
  if (!GpG.timed_facts_present)
    printf("\nTimed facts presence : FALSE");

  for (i = 0; i < GpG.num_false_tmd_fa; i++) {
    if (unsup_tmd_facts[i] -> fact < 0)
      printf("\nFATTO SUPPORTATO IN UNSUP_TIMED %d", i);
    else {
      fct = unsup_tmd_facts[i] -> fact;
      inf_act = GET_ACTION_OF_LEVEL(*(unsup_tmd_facts[i] -> level));
      if (!is_fact_in_preconditions(inf_act -> position, fct)
	  && !is_fact_in_preconditions_overall(inf_act -> position, fct)
	  && !is_fact_in_preconditions_end(inf_act -> position, fct))
	printf("\n    ERROR :: LEVEL : %d", *unsup_tmd_facts[i]->level);
    }
  } 
  
  return 0;

}


/***************************************
 *           FUNZIONI DI RESET
 *
 *            RESET FUNCTIONS
 ***************************************/ 




void reset_time()
{
  int time, i;

  FctNode_list inf_f;
  NoopNode_list inf_n;
  ActNode_list inf_a;


  reset_constraint_matrix ();

  for (time = 0; time < GpG.curr_plan_length; time++)

    {

      if (vectlevel[time] == NULL)
	continue;

      for (i = 0; i < GpG.max_num_facts; i++)
	{
	  inf_f = &vectlevel[time]->fact[i];
	  inf_f->time_f = NOTIME;
	  inf_f->action_f = NULL;

	  inf_n = &vectlevel[time]->noop_act[i];
	  inf_n->time_f = NOTIME;
	  inf_n->action_f = NULL;
	}

      inf_a = &vectlevel[time]->action;

      inf_a->time_f = 0.0;
      inf_a->action_f = NULL;
      inf_a->ord_pos = 0;

    }
}






/**
 * Name: reset_constraint_matrix
 * Scopo: azzerare la matrice degli ordinamenti (mat_ord)
 *        azzerare il vettore di corrispondenza tra la matrice 
 *        degli ordinamenti e i nodi del grafo (act_ord_vect)
 *        azzerare il  numero delle azioni inserite nel piano (num_act_ord)
 * Tipo: void
 * Input: nessuno
 * Output: nessuno
 * Strutture dati principali: num_act_ord
 *                            mat_ord
 *                            act_ord_vect
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: reset_plan
 **
 *  Name:  reset_constraint_matrix
 *  Target:  reset matrix of the orderings (mat_ord)
 *           reset array of correspondence between the matrix of the 
 *           orderings and the nodes of the TDA-graph (act_ord_vect)
 *           reset the number of actions inserted in the plan (num_act_ord)
 * Type:  void
 * Input:  NONE
 * Output:  NONE
 * Main Data Structures :  num_act_ord
 *                         mat_ord
 *                         act_ord_vect
 * Main functions used: none
 * Called by:  reset_plan
 **/

void reset_constraint_matrix ()
{

  int i;

#ifdef __TEST__
  int j;
#endif

  /**
     Pone uguale a zero il numero di azioni nella matrice degli ordinamenti
     **
     The number of actions in the matrix of the orderings is set equal to zero
  **/ 

  num_act_ord = 0;

  /**
     azzera il vettore di corrispondenza
     **
     reset the array of correspondence
  **/   
  for (i = 0; i < MAX_NUM_ACTIONS; i++){
    act_ord_vect[i] = NULL;
  }

  /**
     Azzera le righe della matrice degli ordinamenti
     **
     reset the lines of the matrix of the orderings
  **/ 
  memset (mat_ord[0], 0,MAX_NUM_ACTIONS * MAX_NUM_ACTIONS * sizeof (char));

#ifdef __TEST__

  /**
     Controlla che la matrice degli ordinamenti e che il vettore 
     di corrispondenza siano stati azzerati, in caso contrario 
     visualizza a console un messaggio di errore
     **
     Check that the matrix of the orderings and that the correspondence array
     has been resetted, otherwise it visualizes an error message
  **/ 

  for (i = 0; i < MAX_NUM_ACTIONS; i++)
    if (act_ord_vect[i] != NULL)
      printf ("\nError on resetting act_ord_vect");

  for (i = 0; i < MAX_NUM_ACTIONS; i++)
    for (j = 0; j < MAX_NUM_ACTIONS; j++)
      if (mat_ord[i][j] != 0)
	printf ("\nError on resetting mat_ord");

#endif

}



/**
 * Nome: reset_propagation_vect
 * Scopo: azzerare la propagation list. E' eseguita ad ogni restart
 * Tipo: void
 * Input: nessuno
 * Output: nessuno
 * Strutture dati principali: prop_level_index
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: reset_plan
 **
 *  Name:  reset_propagation_vect
 *  Target:  reset the propagation list. It is esud at each restart
 *  Type:  void
 *  Input:  none
 *  Output:  none
 *  Main Data Structures:  prop_level_index
 *  Main functions Used:  none
 *  Called by:  reset_plan
 **/

void reset_propagation_vect ()
{
  memset (prop_level_index, -1, MAX_PLAN_LENGTH * sizeof (short int));
}


/********************************************************************
 *       GESTIONE LISTA DI PROPAGAZIONE DEGLI ISTANTI TEMPORALI
 *
 *       MANAGEMENT OF THE PROPAGATION LIST FOR TEMPORAL INSTANTS
 **********************************************************************/         

/**
 * Nome: insert_propagation_list
 * Scopo: inserire un'azione nella propagation list
 * Tipo: int
 * Input: ActNode_list infAction (tipo ANODE che descrive l'azione passata)
 * Output: 1 se l'inserimento è andato a buon fine
 *         0 se l'azione è già presente nella propagation list
 *         un messaggio di errore se l'azione non può essere inserita
 * Strutture dati principali: ActNode_list infAction
 *                            prop_level_index
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: propagate_cvars
 *              update_time
 *              noop_remotion_time
 *              forward_noop_remotion_time
 *              forward_noop_propagation_time
 *              propagation_time
 *              insert_time
 **
 *  Name:  insert_propagation_list
 *  Objective:  to insert an action in the propagation list
 *  Type:  int
 *  Input:  ActNode_list infAction (ActNode type describing the input action)
 *  Output:  1 if the insertion has been effected
 *           0 if the action is already present in the propagation list
 *           an error message if the action cannot be inserted
 *  Main Data Structures:  ActNode_list infAction
 *                         prop_level_index
 *  Main functions Used: none
 *  Called by:  propagate_cvars
 *              update_time
 *              noop_remotion_time
 *              forward_noop_remotion_time
 *              forward_noop_propagation_time
 *              propagation_time
 *              insert_time
 **/   

int insert_propagation_list (ActNode_list infAction)
{
  /**
     Controlla che la posizione dell'azione non 
     sia superiore alla lunghezza massima del piano
  **
     Check that the action position is not greater 
     than maximum plan length
  **/          


  if (infAction->position < 0) {
    printf("\nWarning : action position is -1 (insert_propagation_list).");
    return FALSE;
  }
 
  if (*infAction->level >= MAX_PLAN_LENGTH) {
#ifdef __MY_OUTPUT__
    MSG_ERROR ( WAR_MAX_PLAN_LENGTH );   
#else
    printf( WAR_MAX_PLAN_LENGTH );
#endif    
    exit (1);
  }

  /**
     Controlla nella propagation list la presenza dell'azione. 
     Se non è presente la inserisci e ritorna 1 altrimenti non 
     fa nulla e restituisce 0
     **
     Check the presence of the action in the propagation list.  
     If the action is not present, then insert it and return 1 
     otherwise does nothing and return 0
  **/

  if (prop_level_index[*infAction->level] == -1)
    prop_level_index[*infAction->level] = *infAction->level;
  else
    return FALSE;

  return TRUE;

}

/************************************************
         FUNZIONI DI GESTIONE DEL TEMPO
 **
       FUNCTIONS OF MANAGEMENT FOR THE TIME
 **************************************************/    


/**
   Ritorna l'istante inferiore a cui si puo' supportare un fatto
   **
   Return the lowest time at which a fact can be supported
**/
float get_fact_time (int pos)
{
  /**
     Dummy precondition per splitted actions
  **/
  if (gft_conn[pos].fact_type == IS_SPL_PREC )
    return(0.0);

  return (Hvar.dg_facts_min_duration[pos]);
}


/**
   E' chiamata da time_adj e ha il compito di propagare i tempi
   **
   It is called by time_adj and its target is the time propagation
 */

int propagation_time (ActNode_list infAction)
{

  FctNode_list infEl;
  ActNode_list saveact;
  register FctNode_list add_effect = NULL;
  register NoopNode_list infNoop;
  register int el, cel = 0, j;
  float max_time, savetime;
  int level, next_level, ind;
  EfConn *act;

  act = CONVERT_ACTION_TO_VERTEX (infAction->position);
  
  level = *infAction->level;
  next_level = level + 1;

/**
   Stabiliamo l'istante di inizio dell'azione; prendiamo il massimo 
   tra l'istante in cui sono supportate le precondizioni e l'istante 
   finale delle azioni che precedono l'azione inserita
   **
   Set the start time of the action, taking the maximum value between 
   the time in which the preconditions are supported and the 
   end time of the actions that have to precede it
 */

  max_time = 0.0;

  infAction->action_f = NULL;

  /** 
     Precondizioni AT_START 
     *
     at start preconditions
  **/
  for (j = 0; j < gef_conn[infAction->position].num_PC; j++)
    {
      el = gef_conn[infAction->position].PC[j];

      if (el < 0)
	continue;

      infEl = CONVERT_FACT_TO_NODE (el, level);
      if (max_time < infEl->time_f)
	{
	  max_time = infEl->time_f;
	  infAction->action_f = infEl->action_f;


	}
    }

  /**
     Azioni durative
     **
     Durative Actions
  **/
  if (gef_conn[infAction->position].sf != NULL)
    {
      /** 
	 Precondizioni OVERALL 
	 *
	 over all preconditions
      **/
      for (j = 0; j < gef_conn[infAction->position].sf->num_PC_overall; j++)
	{
	  el = gef_conn[infAction->position].sf->PC_overall[j];

	  if (el < 0)
	    continue;

	  /**
             Se il fatto e' negli effetti additivi AT_START non viene valutato
	     **
	     If the fact is an additive at start effect, then it is not considered
	  **/
	  if (is_fact_in_additive_effects_start (infAction->position, el))
	    continue;

	  infEl = CONVERT_FACT_TO_NODE (el, level);
	  if (max_time < infEl->time_f)
	    {
	      max_time = infEl->time_f;
	      infAction->action_f = infEl->action_f;
	    }
	}

      /** 
	 Precondizioni AT_END 
	 *
	 at end preconditions
      **/
      for (j = 0; j < gef_conn[infAction->position].sf->num_PC_end; j++)
	{
	  el = gef_conn[infAction->position].sf->PC_end[j];

	  if (el < 0)
	    continue;

	  /**
	     Se il fatto e' negli effetti additivi AT_START, non viene valutato
	     **
	     If the fact is an AT_START additive effect, then it is not considered 
	  **/

	  if (is_fact_in_additive_effects_start (infAction->position, el))
	    continue;

	  infEl = CONVERT_FACT_TO_NODE (el, level);

	  if (max_time < infEl->time_f - get_action_time (infAction->position, level))
	    {
	      max_time = infEl->time_f - get_action_time (infAction->position, level);
	      infAction->action_f = infEl->action_f;
	    }
	}

    } /*  end durative actions */


  /**
     Istante massimo dato dai vincoli di ordinamento
     **
     Maximum time given by ordering constraints
  **/
    for (ind = 0; ind < num_act_ord; ind++)
      {
	if (GpG.constraint_type==0) 
	  /* 
	     Vincolo di ordinamento piu' restrittivo 
	  ** 
	     Strongest ordering constraint
	  */
	  {
	    if (mat_ord[ind][infAction->ord_pos] == 1)
	      if (max_time < act_ord_vect[ind]->time_f)
		{
		  max_time = act_ord_vect[ind]->time_f;
		  infAction->action_f = act_ord_vect[ind];
		}
	  }
	else 
	  /*
	    Vincolo di ordinamento per azioni durative: sia A un'azione
	    gia' inserita a un livello inferiore all'azione di cui stiamo 
	    propagando il tempo B  
	  **
	    Ordering constraint for durative actions: A is an inserted action 
	    at a level lower than the action B for which LPG is updating
	    the temporal values of the TDA-graph nodes
	  */
	  {
	    if (mat_ord[ind][infAction->ord_pos] == EA_SB) 
	      /*
		l'azione B deve iniziare dopo la fine di A 
		** 
		action B begins after the end of A
	      */
	      {
		if (max_time < act_ord_vect[ind]->time_f)
		  {
		    max_time = act_ord_vect[ind]->time_f;
		    infAction->action_f = act_ord_vect[ind];

		  }
	      }
	    else
	      {
		if (mat_ord[ind][infAction->ord_pos] == EA_EB) 
		  /* 
		     l'azione B deve finire dopo la fine di A 
		  ** 
		     action B ends after the end of A
		   */
		  {
		    if (max_time < act_ord_vect[ind]->time_f - get_action_time (infAction->position, level) )
		      {
			max_time = act_ord_vect[ind]->time_f - get_action_time (infAction->position, level);
			infAction->action_f = act_ord_vect[ind];
		      }
		  }
		else
		  if (mat_ord[ind][infAction->ord_pos] == SA_SB) 
		    /* 
		       l'azione B deve iniziare dopo l'inizio di A 
		    ** 
		       action B begins after the start of A 
		    */
		    {
		      if (max_time < act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level ) )
			{
			  max_time = act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level );
			  infAction->action_f = act_ord_vect[ind];
			}
		    }
		  else
		    {
		      if (mat_ord[ind][infAction->ord_pos] == SA_EB) 
			/* 
			   l'azione B deve finire dopo l'inizio di A 
			** 
			   action B ends after the start of A 
			*/
			{
			  if (max_time < act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level ) - get_action_time (infAction->position, level)  )
			    {
			      max_time = act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level ) - get_action_time (infAction->position, level);
			      infAction->action_f = act_ord_vect[ind];
			    }
			}
		      else
			{
			  if (mat_ord[ind][infAction->ord_pos] == EA_EB__SA_SB)
			    /* 
			       l'azione B e' sovrapposta ad A 
			    ** 
			       action B overlap action A 
			    */
			    {
			      if(get_action_time(infAction->position, level ) < get_action_time(act_ord_vect[ind]->position, *act_ord_vect[ind]->level ))
				{
				  // EA_EB
				  if (max_time < act_ord_vect[ind]->time_f - get_action_time (infAction->position, level) )
				    {
				      max_time = act_ord_vect[ind]->time_f - get_action_time (infAction->position, level);
				      infAction->action_f = act_ord_vect[ind];
				    }
				}
			      else // SA_SB
				{
				  if (max_time < act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level ) )
				    {
				      max_time = act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level );
				      infAction->action_f = act_ord_vect[ind];
				    }
				}
			    }
			  
			}
		      
		    }
	      }
	    
	  }
      }


  if(GpG.timed_facts_present && GET_BIT(GpG.has_timed_preconds, infAction -> position))
    {
      savetime = max_time;
      
      max_time = check_time_interval (max_time, infAction);

      /*
      printf("\nTime returned by check_time_interval %.2f",max_time);
      */

      if (max_time < 0.0) 
	{
	  max_time = savetime;	  
	  
	  /** 
	     Calcoliamo l'istante finale dell'azione inserita 
	     *
	     Compute the end-time of the inserted action
	  **/
	  infAction->time_f = max_time + get_action_time (infAction->position, level);
	}
    }

  /**
     I fatti hanno tempi negativi se falsi. 
     Il tempo di inizio dell'azione non puo' essere negativo.
     **
     Only the false facts have negative times.
     The start time of the action cannot be negative
  **/

  if (max_time < 0)
    max_time = 0.0;

  /**
     Calcoliamo l'istane finale dell'azione inserita: 
     se il suo istante finale non e' cambiato, allora terminiamo la propagazione
     **
     Compute the end time of the inserted action. 
     If its end instant has not changed, then the propagation is finished
  **/
  if (infAction->time_f == max_time + get_action_time (infAction->position, level))
    return (0);
  else
    infAction->time_f = max_time + get_action_time (infAction->position, level);

  /*
  printf("\ntempo assegnato: %.2f",infAction->time_f);
  */

  if (DEBUG4)
    printf("\n  --Propagation Act: %s, level %d\n      start_time %.2f, end_time %.2f",
	   print_op_name_string (infAction->position, temp_name), level, max_time, infAction->time_f);

  /**
     Istante temporale in cui gli effetti additivi vengono realizzati 
     **
     Time at which the additive effects are achieved
  **/

  /** 
     Effetti addittivi AT_END 
     *
     at end additive effects
  **/
  for (j = 0; j < gef_conn[infAction->position].num_A; j++)
    {
      cel = gef_conn[infAction->position].A[j];

      if (cel < 0)
	continue;

      add_effect = CONVERT_FACT_TO_NODE (cel, next_level);


      /**
	 Se il fatto ha un istante maggiore di quello finale dell'azione, 
	 allora viene aggiornato subito il nuovo istante
	 **
	 If the fact has a time greater than the end time of the action, 
	 then we update the time value of the fact node
      **/
      if (add_effect->time_f > infAction->time_f || 
	  add_effect->time_f == NOTIME)
	  {
	    add_effect->time_f = infAction->time_f;
	    add_effect->action_f = infAction;

	  /**
	     Se il fatto e' precondizione dell'azione al livello 
	     successivo allora viene inserita nella propagation_list
	     **
	     If the fact is a precondition of an action A at the 
	     next level, then we add A to the propagation list
          **/
	  if (GET_ACTION_OF_LEVEL (next_level)->w_is_used && 
	      (is_fact_in_preconditions(vectlevel[next_level]->action.position, add_effect->position)
	       || (is_fact_in_preconditions_overall(vectlevel[next_level]->action.position, add_effect->position)
		   && !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position, add_effect->position))))
	    insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));

	  /**
	     Propaghiamo in avanti il nuovo istante temporale
	     **
	     We propagate the temporal value in the following levels
	  **/
	  if (CONVERT_NOOP_TO_NODE (cel, next_level)->w_is_used)
	    forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(cel, next_level));

	  }
      else 
	/**
	   Se l'istante temporale del fatto era dato proprio
	   dall'azione propagata allora valutiamo se la rispettiva
	   NOOP puo' dargli un'istante piu' piccolo
	   **
	   If the temporal value of the fact f depends by the action
	   propagated, then we check if the corresponding NOOP can
	   support f at smaller timeq
        **/
	if (add_effect->action_f == infAction)
	  {
	    savetime = add_effect->time_f;
	    saveact = add_effect->action_f;
    
	    add_effect->time_f = infAction->time_f;
	    
	    /** 
		Se la rispettiva NOOP e' inserita e ha istante finale
		minore dell'istante finale dell'azione propagata, allora
		prendo l'istante della NOOP
		**
		If the corresponding NOOP is present in TDA-graph and it
		has an end time that is smaller than the end time of the
		action propagated, then we use the NOOP time
	    **/
	    if (CONVERT_NOOP_TO_NODE (add_effect->position, level)->w_is_used)
	      
	      if (add_effect->time_f == NOTIME ||
		  add_effect->time_f > CONVERT_NOOP_TO_NODE (add_effect->position, level)->time_f)
		{
		  add_effect->time_f = CONVERT_NOOP_TO_NODE (add_effect->position, level)->time_f;
		  add_effect->action_f = CONVERT_NOOP_TO_NODE (add_effect->position, level)->action_f;
		}
	    
	    /**
	       Se l'istante del fatto e' cambiato...
	       **
	       If the time of the fact is changed... 
	    **/
	    if (savetime != add_effect->time_f || 
		saveact != add_effect->action_f || 
		savetime == Hvar.dg_facts_min_duration[add_effect->position])
	      {
		
		if (DEBUG4)
		  {
		    printf ("\n\t-Propagation end_effect: %s, level %d, time %.2f ",
			    print_ft_name_string (cel, temp_name), next_level, add_effect->time_f);
		    printf ("\n\t  Act: %s", print_op_name_string (act->position, temp_name));
		  }
		
	      /**
		 Se il fatto e' precondizione dell'azione al livello 
		 successivo allora viene inserita nella propagation_list
		 **
		 If the fact is precondition of an action A at the 
		 next level, then we insert A in the propagation list
	      **/
		if ( (savetime != add_effect->time_f || 
		      saveact != add_effect->action_f )
		    && GET_ACTION_OF_LEVEL (next_level)->w_is_used  &&
		    (is_fact_in_preconditions(vectlevel[next_level]->action.position,add_effect->position)
		     ||(is_fact_in_preconditions_overall(vectlevel[next_level]->action.position, add_effect->position)
			&& !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
		  insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));
		
	      /**
		 Propaghiamo in avanti il nuovo istante temporale
		 **
		 We propagate the temporal value in the following levels
	      **/
		if (CONVERT_NOOP_TO_NODE (add_effect->position, next_level)->w_is_used)
		  forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(add_effect->position, next_level));
	      }
	  }
	}

  /**
     Azione durativa
     **
     Durative Action
  **/
  if (gef_conn[infAction->position].sf != NULL)

    /** 
       Effetti AT_START 
       **
       at start effects
    **/
    for (j = 0; j < gef_conn[infAction->position].sf->num_A_start; j++)
      {
	cel = gef_conn[infAction->position].sf->A_start[j];

	if (cel < 0)
	  continue;

	add_effect = CONVERT_FACT_TO_NODE (cel, next_level);
	infNoop = CONVERT_NOOP_TO_NODE (cel, level);

	/** 
	   L'istante finale della NOOP e' uguale all'istante 
	   iniziale dell'azione
	   **
	   The end time of the NOOP is equal than the 
	   start time of the action
	**/
	infNoop->time_f = infAction->time_f - get_action_time (infAction->position, level);
	infNoop->action_f = infAction;

	/**
	   Se l'istante del fatto al livello precedente e' inferiore
	   rispetto all'istante finale della NOOP allora l'istante
	   finale della NOOP e' uguale all'istante del fatto
	   **
	   If the time of the fact at the previous level is lower than
	   the end time of the NOOP, then the end time of the NOOP is
	   equal to the fact time
	**/
	if (CONVERT_FACT_TO_NODE (cel, level)->w_is_true > 0)
	  if (CONVERT_FACT_TO_NODE (cel, level)->time_f < infNoop->time_f)
	    {
	      infNoop->time_f = CONVERT_FACT_TO_NODE (cel, level)->time_f;
	      infNoop->action_f = CONVERT_FACT_TO_NODE (cel, level)->action_f;
	    }
	/**
	   Se il fatto non e' negli effetti cancellanti AT_END...
	   **
	   If the fact is an AT_END delete effects...
	**/
	if (!is_fact_in_delete_effects (infAction->position, cel))
	  {

	    /**
	       Se il fatto ha un istante maggiore di quello finale della NOOP,
	       allora viene aggiornato subito il nuovo istane
	       **
	       If the time of the fact f is greater than the end time
	       of the NOOP, then we update the time of f using no-op time
	    **/
	    if (add_effect->time_f == NOTIME ||
		add_effect->time_f > infNoop->time_f)
	      {
		add_effect->time_f = infNoop->time_f;
		add_effect->action_f = infNoop->action_f;

		/**
		   Se il fatto e' precondizione dell'azione al 
		   livello successivo allora viene inserita nella 
		   propagation_list
		   **
		   If the fact f is a precondition of the action at
		   the next level, then we add f to the propagation
		   list
		**/
		if (GET_ACTION_OF_LEVEL (next_level)->w_is_used &&
		    (is_fact_in_preconditions(vectlevel[next_level]->action.position,add_effect->position)
		     ||(is_fact_in_preconditions_overall(vectlevel[next_level]->action.position,add_effect->position)
			&& !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
		  insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));

		/**
		   Propaghiamo in avanti il nuovo istante temporale
		   **
		   We propagate the temporal value in the following levels
		**/
		if (CONVERT_NOOP_TO_NODE (cel, next_level)->w_is_used)
		  forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(cel, next_level));

	      }

	    else

	      /*
		Se l'istante temporale del fatto era dato proprio
		dalla NOOP allora prendiamo il tempo della NOOP
		**
		If the fact time was given just by the NOOP, then we
		take the time of the NOOP
	      **/
	      if (add_effect->action_f == infNoop->action_f)
		{
		  savetime = add_effect->time_f;
		  saveact = add_effect->action_f;

		  add_effect->time_f = infNoop->time_f;
		  
		/**
		   Se l'istante del fatto e' cambiato...
		   **
		   If the time of the fact is changed...
		**/
		  if (savetime != add_effect->time_f || 
		      saveact != add_effect->action_f 
		      || savetime == Hvar.dg_facts_min_duration[add_effect->position])
		    {
		      
		      if (DEBUG4)
			{
			  printf("\n\t-Propagation Start_eff: %s, level %d, time %.2f ",print_ft_name_string (cel, temp_name), next_level,add_effect->time_f);
			  printf("\n\t  Act: %s", print_op_name_string (act->position, temp_name));
			}
		    /** 
		       Se il fatto e' precondizione dell'azione al
		       livello successivo allora viene inserita nella
		       propagation_list
		       **
		       If the fact f is a precondition of the action
		       at the next level, then we add f in the
		       propagation list
		    **/
		      if ((savetime != add_effect->time_f || 
			   saveact != add_effect->action_f )
			  && GET_ACTION_OF_LEVEL (next_level)->w_is_used
			  && (is_fact_in_preconditions(vectlevel[next_level]->action.position,add_effect->position)
			      || (is_fact_in_preconditions_overall(vectlevel[next_level]->action.position, add_effect->position)
				  && !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
			insert_propagation_list (GET_ACTION_OF_LEVEL(next_level));
		      
		    /*
		      Propaghiamo in avanti il nuovo istante temporale
		      **
		      We propagate the time value in the following levels
		    **/
		      if (CONVERT_NOOP_TO_NODE(add_effect->position, next_level)->w_is_used)
			forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(add_effect->position,next_level));
		    }
		}
	  }
      }	 /* end durative actions */


#ifdef __TEST__
  printf("\nFact time propagation: %s in level %d at time %.2f action %s",
     print_ft_name_string (cel, temp_name), next_level, add_effect->time_f,
     print_op_name_string (act->position, temp_name));
#endif


  /**
     Inseriamo nella propagation_list tutte le azioni ordinate 
     dopo l'azione inserita
     **
     We add to the propagation_list each ordered action with the
     action that is inserted in the TDA-graph in this search step
  **/
  for (ind = 0; ind < num_act_ord; ind++)
    if (GpG.constraint_type==0)
      {
	if (mat_ord[infAction->ord_pos][ind] == 1)
	  insert_propagation_list (act_ord_vect[ind]);
      }
    else
      {
	if (mat_ord[infAction->ord_pos][ind] != 0)
	  insert_propagation_list (act_ord_vect[ind]);
      }
  return (1);

}





/**
   E' richiamata da insert_time e da update_time per la propagazione
   di eventuali istanti di tempo modificati
   **
   It is called by insert_time and by update_time for time propagation
**/

void time_adj (ActNode_list infAction)
{

  int level, ind;

  level = *infAction->level;

  /* 
     Per tutti i livelli... 
     **
     For any level of the TDA-graph...
  */
  for (ind = level + 1; ind < GpG.curr_plan_length; ind++)
    {
      if (prop_level_index[ind] == -1)
	continue;

      /**
	 Se l'azione e' nella propagation_list allora vengono
	 ricalcolati i tempi
	 **
	 If the action is in the propagation_list, then we compute
	 its time
      **/
      propagation_time (GET_ACTION_OF_LEVEL (ind));
      prop_level_index[ind] = -1;
    }

}

/**
 * Nome: insert_time 
 * Scopo: calcolare l'istante in cui gli effetti di una azione
 * inserita possono essere resi veri determinare l'istante di tempo in
 * cui sono supportati gli effetti additivi propaga in avanti gli
 * istanti degli effetti additivi inserisce le azioni successive a
 * quella passata nella propagation liste aggiorna i rispettivi
 * istanti temporali
 * Tipo: void
 * Input: ActNode_list infAction (tipo ANODE che descrive l'azione di input)
 * Output: nessuno
 * Strutture dati principali: ActNode_list infAction
 *                            mat_ord
 *                            act_ord_vect
 *                            gef_conn
 *                            GpG
 * Funzioni principali utilizzate: void temporal_constraints (ActNode_list infAction)
 *                                 float get_action_time (int pos, int level)
 *                                 int is_fact_in_additive_effects (int act_pos,int fact_pos)
 *                                 int insert_propagation_list (ActNode_list infAction)
 *                                 int is_fact_in_additive_effects_start (int act_pos, int fact_pos)
 *                                 void time_adj (ActNode_list infAction)
 *                                 float get_fact_time (int pos)
 *                                 int is_fact_in_preconditions (int act_pos, int
 *                                 int is_fact_in_delete_effects (int act_pos, int fact_pos)
 *                                 char *print_op_name_string (int pos, char *out_string)
 *                                 char *print_ft_name_string (int pos, char *out_string)
 * Chiamata da: compress_plan
 *              insert_action_in_vect_level
 **
 * Name:  insert_time
 * Target: compute the time at which the effects of the action, that
 * is added to the current TDA-graph in this search step, are
 * achieved; for each additive effects, this function propagates the
 * time of the additive effects in the following levels; it adds
 * the actions in the following levels to the propagation list and
 * updates the corresponding temporal values
 * Type:  void
 * Input:  ActNode_list infAction (ActNode type that describes the action passed to the function)
 * Output:  none
 * Main Data Structures:  ActNode_list infAction
 *                        mat_ord
 *                        act_ord_vect
 *                        gef_conn
 *                        GpG
 * main functions used:  void temporal_constraints (ActNode_list infAction)
*                       float get_action_time (int pos, int level)
 *                       int is_fact_in_additive_effects (int act_pos, int fact_pos)
 *                       int insert_propagation_list (ActNode_list infAction)
 *                       int is_fact_in_additive_effects_start (int act_pos, int fact_pos)
 *                       void time_adj (ActNode_list infAction)
 *                       float get_fact_time (int pos)
 *                       int is_fact_in_preconditions (int act_pos, int fact_pos)
 *                       int is_fact_in_preconditions_overall (int act_pos, int fact_pos)
 *                       void forward_noop_propagation_time (ActNode_list infNoop)
 *                       int is_fact_in_additive_effects (int act_pos, int fact_pos)
 *                       int is_fact_in_delete_effects (int act_pos, int fact_pos)
 *                       char * print_op_name_string (int pos, char * out_string)
 *                       char * print_ft_name_string (int pos, char * out_string)
 *  Call gives:  compress_plan
 *               insert_action_in_vect_level
**/ 

void insert_time (ActNode_list infAction)
{
  /**
     infEl variabile di appoggio a cui vengono assegnate le
     precondizioni di una azione infNoop variabile di appoggio a cui
     vengono assegnate le varie noop add_effect variabile di appoggio
     a cui vengono assegnati gli effetti additivi di una azione float
     maxtime istante di massimo inizio level e next_level
     corrispondono rispettivamente al livello dell'azione infAction e
     a quello successivo
  **
     infEl variable of support to which they the preconditions of one
     action are assigned infNoop variable of support to which they the
     several noop are assigned add_effect variable of support to which
     the additive effects of an action are assigned float maxtime
     moment of maximum beginning level and next_level correspond
     respectively to the level of the action infAction and to the
     following one
  **/   
  
  FctNode_list infEl, add_effect;
  NoopNode_list infNoop;
  int el, cel, j;

  /**
     Assegniamo a level il livello dell'azione inserita e assegno a
     next_level il livello successivo
  **
     We assign to level the level of the inserted action and assign to
     next_level to the successive level
  **/
  float max_time, save_time;
  int level, next_level, ind;

  //  reset_propagation_vect();

  level = *infAction->level;
  next_level = level + 1;

  num_shifted_act = 0;
 /*
  if (infAction -> position < 0)
	  return;
  */

  /**
     Stabiliamo i vincoli di ordinamento con le altre azioni del piano
     parziale.  Se insert_time e' chiamata da compress_plan sono
     gia' stati stabiliti i vincoli di ordinamento
  **
     We establish the ordering constraints with the other actions of
     the partial plan.  If insert_time is called by compress_plan, then
     the ordering constraint is already computed
  **/    
  if (GpG.temporal_plan)
    temporal_constraints (infAction);
  
#ifdef __TEST__
  else
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else 
  printf( WAR_BUG );
#endif  

#endif

  /**
     Stabiliamo l'istante di inizio dell'azione: prendiamo il massimo
     tra l'istante in cui sono supportate le precondizioni e l'istante
     finale delle azioni che precedono l'azione inserita
  **
     We compute the start time of the action: we consider the maximum
     value between the time at which the preconditions are supported
     and the end time of the actions that have to precede the
     underlying action
  **/

  max_time = 0.0;
  /**
     Istante di massimo inizio riazzerato 
     ** 
     Reset start time
  **/

  /**
     Precondizioni AT_START. Se la precondizione relativa all'azione è
     falsa prendo l'istante minimo a cui la precondizione è
     raggiungibile mentre se è vera prendo l'istante in cui la
     precondizione è supportata.
  **
     AT_START preconditions. If the precondition is not supported, we
     consider the minimum time at which the precondition is achieved;
     otherwise, if it is supported, we consider the time at which the
     precondition is supported.
  **/ 

  for (j = 0; j < gef_conn[infAction->position].num_PC; j++)
    {
     /**
 	 numero corrispondente alla precondizione dell'azione
      ** 
	 number corresponding to the precondition of the action
      **/   

      el = gef_conn[infAction->position].PC[j];
 
     /**
 	 Precondizione numerica
      **
 	 Numerical precondition      
      **/  

      if (el < 0)
	continue;
      
      /**
 	 Ricava la struttura NODE associata al fatto
      **
 	 structure representing fact node
      **/                                                                        

      infEl = CONVERT_FACT_TO_NODE (el, level);

      /**
 	 Se il fatto e' falso prendiamo l'istante piu' piccolo a cui
	 e' raggiungibile
      **
 	 If the fact is not supported, then we consider the lowest
 	 reachability time
      **/

      if (infEl->w_is_true < 1)
	{
	  infEl->time_f = get_fact_time (el);
	  infEl->action_f = NULL;
	}
      /**
 	 Se il fatto e' vero prendiamo l'istante effettivo a cui e'
 	 supportato
      **
 	 If the fact is supported, we consider the temporal value at
	 which it is supported in the current plan
      **/ 

      if (max_time < infEl->time_f)
	{
	  max_time = infEl->time_f;
	  infAction->action_f = infEl->action_f;
	}
    }
  
  /**
     Azioni durative
     **
     Durative actions
  **/      
                
  /**
     Condizione per verificare se si tratta di un'azione durativa
  **
     Condition for durative action
  **/ 
  if (gef_conn[infAction->position].sf != NULL)
    {
      /**
	 Precondizioni OVERALL
      **
	 OVERALL Preconditions
      **/

      for (j = 0; j < gef_conn[infAction->position].sf->num_PC_overall; j++)
	{
          /**
	     numero corrispondente alla precondizione dell'azione
	  **
	     number corresponding to the action precondition
          **/                                                                    
	  el = gef_conn[infAction->position].sf->PC_overall[j];

	  if (el < 0)
	    continue;

          /**
	     Se il fatto e' negli effetti additivi AT_START non viene
	     valutato perche' supportato dall'azione stessa
	  **
	     If the fact is an AT_START additive effect, then it is not
	     considered because it is supported by the action self
          **/

	  if (is_fact_in_additive_effects_start (infAction->position, el))
	    continue;
          /**
	     Ricava la struttura NODE associata al fatto
	     **
	     It derives the NODE structure associated to the fact
          **/                                                                    
	  infEl = CONVERT_FACT_TO_NODE (el, level);
          /**
	     Se il fatto e' falso prendiamo l'istante piu' piccolo a
	     cui e' raggiungibile
	  **
	     If the fact is not supported, then we consider the lowest
	     reachability value
          **/                                                                    
	  if (infEl->w_is_true < 1)
	    infEl->time_f = get_fact_time (el);

          /**
	     Se il fatto e' vero prendiamo l'istante effettivo a cui
	     e' supportato
	  **
	     If the fact is supported, then we consider the time at which
	     it is supported in the current TDA-graph
          **/
	  if (max_time < infEl->time_f)
	    {
	      max_time = infEl->time_f;
	      infAction->action_f = infEl->action_f;
	    }
	}

      /**
	 Precondizioni AT_END
      **
	 Preconditions AT_END
      **/
      for (j = 0; j < gef_conn[infAction->position].sf->num_PC_end; j++)
	{
	  el = gef_conn[infAction->position].sf->PC_end[j];

	  if (el < 0)
	    continue;

	  /**
	     Se il fatto e' negli effetti additivi AT_START, non viene
	     valutato
	  **
	     If the fact is an AT_START additive effect, then it is
	     not considered
          **/                                                                    	  if (is_fact_in_additive_effects_start (infAction->position, el))
	    continue;


          /**
	     Ricava la struttura NODE associata al fatto
	  **
	     NODE structure corresponding to the fact node
          **/                                                                    
	  infEl = CONVERT_FACT_TO_NODE (el, level);

          /**
	     Se il fatto e' falso prendiamo l'istante piu' piccolo a
	     cui e' raggiungibile
	  **
	     If the fact is not supported, then we consider the lowest
	     reachability value
          **/                                                                    
	  if (infEl->w_is_true < 1)
	    {
	      infEl->time_f = get_fact_time (el);
	      infEl->action_f = NULL;
	    }
          /**
	     Se il fatto e' vero prendiamo l'istante effettivo a cui
	     e' supportato.  Da notare che siccome è una precondizione
	     AT_END per determinare max_time viene tolta la durata
	     dell'azione dal tempo del fatto
	     **
	     If the fact is supported, then we consider the time at
	     which it is supported in the current plan.  Since it is
	     an AT_END precondition of the action A, in order to
	     determine the possible start time of A we subtract the
	     duration of A from the time value at which the fact is
	     supported
          **/                                                                    
	  if (max_time < infEl->time_f - get_action_time (infAction->position, level))
	    {
	      max_time = infEl->time_f - get_action_time (infAction->position, level);
	      infAction->action_f = infEl->action_f;
	    }
	}

    }	/* end durative actions */
    
  /**
     Istante massimo di inizio imposto dai vincoli di ordinamento
  **
     Maximum start time imposed by the ordering constraints
  **/
 


    /**
       Ciclo che scorre tutte le azioni della matrice di ordinamento
    **
       for any action contained in the matrix of the ordering constraints
    **/                                                                          
    for (ind = 0; ind < num_act_ord; ind++)
      {
	if (GpG.constraint_type==0) 
	  /** 
	      Gestione di ordinamento per azioni istantanee
	      **
	      Management of ordering contraints for instantaneous actions
	  **/
	  {
	    if (mat_ord[ind][infAction->ord_pos] == 1)
	      if (max_time < act_ord_vect[ind]->time_f)
		/** 
		   Calcolo del massimo istante di tempo in cui
		   terminano le azioni mutex che devono precedere
		   infAction
		   **
		   Compute the maximum time at which the mutex actions 
		   that have to precede infAction, end
		**/                        
		{
		  max_time = act_ord_vect[ind]->time_f;
		  infAction->action_f = act_ord_vect[ind];
		}
	  }
	else
	  {

	  /**
             tipi di vincolo di ordinamento per azioni durative, sia A
	     un'azione gia' inserita a un livello inferiore all'azione
	     che stiamo inserendo B
	  **
	     types of ordering constraints for durative actions.
	     Supposing A an action of the TDA-graph at a level lower
	     than the level of the action added to the TDA-graph in
	     this search step
	  **/                                                                 


	    if (mat_ord[ind][infAction->ord_pos] == EA_SB) 
	      /** 
		  l'azione B deve iniziare dopo la fine dell'azione A
		  **
		  the action B begins after the end of the action A
	      **/
	      {
		if (max_time < act_ord_vect[ind]->time_f)
		  {
		    max_time = act_ord_vect[ind]->time_f;
		    infAction->action_f = act_ord_vect[ind];
		  }
	      }
	      else 
	      {
		if (mat_ord[ind][infAction->ord_pos] == EA_EB) 
		  /** 
		      l'azione B deve finire dopo la fine di A
		      **
		      the action B ends after the end of the action A 
		  **/
		  {
		    if (max_time < act_ord_vect[ind]->time_f - get_action_time (infAction->position, level) )
		      {
			max_time = act_ord_vect[ind]->time_f - get_action_time (infAction->position, level);
			infAction->action_f = act_ord_vect[ind];
		      }
		  }
		else
		  if (mat_ord[ind][infAction->ord_pos] == SA_SB) 
		    /** 
			l'azione B deve iniziare dopo l'inizio di A
		     **
		        the action B begins after the beginning of the action A
		    **/
		    {
		      if (max_time < act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level ) )
			{
			  max_time = act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level );
			  infAction->action_f = act_ord_vect[ind];
			}
		    }
		  else
		    {
		      if (mat_ord[ind][infAction->ord_pos] == SA_EB) 
			/** 
			    l'azione B deve finire dopo l'inizio di A
			 **
			    The action B ends after the beginning of A 
			**/
			{
			  if (max_time < act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level )- get_action_time (infAction->position, level)  )
			    {
			      max_time = act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level ) - get_action_time (infAction->position, level) ;
			      infAction->action_f = act_ord_vect[ind];
			    }
			}
		      else
			{
			  if (mat_ord[ind][infAction->ord_pos] == EA_EB__SA_SB)
			    /**
			       Tra A e B vi e' un vincolo di
			       ordinamento sia di tipo EA_EB che di
			       tipo SA_SB.  Il vincolo piu'
			       restrittivo dipende dalla durata
			       dell'azione
			       **
			       There is an ordering constraint of type both
			       EA_EB and SA_SB. The most strong constraint
			       depends on the durations of the actions
			    **/
			    {
			      if(get_action_time(infAction->position, level ) < get_action_time(act_ord_vect[ind]->position, *act_ord_vect[ind]->level ))
				{
				  // EA_EB
				  if (max_time < act_ord_vect[ind]->time_f - get_action_time (infAction->position, level) )
				    {
				      max_time = act_ord_vect[ind]->time_f - get_action_time (infAction->position, level);
				      infAction->action_f = act_ord_vect[ind];
				    }
				}
			      else // SA_SB
				{
				  if (max_time < act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level ) )
				    {
				      max_time = act_ord_vect[ind]->time_f - get_action_time (act_ord_vect[ind]->position, *act_ord_vect[ind]->level );
				      infAction->action_f = act_ord_vect[ind];
				    }
				}
			    }
			  
			}
			
		    }
	      }
	  }
      }

#ifdef __TEST__
  else
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else 
  printf( WAR_BUG );
#endif  
#endif


  if(GpG.timed_facts_present && GET_BIT(GpG.has_timed_preconds, infAction -> position))
    {
      save_time = max_time;

      max_time = find_temporal_interval (max_time, infAction, NULL);
      /*
      printf("\nTime returned by find_temporal_interval %.2f",max_time);
      */
      if (max_time < 0.0) 
	{
	  max_time = save_time;	  

	  /** 
	     Calcoliamo l'istante finale dell'azione inserita 
	     **
	     Compute the end time of the examined action
	  **/
	   infAction->time_f = max_time + get_action_time (infAction->position, level);
	   
	}
    }

  /**
     Calcoliamo l'istante finale dell'azione inserita dato dalla somma
     dell'istante di inizio precedentemente calcolato e la durata
     dell'azione
     **
     We compute the end time of the esamined action as the sum between
     the start time previously computed and the duration of the action
  **/

  infAction->time_f = max_time + get_action_time (infAction->position, level);

  if (DEBUG4)
    printf("\n ---Compute Act: %s, level %d\n    start_time %.2f, end_time %.2f",
       print_op_name_string (infAction->position, temp_name), level, max_time,
       infAction->time_f);

    /**
       Istante temporale a cui vengono supportati gli effetti additivi
    **
       Temporal value at which the additive effects are achieved
    **/
    
    /**
       Effetti AT_END
    **
       AT_END Effects
    **/                                                                            

  for (j = 0; j < gef_conn[infAction->position].num_A; j++)
    {
      /**
	 intero corrispondente all'effetto additivo dell'azione
	 **
	 integer corresponding to the additive effect of the action
      **/                                                                        
      cel = gef_conn[infAction->position].A[j];

      if (cel < 0)
	continue;
      /**
	 Ricava la struttura NODE associata al fatto
      **
	 Compute the NODE structure corresponding to the fact node
      **/                                                                        
      add_effect = CONVERT_FACT_TO_NODE (cel, next_level);

      /**
	 Se il fatto e' un effetto cancellante AT_START allora
	 togliamo l'istante dalla rispettiva NOOP
      **
	 If the fact is an AT_START delete effect, then we remove the
	 time from the respective NOOP node
      **/                                                                        

      if (is_fact_in_delete_effects_start (infAction->position, cel))
	{
	  CONVERT_NOOP_TO_NODE (cel, level)->time_f = NOTIME;
	  CONVERT_NOOP_TO_NODE (cel, level)->action_f = NULL;
	}


      /**
	 Se il fatto e' supportato solamente dall'azione che si sta
	 inserendo oppure ha un istante maggiore dell' azione inserita
	 allora aggiorniamo subito l'istante assegnando all'stante di
	 tempo dell'effetto additivo quello dell'azione
	 **
	 If the fact f is supported only by the action A that is added
	 to the TDA-graph in this search step or it has a time value
	 greater than those of A, then we update the time of f with
	 the time of the additive effect of A
      **/

      if (add_effect->w_is_true == 1 || 
	  add_effect->time_f == NOTIME ||
	  add_effect->time_f > infAction->time_f)
	{
	  /**
	    Memorizziamo nella struttura fatto l'azione a cui e'
	    dovuto e il suo istante di tempo
	  **
	    We store a pointer to the action for which the time of f
	    is due in the fact node f
         **/                                                                     
	  add_effect->time_f = infAction->time_f;
	  add_effect->action_f = infAction;

	  if (DEBUG4)
	    printf ("\n\t-Compute End_eff: %s, level %d, time %.2f", print_ft_name_string (cel, temp_name), next_level, add_effect->time_f);

	  /**
	     Se il fatto e' precondizione dell'azione al livello
	     successivo allora viene inserita nella propagation_list
	     **
	     If the fact is precondition of an action at the next
	     level, then we add it in the propagation_list
	  **/
	  if (GET_ACTION_OF_LEVEL (next_level)->w_is_used
	      &&(is_fact_in_preconditions(vectlevel[next_level]->action.position, add_effect->position)
	       ||(is_fact_in_preconditions_overall(vectlevel[next_level]->action.position, add_effect->position)
		  && !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
	    insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));

	  /**
	     Propaghiamo in avanti il nuovo istante temporale
	     **
	     We propagate the time value in the following levels 
	  **/
	  if (CONVERT_NOOP_TO_NODE (cel, next_level)->w_is_used)
	    forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(cel, next_level));
	}
    }

  /**
     Azione durativa
     **
     Durative Actions
  **/
  if (gef_conn[infAction->position].sf != NULL)

    /**
       Effetti additivi AT_START
       **
       AT_START additive effects
    **/
    for (j = 0; j < gef_conn[infAction->position].sf->num_A_start; j++)
      {
	cel = gef_conn[infAction->position].sf->A_start[j];

	if (cel < 0)
	  continue;


	add_effect = CONVERT_FACT_TO_NODE (cel, next_level);
	infNoop = CONVERT_NOOP_TO_NODE (cel, level);

	/**
	   Se la NOOP non ha istante temporale oppure ha un istante
	   temporale maggiore allora aggiorniamo subito l'istante
	   **
	   If the NOOP has not time value or it has a temporal value
	   greater than the start time of the action, then we update
	   the time value of the no-op node using the start time of the
	   action
	**/
	if (infNoop->time_f < 0 || infNoop->time_f > (infAction->time_f - get_action_time (infAction->position, level)))
	  infNoop->time_f = infAction->time_f - get_action_time (infAction->position, level);

	/**
	   Se il fatto non e' negli effetti cancellanti AT_END...
	   **
	   If the fact is not an AT_END delete effect...
	**/
	if (!is_fact_in_delete_effects (infAction->position, cel))
	  {
	    add_effect->time_f = infNoop->time_f;
	    add_effect->action_f = infNoop->action_f;

	    if (DEBUG4)
	      printf ("\n\t-Compute Start_eff: %s, level %d, time %.2f", print_ft_name_string (cel, temp_name), next_level, add_effect->time_f);

	    /**
	       Se il fatto e' precondizione dell'azione al livello
	       successivo allora viene inserita nella propagation_list
	       **
	       If the fact is a precondition of the action at the next
	       level, then we add it in the propagation list
	    **/
	    if (GET_ACTION_OF_LEVEL (next_level)->w_is_used
		&& (is_fact_in_preconditions(vectlevel[next_level]->action.position,add_effect->position)
		   || (is_fact_in_preconditions_overall(vectlevel[next_level]->action.position,add_effect->position)
		       && !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position, add_effect->position))))
	      insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));

	    /**
	       Propaghiamo in avanti il nuovo istante temporale
	       **
	       We propagate the time value in the following levels
	    **/
	    if (CONVERT_NOOP_TO_NODE (cel, next_level)->w_is_used)
	      forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(cel, next_level));

	  }

      }

  /**
     Inseriamo nella propagation_list tutte le azioni ordinate dopo
     l'azione inserita
     **
     We add each ordered with the examined action in the propagation
     list
  **/
  for (ind = 0; ind < num_act_ord; ind++)
    if (GpG.constraint_type==0)
      {
	if (mat_ord[infAction->ord_pos][ind] == 1)
	  insert_propagation_list (act_ord_vect[ind]);
      }
    else
      {
	if (mat_ord[infAction->ord_pos][ind] != 0)
	  insert_propagation_list (act_ord_vect[ind]);
      }


#ifdef __TEST__
  else
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else 
  printf( WAR_BUG );
#endif  
#endif

  /**
     Aggiorna gli istanti temporali delle azioni inserite nella
     propagation_list
     **
     Update the temporal values of the action added in the propagation
     list
  **/
  time_adj (infAction);


#ifdef __TEST__
  check_prop_level_index ();
  check_matrix ();
  check_act_ord_vect ();
#endif

}


/**
   E' chiamata da insert_remove_action durante la cancellazione di
   un'azione.  Deve stabilire a quali istanti temporali i fatti che
   supportava vengono resi veri
   **
   It is called by insert_time during the action deleting.
**/
void update_time (ActNode_list infAction)
{
  float savetime = 0.0;
  int ind, level, next_level, cel, j;
  FctNode_list add_effect = NULL, infEl;
  NoopNode_list infNoop;
  ActNode_list saveact = NULL;

#ifdef __TEST__
  EfConn *act = NULL;
#endif

  //  reset_propagation_vect();

  if (GpG.timed_facts_present)
    {
      if (infAction -> PC_interval)
	/* 
	   Rimuovo i timed fact che sono precondizioni di quest'azione
	   dall'array dei fatti temporali non supportati 
	*/
	remove_all_unsup_tmd_of_act(infAction);
    }

  level = *infAction->level;
  next_level = level + 1;

  if (DEBUG4)
    printf("\n ---Delete Act: %s, level %d\n     start_time %.2f, end_time %.2f", print_op_name_string (infAction->position, temp_name), level,
	   infAction->time_f - get_action_time (infAction->position, level), infAction->time_f);

  /**
     Azzeriamo l'istante finale dell'azione
     **
     Reset the time value of the action examined
  **/
  infAction->time_f = 0.0;
  infAction->action_f = NULL;

  /**
     Inseriamo nella propagation_list tutte le azioni ordinate dopo
     l'azione da rimuovere
     **
     Insert each ordered action with the removing action in the
     propagation list
  **/

  for (ind = 0; ind < num_act_ord; ind++)
    if (GpG.constraint_type == 0)
      {
	if (mat_ord[infAction->ord_pos][ind] == 1)
	  insert_propagation_list (act_ord_vect[ind]);
      }
    else
      {
	if (mat_ord[infAction->ord_pos][ind] != 0)
	  insert_propagation_list (act_ord_vect[ind]);
      }
  /**
     Rimuoviamo i vincoli di ordinamento
     **
     Remove the ordering constraint
  **/
    remove_temporal_constraints (infAction->ord_pos);

    /**
       Gli istanti delle precondizioni non supportate vengono
       annullati
       **
       Reset the time values of the not supported preconditions 
    **/

  /** 
     Precondizioni AT_START
     **
     AT_START preconditions
  **/
  for (j = 0; j < gef_conn[infAction->position].num_PC; j++)
    {
      cel = gef_conn[infAction->position].PC[j];

      if (cel < 0)
	continue;

      infEl = CONVERT_FACT_TO_NODE (cel, level);

      if (infEl->w_is_true <= 0)
	{
	  infEl->time_f = NOTIME;
	  infEl->action_f = NULL;
	}
    }

  /**
     Precondizioni OVERALL
     **
     OVERALL preconditions
  **/
  if (gef_conn[infAction->position].sf)
    for (j = 0; j < gef_conn[infAction->position].sf->num_PC_overall; j++)
      {
	cel = gef_conn[infAction->position].sf->PC_overall[j];

	if (cel < 0)
	  continue;

	infEl = CONVERT_FACT_TO_NODE (cel, level);

	if (infEl->w_is_true <= 0)
	  {
	    infEl->time_f = NOTIME;
	    infEl->action_f = NULL;
	  }
      }

  /**
     Precondizioni AT_END
     **
     AT_END preconditions
  **/
  if (gef_conn[infAction->position].sf)
    for (j = 0; j < gef_conn[infAction->position].sf->num_PC_end; j++)
      {
	cel = gef_conn[infAction->position].sf->PC_end[j];

	if (cel < 0)
	  continue;
	
	infEl = CONVERT_FACT_TO_NODE (cel, level);

	if (infEl->w_is_true <= 0)
	  {
	    infEl->time_f = NOTIME;
	    infEl->action_f = NULL;
	  }
      }


  /* 
     Reinizializzo il puntatore all'azione da cui dipende l'istante di
     tempo dell'azione in esame
     *
     For the fact node f, reset the pointer of the action for which
     depends the time value of f
  */
  infAction->action_f = NULL;

 
  /* 
     rimuove l'azione dalla lista delle azioni associate all'intervallo
  */
  if(GpG.timed_facts_present && GET_BIT(GpG.has_timed_preconds, infAction -> position))
    {
      update_timed_vect_data(infAction -> PC_interval, infAction->level, C_T_REMOVE_ACTION);
      //      update_timed_vect_data(&infAction -> PC_interval, C_T_REMOVE_ACTION);
      
    }



  /**
     Istante temporale a cui vengono supportati gli effetti additivi
     **
     Temporal instant at which the additive effects are supported
  **/

  /**
     Effetti AT_END
     **
     AT_END effects
  **/
  for (j = 0; j < gef_conn[infAction->position].num_A; j++)
    {
      cel = gef_conn[infAction->position].A[j];

      if (cel < 0)
	continue;

      add_effect = CONVERT_FACT_TO_NODE (cel, next_level);


      savetime = add_effect->time_f;
      saveact = add_effect->action_f;

      infNoop = CONVERT_NOOP_TO_NODE (cel, level);

      // DEL_START - ADD_END
      if (is_fact_in_delete_effects_start (infAction->position, cel))
	{
	  /**
	     Se il fatto al livello precedente e' vero allora il suo
	     istante temporale viene assegnato alla NOOP e al fatto al
	     livello successivo
	     **
	     If the fact f is supported at the previous level of the
	     TDA-graph, then we assign the time value of f to either
	     the no-op node and the fact node at the next level
	  **/
	  if (CONVERT_FACT_TO_NODE (cel, level)->w_is_true)
	    {
	      infNoop->time_f = CONVERT_FACT_TO_NODE (cel, level)->time_f;
	      infNoop->action_f = CONVERT_FACT_TO_NODE (cel, level)->action_f;

	      add_effect->time_f = infNoop->time_f;
	      add_effect->action_f = infNoop->action_f;

	    }
	  else
	    {

	      /**
		 Il fatto al livello precedente e' falso
		 **
		 The fact is not supported at the previous level of the 
		 TDA-graph
	      **/

	      add_effect->time_f = NOTIME;
	      add_effect->action_f = NULL;
	    }
	}
      else
	{ // NOT_DEL_START - ADD_END
	  /**
	     Se e' inserita la NOOP allora il suo istante finale e'
	     assegnato al fatto
	     **
	     If the no-op node is in the TDA-graph, then we assign its
	     end time to the fact node
	  **/
	  if (infNoop->w_is_used > 0)
	    {
	      add_effect->time_f = infNoop->time_f;
	      add_effect->action_f = infNoop->action_f;

	    }
	  else
	    {
	      /**
		 La NOOP non e' inserita
		 **
		 The NOOP is in the TDA-graph
	      **/

	      add_effect->time_f = NOTIME;
	      add_effect->action_f = NULL;
	    }

	} //end else

     /**
	 Se l'istante del fatto e' cambiato...
	 **
	 If the time value of the fact is changed...
      **/
      if (savetime != add_effect->time_f || saveact != add_effect->action_f || 
	  savetime == Hvar.dg_facts_min_duration[add_effect->position])
	{
	  /**
	     Propaghiamo in avanti il nuovo istante temporale
	     **
	     We propagate the time value in the following levels
	  **/
	  if (add_effect->time_f >= 0)
	    forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(add_effect->position, next_level));

	  /**
	     Se il fatto e' precondizione dell'azione al livello
	     successivo allora viene inserita nella propagation_list
	     **
	     If the fact is precondition of the action at the next
	     level, then we add it in the propagation_list
	  **/
	  if ( (savetime != add_effect->time_f || 
		saveact != add_effect->action_f) && 
	       GET_ACTION_OF_LEVEL (next_level)->w_is_used
	       && (is_fact_in_preconditions(vectlevel[next_level]->action.position, add_effect->position)
		   ||(is_fact_in_preconditions_overall(vectlevel[next_level]->action.position, add_effect->position)
		      && !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
	    insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));
	}

      if (DEBUG4)
	printf ("\n\t-Delete End_eff: %s, level %d, time %.2f, true %d", print_ft_name_string (cel, temp_name), next_level,
		add_effect->time_f, add_effect->w_is_true);
    }


  /**
     Azioni durative
     **
     Durative Actions
  **/
  if (gef_conn[infAction->position].sf != NULL)

    /** 
	Effetti AT_START
	**
	AT_START effects
    **/
    for (j = 0; j < gef_conn[infAction->position].sf->num_A_start; j++)
      {
	cel = gef_conn[infAction->position].sf->A_start[j];

	if (cel < 0)
	  continue;

	add_effect = CONVERT_FACT_TO_NODE (cel, next_level);

	savetime = add_effect->time_f;
	saveact = add_effect->action_f;

	infNoop = CONVERT_NOOP_TO_NODE (cel, level);

	// ADD_START - DEL_END
	if (is_fact_in_delete_effects (infAction->position, cel))
	  {
	    /**
	       Se il fatto al livello precedente e' vero allora il suo
	       istante temporale viene assegnato alla NOOP e al fatto
	       al livello successivo
	       **
	       If the fact f at the previous level is supported, then
	       we assign the time value of f to either the no-op node
	       and the fact node at the next level
	    **/
	    if (CONVERT_FACT_TO_NODE (cel, level)->w_is_true)
	      {
		infNoop->time_f = CONVERT_FACT_TO_NODE (cel, level)->time_f;
		infNoop->action_f = CONVERT_FACT_TO_NODE (cel, level)->action_f;

		add_effect->time_f = infNoop->time_f;
		add_effect->action_f = infNoop->action_f;

	      }
	    /**
	       Il fatto al livello precedente e' falso
	       **
	       The fact at the previous level is not supported
	    **/
	    else
	      {
		infNoop->time_f = NOTIME;
		infNoop->action_f = NULL;
	      }
	  } // end ADD_START - DEL_END
	else
	  {
	    // ADD_START - NOT_DEL_END

	    /**
	       Se il fatto al livello precedente e' vero allora il suo
	       istante temporale viene assegnato alla NOOP e al fatto
	       al livello successivo
	       **
	       If the fact f at the previous level is supported, then
	       we assign the time value of f to either the no-op node
	       and the fact node at the next level
	    **/
	    if (CONVERT_FACT_TO_NODE (cel, level)->w_is_true)
	      {
		infNoop->time_f = CONVERT_FACT_TO_NODE (cel, level)->time_f;
		infNoop->action_f = CONVERT_FACT_TO_NODE (cel, level)->action_f;

		add_effect->time_f = infNoop->time_f;
		add_effect->action_f = infNoop->action_f;

	      }
	    else
	      {
		/**
		   Il fatto al livello precedente e' falso
		   **
		   The fact at the previous level is not supported
		**/

		infNoop->time_f = NOTIME;
		infNoop->action_f = NULL;

		add_effect->time_f = NOTIME;
		add_effect->action_f = NULL;
	      }

	  }

	/**
	   Se l'istante del fatto e' cambiato...
	   **
	   If the time value of the fact node is changed...
	**/
	if ( (savetime != add_effect->time_f || 
	      saveact != add_effect->action_f) ||
	     savetime == Hvar.dg_facts_min_duration[add_effect->position])
	  {
	    /**
	       Propaghiamo in avanti il nuovo istante temporale
	       **
	       We propagate the time value in the following levels
	    **/
	    if (add_effect->time_f >= 0)
	      forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(add_effect->position, next_level));

	    /**
	       Se il fatto e' precondizione dell'azione al livello
	       successivo allora viene inserita nella propagation_list
	       **
	       If the fact is precondition of the action at the next
	       level, then we add it in the propagation_list
	    **/

	    if ( (savetime != add_effect->time_f || 
		  saveact != add_effect->action_f)
		 && GET_ACTION_OF_LEVEL (next_level)->w_is_used
		 && (is_fact_in_preconditions(vectlevel[next_level]->action.position, add_effect->position)
		     ||(is_fact_in_preconditions_overall(vectlevel[next_level]->action.position, add_effect->position)
			&& !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
	      insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));

	  }

	if (DEBUG4)
	  printf ("\n\t-Delete Start_eff: %s, level %d, time %.2f, true %d", print_ft_name_string (cel, temp_name), next_level,
		  add_effect->time_f, add_effect->w_is_true);
      }

  if (gef_conn[infAction->position].sf != NULL)
    /**
       Effetti canceelant AT_START
       **
       AT_START cancelling effects
    **/
    for (j = 0; j < gef_conn[infAction->position].sf->num_D_start; j++)
      {
	cel = gef_conn[infAction->position].sf->D_start[j];

	if (cel < 0)
	  continue;

	if (is_fact_in_additive_effects (infAction->position, cel))
	  continue;

	add_effect = CONVERT_FACT_TO_NODE (cel, next_level);
	
	savetime = add_effect->time_f;
	saveact = add_effect->action_f;

	// DEL_START - NOT_ADD_END

	/**
	   Se il fatto al livello precedente e' vero allora il suo
	   istante temporale viene assegnato alla NOOP e al fatto al
	   livello successivo
	   **
	   If the fact f at the previous level is supported, then we
	   assign the time value of f to either the no-op node and the
	   fact node at the next level
	**/
	if (CONVERT_FACT_TO_NODE (cel, level)->w_is_true)
	  {

	    infNoop = CONVERT_NOOP_TO_NODE (cel, level);

	    infNoop->time_f = CONVERT_FACT_TO_NODE (cel, level)->time_f;
	    infNoop->action_f = CONVERT_FACT_TO_NODE (cel, level)->action_f;

	    add_effect->time_f = infNoop->time_f;
	    add_effect->action_f = infNoop->action_f;

	  }

	/**
	   Se l'istante del fatto e' cambiato...
	   **
	   If the time value is changed...
	**/
	if (savetime != add_effect->time_f || 
	    saveact != add_effect->action_f || 
	    savetime == Hvar.dg_facts_min_duration[add_effect->position])
	  {
	    /**
	       Propaghiamo in avanti il nuovo istante temporale
	       **
	       We propagate the time value in the following levels
	    **/
	    if (add_effect->time_f >= 0)
	      forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(add_effect->position, next_level));

	    /**
	       Se il fatto e' precondizione dell'azione al livello
	       successivo allora viene inserita nella propagation_list
	       **
	       If the fact is a precondition of the action at the next
	       level, then we add it in the propagation list
	    **/
	    if ( (savetime != add_effect->time_f  || 
		  saveact != add_effect->action_f)
		 && GET_ACTION_OF_LEVEL (next_level)->w_is_used
		 && (is_fact_in_preconditions(vectlevel[next_level]->action.position,add_effect->position)
		     ||(is_fact_in_preconditions_overall(vectlevel[next_level]->action.position,add_effect->position)
			&& !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
	      insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));
	    
	  }

      }


  /**
     effetti cancellanti AT-END 
     ** 
     AT_END delete effects
  **/
  for (j = 0; j < gef_conn[infAction->position].num_D; j++)
    {
      cel = gef_conn[infAction->position].D[j];

      if (cel < 0)
	continue;

      //  NOT_ADD_START - DEL_END
      if (is_fact_in_additive_effects_start (infAction->position, cel))
	continue;

      infNoop = CONVERT_NOOP_TO_NODE (cel, level);

      add_effect = CONVERT_FACT_TO_NODE (cel, next_level);
      
      savetime = add_effect->time_f;
      saveact = add_effect->action_f;

      /**
	 Se la NOOP e' inserita allora propaghiamo il suo istante al fatto
	 **
	 If the no-op node is in the TDA-graph, then we assign its
	 time value to the fact node at the next level
      **/
      if (infNoop->w_is_used)
	{

	  add_effect->time_f = infNoop->time_f;
	  add_effect->action_f = infNoop->action_f;

	}

      /**
	 Se l'istante del fatto e' cambiato...
	 **
	 If the time value of the fact node is changed...
      **/
      if ((savetime != add_effect->time_f || 
	   saveact != add_effect->action_f) || 
	  savetime == Hvar.dg_facts_min_duration[add_effect->position])
	{
	  /**
	     Propaghiamo in avanti il nuovo istante temporale
	     **
	     We propagate the time value in the following levels
	  **/
	  if (add_effect->time_f >= 0)
	    forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(add_effect->position, next_level));

	  /**
	     Se il fatto e' precondizione dell'azione al livello
	     successivo allora viene inserita nella propagation_list
	     **
	     If the fact is a precondition of the action at the next
	     level, then we add it in the propagation list
	  **/
	  if ( (savetime != add_effect->time_f || 
		saveact != add_effect->action_f)
	       && GET_ACTION_OF_LEVEL (next_level)->w_is_used
	       &&(is_fact_in_preconditions(vectlevel[next_level]->action.position, add_effect->position)
		  ||(is_fact_in_preconditions_overall(vectlevel[next_level]->action.position, add_effect->position)
		     && !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
	    insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));
	  
	}
      
    }

/**
   Aggiorna gli istanti temporali delle azioni inserite nella
   propagation_list
   **
   Update the temporal value of the action added in the propagation
   list
**/
time_adj (infAction);

#ifdef __TEST__
  check_prop_level_index ();
  check_matrix ();
  check_act_ord_vect ();
#endif

}



/**
   E' richiamata da remove_noop; ha il compito di aggiornare il tempo
   della noop
   **
   It is called by remove_noop; it updates the time value of the no-op node
**/

void
noop_remotion_time (NoopNode_list infNoop)
{

  float savetime = 0.0;
  int level, next_level, cel;
  FctNode_list add_effect = NULL;
  ActNode_list infSaved;
  ActNode_list saveact;

  level = *infNoop->level;
  next_level = level + 1;

  cel = infNoop->position;

  infSaved =  infNoop->action_f;

  /**
     Se il fatto e' negli effetti cancellanti dell'azione allora viene
     tolto l'istante temporale
     **
     If the fact is in a delete effect of the action, then 
     we remove its temporal value 
  **/
  if (!is_fact_in_delete_effects (GET_ACTION_POSITION_OF_LEVEL (level), cel))
    {
      infNoop->time_f = NOTIME;
      infNoop->action_f = NULL;
    }
#ifdef __TEST__
  printf ("\nRemove noop time: %s in level %d at time %.2f",
	  print_noop_name_string (infNoop->position, temp_name), level,infNoop->time_f);
#endif

  add_effect = CONVERT_FACT_TO_NODE (cel, next_level);

  /**
     Se l'istante del fatto era dato dalla NOOP...
     **
     If the time value of the fact node is given by the no-op node...
  **/
  if (add_effect->action_f == infSaved)
    {
      savetime = add_effect->time_f;
      saveact = add_effect->action_f;
	  
      /**
	 Se il fatto e' falso allora togliamo il suo istante temporale
	 **
	 If the fact is not supported, then we remove its temporal
	 instant
      **/
      if (add_effect->w_is_true < 1)
	{
	  add_effect->time_f = NOTIME;
	  add_effect->action_f = NULL;
	}
      else
	{
	  /**
	     Se il fatto e' vero allora il suo istante temporale e'
	     uguale all'istante finale dell'azione
	     **
	     If the fact is supported, then its temporal value is
	     equal to the end time of the action
	  **/

	  if (CHECK_ACTION_OF_LEVEL (level) && is_fact_in_additive_effects (GET_ACTION_POSITION_OF_LEVEL(level), cel))
	    {

	      add_effect->time_f = GET_ACTION_OF_LEVEL (level)->time_f;
	      add_effect->action_f = GET_ACTION_OF_LEVEL (level);
	    }
	}

      /**
	 Se l'istante del fatto e' cambiato...
	 **
	 If the time value of the fact is changed...
      **/
      if (savetime != add_effect->time_f || saveact != add_effect->action_f)
	{

	  /**
	     Se il fatto e' precondizione dell'azione al livello
	     successivo allora viene inserita nella propagation_list
	     **
	     If the fact is precondition of the action at the next
	     level then we add it in the propagation list
	  **/
	  if (GET_ACTION_OF_LEVEL (next_level)->w_is_used
	      &&(is_fact_in_preconditions(vectlevel[next_level]->action.position, add_effect->position)
		 ||(is_fact_in_preconditions_overall(vectlevel[next_level]->action.position, add_effect->position)
		    && !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
	    insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));

	  GpG.forward_time = 1;

	}
      else
	GpG.forward_time = 0;
#ifdef __TEST__
      printf("\nRemove fact time: %s in level %d at time %.2f true/false: %d",
	     print_ft_name_string (cel, temp_name), next_level,add_effect->time_f, add_effect->w_is_true);
#endif

    }
  else
    GpG.forward_time = 0;

}





/**
   Propaga l'istante temporale di un fatto nei livelli successivi
   tramite NOOP
   **
   Propagate the time value of a fact node in the following levels
   through the no-op nodes
**/
void forward_noop_propagation_time (NoopNode_list infNoop)
{

  register FctNode_list add_effect;
  register NoopNode_list infTemp;
  register ActNode_list infAction, infSaved;
  ActNode_list saveact;

  register int cel, indbreak;
  int level, next_level, position_noop;
  float savetime;


  level = *infNoop->level;
  next_level = level + 1;
  position_noop = infNoop->position;

  if (position_noop < 0)
    return;


  for (infTemp = infNoop; infTemp->w_is_used > 0;
       infTemp = &vectlevel[level]->noop_act[position_noop])
    {

      infAction = GET_ACTION_OF_LEVEL (level);

      cel = infTemp->position;

      infTemp->time_f = CONVERT_FACT_TO_NODE (cel, level)->time_f;

      infSaved = infTemp->action_f;
      infTemp->action_f = CONVERT_FACT_TO_NODE (cel, level)->action_f;

      /**
	 Se il fatto e' negli affetti additivi AT_START dell'azione
	 nel livello allora l'istante della NOOP e' uguale all'istante
	 iniziale dell'azione
	 **
	 If the fact is an AT_START additive effects of the action in
	 the current level, then the NOOP time value is equal to the
	 start time of the action
      **/
      if (infAction->time_f !=NOTIME &&
	  is_fact_in_additive_effects_start (infAction->position, cel))
	{
	  infTemp->time_f =
	    infAction->time_f - get_action_time (infAction->position, level);
	  infTemp->action_f = infAction;
	}
      /**
	 Se il fatto al livello inferiore ha un istante minore
	 dell'istante della NOOP allora l'istante della NOOP e' uguale
	 all'istante del fatto
	 **
	 If the fact at the previous level has a time value lower than
	 the no-op time value, then the no-op time value is equal to
	 the fact time value
      **/
      if (CONVERT_FACT_TO_NODE (cel, level)->w_is_true > 0 && CONVERT_FACT_TO_NODE (cel, level)->time_f >= 0)
	if (CONVERT_FACT_TO_NODE (cel, level)->time_f < infTemp->time_f)
	  {
	    infTemp->time_f = CONVERT_FACT_TO_NODE (cel, level)->time_f;
	    infTemp->action_f = CONVERT_FACT_TO_NODE (cel, level)->action_f;
	  }
      add_effect = CONVERT_FACT_TO_NODE (cel, next_level);

#ifdef __TEST__
      printf ("\nForward propagation noop time: %s in level %d at time %.2f",
	 CONVERT_NOOP_TO_VERTEX (infTemp->position)->name, level, infTemp->time_f);
#endif

      indbreak = 1;

      /**
	 Se il fatto non e' negli effetti cancellanti AT_END...
	 **
	 If the fact is not an AT_END delete effect
      **/
      if (infTemp->w_is_overall != ADD_DEL && infTemp->w_is_overall != NADD_DEL)
	{

	  /**
	     Se il fatto ha istante maggiore dell'istante della NOOP
	     allora l'istante del fatto e' uguale all'istante della
	     no-op
	     **
	     If the fact has a time value greater than the time of the
	     no-op, then the time of the fact is equal to the time
	     of the no-op
	  **/
	  if ((add_effect->time_f > infTemp->time_f && infTemp->time_f >= 0.0) || add_effect->w_is_true == 1 || add_effect->time_f == NOTIME)
	    {
	      add_effect->time_f = infTemp->time_f;
	      add_effect->action_f = infTemp->action_f;

	      /**
		 Se il fatto e' precondizione dell'azione al livello
		 successivo allora viene inserita nella
		 propagation_list
		 **
		 If the fact is a precondition of the action at the
		 next level, then we add it in the propagation list
	      **/
	      if (GET_ACTION_OF_LEVEL (next_level)->w_is_used
		  && (is_fact_in_preconditions(vectlevel[next_level]->action.position, add_effect->position)
		      ||(is_fact_in_preconditions_overall(vectlevel[next_level]->action.position,add_effect->position)
			 && !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
		insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));

	      /**
		 Possiamo proseguire nel livello superiore
		 **
		 We continue in the next level of the TDA-graph
	      **/
	      indbreak = 0;
	    }
	  else
	    /**
	       Se l'istante temporale del fatto era dato dalla NOOP
	       allora cerchiamo l'istante minore a cui si puo'
	       supportare
	       **
	       If the temporal instant of the fact f is given by the
	       no-op node, then we compute the smallest time value at
	       which f can be supported by the action in the current plan
	    **/
	  if (add_effect->action_f == infSaved)
	    {
	      savetime = add_effect->time_f;
	      saveact = add_effect->action_f;

	      /**
		 Se la NOOP non ha istante temporale allora prendiamo
		 l'istante dell'azione
		 **
		 If the no-op node has not a time value, then we
		 assign the end time of the action to f
	      **/
	      if (infTemp->time_f < 0.0)
		{
		  add_effect->time_f = infAction->time_f;
		  add_effect->action_f = infAction;
		}

	      else
		{

		  add_effect->time_f = infTemp->time_f;
		  add_effect->action_f = infTemp->action_f;

		  /**
		     Se il fatto e' supportato anche dall'azione nel
		     livello ...
		     **
		     If the fact is supported also by the action in
		     the current level ...
		  **/
		  if (add_effect->w_is_true > 1)
		    {
		      infAction = GET_ACTION_OF_LEVEL (level);
		      if (infAction && infAction->time_f != NOTIME && infAction->w_is_used && is_fact_in_additive_effects (infAction->position, cel))

			/**
			   Se l'istante del fatto e' maggiore
			   dell'istante finale dell'azione allora
			   l'istante del fatto e' uguale all'istante
			   finale dell'azione
			   **
			   If the time value of the fact f is greater
			   than the end time of the action, then the
			   time value of f is equal to the end time of
			   the action
			**/
			if (add_effect->time_f == NOTIME ||
			    add_effect->time_f > infAction->time_f)
			  {
			    add_effect->time_f = infAction->time_f;
			    add_effect->action_f = infAction;
			  }

		    }
		}		// end else       

	      /**
		 Se l'istante del fatto e' cambiato...
		 **
		 If the time value of the fact is changed...
	      **/
	      if (savetime != add_effect->time_f || saveact != add_effect->action_f)
		{

		  /**
		     Se il fatto e' precondizione dell'azione al
		     livello successivo allora viene inserita nella
		     propagation_list
		     **
		     If the fact is precondition of the action at the
		     next level, then we add it in the
		     propagation list
		  **/
		  if (GET_ACTION_OF_LEVEL (next_level)->w_is_used
		      &&(is_fact_in_preconditions(vectlevel[next_level]->action.position,add_effect->position)
			 ||(is_fact_in_preconditions_overall(vectlevel[next_level]->action.position,add_effect->position)
			    && !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
		    insert_propagation_list (GET_ACTION_OF_LEVEL(next_level));

		  /**
		     Possiamo proseguire nel livello superiore
		     **
		     We continue in the next level of the TDA-graph
		  **/
		  indbreak = 0;
		}
	    }  //end else
	}  //end if AT_END delete effects


      if (indbreak == 1)
	break;

      /** 
	  salgo di livello
	  **
	  increase level
       **/
      level++;
      next_level++;

    }

}



/**
   Propaga l'istante temporale nullo di un fatto nei livelli
   successivi tramite NOOP
   **
   Remove the time value of a fact from the following levels of the
   TDA-graph through no-op nodes
**/
void forward_noop_remotion_time (NoopNode_list infNoop)
{

  float savetime = 0.0;
  int position_noop, level, next_level, cel;
  register NoopNode_list infTemp;
  register ActNode_list infAction, infSaved;
  register FctNode_list add_effect = NULL;
  ActNode_list saveact = NULL;
  

  level = *infNoop->level;
  next_level = level + 1;
  position_noop = infNoop->position;

  if (position_noop < 0)
    return;

  /**
     Se il fatto al livello successivo e' vero allora propaghiamo in
     avanti l'istante del fatto
     **
     If the fact at the next level is supported, then we propagate
     the time value of the fact in the following levels
  **/
  if (CHECK_ACTION_OF_LEVEL (level)
      &&((is_fact_in_additive_effects_start(vectlevel[level]->action.position, position_noop)
	  && !is_fact_in_delete_effects (vectlevel[level]->action.position,position_noop))
	 || is_fact_in_additive_effects (vectlevel[level]->action.position,position_noop)))
    {
      forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(position_noop, level));
      return;
    }


  for (infTemp = infNoop; infTemp->w_is_used > 0;infTemp = &vectlevel[level]->noop_act[position_noop])
    {

      cel = infTemp->position;

      add_effect = CONVERT_FACT_TO_NODE (cel, next_level);

      savetime = add_effect->time_f;
      saveact = add_effect->action_f;

      /**
	 Se il fatto e' un effetto additivo AT_START allora l'istante
	 della NOOP e'uguale all'istante iniziale dell'azione
	 **
	 If the fact is an AT_START additive effect of the action A at
	 the current level, then the time value of the no-op node is
	 equal to the start time of the action A
      **/
      if (CHECK_ACTION_OF_LEVEL (level) && is_fact_in_additive_effects_start (GET_ACTION_POSITION_OF_LEVEL(level), cel))
	{
	  infTemp->time_f = GET_ACTION_OF_LEVEL (level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL (level), level);
	  infTemp->action_f = GET_ACTION_OF_LEVEL (level);

	  /*
	    Se il fatto non e' negli effetti cancellanti allora
	    l'istante del fatto al livello successivo e' uguale
	    all'istante della NOOP
	    **
	    If the fact is not a delete effect, then the time value
	    of the fact at the next level is equal to the time value
	    of the no-op node at the current level
	  **/
	  if (!is_fact_in_delete_effects(GET_ACTION_POSITION_OF_LEVEL (level), cel))
	    {
	      add_effect->time_f = infTemp->time_f;
	      add_effect->action_f = infTemp->action_f;
	    }
	  else			// ADD_START - DEL-END
	    break;

	}

      else
	{


	  /** 
	     azioni non durative 
	     ** 
	     not durative actions 
	  **/
	  infTemp->time_f = NOTIME;

	  infSaved = infTemp->action_f;
	  infTemp->action_f = NULL;

#ifdef __TEST__
	  printf ("\nForward remotion noop timep: %s in level %d at time %.2f",
		  print_noop_name_string (infTemp->position, temp_name), level, infTemp->time_f);
#endif

	  /**
	     Se l'istante del fatto era dato dalla NOOP allora vediamo
	     se puo' avere un'istante dall'azione
	     **
	     If the time value of the fact node is given by the no-op,
	     then we consider the action time value
	  **/
	  if (add_effect->action_f == infSaved)
	    {

	      if (add_effect->w_is_true <= 1)
		{
		  add_effect->time_f = NOTIME;
		  add_effect->action_f = NULL;
		}
	      else
		{
		  infAction = GET_ACTION_OF_LEVEL (level);

		  /**
		     Se il fatto e' negli effetti additivi dell'azione
		     del livello allora l'istante del fatto e' uguale
		     all'istante finale dell'azione
		     **
		     If the fact is in the additive effects of the
		     action A at the current level, then the time
		     value of the fact is equal to the end time of the
		     action A
		  **/
		  if (infAction && infAction->w_is_used  && is_fact_in_additive_effects (infAction->position, cel))
		    {
		      add_effect->time_f = infAction->time_f;
		      add_effect->action_f = infAction;
		    }
		}     // end else

	    }	// end action_f==infSaved

	}	// end else durative actions


      /**
	 Se l'istante del fatto e' cambiato...
	 **
	 If the time value of the fact node is changed...
      **/
      if (savetime != add_effect->time_f || saveact != add_effect->action_f )
	{

	  /**
	     Se il fatto e' precondizione dell'azione al livello
	     successivo allora viene inserita nella propagation_list
	     **
	     If the fact is precondition of the action at the next
	     level, then we add it in the propagation list
	  **/
	  if (GET_ACTION_OF_LEVEL (next_level)->w_is_used
	      &&(is_fact_in_preconditions(vectlevel[next_level]->action.position, add_effect->position)
		 ||(is_fact_in_preconditions_overall(vectlevel[next_level]->action.position, add_effect->position)
		    && !is_fact_in_additive_effects_start (vectlevel[next_level]->action.position,add_effect->position))))
	    insert_propagation_list (GET_ACTION_OF_LEVEL (next_level));

	}
      else
	break;

      /**
	 Se il fatto al livello successivo e' vero allora ci fermiamo
	 **
	 If the fact at the next level is supported, then we stop the 
	 remotion of the time value
      **/
      if ((is_fact_in_additive_effects_start(vectlevel[next_level]->action.position, add_effect->position)
	   && !is_fact_in_delete_effects (vectlevel[next_level]->action.position, add_effect->position))
	  || is_fact_in_additive_effects (vectlevel[next_level]->action.position, add_effect->position))
	break;

#ifdef __TEST__
      printf ("\nRemove fact time: %s in level %d at time %.2f true/false: %d",
	 print_ft_name_string (cel, temp_name), next_level, add_effect->time_f, add_effect->w_is_true - 1);
#endif

      /** 
	  salgo di livello 
	  ** 
	  increase level
      **/
      level++;
      next_level++;

    }

  /**
     Se l'istante del fatto e' cambiato e il fatto non e' un goal
     allora possiamo propagare il suo istante ai livelli successivi
     **
     If the time value of the fact is changed and the fact is not a
     goal of the planning problem, then we propagate its time value at
     the following levels
  **/
  if ( ( savetime != add_effect->time_f || saveact != add_effect->action_f)
       && next_level < GpG.curr_plan_length)
    forward_noop_propagation_time (CONVERT_NOOP_TO_NODE(position_noop, next_level));
}




/* Ritorna la durata totale del piano */


/**
   Ritorna la durata totale del piano
   **
   Compute the plan makespan
**/
void get_total_time_plan ()
{

  int i;
  FctNode_list infGoal;
  float max_time;


  max_time = 0.0;

  if(GpG.total_time_goal){  
    /** 
       Per ogni goal supportato... 
       ** 
       For each supported goal 
    **/
    for (i = 0; i < GpG.curr_goal_state->num_F; i++)
      {
	infGoal = CONVERT_FACT_TO_NODE (GpG.curr_goal_state->F[i], GpG.curr_plan_length);
	
	if (infGoal->w_is_true)
	{
	  /**
	     Se l'istante a cui e' supportato il goal e' maggiore
	     della durata del piano allora la durata e' uguale
	     all'istante del goal
	     **
	     If the time value at which the goal is supported is
	     greater than the plan makespan, then the plan makespan is
	     equal to the time value of the current goal
	  **/
	  if (infGoal->time_f > max_time)
	    max_time = infGoal->time_f;
	}
    }
  }
  else{


    /** 
	For each supported goal 
    **/
  for (i = 0; i < gnum_ft_conn; i++)
    {

      if (vectlevel[GpG.curr_plan_length]->fact[i].w_is_true)
	{

	  /**
	     Se l'istante a cui e' supportato il fatto e' maggiore
	     della durata del piano allora la durata e' uguale
	     all'istante del fatto
	     **
	     If the time value at which the fact is supported is
	     greater than the plan makespan, then the plan makespan
	     is equal to the time value of the fact
	  **/
	  if (vectlevel[GpG.curr_plan_length]->fact[i].time_f > max_time)
	    max_time = vectlevel[GpG.curr_plan_length]->fact[i].time_f;
	}

    }
  }

  GpG.total_time = max_time;

}





/**
   Compatta i piani non temporali usando i vincoli di ordinamento e la
   funzione insert_time
   **
   Compress the not temporal plans using ordering constraints and the
   insert_time function
**/

void compress_plan ()
{
  int level, ind;
  float indtime;

  if (DEBUG4)
    printf ("\n\n [o] COMPRESS PLAN => Delete empty levels \n");

  reset_propagation_vect ();

  if(!GpG.derived_predicates)
    {
      reset_time();

  /**
     Inserisce l'azione nel vettore delle corrispondenze
     **
     Insert the action in the array of the correspondences among the
     action node of the TDA-graph and the elements in the matrix of
     the ordering
  **/
  for (ind = 0, level = 0; level < GpG.curr_plan_length; level++)
    if (CHECK_ACTION_OF_LEVEL (level))
      {

	GET_ACTION_OF_LEVEL (level)->ord_pos = ind;
	act_ord_vect[ind] = GET_ACTION_OF_LEVEL (level);

	num_act_ord++;

	if (num_act_ord >= MAX_NUM_ACTIONS) {
#ifdef __MY_OUTPUT__
	  MSG_ERROR( WAR_MAX_NUM_ACTIONS );
#else
	  printf( WAR_MAX_NUM_ACTIONS );
#endif    
	  exit (1);
	}
	
	ind++;
      }
  
  /**
     Stabilisce i vincoli di ordinamento
     **
     Compute the ordering constraints
  **/
  for (level = 0; level < GpG.curr_plan_length; level++)
    if (CHECK_ACTION_OF_LEVEL (level))
      temporal_constraints (GET_ACTION_OF_LEVEL (level));

  /**
     Per ogni azione calcola l'esatta collocazione nel piano
     **
     For each action, compute its time value 
  **/
  for (level = 0; level < GpG.curr_plan_length; level++)
    if (CHECK_ACTION_OF_LEVEL (level))
      insert_time (GET_ACTION_OF_LEVEL (level));

  /**
     Calcola la durata totale del piano
     **
     Compute the plan makespan
  **/
  get_total_time_plan ();
    }
  else
    {
      for (indtime=0.0,level = 0; level < GpG.curr_plan_length; level++)
	{
	  if (GET_ACTION_POSITION_OF_LEVEL (level) >= 0)
	    {
	      GET_ACTION_OF_LEVEL(level)->time_f = indtime + get_action_time (vectlevel[level]->action.position, level);
	      indtime++;
	    }
	}
    }
}



void compress_numeric_plan()
{
  int i, ordering = 0, se=0, position=0, j, cel;
  PlanAction *temp_act;
  ActNode *celNode;
  float max_time;

  //  if(GpG.num_solutions == 2)
  //  GpG.info_search = 5;

  reset_propagation_vect ();

  if (DEBUG1)
    printf("\n\n\nCompress Numeric Plan:");

  for (temp_act = GpG.tempplan, i = 0; temp_act; i++)
    {

      if(gef_conn[temp_act->act_pos].act_type !=NORMAL_ACT)
	{
	  if (se == 0)
	    {
	      position = gef_conn[temp_act->act_pos].start_ef;
	    }
	  else 
	    if (se == 1)
	      {
		position = gef_conn[temp_act->act_pos].end_ef;
	      }
	}
      else
	position = temp_act->act_pos;

      max_time = 0.0;
      
      for (j = i - 1; j >= 0; j--)
	{
	  cel = GET_ACTION_POSITION_OF_LEVEL(j);
	  celNode = GET_ACTION_OF_LEVEL(j);

	  ordering = Econstraint_type (cel, j, position, i);
	  ordering = get_causal_constraint_type(cel, j, position, i, ordering); 

	  if (ordering == EA_SB) 
	    /** 
		l'azione B deve iniziare dopo la fine dell'azione A
		**
		the action B begins after the end of the action A
	    **/
	    {
	      if (max_time < celNode->time_f)
		{
		  max_time = celNode->time_f;
		}
	    }
	  else 
	    {
	      if (ordering == EA_EB) 
		/** 
		    l'azione B deve finire dopo la fine di A
		    **
		    the action B ends after the end of the action A 
		**/
		{
		  if (max_time < celNode->time_f - get_action_time (position, i) )
		    {
		      max_time = celNode->time_f - get_action_time (position, i);
		    }
		}
	      else
		if (ordering == SA_SB) 
		  /** 
		      l'azione B deve iniziare dopo l'inizio di A
		      **
		      the action B begins after the beginning of the action A
		  **/
		  {
		    if (max_time < celNode->time_f - get_action_time (cel, *celNode->level ) )
		      {
			max_time = celNode->time_f - get_action_time (cel, *celNode->level );
		      }
		  }
		else
		  {
		    if (ordering == SA_EB) 
		      /** 
			    l'azione B deve finire dopo l'inizio di A
			    **
			    The action B ends after the beginning of A 
		      **/
		      {
			if (max_time < celNode->time_f - get_action_time (cel, *celNode->level )- get_action_time (position, i)  )
			  {
			    max_time = celNode->time_f - get_action_time (cel, *celNode->level ) - get_action_time (position, i) ;
			  }
		      }
		    else
		      {
			if (ordering == EA_EB__SA_SB)
			  /**
			     Tra A e B vi e' un vincolo di
			     ordinamento sia di tipo EA_EB che di
			     tipo SA_SB.  Il vincolo piu'
			     restrittivo dipende dalla durata
			     dell'azione
			     **
			     There is an ordering constraint of type both
			     EA_EB and SA_SB. The most strong constraint
			     depends on the durations of the actions
			  **/
			  {
			    if(get_action_time(position, i) < get_action_time(cel, *celNode->level ))
			      {
				// EA_EB
				if (max_time < celNode->time_f - get_action_time (position, i) )
				  {
				    max_time = celNode->time_f - get_action_time (position, i);
				  }
			      }
			    else // SA_SB
			      {
				if (max_time < celNode->time_f - get_action_time (cel, *celNode->level ) )
				  {
				    max_time = celNode->time_f - get_action_time (cel, *celNode->level );
				  }
			      }
			  }
			
		      }
		    
		  }
	    }
	  
	}
      
      
      max_time += get_action_time (position, i);


      //      if (i > 0)
	{
	  for (j = i - 1; j >= 0; j--)
	    {
	      if (GET_ACTION_OF_LEVEL(j)->time_f <= max_time)
		break;
	    }
	}

      if (DEBUG2)
	printf ("\nInitialize->insert action %s  in level %d",
		print_op_name_string (position, temp_name), i);


      if((j + 1) >= gef_conn[temp_act->act_pos].level)
	insert_remove_action (position, j + 1, C_T_INSERT_ACTION,
			      GpG.approximation_level);

      if (DEBUG5)
	print_actions_in_subgraph();

      if (gef_conn[temp_act->act_pos].act_type !=NORMAL_ACT)
	{
	  if (se == 0)
	    se = 1;
	  else
	    se = 0;
	}

      if(gef_conn[temp_act->act_pos].act_type == NORMAL_ACT || se == 0)
	temp_act = temp_act->next;

      GpG.num_false_tot =
	(GpG.num_false_act + GpG.num_false_fa + GpG.num_false_num_fa + GpG.num_false_tmd_fa);  
      
    }


  if (DEBUG5 && GpG.num_false_tot > 0 )
    printf("\n\n\nError: Compress Numerical Plan failed");

}







/**
   Costruisce un piano temporale data una sequenza di azioni soluzione
   **
   Build a temporal plan from a sequence of actions that is a solutiuon
**/

void build_temporal_plan ()
{
  int ind;

  if (DEBUG1)
    printf ("\n\n [o] BUILD TEMPORAL PLAN\n");


    GpG.curr_plan_length=0;


  /**
     Inserisce l'azione nell'action graph
     **
     Insert the action in the action graph
  **/
  for (ind = 0; ind < gnum_plan_ops; ind++)
    {
      insert_remove_action (gplan_ops[ind], ind,
			    C_T_INSERT_ACTION, TRUE);
    }
  
  get_total_time_plan ();
}





/*********************************************************************
            FUNZIONI DI GESTIONE DEI VINCOLI DI ORDINAMENTO
**********************************************************************/






/**
   Stabilisce il tipo di vincolo tra l'azione inf_A e l'azione inf_B
   noto che A si trova a un livello inferiore rispetto a B
   **
   Compute the type of ordering constraint between the inf_A action
   and inf_B action at a level greater than the level of inf_A
**/
int Econstraint_type(int posA, int levA, int posB, int levB)
{
  int i,j,temp=0;
  
  if(gef_conn[posA].is_numeric==1 && gef_conn[posB].is_numeric==1)
    {
      if (GpG.accurate_numeric_constraint == TRUE)
	temp=Accurate_Econstraint_type_numeric(posA, posB, levA, levB);
      else
	temp=Econstraint_type_numeric(posA, posB);      

      if(temp==EA_SB)
	return temp;
    }

  /**
     at_end preconditions of the action A 
  **/
  if(gef_conn[posA].sf)
    for(i=0;i<gef_conn[posA].sf->num_PC_end;i++)
      {
	if(gef_conn[posA].sf->PC_end[i] < 0)
	  continue;

	/** 
	    mutex relation among the at end precondition of A and the
	    at start precondition of B
	**/
	for(j=0;j<gef_conn[posB].num_PC;j++)
	  {
	    if(gef_conn[posB].PC[j] < 0)
	      continue;
	    	    
	    if( ARE_MUTEX_FT(gef_conn[posA].sf->PC_end[i],gef_conn[posB].PC[j]))
	      return(EA_SB); 
	    /** 
		B deve iniziare dopo la fine di A 
		** 
		B starts after the end of A 
	    **/
	  }

	/** 
	    mutex relation among the at end precondition of A and the
	    over all precondition of B
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_PC_overall;j++)
	    {
	      if(gef_conn[posB].sf->PC_overall[j] < 0)
		continue;

	      if( ARE_MUTEX_FT(gef_conn[posA].sf->PC_end[i],gef_conn[posB].sf->PC_overall[j]))
		return(EA_SB); 
	      /**  
		   B deve iniziare dopo la fine di A 
		   **  
		   B starts after the end of A  
	      **/
	    }

	/** 
	    mutex relation among the at end precondition of A and the
	    at start effects of B
	**/
	if(gef_conn[posB].sf)
	    for(j=0;j<gef_conn[posB].sf->num_A_start;j++)
	      {
		if(gef_conn[posB].sf->A_start[j] < 0)
		  continue;

		if( ARE_MUTEX_FT(gef_conn[posA].sf->PC_end[i],gef_conn[posB].sf->A_start[j]))
		  return(EA_SB); 
		/**  
		     B deve iniziare dopo la fine di A  
		     **  
		     B starts after the end of A  
		**/
	      }

	/** 
	    B deletes the at end precondition of A through its at
	    start delete effects
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_D_start;j++)
	    {
	      if(gef_conn[posA].sf->PC_end[i]==gef_conn[posB].sf->D_start[j])
		return(EA_SB); 
	      /**  
		   B deve iniziare dopo la fine di A  
		   **
		   B start after the end of A
	      **/
	    }

	/** 
	    mutex relation among the at end precondition of A and the
	    at end precondition of B
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_PC_end;j++)
	    {
	      if(gef_conn[posB].sf->PC_end[j] < 0)
		continue;

	      if( ARE_MUTEX_FT(gef_conn[posA].sf->PC_end[i],gef_conn[posB].sf->PC_end[j]))
		{
		  temp=EA_EB;  
		  /**  
		       B deve finire dopo la fine di A  
		       **  
		       B ends after the end of A  
		  **/
		  break;
		}
	    }

	/** 
	    mutex relation among the at end precondition of A and the
	    at start additive effects of B
	**/
	for(j=0;j<gef_conn[posB].num_A;j++)
	  {
	    if(gef_conn[posB].A[j] < 0)
	      continue;

	    if( ARE_MUTEX_FT(gef_conn[posA].sf->PC_end[i],gef_conn[posB].A[j]))
	      {
		temp=EA_EB; 
		/** 
		    B deve finire dopo la fine di A 
		    **
		    B ends after the end of A
		**/
		break;
	      }
	  }

	/** 
	    B deletes the at end precondition of A through its at
	    end delete effects
	**/
	for(j=0;j<gef_conn[posB].num_D;j++)
	  {
	    if(gef_conn[posA].sf->PC_end[i]==gef_conn[posB].D[j])
	      {
		temp=EA_EB; 
		/** 
		    B deve iniziare dopo la fine di A 
		    **
		    B starts after the end of A
		**/
		break;
	      }
	  }


      } // end for PC_end action A


  /** 
      Effects at end of the Action A 
   **/
    for(i=0;i<gef_conn[posA].num_A;i++)
      {
	if(gef_conn[posA].A[i] < 0 )
	  continue;

	/** 
	    mutex relation among the at end additive effects of A and the
	    at start preconditions of B
	**/
	for(j=0;j<gef_conn[posB].num_PC;j++)
	  {
	    if(gef_conn[posB].PC[j] < 0)
	      continue;

	    if( ARE_MUTEX_FT(gef_conn[posA].A[i],gef_conn[posB].PC[j]))
	      return(EA_SB); 
	    /** 
		B deve iniziare dopo la fine di A 
		**
		B start after the end of A
	     **/
	  }

	/** 
	    mutex relation among the at end additive effects of A and the
	    overall preconditions of B
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_PC_overall;j++)
	    {
	    if(gef_conn[posB].sf->PC_overall[j] < 0)
	      continue;

	      if( ARE_MUTEX_FT(gef_conn[posA].A[i],gef_conn[posB].sf->PC_overall[j]))
		return(EA_SB); 
	      /** 
		  B deve iniziare dopo la fine di A
		  **
		  B starts after the end of A
	      **/
	    }

	/** 
	    mutex relation among the at end additive effects of A and the
	    at start additive effects of B
	**/
	if(gef_conn[posB].sf)
	    for(j=0;j<gef_conn[posB].sf->num_A_start;j++)
	      {
		if(gef_conn[posB].sf->A_start[j] < 0)
		  continue;

		if( ARE_MUTEX_FT(gef_conn[posA].A[i],gef_conn[posB].sf->A_start[j]))
		  return(EA_SB); 
		/** 
		    B deve iniziare dopo la fine di A 
		    **
		    B starts after the end of A
		**/
	      }

	/** 
	    B deletes the at end additive effects of A through its at
	    start delete effects
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_D_start;j++)
	    {
	      if(gef_conn[posA].A[i]==gef_conn[posB].sf->D_start[j])
		return(EA_SB); 
	      /** 
		  B deve iniziare dopo la fine di A 
		  **
		  B start after the end of A
	      **/
	    }

	/** 
	    mutex relation among the at end additive effects of A and the
	    at end preconditions of B
	**/
	if(gef_conn[posB].sf)
	  {
	    for(j=0;j<gef_conn[posB].sf->num_PC_end;j++)
	      {
		if(gef_conn[posB].sf->PC_end[j] < 0)
		  continue;
		
		if( ARE_MUTEX_FT(gef_conn[posA].A[i],gef_conn[posB].sf->PC_end[j]))
		  {		    
		    temp=EA_EB; 
		    /** 
			B deve finire dopo la fine di A 
			**
			B ends after the end of A
		    **/
		    break;
		  }
	      }
	  }

	/** 
	    mutex relation among the at end additive effects of A and the
	    at end additive effctes of B
	**/
	for(j=0;j<gef_conn[posB].num_A;j++)
	  {
	    if(gef_conn[posB].A[j] < 0)
	      continue;

	    if( ARE_MUTEX_FT(gef_conn[posA].A[i],gef_conn[posB].A[j]))
	      {
		temp=EA_EB; 
		/** 
		    B deve finire dopo la fine di A
		    **
		    B ends after the end of A
		**/
		break;
	      }
	  }

	/** 
	    B deletes the at end additive effects of A through its at
	    end delete effects
	**/
	for(j=0;j<gef_conn[posB].num_D;j++)
	  if(gef_conn[posA].A[i]==gef_conn[posB].D[j])
	    {
	      temp=EA_EB; 
	      /**  
		   B deve iniziare dopo la fine di A  
		   **  
		   B starts after the end of A  
	      **/
	      break;
	    }
      } // for Eff_end action A



    /* Effect DEL_end of the action A */
    for(i=0;i<gef_conn[posA].num_D;i++)
      {

	if(gef_conn[posA].D[i] < 0)
	  continue;

	/** 
	    A deletes the at start preconditions of B through its at
	    end delete effects
	**/
	for(j=0;j<gef_conn[posB].num_PC;j++)
	  {
	    if( gef_conn[posA].D[i]==gef_conn[posB].PC[j])
	      return(EA_SB); 
	    /**  
		 B deve iniziare dopo la fine di A  
		 **  
		 B starts after the end of A  
	    **/
	  }

	/** 
	    A deletes the overall preconditions of B through its at
	    end delete effects
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_PC_overall;j++)
	    {
	      if( gef_conn[posA].D[i]==gef_conn[posB].sf->PC_overall[j])
		return(EA_SB); 
	      /**  
		   B deve iniziare dopo la fine di A  
		   **  
		   B starts after the end of A  
	      **/
	    }

	/** 
	    A deletes the at start additive effects of B through its at
	    end delete effects
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_A_start;j++)
	    {
	      if( gef_conn[posA].D[i]==gef_conn[posB].sf->A_start[j])
		return(EA_SB); 
	      /**  
		   B deve iniziare dopo la fine di A  
		   **  
		   B starts after the end of A  
	      **/
	    }

	/** 
	    A deletes the at end preconditions of B through its at
	    end delete effects
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_PC_end;j++)
	    {
	      if( gef_conn[posA].D[i]==gef_conn[posB].sf->PC_end[j])
		{
		  temp=EA_EB; 
		  /**  
		       B deve iniziare dopo la fine di A  
		       **  
		       B starts after the end of A  
		  **/
		  break;
		}
	    }

	/** 
	    A deletes the at end edditive effects of B through its at
	    end delete effects
	**/
	for(j=0;j<gef_conn[posB].num_A;j++)
	  {
	    if( gef_conn[posA].D[i]==gef_conn[posB].A[j])
	      {
		temp=EA_EB; 
		/**  
		     B deve finire dopo la fine di A  
		     **  
		     B ends after the end of A  
		**/
		break;
	      }
	  }

      } // for Eff_DEL_end action A



 /* Preconditions overall ot the action A */
  if(gef_conn[posA].sf)
    for(i=0;i<gef_conn[posA].sf->num_PC_overall;i++)
      {

	if(gef_conn[posA].sf->PC_overall[i] < 0 )
	  continue;

	/** 
	    mutex relation among the over all preconditions of A and the
	    at start preconditions of B
	**/
	for(j=0;j<gef_conn[posB].num_PC;j++)
	  {
	    if(gef_conn[posB].PC[j] < 0 )
	      continue;

	    if( ARE_MUTEX_FT(gef_conn[posA].sf->PC_overall[i],gef_conn[posB].PC[j]))
	      return(EA_SB);
	    /**  
		 B deve iniziare dopo la fine di A  
		 **  
		 B starts after the end of A 
	    **/
	  }

	/** 
	    mutex relation among the over all preconditions of A and the
	    over all preconditions of B
	**/
	if(gef_conn[posB].sf)
	    for(j=0;j<gef_conn[posB].sf->num_PC_overall;j++)
	      {
		if(gef_conn[posB].sf->PC_overall[j] < 0 )
		  continue;

		if( ARE_MUTEX_FT(gef_conn[posA].sf->PC_overall[i],gef_conn[posB].sf->PC_overall[j]))
		  return(EA_SB); 
		/** 
		    B deve iniziare dopo la fine di A
		**
		    B starts after the end of A
		**/
	      }

	/** 
	    mutex relation among the over all preconditions of A and the
	    at start effects of B
	**/
	if(gef_conn[posB].sf)
	    for(j=0;j<gef_conn[posB].sf->num_A_start;j++)
	      {
		if(gef_conn[posB].sf->A_start[j] < 0 )
		  continue;

		if( ARE_MUTEX_FT(gef_conn[posA].sf->PC_overall[i],gef_conn[posB].sf->A_start[j]))
		  return(EA_SB); 
		/** 
		    B deve iniziare dopo la fine di A
		    **
		    B start after the end of A
		**/
	      }

	/** 
	    B deletes the over all preconditions of B through its at
	    start delete effects
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_D_start;j++)
	    {
	      if(gef_conn[posA].sf->PC_overall[i]==gef_conn[posB].sf->D_start[j])
		return(EA_SB); 
	      /** 
		  B deve iniziare dopo la fine di A
		  **
		  B start after the end of A
	      **/
	    }

	/** 
	    mutex relation among the over all preconditions of A and the
	    at end preconditions of B
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_PC_end;j++)
	    {
	      if(gef_conn[posB].sf->PC_end[j] < 0 )
		continue;

	      if( ARE_MUTEX_FT(gef_conn[posA].sf->PC_overall[i],gef_conn[posB].sf->PC_end[j]))
		{
		  temp=EA_EB; 
		  /** 
		      B deve finire dopo la fine di A
		      **
		      B ends after the end of A
		  **/
		  break;
		}
	    }

	/** 
	    mutex relation among the over all preconditions of A and the
	    at end effects of B
	**/
	for(j=0;j<gef_conn[posB].num_A;j++)
	  {
	    if(gef_conn[posB].A[j] < 0 )
	      continue;

	    if( ARE_MUTEX_FT(gef_conn[posA].sf->PC_overall[i],gef_conn[posB].A[j]))
	      {
		temp=EA_EB; 
		/** 
		    B deve finire dopo la fine di A
		    **
		    B ends after the end of A
		**/
		break;
	      }
	  }

	/** 
	    B deletes the over all preconditions of B through its at
	    end delete effects
	**/
	for(j=0;j<gef_conn[posB].num_D;j++)
	  {
	    if(gef_conn[posA].sf->PC_overall[i]==gef_conn[posB].D[j])
	      {
		temp=EA_EB; // B deve iniziare dopo la fine di A
		break;
	      }
	  }
      } // for PC_overall action A



  /* Precondition at start of the action A */
    for(i=0;i<gef_conn[posA].num_PC;i++)
      {

	if(gef_conn[posA].PC[i] < 0 )
	  continue;

	/** 
	    mutex relation among the at start preconditions of A and the
	    at start preconditions of B
	**/
	for(j=0;j<gef_conn[posB].num_PC;j++)
	  {
	    if(gef_conn[posB].PC[j] < 0 )
	      continue;

	    if( ARE_MUTEX_FT(gef_conn[posA].PC[i],gef_conn[posB].PC[j]))
	      {
		/**
		   Se si e' rilevato che B deve finire dopo la fine di
		   A il vincolo piu' restrittivo dipende dalle durate
		   delle due azioni
		   **
		   If there is an ordering constraint for which B ends
		   after the end of A, then the stronger constrint
		   depends on the durations of the actions involved
		**/
		if(temp!=EA_EB) 
		  temp=SA_SB;
		else		 
		  temp=EA_EB__SA_SB;
		break;
	      }
	  }

	/** 
	    mutex relation among the at start preconditions of A and the
	    over all preconditions of B
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_PC_overall;j++)
	    {
	      if(gef_conn[posB].sf->PC_overall[j] < 0 )
		continue;

	      if( ARE_MUTEX_FT(gef_conn[posA].PC[i],gef_conn[posB].sf->PC_overall[j]))
		{
		  /**
		     Se si e' rilevato che B deve finire dopo la fine
		     di A il vincolo piu' restrittivo dipende dalle
		     durate delle due azioni
		     **
		     If there is an ordering constraint for which B ends
		     after the end of A, then the stronger constrint
		     depends on the durations of the actions involved
		  **/
		  if(temp!=EA_EB)
		    temp=SA_SB;
		  else
		    temp=EA_EB__SA_SB;
		  break;
		}
	    }


	/** 
	    mutex relation among the at start preconditions of A and the
	    at start effects of B
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_A_start;j++)
	    {
	      if(gef_conn[posB].sf->A_start[j] < 0 )
		continue;

	      if( ARE_MUTEX_FT(gef_conn[posA].PC[i],gef_conn[posB].sf->A_start[j]))
		{
		  /**
		     Se si e' rilevato che B deve finire dopo la fine
		     di A il vincolo piu' restrittivo dipende dalle
		     durate delle due azioni
		     **
		     If there is an ordering constraint for which B ends
		     after the end of A, then the stronger constrint
		     depends on the durations of the actions involved
		  **/
		  if(temp!=EA_EB)
		    temp=SA_SB; 
		     /** 
			 B deve iniziare dopo l'inizio di A
			 **
			 B starts after the beginning of A
		      **/
		  else
		    temp=EA_EB__SA_SB;
		  break;
		}
	    }



	/** 
	    B deletes the at end additive effects of B through its at
	    start delete effects
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_D_start;j++)
	    {
	      if(gef_conn[posA].PC[i]==gef_conn[posB].sf->D_start[j])
		{
		  /**
		     Se si e' rilevato che B deve finire dopo la fine
		     di A il vincolo piu' restrittivo dipende dalle
		     durate delle due azioni
		     **
		     If there is an ordering constraint for which B ends
		     after the end of A, then the stronger constrint
		     depends on the durations of the actions involved
		  **/
		  if(temp!=EA_EB)
		    temp=SA_SB; 
		  /** 
		      B deve iniziare dopo l'inizio di A
		      **
		      B starts after the beginning of A
		  **/
		  else
		    temp=EA_EB__SA_SB;
		  break;
	      }
	    }

	/** 
	    mutex relation among the at start preconditions of A and the
	    at end preconditions of B
	**/
	if(gef_conn[posB].sf)
	  for(j=0;j<gef_conn[posB].sf->num_PC_end;j++)
	    {
	      if(gef_conn[posB].sf->PC_end[j] < 0 )
		continue;

	      if( ARE_MUTEX_FT(gef_conn[posA].PC[i],gef_conn[posB].sf->PC_end[j]))
		if( temp!=SA_SB && temp!=EA_EB && temp!=EA_EB__SA_SB)
		  {
		    temp=SA_EB;  
		    /** 
			B deve finire dopo l'inizio di A
			**
			B ends after the beginning of A
		    **/
		    break;
		  }
	    }

	/** 
	    mutex relation among the at start preconditions of A and the
	    at end additive effects of B
	**/
	for(j=0;j<gef_conn[posB].num_A;j++)
	  {
	    if(gef_conn[posB].A[j] < 0 )
	      continue;

	    if( ARE_MUTEX_FT(gef_conn[posA].PC[i],gef_conn[posB].A[j]))
	      if( temp!=SA_SB && temp!=EA_EB && temp!=EA_EB__SA_SB)
		{
		  temp=SA_EB; 
		  /** 
		      B deve finire dopo l'inizio di A
		      **
		      B ends after the beginning of A
		  **/
		  break;
		}
	  }

	/** 
	    B deletes the at end additive effects of B through its at
	    end delete effects
	**/
	for(j=0;j<gef_conn[posB].num_D;j++)
	  {
	    if(gef_conn[posA].PC[i]==gef_conn[posB].D[j])
	      if( temp!=SA_SB && temp!=EA_EB && temp!=EA_EB__SA_SB)
		{
		  temp=SA_EB; 
		  /** 
		      B deve finire dopo l'inizio di A
		      **
		      B ends after the beginning of A
		  **/
		  break;
		}
	  }

      } // for PC action A



    /**
       Effetti start Action A
       **
       Start action A effects
    **/
    if(gef_conn[posA].sf)
      for(i=0;i<gef_conn[posA].sf->num_A_start;i++)
	{

	  if (gef_conn[posA].sf->A_start[i])
	    continue;

	  /** 
	      mutex relation among the at start effects of A and the
	      at start preconditions of B
	  **/
	  for(j=0;j<gef_conn[posB].num_PC;j++)
	    {
	      if (gef_conn[posB].PC[j])
		continue;

	      if( ARE_MUTEX_FT(gef_conn[posA].sf->A_start[i],gef_conn[posB].PC[j]))
		{
		  /**
		     Se si e' rilevato che B deve finire dopo la fine
		     di A il vincolo piu' restrittivo dipende dalle
		     durate delle due azioni
		     **
		     If there is an ordering constraint for which B ends
		     after the end of A, then the stronger constrint
		     depends on the durations of the actions involved
		  **/
		  if(temp!=EA_EB) 
		    temp=SA_SB;
		  else
		    temp=EA_EB__SA_SB;
		  break;
		}
	    }

	  /** 
	      mutex relation among the at start effects of A and the
	      over all preconditions of B
	  **/
	  if(gef_conn[posB].sf)
	    for(j=0;j<gef_conn[posB].sf->num_PC_overall;j++)
	      {
		if (gef_conn[posB].sf->PC_overall[j])
		  continue;

		if( ARE_MUTEX_FT(gef_conn[posA].sf->A_start[i],gef_conn[posB].sf->PC_overall[j]))
		{
		  /**
		     Se si e' rilevato che B deve finire dopo la fine
		     di A il vincolo piu' restrittivo dipende dalle
		     durate delle due azioni
		     **
		     If there is an ordering constraint for which B ends
		     after the end of A, then the stronger constrint
		     depends on the durations of the actions involved
		  **/
		  if(temp!=EA_EB)
		    temp=SA_SB;
		  else
 		    temp=EA_EB__SA_SB;
		  break;
		}
	      }

	  /** 
	      mutex relation among the at start effects of A and the
	      at start additive effects of B
	  **/
	  if(gef_conn[posB].sf)
	    for(j=0;j<gef_conn[posB].sf->num_A_start;j++)
	      {
		if (gef_conn[posB].sf->A_start[j])
		  continue;

		if( ARE_MUTEX_FT(gef_conn[posA].sf->A_start[i],gef_conn[posB].sf->A_start[j]))
		  {
		  /**
		     Se si e' rilevato che B deve finire dopo la fine
		     di A il vincolo piu' restrittivo dipende dalle
		     durate delle due azioni
		     **
		     If there is an ordering constraint for which B ends
		     after the end of A, then the stronger constrint
		     depends on the durations of the actions involved
		  **/
		    if(temp!=EA_EB)
		      temp=SA_SB; 
		    /** 
			B deve iniziare dopo l'inizio di A 
			**
			B starts after the beginning of A
		    **/
		    else
		      temp=EA_EB__SA_SB;
		    break;
		  }
	      }

	  /** 
	      B deletes the at start additive effects of B through its at
	      start delete effects
	  **/
	  if(gef_conn[posB].sf)
	    for(j=0;j<gef_conn[posB].sf->num_D_start;j++)
	      {
		//	if (gef_conn[posB].sf->D_start[j])
		//  continue;

		if(gef_conn[posA].sf->A_start[i]==gef_conn[posB].sf->D_start[j])
		  {
		  /**
		     Se si e' rilevato che B deve finire dopo la fine
		     di A il vincolo piu' restrittivo dipende dalle
		     durate delle due azioni
		     **
		     If there is an ordering constraint for which B ends
		     after the end of A, then the stronger constrint
		     depends on the durations of the actions involved
		  **/
		    if(temp!=EA_EB)
		      temp=SA_SB; 
		    /** 
			B deve iniziare dopo l'inizio di A 
			**
			B starts after the beginning of A
		    **/
		    else
		      temp=EA_EB__SA_SB;
		    break;
		}
	      }

	  /** 
	      mutex relation among the at start effects of A and the
	      at end preconditions of B
	  **/
	  if(gef_conn[posB].sf)
	    for(j=0;j<gef_conn[posB].sf->num_PC_end;j++)
	      {
		if (gef_conn[posB].sf->PC_end[j])
		  continue;

		if( ARE_MUTEX_FT(gef_conn[posA].sf->A_start[i],gef_conn[posB].sf->PC_end[j]))
		  if( temp!=SA_SB && temp!=EA_EB  && temp!=EA_EB__SA_SB)
		    {
		      temp=SA_EB;  
		      /** 
			  B deve finire dopo l'inizio di A
			  **
			  B ends after the beginning of A
		      **/
		      break;
		    }
	      }

	  /** 
	      mutex relation among the at start effects of A and the
	      at end additive effects of B
	  **/
	for(j=0;j<gef_conn[posB].num_A;j++) 
	  {
	    if (gef_conn[posB].A[j])
	      continue;

	    if( ARE_MUTEX_FT(gef_conn[posA].sf->A_start[i],gef_conn[posB].A[j]))
	      if( temp!=SA_SB && temp!=EA_EB  && temp!=EA_EB__SA_SB)
		{
		  temp=SA_EB; 
		  /** 
		      B deve finire dopo l'inizio di A
		      **
		      B ends after the beginning of A
		  **/
		  break;
		}
	  }

	  /** 
	      B deletes the at start additive effects of B through its at
	      end delete effects
	  **/
	for(j=0;j<gef_conn[posB].num_D;j++)
	  {
	    if( gef_conn[posA].sf->A_start[i]==gef_conn[posB].D[j])
	      if( temp!=SA_SB && temp!=EA_EB  && temp!=EA_EB__SA_SB)
		{
		  temp=SA_EB; 
		  /** 
		      B deve finire dopo l'inizio di A
		      **
		      B ends after the beginning of A
		  **/
		  break;
		}
	  }

      } // for PC action A 
 




    /* Effetti DEL-start of action A */
    if(gef_conn[posA].sf)
      for(i=0;i<gef_conn[posA].sf->num_D_start;i++)
	{
	  if (gef_conn[posA].sf->D_start[i])
	    continue;
	  
	  /** 
	      A deletes the at start preconditions of B through its at
	      start delete effects
	  **/
	  for(j=0;j<gef_conn[posB].num_PC;j++)
	    {
	      if( gef_conn[posA].sf->D_start[i]==gef_conn[posB].PC[j])
		{
		  /**
		     Se si e' rilevato che B deve finire dopo la fine
		     di A il vincolo piu' restrittivo dipende dalle
		     durate delle due azioni
		     **
		     If there is an ordering constraint for which B ends
		     after the end of A, then the stronger constrint
		     depends on the durations of the actions involved
		  **/
		  if(temp!=EA_EB) 
		    temp=SA_SB;
		  else
		    temp=EA_EB__SA_SB;
		  break;
		}
	    }

	  /** 
	      A deletes the over all preconditions of B through its at
	      start delete effects
	  **/
	  if(gef_conn[posB].sf)
	    for(j=0;j<gef_conn[posB].sf->num_PC_overall;j++)
	      {
		if( gef_conn[posA].sf->D_start[i]==gef_conn[posB].sf->PC_overall[j])
		  {
		  /**
		     Se si e' rilevato che B deve finire dopo la fine
		     di A il vincolo piu' restrittivo dipende dalle
		     durate delle due azioni
		     **
		     If there is an ordering constraint for which B ends
		     after the end of A, then the stronger constrint
		     depends on the durations of the actions involved
		  **/
		    if(temp!=EA_EB)
		      temp=SA_SB;
		    else
		      temp=EA_EB__SA_SB;
		    break;
		}
	      }

	  /** 
	      A deletes the at start additive effcts of B through its at
	      start delete effects
	  **/
	  if(gef_conn[posB].sf)
	    for(j=0;j<gef_conn[posB].sf->num_A_start;j++)
	      {
		//	      if(gef_conn[posB].sf->A_start[j] < 0)
		//	continue;

		if( gef_conn[posA].sf->D_start[i]==gef_conn[posB].sf->A_start[j])
		  {
		  /**
		     Se si e' rilevato che B deve finire dopo la fine
		     di A il vincolo piu' restrittivo dipende dalle
		     durate delle due azioni
		     **
		     If there is an ordering constraint for which B ends
		     after the end of A, then the stronger constrint
		     depends on the durations of the actions involved
		  **/
		    if(temp!=EA_EB)
		      temp=SA_SB; 
		    /** 
			B deve iniziare dopo l'inizio di A
			**
			B start after the beginning of A
		    **/
		    else
		      temp=EA_EB__SA_SB;
		    break;
		  }
	      }

	  /** 
	      A deletes the at end preconditions of B through its at
	      start delete effects
	  **/
	  if(gef_conn[posB].sf)
	    for(j=0;j<gef_conn[posB].sf->num_PC_end;j++)
	      {
		if( gef_conn[posA].sf->D_start[i]==gef_conn[posB].sf->PC_end[j])
		  if( temp!=SA_SB && temp!=EA_EB && temp!=EA_EB__SA_SB)
		    {
		      temp=SA_EB;  
		      /** 
			  B deve finire dopo l'inizio di A
			  **
			  B ends after the beginning of A
		      **/
		      break;
		    }
	      }

	  /** 
	      A deletes the at end additive effects of B through its at
	      start delete effects
	  **/
	for(j=0;j<gef_conn[posB].num_A;j++)
	  {
	    if( gef_conn[posA].sf->D_start[i]==gef_conn[posB].A[j])
	      if( temp!=SA_SB && temp!=EA_EB  && temp!=EA_EB__SA_SB)
		{
		  temp=SA_EB; 
		  /** 
		      B deve finire dopo l'inizio di A
		      **
		      B ends after the beginning of A
		  **/
		  break;
		}
	  }
      } // for PC action A

   
    
    return(temp);


}



int Accurate_Econstraint_type_numeric(int posA, int posB, int levA, int levB)
{
  
  int k, b, j, ind, indA, indB, el, el_a, el_b, ord = 0, unsup_link;
  register int temp, tempA, tempB;

  for (k = 0, j = 0; k < gnum_fullnum_blocks; k++, j += 32)
    {

      //se aggiorno qualcosa che dall'altra parte sto usando a dx dell'aggiornamento
      if (get_bit_table_block(l_vals, posA, k) & get_bit_table_block(r_vals, posB, k))
	{
	  tempA = get_bit_table_block(l_vals, posA, k);
	  tempB = get_bit_table_block(r_vals, posB, k);

	  b = 32;
	  while (tempA & tempB)
	    {
	      b--;

	      if ((tempA & FIRST_1) && (tempB & FIRST_1)) 
		{
		  for (indA = 0; indA < gef_conn[posA].num_A; indA++)
		    {
		      el_a = gef_conn[posA].A[indA];

		      if (el_a < 0 && is_var_in_eff_cvar( j + b, el_a) )
			{
			  if (gef_conn[posB].sf)
			    for (indB = 0; indB < gef_conn[posB].sf->num_A_start; indB++)
			      {
				el_b = gef_conn[posB].sf->A_start[indB];
				
				if (el_b < 0 && is_var_in_eff_cvar( j + b, el_b) )
				  return (EA_SB);
			      }
			  
			  for (indB = 0; indB < gef_conn[posB].num_A; indB++)
			    {
			      el_b = gef_conn[posB].A[indB];
			      
			      if (el_b < 0 && is_var_in_eff_cvar( j + b, el_b) )
				{
				  if (ord == 0)
				    ord = EA_EB;
				  else if (ord == SA_SB)
				    ord = EA_EB__SA_SB;
				}
			    }
			  
			}
		    }


		  if (gef_conn[posA].sf)
		    for (indA = 0; indA < gef_conn[posA].sf->num_A_start; indA++)
		      {
			el_a = gef_conn[posA].sf->A_start[indA];
			
			if (el_a < 0 && is_var_in_eff_cvar( j + b, el_a) )
			  {
			    if (gef_conn[posB].sf)
			      for (indB = 0; indB < gef_conn[posB].sf->num_A_start; indB++)
				{
				  el_b = gef_conn[posB].sf->A_start[indB];
				  
				  if (el_b < 0 && is_var_in_eff_cvar( j + b, el_b) )
				    {
				      if (ord == 0)
					ord = SA_SB;
				      else if (ord == EA_EB)
					ord = EA_EB__SA_SB;
				    }
				}
			    
			    for (indB = 0; indB < gef_conn[posB].num_A; indB++)
			      {
				el_b = gef_conn[posB].A[indB];
				
				if (el_b < 0 && is_var_in_eff_cvar( j + b, el_b) )
				  {
				    if (ord == 0)
				      ord = SA_EB;
				  }
			      }
			    
			  }
		      }
		}
	      
	      tempA <<= 1;
	      tempB <<= 1;
	    }
	  
	}


      /*
      //se aggiorno qualcosa che dall'altra parte sto usando a dx dell'aggiornamento
      if (get_bit_table_block(l_vals, posA, k) & get_bit_table_block(r_vals, posB, k))
	return (EA_SB);
      */

      //se testo qualcosa che dall'altra parte sto aggiornando
      if (levA >= 0)
	{
	  if (get_bit_table_block(tested_vars, posB, k) & get_bit_table_block(l_vals, posA, k))
	    {
	      
	      temp = get_bit_table_block(l_vals, posA, k);
 
	      b = 32;
	      while (temp)
		{
		  b--;
		  if (temp & FIRST_1)
		    {

		      // PREC AT START
		      for(ind=0; ind < gef_conn[posB].num_PC ; ind++ )
			{
			  el = gef_conn[posB].PC[ind];
			  if (el < 0 &&
			      is_var_in_prec_cvar( j + b, el) ) 
			    {
			      if (!is_num_prec_satisfied_after_start(el, levA))
				return (EA_SB);
			      else if (!is_num_prec_satisfied (el, levA ))
				{
				  if (ord == 0)
				    ord = SA_SB;
				  else if (ord == EA_EB)
				    ord = EA_EB__SA_SB;
				}
			    }
			}


		      
		      // PREC OVERALL
		      if (gef_conn[posB].sf)
			for(ind=0; ind < gef_conn[posB].sf->num_PC_overall; ind++ )
			  {
			    el = gef_conn[posB].sf->PC_overall[ind];
			    if (el < 0 && is_var_in_prec_cvar( j + b, el) )
			      return(EA_SB);
			  }
		      
		      
		      // PREC AT END
		      if (gef_conn[posB].sf)
			for(ind=0; ind < gef_conn[posB].sf->num_PC_end ; ind++ )
			  {
			    el = gef_conn[posB].sf->PC_end[ind];
			    if (el < 0 && is_var_in_prec_cvar( j + b, el))
			      {
				if (!is_num_prec_satisfied_after_start (el, levA))
				  {
				    if (ord == 0)
				      ord = EA_EB;
				    else if (ord == SA_SB)
				      ord = EA_EB__SA_SB;
				  }
				else if (!is_num_prec_satisfied (el, levA ) && ord == 0)
				  ord = SA_EB;
				
			      }
			  }
		      
		    }
		  temp <<= 1;

		}
	    }
	}

      /**
	 In questo caso bisogna testare su un vettore temporaneo gli effetti delle mie
	 modifiche sulla variabile gia' nel grafo che testo

      **/

      //se aggiorno qualcosa che dall'altra parte sto testando
      if (get_bit_table_block(l_vals, posB, k) & get_bit_table_block(tested_vars, posA, k))
	{

	  temp = get_bit_table_block(l_vals, posB, k);

	  b = 32;
	  while (temp)
	    {
	      b--;
	      if (temp & FIRST_1)
		{
		  // PREC AT START
		  for(ind=0; ind < gef_conn[posA].num_PC ; ind++ )
		    {
		      el = gef_conn[posA].PC[ind];
		      if (el < 0 && is_var_in_prec_cvar( j + b, el))
			{
			  unsup_link = is_num_prec_unsatisfied_applying_action(el, AT_START_TIME, levA, posB);//GET_ACTION_POSITION_OF_LEVEL(levA));
			  if (unsup_link == 1)
			    {
			      if (ord == 0)
				ord = SA_SB;
			      else if (ord == EA_EB)
				ord = EA_EB__SA_SB;
			    }
			  else if (unsup_link == 2 && ord == 0)
			    ord = SA_EB;
			}
		    }
		  

		  // PREC OVERALL
		  if (gef_conn[posA].sf)
		    for(ind=0; ind < gef_conn[posA].sf->num_PC_overall; ind++ )
		      {
			el = gef_conn[posA].sf->PC_overall[ind];
			if (el < 0 &&
			    is_var_in_prec_cvar( j + b, el) )
			  return(EA_SB);
		      }
		  
		  
		  // PREC AT END
		  if (gef_conn[posA].sf)
		    for(ind=0; ind < gef_conn[posA].sf->num_PC_end ; ind++ )
		      {
			el = gef_conn[posA].sf->PC_end[ind];
			if (el < 0 && is_var_in_prec_cvar( j + b, el))
			  {
			    unsup_link = is_num_prec_unsatisfied_applying_action(el, AT_END_TIME, levA, posB);//GET_ACTION_POSITION_OF_LEVEL(levA));
			    if (unsup_link == 1)
			      return (EA_SB);
			    else if (unsup_link == 2)
			      {
				if (ord == 0)
				  ord = EA_EB;
				else if (ord == SA_SB)
				  ord = EA_EB__SA_SB;
			      }
			  }
		      }
		  
		}
	      temp <<= 1;
	    }
	  
	}


      /**
      //se La^Lb != La* ^ Lb*, allora a e b sono mutex 
      if ((get_bit_table_block(l_vals, posA, k) & get_bit_table_block(l_vals, posB, k)) !=
	  (get_bit_table_block(lstar_vals, posA, k) & get_bit_table_block(lstar_vals, posB, k)))
	return(EA_SB);
      **/

      if ((get_bit_table_block(l_vals, posA, k) & get_bit_table_block(l_vals, posB, k)) !=
	  (get_bit_table_block(lstar_vals, posA, k) & get_bit_table_block(lstar_vals, posB, k)))
	{

	  tempA = get_bit_table_block(l_vals, posA, k) & (~get_bit_table_block(lstar_vals, posA, k));
	  tempB = get_bit_table_block(l_vals, posB, k) & (~get_bit_table_block(lstar_vals, posB, k));

	  b = 32;
	  while (tempA & tempB)
	    {
	      b--;

	      if ((tempA & FIRST_1) && (tempB & FIRST_1)) 
		{
		  for (indA = 0; indA < gef_conn[posA].num_A; indA++)
		    {
		      el_a = gef_conn[posA].A[indA];

		      if (el_a < 0 && is_var_in_eff_cvar( j + b, el_a) )
			{
			  if (gef_conn[posB].sf)
			    for (indB = 0; indB < gef_conn[posB].sf->num_A_start; indB++)
			      {
				el_b = gef_conn[posB].sf->A_start[indB];
				
				if (el_b < 0 && is_var_in_eff_cvar( j + b, el_b) )
				  return (EA_SB);
			      }
			  
			  for (indB = 0; indB < gef_conn[posB].num_A; indB++)
			    {
			      el_b = gef_conn[posB].A[indB];
			      
			      if (el_b < 0 && is_var_in_eff_cvar( j + b, el_b) )
				{
				  if (ord == 0)
				    ord = EA_EB;
				  else if (ord == SA_SB)
				    ord = EA_EB__SA_SB;
				}
			    }
			  
			}
		    }


		  if (gef_conn[posA].sf)
		    for (indA = 0; indA < gef_conn[posA].sf->num_A_start; indA++)
		      {
			el_a = gef_conn[posA].sf->A_start[indA];
			
			if (el_a < 0 && is_var_in_eff_cvar( j + b, el_a) )
			  {
			    if (gef_conn[posB].sf)
			      for (indB = 0; indB < gef_conn[posB].sf->num_A_start; indB++)
				{
				  el_b = gef_conn[posB].sf->A_start[indB];
				  
				  if (el_b < 0 && is_var_in_eff_cvar( j + b, el_b) )
				    {
				      if (ord == 0)
					ord = SA_SB;
				      else if (ord == EA_EB)
					ord = EA_EB__SA_SB;
				    }
				}
			    
			    for (indB = 0; indB < gef_conn[posB].num_A; indB++)
			      {
				el_b = gef_conn[posB].A[indB];
				
				if (el_b < 0 && is_var_in_eff_cvar( j + b, el_b) )				{
				  if (ord == 0)
				    ord = SA_EB;
				}
			      }
			    
			  }
		      }
		}
	      
	      tempA <<= 1;
	      tempB <<= 1;
	    }
	}
    }

  return(ord);
  
}






int Econstraint_type_numeric(int posA, int posB)
{
  
  int k;
  int l_val_block_a, l_val_block_b;

  for (k = 0; k < gnum_fullnum_blocks; k++)
    {

      l_val_block_a = get_bit_table_block(l_vals, posA, k);

      if (l_val_block_a)
	{
	  //se aggiorno qualcosa che dall'altra parte sto usando a dx dell'aggiornamento
	  if (l_val_block_a & get_bit_table_block(r_vals, posB, k))
	    return TRUE;
	  
	  //se aggiorno qualcosa che dall'altra parte sto testando
	  if (l_val_block_a & get_bit_table_block(tested_vars, posB, k))
	    return TRUE;
	 
	  l_val_block_b = get_bit_table_block(l_vals, posB, k);

	  if (l_val_block_b)
	    {
	      //se testo qualcosa che dall'altra parte sto aggiornando
	      if (get_bit_table_block(tested_vars, posA, k) & l_val_block_b)
		return TRUE;
 
	      //se La^Lb != La* ^ Lb*, allora a e b sono mutex 
	      if ((l_val_block_a & l_val_block_b) !=
		  (get_bit_table_block(lstar_vals, posA, k) & get_bit_table_block(lstar_vals, posB, k)))
		return TRUE;
	    }
	}
    }

  return FALSE;
  
}





/** 
    Restituisce il tipo di constraint tra l'azione A e l'azione B che
    segue A, che e' piu' restrittivo per B
    **
    Compute the strongest constraint type between the action A and
    the action B at the level greater than the level of A
**/
int get_constraint_type(int posA, int levA, int posB, int levB)
{
  int ordering;

  ordering = 0;

  
  /** 
     Notate che A precede B
     **
     Note that A precede B
  **/ 

  /** 
     Analisi del tipo di ordinamento dovuto a mutue esclusioni
     *
     Compute the ordering constraints considering the mutex relations
     between the actions
  **/
  

  ordering =  mat_ord[GET_ACTION_OF_LEVEL(levA)->ord_pos][GET_ACTION_OF_LEVEL(levB)->ord_pos];


  if (ordering == EA_SB)
    return(EA_SB);
  
  if (get_action_time(posA, levA) < get_action_time(posB, levB))
    {
      if (ordering == SA_SB || ordering == EA_EB__SA_SB)
	ordering = SA_SB;
    }
  else
    {
      if (ordering == EA_EB || ordering == EA_EB__SA_SB)
	ordering = EA_EB;
    }

  ordering = get_causal_constraint_type(posA, levA, posB, levB, ordering);

  return ordering;

}







  /**
     Analisi del tipo di ordinamento dovuto a link causali
     **
     Compute the ordering constraints considering the casual links
     between the actions
  **/
int get_causal_constraint_type(int posA, int levA, int posB, int levB, int ordering)
{
  int i;

  for (i = 0; i < gef_conn[posA].num_A; i++)
    {
      if (gef_conn[posA].A[i] < 0)
	continue;

      if (vectlevel[levA]->fact[gef_conn[posA].A[i]].w_is_true >= 1)
	continue;

      if(is_fact_in_preconditions(posB, gef_conn[posA].A[i]) || is_fact_in_preconditions_overall(posB, gef_conn[posA].A[i]))
	return(EA_SB);

      if(is_fact_in_preconditions_end(posB, gef_conn[posA].A[i]))
	{
	  if (ordering == SA_SB)
	    ordering = EA_EB__SA_SB;
	  else 
	    ordering = EA_EB;
	}
    }
  
  if (gef_conn[posA].sf) {
  
    for (i = 0; i < gef_conn[posA].sf->num_A_start; i++)
      {

	if (gef_conn[posA].sf->A_start[i] < 0)
	  continue;

	if (vectlevel[levA]->fact[gef_conn[posA].sf->A_start[i]].w_is_true >= 1)
	  continue;

	if(is_fact_in_preconditions(posB, gef_conn[posA].sf->A_start[i]) || is_fact_in_preconditions_overall(posB, gef_conn[posA].sf->A_start[i]))
	  {
	    if(ordering == EA_EB)
	      ordering = EA_EB__SA_SB;
	    else
	      ordering = SA_SB;
	  }
	
	if(is_fact_in_preconditions_end(posB, gef_conn[posA].sf->A_start[i]))
	  if(ordering != SA_SB && ordering!=EA_EB && ordering!=EA_EB__SA_SB)
	    ordering = SA_EB;
      }

  }


  if (get_action_time(posA, levA) < get_action_time(posB, levB))
    {
      if (ordering == SA_SB || ordering == EA_EB__SA_SB)
	return(SA_SB);
    }
  else
    {
      if (ordering == EA_EB || ordering == EA_EB__SA_SB)
	return(EA_EB);
    }

  return(ordering);
  
}



/**
   Inserisce i vincoli tra l'azione infAction e il resto del piano
   parziale
   **
   Insert the ordering constraints between the action infAction and
   the rest of the partial plan in the matrix of the orderings
**/

void
temporal_constraints (ActNode_list infAction)
{

  int level, posAction, posB, ind_level;


  level = *infAction->level;

  /**
     Cerchiamo la prima posizione libera nella matrice degli
     ordinamenti e nel vettore di corrispondenza
     **
     Analyze the first empty row in the matrix of the orderings using
     the array of the correspondences
  **/
  if (GpG.temporal_plan)
    {
      for (posAction = 0; posAction < num_act_ord; posAction++)
	if (act_ord_vect[posAction] == NULL)
	  break;
     
      /**
	 Non ci sono buchi liberi
	 **
	 There is no empty row in the matrix of the orderings
      **/
      if (posAction == num_act_ord)
	num_act_ord++;

      if (num_act_ord >= MAX_NUM_ACTIONS) {
#ifdef __MY_OUTPUT__
	  MSG_ERROR( WAR_MAX_NUM_ACTIONS );
#else
	  printf( WAR_MAX_NUM_ACTIONS );
#endif    
	  exit (1);
      } 
      
      infAction->ord_pos = posAction;
      act_ord_vect[posAction] = infAction;
    }
  else
    {
      /**
	 Se non e' settato GpG.temporal
	 **
	 If GpG.temporal is not setted
      **/

      posAction = infAction->ord_pos;

#ifdef __TEST__
      if (posAction > num_act_ord)
#ifdef __MY_OUTPUT__
	MSG_ERROR( WAR_MAX_NUM_ACTIONS );
#else
      printf( WAR_MAX_NUM_ACTIONS );
#endif
#endif
      
    }

  /**
     Per tutti i livelli...
     **
     For each level...
  **/
  for (ind_level = 0; ind_level < GpG.curr_plan_length; ind_level++)
    {

      if (&vectlevel[ind_level]->action == infAction)
	continue;

      posB = vectlevel[ind_level]->action.ord_pos;

      /**
	 Se l'azione del livello e' mutex con l'azione che deve essere
	 inserita nella matrice allora viene introdotto l'ordinamento
	 **
	 If the action of the current level is mutex with the action
	 examined, then we insert an ordering in the matrix
      **/
      if (check_mutex_action (infAction->position, ind_level) >= 0)
	{

	  if (vectlevel[ind_level]->action.w_is_used > 0)
	    {
	      /**
		 L'ordinamento tra le azioni rispetta l'ordinamento
		 dei livelli
		 **
		 The direction of the ordering constraint depends on
		 the levels of the actions involved
	      **/
	      if (ind_level < level)
		{

		  if(GpG.constraint_type && GpG.durative_actions_in_domain)
		    /** 
			Tipi di vincoli di ordinamento per azioni durative
			**
			Types of ordering constraints for durative actions
		    **/
		    mat_ord[posB][posAction] = Econstraint_type(vectlevel[ind_level]->action.position, ind_level, infAction->position, *infAction->level);
		  else /** 
			  Vincolo di ordinamento piu' restrittivo
			  **
			  Strongest ordering constraints
		       **/
		    mat_ord[posB][posAction] = 1;
		}

	      if (ind_level > level)
		{
		  if(GpG.constraint_type && GpG.durative_actions_in_domain)
		    /** 
			Tipi di vincoli di ordinamento per azioni durative
			**
			Types of ordering constraints for durative actions
		    **/
		    mat_ord[posAction][posB] = Econstraint_type(infAction->position, *infAction->level, vectlevel[ind_level]->action.position, ind_level);
		  else  /** 
			  Vincolo di ordinamento piu' restrittivo
			  **
			  Strongest ordering constraint
		       **/
		    mat_ord[posAction][posB] = 1;
		}
	    }
	}
    }


#ifdef __TEST__
  {
    int i,j;
  printf ("\n\nMATRICE DEI VINCOLI DI ORDINAMENTO");
  printf ("\nInserimento azione:");
  print_op_name_string (infAction->position, temp_name);
  for (i = 0; i < num_act_ord; i++)
    for (j = 0; j < num_act_ord; j++)

      if (mat_ord[i][j] != 0)
	{
	  printf ("\nl'azione %s", print_op_name_string (act_ord_vect[i]->position, temp_name));
	  printf ("al livello %d precede %s", *act_ord_vect[i]->level, print_op_name_string (act_ord_vect[j]->position, temp_name));
	  printf ("al livello %d --> tipo constraint: %d ", *act_ord_vect[j]->level,mat_ord[i][j] );
	}
  printf ("\n");
  }
#endif

}


/**
   Rimuove i vincoli tra l'azione infAction e il resto del piano
   parziale
   **
   Remove the ordering constraint between an action and the actions of
   the partial plan
**/
void remove_temporal_constraints (int posAction)
{
  int i;

#ifdef __DTEST__
  int j;
  ActNode_list infAction;
#endif


  /**
     Azzeriamo riga e colonna corrispondenti all'azione da rimuovere
     **
     Reset the line and the column corresponding to the removing action
     in the matrix of the orderings
  **/
  for (i = 0; i < num_act_ord; i++)
    {
      mat_ord[i][posAction] = 0;
      mat_ord[posAction][i] = 0;
    }


#ifdef __DTEST__
  infAction = act_ord_vect[posAction];
  printf ("\n\nMATRICE DEI VINCOLI DI ORDINAMENTO");
  printf ("\nRimozione azione:");
  print_op_name_string (infAction->position, temp_name);
  for (i = 0; i < num_act_ord; i++)
    for (j = 0; j < num_act_ord; j++)

      if (mat_ord[i][j] != 0)
	{
	  printf ("\nl'azione %s", print_op_name_string(act_ord_vect[i]->position, temp_name) );
	  printf ("al livello %d precede l'azione %s", *act_ord_vect[i]->level, print_op_name_string(act_ord_vect[j]->position, temp_name) );
	  printf ("al livello %d", *act_ord_vect[j]->level);
	}
  printf ("\n");
#endif

  /**
     L'azione viene tolta dal vettore delle corrispondenze
     **
     The action is removed from the array of the correspondences
  **/
  act_ord_vect[posAction] = NULL;

  if (posAction == (num_act_ord - 1))
    num_act_ord--;

}
     
 /**
  * Trova gli intervalli temporali da associare alle precondizioni
  * TIMED di un'azione, restituisce il time_start dell'azione che
  * permette tali associazioni e la prima precondizione che è stata
  * spostata. Inoltre segnala eventuali inconsistenze (nn esiste un
  * intervallo valido per una data precondizione)
  **/
float find_temporal_interval(float t, ActNode_list infact, int *first_moved) {

  int i, j, act_pos, pc, lev;
  float time;
  Bool fixpoint;
  Bool first;
  
  if (!gef_conn[infact -> position].timed_PC)
    return t;

  if (DEBUG3) {
    printf("\n\n");
    print_op_name(infact->position);
    printf("\nSearching temporal interval (time = %f) ...", t);
  }
  
  lev = *infact -> level;
  
  // Alloco il vettore per gli intervalli se nn è già stato fatto
  if (!infact -> PC_interval) {
    infact -> PC_interval = (int *)calloc(gnum_timed_facts, sizeof(int));
    memset(infact -> PC_interval, -1, gnum_timed_facts * sizeof(int));
  }
  
  // Resetto il vettore temporaneo su cui memorizzare gli assegnamenti
  memset(temp_PC_int, -1, gnum_timed_facts * sizeof(int)); 

  time = t;

  act_pos = infact -> position;

  fixpoint = FALSE;

  first = TRUE;
  
  if (first_moved)
    *first_moved = -1;
  
  while (!fixpoint) {
    
    fixpoint = TRUE;

    // Precondizioni at start
    for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_start; i++) {
      pc = gef_conn[act_pos].timed_PC -> PC_start[i];

      if (pc < 0)
	continue;
      
      // Cerco un intervallo, eventualmente a partire da quello precedentemente assegnato
      for (j = (first || (temp_PC_int[TIMED_IDX(pc)] < 0))?0:(temp_PC_int[TIMED_IDX(pc)]); 
	   j < NUM_INTERVALS(pc); 
	   j++) {
	time = MAX(time, gtimed_fct_vect[TIMED_IDX(pc)][j].start_time);
	if (IS_TIME_IN_INTERVAL(time, pc, j)) {
	  if (j != temp_PC_int[TIMED_IDX(pc)]) {
	    temp_PC_int[TIMED_IDX(pc)] = j;
	    fixpoint = FALSE;
	    if ((first_moved) && (first_moved < 0) && (time > t))
	      *first_moved = pc;
	  }
	  break;
	}
      }
      // Se non ho trovato nessun possibile intervallo
      if (j >= NUM_INTERVALS(pc)) {
	//printf("not found.");
	// Segnalo l'inconsistenza ed esco
	insert_unsup_timed_fact(pc, lev);
	return -1.0;
      }
    }
    
    // Precondizioni overall
    for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_overall; i++) {
      pc = gef_conn[act_pos].timed_PC -> PC_overall[i];
      
      if (pc < 0)
	continue;
      
      // Cerco un intervallo, eventualmente a partire da quello precedentemente assegnato
      for (j = (first || (temp_PC_int[TIMED_IDX(pc)] < 0))?0:(temp_PC_int[TIMED_IDX(pc)]); 
	   j < NUM_INTERVALS(pc); 
	   j++) {
	time = MAX(time, gtimed_fct_vect[TIMED_IDX(pc)][j].start_time);
	if (IS_TIME_IN_INTERVAL(time, pc, j) &&
	    IS_TIME_IN_INTERVAL(time + get_action_time (act_pos, lev), pc, j)) {
	  if (j != temp_PC_int[TIMED_IDX(pc)]) {
	    temp_PC_int[TIMED_IDX(pc)] = j;
	    fixpoint = FALSE;
	    if ((first_moved) && (first_moved < 0) && (time > t))
	      *first_moved = pc;
	  }
	  break;
	}
      }
      // Se non ho trovato nessun possibile intervallo
      if (j >= NUM_INTERVALS(pc)) {
	//printf("not found.");
	// Segnalo l'inconsistenza ed esco
	insert_unsup_timed_fact(pc, lev);
	return -1.0;
      } 
    }
    
    // Precondizioni at end
    for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_end; i++) {
      pc = gef_conn[act_pos].timed_PC -> PC_end[i];
      
      if (pc < 0)
	continue;
      
      // Cerco un intervallo, eventualmente a partire da quello precedentemente assegnato
      for (j = (first || (temp_PC_int[TIMED_IDX(pc)] < 0))?0:(temp_PC_int[TIMED_IDX(pc)]); 
	   j < NUM_INTERVALS(pc); 
	   j++) {
	time = MAX(time, gtimed_fct_vect[TIMED_IDX(pc)][j].start_time - get_action_time (act_pos, lev));
	if (IS_TIME_IN_INTERVAL(time + get_action_time (act_pos, lev), pc, j)) {
	  if (j != temp_PC_int[TIMED_IDX(pc)]) {
	    temp_PC_int[TIMED_IDX(pc)] = j;
	    fixpoint = FALSE;
	    if ((first_moved) && (first_moved < 0) && (time > t))
	      *first_moved = pc;
	  }
	  break;
	}
      }
      // Se non ho trovato nessun possibile intervallo
      if (j >= NUM_INTERVALS(pc)) {
	//printf("not found.");
	// Segnalo l'inconsistenza ed esco
	insert_unsup_timed_fact(pc, lev);
	return -1.0;
      }
    }
      
    
    first = FALSE;
    
  } // End while

    
  memcpy(infact -> PC_interval, temp_PC_int, gnum_timed_facts * sizeof(int));
  
  update_timed_vect_data(infact -> PC_interval, infact->level, C_T_INSERT_ACTION);
  
  if (DEBUG3) {
    printf("found --> Time Start = %f", time);
    printf("\n******************************");
    printf("\nIntervalli per le precondizioni dell'azione : ");
    for (i = 0; i < gnum_timed_facts; i++)
      if (infact -> PC_interval[i] >= 0) {
	printf("\n");
	print_ft_name(gtimed_fct_vect[i][infact -> PC_interval[i]].position);
	printf(" Start : %f  End : %f", gtimed_fct_vect[i][infact -> PC_interval[i]].start_time, gtimed_fct_vect[i][infact -> PC_interval[i]].end_time);
      }
  }
  
  return time;
  
}



/**
 * Aggiorna le strutture dati degli intervalli temporali in caso di rimozione o inserimento di un'azione
 **/
void update_timed_vect_data(int *PCint, int * level, int ins_rem) {

  int i, j;
  
  // Se ci sono delle associazioni con gli intervalli temporali
  if (PCint) {
    for (i = 0; i < gnum_timed_facts; i++) {
      // Se per questa azione ho una associazione dell'i-esimo timed fact ad un intervallo temporale
      if (PCint[i] >= 0) {
	// Aggiorno le info di questo intervallo temporale
	if (ins_rem == C_T_INSERT_ACTION)
	  {
	    if (gtimed_fct_vect[i][PCint[i]].levels == NULL)
	      {
		gtimed_fct_vect[i][PCint[i]].levels = (int **) calloc (MAX_NUM_ACTIONS, sizeof(int *));
		//  gtimed_fct_vect[i][PCint[i]].num_act_PC = 0;
	      }
	    
	    for (j=0; j < gtimed_fct_vect[i][PCint[i]].num_act_PC; j++)
	      if (gtimed_fct_vect[i][PCint[i]].levels[j] == level) 
		{
		  if (DEBUG5) {
		    printf("\nAction already inserted : ");
		    print_op_name(GET_ACTION_POSITION_OF_LEVEL(*level));
		  }
		  break;
		}
	    
	    if (j == gtimed_fct_vect[i][PCint[i]].num_act_PC)
	      {
		gtimed_fct_vect[i][PCint[i]].levels[gtimed_fct_vect[i][PCint[i]].num_act_PC] = level;
		gtimed_fct_vect[i][PCint[i]].num_act_PC++;
	      }
	  }
	else
	  {
	    if(gtimed_fct_vect[i][PCint[i]].num_act_PC>0)
	      {
		gtimed_fct_vect[i][PCint[i]].num_act_PC--;
	      }
	    else
	      {
		printf("\nError : num_act_PC <= 0 for interval %d in timed fact %s", PCint[i], print_ft_name_string(gtimed_fct_vect[i][PCint[i]].position, temp_name));
	      }

	    for (j=0; j < gtimed_fct_vect[i][PCint[i]].num_act_PC; j++)
	      {
		if (gtimed_fct_vect[i][PCint[i]].levels[j] == level)
		  {
		    gtimed_fct_vect[i][PCint[i]].levels[j] = gtimed_fct_vect[i][PCint[i]].levels[gtimed_fct_vect[i][PCint[i]].num_act_PC];
		    gtimed_fct_vect[i][PCint[i]].levels[gtimed_fct_vect[i][PCint[i]].num_act_PC] = NULL;
		    break;
		  }
		if (j == gtimed_fct_vect[i][PCint[i]].num_act_PC)
		  printf("\nWarning: Action for temporal literal not found");
	      }
	  }
      }
    }

  }
  
}


/**
 * Inserisce in una lista le inconsistenze temporali
 **/
void insert_unsup_timed_fact(int fact_pos, int level) {

  FctNode_list tmd_fact;

  if (fact_pos < 0)
    return;

  if (gft_conn[fact_pos].fact_type != IS_TIMED) {

#ifdef __MY_OUTPUT__
    printf("Warning : %d is not a timed fact.", fact_pos);
#endif   

    return;
  }

  tmd_fact = CONVERT_FACT_TO_NODE(fact_pos, level);

  if (tmd_fact -> false_position >= 0) {

#ifdef __MY_OUTPUT
    printf("Warning : %d already inserted.", fact_pos);
#endif  

    return;
  }
 
  if (unsup_tmd_facts[GpG.num_false_tmd_fa] == NULL)
    unsup_tmd_facts[GpG.num_false_tmd_fa] = (constraints_list) malloc (sizeof (constraints));
  unsup_tmd_facts[GpG.num_false_tmd_fa]->fact = fact_pos;
  unsup_tmd_facts[GpG.num_false_tmd_fa]->action = -1;
  unsup_tmd_facts[GpG.num_false_tmd_fa]->constraint_type = C_T_UNSUP_TMD_FACT;
  unsup_tmd_facts[GpG.num_false_tmd_fa]->level = &(vectlevel[level]->level);
  tmd_fact -> false_position = GpG.num_false_tmd_fa;
  GpG.num_false_tmd_fa++;

  if (DEBUG3) {
    printf("\nInserita inconsistenza temporale (livello %d) : ", level);
    print_ft_name(fact_pos);
  }

  if (GpG.num_false_tmd_fa >= MAX_FALSE){
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_MAX_FALSE );
#else
    printf( WAR_MAX_FALSE );
#endif    
    exit (1);
  }
  /*
  printf("\nNuovo timed fact non supportato : ");
  print_ft_name(fact_pos);
  */
}

/**
 * Rimuove una inconsistenza dalla lista delle inconsistenze temporali
 **/
void remove_unsup_timed_fact(FctNode_list false_tmd) {

  FctNode_list tmd_fact;
  int fact_pos, level, false_pos;
  constraints_list tmp;

  false_pos = false_tmd -> false_position;

  if (GpG.num_false_tmd_fa == 0)
    return;
  if (false_pos < 0)
    return;
  if (false_pos >= GpG.num_false_tmd_fa)
    return;
  if (!unsup_tmd_facts[false_pos])
    return;

  fact_pos = unsup_tmd_facts[false_pos] -> fact;
  
  level = *(unsup_tmd_facts[false_pos] -> level);
  tmd_fact = CONVERT_FACT_TO_NODE(fact_pos, level);

  tmd_fact -> false_position = -1;
  
  tmp = unsup_tmd_facts[false_pos];
  tmp -> fact = -1;
  unsup_tmd_facts[false_pos] = unsup_tmd_facts[GpG.num_false_tmd_fa - 1];
  
  if (GpG.num_false_tmd_fa > (false_pos + 1))
    CONVERT_FACT_TO_NODE(unsup_tmd_facts[false_pos]->fact, *(unsup_tmd_facts[false_pos]->level))->false_position = false_pos;
  
  unsup_tmd_facts[GpG.num_false_tmd_fa - 1] = tmp;

  GpG.num_false_tmd_fa--;

  if (DEBUG3) {
    printf("\nInconsistenza temporale rimossa (livello %d) : ", *false_tmd -> level);
    print_ft_name(fact_pos);
  }

}

/**
 * Rimuove tutte le inconsistenze associate ai timed facts che sono precondizioni
 * dell'azione infact
 **/
void remove_all_unsup_tmd_of_act(ActNode_list infact) {

  int i, pc;

  if (!gef_conn[infact -> position].timed_PC)
    return;
  
  /*
  printf("\nRimuovo le inconsistenze (timed) legate all'azione : ");
  print_op_name(infact -> position);
  */
  for (i = 0; i < gef_conn[infact -> position].timed_PC -> num_PC_start; i++) {
    pc = gef_conn[infact -> position].timed_PC -> PC_start[i];
    // Se la precondizione timed pc era stata messa tra le inconsistenze la rimuovo
    if (CONVERT_FACT_TO_NODE(pc, *infact -> level) -> false_position >= 0)
      remove_unsup_timed_fact(CONVERT_FACT_TO_NODE(pc, *infact -> level));
  }

  for (i = 0; i < gef_conn[infact -> position].timed_PC -> num_PC_overall; i++) {
    pc = gef_conn[infact -> position].timed_PC -> PC_overall[i];
    // Se la precondizione timed pc era stata messa tra le inconsistenze la rimuovo
    if (CONVERT_FACT_TO_NODE(pc, *infact -> level) -> false_position >= 0)
      remove_unsup_timed_fact(CONVERT_FACT_TO_NODE(pc, *infact -> level));
  }

  for (i = 0; i < gef_conn[infact -> position].timed_PC -> num_PC_end; i++) {
    pc = gef_conn[infact -> position].timed_PC -> PC_end[i];
    // Se la precondizione timed pc era stata messa tra le inconsistenze la rimuovo
    if (CONVERT_FACT_TO_NODE(pc, *infact -> level) -> false_position >= 0)
      remove_unsup_timed_fact(CONVERT_FACT_TO_NODE(pc, *infact -> level));
  }

}






/**
 * Controlla il se time assegnato all'azione infact è consistente o meno con gli
 * intervalli associati alle sue precondizioni temporali. Aggiorna la lista
 * delle inconsistenze e restituisce il time, eventualmente modificato 
 * in caso quello passato fosse inconsistente e ne esista uno
 * consistente.
 *
 * start = tempo di inizio attualmente assegnato all'azione
 * tprec = tempo di inizio che avrebbe senza tenere conto dei timed (solo precondizioni normali e mutex)
 **/
float check_time_interval(float tprec, ActNode_list infact) {

  float time, start;
  int first_moved;
  int *PCint;
  
  if (gef_conn[infact -> position]. act_type == TIMED_FACT_ACT) {
	printf("\nWarning ---> check_time_interval : Azione fittizia!!");
	  return tprec;
  }
  
  start = infact -> time_f -  get_action_time (infact -> position, *infact -> level);

  PCint =  (int *)calloc(gnum_timed_facts, sizeof(int));
  // Copio le associazioni attuali per i timed facts
  memcpy(PCint, infact -> PC_interval, gnum_timed_facts * sizeof(int));

  // Ricalcolo gli intervalli associati alle preconds dell'azione e il time_start
  time = find_temporal_interval(tprec, infact, &first_moved);

  // Se non ho modificato il tempo e tprec è inconsistente
  if (time < 0) {
    /*
      shifted_act[num_shifted_act].act_pos = infact -> position;
      shifted_act[num_shifted_act].act_level = *infact -> level;
      shifted_act[num_shifted_act].constraint_type = C_T_REMOVE_ACTION;
      num_shifted_act++;
    */
    free(PCint);
    return -1.0;
  }

  // Se non ho modificato l'intervallo e tprec è consistente
  else if (time == start) {
    // Rimuovo le inconsistenze che erano state segnalate
    remove_all_unsup_tmd_of_act(infact);
    free(PCint);
    return time;
  }

  // Se l'istante start era inconsistente e sono passato ad un intervallo successivo 
  else if (time > start) {
    /*
      shifted_act[num_shifted_act].act_pos = infact -> position;
      shifted_act[num_shifted_act].act_level = *infact -> level;
      shifted_act[num_shifted_act].constraint_type = C_T_REMOVE_ACTION;
      num_shifted_act++;
      memcpy(infact -> PC_interval, PCint, gnum_timed_facts * sizeof(int));
      // Segnalo un inconsistenza sulla prima precondizione timed che è stata spostata
      if (first_moved >= 0) {
      insert_unsup_timed_fact(first_moved, *infact -> level);
      }
    */
    update_timed_vect_data(PCint, infact->level ,C_T_REMOVE_ACTION);
    update_timed_vect_data(infact -> PC_interval, infact->level, C_T_INSERT_ACTION);
    
    free(PCint);
    return time;
  }

  // Se l'azione può essere spostata in un intervallo precedente
  else if (time >= 0 && time < start) {
    // Rimuovo le inconsistenze che erano state segnalate
    remove_all_unsup_tmd_of_act(infact);
    // Aggiorno i dati relativi agli intervalli temporali

    update_timed_vect_data(PCint, infact->level ,C_T_REMOVE_ACTION);
    update_timed_vect_data(infact -> PC_interval, infact->level, C_T_INSERT_ACTION);
    free(PCint);
    return time;
  }
  free(PCint);
  return start; 

}





/**
 * Fissa un'inconsistenza temporale (timed fact)
 **/
int fix_unsup_timed_fact(constraints_list unsup_tmd_fct, int num, float new_time) {

  int num_min, num_neg, choice, level, i;
  EfConn *act;
  float best = 0.0;
  float shift_cost = 0.0;
  FctNode_list tofix;

  tofix = CONVERT_FACT_TO_NODE (unsup_tmd_fct->fact, *unsup_tmd_fct->level);
  
  if (DEBUG2)
    {
      printf
	("\n\n### INC CHOICE:\n  Unsupported timed fact: position %d, level %d fact name : ",
	 unsup_tmd_fct->fact, *unsup_tmd_fct->level);
      print_ft_name (unsup_tmd_fct->fact);
      printf ("\n");
    }

#ifdef __TEST__

  if (unsup_tmd_fct->constraint_type != C_T_UNSUP_TMD_FACT) {
    
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else
    printf( WAR_BUG );
#endif
  }
  
  if (GpG.temporal_plan)
    check_temporal_plan ();

#endif

  /*
  if(GpG.timed_facts_present) 
    slack_fact_from_act (Hvar.constr);
  
  if(GpG.timed_facts_present && DEBUG3)
    for (i=0; i < gnum_timed_facts; i++)
      for (j=0; j < gnum_tmd_interval[i]; j++)
	{
	  timedFct = &gtimed_fct_vect[i][j];
	  printf("\nslack of %s: %.2f", print_ft_name_string(timedFct->position,temp_name),timedFct->slack);
	}
  */

  // Reset shifted_act;
  num_shifted_act = 0;
  
  // Calcolo il costo per shiftare l'azione
  for (i = 0; i < num_shifted_act; i++)
    shift_cost += action_cost(&shifted_act[i]);

  if (num <= 0 && num_shifted_act <= 0)
    {
#ifdef __MY_OUTPUT__
      printf ("\n   Warning: step %d - num action for make supported tmd fact %d == 0, level %d, name ",GpG.count_num_try, unsup_tmd_fct->fact,  *unsup_tmd_fct->level);
      print_ft_name(unsup_tmd_fct->fact);
#endif
      remove_unsup_timed_fact(tofix);
      return (FALSE);
    }

  // Find the action set from the neighborhood with lower cost and insert them in pos_temp_vect.
  // If more than one action has negative cost, insert them in pos_temp_vect.
  // The cost is put in "best" var.
  if (DEBUG3)
    {
      printf ("\n>< NEIGHBORHOOD EVALUTATION ><  Num act: %d\n", num);
      if (num < 0)
	printf ("\n\n  ___NO ACTIONS\n");
      if (num == 1)
	printf ("\n\n  ___Only ONE action ENABLE");
    }

  if (num > 1)
    best = find_min (unsup_tmd_fct, pos_temp_vect, num, &num_min, &num_neg);
  else if (num == 1) 
    best = action_cost(neighb_vect[0]);

  // Se ho risolto l'inconsistenza shiftando gli intervalli temporali con un costo minore di quello degli altri vicini, esco
  if ((shift_cost <= best) && (new_time >=0)) {
    remove_unsup_timed_fact (tofix);

    if (DEBUG1) {
      printf("\nAzione shiftata (time = %f) : ", new_time);
      print_op_name(GET_ACTION_POSITION_OF_LEVEL(*tofix->level));
    }
    
    return 0;
  }
  if (num_shifted_act < 0) num_shifted_act = 0;
 
  // Altrimenti valuto il vicinato per la rimozione di un'azione 

  if (num <=1) 
    {
      num_min = 1;
      pos_temp_vect[0] = 0;
    }
  GpG.is_lm = 0;		// LM Per default NON considero la configuraz. corrente come un minimo locale
  if (num == 1)
    {
      choice = 0;			// choose_actions() sets "num" to 1 if ME relations were updated   
      neighb_vect[choice]->cost.weight=0.0;
      neighb_vect[choice]->cost.act_cost=0.0;
      neighb_vect[choice]->cost.act_time=0.0;
    }
  else if (best > 0)
    {
      GpG.is_lm = 1;		// LM Siamo in un minimo locale
      if (( MY_RANDOM % GpG.denominator) < GpG.numerator)
	{
	  choice = MY_RANDOM % num;
	  if (DEBUG1)
	    printf("\n Random choice= %d",choice);
	}
      else if (num_min == 1)
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
  //if (choice >= 0)
    //remove_unsup_timed_fact (tofix);
  
  choice =
    insert_remove_action (neighb_vect[choice]->act_pos,
			  neighb_vect[choice]->act_level,
			  neighb_vect[choice]->constraint_type,
			  GpG.approximation_level);
  
#ifdef __TEST__
  check_plan (GpG.curr_plan_length);
  if (DEBUG6)
    my_print_plan ((*tofix->level) - 1);

  if (GpG.temporal_plan)
    check_temporal_plan ();
  check_plan (GpG.curr_plan_length);
  
#endif

  return (choice);
}

/**
 * Selezione di un'inconsistenza temporale
 **/
int choose_min_cost_unsup_tmd_fact () {
  int i, best = 0, min_level = 0;
  float min = 100000.0, min_constr = 100000.0, curr_min_constr = 100000.0, tot, endtime;
  dg_inform_list loc_dg_cost;
  
  if (GpG.inc_choice_type == MIN_LEVEL_INC
      || GpG.inc_choice_type == MIN_LEVEL_COST_INC
      || GpG.inc_choice_type == MIN_LEVEL_CONSTR_INC)
    min_level = 100000;
  else if (GpG.inc_choice_type == MAX_LEVEL_INC)
    min_level = 0;
  if (GpG.inc_choice_type == MIN_COST_INC
      || GpG.inc_choice_type == MIN_LEVEL_COST_INC)
    min = 100000.0;
  if (GpG.inc_choice_type == MAX_COST_INC)
    min = 0.0;
  
  best = MY_RANDOM % GpG.num_false_tmd_fa;
   
  for (i = GpG.num_false_tmd_fa - 1; i >= 0; i--)
    {
      
      if (GpG.inc_choice_type == MIN_LEVEL_INC)
	{

	  if (min_level > *unsup_tmd_facts[i]->level
	      || (min_level == *unsup_tmd_facts[i]->level && MY_RANDOM % 2))
	    {
	      min_level = *unsup_tmd_facts[i]->level;
	      best = i;
	    }
	}
      else if (GpG.inc_choice_type == MIN_LEVEL_COST_INC)
	{

	  if (min_level > *unsup_tmd_facts[i]->level)
	    {
	      min_level = *unsup_tmd_facts[i]->level;
	      best = i;
	      get_dg_fact_cost (unsup_tmd_facts[i]->fact,
				*unsup_tmd_facts[i]->level, &loc_dg_cost);
           if(GpG.verify_inc_choice)
	              min = loc_dg_cost->num_actions;
	   else
	      min = loc_dg_cost->totcost;
	    }
	  else if (min_level == *unsup_tmd_facts[i]->level)
	    {

	      get_dg_fact_cost (unsup_tmd_facts[i]->fact,
				*unsup_tmd_facts[i]->level, &loc_dg_cost);
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
      else if (GpG.inc_choice_type == MIN_LEVEL_CONSTR_INC)
	{

	  if (min_level > *unsup_tmd_facts[i]->level)
	    {
	      min_level = *unsup_tmd_facts[i]->level;
	      best = i;
	      min_constr =
		compute_constr_fact ( unsup_tmd_facts[i]->fact, unsup_tmd_facts[i]->fact,
				     *unsup_tmd_facts[i]->level, 1,*unsup_tmd_facts[i]->level, &min, &endtime);
	      /**
	      get_dg_fact_cost (unsup_tmd_facts[i]->fact,
				*unsup_tmd_facts[i]->level, &loc_dg_cost);
              if(GpG.verify_inc_choice)
	         min = loc_dg_cost->num_actions;
	      else
	      min = loc_dg_cost->totcost;

	      **/
	    }
	  else if (min_level == *unsup_tmd_facts[i]->level)
	    {

	      curr_min_constr =
		compute_constr_fact ( unsup_tmd_facts[i]->fact, unsup_tmd_facts[i]->fact,
				     *unsup_tmd_facts[i]->level, 1, *unsup_tmd_facts[i]->level, &tot, &endtime);
	   
	      /**

	      get_dg_fact_cost (unsup_tmd_facts[i]->fact,
				*unsup_tmd_facts[i]->level, &loc_dg_cost);
             if(GpG.verify_inc_choice) 
                tot= loc_dg_cost->num_actions;
             else
                tot= loc_dg_cost->totcost;

	      **/

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
      else if (GpG.inc_choice_type == MIN_LEVEL_MIN_CONSTR_INC)
	{

	  if (min_level > *unsup_tmd_facts[i]->level)
	    {
	      min_level = *unsup_tmd_facts[i]->level;
	      best = i;
	      min_constr =
		compute_constr_fact ( unsup_tmd_facts[i]->fact, unsup_tmd_facts[i]->fact,
				     *unsup_tmd_facts[i]->level, 1, *unsup_tmd_facts[i]->level, &min, &endtime);

	      /**
	      get_dg_fact_cost (unsup_tmd_facts[i]->fact,
				*unsup_tmd_facts[i]->level, &loc_dg_cost);



              if(GpG.verify_inc_choice)
	          min = loc_dg_cost->num_actions;
              else
	          min = loc_dg_cost->totcost;	    
	    
	      min = loc_dg_cost->totcost;
	      **/
	    }
	  else if (min_level == *unsup_tmd_facts[i]->level)
	    {

	      curr_min_constr =
		compute_constr_fact ( unsup_tmd_facts[i]->fact, unsup_tmd_facts[i]->fact,
				     *unsup_tmd_facts[i]->level, 1, *unsup_tmd_facts[i]->level, &tot, &endtime );

	      /**
	      get_dg_fact_cost (unsup_tmd_facts[i]->fact,
				*unsup_tmd_facts[i]->level, &loc_dg_cost);
	     
	

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
		}



	    }
	}
      else if (GpG.inc_choice_type == MAX_LEVEL_INC)
	{

	  if (min_level < *unsup_tmd_facts[i]->level)
	    {
	      min_level = *unsup_tmd_facts[i]->level;
	      best = i;
	    }
	}
      else if (GpG.inc_choice_type == MIN_COST_INC)
	{

	  get_dg_fact_cost (unsup_tmd_facts[i]->fact, *unsup_tmd_facts[i]->level ,
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

	  get_dg_fact_cost (unsup_tmd_facts[i]->fact, *unsup_tmd_facts[i]->level,
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


      // printf("\n Fatto: %d Costo: %2.10f",unsup_tmd_facts[i]->fact,loc_dg_cost->totcost);
    }

  return best;
}

/**
 * Vicinato per i timed facts
 **/
int define_neighborhood_for_timed_fact (register FctNode_list tofix, float *new_time, int initialize)
{
 
  ActNode_list inf_action;
  ActNode_list index_act;
  neighb temp_act;
  int tmd_idx, new_interval;
  float tstart, duration, totDur_CrtPath;


  totDur_CrtPath = 0;
  
  if (initialize != 0)
    reset_neighborhood ();

  if (*tofix->level > GpG.curr_plan_length)
    return 0;
  
#ifdef __TEST__
  check_plan (GpG.curr_plan_length);
  
#endif

  tmd_idx = TIMED_IDX(tofix -> position);
  inf_action = GET_ACTION_OF_LEVEL(*tofix -> level);

  // Se ho degli intervalli disponibili
  if (inf_action -> PC_interval[tmd_idx] < (gnum_tmd_interval[tmd_idx] - 1)) {
 
    duration = get_action_time(inf_action -> position, *inf_action -> level);
    tstart = inf_action -> time_f - duration; 
    new_interval = inf_action -> PC_interval[tmd_idx] + 1;
    
    // Provo a shiftare l'azione e vedo quali azioni dovranno essere a loro volta spostate
    if (is_fact_in_preconditions_end(inf_action -> position, tofix -> position))
      (*new_time) = MAX(tstart, gtimed_fct_vect[tmd_idx][new_interval].end_time - duration);
      
    else
      (*new_time) = MAX(tstart, gtimed_fct_vect[tmd_idx][new_interval].start_time);

    (*new_time) = find_temporal_interval((*new_time), inf_action, NULL);
 
    if (((*new_time) >= 0) && ((*new_time) != (inf_action -> time_f + get_action_time(inf_action->position, *inf_action->level))))  
      // Propago i tempi e salvo le azioni che hanno preconds timed che verrebbero rese inconsistenti
      insert_time(inf_action);
  }

  // Inserisco nel vicinato gli elementi che stanno sul critical path
  if (DEBUG3)
    printf("\n\nEvaluate neighborhood : searching in CRITICAL PATH of %s",  print_op_name_string(inf_action -> position, temp_name));
 
  for (index_act = inf_action; index_act; index_act = index_act -> action_f) {

    temp_act.act_pos = index_act -> position;
    temp_act.act_level = *index_act->level;
    temp_act.constraint_type = C_T_REMOVE_ACTION;
    temp_act.unsup_fact = tofix -> position;

    insert_element_in_neighb (&temp_act);
    
    totDur_CrtPath += get_action_time(index_act -> position, *index_act->level);
    
    slack_vect[*index_act->level] = totDur_CrtPath;
    
    if (DEBUG3)
      printf("\nNew action in neighborhood: %s at level %d", print_op_name_string(index_act -> position, temp_name), *index_act->level);
  }
  
  return (num_neighborhood);
}





/*********************************
 * FUNZIONI PER STIMARE LO SLACK *
 *********************************/




void compute_slack (ActNode_list infAction)
{  
  int level, ordering,i;
  float tempslack;

  level = *infAction->level;


  for (i = level + 1; i < GpG.curr_plan_length; i++)
    {
      
      if (GET_ACTION_POSITION_OF_LEVEL(i) < 0)
	continue;

      ordering = get_constraint_type(infAction->position, *infAction->level, vectlevel[i]->action.position, *vectlevel[i]->action.level);

      if ( ordering > 0 )
	{ 
	  if (DEBUG5) {
	    printf("\n%s ",print_op_name_string(infAction->position, temp_name));
	    printf("is ordered with %s [%d]", print_op_name_string(vectlevel[i]->action.position, temp_name), ordering);
	  }


	  if (ordering == EA_SB) 
	    tempslack = vectlevel[i]->action.time_f - get_action_time(vectlevel[i]->action.position, i) - infAction->time_f;
	  else
	    if (ordering == EA_EB)
	      tempslack = vectlevel[i]->action.time_f - infAction->time_f;
	    else
	      if (ordering == SA_SB)
		tempslack = vectlevel[i]->action.time_f - get_action_time(vectlevel[i]->action.position, i) - (infAction->time_f - get_action_time(infAction->position, level));
	      else /* ordering == SA_EB */
		tempslack = infAction->time_f - get_action_time(infAction->position, level) - vectlevel[i]->action.time_f;
	  insert_propagation_list (GET_ACTION_OF_LEVEL(i));

	  tempslack += slack_vect[level];

	  if(slack_vect[i] > 0)
	    {
	      if ( tempslack < slack_vect[i])
		{
		  slack_vect[i] = tempslack;
		  if (DEBUG5)
		    printf("\nslack assigned %.2f",slack_vect[i]);
		}
	    }
	  else
	    {
	      slack_vect[i] = tempslack;
	      if (DEBUG5)
		printf("\nslack assigned %.2f",slack_vect[i]);
	    }
	  
	}
      
    }


}




void slack_adj (ActNode_list infAction)
{

  int level, ind;

  level = *infAction->level;

  /* Per tutti i livelli... */
  for (ind = level ; ind < GpG.curr_plan_length; ind++)
    {
      if (prop_level_index[ind] == -1)
	continue;

      /* Se l'azione e' nella propagation_list allora vengono ricalcolati i tempi */
      compute_slack (GET_ACTION_OF_LEVEL (ind));
      prop_level_index[ind] = -1;
    }

}





void slack_fact_from_act (constraints_list fix)
{

  ActNode_list infAction;
  int level,i,j,k;
  Timed_list timedFct;


  level = *fix->level;
  infAction = &vectlevel[level]->action;

  if(infAction->position <0)
    {
      for (i=0; i < gnum_timed_facts; i++)
	for (j=0; j < gnum_tmd_interval[i]; j++)
	  gtimed_fct_vect[i][j].slack = MAXFLOAT;

      return;
    }

  reset_propagation_vect ();
  memset (slack_vect, -1.0, MAX_PLAN_LENGTH * sizeof (float));

  if(is_fact_in_preconditions(infAction->position, fix->fact) || is_fact_in_preconditions_overall(infAction->position, fix->fact))
    slack_vect[level] = infAction->time_f - get_action_time(infAction->position, level);
  else
    {
      if(is_fact_in_preconditions_end(infAction->position, fix->fact))
	slack_vect[level] = infAction->time_f;
      else
	{
	  printf("\nError (in slack_fact_from_act) : %s %d", print_ft_name_string(fix->fact,temp_name), fix->fact);
	  printf("is not precondition of %s at level %d", print_op_name_string(infAction -> position, temp_name), level);
	}
    }
  insert_propagation_list (infAction);

  slack_adj(infAction);

  if (DEBUG5)
    printf("\n\n numtry %d PRINT SLACK of %s of level %d\n",num_try,print_ft_name_string(fix->fact,temp_name), level );
  for (i = 0; i < GpG.curr_plan_length; i++)
    {
      if(slack_vect[i]>=0)
	{
	  if (DEBUG5) {
	    printf("slack among %s ",print_ft_name_string(fix->fact,temp_name));
	    printf("and action %s of level %d is %.2f\n", print_op_name_string(GET_ACTION_OF_LEVEL(i)->position,temp_name),i,slack_vect[i]);
	  }
	}
    }
  
  if (DEBUG5)
    print_actions_in_subgraph ();

  for (i=0; i < gnum_timed_facts; i++)
    for (j=0; j < gnum_tmd_interval[i]; j++)
      {
	timedFct = &gtimed_fct_vect[i][j];

	timedFct->slack = MAXFLOAT;

	for (k=0; k < timedFct->num_act_PC; k++)
	  {
	    infAction = GET_ACTION_OF_LEVEL(*timedFct->levels[k]);

	    if(is_fact_in_preconditions_overall(infAction->position, timedFct->position) || is_fact_in_preconditions_end(infAction->position, timedFct->position))
	      {
		if (timedFct->end_time - infAction->time_f > 0)
		  {
		    if (timedFct->slack > slack_vect[*infAction->level] + timedFct->end_time - infAction->time_f)
		      timedFct->slack = slack_vect[*infAction->level] + timedFct->end_time - infAction->time_f;
		  }
	      }
	    else
	      if(is_fact_in_preconditions(infAction->position, timedFct->position))
		{
		  if (timedFct->end_time - (infAction->time_f - get_action_time(infAction->position, *infAction->level) ) > 0)
		    {
		      if (timedFct->slack > slack_vect[*infAction->level] + timedFct->end_time - (infAction->time_f - get_action_time(infAction->position, *infAction->level)))
			timedFct->slack = slack_vect[*infAction->level] + timedFct->end_time - (infAction->time_f - get_action_time(infAction->position, *infAction->level));
		    }
		}
	      else {
		printf("\nError : Timed fact %s isn't a precondition of ", print_ft_name_string(timedFct -> position, temp_name));
		print_op_name(GET_ACTION_POSITION_OF_LEVEL(*timedFct->levels[k]));
	      }
	  }
      }

}

