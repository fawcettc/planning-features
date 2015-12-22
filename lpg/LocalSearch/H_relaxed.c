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
 * File: H_relaxed.c
 * Description: Computes the RelaxedPlan heuristic (ICAPS-03).
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
#include "inst_utils.h"
#include "H_relaxed.h"
#include "ComputeReachInf.h"
#include "H_max.h"
#include "utilities.h"
#include "numeric.h"
#include "LpgOutput.h"
#include "output.h"
#include "LpgTime.h"
#include "LocalSearch.h"
#include "ActionSubgraph.h"
#include "derivedpred.h"

#define __TEST_ITER__
void print_dg_inform(dg_inform_list dg_fact_node)
{
  printf("\nDg inform for");
  printf(" Fact %d - ", dg_fact_node->fact_pos);
  print_ft_name(dg_fact_node->fact_pos);
  printf(" num_actions %d ",dg_fact_node->num_actions);
  printf(" level %d ",*dg_fact_node->level);
  printf(" best act %d - ",dg_fact_node->best_act);
  print_op_name(dg_fact_node->best_act);
  printf(" related fact %d ",dg_fact_node->related_fact);
  printf(" stop %d ",dg_fact_node->stop);
}

/**
 * Cerco se ci sono degli intervalli temporali associabili alle precondizioni dell'azione act_pos
 * e compatibili con il tempo t.
 **/
float search_for_pc_intervals(float t, int act_pos, int lev, int *num_Timed_Prec) {

  int i, j, pc;
  float time;
  Bool fixpoint;
  Bool first;

   *num_Timed_Prec = 0;

  if (!gef_conn[act_pos].timed_PC) 
    return t;

  if(DEBUG3)
    {
      printf("\n\n********* >< Evaluate time interval for preconds of %s >< *********", print_op_name_string(act_pos, temp_name));
      printf("\n ----> Time : %.2f", t);
    }

  if (DEBUG3) {
    printf("\n\n******** >< Evaluate time interval for preconds of %s >< *********", print_op_name_string(act_pos, temp_name));
    printf("\n ----> Time : %.2f", t);
  }
  
  *num_Timed_Prec = 0;

  // Alloco un vettore temporaneo su cui memorizzare gli assegnamenti
  memset(temp_PC_int, -1, gnum_timed_facts * sizeof(int)); 

  time = t;

  fixpoint = FALSE;

  first = TRUE;
  
  while (!fixpoint) {
    
    fixpoint = TRUE;

    // Precondizioni at start
    for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_start; i++) {
      pc = gef_conn[act_pos].timed_PC -> PC_start[i];

      if (pc < 0)
	continue;

      // Se so già che nn esiste un intervallo per questa precondizione, la salto
      if (temp_PC_int[TIMED_IDX(pc)] < -1) 
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
	  }
	  break;
	}
      }
      // Se non ho trovato nessun possibile intervallo
      if (j >= NUM_INTERVALS(pc)) {
	(*num_Timed_Prec)++;
	// Marco la pc in modo da nn riconsiderarla la prossima volta
	temp_PC_int[TIMED_IDX(pc)] = -2;
	if (DEBUG3)
	  printf("\nNo temporal interval found for %s", print_ft_name_string(pc, temp_name));
      }
    }
    
    // Precondizioni overall
    for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_overall; i++) {
      pc = gef_conn[act_pos].timed_PC -> PC_overall[i];

      if (pc < 0)
	continue;
      
      if (temp_PC_int[TIMED_IDX(pc)] < -1) 
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
	  }
	  break;
	}
      }
      // Se non ho trovato nessun possibile intervallo
      if (j >= NUM_INTERVALS(pc)) {
	(*num_Timed_Prec)++;
	// Marco la pc in modo da nn riconsiderarla la prossima volta
	temp_PC_int[TIMED_IDX(pc)] = -2;
	if (DEBUG3)
	  printf("\nNo temporal interval found for %s", print_ft_name_string(pc, temp_name));
      }
    }
    
    // Precondizioni at end
    for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_end; i++) {
      pc = gef_conn[act_pos].timed_PC -> PC_end[i];
      
      if (pc < 0)
	continue;
      
      if (temp_PC_int[TIMED_IDX(pc)] < -1) 
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
	  }
	  break;
	}
      }
      // Se non ho trovato nessun possibile intervallo
      if (j >= NUM_INTERVALS(pc)) {
	(*num_Timed_Prec)++;
	// Marco la pc in modo da nn riconsiderarla la prossima volta
	temp_PC_int[TIMED_IDX(pc)] = -2;
	if (DEBUG3)
	  printf("\nNo temporal interval found for %s", print_ft_name_string(pc, temp_name));
      }
    }
    
    first = FALSE;

  } // End while
  
  
  if (DEBUG3) {
    for (i = 0; i < gnum_timed_facts; i++) {
      pc = gtimed_fct_vect[i][0].position;
      if (is_fact_in_preconditions(act_pos, pc) || is_fact_in_preconditions_overall(act_pos, pc) || is_fact_in_preconditions_end(act_pos, pc)) {
	printf("\nTemporal interval associated to %s : ", print_ft_name_string(pc, temp_name));
	if (temp_PC_int[i] >= 0)
	  printf("%.2f - %.2f", gtimed_fct_vect[i][temp_PC_int[i]].start_time, gtimed_fct_vect[i][temp_PC_int[i]].end_time);
	else 
	  printf("ANY");
      }
    }
    printf("\nTime for action %s level %d : %.2f", print_op_name_string(act_pos, temp_name), lev, (*num_Timed_Prec == 0)?time:-1.0);
    printf("\nNumber of incons : %d", *num_Timed_Prec);
    printf("\n****** >< ****************** >< ******");
  }
    
  if ((*num_Timed_Prec) > 0)
    return -1.0;

  return time;
 
}






/* Alloca nodi dg_node o utilizza nodi dg_node gia' allocati*/
struct _DG_ACT * calloc_dg_inform()
{
  static int index=0;
  //  static dg_inform_list dg_delete_array;
  dg_inform_list dg_node=NULL;



  if (Hvar.dg_delete_array==NULL && (Hvar.dg_inform_array==NULL || index==DG_ARRAY_DIM) )
    {
      index=0;
      Hvar.dg_inform_array=(dg_inform_list) calloc (DG_ARRAY_DIM, sizeof (_dg_act));

    }

  if(Hvar.dg_delete_array!=NULL)
    {
      dg_node=Hvar.dg_delete_array;
      Hvar.dg_delete_array=Hvar.dg_delete_array->prev;
    }
  else 
    {
      dg_node=&Hvar.dg_inform_array[index];
      index++;
    }

  return(dg_node);
}



/* Mette i nodi dg_node che non servono piu' nella lista dg_delete_array */
void free_dg_inform(dg_inform_list dg_node)
{
#ifdef __TEST__
  if (dg_node==NULL)
    printf("\nErrore nella disallocazione delle strutture dg_act");
#endif
  if (dg_node==NULL)
    return;
  dg_node->prev=Hvar.dg_delete_array;
  dg_node->next=NULL;
  Hvar.dg_delete_array=dg_node;

}






float get_cost_for_future_possibilities(int action, int level, float action_start_time, float action_end_time) {

  int tmd, j, k, fct, act_select, num_inc = 0, temp = 0;
  float cost = 0.0, last_dur = MAXFLOAT, duration;

  // Conto le inconsistenze a livelli superiori a level
  for (j = 0; j < GpG.num_false_fa; j++)
    if ((unsup_fact[j] -> fact >= 0) && (*unsup_fact[j] -> level >= level) && !GET_BIT (Hvar.bit_vect_facts, unsup_fact[j] -> fact ))
      num_inc++;

  for (tmd = 0; tmd < gnum_timed_facts; tmd++) {
    for (j = 0; j < gnum_tmd_interval[tmd]; j++) {
      
      if (action_start_time >= gtimed_fct_vect[tmd][j].end_time)
	continue;

      fct = gtimed_fct_vect[tmd][j].position;

      // Scelgo l'azione con durata minore tra quelle che hanno per precondizione il timed
      for (k = 0; k < gft_conn[fct].num_PC; k++) {
	duration = get_action_time(gft_conn[fct].PC[k], level);
	if (duration < last_dur) {
	  last_dur = duration;
	  act_select = gft_conn[fct].PC[k];
	}
      }

      // Valuto la porzione di intervallo temporale utile ad applicare l'azione
      if (action_end_time <= gtimed_fct_vect[tmd][j].start_time)
	duration = gtimed_fct_vect[tmd][j].duration;
      else 
	duration = MAX(0, (gtimed_fct_vect[tmd][j].end_time - action_end_time));

      // Valuto quante volte l'azione può essere eseguita nel tempo stimato 
      temp += (int)(duration / last_dur);
       
    }
  }

  cost = MAX(0, (num_inc - temp));

  if(DEBUG3)
    printf ("\n\nINC: %d, ACT in following TIMED: %d, COST %.2f", num_inc, temp, cost);

  //printf("\nget_cost_for_ ... _2 --> Increase cost: %.2f", cost);

  return cost;

}











void free_dg_num_inform(dg_num_inform_list dg_fact_node)
{
#ifdef __TEST__
  if (dg_fact_node==NULL)
    printf("\nErrore nella disallocazione delle strutture dg_act");
#endif


  if(dg_fact_node->prev)
    dg_fact_node->prev->next=dg_fact_node->next;

  if(dg_fact_node->next)
    dg_fact_node->next->prev=dg_fact_node->prev;


  dg_fact_node->next=NULL;
  free(dg_fact_node);

}





/* Aggiorna la lista per l'inserimento di un elemento nella stessa 
   Restituisce TRUE se i costi di raggiungibilita' vengono inseriti
   diminuendo i valori di raggiungibilita'
*/
Bool update_dg_fact_list(int fact_pos, int *level_ptr, int num_actions, int best_act, float duration, float cost, int related_fact)
{
 
  int l1, indlevel;
  dg_inform_list dg_fact_node, dg_next_samelevel=NULL, dg_prev_samelevel=NULL;

  l1=*level_ptr;

  duration=0.0;// Hvar.ri_duration_of_numeric_facts[fact_pos]; // Va riabilitato quando e' possibile calcolarla in modo preciso

 
  if(related_fact<0) /* inserisco nuova inform ragg */
  {
 /* reset dei valori di dg_fact_node */ 
    if(l1>=0)
    {
      if(vectlevel[l1]->dg_facts_array[fact_pos])
	{
	  dg_fact_node=vectlevel[l1]->dg_facts_array[fact_pos];
	  while(dg_fact_node)
	    {
	      dg_next_samelevel = dg_fact_node->next_samelevel;
	      free_dg_inform(dg_fact_node);
	      dg_fact_node=dg_next_samelevel;	      
	    }
	  vectlevel[l1]->dg_facts_array[fact_pos]=NULL;
	  dg_next_samelevel=NULL;
	}


     }
  }
  else
  {
 /* Se il fatto puo' essere reso supportato dall'azione nell'action
     subgraph (related_fact==-1) con un costo inferiore all'attuale
     non faccio niente
  */
    if(vectlevel[l1]->dg_facts_array[fact_pos])
      {
	/* Verifico che costo dell'inserimento dell'azione non sia 
	   superiore al costo del fatto che sto valutando
	*/


	dg_fact_node=vectlevel[l1]->dg_facts_array[fact_pos];
	while(dg_fact_node)
	  {
	     if(dg_fact_node->related_fact==-1)
	       {
		 if(dg_fact_node->next_samelevel)
		   printf("\nWarning some elements after related_fact=-1");

		 break;
	       }

	     dg_fact_node = dg_fact_node->next_samelevel;

	  }


	  if(dg_fact_node!=NULL && ( dg_fact_node->num_actions<num_actions  || 
	      ( dg_fact_node->num_actions==num_actions &&
		dg_fact_node->cost<=cost)))
	    return FALSE;
      }

  }



  dg_fact_node=calloc_dg_inform();   /* creazione nodo da inserire nella lista */ 


  dg_fact_node->fact_pos=fact_pos;
  dg_fact_node->level=level_ptr;
  dg_fact_node->num_actions=num_actions;
  dg_fact_node->best_act=best_act;
  dg_fact_node->duration=duration;
  dg_fact_node->cost=cost;
  dg_fact_node->totcost = cost * GpG.orig_weight_cost + duration * GpG.orig_weight_time;
  dg_fact_node->stop=FALSE;
  dg_fact_node->related_fact=related_fact;
  dg_fact_node->next_samelevel=NULL;
  dg_fact_node->prev=NULL;
  dg_fact_node->next=NULL;


  if(best_act<0 && best_act!=INITIAL_ACTION)
    {
      dg_fact_node->num_actions=MAX_COST;
      dg_fact_node->cost=MAX_COST;
      dg_fact_node->totcost = MAX_COST;
    }


  if(DEBUG5)
    {
      printf("\nUPDATE RI: fact reachability info: fact %s level %d best_action %s num_action %d duration %.2f cost %.2f", print_ft_name_string(fact_pos,temp_name), l1, print_op_name_string(dg_fact_node->best_act, temp_name), dg_fact_node->num_actions,dg_fact_node->duration, dg_fact_node->cost);
    }
  
  
  if(l1<0)
    {
      dg_next_samelevel= Hvar.init_facts_array[fact_pos];
      Hvar.init_facts_array[fact_pos]=dg_fact_node;
      dg_fact_node->stop=TRUE; 
      if(dg_next_samelevel)
	free_dg_inform(dg_next_samelevel);

      if(DEBUG4)
	print_dg_inform(dg_fact_node);
      return TRUE ;
      
    }


 
 if (GpG.relax_list_fact_cost == FALSE)
   {
     dg_prev_samelevel=NULL;
     dg_next_samelevel=vectlevel[l1]->dg_facts_array[fact_pos];
     
     /* Definisco la posizione in cui inserire dg_fact_node:
	tra dg_prev_samelevel e dg_next_samelevel
     */
     while(dg_next_samelevel)
       {
	 
	 if( dg_next_samelevel->num_actions> num_actions  || 
	     ( dg_next_samelevel->num_actions==num_actions &&
	       dg_next_samelevel->cost>=cost))
	   break;
	 
	 dg_prev_samelevel= dg_next_samelevel;
	 
	 dg_next_samelevel =  dg_next_samelevel->next_samelevel;
	 
       }

	
     if(dg_prev_samelevel==NULL) /* quindi dg_fact_node va inserito all'inizio della lista */
       {
	 dg_next_samelevel= vectlevel[l1]->dg_facts_array[fact_pos];
	 vectlevel[l1]->dg_facts_array[fact_pos]=dg_fact_node;     
	 SET_BIT(vectlevel[l1]->local_bit_vect_facts,fact_pos);
	 if(DEBUG4)
	   {
	     printf("\nNo Prev inform");
	     print_dg_inform(dg_fact_node);
	   }

      }
     else
       {
	 dg_prev_samelevel->next_samelevel=dg_fact_node;


	 if(DEBUG4)
	   {
	     printf("\nPrev inform");
	     print_dg_inform(dg_prev_samelevel);
	     printf("\nNew next");
	     print_dg_inform(dg_fact_node);
	   }

	 dg_fact_node->next_samelevel=dg_next_samelevel;
       }


     return TRUE;
   }


  /* test di mutua esclusione per sapere se la catena di nodi dg e' bloccata */ 
  if(GET_ACTION_POSITION_OF_LEVEL (l1) >=0 )
    {
      if(check_mutex_noop(fact_pos, l1) )
	{
	  if(DEBUG5)
	    {
	      printf("\nSRI: Mutex between %s at level %d and %s", print_op_name_string (GET_ACTION_POSITION_OF_LEVEL(l1), temp_name), l1, print_ft_name_string (fact_pos, temp_name));
	    }
	  dg_fact_node->stop=TRUE;
	}
    }
#ifdef __TEST_UPD__
  else
    printf("Warning: azione assente nella gestione della lista");
#endif

  /* inserimento dell'elemento dg_fact_node nella lista */
  /* dg_fact_node->next indica elementi dg in livelli successivi a level */
  /* dg_fact_node->prev indica elementi dg in livelli precedenti a level */

  dg_prev_samelevel=NULL;
  dg_next_samelevel=vectlevel[l1]->dg_facts_array[fact_pos];

	 /* Definisco la posizione in cui inserire dg_fact_node:
	    tra dg_prev_samelevel e dg_next_samelevel
	 */
  while(dg_next_samelevel)
    {
      
      if( dg_next_samelevel->num_actions> num_actions  || 
	  ( dg_next_samelevel->num_actions==num_actions &&
	    dg_next_samelevel->cost>=cost))
	break;

      dg_prev_samelevel= dg_next_samelevel;

      dg_next_samelevel =  dg_next_samelevel->next_samelevel;

    }

       
  if(vectlevel[l1]->dg_facts_array[fact_pos])
  {
    dg_fact_node->next=vectlevel[l1]->dg_facts_array[fact_pos]->next;
    dg_fact_node->prev=vectlevel[l1]->dg_facts_array[fact_pos]->prev;

    if(dg_prev_samelevel==NULL)/* quindi dg_fact_node va inserito all'inizio della lista */
      {
	dg_fact_node->prev->next=dg_fact_node;
	if(dg_fact_node->next!=NULL)
	  dg_fact_node->next->prev=dg_fact_node;
	dg_next_samelevel= vectlevel[l1]->dg_facts_array[fact_pos];
	dg_fact_node->next_samelevel=dg_next_samelevel;
	vectlevel[l1]->dg_facts_array[fact_pos]=dg_fact_node;     
	SET_BIT(vectlevel[l1]->local_bit_vect_facts,fact_pos);
      }
    else
      {
	 dg_prev_samelevel->next_samelevel=dg_fact_node;
	 dg_fact_node->next_samelevel=dg_next_samelevel;
      }
  }
  else
  {
   for(indlevel=l1-1; indlevel >=0; indlevel--)
    if(vectlevel[indlevel]->dg_facts_array && vectlevel[indlevel]->dg_facts_array[fact_pos]) /* si cerca il primo elemento della lista nei livelli precedenti a level */
      {
	dg_fact_node->next=vectlevel[indlevel]->dg_facts_array[fact_pos]->next;
	vectlevel[indlevel]->dg_facts_array[fact_pos]->next=dg_fact_node;

	dg_fact_node->prev=vectlevel[indlevel]->dg_facts_array[fact_pos];
	if(dg_fact_node->next!=NULL)
	  dg_fact_node->next->prev=dg_fact_node;
	break;
      }



  if(DEBUG5)
    printf("\nSRI: Find a previous dg_fact_node fact_pos: fact_pos %d at level: %d", fact_pos, indlevel);

  if(indlevel<0) /* Se non si trova nessun elemento nei livelli precedenti */
      {
	/* l'elemento che precede dg_fact_node e' quello legato al livello 0: informazioni di raggiungibilita' precalcolate */
	dg_fact_node->next=Hvar.init_facts_array[fact_pos]->next; 
    	
	if(Hvar.init_facts_array[fact_pos]->next!=NULL)
	  Hvar.init_facts_array[fact_pos]->next->prev=dg_fact_node;
	
	dg_fact_node->prev=Hvar.init_facts_array[fact_pos];
	Hvar.init_facts_array[fact_pos]->next=dg_fact_node;
      }
  }

  if(DEBUG4)
    print_dg_inform(dg_fact_node);

  return TRUE;
}



struct _DG_ACT_NUM * calloc_dg_num_inform()
{
  
  dg_num_inform_list dg_node=NULL;
  
  dg_node=(dg_num_inform_list) calloc (1, sizeof (_dg_act_num));
  
  return(dg_node);
}

dg_num_inform_list update_num_dg_fact_list(int fact_pos, int *level_ptr, int num_actions, int best_increase,int best_decrease, int best_assign, float duration, float cost)
{

  int l1, indlevel;
  dg_num_inform_list dg_fact_node;

  l1=*level_ptr;

  dg_fact_node=calloc_dg_num_inform();   /* creazione nodo da inserire nella lista */ 

  /* reset dei valori di dg_fact_node */ 

  if(l1>=0)
    {
      if(vectlevel[l1]->dg_num_facts_array[fact_pos])
	{
	  free_dg_num_inform(vectlevel[l1]->dg_num_facts_array[fact_pos]);
	  vectlevel[l1]->dg_num_facts_array[fact_pos]=NULL;
	}
      vectlevel[l1]->dg_num_facts_array[fact_pos]=dg_fact_node;

    }
  dg_fact_node->level=level_ptr;
  dg_fact_node->num_actions=num_actions;
  dg_fact_node->best_increase=best_increase;
  dg_fact_node->best_decrease=best_decrease;
  dg_fact_node->best_assign=best_assign;
  dg_fact_node->duration=duration;
  dg_fact_node->cost=cost;
  dg_fact_node->totcost = cost * GpG.orig_weight_cost + duration * GpG.orig_weight_time;
  dg_fact_node->stop=FALSE;
  dg_fact_node->prev=NULL;
  dg_fact_node->next=NULL;


 if(l1<0)
   {   
     dg_fact_node->stop=TRUE;
     return dg_fact_node ;
   }
 
 if (GpG.relax_list_fact_cost == FALSE)
   {
     return dg_fact_node ;
   }


  /* test di mutua esclusione per sapere se la catena di nodi dg e' bloccata */ 
 

  /* inserimento dell'elemento dg_fact_node nella lista */
  /* dg_fact_node->next indica elementi dg in livelli successivi a level */
  /* dg_fact_node->prev indica elementi dg in livelli precedenti a level */
  for(indlevel=l1-1; indlevel >=0; indlevel--)
    if(vectlevel[indlevel]->dg_num_facts_array[fact_pos]) /* si cerca il primo elemento della lista nei livelli precedenti a level */
      {
	dg_fact_node->next=vectlevel[indlevel]->dg_num_facts_array[fact_pos]->next;
	vectlevel[indlevel]->dg_num_facts_array[fact_pos]->next=dg_fact_node;

	dg_fact_node->prev=vectlevel[indlevel]->dg_num_facts_array[fact_pos];
	if(dg_fact_node->next!=NULL)
	  dg_fact_node->next->prev=dg_fact_node;
	break;
      }

  if(DEBUG5)
    printf("\nSRI: Find a previous dg_fact_node fact_pos: fact_pos %d at level: %d", fact_pos, indlevel);

  if(indlevel<0) /* Se non si trova nessun elemento nei livelli precedenti */
      {
	/* l'elemento che precede dg_fact_node e' quello legato al livello 0: informazioni di raggiungibilita' precalcolate */
	dg_fact_node->next=Hvar.init_num_facts_array[fact_pos]->next; 
    	
	if(Hvar.init_num_facts_array[fact_pos]->next!=NULL)
	  Hvar.init_num_facts_array[fact_pos]->next->prev=dg_fact_node;
	
	dg_fact_node->prev=Hvar.init_num_facts_array[fact_pos];
	Hvar.init_num_facts_array[fact_pos]->next=dg_fact_node;
      }

  return(dg_fact_node);
}





/* Aggiorna la lista per l'eliminazione di un elemento nella stessa */
void delete_dg_fact_list(int fact_pos, int *level)
{

  dg_inform_list dg_fact_node, dg_next_samelevel;
  int l1;

  l1=*level;

  if(DEBUG5)
    printf("\nSRI: Delete dg_fact_node fact_pos: %d level: %d",fact_pos, l1 );

  dg_fact_node=vectlevel[l1]->dg_facts_array[fact_pos]; /* nodo da cancellare */

  if(dg_fact_node==NULL)
    return;

  /* togliamo l'elemento dg_fact_node dalla lista */
  if(dg_fact_node->prev)
    dg_fact_node->prev->next=dg_fact_node->next;

  if(dg_fact_node->next)
    dg_fact_node->next->prev=dg_fact_node->prev;

  /*  dg_fact_node->next=NULL;
      dg_fact_node->prev=NULL; */
  while(dg_fact_node)
    {
      dg_fact_node->cost=0.0;
      dg_fact_node->totcost=0.0;
      dg_fact_node->duration=0.0;
      dg_fact_node->level=NULL;
      dg_fact_node->num_actions=-1;
      dg_fact_node->best_act=-1;
      dg_fact_node->stop=FALSE;

      dg_next_samelevel=dg_fact_node->next_samelevel;
      free_dg_inform(dg_fact_node); /* inseriamo l'elemento dg_fact_node nella lista dei nodi cancellati */ 
      dg_fact_node=dg_next_samelevel;
    }
}





/* Aggiorna la lista per l'eliminazione di un elemento nella stessa */
void delete_dg_element(dg_inform_list dg_node, int fact_pos, int *level)
{


  if(DEBUG5)
    printf("\nSRI: Delete dg_fact_node fact_pos: %d level: %d",fact_pos,*level );

  if(dg_node==NULL)
    return;

  if(dg_node->next_samelevel)
    {
      if(dg_node->prev)
	dg_node->prev->next=dg_node->next_samelevel;

      if(dg_node->next)
	dg_node->next->prev=dg_node->next_samelevel;


      RESET_BIT(vectlevel[*level]->local_bit_vect_facts,fact_pos);

    }
  else
    {
      /* togliamo l'elemento dg_fact_node dalla lista */
      if(dg_node->prev)
	dg_node->prev->next=dg_node->next;
      
      if(dg_node->next)
	dg_node->next->prev=dg_node->prev;

  if(DEBUG5)
    printf("\nSRI: Delete dg_fact_node fact_pos: %d level: %d",fact_pos, *level );
    }

  dg_node->cost=0.0;
  dg_node->totcost=0.0;
  dg_node->duration=0.0;
  dg_node->level=NULL;
  dg_node->num_actions=-1;
  dg_node->best_act=-1;
  dg_node->stop=FALSE;

  free_dg_inform(dg_node); /* inseriamo l'elemento dg_fact_node nella lista dei nodi cancellati */ 
 
}


void verify_cri_until_level(int level)
{
  int l1;


  if(GpG.cri_intermediate_levels!=STANDARD_INTERMEDIATE_REACHAB_INFORM)
    return;


  for (l1 = 0; l1 < level ; l1++)
    if(GET_ACTION_POSITION_OF_LEVEL(l1)>=0 && vectlevel[l1]->is_cri_computed==FALSE )
      {

#ifdef __TEST_REACH__
	cri_heuristic_for_action_numeric_reach( GET_ACTION_POSITION_OF_LEVEL(l1) , l1);
#else
	cri_heuristic_for_action( GET_ACTION_POSITION_OF_LEVEL(l1) , l1);
#endif
      set_computed_dg_costs (l1);	// memorizza nel livello i costi calcolati

      }

  reset_bitarray (Hvar.bit_vect_facts, gnum_ft_block);

}


/* restituisce la stima del fatto a un dato livello */
int get_dg_fact_cost (int fact_pos, int level, dg_inform_list * loc_dg_cost)
{
  register int l1=0;
  int stop;

  dg_inform_list index_dg, temp_dg_cost;
  dg_inform_list  best_dg_cost=NULL;

  if(level > GpG.curr_plan_length)
    level = GpG.curr_plan_length;


  if(GpG.cri_intermediate_levels==NO_INTERMEDIATE_REACHAB_INFORM)
    {
     *loc_dg_cost =best_dg_cost= Hvar.init_facts_array[fact_pos];

      if(DEBUG5)
	{
	  printf("\nGRI2: get fact reachability info: fact %s level %d  num_action %d duration %.2f cost %.2f    best_action %d - ", print_ft_name_string(fact_pos,temp_name), l1 , best_dg_cost->num_actions,best_dg_cost->duration, best_dg_cost->cost, best_dg_cost->best_act);
	  print_op_name(best_dg_cost->best_act);

	}

      return level;

    }
  
  if(GpG.cri_intermediate_levels==DYNAMIC_INTERMEDIATE_REACHAB_INFORM)
    return  get_intermediate_reachab_inform(fact_pos, level,  loc_dg_cost);
 
  /* trova la prima struttura dg_act nei livelli inferiori a level */
  for (l1 = get_prev(level); l1 >= 0; l1 = get_prev(l1))
   if (vectlevel[l1]->dg_facts_array  && vectlevel[l1]->dg_facts_array[fact_pos])
     //if (vectlevel[l1]->is_cri_computed==TRUE  && vectlevel[l1]->dg_facts_array[fact_pos])
      {
	best_dg_cost = vectlevel[l1]->dg_facts_array[fact_pos];
	if (GpG.relax_list_fact_cost == FALSE ||  best_dg_cost->stop==TRUE)
	  {
	    /* valuto se best_dg_cost e' valido: se related_fact==-1 o related_fact e' attualmente supportato
	     */
	    stop=FALSE;
	    while(stop==FALSE && best_dg_cost!=NULL )
	      {
		if(best_dg_cost->related_fact==-1 ||(best_dg_cost->related_fact>=0 && GET_BIT(vectlevel[l1]->fact_vect,best_dg_cost->related_fact)!=0)) 
		  {
		    *loc_dg_cost = best_dg_cost;
		    stop=TRUE;
		  }
		else
		  {
      		    index_dg= best_dg_cost;
		    best_dg_cost= best_dg_cost->next_samelevel;


		    if(GpG.relax_list_fact_cost == FALSE && best_dg_cost==NULL)
		      break;  
		    else
		    if(best_dg_cost==NULL)
		      {
			if(  index_dg->next )
			  {
			    index_dg->next->prev=index_dg->prev;
			  }

			if( index_dg->prev )
			  {
			    best_dg_cost=index_dg->prev;
			    l1=*best_dg_cost->level;
			    index_dg->prev->next=index_dg->next;
			  }
		      }
		    else
		      {
			if( index_dg->prev )
			  best_dg_cost->prev=index_dg->prev;
		    
			if( index_dg->next )
			  best_dg_cost->next=index_dg->next;
		      }
		    free_dg_inform(index_dg);
		  }

	      }
	    if(stop==FALSE && best_dg_cost==NULL)
	      continue;


	    if(DEBUG5)
	      {
	        printf("\nGRI1: get fact reachability info: fact");
		print_ft_name(fact_pos);
		printf("level %d best_action ", l1);
		print_op_name(best_dg_cost->best_act);
		printf(" num_action %d duration %.2f cost %.2f", best_dg_cost->num_actions, best_dg_cost->duration, best_dg_cost->cost);

	      }


	    return l1;
	  }
	else
	  break;
      }

  if(l1<0)
    {
      *loc_dg_cost =best_dg_cost= Hvar.init_facts_array[fact_pos];

      if(DEBUG5)
	{
	  printf("\nGRI2: get fact reachability info: fact %s level %d  num_action %d duration %.2f cost %.2f    best_action %d - ", print_ft_name_string(fact_pos,temp_name), l1 , best_dg_cost->num_actions,best_dg_cost->duration, best_dg_cost->cost, best_dg_cost->best_act);
	  print_op_name(best_dg_cost->best_act);

	}

      return 0;
    }



  /* Verifica di best_dg_cost */

	    stop=FALSE;
	    while( stop==FALSE && best_dg_cost)
	      {
		if(best_dg_cost->related_fact==-1 ||(best_dg_cost->related_fact>=0 && GET_BIT(vectlevel[l1]->fact_vect,best_dg_cost->related_fact)!=0)) 
		  {
		    stop=TRUE;
		  }

		else
		  {
		    temp_dg_cost=best_dg_cost;
      		    best_dg_cost= best_dg_cost->next_samelevel;

		    if(best_dg_cost==NULL)
		      {
			best_dg_cost=temp_dg_cost->prev;

			if( temp_dg_cost->prev )
			  temp_dg_cost->prev->next=temp_dg_cost->next;

			if( temp_dg_cost->next )
			  temp_dg_cost->next->prev=temp_dg_cost->prev;

		      }
		    else
		      {
			if( temp_dg_cost->prev )
			  {
			    best_dg_cost->prev=temp_dg_cost->prev;
			    temp_dg_cost->prev->next=best_dg_cost;
			  }
			if( temp_dg_cost->next )
			  {
			    best_dg_cost->next=temp_dg_cost->next;
			    temp_dg_cost->next->prev=best_dg_cost;
			  }
		      }
		    free_dg_inform(temp_dg_cost);
		  }

	      }


  /* controlliamo che non ci siamo delle stime migliori nei livelli precedenti scorrendo la lista di dg_act */
  for(index_dg=best_dg_cost->prev; index_dg  ; index_dg=index_dg->prev) 
    {
     
      /* Verifichiamo che l'azione non sia gia' stata esaminata nei livelli precedenti
       */

      if( best_dg_cost->best_act==index_dg->best_act )
	{ 
	  if(index_dg->stop==TRUE) /* se la catena e' bloccata restituiamo la migliore stima finora pervenuta */
	    break;
	  else
	    continue;

	}

/* se index_dg migliora  la stima corrente  aggiorniamo best_dg_cost=index_dg 
 */ 
       if(best_dg_cost->num_actions > index_dg->num_actions ||  (best_dg_cost->num_actions == index_dg->num_actions && best_dg_cost->totcost > index_dg->totcost  )  ) 
	 {

	     /* valuto se index_dg e' valido: se related_fact==-1 o related_fact e' attualmente supportato
	     */
	    stop=FALSE;
	    while( stop==FALSE && index_dg)
	      {
		if(index_dg->related_fact==-1 ||(index_dg->related_fact>=0 && GET_BIT(vectlevel[l1]->fact_vect,index_dg->related_fact)!=0)) 
		  {
		    stop=TRUE;
		  }

		else
		  {
		    temp_dg_cost=index_dg;
      		    index_dg = index_dg->next_samelevel;

		    if(index_dg==NULL)
		      {
			index_dg=temp_dg_cost->prev;

			if( temp_dg_cost->prev )
			  temp_dg_cost->prev->next=temp_dg_cost->next;

			if( temp_dg_cost->next )
			  temp_dg_cost->next->prev=temp_dg_cost->prev;

		      }
		    else
		      {
			if( temp_dg_cost->prev )
			  {
			    index_dg->prev=temp_dg_cost->prev;
			    temp_dg_cost->prev->next=index_dg;
			  }
			if( temp_dg_cost->next )
			  {
			    index_dg->next=temp_dg_cost->next;
			    temp_dg_cost->next->prev=index_dg;
			  }
		      }
		    free_dg_inform(temp_dg_cost);
		  }

	      }


	    /* se index_dg migliora  la stima corrente  aggiorniamo best_dg_cost=index_dg 
	     */ 
	    if(best_dg_cost->num_actions > index_dg->num_actions ||  (best_dg_cost->num_actions == index_dg->num_actions && best_dg_cost->totcost > index_dg->totcost  )  ) 
	      {

		if (DEBUG5)
		  {
		    printf("\n GRI3: Find better RI: fact %s level %d best_action %s num_action %d duration %.2f cost %.2f", print_ft_name_string(fact_pos,temp_name), *best_dg_cost->level, print_op_name_string(best_dg_cost->best_act, temp_name), best_dg_cost->num_actions,best_dg_cost->duration, best_dg_cost->cost);
		  }

		best_dg_cost=index_dg;
	      }
	 }

       if(index_dg->stop==TRUE) /* se la catena e' bloccata restituiamo la migliore stima finora pervenuta */
	 break;


       if(*index_dg->level < 0) /* da sostituire con index_dg_cost->next!=NULL */
	 break;
    }


  *loc_dg_cost = best_dg_cost;
  if(DEBUG5)
    printf("\nGRI4: get fact reachability info: fact %s level %d best_action %s num_action %d duration %.2f cost %.2f", print_ft_name_string(fact_pos,temp_name), l1, print_op_name_string(best_dg_cost->best_act, temp_name), best_dg_cost->num_actions,best_dg_cost->duration, best_dg_cost->cost);

  if(*best_dg_cost->level>=0)
    return (*best_dg_cost->level);
  else return(0);

}



int num_action_for_unsup_num_precondition(int fact_pos, int level)
{

  int k=1;

  /******
  
   il valore a cui si vuole arrivare e' 
	 A=vectlevel[level]->numeric->values[gcomp_var[fact_pos].second_op]

   il valore di partenza e' 
         B=vectlevel[level]->numeric->values[gcomp_var[fact_pos].first_op]

   il max increase di B
   Hvar.ri_max_increase_for_compvar[gcomp_var[fact_pos].first_op]

   max decrease di B
      Hvar.ri_max_decrease_for_compvar[gcomp_var[fact_pos].first_op]

   il minimo assegnamento di B
      Hvar.ri_min_assign_for_compvar[gcomp_var[fact_pos].first_op]


   Per verificare che un A sia effettivamente una COSTANTE
       gcomp_var[gcomp_var[fact_pos].second_op].operator==FIX_NUMBER

   Per verificare che un B sia effettivamente un FLUENT
       gcomp_var[gcomp_var[fact_pos].first_op].operator==VARIABLE_OP

   *****/


   switch (gcomp_var[fact_pos].operator)
    {
      
       case LESS_THAN_OP: /* B<A */
	 if( Hvar.ri_min_assign_for_compvar[gcomp_var[fact_pos].first_op]!=MIN_NEG_VALUE && (Hvar.ri_min_assign_for_compvar[gcomp_var[fact_pos].first_op]<vectlevel[level]->numeric->values[gcomp_var[fact_pos].second_op]))
	   return 1;      


	 if(Hvar.ri_max_decrease_for_compvar[gcomp_var[fact_pos].first_op]<=0)
	   return  MAX_COST;

	 k= (int) abs(ceil((vectlevel[level]->numeric->values[gcomp_var[fact_pos].second_op]+ MAX_APPROX-vectlevel[level]->numeric->values[gcomp_var[fact_pos].first_op])/Hvar.ri_max_decrease_for_compvar[gcomp_var[fact_pos].first_op]));
	 if(k==0)
	   k++;  
	 return k;

	 break;
	 


      case LESS_THAN_OR_EQUAL_OP:

        if( Hvar.ri_min_assign_for_compvar[gcomp_var[fact_pos].first_op]!=MIN_NEG_VALUE && (Hvar.ri_min_assign_for_compvar[gcomp_var[fact_pos].first_op]<=vectlevel[level]->numeric->values[gcomp_var[fact_pos].second_op]))
	   return 1;

	if(Hvar.ri_max_decrease_for_compvar[gcomp_var[fact_pos].first_op]<=0)
	  return  MAX_COST;




	k= (int) abs(ceil((vectlevel[level]->numeric->values[gcomp_var[fact_pos].second_op]-vectlevel[level]->numeric->values[gcomp_var[fact_pos].first_op])/Hvar.ri_max_decrease_for_compvar[gcomp_var[fact_pos].first_op]));
	if(k==0)
	  k++;  
	return k;

	break;



      case GREATER_THAN_OP:

	if( Hvar.ri_max_assign_for_compvar[gcomp_var[fact_pos].first_op]!=MIN_NEG_VALUE && (Hvar.ri_max_assign_for_compvar[gcomp_var[fact_pos].first_op]>vectlevel[level]->numeric->values[gcomp_var[fact_pos].second_op]))
	  return 1;

	if(Hvar.ri_max_increase_for_compvar[gcomp_var[fact_pos].first_op] <=0)
	  return  MAX_COST;


	k= (int) abs(ceil((vectlevel[level]->numeric->values[gcomp_var[fact_pos].second_op]+MAX_APPROX-vectlevel[level]->numeric->values[gcomp_var[fact_pos].first_op])/Hvar.ri_max_increase_for_compvar[gcomp_var[fact_pos].first_op]));
	if(k==0)
	  k++;  
	
	return k;

	break;


      case GREATER_OR_EQUAL_OP:

	if( Hvar.ri_max_assign_for_compvar[gcomp_var[fact_pos].first_op]!=MIN_NEG_VALUE && (Hvar.ri_max_assign_for_compvar[gcomp_var[fact_pos].first_op]>=vectlevel[level]->numeric->values[gcomp_var[fact_pos].second_op]))
	  return 1;
	

	if(Hvar.ri_max_increase_for_compvar[gcomp_var[fact_pos].first_op] <=0)
	  return  MAX_COST;


	k= (int) abs(ceil((vectlevel[level]->numeric->values[gcomp_var[fact_pos].second_op]-vectlevel[level]->numeric->values[gcomp_var[fact_pos].first_op])/Hvar.ri_max_increase_for_compvar[gcomp_var[fact_pos].first_op]));
	if(k==0)
	  k++;  
	return k;
	break;
	
       default:
      
       MSG_ERROR("Warning: Errore nel calcolo dei valori di raggiungibilità, la variabile non è una precondizione");
      break;
    } 

   return 1;
}



int get_dg_num_fact_cost (register int fact_pos, register int level, dg_num_inform_list * loc_dg_num_cost)
{
  register int l1;
  dg_num_inform_list  best_dg_cost=NULL;
  register dg_num_inform_list index_dg;


  /* ATTENZIONE da disabilitare se si calcolano le informazioni 
     di raggiungibilita' numeriche nei livelli intermedi __TEST_REACH__ */
  level=-1;

  /* trova la prima struttura dg_act nei livelli inferiori a level */
  for (l1 = get_prev(level); l1 >= 0; l1 = get_prev(l1))
    if ( vectlevel[l1]->dg_num_facts_array && vectlevel[l1]->dg_num_facts_array[fact_pos])
      {
	best_dg_cost = vectlevel[l1]->dg_num_facts_array[fact_pos];
	if (GpG.relax_list_fact_cost == FALSE)
	  {
	    *loc_dg_num_cost = best_dg_cost;

	    return l1;
	  }
	else
	  break;
      }

  if(l1<0)
    {
      *loc_dg_num_cost =best_dg_cost= Hvar.init_num_facts_array[fact_pos];

      return 0;
    }


  /* controlliamo che non ci siamo delle stime migliori nei livelli precedenti scorrendo la lista di dg_act */
  for(index_dg=best_dg_cost; index_dg  ; index_dg=index_dg->prev) 
    {
      if(index_dg->stop==TRUE) /* se la catena e' bloccata restituiamo la migliore stima finora pervenuta */
	break;
      /* Verifichiamo che l'azione non sia gia' stata esaminata nei livelli precedenti
       */
     
              
/* se index_dg migliora  la stima corrente  aggiorniamo best_dg_cost=index_dg 
 */ 
       if(best_dg_cost->num_actions > index_dg->num_actions ||  (best_dg_cost->num_actions == index_dg->num_actions && best_dg_cost->totcost > index_dg->totcost  )  ) 
	 {

	   best_dg_cost=index_dg;

	 }
       if(*index_dg->level <= -1) /* da sostituire con index_dg_cost->next!=NULL */
	 break;
    }


  *loc_dg_num_cost = best_dg_cost;
    if(*best_dg_cost->level>=0)
    return (*best_dg_cost->level);
  else return(0);


 

}






int
get_dg_fact_cost2 (register int fact_pos, register int level,
		  dg_inform_list * loc_dg_cost)
{
  // static int call = 0;
  register int l1;
  // call++;
  //  assert(gis_inertial[1]==0);

  for (l1 = level; l1 >= 0; l1--)
    if (vectlevel[l1]->dg_facts_array[fact_pos])
      {
	*loc_dg_cost = vectlevel[l1]->dg_facts_array[fact_pos];
	return l1;
      }


  *loc_dg_cost = Hvar.init_facts_array[fact_pos];
  //      loc_n_cost->weight=Hvar.dg_facts_array[fact_pos]->totcost;
  //      loc_n_cost->num_actions=Hvar.dg_facts_array[fact_pos]->num_actions;
  //      loc_n_cost->act_cost=Hvar.dg_facts_array[fact_pos]->cost;
  //      loc_n_cost->act_time=Hvar.dg_facts_array[fact_pos]->duration;
  return 0;
}



float
compute_constr_fact (int constraint, int fact_pos, int level, int initialize, int orig_level, float *cost, float *end_time)
{

  // Controllo che le azioni non siano in conflitto con le inconsistenze presenti ai livelli successivi, viceversa incremento num_constr

  int num_constr = 0, i, lev1, action, el, me, k,j,temp;
  dg_inform_list loc_dg_cost = NULL;
  float start_time = 0.0;
  int ord, ind_level;

  if (initialize)
    {
      reset_bitarray (Hvar.threated_bit_vect_facts, gnum_ft_block);
  
      reset_bitarray (Hvar.bit_vect_actions, gnum_ef_block);
      reset_bitarray (Hvar.bit_vect_facts,gnum_ft_block);
      *cost=0.0;
    }
  

#ifdef __TEST__

  if (unsup_fact[constraint]->fact == fact_pos)
    printf ("\n ------------------------------------------");

  printf ("\n Compute constr of ");
  print_ft_name (fact_pos);
#endif


  lev1 = get_dg_fact_cost (fact_pos, level+1, &loc_dg_cost);



  action = loc_dg_cost->best_act;


  if (action < 0)
    {

#ifdef __TEST__
      printf ("\n INIT ACTION");
#endif
      return 0;			// azione precedentem. inserita
    }


#ifdef __TEST__
  printf ("\n Action:: %s",print_op_name_string (action, temp_name) );
  printf (" cost %.2f num_act %d duration %.2f for fact %d : ",
	  loc_dg_cost->cost, loc_dg_cost->num_actions, loc_dg_cost->duration,
	  fact_pos);
  print_ft_name (fact_pos);

#endif

  if (GET_BIT (Hvar.bit_vect_actions, action))
    {

#ifdef __TEST__
      printf ("\n Insert prec action");
#endif
      return 0;			// azione precedentem. inserita
    }



  SET_BIT (Hvar.bit_vect_actions, action);

  if(DEBUG4)
    printf("\n Comp CF insert action %d -- %s " ,action, print_op_name_string(action,temp_name)); 


  if(GpG.verify_inc_choice)
    *cost+=1.0;
  else
    *cost += get_action_cost (action, level, NULL);


  // calcolo le mutue esclusioni dell'azione con i fatti non supportati dei livelli succ
  for (i = 0; i < GpG.num_false_fa; i++)
    {
      if (constraint == unsup_fact[i]->fact)
	continue;		// non considero le eventuali inconsistenze con fact_pos

      // if (orig_level != *unsup_fact[i]->level)
      if (orig_level > *unsup_fact[i]->level)
	continue;		// l'azione non influenza la raggiungibilita' dell'inconsistenza

      //      if(GET_BIT(Hvar.threated_bit_vect_facts,unsup_fact[i]->fact))
      //	continue; //gia minacciato


      if (gef_conn[action].ft_exclusive_vect[GUID_BLOCK (unsup_fact[i]->fact)]
	  & (GUID_MASK (unsup_fact[i]->fact)))
	{
	  num_constr++;
	  //	  SET_BIT(Hvar.threated_bit_vect_facts,unsup_fact[i]->fact);
	  if(DEBUG4)
	    {
	      printf ("\n -------> Constr : fact %d __ ",unsup_fact[i]->fact);
	      print_ft_name (unsup_fact[i]->fact);
	      printf( "  action %s ", print_op_name_string(action, temp_name));
	    }
	}

    }

  for (i = 0; i < gef_conn[action].num_PC; i++)
    {
      el = gef_conn[action].PC[i];
      if (el < 0)
	continue;		// LAZZA

      if(start_time < vectlevel[level]->fact[el].time_f)
	start_time = vectlevel[level]->fact[el].time_f; 

      if (fact_is_supported (el, lev1)|| GET_BIT (Hvar.bit_vect_facts, el) )
	{
#ifdef __TEST__
	  printf ("\n Supported fact %s lev %d",
		  print_ft_name_string (el, temp_name), level);
#endif
	  continue;
	}

      num_constr += compute_constr_fact (constraint, el, lev1, 0, orig_level, cost, end_time);

      if (start_time < *end_time)
	start_time = *end_time;
    }

  if (gef_conn[action].sf != NULL)
    {
      // Precondizioni OVERALL
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{
	  el = gef_conn[action].sf->PC_overall[i];
	  if (el < 0)
	    continue;		// LAZZA

	  if (is_fact_in_additive_effects_start
	      (action, gef_conn[action].sf->PC_overall[i]))
	    continue;

	  if(start_time < vectlevel[level]->fact[el].time_f)
	    start_time = vectlevel[level]->fact[el].time_f; 

	  if (fact_is_supported (el, orig_level) || GET_BIT (Hvar.bit_vect_facts, el))
	    {
#ifdef __TEST__
	      printf ("\n Supported fact %s lev %d",
		      print_ft_name_string (el, temp_name), level);
#endif
	      continue;
	    }

	  num_constr += compute_constr_fact (constraint, el, lev1, 0, orig_level, cost, end_time);

	  if (start_time < *end_time)
	    start_time = *end_time;
 
	}

      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	{
	  el = gef_conn[action].sf->PC_end[i];
	  if (el < 0)
	    continue;		// LAZZA
	  if (is_fact_in_additive_effects_start (action, gef_conn[action].sf->PC_end[i]))
	    continue;

	  
	  if(start_time < vectlevel[level]->fact[el].time_f - get_action_time(action,level))
	    start_time = vectlevel[level]->fact[el].time_f - get_action_time(action,level); 


	  if (fact_is_supported (el, lev1)|| GET_BIT (Hvar.bit_vect_facts, el))
	    {
#ifdef __TEST__
	      printf ("\n Supported fact %s lev %d",
		      print_ft_name_string (el, temp_name), level);
#endif
	      continue;
	    }

	  num_constr += compute_constr_fact (constraint, el, lev1, 0, orig_level, cost, end_time);

	  if (start_time < *end_time)
	    start_time = *end_time;
 
	}
    }



  for (ind_level = orig_level - 1; ind_level >= 0; ind_level--)
    {    
      if (check_mutex_action (action, ind_level) >= 0 )
	{
	  /* 
	     Il vincolo di ordinamento tra azioni mutex e' sempre di
	     tipo piu' restrittivo
	  */
	  if (GpG.constraint_type <= 1) 
	    {
	      if (start_time < GET_ACTION_OF_LEVEL(ind_level)->time_f)
		start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f;
	    }
	  else 
	    /* 
	       Vincoli di ordinamento avanzati
	    */
	    { 
	      /* 
		 Stabilisce il tipo di vincolo tra l'azione act e
		 l'azione "GET_ACTION__OF_LEVEL(ind_level)" noto che
		 "GET_ACTION__OF_LEVEL(ind_level)" si trova a un livello
		 inferiore rispetto a "act"  
	      */
	      
	      ord = Econstraint_type(GET_ACTION_POSITION_OF_LEVEL(ind_level), 
				     ind_level, action, -1);
	      
	      if (ord == EA_SB) // l'azione  "act" deve iniziare dopo la fine dell'azione "GET_ACTION__OF_LEVEL(ind_level)" 
		{
		  if (start_time < GET_ACTION_OF_LEVEL(ind_level)->time_f)
		    start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f;
		}
	      else
		{
		  if (ord == EA_EB) // l'azione "act"  deve finire dopo la fine di "GET_ACTION__OF_LEVEL(ind_level)" 
		    {
		      if (start_time < GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (action, orig_level) )
			start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (action, orig_level);
		    }
		  else
		    if (ord == SA_SB) // l'azione "act" deve iniziare dopo l'inizio di "GET_ACTION__OF_LEVEL(ind_level)" 
		      {
			if (start_time < GET_ACTION_OF_LEVEL (ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level) )
			  start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level);
		      }
		    else
		      {
			if (ord == SA_EB) // l'azione "act" deve finire dopo l'inizio di "GET_ACTION__OF_LEVEL(ind_level)" 
			  {
			    if (start_time < GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level)  - get_action_time (action, orig_level) )
			      start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level) - get_action_time (action, orig_level);
			  }
			else
			  {
			    if (ord == EA_EB__SA_SB) // l'azione "act" e' sovrapposta ad "GET_ACTION__OF_LEVEL(ind_level)" 
			      {
				if( get_action_time (action, orig_level) < get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level))
				  {
				    // l'azione "act"  deve finire dopo la fine di "GET_ACTION__OF_LEVEL(ind_level)" 
				    if (start_time < GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (action, orig_level) )
				      start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (action, orig_level);
				  }
				else // l'azione "act" deve iniziare dopo l'inizio di "GET_ACTION__OF_LEVEL(ind_level)" 
				  {
				    if (start_time < GET_ACTION_OF_LEVEL (ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level) )
				      start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level);
				  }
			      }
			  }
		      }
		}
	    }
	}
    }
  
  
  *end_time = start_time + get_action_time(action,orig_level);



  for (i = 0; i < gef_conn[action].num_A; i++)
    {
      el = gef_conn[action].A[i];
      if (el < 0)
	{
	  continue;	
	}

      SET_BIT (Hvar.bit_vect_facts, el);
    }
  
  if (gef_conn[action].sf)
    for (i = 0; i < gef_conn[action].sf->num_A_start; i++)
      {
	el = gef_conn[action].sf->A_start[i];
	
	if (el < 0)
	  {
	  continue;	
	  }
	
	SET_BIT (Hvar.bit_vect_facts, el);
      }

  if ( GpG.inc_choice_type == MIN_LEVEL_MIN_CONSTR_INC)
    { 
      for ( me=0, i=j = 0; i < gnum_ft_block; i++,j+=32)
	
	{
	  temp =CONVERT_ACTION_TO_VERTEX (action)->ft_exclusive_vect[i] & vectlevel[orig_level]->fact_vect[i];
	  k = 32;
	  while (temp)
	    {
	      k--;
	      if (temp & FIRST_1)
		{
		  if(GET_BIT(Hvar.threated_bit_vect_facts,(j + k))!=0)
		    {
		      me++;
		      SET_BIT(Hvar.threated_bit_vect_facts,(j + k));
		    }
		}
	      temp <<= 1;
	    }
	}


      // for (  me = 0, i = 0; i < gnum_ft_block; i++)
      //	 me+=  count_bit1 (CONVERT_ACTION_TO_VERTEX (action)->ft_exclusive_vect[i] & vectlevel[orig_level]->fact_vect[i]);

      num_constr +=me;
      if(me>0 && DEBUG4)
	printf("\n  ME %d  act %d -- %s level %d ", me, action, print_op_name_string(action, temp_name), orig_level );
      
    }
  //#ifdef __TEST__
  if(DEBUG2 && initialize)
    {
      printf("\n CCF Fact %d - %s level %d ",  fact_pos, print_ft_name_string( fact_pos, temp_name), level);
      printf ("  Total constr %d, cost %f ", num_constr, *cost);
    }

  //#endif

  return num_constr;

}

// if(n_cost1>n_cost2)









void ls_insert_fact_inlist (int pos)
{
  /**
     This function does not consider numerical fact
   **/
  if (pos < 0)
    return;

  if (GET_BIT (Hvar.bit_vect_facts, pos))
    return;
  
  if (Hvar.num_facts_define_cost >= MAX_LENGTH_H) {
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_MAX_LENGTH_H );
#else 
    printf( WAR_MAX_LENGTH_H );
#endif    
    exit (0);
  }

 
  Hvar.list_ft_define_cost[Hvar.num_facts_define_cost++] = pos;

  SET_BIT (Hvar.bit_vect_facts, pos);

#ifdef __TEST__

  printf ("\n Insert fact %d in list: ", pos);
  print_ft_name (pos);

#endif


}


int
insert_action_inlist (int pos, int fact)
{


#ifdef __TEST__

  printf ("\n:::::::::::::::::: Insert ACTION %d in list:", pos);
  print_op_name (pos);
  printf ("\n Hvar.num_actions_define_cost %d", Hvar.num_actions_define_cost);
  printf ("\n Hvar.weight_facts_define_cost %.2f  \n\n",
	  Hvar.weight_facts_define_cost);
#endif


  if (GET_BIT (Hvar.bit_vect_actions, pos) != 0)
    {
#ifdef __TEST__

      printf ("\n ACTION %d already in list:", pos);
      print_op_name (pos);
      printf ("\n Hvar.num_actions_define_cost %d ",
	      Hvar.num_actions_define_cost);
      printf ("\n Hvar.weight_facts_define_cost %.2f ",
	      Hvar.weight_facts_define_cost);
#endif
      if( GpG.avoid_best_action_cycles )
	{
	  
	  if( GpG.avoid_best_action_cycles==2 &&  Hvar.best_act_for_fact_array[pos]==fact)
	    return -1; // Individuato ciclo e mi fermo
	  
	  if( Hvar.best_act_insertion_array[pos] > MAX_NUM_SAME_BEST_ACT) 
	    return 0;
	  else
	    Hvar.best_act_insertion_array[pos]++;
	  
	}
      else
	return 0;

    }
  else
    {
      if( GpG.avoid_best_action_cycles )
	{
	  Hvar.best_act_insertion_array[pos]=1;
	  Hvar.best_act_for_fact_array[pos]=fact;
	}
      Hvar.list_ef_define_cost[Hvar.num_actions_define_cost] = pos;
    }



  if (Hvar.num_actions_define_cost >= MAX_LENGTH_H) {
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_MAX_LENGTH_H );
#else 
    printf( WAR_MAX_LENGTH_H );
#endif    
    exit (0);
  }
  


  Hvar.num_actions_define_cost++;
  
  SET_BIT (Hvar.bit_vect_actions, pos);
  Hvar.cost_actions_define_cost += get_action_cost (pos, *Hvar.constr->level, NULL);


#ifdef __TEST__

  printf ("\n::::::::::::::::::2 Insert ACTION %d in list:", pos);
  print_op_name (pos);
  printf ("\n Hvar.num_actions_define_cost %d", Hvar.num_actions_define_cost);
  printf ("\n Hvar.weight_facts_define_cost %.2f  \n\n",
	  Hvar.weight_facts_define_cost);
#endif

  return 1;

}





float
max_neighborhood_evaluation (int act_pos, int level, node_cost_list n_cost, float max_time_for_timed_fact)
{
  register int i;
  int j, diff, el, num_actions;
  register EfConn *act;
  float total, prec_par, excl_par, add_effect_par, temp;
  dg_inform_list loc_dg_cost = NULL;
  float time_Timed_Prec=-1.0;
  int num_Timed_Prec=0;

#ifdef __TEST_REACH__
    dg_num_inform_list loc_dg_num_cost;
  int cost_unsup_num_fact = 1;
#endif


  //  assert(gis_inertial[1]==0);

  /* Define the alpha, beta, gamma coefficents of F() to  
     remove the action act from the action subgraph */

  prec_par = GpG.prec_par;
  excl_par = GpG.excl_par;
  add_effect_par = GpG.add_effect_par;

  total = 0.0;
  n_cost->weight = 0.0;
  n_cost->num_actions = 0;
  n_cost->act_cost = 0.0;
  n_cost->act_time = 0.0;

  act = &gef_conn[act_pos];

  if (DEBUG5)
    printf ("\n >>> DG_INSERTION  Act: %d -- %s, level %d ",act_pos,
	    print_op_name_string (act_pos, temp_name), level);

#ifdef __TEST__
  printf ("\nFIC ");
#endif


  /* Cost of  unsatisfied Preconditions */
  if (prec_par)
    {
	  // **** Precondizioni AT START
	  for (i = 0, temp = 0.0; i < gef_conn[act_pos].num_PC; i++)
	    {
	      el = gef_conn[act_pos].PC[i];

	      //LAZZA
	      if (el < 0)
		{
		  if (!is_num_prec_satisfied  (el,level))
		    {
		      //#ifdef __TEST_REACH__
		      {
			//get_dg_num_fact_cost (-el, level - 1, &loc_dg_num_cost); 
			num_actions=num_action_for_unsup_num_precondition(-el, level);
			
			if(num_actions<=0)
			  printf("\n Warning num_actions = %d ", num_actions);


			if (num_actions== MAX_COST) // loc_dg_num_cost==NULL)
			  {
			    n_cost->weight = MAX_COST;
			    n_cost->num_actions = MAX_COST;
			    n_cost->act_time = MAX_COST;
			    return ( MAX_COST);
			  }		
			else
			  {
			    if (n_cost->weight < (float) num_actions) //(float) loc_dg_num_cost->num_actions)     
			      n_cost->weight = (float) num_actions; // loc_dg_num_cost->num_actions;	//->totcost;
			    if (n_cost->num_actions < num_actions) //  loc_dg_num_cost->num_actions)
			      n_cost->num_actions = num_actions; // loc_dg_num_cost->num_actions;
			  }
		      }
		      // Da ricalcolare perche' consideriamo raggiungibilita' iniziale
		    
			
		    }



		  if (GpG.penalize_inconsistence_in_relaxed_plan)
		    { 
		      
		      if (Hvar.constr->constraint_type ==C_T_UNSUP_NUM_FACT
			  && Hvar.constr->fact == -el)
			{
#ifdef __TEST__
			  printf
			    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
			  
#endif
			  
			  n_cost->weight= MAX_COST;
			  n_cost->act_cost= MAX_COST;
			  n_cost->act_time= MAX_COST;
			  
			  
			  if(DEBUG4)
			    {
			    printf("\nSTOP FACT to MAXCOST %d, level %d, name ",  el, level);
			    print_cvar_tree(-el,level);
			    
			    printf("\n\n");
			    
			    }
			  
			  
			  return ( MAX_COST);
			}
		    }
		  

		  
		  continue;
		  
		}


	      if (fact_is_supported (el, level))
		{
		  //#ifdef __TEST__
		  if(DEBUG5)
		    printf ("\n Supported fact %s lev %d",
			  print_ft_name_string (el, temp_name), level);
		  //#endif

		  if( n_cost->act_time < CONVERT_FACT_TO_NODE(el, level)->time_f)
		  n_cost->act_time = CONVERT_FACT_TO_NODE(el, level)->time_f;
		  continue;
		}



	      if (GpG.penalize_inconsistence_in_relaxed_plan)
		{ 
		  if (Hvar.constr->constraint_type == C_T_UNSUP_FACT
		      && el== Hvar.constr->fact)
		    {
#ifdef __TEST__
		      printf
			("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
		      
#endif
		      n_cost->weight= MAX_COST;
		      n_cost->act_cost= MAX_COST;
		      n_cost->act_time= MAX_COST;
		      
		      if(DEBUG4)
			    {
			      printf("\nDG INSERTION STOP FACT to MAXCOST %d, level %d, name ",  el, level);
			      if(el>=0)
				print_ft_name( el );
			      
			      printf("\n\n");
			      
			    }      
		      return ( MAX_COST);
		    }
		}

	      // Da migliorare
	      get_dg_fact_cost (el, level, &loc_dg_cost);

	      if (loc_dg_cost==NULL)
		{
		  n_cost->weight = MAX_COST;
		  n_cost->num_actions = MAX_COST;
		  n_cost->act_time = MAX_COST;
		  return ( MAX_COST);
		}		
		else
		{
		  if (n_cost->weight < (float) loc_dg_cost->num_actions)	// ->totcost)
		    n_cost->weight = (float) loc_dg_cost->num_actions;	//->totcost;
		  if (n_cost->num_actions < loc_dg_cost->num_actions)
		    n_cost->num_actions = loc_dg_cost->num_actions;
		  if (n_cost->act_cost < loc_dg_cost->cost)
		    n_cost->act_cost = loc_dg_cost->cost;
		  if (n_cost->act_time < loc_dg_cost->duration)
		    n_cost->act_time = loc_dg_cost->duration;
		}


#ifdef __TEST__
	      printf
		("\n Unsupported fact %s lev %d weight %.2f cost  %.2f time  %.2f num_actions %d ",
		 print_ft_name_string (el, temp_name), level,
		 (float) loc_dg_cost->num_actions, loc_dg_cost->cost,
		 loc_dg_cost->duration, loc_dg_cost->num_actions);
#endif
	    }


	  // **** Precondizioni OVERALL
	  if (gef_conn[act_pos].sf != NULL)
	    {
	      for (i = 0, temp = 0.0; i < gef_conn[act_pos].sf->num_PC_overall; i++)
		{
		  el = gef_conn[act_pos].sf->PC_overall[i];


		  if (el < 0)
		    {
		      if (!is_num_prec_satisfied (el,level))
			{
			  //#ifdef __TEST_REACH__
			  {
			    //			    get_dg_num_fact_cost (-el, level - 1, &loc_dg_num_cost);
			    
			    num_actions=num_action_for_unsup_num_precondition(-el, level);
			if(num_actions<=0)
			  printf("\n Warning num_actions = %d ", num_actions);


			    if (num_actions== MAX_COST) //loc_dg_num_cost==NULL)
			      {
				n_cost->weight = MAX_COST;
				n_cost->num_actions = MAX_COST;
				n_cost->act_time = MAX_COST;
				return ( MAX_COST);
			      }		
			    else
				  {
				    if (n_cost->weight < (float) num_actions) // (float) loc_dg_num_cost->num_actions)	// ->totcost)
				      n_cost->weight =  (float)num_actions; //  (float) loc_dg_num_cost->num_actions;	//->totcost;
				    if (n_cost->num_actions < num_actions) //  loc_dg_num_cost->num_actions)
				      n_cost->num_actions = num_actions; // loc_dg_num_cost->num_actions;
				    //   if (n_cost->act_cost < loc_dg_num_cost->cost)
				    //   n_cost->act_cost = loc_dg_num_cost->cost;
				    //  if (n_cost->act_time < loc_dg_num_cost->duration)
				    //    n_cost->act_time = loc_dg_num_cost->duration;
				  }
			  }    
			  // Da ricalcolare perche' consideriamo raggiungibilita' iniziale





			}
		  
		      
			  
		      if (GpG.penalize_inconsistence_in_relaxed_plan)
			{ 
			  
			  if (Hvar.constr->constraint_type ==C_T_UNSUP_NUM_FACT
			      && Hvar.constr->fact == -el)
			    {
#ifdef __TEST__
			      printf
				    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
			      
#endif
			      
			      n_cost->weight= MAX_COST;
			      n_cost->act_cost= MAX_COST;
			      n_cost->act_time= MAX_COST;
			      
			      
			      if(DEBUG4)
				{
				  printf("\nSTOP FACT to MAXCOST %d, level %d, name ",  el, level);
				  print_cvar_tree(-el,level);
				  
				  printf("\n\n");
				  
				}
			      
			      
			      return ( MAX_COST);
			    }
			}
		      

		      continue;
		      
		    }


		  if (is_fact_in_additive_effects_start
		      (act_pos, gef_conn[act_pos].sf->PC_overall[i]))
		    continue;

		  if (fact_is_supported (el, level))
		    {
#ifdef __TEST__
		      printf ("\n Supported fact %s lev %d",
			      print_ft_name_string (el, temp_name), level);
#endif
		      if (n_cost->act_time <
			  CONVERT_FACT_TO_NODE (el, level)->time_f)
			n_cost->act_time =
			  CONVERT_FACT_TO_NODE (el, level)->time_f;

		      continue;
		    }



		  if (GpG.penalize_inconsistence_in_relaxed_plan)
		    { 

		      if (Hvar.constr->constraint_type == C_T_UNSUP_FACT
			  && el== Hvar.constr->fact)
			{
#ifdef __TEST__
			  printf
			    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
      
#endif
			  n_cost->weight= MAX_COST;
			  n_cost->act_cost= MAX_COST;
			  n_cost->act_time= MAX_COST;
			
			  if(DEBUG4)
			    {
			      printf("\nDG INSERTION STOP FACT to MAXCOST %d, level %d, name ",  el, level);
			      if(el>=0)
				print_ft_name(el);

			      printf("\n\n");

			    }      
			  return ( MAX_COST);
			}

		    }

		  // Da migliorare
		  get_dg_fact_cost (el, level, &loc_dg_cost);

		  if (loc_dg_cost==NULL)
		    {
		      n_cost->weight = MAX_COST;
		      n_cost->num_actions = MAX_COST;
		      n_cost->act_time = MAX_COST;	 
		      return ( MAX_COST);
		    }		
		  else
		    {
		      if (n_cost->weight < (float) loc_dg_cost->num_actions)	// ->totcost)
			n_cost->weight = (float) loc_dg_cost->num_actions;	//->totcost;
		      if (n_cost->num_actions < loc_dg_cost->num_actions)
			n_cost->num_actions = loc_dg_cost->num_actions;
		      if (n_cost->act_cost < loc_dg_cost->cost)
			n_cost->act_cost = loc_dg_cost->cost;
		      if (n_cost->act_time < loc_dg_cost->duration)
			n_cost->act_time = loc_dg_cost->duration;
		    }



#ifdef __TEST__
		  printf
		    ("\n Unsupported fact %s lev %d weight %.2f cost  %.2f time  %.2f num_actions %d ",
		     print_ft_name_string (el, temp_name), level,
		     (float) loc_dg_cost->num_actions, loc_dg_cost->cost,
		     loc_dg_cost->duration, loc_dg_cost->num_actions);
#endif
		}



	      for (i = 0, temp = 0.0; i < gef_conn[act_pos].sf->num_PC_end; i++)
		{
		  el = gef_conn[act_pos].sf->PC_end[i];


		  if (el < 0)
		    {
		      if (!is_num_prec_satisfied (el,level))
			{
			  //#ifdef __TEST_REACH__
			  {

			    //			  get_dg_num_fact_cost (-el, level - 1, &loc_dg_num_cost);
			    num_actions=num_action_for_unsup_num_precondition(-el, level);
			if(num_actions<=0)
			  printf("\n Warning num_actions = %d ", num_actions);


			  if (num_actions== MAX_COST) // loc_dg_num_cost==NULL)
			    {
			      n_cost->weight = MAX_COST;
			      n_cost->num_actions = MAX_COST;
			      n_cost->act_time = MAX_COST;
			      return ( MAX_COST);
			    }		
			  else
				{
				  if (n_cost->weight < (float) num_actions) // (float) loc_dg_num_cost->num_actions)	// ->totcost)
				    n_cost->weight = (float) num_actions; // (float) loc_dg_num_cost->num_actions;	//->totcost;
				  if (n_cost->num_actions < num_actions) // loc_dg_num_cost->num_actions)
				 n_cost->num_actions = num_actions; // loc_dg_num_cost->num_actions;
				//  if (n_cost->act_cost < loc_dg_num_cost->cost)
				//    n_cost->act_cost = loc_dg_num_cost->cost;
				//  if (n_cost->act_time < loc_dg_num_cost->duration)
				//    n_cost->act_time = loc_dg_num_cost->duration;
				}		       		      
			  
			  }
			  // Da ricalcolare perche' consideriamo raggiungibilita' iniziale
			  
						  
			}
		      
		      if (GpG.penalize_inconsistence_in_relaxed_plan)
			{ 
			  
			  if (Hvar.constr->constraint_type ==C_T_UNSUP_NUM_FACT
			      && Hvar.constr->fact == -el)
			    {
#ifdef __TEST__
			      printf
				    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
			      
#endif
			      
			      n_cost->weight= MAX_COST;
			      n_cost->act_cost= MAX_COST;
			      n_cost->act_time= MAX_COST;
			      
			      
			      if(DEBUG4)
				{
				  printf("\nSTOP FACT to MAXCOST %d, level %d, name ",  el, level);
				  print_cvar_tree(-el,level);
				  
				  printf("\n\n");
				  
				}
			      
			      
			      return ( MAX_COST);
			    }
			}
		      
		      continue;
		      
		    }
		  //ENDLAZZA


		  if (is_fact_in_additive_effects (act_pos, gef_conn[act_pos].sf->PC_end[i]))
		    continue;
		  
		  if (fact_is_supported (el, level))
		    {
#ifdef __TEST__
		      printf ("\n Supported fact %s lev %d",
			      print_ft_name_string (el, temp_name), level);
#endif
		      if( n_cost->act_time < CONVERT_FACT_TO_NODE(el, level)->time_f -get_action_time(act_pos,0))
			n_cost->act_time = CONVERT_FACT_TO_NODE(el, level)->time_f -get_action_time(act_pos,0);

		      continue;
		    }
		  


		  if (GpG.penalize_inconsistence_in_relaxed_plan)
		    { 

		      if (Hvar.constr->constraint_type == C_T_UNSUP_FACT
			  && el== Hvar.constr->fact)
			{
#ifdef __TEST__
			  printf
			    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
      
#endif
			  n_cost->weight= MAX_COST;
			  n_cost->act_cost= MAX_COST;
			  n_cost->act_time= MAX_COST;
			
			  if(DEBUG4)
			    {
			      printf("\nDG INSERTION STOP FACT to MAXCOST %d, level %d, name ",  el, level);
			      if(el>=0)
				print_ft_name( el );

			      printf("\n\n");

			    }      
			  return ( MAX_COST);
			}

		    }


		  // Da migliorare
		  get_dg_fact_cost (el, level, &loc_dg_cost);

		  if (loc_dg_cost==NULL)
		    {
		      n_cost->weight = MAX_COST;
		      n_cost->num_actions = MAX_COST;
		      n_cost->act_time = MAX_COST; 
		      return ( MAX_COST);
		    }		
		  else
		    {
		      if (n_cost->weight < (float) loc_dg_cost->num_actions)	// ->totcost)
			n_cost->weight = (float) loc_dg_cost->num_actions;	//->totcost;
		      if (n_cost->num_actions < loc_dg_cost->num_actions)
			n_cost->num_actions = loc_dg_cost->num_actions;
		      if (n_cost->act_cost < loc_dg_cost->cost)
			n_cost->act_cost = loc_dg_cost->cost;
		      if (n_cost->act_time < loc_dg_cost->duration)
			n_cost->act_time = loc_dg_cost->duration;
		    }


#ifdef __TEST__
		  printf
		    ("\n Unsupported fact %s lev %d weight %.2f cost  %.2f time  %.2f num_actions %d ",
		     print_ft_name_string (el, temp_name), level,
		     (float) loc_dg_cost->num_actions, loc_dg_cost->cost,
		     loc_dg_cost->duration, loc_dg_cost->num_actions);
#endif
		}

	    }



      total = prec_par * n_cost->weight;


      if (DEBUG5)
	printf ("\n Num. P: %.2f", n_cost->weight);



    }

  if (excl_par)
    {

      
      temp = (float) count_mutex_noop_at_start (act_pos, level);


      total += excl_par * temp;

      if (DEBUG5)
	printf ("\n  M.E.: %.2f   ", temp);

    }




  if (FALSE && GpG.Twalkplan && GpG.tabu_length >0)
    {				
      /* T_walkgraph: increase the cost function of act if it is in
	 the tabu list 
      */
      diff = GpG.count_num_try - gef_conn[act->position].step;
      
      if (diff < GpG.tabu_length)
	total += GpG.delta * (GpG.tabu_length - diff);
    }

	  
  if (GpG.timed_facts_present) {
    if (GET_BIT(GpG.has_timed_preconds, act_pos))
      {
      
     	      /*
		-time_Timed_Prec restituisce l'istante in cui  l'azione puo' iniziare considerando le precondiz temporali
		- num_Timed_Prec indica il numero di precondizione temporali che non si e' riusciti ad assegnare
	      */
	time_Timed_Prec = search_for_pc_intervals(n_cost->act_time,  act_pos, 0, &num_Timed_Prec);
	
	if (num_Timed_Prec > 0)
	  {
	    total +=num_Timed_Prec;// *  GpG.SearchCost_UnsupTimedFact;
	    n_cost->act_cost +=10.0;// MAX_COST; CAZZO
	    n_cost->act_time +=10.0;//  MAX_COST;
	    
	    if(DEBUG3)
	      printf("\nTF-BA: Increase search cost for %d unsup timed prec of best action candidate  %s", num_Timed_Prec, print_op_name_string(act_pos, temp_name));
	  }
	
	if( time_Timed_Prec>0)
	  {
	    if(n_cost->act_time < time_Timed_Prec)
	      {
		n_cost->act_time= time_Timed_Prec;
		if(DEBUG3)
		  printf("\nTF-BA: Update start time %.2f of %s", n_cost->act_time, print_op_name_string(act_pos, temp_name));
	      }	      
	  }
  
      }
  }





  total++;			//l'azione stessa
  n_cost->act_cost += get_action_cost (act_pos, level, NULL);
  n_cost->act_time += get_action_time (act_pos, 0);
  n_cost->weight = total;
  n_cost->num_actions++;	// l'azione stessa


  if(max_time_for_timed_fact<MAXFLOAT && GpG.timed_facts_present)
    {

      for (i=0; i < gnum_timed_facts; i++)
	for (j=0; j < gnum_tmd_interval[i]; j++)
	  {
	    if (n_cost->act_time + max_time_for_timed_fact > gtimed_fct_vect[i][j].slack) 
	      {
		total ++;
		if (DEBUG3) 
		  {
		    printf("\nTF-BA: Increase cost for BA %s: time(BA) %.2f, time of previous actions in Rplan %.2f, slack %.2f", print_op_name_string(act_pos,temp_name),n_cost->act_time,max_time_for_timed_fact,gtimed_fct_vect[i][j].slack);
		    printf("for timed fact %s", print_ft_name_string(gtimed_fct_vect[i][j].position,temp_name));
		}
	      }
	  }
    }


  if (DEBUG4)
    {
      print_op_name(act_pos);
      printf (" tot %f [cost: %.2f  time: %.2f] level %d \n", total, n_cost->act_cost, n_cost->act_time,level );

    }
  if (DEBUG5)
    {
      printf("\n END eval action ");
      print_op_name(act_pos);
      printf (" -> tot %f\n", total);
    }

  return (total);

}




void update_fact_in_action_cost_list(int act, int level, int fact, float cost) {

  register int i, j;

  for (i = 0; i < last_best_act_cost[act].saved_prec; i++) {
    if (last_best_act_cost[act].max_best_act_cost[i] < cost)
      break;
  }

  if (i < NUM_SAVED_PREC_COST) {
    for (j = NUM_SAVED_PREC_COST - 1; j > i; j--) {
      last_best_act_cost[act].max_best_act_cost[j] = last_best_act_cost[act].max_best_act_cost[j - 1];
      last_best_act_cost[act].fact_best_act_cost[j] = last_best_act_cost[act].fact_best_act_cost[j - 1];
    }
    
    last_best_act_cost[act].max_best_act_cost[i] = cost;
    last_best_act_cost[act].fact_best_act_cost[i] = fact;

    if (last_best_act_cost[act].saved_prec < NUM_SAVED_PREC_COST)
      last_best_act_cost[act].saved_prec++;
  }

}





void update_mutex_in_action_cost_list(int act, int mutex) {

  last_best_act_cost[act].level_mutex = mutex;

}


void update_act_time_cost_in_list(int act, float act_time) {

  last_best_act_cost[act].max_time = act_time;

}



inline float evaluate_action_cost_from_list( register int act_pos, int level, node_cost_list n_cost,
				      float max_time_for_timed_fact, node_cost_list max_n_cost) {
  
  int penalization = 1;
  register int i;
    
  if (gef_conn[act_pos].has_numeric_precs)
    return best_action_evaluation(act_pos, level, n_cost, max_time_for_timed_fact, max_n_cost);

  if ((last_best_act_cost[act_pos].step != GpG.count_num_try)
      || (level != last_best_act_cost[act_pos].level)) 
    {
      last_best_act_cost[act_pos].saved_prec = 0;
      last_best_act_cost[act_pos].step = GpG.count_num_try;
      last_best_act_cost[act_pos].level = level;

      return best_action_evaluation(act_pos, level, n_cost, max_time_for_timed_fact, max_n_cost);
    }
  
  for (i = 0; i < last_best_act_cost[act_pos].saved_prec; i++) {
    
    if (!GET_BIT(Hvar.bit_vect_facts, last_best_act_cost[act_pos].fact_best_act_cost[i]))
      break;    

  }
  
  if (i == last_best_act_cost[act_pos].saved_prec)
    return best_action_evaluation(act_pos, level, n_cost, max_time_for_timed_fact, max_n_cost);
  
  if (i < last_best_act_cost[act_pos].saved_prec) {

    n_cost->weight = last_best_act_cost[act_pos].max_best_act_cost[i] + penalization;
    n_cost->num_actions = (int)last_best_act_cost[act_pos].max_best_act_cost[i];
    n_cost->act_cost = last_best_act_cost[act_pos].max_best_act_cost[i] + get_action_cost(act_pos, level, NULL);
    n_cost->act_time = last_best_act_cost[act_pos].max_time;
      
    n_cost->weight += last_best_act_cost[act_pos].level_mutex;

    return  n_cost->weight;

  }
      
  return (0.0);
  
} 



int compute_fast_fact_cost(int level, int act_level, register int best_action)
{
  register int i, el;
  int  prev_level, num_actions;
  dg_inform_list loc_dg_cost = NULL;

  if( best_action<0)
    return 0;

  if (GET_BIT (Hvar.ri_bit_vect_actions, best_action) != 0)
    {
#ifdef __TEST__
      printf ("\n ACTION %d already in list:",  best_action);
      print_op_name (best_action);
      printf ("\n Hvar.ri_num_actions_define_cost %d ", Hvar.ri_num_actions_define_cost);
#endif
      return 1;
    }
  Hvar.ri_num_actions_define_cost++;

  SET_BIT (Hvar.ri_bit_vect_actions,  best_action);

  Hvar.ri_cost_actions_define_cost +=  get_action_cost ( best_action, level, NULL);

     
  if(DEBUG5)
    {
      printf ("\n  Relaxed Eval INSERTION  ACTION %d:",  best_action);
      print_op_name (best_action);
      printf ("\n Hvar.ri_num_actions_define_cost %d ", Hvar.ri_num_actions_define_cost);
    }


  for (i = 0; i < gef_conn[ best_action].num_PC && Hvar.ri_num_actions_define_cost< MAX_INT_COST; i++)
    {
      
      el=gef_conn[best_action].PC[i];
   
      if (el < 0)
	{
	  if( !is_num_prec_satisfied  (el,level))
	    { 
	      num_actions=num_action_for_unsup_num_precondition(-el, level);
			
	      if(num_actions<=0)
		printf("\n Warning num_actions = %d ", num_actions);
	      else
		if (num_actions== MAX_INT_COST) // loc_dg_num_cost==NULL)
		      {
			Hvar.ri_num_actions_define_cost= MAX_INT_COST;
			
			return 2;
		      }		
		    else
		      {

			Hvar.ri_num_actions_define_cost+= num_actions; 
		      }

	    }
	  continue;
	}


      if(GET_BIT ( Hvar.ri_supp_bit_vect_facts, el))
	{
	  //#ifdef __TEST__
	  if(DEBUG5)
	    printf ("\n  fact %s lev %d in   Hvar.ri_supp_bit_vect_facts == 1",
		    print_ft_name_string (el, temp_name), level);
	  //#endif
	  continue;
	}
   
      if (fact_is_supported (el, level))
	{

	  if(DEBUG5)
	    printf ("\n Supported fact %s lev %d",
		    print_ft_name_string (el, temp_name), level);

	  SET_BIT ( Hvar.ri_supp_bit_vect_facts, el); // LA PROSSIMA VOLTA VIENE INDIVIDUATO PIU' RAPIDAMENTE CON  Hvar.ri_supp_bit_vect_facts

	  continue;
	}


      prev_level=act_level;
      if(TRUE ||  act_level<0)
	loc_dg_cost=Hvar.init_facts_array[el];
      else
	{
	  if (vectlevel[act_level]->dg_facts_array  && vectlevel[act_level]->dg_facts_array[el])
	    loc_dg_cost= vectlevel[act_level]->dg_facts_array[el];
	  else 
	    prev_level=get_dg_fact_cost (el,level, &loc_dg_cost);
		  
	}
      if( loc_dg_cost)
	compute_fast_fact_cost( level,  prev_level, loc_dg_cost->best_act);


    }


  if(  Hvar.ri_num_actions_define_cost>= MAX_INT_COST)
    return 0;


  if (gef_conn[best_action].sf != NULL)
    {


      // effetti additivi AT_START
      for (i = 0; i < gef_conn[ best_action].sf->num_A_start && Hvar.ri_num_actions_define_cost< MAX_INT_COST; i++)
	if (gef_conn[ best_action].sf->A_start[i] >= 0)
	  {	
	    /* Non prendo in considerazione effetti numerici
	     */	  
	    /* Rendo il fatto attualmente supportato
	     */
	    SET_BIT(  Hvar.ri_supp_bit_vect_facts, gef_conn[ best_action].sf->A_start[i]); 
	    
	  }


  // **** Precondizioni OVERALL
     for (i = 0; i < gef_conn[ best_action].sf->num_PC_overall; i++)
	{
	  el = gef_conn[ best_action].sf->PC_overall[i];


	  if (el < 0)
	    { 
	      if( !is_num_prec_satisfied  (el,level))
		{ 
		  num_actions=num_action_for_unsup_num_precondition(-el, level);
		  
		  if(num_actions<=0)
		    printf("\n Warning num_actions = %d ", num_actions);
		  else
		    if (num_actions== MAX_INT_COST) // loc_dg_num_cost==NULL)
		      {
			Hvar.ri_num_actions_define_cost= MAX_INT_COST;
			
			return 2;
		      }		
		    else
		      {
			
			Hvar.ri_num_actions_define_cost+= num_actions; 
		      }
		  
		}

	      continue;
	    }

	  if(GET_BIT ( Hvar.ri_supp_bit_vect_facts, el))
	    {
	      //#ifdef __TEST__
	      if(DEBUG5)
		printf ("\n  fact %s lev %d in  Hvar.ri_supp_bit_vect_facts == 1",
			print_ft_name_string (el, temp_name), level);
	      //#endif
	      continue;
	    }

	  if (fact_is_supported (el, level))
	    {

	      if(DEBUG5)
		printf ("\n Supported fact %s lev %d",
			print_ft_name_string (el, temp_name), level);

	      SET_BIT ( Hvar.ri_supp_bit_vect_facts, el); // LA PROSSIMA VOLTA VIENE INDIVIDUATO PIU' RAPIDAMENTE CON  Hvar.ri_supp_bit_vect_facts

	      continue;
	    }



	  prev_level=act_level;
	  if(act_level<0)
	    loc_dg_cost=Hvar.init_facts_array[el];
	  else
	    {
	      if (vectlevel[act_level]->dg_facts_array  && vectlevel[act_level]->dg_facts_array[el])
		loc_dg_cost= vectlevel[act_level]->dg_facts_array[el];
	      else 
		prev_level=get_dg_fact_cost (el,level, &loc_dg_cost);
		  
	    }
	      
	  if( loc_dg_cost)
	    compute_fast_fact_cost( level,  prev_level, loc_dg_cost->best_act);


	}

      for (i = 0; i < gef_conn[ best_action].sf->num_PC_end && Hvar.ri_num_actions_define_cost< MAX_INT_COST; i++)
	{

	  el =gef_conn[ best_action].sf->PC_end[i];


	  if (el < 0)
	    {
	
	      if( !is_num_prec_satisfied  (el,level))
		{ 
		  num_actions=num_action_for_unsup_num_precondition(-el, level);
		  
		  if(num_actions<=0)
		    printf("\n Warning num_actions = %d ", num_actions);
		  else
		    if (num_actions== MAX_INT_COST) // loc_dg_num_cost==NULL)
		      {
			Hvar.ri_num_actions_define_cost= MAX_INT_COST;
			
			return 2;
		      }		
		    else
		      {
			
			Hvar.ri_num_actions_define_cost+= num_actions; 
		      }
		}
	      continue;
	    }


	  /**
	     Se il fatto appartiene agli effetti at_start e' gia' 
	     supportato dall'azione stessa, quindi non viene preso 
	     in considerazione
	     *
	     if the fact is an at start effect is already supported
	     by the action "pos" so it doesn't need to be considered
	  **/ 
	  if (is_fact_in_additive_effects_start( best_action, el ))
	    continue;

		 
	  if(GET_BIT (Hvar.ri_supp_bit_vect_facts, el))
	    {
	      //#ifdef __TEST__
	      if(DEBUG5)
		printf ("\n  fact %s lev %d in  Hvar.ri_supp_bit_vect_facts== 1",print_ft_name_string (el, temp_name), level);
	      //#endif
	      continue;
	    }
 

  
	  if (fact_is_supported (el, level))
	    {

	      if(DEBUG5)
		printf ("\n Supported fact %s lev %d",
			print_ft_name_string (el, temp_name), level);

	      SET_BIT ( Hvar.ri_supp_bit_vect_facts, el); // LA PROSSIMA VOLTA VIENE INDIVIDUATO PIU' RAPIDAMENTE CON  Hvar.ri_supp_bit_vect_facts

	      continue;
	    }


	  prev_level=act_level;
	  if(act_level<0)
	    loc_dg_cost=Hvar.init_facts_array[el];
	  else
	    {
	      if (vectlevel[act_level]->dg_facts_array  && vectlevel[act_level]->dg_facts_array[el])
		loc_dg_cost= vectlevel[act_level]->dg_facts_array[el];
	      else 
		prev_level=get_dg_fact_cost (el,level, &loc_dg_cost);
		  
	    }
	      
	  if( loc_dg_cost)
	    compute_fast_fact_cost( level,  prev_level, loc_dg_cost->best_act);

	}

    }

  if(  Hvar.ri_num_actions_define_cost>= MAX_INT_COST)
    return 0;

  /* Effetti additivi at end
   */
  for (i = 0; i < gef_conn[ best_action].num_A; i++)
    /* Non prendo in considerazione effetti numerici
     */
    if (gef_conn[ best_action].A[i] >= 0)
      {
	/* Rendo il fatto attualmente supportato
	 */

	  SET_BIT( Hvar.ri_supp_bit_vect_facts, gef_conn[ best_action].A[i]);

      }

  return 1;

}


float
relaxed_neighborhood_evaluation (int act_pos, int level,  node_cost_list n_cost, float max_time_for_timed_fact)
{
  register int i, temp1;
  int j, k, diff, el, num_actions, act_level;
  register EfConn *act;
  float total, prec_par, excl_par, add_effect_par, temp;
  dg_inform_list loc_dg_cost = NULL;
  float time_Timed_Prec=-1.0;
  int num_Timed_Prec=0;


  Hvar.ri_num_actions_define_cost = 0;
  Hvar.ri_num_actions_inserted = 0;
  Hvar.ri_num_facts_define_cost = 0;
  Hvar.ri_cost_actions_define_cost=0.0;
  Hvar.ri_time_actions_define_cost=0.0;

  reset_bitarray (Hvar.ri_bit_vect_actions, gnum_ef_block);
  reset_bitarray (Hvar.ri_supp_bit_vect_facts, gnum_ft_block);



  /* Define the alpha, beta, gamma coefficents of F() to  
     remove the action act from the action subgraph */

  prec_par = GpG.prec_par;
  excl_par = GpG.excl_par;
  add_effect_par = GpG.add_effect_par;

  total = 0.0;
  n_cost->weight = 0.0;
  n_cost->num_actions = 0;
  n_cost->act_cost = 0.0;
  n_cost->act_time = 0.0;

  act = &gef_conn[act_pos];


  //L'azione stessa

  n_cost->weight++;
  n_cost->act_cost += get_action_cost (act_pos, level, NULL);
  //   n_cost->act_time += get_action_time (act_pos, 0);



  if (DEBUG5)
    printf ("\n >>> RELAXED DG_INSERTION  Act: %s, level %d ",
	    print_op_name_string (act_pos, temp_name), level);

#ifdef __TEST__
  printf ("\nFIC ");
#endif


  /* Cost of  unsatisfied Preconditions */
  if (prec_par)
    {

      // **** Precondizioni AT START
      for (i = 0, temp = 0.0; i < gef_conn[act_pos].num_PC; i++)
	{
	  el = gef_conn[act_pos].PC[i];

	  //LAZZA
	  if (el < 0)
	    {
	      if (!is_num_prec_satisfied  (el,level))
		{
		  //#ifdef __TEST_REACH__

		  //get_dg_num_fact_cost (-el, level - 1, &loc_dg_num_cost); 
		  num_actions=num_action_for_unsup_num_precondition(-el, level);
			
		  if(num_actions<=0)
		    printf("\n Warning num_actions = %d ", num_actions);
		  else
		    if (num_actions== MAX_INT_COST) // loc_dg_num_cost==NULL)
		      {
			n_cost->weight = MAX_COST;
			n_cost->num_actions = MAX_INT_COST;
			n_cost->act_time = MAX_COST;
			return ( MAX_INT_COST);
		      }		
		    else
		      {

			n_cost->weight += (float) num_actions; 

			n_cost->num_actions += num_actions; 
		      }

		      
		}
		

	      if (GpG.penalize_inconsistence_in_relaxed_plan)
		{ 
		      
		  if (Hvar.constr->constraint_type ==C_T_UNSUP_NUM_FACT
		      && Hvar.constr->fact == -el)
		    {
#ifdef __TEST__
		      printf
			("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
			  
#endif
			  
		      n_cost->weight= MAX_COST;
		      n_cost->act_cost= MAX_INT_COST;
		      n_cost->act_time= MAX_COST;
			  
			  
		      if(DEBUG4)
			{
			  printf("\nSTOP FACT to MAXCOST %d, level %d, name ",  el, level);
			  print_cvar_tree(-el,level);
			    
			  printf("\n\n");
			    
			}
			  
			  
		      return ( MAX_INT_COST);
		    }
		}
		  
  
	      continue;
		  
	    }

	  if (fact_is_supported (el, level))
	    {

	      if(DEBUG5)
		printf ("\n Supported fact %s lev %d",
			print_ft_name_string (el, temp_name), level);


	      if( n_cost->act_time < CONVERT_FACT_TO_NODE(el, level)->time_f)
		n_cost->act_time = CONVERT_FACT_TO_NODE(el, level)->time_f;

	      continue;
	    }


	  if(GET_BIT (Hvar.ri_supp_bit_vect_facts, el))
	    {
	      //#ifdef __TEST__
	      if(DEBUG5)
		printf ("\n  fact %s lev %d in  Hvar.bit_vect_facts == 1",
			print_ft_name_string (el, temp_name), level);
	      //#endif
	      continue;
	    }


	  if (GpG.penalize_inconsistence_in_relaxed_plan)
	    { 
	      if (Hvar.constr->constraint_type == C_T_UNSUP_FACT
		  && el== Hvar.constr->fact)
		{
#ifdef __TEST__
		  printf
		    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
		      
#endif
		  n_cost->weight= MAX_COST;
		  n_cost->act_cost= MAX_INT_COST;
		  n_cost->act_time= MAX_COST;
		      
		  if(DEBUG4)
		    {
		      printf("\nDG INSERTION STOP FACT to MAXCOST %d, level %d, name ",  el, level);
		      if(el>=0)
			print_ft_name( el );
			      
		      printf("\n\n");
			      
		    }      
		  return ( MAX_INT_COST);
		}
	    }

	   
	  // Da migliorare
	  act_level=get_dg_fact_cost (el, level, &loc_dg_cost);

	  if (loc_dg_cost==NULL)
	    {
	      n_cost->weight = MAX_COST;
	      n_cost->num_actions = MAX_INT_COST;
	      n_cost->act_time = MAX_COST;
	      return ( MAX_INT_COST);
	    }		
	  else
	    {
	      compute_fast_fact_cost( level,  act_level, loc_dg_cost->best_act);
		  
	    }

#ifdef __TEST__
	  printf
	    ("\n Unsupported fact %s lev %d weight %.2f cost  %.2f time  %.2f num_actions %d ",
	     print_ft_name_string (el, temp_name), level,
	     (float)  Hvar.ri_num_actions_define_cost  , Hvar.ri_cost_actions_define_cos,
	     0.0, Hvar.ri_num_actions_define_cost);
#endif
	}


      // effetti additivi AT_START
      if (gef_conn[ act_pos ].sf)
	for (i = 0; i < gef_conn[ act_pos ].sf->num_A_start; i++)
	  /* Non prendo in considerazione effetti numerici
	   */
	  if (gef_conn[ act_pos ].sf->A_start[i] >= 0)
	    {

		/* Rendo il fatto attualmente supportato
		 */
		SET_BIT( Hvar.ri_supp_bit_vect_facts, gef_conn[ act_pos ].sf->A_start[i]); 

	    }
    

      // **** Precondizioni OVERALL
      if (gef_conn[act_pos].sf != NULL)
	{
	  for (i = 0, temp = 0.0; i < gef_conn[act_pos].sf->num_PC_overall; i++)
	    {
	      el = gef_conn[act_pos].sf->PC_overall[i];

	      if (el < 0)
		{
		  if (!is_num_prec_satisfied (el,level))
		    {
		      //#ifdef __TEST_REACH__
		      //			    get_dg_num_fact_cost (-el, level - 1, &loc_dg_num_cost);
			    
		      num_actions=num_action_for_unsup_num_precondition(-el, level);
		      if(num_actions<=0)
			printf("\n Warning num_actions = %d ", num_actions);
		      else
			if (num_actions== MAX_INT_COST) //loc_dg_num_cost==NULL)
			  {
			    n_cost->weight = MAX_COST;
			    n_cost->num_actions = MAX_INT_COST;
			    n_cost->act_time = MAX_COST;
			    return ( MAX_COST);
			  }		
			else
			  {

			    n_cost->weight +=  (float)num_actions;
				
			    n_cost->num_actions += num_actions; 
			  }
			   
		      		      
		    }



		      
			  
		  if (GpG.penalize_inconsistence_in_relaxed_plan)
		    { 
			  
		      if (Hvar.constr->constraint_type ==C_T_UNSUP_NUM_FACT
			  && Hvar.constr->fact == -el)
			{
#ifdef __TEST__
			  printf
			    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
			      
#endif
			      
			  n_cost->weight= MAX_COST;
			  n_cost->act_cost= MAX_COST;
			  n_cost->act_time= MAX_COST;
			      
			      
			  if(DEBUG4)
			    {
			      printf("\nSTOP FACT to MAXCOST %d, level %d, name ",  el, level);
			      print_cvar_tree(-el,level);
				  
			      printf("\n\n");
				  
			    }
			      
			      
			  return ( MAX_COST);
			}
		    }
		      

		  continue;
		}


	      if (is_fact_in_additive_effects_start
		  (act_pos, gef_conn[act_pos].sf->PC_overall[i]))
		continue;

	      if (fact_is_supported (el, level))

		{
#ifdef __TEST__
		  printf ("\n Supported fact %s lev %d",
			  print_ft_name_string (el, temp_name), level);
#endif
		  if (n_cost->act_time <
		      CONVERT_FACT_TO_NODE (el, level)->time_f)
		    n_cost->act_time =
		      CONVERT_FACT_TO_NODE (el, level)->time_f;

		  continue;
		}




	      if(GET_BIT (Hvar.ri_supp_bit_vect_facts, el))
		{
		  //#ifdef __TEST__
		  if(DEBUG5)
		    printf ("\n  fact %s lev %d in  Hvar.bit_vect_facts == 1",
			    print_ft_name_string (el, temp_name), level);
		  //#endif
		  continue;
		}


	      if (GpG.penalize_inconsistence_in_relaxed_plan)
		{ 

		  if (Hvar.constr->constraint_type == C_T_UNSUP_FACT
		      && el== Hvar.constr->fact)
		    {
#ifdef __TEST__
		      printf
			("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
      
#endif
		      n_cost->weight= MAX_COST;
		      n_cost->act_cost= MAX_COST;
		      n_cost->act_time= MAX_COST;
			
		      if(DEBUG4)
			{
			  printf("\nDG INSERTION STOP FACT to MAXCOST %d, level %d, name ",  el, level);
			  if(el>=0)
			    print_ft_name(el);

			  printf("\n\n");

			}      
		      return ( MAX_COST);
		    }

		}


	      // Da migliorare
	      act_level=get_dg_fact_cost (el, level, &loc_dg_cost);

	      if (loc_dg_cost==NULL)
		{
		  n_cost->weight = MAX_COST;
		  n_cost->num_actions = MAX_COST;
		  n_cost->act_time = MAX_COST;	 
		  return ( MAX_COST);
		}		
	      else
		{

		  compute_fast_fact_cost(level,  act_level, loc_dg_cost->best_act);
		}

#ifdef __TEST__
	      printf
		("\n Unsupported fact %s lev %d weight %.2f cost  %.2f time  %.2f num_actions %d ",
		 print_ft_name_string (el, temp_name), level,
		 (float)  Hvar.ri_num_actions_define_cost  , Hvar.ri_cost_actions_define_cos,
	     0.0, Hvar.ri_num_actions_define_cost);
#endif
	    }



	  for (i = 0, temp = 0.0; i < gef_conn[act_pos].sf->num_PC_end; i++)
	    {
	      el = gef_conn[act_pos].sf->PC_end[i];

	      if (el < 0)
		{
		  if (!is_num_prec_satisfied (el,level))
		    {
		      //#ifdef __TEST_REACH__
		      {
			//			  get_dg_num_fact_cost (-el, level - 1, &loc_dg_num_cost);
			num_actions=num_action_for_unsup_num_precondition(-el, level);
			if(num_actions<=0)
			  printf("\n Warning num_actions = %d ", num_actions);
			else
			  if (num_actions== MAX_COST) // loc_dg_num_cost==NULL)
			    {
			      n_cost->weight = MAX_COST;
			      n_cost->num_actions = MAX_COST;
			      n_cost->act_time = MAX_COST;
			      return ( MAX_COST);
			    }		
			  else
			    {

			      n_cost->weight += (float) num_actions;

			      n_cost->num_actions += num_actions;
			    }		       		      
			  
		      }

		    }


		      
		  if (GpG.penalize_inconsistence_in_relaxed_plan)
		    { 
			  
		      if (Hvar.constr->constraint_type ==C_T_UNSUP_NUM_FACT
			  && Hvar.constr->fact == -el)
			{
#ifdef __TEST__
			  printf
			    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
			      
#endif
			      
			  n_cost->weight= MAX_COST;
			  n_cost->act_cost= MAX_COST;
			  n_cost->act_time= MAX_COST;
			      
			      
			  if(DEBUG4)
			    {
			      printf("\nSTOP FACT to MAXCOST %d, level %d, name ",  el, level);
			      print_cvar_tree(-el,level);
				  
			      printf("\n\n");
				  
			    }
			      
			      
			  return ( MAX_COST);
			}
		    }
		      
		  continue;
		      
		}



	      if (is_fact_in_additive_effects (act_pos, gef_conn[act_pos].sf->PC_end[i]))
		continue;

		  
	      if (fact_is_supported (el, level))  
		{
#ifdef __TEST__
		  printf ("\n Supported fact %s lev %d",
			  print_ft_name_string (el, temp_name), level);
#endif
		  if( n_cost->act_time < CONVERT_FACT_TO_NODE(el, level)->time_f -get_action_time(act_pos,0))
		    n_cost->act_time = CONVERT_FACT_TO_NODE(el, level)->time_f -get_action_time(act_pos,0);

		  continue;
		}
		  


	      if(GET_BIT (Hvar.ri_supp_bit_vect_facts, el))
		{
		  //#ifdef __TEST__
		  if(DEBUG5)
		    printf ("\n  fact %s lev %d in  Hvar.bit_vect_facts == 1",
			    print_ft_name_string (el, temp_name), level);
		  //#endif
		  continue;
		}



	      if (GpG.penalize_inconsistence_in_relaxed_plan)
		{ 

		  if (Hvar.constr->constraint_type == C_T_UNSUP_FACT
		      && el== Hvar.constr->fact)
		    {
#ifdef __TEST__
		      printf
			("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
      
#endif
		      n_cost->weight= MAX_COST;
		      n_cost->act_cost= MAX_COST;
		      n_cost->act_time= MAX_COST;
			
		      if(DEBUG4)
			{
			  printf("\nDG INSERTION STOP FACT to MAXCOST %d, level %d, name ",  el, level);
			  if(el>=0)
			    print_ft_name( el );

			  printf("\n\n");

			}      
		      return ( MAX_COST);
		    }

		}


	      // Da migliorare
	      act_level=get_dg_fact_cost (el, level, &loc_dg_cost);

	      if (loc_dg_cost==NULL)
		{
		  n_cost->weight = MAX_COST;
		  n_cost->num_actions = MAX_COST;
		  n_cost->act_time = MAX_COST; 
		  return ( MAX_COST);
		}		
	      else
		{

		  compute_fast_fact_cost(level,  act_level, loc_dg_cost->best_act);
		}

#ifdef __TEST__
	      printf
		("\n Unsupported fact %s lev %d weight %.2f cost  %.2f time  %.2f num_actions %d ",
		 print_ft_name_string (el, temp_name), level,
		 (float)Hvar.ri_num_actions_define_cost  , Hvar.ri_cost_actions_define_cos,
	     0.0, Hvar.ri_num_actions_define_cost);
#endif
	    }

	}


      total = prec_par * n_cost->weight;


      if (DEBUG5)
	printf ("\n Num. P: %.2f", n_cost->weight);


      /* Effetti additivi at end
       */
      for (i = 0; i < gef_conn[ act_pos ].num_A; i++)
	/* Non prendo in considerazione effetti numerici
	 */
	if (gef_conn[ act_pos ].A[i] >= 0)
	  {
	    /* Rendo il fatto attualmente supportato
	     */

	      SET_BIT(Hvar.ri_supp_bit_vect_facts, gef_conn[ act_pos ].A[i]);

	  }



    }

  if (excl_par)
    {


      for (temp = 0, i= j = 0; i < gnum_ft_block; i++, j+=32)
	if (vectlevel[level]->prec_vect[i])	// Solo se sono diversi da 0 faccio il test 
	  {
	    temp1 = CONVERT_ACTION_TO_VERTEX (act_pos)->ft_exclusive_vect[i] & (vectlevel[level]->fact_vect[i]) & vectlevel[level]->prec_vect[i];
	    k = 32;

	    while (temp1)
	      {
		k--;
		if (temp1 & FIRST_1)
		  {	
		      
		    el=j+k;


		    if(GET_BIT (Hvar.ri_supp_bit_vect_facts, el))
		      {
			//#ifdef __TEST__
			if(DEBUG5)
			  printf ("\n  fact %s lev %d in  Hvar.bit_vect_facts == 1",
				  print_ft_name_string (el, temp_name), level);
			//#endif
			n_cost->weight++;
		      }
		    else
		      {


			act_level=get_dg_fact_cost (el, level, &loc_dg_cost);
			  
			if (loc_dg_cost==NULL)
			  {
			    n_cost->weight = MAX_COST;
			    n_cost->num_actions = MAX_COST;
			    n_cost->act_time = MAX_COST; 
			    return ( MAX_COST);
			  }		
			else
			  {
			    compute_fast_fact_cost( level,  act_level, loc_dg_cost->best_act);
			  }
		      }
		  }
		temp1 <<= 1;
	      }



	  }


    }








  if (FALSE && GpG.Twalkplan && GpG.tabu_length >0)
    {				
      /* T_walkgraph: increase the cost function of act if it is in
	 the tabu list 
      */
      diff = GpG.count_num_try - gef_conn[act->position].step;
      
      if (diff < GpG.tabu_length)
	n_cost->weight += GpG.delta * (GpG.tabu_length - diff);
    }

	
	  
  if (GpG.timed_facts_present) {
    if (GET_BIT(GpG.has_timed_preconds, act_pos))
      {
      
	/*
	  -time_Timed_Prec restituisce l'istante in cui  l'azione puo' iniziare considerando le precondiz temporali
	  - num_Timed_Prec indica il numero di precondizione temporali che non si e' riusciti ad assegnare
	*/
	time_Timed_Prec = search_for_pc_intervals(n_cost->act_time,  act_pos, 0, &num_Timed_Prec);
	
	if (num_Timed_Prec > 0)
	  {
	    total +=num_Timed_Prec;// *  GpG.SearchCost_UnsupTimedFact;
	    n_cost->act_cost +=10.0;// MAX_COST; CAZZO
	    n_cost->act_time +=10.0;//  MAX_COST;
	    
	    if(DEBUG3)
	      printf("\nTF-BA: Increase search cost for %d unsup timed prec of best action candidate  %s", num_Timed_Prec, print_op_name_string(act_pos, temp_name));
	  }
	
	if( time_Timed_Prec>0)
	  {
	    if(n_cost->act_time < time_Timed_Prec)
	      {
		n_cost->act_time= time_Timed_Prec;
		if(DEBUG3)
		  printf("\nTF-BA: Update start time %.2f of %s", n_cost->act_time, print_op_name_string(act_pos, temp_name));
	      }	      
	  }
  
      }
  }

  

  if(max_time_for_timed_fact<MAXFLOAT && GpG.timed_facts_present)
    {

      for (i=0; i < gnum_timed_facts; i++)
	for (j=0; j < gnum_tmd_interval[i]; j++)
	  {
	    if (n_cost->act_time + max_time_for_timed_fact > gtimed_fct_vect[i][j].slack) 
	      {
		total ++;
		if (DEBUG3) 
		  {
		    printf("\nTF-BA: Increase cost for BA %s: time(BA) %.2f, time of previous actions in Rplan %.2f, slack %.2f", print_op_name_string(act_pos,temp_name),n_cost->act_time,max_time_for_timed_fact,gtimed_fct_vect[i][j].slack);
		    printf("for timed fact %s", print_ft_name_string(gtimed_fct_vect[i][j].position,temp_name));
		  }
	      }
	  }
    }


  
  n_cost->weight+= Hvar.ri_num_actions_define_cost;
 n_cost->num_actions+=Hvar.ri_num_actions_define_cost;
  n_cost->act_cost+= Hvar.ri_cost_actions_define_cost;
  n_cost->act_time=0.0; // Va calcolato bene per ora evito di consisderarlo CAZZO



  if (DEBUG4)
    {
      print_op_name(act_pos);
      printf (" tot %f [cost: %.2f  time: %.2f]\n",  n_cost->weight, n_cost->act_cost, n_cost->act_time );
    }
  if (DEBUG5)
    {
      print_op_name(act_pos);
      printf (" -> W  %f cost %f \n",  n_cost->weight,n_cost->act_cost  );
    }



  return ( n_cost->weight);

}


float
dg_insertion_action_cost (int act_pos, int level,
			  node_cost_list n_cost, float max_time_for_timed_fact)

{
  if(GpG.relaxed_neighborhood_evaluation ==0)
    return  max_neighborhood_evaluation (act_pos, level,  n_cost, max_time_for_timed_fact);
  else
    return  relaxed_neighborhood_evaluation (act_pos, level,  n_cost, max_time_for_timed_fact);
}







float
best_action_evaluation ( int act_pos, int level, node_cost_list n_cost, 
                           float max_time_for_timed_fact, node_cost_list max_n_cost)
{

  register int i;
  int j, diff, el, num_actions;

  register EfConn *act;
  float total, prec_par, excl_par, add_effect_par, temp;
  dg_inform_list loc_dg_cost = NULL;
  float time_Timed_Prec=-1.0;

  int num_Timed_Prec=0;
  float penalization =0.0;
 
  Bool save_action_cost_list = (GpG.save_action_cost_list && (!gef_conn[act_pos].has_numeric_precs));

  //#ifdef __TEST_REACH__
  //  dg_num_inform_list loc_dg_num_cost;
  //#endif


#ifdef __TEST_REACH__
  dg_num_inform_list loc_dg_num_cost;
  int cost_unsup_num_fact = 1;
#endif

  //  assert(gis_inertial[1]==0);

  /* Define the alpha, beta, gamma coefficents of F() to  
     remove the action act from the action subgraph */

  prec_par = GpG.prec_par;
  excl_par = GpG.excl_par;
  add_effect_par = GpG.add_effect_par;

  total = 0.0;
  n_cost->weight = 0.0;  // starting penalization : the action itself
  n_cost->num_actions = 0;
  n_cost->act_cost = 0.0;
  n_cost->act_time = 0.0;

  act = &gef_conn[act_pos];

  if (DEBUG5)
    printf ("\n\n\n >>> DG_INSERTION  Act: %s, level %d ",
	    print_op_name_string (act_pos, temp_name), level);

#ifdef __TEST__
  printf ("\nFIC ");
#endif


  /* Cost of  unsatisfied Preconditions */
  if (prec_par)
    {
	  // **** Precondizioni AT START
	  for (i = 0, temp = 0.0; i < gef_conn[act_pos].num_PC; i++)
	    {
	      el = gef_conn[act_pos].PC[i];

	      //LAZZA
	      if (el < 0)
		{
		  if (!is_num_prec_satisfied_in_common_level (el))
		    {
		      //#ifdef __TEST_REACH__
		      {
			//get_dg_num_fact_cost (-el, level - 1, &loc_dg_num_cost); 
			num_actions = num_action_for_unsup_num_precondition(-el, level);

			if(num_actions<=0)
			  printf("\n Warning num_actions = %d ", num_actions);


			if (num_actions == MAX_COST) // loc_dg_num_cost==NULL)
			  {
			    n_cost->weight = MAX_COST;
			    n_cost->num_actions = MAX_COST;
			    n_cost->act_time = MAX_COST;
			    return ( MAX_COST);
			  }		
			else
			  {
			    if (n_cost->weight < (float) num_actions) //(float) loc_dg_num_cost->num_actions)     
			      n_cost->weight = (float) num_actions; // loc_dg_num_cost->num_actions;	//->totcost;
			    if (n_cost->num_actions < num_actions) //  loc_dg_num_cost->num_actions)
			      n_cost->num_actions = num_actions;
			  }
		      }
		      
		      // Da ricalcolare perche' consideriamo raggiungibilita' iniziale
		      
		      if (n_cost->weight > max_n_cost->weight) 
			return (n_cost->weight);
					      
		    }


		  if (GpG.penalize_inconsistence_in_relaxed_plan==2)
		    { 
		      
		      if (Hvar.constr->constraint_type ==C_T_UNSUP_NUM_FACT
			  && Hvar.constr->fact == -el)
			{
#ifdef __TEST__
			  printf
			    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
			  
#endif
			  
			  if(DEBUG4)
			    {
			    printf("\nPenalize FACT  %d, level %d, name ",  el, level);
			    print_cvar_tree(-el,level);
			    
			    printf("\n\n");
			    
			    }
			  
			  penalization++;
			}
		      
		    }
		  
		  continue;
		  
		}


	      if (is_fact_supported_in_relaxed_plan (el,level))
		{
		  //#ifdef __TEST__
		  if(DEBUG5)
		    printf ("\n Supported fact %s lev %d",
			  print_ft_name_string (el, temp_name), level);
		  //#endif

		  if( n_cost->act_time < CONVERT_FACT_TO_NODE(el, level)->time_f)
		  n_cost->act_time = CONVERT_FACT_TO_NODE(el, level)->time_f;
		  continue;
		}

	   
	      if ( GET_BIT (Hvar.bit_vect_facts, el))
		{
		  //#ifdef __TEST__
		  if(DEBUG5)
		    printf ("\n  fact %s lev %d in  Hvar.bit_vect_facts == 1",
			  print_ft_name_string (el, temp_name), level);
		  //#endif
		  if (n_cost->act_time <
		      CONVERT_FACT_TO_NODE (el, level)->time_f)
		    n_cost->act_time =
		      CONVERT_FACT_TO_NODE (el, level)->time_f;

		  continue;
		}



	      if (GpG.penalize_inconsistence_in_relaxed_plan==2)
		{ 
		  if (Hvar.constr->constraint_type == C_T_UNSUP_FACT
		      && el== Hvar.constr->fact)
		    {
#ifdef __TEST__
		      printf
			("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
		      
#endif
		      
		      if(DEBUG4)
			{
			  printf("\nPenalize FACT %d, level %d, name ",  el, level);
			  if(el>=0)
			    print_ft_name( el );
			      
			  printf("\n\n");
			      
			}      
		      
		      penalization++;
		    }
		}

	      // Da migliorare
	      get_dg_fact_cost (el, level, &loc_dg_cost);

	      if (loc_dg_cost==NULL)
		{
		  if (save_action_cost_list)
		    update_fact_in_action_cost_list(act_pos, level, el, MAX_COST); 
		  
		  n_cost->weight = MAX_COST;
		  n_cost->num_actions = MAX_COST;
		  n_cost->act_time = MAX_COST;
		  return ( MAX_COST);
		}		
		else
		{ 
		  if (save_action_cost_list)
		    update_fact_in_action_cost_list(act_pos, level, el, (float)loc_dg_cost->num_actions); 
		  
		  if (n_cost->weight < (float) loc_dg_cost->num_actions)	// ->totcost)
		    n_cost->weight = (float) loc_dg_cost->num_actions;	//->totcost;
		  if (n_cost->num_actions < loc_dg_cost->num_actions)
		    n_cost->num_actions = loc_dg_cost->num_actions;
		  if (n_cost->act_cost < loc_dg_cost->cost)
		    n_cost->act_cost = loc_dg_cost->cost;
		  if (n_cost->act_time < loc_dg_cost->duration)
		    n_cost->act_time = loc_dg_cost->duration;
		}


	      if (n_cost->weight > max_n_cost->weight) 
		return (n_cost->weight);
		
	      	      

#ifdef __TEST__
	      printf
		("\n Unsupported fact %s lev %d weight %.2f cost  %.2f time  %.2f num_actions %d ",
		 print_ft_name_string (el, temp_name), level,
		 (float) loc_dg_cost->num_actions, loc_dg_cost->cost,
		 loc_dg_cost->duration, loc_dg_cost->num_actions);
#endif
	    }

	  // **** Precondizioni OVERALL
	  if (gef_conn[act_pos].sf != NULL)
	    {
	      for (i = 0, temp = 0.0; i < gef_conn[act_pos].sf->num_PC_overall; i++)
		{
		  el = gef_conn[act_pos].sf->PC_overall[i];


		  if (el < 0)
		    {
		      if (!is_num_prec_satisfied_in_common_level (el))
			{
			  //#ifdef __TEST_REACH__
			  {
			    //			    get_dg_num_fact_cost (-el, level - 1, &loc_dg_num_cost);
			    
			    num_actions = num_action_for_unsup_num_precondition(-el, level);
			   
			    if(num_actions<=0)
			      printf("\n Warning num_actions = %d ", num_actions);

			    
			    if (num_actions == MAX_COST) //loc_dg_num_cost==NULL)
			      {
				n_cost->weight = MAX_COST;
				n_cost->num_actions = MAX_COST;
				n_cost->act_time = MAX_COST;
				return ( MAX_COST);
			      }		
			    else
			      {
				if (n_cost->weight < (float) num_actions) //(float) loc_dg_num_cost->num_actions)     
				  n_cost->weight = (float) num_actions; // loc_dg_num_cost->num_actions;	//->totcost;
				if (n_cost->num_actions < num_actions) //  loc_dg_num_cost->num_actions)
				  n_cost->num_actions = num_actions;
			      }
			  }    
			 
			  // Da ricalcolare perche' consideriamo raggiungibilita' iniziale
			  if (n_cost->weight > max_n_cost->weight) 
			    return (n_cost->weight);
			    
			  
			}
		
			  
		      if (GpG.penalize_inconsistence_in_relaxed_plan==2)
			{ 
			  
			  if (Hvar.constr->constraint_type ==C_T_UNSUP_NUM_FACT
			      && Hvar.constr->fact == -el)
			    {
#ifdef __TEST__
			      printf
				    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
			      
#endif
			      
			      if(DEBUG4)
				{
				  printf("\nPenalize FACT %d, level %d, name ",  el, level);
				  print_cvar_tree(-el,level);
				  
				  printf("\n\n");
				  
				}
			      
			      
			      penalization++;

			    }
			}
		      

		      continue;
		      
		    }


		  if (is_fact_in_additive_effects_start(act_pos, gef_conn[act_pos].sf->PC_overall[i]))
		    continue;
		  
		  if (is_fact_supported_in_relaxed_plan (el, level))
		    {
#ifdef __TEST__
		      printf ("\n Supported fact %s lev %d",
			      print_ft_name_string (el, temp_name), level);
#endif
		      if (n_cost->act_time <
			  CONVERT_FACT_TO_NODE (el, level)->time_f)
			n_cost->act_time =
			  CONVERT_FACT_TO_NODE (el, level)->time_f;

		      continue;
		    }


		  if ( GET_BIT (Hvar.bit_vect_facts, el))
		    {
#ifdef __TEST__
		      printf
			("\n  fact %s lev %d in  Hvar.bit_vect_facts == 1",
			 print_ft_name_string (el, temp_name), level);
#endif
		      continue;
		    }


		  if (GpG.penalize_inconsistence_in_relaxed_plan==2)
		    { 

		      if (Hvar.constr->constraint_type == C_T_UNSUP_FACT
			  && el== Hvar.constr->fact)
			{
#ifdef __TEST__
			  printf
			    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
      
#endif
			
			  if(DEBUG4)
			    {
			      printf("\nPenalize FACT %d, level %d, name ",  el, level);
			      if(el>=0)
				print_ft_name(el);

			      printf("\n\n");

			    }      

			  
			  penalization++;
			}

		    }

		  // Da migliorare
		  get_dg_fact_cost (el, level, &loc_dg_cost);

		  if (loc_dg_cost==NULL)
		    {
		      if (save_action_cost_list)
			update_fact_in_action_cost_list(act_pos, level, el, MAX_COST);

		      n_cost->weight = MAX_COST;
		      n_cost->num_actions = MAX_COST;
		      n_cost->act_time = MAX_COST;	 
		      return ( MAX_COST);
		    }		
		  else
		    {
		      if (save_action_cost_list)
			update_fact_in_action_cost_list(act_pos, level, el, (float)loc_dg_cost->num_actions); 

		      if (n_cost->weight < (float) loc_dg_cost->num_actions)	// ->totcost)
			n_cost->weight = (float) loc_dg_cost->num_actions;	//->totcost;
		      if (n_cost->num_actions < loc_dg_cost->num_actions)
			n_cost->num_actions = loc_dg_cost->num_actions;
		      if (n_cost->act_cost < loc_dg_cost->cost)
			n_cost->act_cost = loc_dg_cost->cost;
		      if (n_cost->act_time < loc_dg_cost->duration)
			n_cost->act_time = loc_dg_cost->duration;
		    }

		 
		  if (n_cost->weight > max_n_cost->weight) 
		    return (n_cost->weight);
		    
#ifdef __TEST__
		  printf
		    ("\n Unsupported fact %s lev %d weight %.2f cost  %.2f time  %.2f num_actions %d ",
		     print_ft_name_string (el, temp_name), level,
		     (float) loc_dg_cost->num_actions, loc_dg_cost->cost,
		     loc_dg_cost->duration, loc_dg_cost->num_actions);
#endif
		}



	      for (i = 0, temp = 0.0; i < gef_conn[act_pos].sf->num_PC_end; i++)
		{
		  el = gef_conn[act_pos].sf->PC_end[i];


		  if (el < 0)
		    {
		      if (!is_num_prec_satisfied_in_common_level (el))
			{
			  //#ifdef __TEST_REACH__
			  {

			    //			  get_dg_num_fact_cost (-el, level - 1, &loc_dg_num_cost);
			    num_actions=num_action_for_unsup_num_precondition(-el, level);

			    if(num_actions<=0)
			      printf("\n Warning num_actions = %d ", num_actions);
			    

			    if (num_actions== MAX_COST) // loc_dg_num_cost==NULL)
			      {
				n_cost->weight = MAX_COST;
				n_cost->num_actions = MAX_COST;
				n_cost->act_time = MAX_COST;
				return ( MAX_COST);
			      }		
			    else
			      {
				if (n_cost->weight < (float) num_actions) //(float) loc_dg_num_cost->num_actions)     
				  n_cost->weight = (float) num_actions; // loc_dg_num_cost->num_actions;	//->totcost;
				if (n_cost->num_actions < num_actions) //  loc_dg_num_cost->num_actions)
				  n_cost->num_actions = num_actions;
			      }				    
			    
			  }
			  
			  // Da ricalcolare perche' consideriamo raggiungibilita' iniziale
			  if (n_cost->weight > max_n_cost->weight) 
			    return (n_cost->weight);
			    						  
			}
		      
		      if (GpG.penalize_inconsistence_in_relaxed_plan==2)
			{ 
			  
			  if (Hvar.constr->constraint_type ==C_T_UNSUP_NUM_FACT
			      && Hvar.constr->fact == -el)
			    {
#ifdef __TEST__
			      printf
				    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
			      
#endif
			      			      
			      
			      if(DEBUG4)
				{
				  printf("\nPenalize FACT %d, level %d, name ",  el, level);
				  print_cvar_tree(-el,level);
				  
				  printf("\n\n");
				  
				}
			      
			    }
			}
		      
		      continue;
		      
		    }
		  //ENDLAZZA


		  if (is_fact_in_additive_effects (act_pos, gef_conn[act_pos].sf->PC_end[i]))
		    continue;
		  
		  if (is_fact_supported_in_relaxed_plan (el, level))
		    {
#ifdef __TEST__
		      printf ("\n Supported fact %s lev %d",
			      print_ft_name_string (el, temp_name), level);
#endif
		      if( n_cost->act_time < CONVERT_FACT_TO_NODE(el, level)->time_f -get_action_time(act_pos,0))
			n_cost->act_time = CONVERT_FACT_TO_NODE(el, level)->time_f -get_action_time(act_pos,0);

		      continue;
		    }
		  
		  // SSSS
		  if (GET_BIT (Hvar.bit_vect_facts, el))
		    {
#ifdef __TEST__
		      printf
			("\n  fact %s lev %d in  Hvar.bit_vect_facts == 1",
			 print_ft_name_string (el, temp_name), level);
#endif

		      if (n_cost->act_time <
			  CONVERT_FACT_TO_NODE (el, level)->time_f)
			n_cost->act_time =
			  CONVERT_FACT_TO_NODE (el, level)->time_f;


		      continue;
		    }

		  if (GpG.penalize_inconsistence_in_relaxed_plan==2)
		    { 

		      if (Hvar.constr->constraint_type == C_T_UNSUP_FACT
			  && el== Hvar.constr->fact)
			{
#ifdef __TEST__
			  printf
			    ("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
      
#endif
					
			  if(DEBUG4)
			    {
			      printf("\nPenalize FACT %d, level %d, name ",  el, level);
			      if(el>=0)
				print_ft_name( el );

			      printf("\n\n");

			    }      
		 
			  penalization++;
			}

		    }


		  // Da migliorare
		  get_dg_fact_cost (el, level, &loc_dg_cost);

		  if (loc_dg_cost==NULL)
		    {
		      if (save_action_cost_list)
			update_fact_in_action_cost_list(act_pos, level, el, MAX_COST);

		      n_cost->weight = MAX_COST;
		      n_cost->num_actions = MAX_COST;
		      n_cost->act_time = MAX_COST; 
		      return ( MAX_COST);
		    }		
		  else
		    {
		      if (save_action_cost_list)
			update_fact_in_action_cost_list(act_pos, level, el, (float)loc_dg_cost->num_actions); 

		      if (n_cost->weight < (float) loc_dg_cost->num_actions)	// ->totcost
			n_cost->weight = (float) loc_dg_cost->num_actions;	//->totcost;
		      if (n_cost->num_actions < loc_dg_cost->num_actions)
			n_cost->num_actions = loc_dg_cost->num_actions;
		      if (n_cost->act_cost < loc_dg_cost->cost)
			n_cost->act_cost = loc_dg_cost->cost;
		      if (n_cost->act_time < loc_dg_cost->duration)
			n_cost->act_time = loc_dg_cost->duration;
		    }

		  if (n_cost->weight > max_n_cost->weight) 
		    return (n_cost->weight);
		    		  
#ifdef __TEST__
		  printf
		    ("\n Unsupported fact %s lev %d weight %.2f cost  %.2f time  %.2f num_actions %d ",
		     print_ft_name_string (el, temp_name), level,
		     (float) loc_dg_cost->num_actions, loc_dg_cost->cost,
		     loc_dg_cost->duration, loc_dg_cost->num_actions);
#endif
		}

	    }



	  total = prec_par * n_cost->weight;

	  
	  if (DEBUG5)
	    printf ("\n Num. P: %.2f", n_cost->weight);
	  
	    
    }
  
  if (excl_par)
    {
      
      if(GpG.mutex_and_additive_effects)
	temp = (float) count_mutex_noop_at_start (act_pos, level);
      else
	temp = (float) count_mutex_facts (act_pos, level);


      total += excl_par*GpG.weight_mutex_in_relaxed_plan * temp;

      if (DEBUG5)
	printf ("\n  M.E.: %.2f   ", temp);
      
      if (save_action_cost_list)
	update_mutex_in_action_cost_list(act_pos, (int) temp); 
      
    }
  else if (save_action_cost_list)
    update_mutex_in_action_cost_list(act_pos, 0); 
  
  
  
  if (FALSE && GpG.Twalkplan && GpG.tabu_length >0)
    {				
      /* T_walkgraph: increase the cost function of act if it is in
	 the tabu list 
      */
      diff = GpG.count_num_try - gef_conn[act->position].step;
      
      if (diff < GpG.tabu_length)
	total += GpG.delta * (GpG.tabu_length - diff);
    }
  
  
  if (GpG.timed_facts_present) {
    if (GET_BIT(GpG.has_timed_preconds, act_pos))
      {
	
	/*
	  -time_Timed_Prec restituisce l'istante in cui  l'azione puo' iniziare considerando le precondiz temporali
	  - num_Timed_Prec indica il numero di precondizione temporali che non si e' riusciti ad assegnare
	*/
	time_Timed_Prec = search_for_pc_intervals(n_cost->act_time,  act_pos, 0, &num_Timed_Prec);
	
	if (num_Timed_Prec > 0)
	  {
	    total +=num_Timed_Prec;// *  GpG.SearchCost_UnsupTimedFact;
	    n_cost->act_cost +=10.0;// MAX_COST; CAZZO
	    n_cost->act_time +=10.0;//  MAX_COST;
	    
	    if(DEBUG3)
	      printf("\nTF-BA: Increase search cost for %d unsup timed prec of best action candidate  %s", num_Timed_Prec, print_op_name_string(act_pos, temp_name));
	  }
	
	if( time_Timed_Prec>0)
	  {
	    if(n_cost->act_time < time_Timed_Prec)
	      {
		n_cost->act_time= time_Timed_Prec;
		if(DEBUG3)
		  printf("\nTF-BA: Update start time %.2f of %s", n_cost->act_time, print_op_name_string(act_pos, temp_name));
	      }	      
	  }
	
      }
  }
  

  total+=penalization;
  total++;			//l'azione stessa
  n_cost->act_cost += get_action_cost (act_pos, level, NULL);
  n_cost->act_time += get_action_time (act_pos, 0);

  if (save_action_cost_list)
    update_act_time_cost_in_list(act_pos, n_cost->act_time);

  n_cost->weight = total;
  n_cost->num_actions++;	// l'azione stessa
  
  
  if(max_time_for_timed_fact<MAXFLOAT && GpG.timed_facts_present)
    {
      
      for (i=0; i < gnum_timed_facts; i++)
	for (j=0; j < gnum_tmd_interval[i]; j++)
	  {
	    if (n_cost->act_time + max_time_for_timed_fact > gtimed_fct_vect[i][j].slack) 
	      {
		total ++;
		if (DEBUG3) 
		  {
		    printf("\nTF-BA: Increase cost for BA %s: time(BA) %.2f, time of previous actions in Rplan %.2f, slack %.2f", print_op_name_string(act_pos,temp_name),n_cost->act_time,max_time_for_timed_fact,gtimed_fct_vect[i][j].slack);
		    printf("for timed fact %s", print_ft_name_string(gtimed_fct_vect[i][j].position,temp_name));
		  }
	      }
	  }
    }
  
  
  if (DEBUG4)
    {
      print_op_name(act_pos);
      printf (" tot %f [cost: %.2f  time: %.2f]\n", total, n_cost->act_cost, n_cost->act_time );
    }
  if (DEBUG5)
    {
      printf("\n END eval action ");
      print_op_name(act_pos);
      printf (" -> tot %f\n", total);
    }
  
  return (total);
  
}








///////////////////////////////////////////////////////////

// Sezione dedicata alle funzioni di DISTANCE_GRAPH


void action_remotion_negative_numeric_effects(neighb_list neighb_act, int level, node_cost_list  best_eff_cost )
{
  int i;
  int next_level;
  int num_vars=0; 
  int action_pos; 
  int counter;
  float temp_max,temp_min, effect=0.0, eff=0.0,  temp;
  int unsat_facts=0;
  node_cost loc_n_cost;


 if(Hvar.temp_num_level==NULL)
    Hvar.temp_num_level=(float *)calloc(gnum_comp_var, sizeof (float));
  if(Hvar.to_control==NULL)
    Hvar.to_control=alloc_vect(gnum_block_compvar);


  next_level = level + 1;

	  /* Facciamo la propagazione in avanti per vedere le azioni che risultano non supportate o che si
	     allontaneranno dal valore di verita' dopo la rimozione dell'azione*/

      if(gef_conn[neighb_act->act_pos].is_numeric && next_level<GpG.curr_plan_length)
	{
	  reset_bitarray(Hvar.to_control,gnum_block_compvar);
	  memcpy(Hvar.temp_num_level,vectlevel[neighb_act->act_level]->numeric->values,gnum_comp_var*sizeof(float));
	  for(i=0;i<gef_conn[neighb_act->act_pos].num_numeric_effects;i++)
	    {
	      add_affects_list(gef_conn[neighb_act->act_pos].numeric_effects[i].lval,Hvar.to_control);
	      num_vars++;
	      
	    }
       
	  for(next_level=level+1;next_level<=GpG.curr_plan_length;next_level++)
	    {
	      if (num_vars==0)
		break;
	      if(next_level==GpG.curr_plan_length)
		{

		  for(i=0;i<gnum_comp_var;i++)
		    {
		      if(vectlevel[next_level]->numeric->w_is_goal[i])
			{
			  if(!GET_BIT(Hvar.to_control,i))
			    continue;
			  if(vectlevel[next_level]->numeric->values[i]<0.5)
			    {
			      
			      if(gcomp_var[i].operator==GREATER_THAN_OP || 
				 gcomp_var[i].operator== GREATER_OR_EQUAL_OP)
				if(vectlevel[next_level]->numeric->values[gcomp_var[i].first_op] >
				   Hvar.temp_num_level[gcomp_var[i].first_op])
				  {
				    
				    unsat_facts++;
				    temp_max= Hvar.common_max_values[gcomp_var[i].first_op];
				    temp_min=Hvar.common_min_values[gcomp_var[i].first_op];
				    Hvar.common_max_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];
				    Hvar.common_min_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];
				    
				    /*
				     loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatt -i
				     Azzero loc_n_cost
				    */
				    loc_n_cost.weight = 0.0;
				    loc_n_cost.act_cost = 0.0;
				    loc_n_cost.act_time = 0.0;
				    loc_n_cost.action=GOAL_ACTION;
 
				    temp= compute_relaxed_fact_cost (-i,level, &loc_n_cost, next_level, MAXFLOAT);
				    
				    Hvar.common_max_values[gcomp_var[i].first_op]=temp_max;
				    Hvar.common_min_values[gcomp_var[i].first_op]=temp_min;

				    //				    RESET_BIT(Hvar.to_control,i);
				    
				    if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
				      {
					
					
					best_eff_cost->act_cost += loc_n_cost.act_cost;
					
					//      best_eff_cost->act_time += loc_n_cost.act_time; 
					
					eff += temp;
					
					
					if (best_eff_cost->act_time < loc_n_cost.act_time
					    && loc_n_cost.act_time < MAX_COST)
					  best_eff_cost->act_time = loc_n_cost.act_time;
					
					effect += temp * local_search.lamda_prec;
					
				      }
				    
			
				    continue;
				    
				    
				    
				  }
			      if(gcomp_var[i].operator==LESS_THAN_OP || 
				 gcomp_var[i].operator== LESS_THAN_OR_EQUAL_OP)
				if(vectlevel[next_level]->numeric->values[gcomp_var[i].first_op] <
				   Hvar.temp_num_level[gcomp_var[i].first_op])
				  {
				    
				    unsat_facts++;
				    
				    //				    RESET_BIT(Hvar.to_control,i);
				    //				    printf("\n entro");
				    temp_max= Hvar.common_max_values[gcomp_var[i].first_op];
				    temp_min=Hvar.common_min_values[gcomp_var[i].first_op];
				    Hvar.common_max_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];
				    Hvar.common_min_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];
				    /*
				     loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatt -i
				     Azzero loc_n_cost
				    */
				    loc_n_cost.weight = 0.0;
				    loc_n_cost.act_cost = 0.0;
				    loc_n_cost.act_time = 0.0;
				    loc_n_cost.action=GOAL_ACTION;

				    temp= compute_relaxed_fact_cost (-i,level, &loc_n_cost, next_level, MAXFLOAT);
				    if(temp==0)
				      printf("ZERO!!\n");
				    Hvar.common_max_values[gcomp_var[i].first_op]=temp_max;
				    Hvar.common_min_values[gcomp_var[i].first_op]=temp_min;


				    if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
				      {
					
					
					best_eff_cost->act_cost += loc_n_cost.act_cost;
					
					//      best_eff_cost->act_time += loc_n_cost.act_time; 
					
					eff += temp;
					
					
					if (best_eff_cost->act_time < loc_n_cost.act_time)
					    // && loc_n_cost.act_time < MAX_COST)
					  best_eff_cost->act_time = loc_n_cost.act_time;
					
					effect += temp * local_search.lamda_prec;
					
				      }
				    
				    continue;
				    
				    
				    
				  }
			      
			      
			    }
			  if(ri_eval_comp_var (&gcomp_var[i], i ,Hvar.temp_num_level
					       ,Hvar.temp_num_level,TRUE)<0.5)
			    {
			      

			      unsat_facts++;
			      
			      // RESET_BIT(Hvar.to_control,i);
			      temp_max= Hvar.common_max_values[gcomp_var[i].first_op];
			      temp_min=Hvar.common_min_values[gcomp_var[i].first_op];
			      Hvar.common_max_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];
			      Hvar.common_min_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];
			     /*
				     loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatt -i
				     Azzero loc_n_cost
			     */
			      loc_n_cost.weight = 0.0;
			      loc_n_cost.act_cost = 0.0;
			      loc_n_cost.act_time = 0.0;
			      loc_n_cost.action=GOAL_ACTION;

			      temp= compute_relaxed_fact_cost (-i,level, &loc_n_cost, next_level,MAXFLOAT);
			    
			      Hvar.common_max_values[gcomp_var[i].first_op]=temp_max;
			      Hvar.common_min_values[gcomp_var[i].first_op]=temp_min;

			      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
				{
				  
				  
				  best_eff_cost->act_cost += loc_n_cost.act_cost;
				  
				  //      best_eff_cost->act_time += loc_n_cost.act_time; 
				  
				  eff += temp;
				  
				  
				  if (best_eff_cost->act_time < loc_n_cost.act_time
				      && loc_n_cost.act_time < MAX_COST)
				    best_eff_cost->act_time = loc_n_cost.act_time;
				  
				  effect += temp * local_search.lamda_prec;
				  
				}

			      continue;
			      
			      
			    }
			  
			  
			}
		      
		      
		      
		    }
		  
		  
		}

	      /*Non sono all'ultimo livello, devo applicare gli effetti delle azioni*/
	      action_pos = vectlevel[next_level]->action.position;
	      if (action_pos < 0)		
		continue;
	      if(!gef_conn[action_pos].is_numeric)
		continue;	 
	      /* Se il livello non e' vuoto e l'azione  e' numerica*/
	      for(counter=0;counter<gef_conn[action_pos].num_PC;counter++)
		{
		  if(gef_conn[action_pos].PC[counter]<0)
		    {
		      if(!GET_BIT(Hvar.to_control,-(gef_conn[action_pos].PC[counter])))
			continue;
		      if(vectlevel[next_level]->numeric->values[-(gef_conn[action_pos].PC[counter])]<0.5)
			{
			  /* Se e' falso controllo se si e' allontanato ulteriormente 
			     dal valore di verita'*/
			  if(gcomp_var[-(gef_conn[action_pos].PC[counter])].operator==GREATER_THAN_OP || 
			     gcomp_var[-(gef_conn[action_pos].PC[counter])].operator== GREATER_OR_EQUAL_OP)
			    if(vectlevel[next_level]->numeric->values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op] >
			       Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op])
			      {
				/*In tal caso considero il costo per renderlo supportato*/
				unsat_facts++;
			       
				//	RESET_BIT(Hvar.to_control,-(gef_conn[action_pos].PC[counter]));
				temp_max= Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
				temp_min=Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
				Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
				Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]; 
				/*
				     loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
				     Azzero loc_n_cost
				*/
				    loc_n_cost.weight = 0.0;
				    loc_n_cost.act_cost = 0.0;
				    loc_n_cost.act_time = 0.0;
				    loc_n_cost.action=action_pos;

				   
				temp= compute_relaxed_fact_cost (gef_conn[action_pos].PC[counter],level, &loc_n_cost, next_level, MAXFLOAT);
			
				Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_max;
				Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_min;
			      
				if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
				  {
				    
				    
				    best_eff_cost->act_cost += loc_n_cost.act_cost;
				    
				    //      best_eff_cost->act_time += loc_n_cost.act_time; 
				    
				    eff += temp;
				    
				    
				    if (best_eff_cost->act_time < loc_n_cost.act_time
					&& loc_n_cost.act_time < MAX_COST)
				      best_eff_cost->act_time = loc_n_cost.act_time;
				    
				    effect += temp * local_search.lamda_prec;

				  }

		    
				continue;



			      }
			  if(gcomp_var[-(gef_conn[action_pos].PC[counter])].operator==LESS_THAN_OP || 
			     gcomp_var[-(gef_conn[action_pos].PC[counter])].operator== LESS_THAN_OR_EQUAL_OP)
			    if(vectlevel[next_level]->numeric->values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op] <
			       Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op])
			      {
				
				unsat_facts++;
			      
				//RESET_BIT(Hvar.to_control,-(gef_conn[action_pos].PC[counter]));
				temp_max= Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
				temp_min=Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
				Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];
				Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];

/*
				     loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
				     Azzero loc_n_cost
				*/
				    loc_n_cost.weight = 0.0;
				    loc_n_cost.act_cost = 0.0;
				    loc_n_cost.act_time = 0.0;
				    loc_n_cost.action=action_pos;
			  
				temp= compute_relaxed_fact_cost (gef_conn[action_pos].PC[counter],level, &loc_n_cost, next_level, MAXFLOAT);
			
				Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_max;
				Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_min;
		    


				if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
				  {
				    
				    
				    best_eff_cost->act_cost += loc_n_cost.act_cost;
				    
				    //      best_eff_cost->act_time += loc_n_cost.act_time; 
				    
				    eff += temp;
				    
				    
				    if (best_eff_cost->act_time < loc_n_cost.act_time
					&& loc_n_cost.act_time < MAX_COST)
				      best_eff_cost->act_time = loc_n_cost.act_time;
				    
				    effect += temp * local_search.lamda_prec;

				  }

			    
				continue;



			      }


			}


		      if(ri_eval_comp_var (&gcomp_var[-(gef_conn[action_pos].PC[counter])], -(gef_conn[action_pos].PC[counter]) ,Hvar.temp_num_level
					   ,Hvar.temp_num_level,TRUE)<0.5)
			{
			  
			  unsat_facts++;
			 
			  //RESET_BIT(Hvar.to_control,-(gef_conn[action_pos].PC[counter]));
			  temp_max= Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
			  temp_min=Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
			  Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
			  Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];

			  /*
			    loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
			    Azzero loc_n_cost
			  */
			  loc_n_cost.weight = 0.0;
			  loc_n_cost.act_cost = 0.0;
			  loc_n_cost.act_time = 0.0;
			  loc_n_cost.action=action_pos;


			  temp= compute_relaxed_fact_cost (gef_conn[action_pos].PC[counter],level, &loc_n_cost, next_level, MAXFLOAT);
		
			  Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_max;
			  Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_min;
			 


			  if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
			    {
			      
			      
			      best_eff_cost->act_cost += loc_n_cost.act_cost;
			      
			      //      best_eff_cost->act_time += loc_n_cost.act_time; 
			      
			      eff += temp;
			      
			      
			      if (best_eff_cost->act_time < loc_n_cost.act_time
				  && loc_n_cost.act_time < MAX_COST)
				best_eff_cost->act_time = loc_n_cost.act_time;
			      
			      effect += temp * local_search.lamda_prec;

			    }

			
			  continue;
			 

			}
		    }

		}
	     
	      if(next_level<GpG.curr_plan_length)
	      for(counter=0;counter<gef_conn[action_pos].num_numeric_effects;counter++)
		{
		  if(!GET_BIT(Hvar.to_control,gef_conn[action_pos].numeric_effects[counter].lval))
		    continue;
		  if(gcomp_var[gef_conn[action_pos].numeric_effects[counter].index].operator==ASSIGN_OP)
		    {
		      num_vars--;
		      sub_affects_list(gef_conn[action_pos].numeric_effects[counter].lval,Hvar.to_control);
		      continue;
		    }
		  Hvar.temp_num_level[gef_conn[action_pos].numeric_effects[counter].lval]=ri_eval_comp_var (&gcomp_var_effects[(gef_conn[action_pos].numeric_effects[counter]).index],
												       (gef_conn[action_pos].numeric_effects[counter].index) ,Hvar.temp_num_level
												       ,Hvar.temp_num_level,TRUE);
		  
		}

	    }
	}

}



void negative_numeric_effects(neighb_list neighb_act, int level,  node_cost_list  best_eff_cost)
{

  int i; 
  int next_level;
  int num_vars=0;
  int action_pos;
 
  int counter;
  float temp_max,temp_min;
  node_cost loc_n_cost;
  float effect=0.0, eff=0.0, temp;
 
  int unsat_facts=0;

 if(Hvar.temp_num_level==NULL)
    Hvar.temp_num_level=(float *)calloc(gnum_comp_var, sizeof (float));
  if(Hvar.to_control==NULL)
    Hvar.to_control=alloc_vect(gnum_block_compvar);
  num_vars=0;
  next_level=level+1;

      /* Andiamo a fare la propagazione in avanti per verificare eventuali effetti negativi dovuti
	 all'inserimento dell'azione, cioe' le precondizioni numeriche che diventano non
supportate
      */


      if(gef_conn[neighb_act->act_pos].is_numeric && next_level<GpG.curr_plan_length)
	{
	  reset_bitarray(Hvar.to_control,gnum_block_compvar);
	  memcpy(Hvar.temp_num_level,vectlevel[neighb_act->act_level]->numeric->values,gnum_comp_var*sizeof(float));
	  /* Applico gli effetti numerici dell'azione nel Hvar.temp_num_level*/
	  for(i=0;i<gef_conn[neighb_act->act_pos].num_numeric_effects;i++)
	    {
	      add_affects_list(gef_conn[neighb_act->act_pos].numeric_effects[i].lval,Hvar.to_control);
	      Hvar.temp_num_level[gef_conn[neighb_act->act_pos].numeric_effects[i].lval]=ri_eval_comp_var (&gcomp_var_effects[(gef_conn[neighb_act->act_pos].numeric_effects[i]).index],
												   (gef_conn[neighb_act->act_pos].numeric_effects[i].index) ,Hvar.temp_num_level
												   ,Hvar.temp_num_level,TRUE);
	      num_vars++;
	      
	    }
	  /*Esamino i livelli successivi per verificare eventuali preco non supportate*/
	  for(next_level=level+1;next_level<=GpG.curr_plan_length;next_level++)
	    {
	      if (num_vars==0)
		break;
	      if(next_level==GpG.curr_plan_length)
		{
		  /*Se sono all'ultimo livello esamino i goal*/
		  for(i=0;i<gnum_comp_var;i++)
		    {
		      if(vectlevel[next_level]->numeric->w_is_goal[i])
			{
			  /* E' un goal*/
			  if(!GET_BIT(Hvar.to_control,i))
			    continue; /* Se non viene influenzato non lo considero*/
			  
			  if(vectlevel[next_level]->numeric->values[i]<0.5)
			    {
			      /* Se e' falso controllo se si e' allontanato ulteriormente 
				 dal valore di verita'*/
			      if(gcomp_var[i].operator==GREATER_THAN_OP || 
				 gcomp_var[i].operator== GREATER_OR_EQUAL_OP)
				if(vectlevel[next_level]->numeric->values[gcomp_var[i].first_op] >
				   Hvar.temp_num_level[gcomp_var[i].first_op])
				  {
				    /*In tal caso considero il costo per renderlo supportato*/				    
				    unsat_facts++;
				    temp_max= Hvar.common_max_values[gcomp_var[i].first_op];
				    temp_min=Hvar.common_min_values[gcomp_var[i].first_op];
				    Hvar.common_max_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];
				    Hvar.common_min_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];

				    /*
				      loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
				      Azzero loc_n_cost
				    */
				    loc_n_cost.weight = 0.0;
				    loc_n_cost.act_cost = 0.0;
				    loc_n_cost.act_time = 0.0;
				    loc_n_cost.action=GOAL_ACTION;

				    temp= compute_relaxed_fact_cost (-i,level, &loc_n_cost, next_level, MAXFLOAT);
				    
				    Hvar.common_max_values[gcomp_var[i].first_op]=temp_max;
				    Hvar.common_min_values[gcomp_var[i].first_op]=temp_min;

				    //				    RESET_BIT(Hvar.to_control,i);
				    
				    
				    if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
				      {
					
					
					best_eff_cost->act_cost += loc_n_cost.act_cost;
					
					//      best_eff_cost->act_time += loc_n_cost.act_time; 
					
					eff += temp;
					
					
					if (best_eff_cost->act_time < loc_n_cost.act_time
					    && loc_n_cost.act_time < MAX_COST)
					  best_eff_cost->act_time = loc_n_cost.act_time;
					
					effect += temp * local_search.lamda_prec;
					
				      }
				    
			
				    continue;
				    
				    
				    
				  }
			      if(gcomp_var[i].operator==LESS_THAN_OP || 
				 gcomp_var[i].operator== LESS_THAN_OR_EQUAL_OP)
				if(vectlevel[next_level]->numeric->values[gcomp_var[i].first_op] <
				   Hvar.temp_num_level[gcomp_var[i].first_op])
				  {
				    
				    unsat_facts++;
				    
				    //				    RESET_BIT(Hvar.to_control,i);
				    //				    printf("\n entro");
				    temp_max= Hvar.common_max_values[gcomp_var[i].first_op];
				    temp_min=Hvar.common_min_values[gcomp_var[i].first_op];
				    Hvar.common_max_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];
				    Hvar.common_min_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];

				    /*
				      loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
				      Azzero loc_n_cost
				    */
				    loc_n_cost.weight = 0.0;
				    loc_n_cost.act_cost = 0.0;
				    loc_n_cost.act_time = 0.0;
				    loc_n_cost.action=GOAL_ACTION;

				    temp= compute_relaxed_fact_cost (-i,level, &loc_n_cost, next_level, MAXFLOAT);
				    if(temp==0)
				      printf("ZERO!!\n");
				    Hvar.common_max_values[gcomp_var[i].first_op]=temp_max;
				    Hvar.common_min_values[gcomp_var[i].first_op]=temp_min;


				    if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
				      {
					
					
					best_eff_cost->act_cost += loc_n_cost.act_cost;
					
					//      best_eff_cost->act_time += loc_n_cost.act_time; 
					
					eff += temp;
					
					
					if (best_eff_cost->act_time < loc_n_cost.act_time)
					    // && loc_n_cost.act_time < MAX_COST)
					  best_eff_cost->act_time = loc_n_cost.act_time;
					
					effect += temp * local_search.lamda_prec;
					
				      }
				    
				    
				    continue;
				    
				    
				    
				  }
			      
			      
			    }

			  /* Se prima era vero ed adesso e' falso*/
			  if(ri_eval_comp_var (&gcomp_var[i], i ,Hvar.temp_num_level
					       ,Hvar.temp_num_level,TRUE)<0.5)
			    {
			      
			      /* Determino il costo per renderlo supportato*/
			      unsat_facts++;
			      
			      // RESET_BIT(Hvar.to_control,i);
			      temp_max= Hvar.common_max_values[gcomp_var[i].first_op];
			      temp_min=Hvar.common_min_values[gcomp_var[i].first_op];
			      Hvar.common_max_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];
			      Hvar.common_min_values[gcomp_var[i].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];

			      /*
				loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
				Azzero loc_n_cost
			      */
			      loc_n_cost.weight = 0.0;
			      loc_n_cost.act_cost = 0.0;
			      loc_n_cost.act_time = 0.0;
			      loc_n_cost.action=GOAL_ACTION;

			     
			      temp= compute_relaxed_fact_cost (-i,level, &loc_n_cost, next_level, MAXFLOAT);
			    
			      Hvar.common_max_values[gcomp_var[i].first_op]=temp_max;
			      Hvar.common_min_values[gcomp_var[i].first_op]=temp_min;
	

			      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
				{
				  
				  
				  best_eff_cost->act_cost += loc_n_cost.act_cost;
				  
				  //      best_eff_cost->act_time += loc_n_cost.act_time; 
				  
				  eff += temp;
				  
				  
				  if (best_eff_cost->act_time < loc_n_cost.act_time
				      && loc_n_cost.act_time < MAX_COST)
				    best_eff_cost->act_time = loc_n_cost.act_time;
				  
				  effect += temp * local_search.lamda_prec;
				  
				}

			
			      continue;
			      
			      
			    }
			  
			  
			}
		      
		      
		      
		    }
		  
		  
		}
	      /*Non sono all'ultimo livello, devo applicare gli effetti delle azioni*/
	      action_pos = vectlevel[next_level]->action.position;
	      if (action_pos < 0)		
		continue;
	      if(!gef_conn[action_pos].is_numeric)
		continue;	      
	      /* Se il livello non e' vuoto e l'azione  e' numerica*/
	      for(counter=0;counter<gef_conn[action_pos].num_PC;counter++)
		{
		  if(gef_conn[action_pos].PC[counter]<0)
		    {
		      if(!GET_BIT(Hvar.to_control,-(gef_conn[action_pos].PC[counter])))
			continue;
		      if(vectlevel[next_level]->numeric->values[-(gef_conn[action_pos].PC[counter])]<0.5)
			{
			  /* Se e' falso controllo se si e' allontanato ulteriormente 
			     dal valore di verita'*/
			  if(gcomp_var[-(gef_conn[action_pos].PC[counter])].operator==GREATER_THAN_OP || 
			     gcomp_var[-(gef_conn[action_pos].PC[counter])].operator== GREATER_OR_EQUAL_OP)
			    if(vectlevel[next_level]->numeric->values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op] >
			       Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op])
			      {
				/*In tal caso considero il costo per renderlo supportato*/
				unsat_facts++;
			       
				//	RESET_BIT(Hvar.to_control,-(gef_conn[action_pos].PC[counter]));
				temp_max= Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
				temp_min=Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
				Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
				Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];

				/*
				  loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
				  Azzero loc_n_cost
				*/
				    loc_n_cost.weight = 0.0;
				    loc_n_cost.act_cost = 0.0;
				    loc_n_cost.act_time = 0.0;
				    loc_n_cost.action=action_pos;

				temp= compute_relaxed_fact_cost (gef_conn[action_pos].PC[counter],level, &loc_n_cost, next_level, MAXFLOAT);
			
				Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_max;
				Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_min;
			      

				
				if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
				  {
				    
				    
				    best_eff_cost->act_cost += loc_n_cost.act_cost;
				    
				    //      best_eff_cost->act_time += loc_n_cost.act_time; 
				    
				    eff += temp;
				    
				    
				    if (best_eff_cost->act_time < loc_n_cost.act_time
					&& loc_n_cost.act_time < MAX_COST)
				      best_eff_cost->act_time = loc_n_cost.act_time;
				    
				    effect += temp * local_search.lamda_prec;

				  }

		
				continue;



			      }
			  if(gcomp_var[-(gef_conn[action_pos].PC[counter])].operator==LESS_THAN_OP || 
			     gcomp_var[-(gef_conn[action_pos].PC[counter])].operator== LESS_THAN_OR_EQUAL_OP)
			    if(vectlevel[next_level]->numeric->values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op] <
			       Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op])
			      {
				
				unsat_facts++;
			      
				//RESET_BIT(Hvar.to_control,-(gef_conn[action_pos].PC[counter]));
				temp_max= Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
				temp_min=Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
				Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];
				Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[i].first_op];

				/*
				  loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
				  Azzero loc_n_cost
				*/
				loc_n_cost.weight = 0.0;
				loc_n_cost.act_cost = 0.0;
				loc_n_cost.act_time = 0.0;
				loc_n_cost.action=action_pos;

				temp= compute_relaxed_fact_cost (gef_conn[action_pos].PC[counter],level, &loc_n_cost, next_level, MAXFLOAT);
			
				Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_max;
				Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_min;
		    

				if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
				  {
				    
				    
				    best_eff_cost->act_cost += loc_n_cost.act_cost;
				    
				    //      best_eff_cost->act_time += loc_n_cost.act_time; 
				    
				    eff += temp;
				    
				    
				    if (best_eff_cost->act_time < loc_n_cost.act_time
					&& loc_n_cost.act_time < MAX_COST)
				      best_eff_cost->act_time = loc_n_cost.act_time;
				    
				    effect += temp * local_search.lamda_prec;

				  }

		   
				continue;



			      }


			}

		      /* Se prima era vero ed adesso e' falso*/
		      if(ri_eval_comp_var (&gcomp_var[-(gef_conn[action_pos].PC[counter])], -(gef_conn[action_pos].PC[counter]) ,Hvar.temp_num_level
					   ,Hvar.temp_num_level,TRUE)<0.5)
			{
			  
			  unsat_facts++;
			  /* Determino il costo per renderlo supportato*/
			  //RESET_BIT(Hvar.to_control,-(gef_conn[action_pos].PC[counter]));
			  temp_max= Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
			  temp_min=Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
			  Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
			  Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=Hvar.temp_num_level[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op];
			  
			  /*
			    loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
			    Azzero loc_n_cost
			  */
			  loc_n_cost.weight = 0.0;
			  loc_n_cost.act_cost = 0.0;
			  loc_n_cost.act_time = 0.0;
			  loc_n_cost.action=action_pos;

			  temp= compute_relaxed_fact_cost (gef_conn[action_pos].PC[counter],level, &loc_n_cost, next_level, MAXFLOAT);
		
			  Hvar.common_max_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_max;
			  Hvar.common_min_values[gcomp_var[-(gef_conn[action_pos].PC[counter])].first_op]=temp_min;
			 

			  if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
			    {
			      
			      
			      best_eff_cost->act_cost += loc_n_cost.act_cost;
			      
			      //      best_eff_cost->act_time += loc_n_cost.act_time; 
			      
			      eff += temp;
			      
			      
			      if (best_eff_cost->act_time < loc_n_cost.act_time
				  && loc_n_cost.act_time < MAX_COST)
				best_eff_cost->act_time = loc_n_cost.act_time;
			      
			      effect += temp * local_search.lamda_prec;

			    }

			    
			  continue;
			 

			}
		    }

		}
	      /*Applico gli effetti numerici dell'azione a Hvar.temp_num_level, se trovo un
		ASSIGN blocco la catena*/
	      if(next_level<GpG.curr_plan_length)
	      for(counter=0;counter<gef_conn[action_pos].num_numeric_effects;counter++)
		{
		  if(!GET_BIT(Hvar.to_control,gef_conn[action_pos].numeric_effects[counter].lval))
		    continue;
		  if(gcomp_var[gef_conn[action_pos].numeric_effects[counter].index].operator==ASSIGN_OP)
		    {
		      num_vars--;
		      sub_affects_list(gef_conn[action_pos].numeric_effects[counter].lval,Hvar.to_control);
		      continue;
		    }
		  Hvar.temp_num_level[gef_conn[action_pos].numeric_effects[counter].lval]=ri_eval_comp_var (&gcomp_var_effects[(gef_conn[action_pos].numeric_effects[counter]).index],
												       (gef_conn[action_pos].numeric_effects[counter].index) ,Hvar.temp_num_level
												       ,Hvar.temp_num_level,TRUE);
		  
		}

	    }
	}
}


float start_time_respect_to_mutex_constraint(int action, int level)
{

  int ind_level, ord;
  float start_time=0.0;

  for (ind_level = level - 1; ind_level >= 0; ind_level--)
    {
      if (vectlevel[ind_level]->action.w_is_used <= 0)
	continue;

      if (check_mutex_action (action, ind_level) >= 0 )
	{
	  if (GpG.constraint_type <= 1) /* Il vincolo di ordinamento tra azioni mutex e' sempre di tipo piu' restrittivo */
	    {
	      if (start_time < GET_ACTION_OF_LEVEL(ind_level)->time_f)
		start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f;
	    }
	  else /* Vincoli di ordinamento avanzati */
	    { /* Stabilisce il tipo di vincolo tra l'azione act e l'azione "GET_ACTION__OF_LEVEL(ind_level)" noto che "GET_ACTION__OF_LEVEL(ind_level)" si trova a un livello inferiore rispetto a "act"  */

	      ord = Econstraint_type(GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level, action, -1);

	      if (ord == EA_SB) // l'azione  "act" deve iniziare dopo la fine dell'azione "GET_ACTION__OF_LEVEL(ind_level)" 
		{
		  if (start_time < GET_ACTION_OF_LEVEL(ind_level)->time_f)
		    start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f;
		}
	      else
		{
		  if (ord == EA_EB) // l'azione "act"  deve finire dopo la fine di "GET_ACTION__OF_LEVEL(ind_level)" 
		    {
		      if (start_time < GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (action, level) )
			start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (action, level);
		    }
		  else
		    if (ord == SA_SB) // l'azione "act" deve iniziare dopo l'inizio di "GET_ACTION__OF_LEVEL(ind_level)" 
		      {
			if (start_time < GET_ACTION_OF_LEVEL (ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level) )
			  start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level);
		      }
		    else
		      {
			if (ord == SA_EB) // l'azione "act" deve finire dopo l'inizio di "GET_ACTION__OF_LEVEL(ind_level)" 
			  {
			    if (start_time < GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level)  - get_action_time (action, level) )
			      start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level) - get_action_time (action, level);
			  }
			else
			  {
			    if (ord == EA_EB__SA_SB) // l'azione "act" e' sovrapposta ad "GET_ACTION__OF_LEVEL(ind_level)" 
			      {
				if( get_action_time (action, level) < get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level))
				  {
				    // l'azione "act"  deve finire dopo la fine di "GET_ACTION__OF_LEVEL(ind_level)" 
				    if (start_time < GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (action, level) )
				      start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (action, level);
				  }
				else // l'azione "act" deve iniziare dopo l'inizio di "GET_ACTION__OF_LEVEL(ind_level)" 
				  {
				    if (start_time < GET_ACTION_OF_LEVEL (ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level) )
				      start_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level);

				  }
			      }
			  }
		      }
		}
	    }
	}
    }

  return  start_time;
}


/* find the cost function  F(.,.) of removing or adding an action */

float
dg_action_cost (neighb_list neighb_act)
{
  register int temp1, k, unsat_facts = 0;
  int level, i, j = 0, k1, diff = 0, next_level=0, init_w, init_na, ord;
  register EfConn *act;
  auto float total, prec_par, excl_par, add_effect_par, temp = 0.0, prec = 0.0, eff;
  FctNode_list inf_fact;
  int el = 0, fact_pos, ind_level;
  auto float precond, mutex, effect, act_cost;	//  LM  
  node_cost loc_n_cost, best_prec_cost, best_eff_cost, best_mutex_cost;
  float init_cost;
  float time_Timed_Prec=-1.0;
  int future_timed_cost;
  int num_Timed_Prec=0;
  int supported_percondition_facts[MAX_GOALS];
  int num_supported_percondition_facts=0;
  int init_penalize_inconsistence_in_relaxed_plan=0;
  int cond1, cond2;

#ifdef __TEST_ITER__

   static int cfc_iter=0;  
   if(DEBUG4)     
     printf("\n\n\n\n #############ITERATION %d ",cfc_iter);
    cfc_iter++;
   
#endif

   if (GpG.derived_predicates && GpG.derived_pred_in_preconds) {
     if (!temp_dp_precs)
       temp_dp_precs = (int *)calloc(gnum_dp_conn, sizeof(int));
     memcpy(temp_dp_precs, vectlevel[neighb_act->act_level] -> gnum_dp_precs, gnum_dp_conn * sizeof(int));
   }  

  if(Hvar.estimate_time_facts==NULL) //Inizializzo  Hvar.estimate_time_facts
    Hvar.estimate_time_facts=(float *)calloc(gnum_ft_conn, sizeof (float));

  memset (Hvar.estimate_time_facts, 0, gnum_ft_conn * sizeof (float)); // Azzero Hvar.estimate_time_facts

 

  precond = mutex = effect = act_cost = 0.0;	//  LM 
  Hvar.cost_actions_define_cost = 0.0;
  Hvar.time_actions_define_cost = 0.0;

  // resetto variabili per calcorare il costo delle precondizioni 
  Hvar.num_actions_define_cost = 0;
  Hvar.num_facts_define_cost = 0;
  Hvar.weight_facts_define_cost = 0.0;
  Hvar.timed_facts_define_cost = 0.0;
  
  reset_bitarray (Hvar.bit_vect_facts, gnum_ft_block);
  reset_bitarray (Hvar.bit_vect_actions, gnum_ef_block);
  reset_bitarray (Hvar.threated_bit_vect_facts, gnum_ft_block);
 
 
  best_prec_cost.weight = 0.0;

  best_prec_cost.act_cost = 0.0;

  best_prec_cost.act_time = 0.0;

  best_mutex_cost.weight = 0.0;
 
  best_mutex_cost.act_cost = 0.0;

  best_mutex_cost.act_time = 0.0;


  best_eff_cost.weight = 0.0;

  best_eff_cost.act_cost = 0.0;

  best_eff_cost.act_time = 0.0;


  local_search.ls_continue = TRUE;

  local_search.apply_stop_in_relaxed_plan=TRUE;

  level = neighb_act->act_level;
  act = &gef_conn[neighb_act->act_pos];


  loc_n_cost.weight = 0.0;
  
  loc_n_cost.act_cost = 0.0;
  
  loc_n_cost.act_time = 0.0;
  
  reset_supported_preconds();


  memcpy(Hvar.initial_relaxed_bit_vect_facts, vectlevel[level] -> fact_vect, gnum_ft_block * sizeof(int));

 
  if (neighb_act->constraint_type == C_T_REMOVE_ACTION)
        memcpy(Hvar.relaxed_bit_vect_preconds, vectlevel[level+1] -> prec_vect, gnum_ft_block * sizeof(int));
  else
    memcpy(Hvar.relaxed_bit_vect_preconds, vectlevel[level] -> prec_vect, gnum_ft_block * sizeof(int));

   

#ifdef __TEST__

  /*  if(neighb_act->constraint_type==C_T_REMOVE_ACTION ) 
     { 
     MSG_ERROR("  max_action_cost; debug me please"); 
     exit(0); 
     } 
   */
  printf("\n\n\n ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n MAX ACTION COST level %d action %s duration %f",
     level, print_op_name_string (act->position, temp_name),
     get_action_time (neighb_act->act_pos, level));

  check_plan (GpG.curr_plan_length);
#endif

  total = 0.0;


  if (GpG.lm_multilevel) { 
    local_search.lamda_prec=vectlevel[level]->lambda_prec[act->position];
    local_search.lamda_me=vectlevel[level]->lambda_me[act->position];
  }
  
  else {
    local_search.lamda_prec = act->lamda_prec;	// Variabili utilizzare per decidere se interrompere la fase di calcolo del costo delle precondizioni e mutex 
    local_search.lamda_me = act->lamda_me;
  }



   if(DEBUG5)
     print_act_eff_prec(neighb_act->act_pos, neighb_act->act_level);


  /* Define the alpha, beta, gamma coefficents of F() to  
     remove the action act from the action subgraph */

  //  infAction = act->inf_ptr;  
  if (neighb_act->constraint_type == C_T_REMOVE_ACTION)
    {				/* ... became unused */

      neighb_act->cost.act_cost = 0.0;
      neighb_act->cost.act_time = 0.0;
      neighb_act->cost.timed_fa = 0.0;

      if (GpG.maximize_plan || GpG.H_positive_benefits)
	{
	  /* Si considerano i benefici tratti dalla rimozione dell'azione A. 
	     Se rimuovo A il piano poi costa di meno. */

	  Hvar.cost_actions_define_cost -= get_action_cost(neighb_act->act_pos, neighb_act->act_level, NULL);

	  neighb_act->cost.act_cost -= get_action_cost(neighb_act->act_pos, neighb_act->act_level, NULL);

	  Hvar.num_actions_define_cost += 1;
	}

      prec_par = GpG.used_prec_par;
      excl_par = GpG.used_excl_par;
      add_effect_par = GpG.used_add_effect_par;
      Hvar.temp_removed_act = neighb_act->act_pos;

    }
  /*define the alpha, beta, gamma coefficents of F() for  
     add the action act from the action subgraph */
  else
    {				/* ... became used */


      neighb_act->cost.act_cost = 0.0;	//get_action_cost(neighb_act->act_pos,NULL);
      neighb_act->cost.act_time = 0.0;
      neighb_act->cost.timed_fa = 0.0;

      prec_par = GpG.prec_par;
      excl_par = GpG.excl_par;
      add_effect_par = GpG.add_effect_par;

      Hvar.temp_removed_act = -1;

      if (GpG.temporal_plan)
        for (ind_level = level - 1; ind_level >= 0; ind_level--)
          {
            if (vectlevel[ind_level]->action.w_is_used <= 0)
              continue;

            if (check_mutex_action (act->position, ind_level) >= 0 )
	      {
              if (GpG.constraint_type <= 1) /* Il vincolo di ordinamento tra azioni mutex e' sempre di tipo piu' restrittivo */
                {
                  if (best_prec_cost.act_time < GET_ACTION_OF_LEVEL(ind_level)->time_f)
                    best_prec_cost.act_time = GET_ACTION_OF_LEVEL(ind_level)->time_f;
                }
              else /* Vincoli di ordinamento avanzati */
                { /* Stabilisce il tipo di vincolo tra l'azione act e l'azione "GET_ACTION__OF_LEVEL(ind_level)" noto che "GET_ACTION__OF_LEVEL(ind_level)" si trova a un livello inferiore rispetto a "act"  */
		  
                  ord = Econstraint_type(GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level, act->position, -1 );
		  
                  if (ord == EA_SB) // l'azione  "act" deve iniziare dopo la fine dell'azione "GET_ACTION__OF_LEVEL(ind_level)" 
                    {
                      if (best_prec_cost.act_time < GET_ACTION_OF_LEVEL(ind_level)->time_f)
                        best_prec_cost.act_time = GET_ACTION_OF_LEVEL(ind_level)->time_f;
                    }
                  else
                    {
                      if (ord == EA_EB) // l'azione "act"  deve finire dopo la fine di "GET_ACTION__OF_LEVEL(ind_level)" 
                        {
                          if (best_prec_cost.act_time < GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (act->position, level) )
                            best_prec_cost.act_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (act->position, level);
                        }
                      else
                        if (ord == SA_SB) // l'azione "act" deve iniziare dopo l'inizio di "GET_ACTION__OF_LEVEL(ind_level)" 
                          {
                            if (best_prec_cost.act_time < GET_ACTION_OF_LEVEL (ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level) )
                              best_prec_cost.act_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level);
                          }
                        else
                          {
                            if (ord == SA_EB) // l'azione "act" deve finire dopo l'inizio di "GET_ACTION__OF_LEVEL(ind_level)" 
                              {
                                if (best_prec_cost.act_time < GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level)  - get_action_time (act->position, level) )
                                      best_prec_cost.act_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level) - get_action_time (act->position, level);
                              }
                            else
                             {
                                if (ord == EA_EB__SA_SB) // l'azione "act" e' sovrapposta ad "GET_ACTION__OF_LEVEL(ind_level)" 
                                  {
                                    if( get_action_time (act->position, level) < get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level))
                                      {
                                        // l'azione "act"  deve finire dopo la fine di "GET_ACTION__OF_LEVEL(ind_level)" 
                                        if (best_prec_cost.act_time < GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (act->position, level) )
                                          best_prec_cost.act_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (act->position, level);
                                      }
                                    else // l'azione "act" deve iniziare dopo l'inizio di "GET_ACTION__OF_LEVEL(ind_level)" 
                                      {
                                        if (best_prec_cost.act_time < GET_ACTION_OF_LEVEL (ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level) )
                                          best_prec_cost.act_time = GET_ACTION_OF_LEVEL(ind_level)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(ind_level), ind_level);

                                      }
                                  }
                              }
                          }
                    }
                }
	      }
	  }
    }


  if (DEBUG4)
    {
      if (DEBUG5)
	printf ("\n\nEvalutate action");
       printf ("\nDG_ACTION Act: %s, level %d\n  ",
	      print_op_name_string (act->position, temp_name), level);

    }



  if (neighb_act->constraint_type == C_T_INSERT_ACTION)
    {





      /* Inserisco in Hvar.supported_preconds le precondizioni non supportate */


      for (prec = 0.0, diff = 0, j = 0;
	   j < gef_conn[act->position].num_PC && local_search.ls_continue;
	   j++)
	{ 
	  el = gef_conn[act->position].PC[j];

	  if (el>=0 && is_fact_supported_in_relaxed_plan (el, level))
	    {
	      
	      insert_supported_preconds(el);

	      supported_percondition_facts[num_supported_percondition_facts++]=el;
	      if(num_supported_percondition_facts>=MAX_GOALS)
		{
		  printf ("\n\nlpg: increase MAX_GOALS( preset value: %d )",MAX_GOALS);
		  exit(0);
		}

	    }

	}


      if (gef_conn[act->position].sf != NULL && local_search.ls_continue)
	{
	  for (j = 0;
	       j < gef_conn[act->position].sf->num_PC_overall
		 && local_search.ls_continue; j++)
	    {
	      el = gef_conn[act->position].sf->PC_overall[j];

	      if (is_fact_in_additive_effects_start (act->position, el))
		continue;
	      if (el>=0 && is_fact_supported_in_relaxed_plan (el, level))
		{
	      
		  insert_supported_preconds(el);
	       
		  supported_percondition_facts[num_supported_percondition_facts++]=el;
		  if(num_supported_percondition_facts>=MAX_GOALS)
		    {
		      printf ("\n\nlpg: increase MAX_GOALS( preset value: %d )",MAX_GOALS);
		      exit(0);
		    }

		}

	    }


	  // precondizioni at_end
	  for (j = 0; j < gef_conn[act->position].sf->num_PC_end && local_search.ls_continue; j++)
	    {
	      el = gef_conn[act->position].sf->PC_end[j];


	      if (is_fact_in_additive_effects_start (act->position, el))
		continue;


	      if (el>=0 && is_fact_supported_in_relaxed_plan (el, level))
		{
	      
		  insert_supported_preconds(el);
	       
		  supported_percondition_facts[num_supported_percondition_facts++]=el;
		  if(num_supported_percondition_facts>=MAX_GOALS)
		    {
		      printf ("\n\nlpg: increase MAX_GOALS( preset value: %d )",MAX_GOALS);
		      exit(0);
		    }

		}
	    }
	}


  /* Counts unsatisfied Preconditions */

      unsat_facts = 0;
      for (prec = 0.0, diff = 0, j = 0;
	   j < gef_conn[act->position].num_PC && local_search.ls_continue;
	   j++)
	{
	  el = gef_conn[act->position].PC[j];

	  if (CHECK_FACT_POS (el, level))
	    {
	      if (DEBUG4)
		{
		  printf ("\n\n %d +++++ DG_MAX_COST Prec_start  Act %s",
			  ++diff, print_op_name_string (act->position,
							temp_name));
		  printf ("\n  fact %s\n", print_ft_name_string (el, temp_name));
		}


	      loc_n_cost.weight = 0.0;

	      loc_n_cost.act_cost = 0.0;

	      loc_n_cost.act_time = 0.0;



	      //Costo per rendere vere le precondizioni 

	      if (el < 0)
		{
		  if (is_num_prec_satisfied_in_common_level (el))
		    continue;
		}
	      else if (is_fact_supported_in_relaxed_plan (el, level))
		{
		  #ifdef __TEST__
		  if (DEBUG4)
		    printf ("\n Level %d Supported fact %s - 1", level,
			    print_ft_name_string (el, temp_name));
		  #endif  

		  inf_fact = CONVERT_FACT_TO_NODE (el, level);

		 

		  if (GpG.temporal_plan)
		    {
		      if (best_prec_cost.act_time < inf_fact->time_f)
			{
			  best_prec_cost.act_time = inf_fact->time_f;

#ifdef __TEST__
			  printf
			    ("\n Max Time prec. supported fact %d time %.2f ",
			     el, inf_fact->time_f);
			  print_ft_name (el);
#endif

			  if (Hvar.time_actions_define_cost <
			      best_prec_cost.act_time)
			    Hvar.time_actions_define_cost =
			      best_prec_cost.act_time;


			}

		    }


		  continue;
		}



	      if (el >= 0 && GpG.accurate_cost >= COMPUTE_DG_LIST_COST
		  && GET_BIT (Hvar.bit_vect_facts, el))
		{
#ifdef __TEST__
		  printf
		    ("\nFact %s already supported in COMPUTE_DG_LIST_COST, level %d",
		     print_ft_name_string (el, temp_name), level);
#endif
		  continue;
		}


	      /*
		loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		Azzero loc_n_cost
	      */
	      loc_n_cost.weight = 0.0;
	      loc_n_cost.act_cost = 0.0;
	      loc_n_cost.act_time = 0.0;
	      loc_n_cost.action=act->position;


	      temp = compute_relaxed_fact_cost (el, level, &loc_n_cost, level,  get_action_time (act->position, level));





	      if (DEBUG4)
		{
		  printf ("\n\n %d +++ END DG_MAX_COST Prec_start  Act %s ",
			  ++diff, print_op_name_string (act->position,
							temp_name));
		  printf
		    ("\n  fact %s, COST  weight %f cost %f time %f unsatisf_prec %d ",
		     print_ft_name_string (el, temp_name), loc_n_cost.weight,
		     loc_n_cost.act_cost, loc_n_cost.act_time, unsat_facts);
		}

	      
	      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
		{
		  prec += temp;

		  //		  best_prec_cost.weight += loc_n_cost.weight;

		  //		  best_prec_cost.act_cost += loc_n_cost.act_cost;

		  if (best_prec_cost.act_time < loc_n_cost.act_time
		      && loc_n_cost.act_time < MAX_COST)
		    best_prec_cost.act_time = loc_n_cost.act_time;


		}

	    }
#ifdef __TEST__
	  else
	    MSG_ERROR ("Max act cost precond");
#endif

	  if (Hvar.time_actions_define_cost < best_prec_cost.act_time)
	    Hvar.time_actions_define_cost = best_prec_cost.act_time;



	}


      //************************************************************************************************************* Saetti
      // precondizioni overall
      if (gef_conn[act->position].sf != NULL && local_search.ls_continue)
	{
	  for (j = 0;
	       j < gef_conn[act->position].sf->num_PC_overall
	       && local_search.ls_continue; j++)
	    {
	      el = gef_conn[act->position].sf->PC_overall[j];

	      if (is_fact_in_additive_effects_start (act->position, el))
		continue;

	      if (CHECK_FACT_POS (el, level))
		{
		  if (DEBUG4)
		    {
		      printf
			("\n\n %d +++++ DG_MAX_COST Prec_overall  Act %s",
			 ++diff, print_op_name_string (act->position,
						       temp_name));
		      printf ("\n  fact %s\n",
			      print_ft_name_string (el, temp_name));
		    }

		  loc_n_cost.weight = 0.0;

		  loc_n_cost.act_cost = 0.0;

		  loc_n_cost.act_time = 0.0;


		  //Costo per rendere vere le precondizioni 
		  if (el < 0)
		    {
		      if (is_num_prec_satisfied_in_common_level (el))
			continue;
		    }
		  else if ( is_fact_supported_in_relaxed_plan(el, level))
		    {
#ifdef __TEST__
		      printf ("\n Level %d Supported fact %s ", level,
			      print_ft_name_string (el, temp_name));
#endif

		      inf_fact = CONVERT_FACT_TO_NODE (el, level);

		      if (GpG.temporal_plan)
			{
			  if (best_prec_cost.act_time < inf_fact->time_f)
			    {
			      best_prec_cost.act_time = inf_fact->time_f;

#ifdef __TEST__
			      printf
				("\n Max Time prec. supported fact %d time %.2f ",
				 el, inf_fact->time_f);
			      print_ft_name (el);
#endif
			    }


			  if (Hvar.time_actions_define_cost <
			      best_prec_cost.act_time)
			    Hvar.time_actions_define_cost =
			      best_prec_cost.act_time;



			}

		      continue;
		    }



		  if (el >= 0 && GpG.accurate_cost >= COMPUTE_DG_LIST_COST
		      && GET_BIT (Hvar.bit_vect_facts, el))
		    {
#ifdef __TEST__
		      printf
			("\nFact %s already supported in COMPUTE_DG_LIST_COST prec OVER ALL, level %d",
			 print_ft_name_string (el, temp_name), level);
#endif
		      continue;
		    }

		  /*
		    loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		    Azzero loc_n_cost
		  */
		  loc_n_cost.weight = 0.0;
		  loc_n_cost.act_cost = 0.0;
		  loc_n_cost.act_time = 0.0;
		  loc_n_cost.action=act->position;



		  temp =
		    compute_relaxed_fact_cost (el, level, &loc_n_cost, level, get_action_time (act->position, level));



		  if (DEBUG4)
		    {
		      printf
			("\n\n %d +++ END DG_MAX_COST Prec_overall  Act %s ",
			 ++diff, print_op_name_string (act->position,
						       temp_name));
		      printf
			("\n  fact %s, COST  weight %f cost %f time %f unsatisf_prec %d ",
			 print_ft_name_string (el, temp_name),
			 loc_n_cost.weight, loc_n_cost.act_cost,
			 loc_n_cost.act_time, unsat_facts);


		    }
		  
		  if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
		    {
		      prec += temp;

		      //		      best_prec_cost.weight += loc_n_cost.weight;

		      //		      best_prec_cost.act_cost += loc_n_cost.act_cost;

		      if (best_prec_cost.act_time < loc_n_cost.act_time
			  && loc_n_cost.act_time < MAX_COST)
			best_prec_cost.act_time = loc_n_cost.act_time;


		    }

		}

#ifdef __TEST__
	      else
		MSG_ERROR ("Max act cost precond");
#endif




	      if (Hvar.time_actions_define_cost < best_prec_cost.act_time)
		Hvar.time_actions_define_cost = best_prec_cost.act_time;



	    }

	  // precondizioni at_end
	  for (j = 0; j < gef_conn[act->position].sf->num_PC_end && local_search.ls_continue; j++)
	    {
	      el = gef_conn[act->position].sf->PC_end[j];

	      //      if(el<0)
	      //        continue; //LAZZA


	      if (is_fact_in_additive_effects_start (act->position, el))
		continue;


	      if (CHECK_FACT_POS (el, level))
		{
		  if (DEBUG4)
		    {
		      printf ("\n\n %d +++++ DG_MAX_COST Prec_end  Act %s",
			      ++diff, print_op_name_string (act->position,
							    temp_name));
		      printf ("\n  fact %s\n",
			      print_ft_name_string (el, temp_name));
		    }

		  loc_n_cost.weight = 0.0;

		  loc_n_cost.act_cost = 0.0;

		  loc_n_cost.act_time = 0.0;


		  //Costo per rendere vere le precondizioni 

		  if (el < 0)
		    {
		      if (is_num_prec_satisfied_in_common_level (el))
			continue;
		    }
		  else if (is_fact_supported_in_relaxed_plan (el, level))
		    {
#ifdef __TEST__
		      printf ("\n Level %d Supported fact %s ", level,
			      print_ft_name_string (el, temp_name));
#endif

		      inf_fact = CONVERT_FACT_TO_NODE (el, level);
		     

		      if (GpG.temporal_plan)
			{
			  if (best_prec_cost.act_time < inf_fact->time_f - get_action_time (neighb_act->act_pos, level))
			    {
			      best_prec_cost.act_time = inf_fact->time_f - get_action_time (neighb_act->act_pos, level);

#ifdef __TEST__
			      printf
				("\n Max Time prec. supported fact %d time %.2f ",
				 el, inf_fact->time_f);
			      print_ft_name (el);
#endif
			    }


			  if (Hvar.time_actions_define_cost <
			      best_prec_cost.act_time)
			    Hvar.time_actions_define_cost =
			      best_prec_cost.act_time;


			}


		      continue;
		    }



		  if (el >= 0 && GpG.accurate_cost >= COMPUTE_DG_LIST_COST
		      && GET_BIT (Hvar.bit_vect_facts, el))
		    {
#ifdef __TEST__
		      printf
			("\nFact %s already supported in COMPUTE_DG_LIST_COST, level %d",
			 print_ft_name_string (el, temp_name), level);
#endif
		      continue;
		    }

		  /*
		    loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		    Azzero loc_n_cost
		  */
		  loc_n_cost.weight = 0.0;
		  loc_n_cost.act_cost = 0.0;
		  loc_n_cost.act_time = 0.0;
		  loc_n_cost.action=act->position;


		  temp = compute_relaxed_fact_cost (el, level, &loc_n_cost, level, get_action_time (act->position, level));


		  if (DEBUG4)
		    {
		      printf ("\n\n %d +++ END DG_MAX_COST Prec_end  Act %s ",
			      ++diff, print_op_name_string (act->position,
							    temp_name));
		      printf
			("\n  fact %s, COST  weight %f cost %f time %f unsatisf_prec %d ",
			 print_ft_name_string (el, temp_name),
			 loc_n_cost.weight, loc_n_cost.act_cost,
			 loc_n_cost.act_time, unsat_facts);


		    }

		  if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
		    {
		      prec += temp;

		      //		      best_prec_cost.weight += loc_n_cost.weight;

		      //		      best_prec_cost.act_cost += loc_n_cost.act_cost;

		      if (best_prec_cost.act_time < loc_n_cost.act_time - get_action_time (neighb_act->act_pos, level) && loc_n_cost.act_time < MAX_COST)
			best_prec_cost.act_time = loc_n_cost.act_time - get_action_time (neighb_act->act_pos, level);


		    }

		}

#ifdef __TEST__
	      else
		MSG_ERROR ("Max act cost precond");
#endif


	      if (Hvar.time_actions_define_cost < best_prec_cost.act_time)
		Hvar.time_actions_define_cost = best_prec_cost.act_time;



	    }
	}







      //*********************************************************************************************************************** Saetti end


      total = prec_par * prec;

      precond = local_search.lamda_prec * total;


      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
	{

	  if (GpG.lagrange_multipl)
	    best_prec_cost.weight = (Hvar.weight_facts_define_cost + Hvar.num_actions_define_cost) * local_search.lamda_prec;
	  else
	    best_prec_cost.weight = Hvar.weight_facts_define_cost + Hvar.num_actions_define_cost;

	  best_prec_cost.act_cost = Hvar.cost_actions_define_cost;


	  best_prec_cost.num_actions = Hvar.num_actions_define_cost;
	  //  best_prec_cost.act_time += loc_n_cost.act_time; 
	}
      if (DEBUG4)
	{
 	  printf ("  Temp Num. P: %f weight %.2f ", prec,
		  best_prec_cost.weight);

	  if (DEBUG5)
	    printf ("\n\n<< Evalutate precondition END");
	}

      update_supported_precond_for_action(act->position);

    


  /* Counts the number of ME actions with the current one */


    if( local_search.ls_continue != 0)
    {
      next_level=level+1;

      //#ifdef __TEST_REACH__
      if(GpG.verify_negative_numeric_effects)
	{
	  negative_numeric_effects(neighb_act, level,  &best_eff_cost);
	}
      //#endif


      init_w = Hvar.weight_facts_define_cost;
      init_na = Hvar.num_actions_define_cost;
      init_cost = Hvar.cost_actions_define_cost;

      if (DEBUG4)
	{
	  printf ("\n\n %d +++++  DG_MAX_COST Mutex  Act :", ++diff);
	  print_op_name (act->position);
	}

      if(GpG.evaluate_threated_supported_preconds_of_neighb_action==TRUE)
	{

	  if(DEBUG5)
	    printf("\n\n START evaluate_threated_supported_preconds_of_neighb_action, action %d --  %s ",act->position, print_op_name_string( act->position, temp_name));
	  // Valuto le precondizione dell'elem del vicinato che vengono minacciate

	  //Definisco nuovo stato iniziale calcolo piano rilassato considerando  mutex azioni piano rilassato 
	  for(i=0;  i < gnum_ft_block; i++)
	    Hvar.initial_relaxed_bit_vect_facts[i] &= (~Hvar.threated_bit_vect_facts[i]);

	  for(i=0; i< num_supported_percondition_facts; i++)
	    {
	      // Il fatto e' una delle precondizioni vere dell'elem del vicinato ma viene minacciato da una delle azioni del piano rilassato e non piu' resa vera

	      if(DEBUG5)
		printf("\n Evaluate %d -- %s",supported_percondition_facts[i], print_ft_name_string(supported_percondition_facts[i], temp_name));

	      

	      if(GET_BIT(Hvar.threated_bit_vect_facts, supported_percondition_facts[i]) && !GET_BIT(Hvar.bit_vect_facts, supported_percondition_facts[i]))
	      {
		   loc_n_cost.weight = 0.0;
		   loc_n_cost.act_cost = 0.0;
		   loc_n_cost.act_time = 0.0;
		   loc_n_cost.action=act->position;


		   temp = compute_relaxed_fact_cost (supported_percondition_facts[i], level, &loc_n_cost, level,  get_action_time (act->position, level));


	      
	      }

	    }

	  if(DEBUG5)
	    printf("\n\n END evaluate_threated_supported_preconds_of_neighb_action ");
	}



      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
	{

#ifdef __TEST__
	  printf ("\n\n\n  '''''''''' SET effect of action %d : ",
		  act->position);
	  print_op_name (act->position);
#endif




	  if (gef_conn[act->position].sf)
	    for (j = 0; j < gef_conn[act->position].sf->num_A_start; j++)
	      {
		el = gef_conn[act->position].sf->A_start[j];
		if (el < 0)
		  {
		    // Applico  eff in common level
		    apply_numeric_effect_in_common_level (el,1);
		    continue;	// LAZZA
		  }

		if (is_fact_in_delete_effects (act->position, el))
		  continue;

		if (GpG.derived_pred_in_preconds)
		  calc_new_derived_predicates_from(el, temp_dp_precs, Hvar.bit_vect_facts, ADD_FACT, NULL);

		SET_BIT (Hvar.bit_vect_facts, el);

#ifdef __TEST__
		printf ("\n ''''FACT %d : ", el);
		print_ft_name (el);
#endif
	      }

	  if(GpG.reset_extended_unsupported_facts==2  || GpG.reset_extended_unsupported_facts==3)
	    {
	      remove_action_mutex_facts_in_bitvect(neighb_act->act_pos,Hvar.initial_relaxed_bit_vect_facts);

	      if(GpG.reset_extended_unsupported_facts==3)
		remove_action_mutex_facts_in_bitvect(neighb_act->act_pos,Hvar.bit_vect_facts);

	    }


	  for (j = 0; j < gef_conn[act->position].num_A; j++)
	    {
	      el = gef_conn[act->position].A[j];
	      if (el < 0)
		{
		  // Applico  eff in common level, 1 volta (l'azione stessa)
		 apply_numeric_effect_in_common_level (el,1);
		  continue;	// LAZZA
		}

	      if (GpG.derived_pred_in_preconds)
		calc_new_derived_predicates_from(el, temp_dp_precs, Hvar.bit_vect_facts, ADD_FACT, NULL);

	      SET_BIT (Hvar.bit_vect_facts, el);

#ifdef __TEST__
	      printf ("\n ''''FACT %d : ", el);
	      print_ft_name (el);
#endif
	    }




	}




      // Definisco il costo per rendere nuovamente veri i fatti BOOLEANI che vengono invalidati dall'azione e sono precondizione di una azione successiva       
      temp = 0.0;


      init_penalize_inconsistence_in_relaxed_plan=GpG.penalize_inconsistence_in_relaxed_plan;
      GpG.penalize_inconsistence_in_relaxed_plan=0;

 
 
	  for (i = 0, j = 0; j < gnum_ft_conn; i++, j += 32)
	    {

	      temp1 = vectlevel[level]->fact_vect[i] & (Hvar.relaxed_bit_vect_preconds[i]);// |  Hvar.supported_bit_vect_preconds[i]);
	      
	      if( Hvar.supported_bit_vect_preconds[i]!=0)
		printf("\n Err search step %d ",GpG.count_num_try);

	      //  temp1 = act->ft_exclusive_vect[i] & vectlevel[level]->prec_vect[i] & (vectlevel[level]->fact_vect[i]);


	      k = 32;
	      while (temp1)
		{
		  k--;
		  if (temp1 & FIRST_1) 
		    {

		      k1 = j + k;
		      // if(GpG.mutex_and_additive_effects || is_fact_in_additive_effects( act->position ,k1)==FALSE)
		      //    if( GET_BIT( act->ft_exclusive_vect, (k1)) || (GpG.supported_preconds_evaluation && GET_BIT(Hvar.threated_bit_vect_facts , (k1)) && !GET_BIT(Hvar.bit_vect_facts , (k1)) ) )
		      if(GpG.no_mutex_with_additive_effects==FALSE)
			cond1=GET_BIT( act->ft_exclusive_vect, (k1));
		      else
			cond1=GET_BIT( act->ft_exclusive_vect, (k1))&& is_fact_in_additive_effects( act->position ,k1)==FALSE;

		      if(cond1==FALSE)
			cond2=(GpG.supported_preconds_evaluation && GET_BIT(Hvar.threated_bit_vect_facts , (k1)) && !GET_BIT(Hvar.bit_vect_facts , (k1)) );
		      else
			cond2=FALSE;

		      if(cond1 || cond2)
		      {
		      
#ifdef __TEST__
		      if (DEBUG6)
			{
			  printf ("\n\n\n %d ------------------FACT : %d  ",
				  diff, k1);
			  print_ft_name (k1);

			}
#endif

		      /*
			loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
			Azzero loc_n_cost
		      */
		      loc_n_cost.weight = 0.0;
		      loc_n_cost.act_cost = 0.0;
		      loc_n_cost.act_time = best_prec_cost.act_time+get_action_time (neighb_act->act_pos, level);

		      loc_n_cost.options=3;

		      temp +=
			compute_relaxed_fact_cost (k1, level, &loc_n_cost, level, MAXFLOAT);



		      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
			{
			  prec += temp;

			  best_mutex_cost.weight += loc_n_cost.weight;

			  best_mutex_cost.act_cost += loc_n_cost.act_cost;

			  if (best_mutex_cost.act_time < loc_n_cost.act_time
			      && loc_n_cost.act_time < MAX_COST)
			    best_mutex_cost.act_time = loc_n_cost.act_time;
			  //SISTEMARE           

			}

		      if (DEBUG4)
			{
			  printf ("\n\n %d +++ END DG_MAX_COST Mutex  Act %s",
				  ++diff, print_op_name_string (act->position,
								temp_name));
			  printf
			    ("\n  fact %s, COST  weight %f cost %f time %f",
			     print_ft_name_string (k1, temp_name),
			     loc_n_cost.weight, loc_n_cost.act_cost,
			     loc_n_cost.act_time);
			}
		      }
		    
		   else
		    if(DEBUG5)
		      printf("\n Fact in additive effects not considered %d - %s ", j+k,print_ft_name_string(j+k,temp_name)); 
		   }
		  temp1 <<= 1;
		}		// while

	    }	// for



	  GpG.penalize_inconsistence_in_relaxed_plan=init_penalize_inconsistence_in_relaxed_plan;


	  mutex = excl_par * best_mutex_cost.weight;	//  LM 
	  total += mutex;
	  mutex *= local_search.lamda_me;
	

      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
	{

	  if (GpG.lagrange_multipl)
	    best_mutex_cost.weight =
	      (Hvar.weight_facts_define_cost - init_w +
	       Hvar.num_actions_define_cost - init_na) *  local_search.lamda_me;
	  else
	    best_mutex_cost.weight =
	      Hvar.weight_facts_define_cost - init_w +
	      Hvar.num_actions_define_cost - init_na;

	  best_mutex_cost.act_cost =
	    Hvar.cost_actions_define_cost - init_cost;

	}

#ifdef __TEST__
      if (DEBUG3)
	{
	  printf
	    ("\n----- %d COMPUTE DG MAX COST END MUTEX  COST  weight %f cost %f time %f, total %.2f mutex %.2f  ACTION :",
	     ++diff, best_mutex_cost.weight, best_mutex_cost.act_cost,
	     best_mutex_cost.act_time, total, mutex);

	  print_op_name (act->position);
	}
#endif

    }
  




  if (DEBUG4)
    {
      printf ("  Temp  M.E.: %f", temp);

      if (DEBUG5)
	printf ("\n\n<< Evalutate mutex END");

    }

    
  if( GpG.consider_relaxed_plan_for_inconsistences==TRUE )
    {
      // Valuto vatti che servono nei piani rilassati delle inconsistenze future e vengono invalidati
      verify_supported_fact_in_relaxed_plan_for_inconsistences(neighb_act->act_pos, level, Hvar.bit_vect_facts);
    }


   }
  else // Evaluate Act remove C_T_REMOVE_ACTION
    {


  /* define the cost of Add_effect critics nodes */
  /* a fact is a true critic node if it is precondition of almost an action */
  /* of the next level and it's supported from only one action */

  /* a fact is a false critic node if it is precondition of almost an action */
  /* of the next level and it's not supported */



      init_w = Hvar.weight_facts_define_cost;
      init_na = Hvar.num_actions_define_cost;
      init_cost = Hvar.cost_actions_define_cost;

      local_search.lamda_prec = MIN_POS_S_S;


      next_level = level + 1;

       

      unsat_facts = 0;

#ifdef TEST_GR
	  printf ("\n MAX action cost level %d", level);
	  check_plan (GpG.curr_plan_length);
#endif

	  //	  remove_temp_action (neighb_act->act_pos, neighb_act->act_level);	// Rimuovo temporaneamente l'azione per calcolare il costo di rendere veri gli effetti additivi critici 









 /* Inserisco in Hvar.supported_preconds le precondizioni non supportate */



	  // Effetti at start
	  if (gef_conn[neighb_act->act_pos].sf != NULL)
	    {
	      for (i = 0;
		   i < gef_conn[neighb_act->act_pos].sf->num_A_start
		     && local_search.ls_continue; i++)
		{
		  fact_pos = gef_conn[neighb_act->act_pos].sf->A_start[i];

		  if (is_fact_in_delete_effects (neighb_act->act_pos, fact_pos))
		    continue;

		  if (fact_pos < 0)
		    continue;

	      
		  if (is_fact_supported_in_relaxed_plan (fact_pos, level))
		    insert_supported_preconds(el);

		}
	    }


	  for (i = 0;
	       i < gef_conn[neighb_act->act_pos].num_A
		 && local_search.ls_continue; i++)
	    {
	  
	      fact_pos = gef_conn[neighb_act->act_pos].A[i];

	      // da sistemare LAZZA  
	      if (fact_pos < 0)
		continue;

	      if(is_fact_supported_in_relaxed_plan (fact_pos,level))
		insert_supported_preconds(el);

	    }


	  //#ifdef __TEST_REACH__	  

     if(GpG.verify_action_remotion_negative_numeric_effects)
	{

	  action_remotion_negative_numeric_effects(neighb_act, level,  &best_eff_cost);
	
	}
     //#endif
	
      eff=0.0;
      next_level = level + 1;



    
      for (i = 0;
	   i < gef_conn[neighb_act->act_pos].num_A
	   && local_search.ls_continue; i++)
	{

	  fact_pos = gef_conn[neighb_act->act_pos].A[i];

	  // da sistemare LAZZA  
	  if (fact_pos < 0)
	    continue;

	  loc_n_cost.weight = 0.0;
	  loc_n_cost.act_cost = 0.0;
	  loc_n_cost.act_time = 0.0;


	  if (fact_pos > 0)	// Determino il moltiplic di lagr con il valore piu' alto 
	    {
	      for (j = neighb_act->act_level; j < GpG.curr_plan_length; j++)
		if (CONVERT_FACT_TO_NODE (fact_pos, j)->w_is_used)	// il fatto e' precondizione della azione del corrispondente livello
		  break;

	      if (GET_ACTION_POSITION_OF_LEVEL (j) >= 0)
		{		
		  if (j==GpG.curr_plan_length) {
		    local_search.lamda_prec = MAX (local_search.lamda_prec,GpG.goal_lambda);
		  }
		  else {
		    if (GpG.lm_multilevel) 
		      local_search.lamda_prec = MAX (local_search.lamda_prec,vectlevel[j]->lambda_prec[GET_ACTION_POSITION_OF_LEVEL(j)]);
		    else
		      local_search.lamda_prec = MAX (local_search.lamda_prec,CONVERT_ACTION_TO_VERTEX (GET_ACTION_POSITION_OF_LEVEL(j))->lamda_prec);
		    
		  }
		}

	    }


	      if (CONVERT_FACT_TO_NODE (fact_pos, next_level)->w_is_true == 1
		  && CONVERT_FACT_TO_NODE (fact_pos, next_level)->w_is_goal)
		{
		  // Trovo il primo livello in cui questo fatto diventerebbe una precondizione non supportata 

		  if (FALSE)	// GPG2 DA RIVEDERE 
		    for (next_level = level + 1;
			 next_level <= GpG.curr_plan_length; next_level++)
		      if ((CONVERT_FACT_TO_NODE (fact_pos, next_level)->w_is_used))	// fatto precondizione dell'azione 
			break;

		  if (next_level > GpG.curr_plan_length)
		    {
#ifdef __TEST__
		      if (DEBUG3)
			MSG_ERROR ("Fact precondition of NO action");
#endif

		      continue;

		    }
#ifdef __TEST__
		  else if (DEBUG3)
		    {
		      if (GET_ACTION_POSITION_OF_LEVEL (next_level) >= 0)
			printf
			  ("\n ++++++++++++++++++++++++++++++++++Fact %s precondition of action %s at level %d",
			   print_ft_name_string (fact_pos, temp_name),
			   print_op_name_string (GET_ACTION_POSITION_OF_LEVEL
						 (next_level), temp_name),
			   next_level);
		      else
			printf
			  ("\n Fact %s precondition of no action  at level %d",
			   print_ft_name_string (fact_pos, temp_name),
			   next_level);
		    }

#endif

		  //#ifdef __TEST__ 
		  if (DEBUG4)
		    {
		      printf ("\n\n %d +++++* DG_MAX_COST End_eff  Act %s",
			      ++diff, print_op_name_string (act->position,
							    temp_name));
		      printf ("\n  fact %s\n",
			      print_ft_name_string (fact_pos, temp_name));
		    }
		  //#endif 


		  if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST
		      && GET_BIT (Hvar.bit_vect_facts, fact_pos))
		    {
		      //#ifdef __TEST__
		      if (DEBUG4)
			printf
			  ("\nFact %s already supported in COMPUTE_DG_LIST_COST, level %d",
			   print_ft_name_string (fact_pos, temp_name), level);
		      //#endif

		      continue;
		    }

		  if(is_fact_supported_in_relaxed_plan (fact_pos,level))
		    {

		      if (DEBUG5)
			printf
			  ("\nFact %s already supported in vectlevel, level %d",
			   print_ft_name_string (fact_pos, temp_name), level);


		      continue;

		    }
		     else
		      if (DEBUG5)
			printf
			  ("\nFact %s ** NOT already supported in vectlevel, level %d",
			   print_ft_name_string (fact_pos, temp_name), level);



		  
		  /*
		    loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		    Azzero loc_n_cost
		  */
		  loc_n_cost.weight = 0.0;
		  loc_n_cost.act_cost = 0.0;
		  loc_n_cost.act_time = 0.0;
		  loc_n_cost.action=act->position;
		
		  loc_n_cost.options=2; // Do not consider mutex relation number for this best action

		      		  
		  Hvar.initial_unsup_fact_of_relaxed_plan=fact_pos;

		  temp =
		    compute_relaxed_fact_cost (fact_pos, next_level, &loc_n_cost,
					   level, -get_action_time (act->position, level));


		  if(GpG.evaluate_mutex_for_action_remotion && local_search.ls_continue)
		    {
		      // realizzo mutex di best action nel piano rilassato

		      evaluate_mutex_in_relaxed_plan(loc_n_cost.best_action, level);
		    }


		  if( GpG.consider_relaxed_plan_for_inconsistences==TRUE && local_search.ls_continue )
		    { 
		      
		      // Valuto vatti che servono nei piani rilassati delle inconsistenze future e vengono invalidati
	  
		      // imposto action=-1 piche sto considerando rimozione
		      verify_supported_fact_in_relaxed_plan_for_inconsistences(loc_n_cost.best_action, level, Hvar.bit_vect_facts);
		    }
		      


		}

	  
	



	  if (DEBUG4)
	    {
	      printf ("\n\n %d +++ DG_MAX_COST End_eff  Act %s ", ++diff,
		      print_op_name_string (neighb_act->act_pos, temp_name));
	      printf ("\n  fact %s, COST  weight %f cost %f time %f",
		      print_ft_name_string (fact_pos, temp_name),
		      loc_n_cost.weight, loc_n_cost.act_cost,
		      loc_n_cost.act_time);
	    }


	  if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
	    {


	      best_eff_cost.act_cost += loc_n_cost.act_cost;

	      //      best_eff_cost.act_time += loc_n_cost.act_time; 

	      eff += temp;


	      if (best_eff_cost.act_time < loc_n_cost.act_time
		  && loc_n_cost.act_time < MAX_COST)
		best_eff_cost.act_time = loc_n_cost.act_time;

	      effect += temp * local_search.lamda_prec;

	    }
	  
	}




      //****************************************************************************************************** Saetti
      // Effetti at start
      if (gef_conn[neighb_act->act_pos].sf != NULL)
	{
	  for (i = 0;
	       i < gef_conn[neighb_act->act_pos].sf->num_A_start
	       && local_search.ls_continue; i++)
	    {
	      fact_pos = gef_conn[neighb_act->act_pos].sf->A_start[i];

	      if (is_fact_in_delete_effects (neighb_act->act_pos, fact_pos))
		continue;


	      // da sistemare LAZZA  
	      if (fact_pos < 0)
		continue;

	      loc_n_cost.weight = 0.0;
	      loc_n_cost.act_cost = 0.0;
	      loc_n_cost.act_time = 0.0;



	      //      local_search.lamda_prec=CONVERT_FACT_TO_VERTEX(fact_pos)->lamda_prec; 

	      if (neighb_act->constraint_type == C_T_REMOVE_ACTION)
		{

		  if (CONVERT_FACT_TO_NODE (fact_pos, next_level)->
		      w_is_true == 1
		      && CONVERT_FACT_TO_NODE (fact_pos,
						 next_level)->w_is_goal)
		    {
		      // Trovo il primo livello in cui questo fatto diventerebbe una precondizione non supportata 

		      if (FALSE)	// GPG2 DA RIVEDERE 
			for (next_level = level + 1;
			     next_level <= GpG.curr_plan_length; next_level++)
			  if ((CONVERT_FACT_TO_NODE (fact_pos, next_level)->w_is_used))	// fatto precondizione dell'azione 
			    break;

		      if (next_level > GpG.curr_plan_length)
			{
			  if (DEBUG3)
			    MSG_ERROR ("Fact precondition of NO action");
			  continue;

			}
#ifdef __TEST__
		      else if (DEBUG3)
			{
			  if (GET_ACTION_POSITION_OF_LEVEL (next_level) >= 0)
			    printf
			      ("\n ++++++++++++++++++++++++++++++++++Fact %s precondition of action %s at level %d",
			       print_ft_name_string (fact_pos, temp_name),
			       print_op_name_string
			       (GET_ACTION_POSITION_OF_LEVEL (next_level),
				temp_name), next_level);
			  else
			    printf
			      ("\n Fact %s precondition of no action  at level %d",
			       print_ft_name_string (fact_pos, temp_name),
			       next_level);
			}

#endif


		      //#ifdef __TEST__ 
		      if (DEBUG4)
			{
			  printf
			    ("\n\n %d +++++ DG_MAX_COST Start_eff  Act %s ",
			     ++diff, print_op_name_string (act->position,
							   temp_name));
			  printf ("\n  fact %s\n",
				  print_ft_name_string (fact_pos, temp_name));

			}
		      //#endif 






		      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST
			  && GET_BIT (Hvar.bit_vect_facts, fact_pos))
			{
			  //#ifdef __TEST__
			  if (DEBUG4)
			    printf
			      ("\nFact %s already supported in COMPUTE_DG_LIST_COST, level %d",
			       print_ft_name_string (el, temp_name), level);
			  //#endif

			  continue;
			}
		      
		      if (is_fact_supported_in_relaxed_plan (fact_pos, level))
			{
			  //#ifdef __TEST__
			  if (DEBUG4)
			    printf ("\n  Supported fact %s, level %d",
				    print_ft_name_string (fact_pos,
							  temp_name),
				    level);
			  //#endif             


			  insert_supported_preconds(el);

			  continue;
			}
		      /*
			loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
			Azzero loc_n_cost
		      */
		      loc_n_cost.weight = 0.0;
		      loc_n_cost.act_cost = 0.0;
		      loc_n_cost.act_time = 0.0;
		      loc_n_cost.action=act->position;


		      loc_n_cost.options=2; // Do not consider mutex relation number for this best action
		    
		      Hvar.initial_unsup_fact_of_relaxed_plan=fact_pos;
		      

		      temp =
			compute_relaxed_fact_cost (fact_pos, level, &loc_n_cost,
					       level,-get_action_time (act->position, level));



		      if(GpG.evaluate_mutex_for_action_remotion && local_search.ls_continue)
			{
			  // realizzo mutex di best action nel piano rilassato
			  
			  evaluate_mutex_in_relaxed_plan(loc_n_cost.best_action, level);
			}
		      
		      if( GpG.consider_relaxed_plan_for_inconsistences==TRUE && local_search.ls_continue )
			{ 
			
			  // Valuto vatti che servono nei piani rilassati delle inconsistenze future e vengono invalidati
	  
			  // imposto action=-1 piche sto considerando rimozione
			  verify_supported_fact_in_relaxed_plan_for_inconsistences(loc_n_cost.best_action, level, Hvar.bit_vect_facts);
			}
		      




		    }

		}


	      if (DEBUG4)
		{
		  printf ("\n\n %d +++++ DG_MAX_COST Start_eff  Act %s ",
			  ++diff, print_op_name_string (neighb_act->act_pos,
							temp_name));
		  printf ("\n  fact %s, COST  weight %f cost %f time %f",
			  print_ft_name_string (fact_pos, temp_name),
			  loc_n_cost.weight, loc_n_cost.act_cost,
			  loc_n_cost.act_time);
		}

	      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
		{


		  best_eff_cost.act_cost += loc_n_cost.act_cost;

		  // IV????    best_eff_cost.act_time += loc_n_cost.act_time; 

		  eff += temp;


		  if (best_eff_cost.act_time < loc_n_cost.act_time
		      && loc_n_cost.act_time < MAX_COST)
		    best_eff_cost.act_time = loc_n_cost.act_time;

		  effect += temp * local_search.lamda_prec;

		}

	    }


	}
      //****************************************************************************************************** Saetti end



      total += add_effect_par * eff;
      effect *= add_effect_par;	//  LM 



      if( GpG.consider_relaxed_plan_for_inconsistences==TRUE )
	{
	  // Valuto vatti che servono nei piani rilassati delle inconsistenze future e vengono invalidati
	  
	  // imposto action=-1 piche sto considerando rimozione
	  verify_supported_fact_in_relaxed_plan_for_inconsistences(-1, level, Hvar.bit_vect_facts);
	}


      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
	{
	  if (GpG.lagrange_multipl)
	    best_eff_cost.weight =
	      (Hvar.weight_facts_define_cost - init_w +
	       Hvar.num_actions_define_cost -
	       init_na) * local_search.lamda_prec;
	  else
	    best_eff_cost.weight =
	      Hvar.weight_facts_define_cost - init_w +
	      Hvar.num_actions_define_cost - init_na;

	  best_eff_cost.act_cost = Hvar.cost_actions_define_cost - init_cost;


	  best_eff_cost.num_actions = Hvar.num_actions_define_cost - init_na;

	}



      if (DEBUG4)
	{
	  printf ("   Temp Add-E: %f, effects %f ", temp,
		  effect /*, local_search.lamda_prec */ );
	  if (DEBUG5)
	    printf ("\n\n<< Evalutate effect END");
	}


    }
  //End Evaluate remotion




// E' abilitato GpG.extended_unsupported_facts e l'elemento del vicinato considerato non e' l'azione che ha come precondizione l'inconsistenza stessa (per cui si valuta la rimozione)
      if(GpG.extended_unsupported_facts && !( neighb_act->constraint_type == C_T_REMOVE_ACTION && Hvar.temp_removed_act == neighb_act->act_pos)  )
	{
	  if(DEBUG5)
	    printf("\n\n %d START Extended unsupported facts evaluation ", GpG.count_num_try);

	  if( Hvar.num_extended_unsupported_facts>0 && GpG.reset_extended_unsupported_facts<2 )
	    {
	      remove_action_mutex_facts_in_bitvect(neighb_act->act_pos,Hvar.initial_relaxed_bit_vect_facts);

	      if(GpG.reset_extended_unsupported_facts==1)
		remove_action_mutex_facts_in_bitvect(neighb_act->act_pos,Hvar.bit_vect_facts);
	    }

	  for(i=0; i<  Hvar.num_extended_unsupported_facts; i++)
	    {
	      el=Hvar.extended_unsupported_facts[i];
	      if( GET_BIT (Hvar.bit_vect_facts, el))
		{
		  if(DEBUG5)
		    printf("\n %d Already supported START_Externded comput. for fact %d - %s , level %d Hvar.weight_facts_define_cost %f Hvar.num_actions_define_cost %d " , GpG.count_num_try,  el, print_ft_name_string(el, temp_name), level,Hvar.weight_facts_define_cost,Hvar.num_actions_define_cost ); 
		  continue; // Fatto reso vero da azioni piano rilassato
		}

		  /*
		    loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		    Azzero loc_n_cost
		  */
		  loc_n_cost.weight = 0.0;
		  loc_n_cost.act_cost = 0.0;
		  loc_n_cost.act_time = 0.0;
		  loc_n_cost.action=act->position;
		  loc_n_cost.options=3;

		  if(DEBUG5)
		    {
		      printf("\n %d START_Externded comput. for fact %d - %s , level %d Hvar.weight_facts_define_cost %f Hvar.num_actions_define_cost %d " , GpG.count_num_try,  el, print_ft_name_string(el, temp_name), level,Hvar.weight_facts_define_cost,Hvar.num_actions_define_cost );  
		    }

		  temp =
		    compute_relaxed_fact_cost (el, level, &loc_n_cost, level, MAXFLOAT);


		  if(DEBUG5)
		    {
		      printf("\n END_Externded comput. for fact %d - %s , level %d Hvar.weight_facts_define_cost %f Hvar.num_actions_define_cost %d " ,  el, print_ft_name_string(el, temp_name), level,Hvar.weight_facts_define_cost,Hvar.num_actions_define_cost );  
		    }


	    }


	}	
	  




  //DA VERIFICARE BENE  
  if (GpG.num_solutions <= 0
      || neighb_act->constraint_type == C_T_INSERT_ACTION)
    {
      init_w = Hvar.weight_facts_define_cost;
      init_na = Hvar.num_actions_define_cost;
      init_cost = Hvar.cost_actions_define_cost;


      insert_action_inlist (neighb_act->act_pos,Hvar.constr->fact);

      // e' necessario quando  utilizzo  i moltiplicatori di lagrange

      best_eff_cost.weight +=
	(Hvar.weight_facts_define_cost - init_w +
	 Hvar.num_actions_define_cost - init_na);
      best_eff_cost.act_cost += (Hvar.cost_actions_define_cost - init_cost);

    }

  // LM Sostituisco il costo ottentuto con i moltiplicatori di lagr a quello 
  // standard se e' impostata la corrispondente modalita' 

  if (GpG.lagrange_multipl)
    total = precond + mutex + effect;



  if (unsat_facts > 1)
    total += (unsat_facts - 1);	// precondiz non supportate - quella di cui si e' fatto il max  




   if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
    {
      if (GpG.lagrange_multipl)
	neighb_act->cost.weight =
	  best_prec_cost.weight + best_mutex_cost.weight +
	  best_eff_cost.weight;
      else
	{
	  neighb_act->cost.weight = Hvar.weight_facts_define_cost + Hvar.num_actions_define_cost;
	}

      neighb_act->cost.act_cost = Hvar.cost_actions_define_cost;
      neighb_act->cost.num_actions = Hvar.num_actions_define_cost;







      if(GpG.timed_facts_present && neighb_act->constraint_type == C_T_INSERT_ACTION )
	{
	 

	  /*
	    considero il costo timed del piano rilassato 
	    precedentemente calcolato 
	  
	   */
	  neighb_act->cost.timed_fa = Hvar.timed_facts_define_cost;


	  if (GET_BIT(GpG.has_timed_preconds, neighb_act -> act_pos))
	    {

	      /*
		-time_Timed_Prec restituisce l'istante in cui  l'azione puo' iniziare considerando le precondiz temporali
		- num_Timed_Prec indica il numero di precondizione temporali che non si e' riusciti ad assegnare
	      */
	      time_Timed_Prec = search_for_pc_intervals(best_prec_cost.act_time, neighb_act->act_pos, level, &num_Timed_Prec);
	      if (num_Timed_Prec > 0)
		{
		  neighb_act->cost.timed_fa +=num_Timed_Prec * GpG.SearchCost_UnsupTimedFact;
		  if(DEBUG3)
		    printf("\nTF-NeighbAct: Increase timed cost for %d unsup timed prec of %s in Rplan", num_Timed_Prec, print_op_name_string(neighb_act->act_pos, temp_name));
		}
	      
	      if( time_Timed_Prec>0)
		{
		  if(neighb_act->cost.act_time < time_Timed_Prec)
		    {
		      neighb_act->cost.act_time= time_Timed_Prec;
		      if(DEBUG3)
			printf("\nUpdate start time %.2f of %s", neighb_act->cost.act_time, print_op_name_string(neighb_act->act_pos, temp_name));
		    }	      
		}
	    }
	}
      




      /*
	Compute time in which lpg supports the inconsistency
      */

      if(neighb_act->constraint_type == C_T_REMOVE_ACTION)
	neighb_act->cost.act_time=best_eff_cost.act_time;
      else
	{

	  /*
	    The unsupported fact (Hvar.constr->fact) in the at_start effects of the examined action
	  */
	  if(is_fact_in_additive_effects_start(neighb_act->act_pos,  Hvar.constr->fact))
	    neighb_act->cost.act_time=best_prec_cost.act_time;
	  else
	    neighb_act->cost.act_time = best_prec_cost.act_time+get_action_time (neighb_act->act_pos, level); ;

	}



      if(GpG.timed_facts_present )
	{
	  
	  /**
	     In caso di Risoluzione di una inconsistenza temporale:
	     Incrementiamo il costo temporale di una quantita' pari
	     alla durata delle azioni che si trovano nel corrente
	     TA-graph tra il livello dell'azione del vicinato e il
	     livello dell'inconsistenza
	   **/

	  if( Hvar.constr->constraint_type ==  C_T_UNSUP_TMD_FACT && 
	      neighb_act->constraint_type == C_T_REMOVE_ACTION)
	    {
	      neighb_act->cost.act_time += slack_vect[neighb_act->act_level];
	      
	      if(DEBUG3)
		printf("\nTF-NeighbAct: Increase temporal cost of %.2f for %s at level %d; total timecost -> %.2f", slack_vect[neighb_act->act_level], print_op_name_string(neighb_act->act_pos,temp_name), neighb_act->act_level, neighb_act->cost.act_time);
	    }

	  /**
	     Incrementiamo il TimedCost considerando il numero di precondizioni
	     timed che diventerebbero non supportate nel corrente LA-graph
	     a seguito dell'insierimento o rimozione dell'azione
	   **/

	  for (i=0; i < gnum_timed_facts; i++)
	    for (j=0; j < gnum_tmd_interval[i]; j++)
	      {
		if (neighb_act->cost.act_time > gtimed_fct_vect[i][j].slack) 
		  {
		    neighb_act->cost.timed_fa += gtimed_fct_vect[i][j].num_act_PC;
		    if(DEBUG3)
		      printf("\nTF-NeighbAct: Increase timed cost for %d new unsupported timed preconditions", gtimed_fct_vect[i][j].num_act_PC);//, neighb_act->cost.weight);
		  }
	      }

	  /**
	     Incrementiamo il TimedCost considerando il numero di precondizioni
	     ai livelli successivi del piano che non potrebbero piu' essere 
	     supportate
	   **/

	  if (FALSE && vectlevel[*Hvar.constr->level]->action.position >= 0)
	    {
	      if(neighb_act->constraint_type == C_T_INSERT_ACTION)
		{
		  future_timed_cost = get_cost_for_future_possibilities(
		   neighb_act -> act_pos, level, 
		   vectlevel[*Hvar.constr->level]->action.time_f 
		   - get_action_time (vectlevel[*Hvar.constr->level]->action.position, *Hvar.constr->level),  
		   best_prec_cost.act_time + get_action_time (neighb_act->act_pos, level));

		  neighb_act -> cost.timed_fa += future_timed_cost;
		}
	      else
		{
		  future_timed_cost = get_cost_for_future_possibilities(
		      neighb_act -> act_pos, level, 
		      vectlevel[*Hvar.constr->level]->action.time_f, 
		      best_eff_cost.act_time );

		  neighb_act -> cost.timed_fa += future_timed_cost;
		}
	      if(DEBUG3 && future_timed_cost > 0.0)
		printf("\nTF-NeighbAct: Increase timed cost for %d precs that cannot be supported", future_timed_cost);//, neighb_act->cost.weight);

	    }
	  /*
	  else
	    neighb_act -> cost.timed_fa += get_cost_for_future_possibilities(neighb_act -> act_pos, level, best_prec_cost.act_time,  best_prec_cost.act_time+get_action_time (neighb_act->act_pos, level));
	  */

	  


      
	}





      /************
      if (neighb_act->cost.act_time < Hvar.time_actions_define_cost)
	{
#ifdef __TEST__
	  printf
	    ("\n  neighb_act->cost.act_time %.2f  Hvar.time_actions_define_cost %.2f ",
	     neighb_act->cost.act_time, Hvar.time_actions_define_cost);
#endif
	  neighb_act->cost.act_time = Hvar.time_actions_define_cost;
	}
      *************/


      if (GpG.Twalkplan && GpG.tabu_length >0 && 
	  neighb_act->constraint_type == C_T_REMOVE_ACTION)
	{			
	  /* 
	     T_walkgraph: increase the cost function of act if it is
	     in the tabu list
	  */
	  diff = GpG.count_num_try - gef_conn[act->position].step;

	  if (diff < GpG.tabu_length  && num_try > GpG.tabu_length)
	    {
	      neighb_act->cost.weight += GpG.delta * (GpG.tabu_length - diff);
	      //	      printf("\nAct in TABU: cost increased by %.2f", GpG.delta * (GpG.tabu_length - diff));
	    }
	}


#ifdef __TEST__
      printf
	("\n\n\n Variables :   total %.2f --  Hvar.num_actions_define_cost %d --   Hvar.weight_facts_define_cost %.2f -- neighb_act->cost.weight  %.2f -- neighb_act->cost.act_cost  %.2f --  neighb_act->cost.num_actions %d -- neighb_act->cost.act_time %.2f -- ",
	 total, Hvar.num_actions_define_cost, Hvar.weight_facts_define_cost,
	 neighb_act->cost.weight, neighb_act->cost.act_cost,
	 neighb_act->cost.num_actions, neighb_act->cost.act_time);

#endif





    }


  // Se ho gia delle soluzioni ed il costo attuale e' molto alto, Sfavorisco ulteriormente inserimento di azioni
  if (GpG.num_solutions && neighb_act->constraint_type == C_T_INSERT_ACTION)
    {
      if (GpG.orig_weight_cost > 0 && GpG.best_cost * 1.5 > GpG.total_cost)
	{
	  //  printf("-");
	  neighb_act->cost.act_cost += get_action_cost (neighb_act->act_pos, neighb_act->act_level, NULL);
	  Hvar.cost_actions_define_cost +=
	    get_action_cost (neighb_act->act_pos, neighb_act->act_level, NULL);

	}
      if (GpG.orig_weight_time > 0 && GpG.best_time * 1.5 > GpG.total_time)
	{
	  neighb_act->cost.act_time +=
	    (10.0 + get_action_time (neighb_act->act_pos, level));
	  Hvar.time_actions_define_cost +=
	    (10.0 + get_action_time (neighb_act->act_pos, level));
	  //   printf("/");
	}
    }


#ifdef __TEST__
  if (DEBUG3)
    {
      printf ("\n Temp TOTAL COST of %s %f,  ",
	      print_op_name_string (act->position, temp_name), total);
      printf
	("\n\n  $$$$$$$++++++++++++++++++++++++++++++++++ MAX COST inc %.2f cost %.2f time %.2f ",
	 neighb_act->cost.weight, neighb_act->cost.act_cost,
	 neighb_act->cost.act_time);


    }
#endif


#ifdef __TEST__
  check_plan (GpG.curr_plan_length);
#endif
  if (DEBUG4)
    {
      printf ("\n\n<<<< Evalutate action END  Act: %s",
	      print_op_name_string (act->position, temp_name));
      printf
	("\n--------------------------------------------------------------\n\n");

      if (DEBUG6)
	printf ("\n -> tot %f", total);

    }



  /*
    Se neighb_act->cost.weight e' superiora a MAX_COST, significa 
    che l'elemento del vicinato non e' stato accettato e quindi assegno a
    tutte le sue componenti lo stesso costo.
   */

  if(neighb_act->cost.weight>=MAX_COST)
    {
     neighb_act->cost.weight = MAX_COST;

      neighb_act->cost.act_cost= MAX_COST;
      neighb_act->cost.num_actions = MAX_COST;
      neighb_act->cost.act_time =MAX_COST;

    }




  return (total);
}













// Definisce utilizzando i bit array il costo per rendere vero Fact
// Quando viene richiamata all'interno di un  dg_action_cost prende 
// inconsiderazione anche le azioni utlizzate per render vere tutte le 
// precondizioni dell'azione originaria

inline float compute_relaxed_fact_cost (int Fact_position, int level, node_cost_list n_cost, int action_level, float max_time_for_timed_fact)
{

  register int temp;
  int curr_level, k, j;
  // int result;
  NoopNode_list inf_noop;
  FtConn *tofix;
  float total=0.0, cost=0.0, prec=0.0, mutex=0.0, prec_act_cost=0.0;
  int times=1;
  int best_action = -1, best_level = 0, best_act_type = 0;
  int el;
  int cel;
  int stop;
  float time_Timed_Prec=-1.0;
  int num_Timed_Prec=0;

  node_cost loc_n_cost, best_n_cost;
  dg_inform_list cri_cost=NULL, best_cri_cost=NULL;


#ifdef __TEST_ITER__

  dg_inform_list loc_dg_cost;
   static int cfc_iter=0;
   cfc_iter++;
   if(DEBUG5)
       printf("\n CRI ITERATION %d ",cfc_iter);
#endif   

  if(DEBUG4)
	{
	  printf("\nFACT to Examine %d, level %d, name ",  Fact_position, level);
	  if(Fact_position>=0)
	    print_ft_name( Fact_position);
	  else
	    print_cvar_tree(-Fact_position,level);
	  // printf(" action %d -- %s ",n_cost->action,print_op_name_string(n_cost->action, temp_name));
	  printf("\n\n");

	}
  prec_act_cost = 0.0;



  if (local_search.ls_continue == 0)
    {
      n_cost->best_action=-1;
      return 0.0;
    }

  stop = 3;
  // stop = 4;
  if (local_search.apply_stop_in_relaxed_plan==TRUE && (Hvar.weight_facts_define_cost+ Hvar.num_actions_define_cost) > local_search.max_act_incons)
    stop--;

  if (GpG.weight_cost <= 0
      || Hvar.cost_actions_define_cost >= local_search.max_act_cost)
    stop--;


  if (GpG.weight_time <= 0
      || Hvar.time_actions_define_cost >= local_search.max_act_time)
    stop--;

  /**
  if (GpG.weight_timed_fa <= 0 ||  Hvar.timed_facts_define_cost > local_search.max_timed_fa)
    stop--;
  **/


  if (stop <= 0)
    {
      //#ifdef __TEST__
      if (DEBUG4)
	printf ("\n STOP compute_dg_cost ");
      //#endif
      // Non esamino ulteriormente gli altri termini di costo dell'elemento del  vicinato 

      Hvar.weight_facts_define_cost++;
      local_search.ls_continue = 0;
      n_cost->best_action=-1;
      return 0.0;
    }
#ifdef __TEST__
  else if (DEBUG2)
    printf ("\nContinue compute_dg_cost");

#endif



  if (local_search.ls_continue == 0)
    {
      n_cost->best_action=-1;
      return 0.0;
    }



  if((GpG.zero_num_A || local_search.apply_stop_in_relaxed_plan==FALSE) && (Fact_position >= 0) && gft_conn[Fact_position].fact_type != IS_DERIVED && gft_conn[Fact_position].num_A==0 )
    {
      if(DEBUG5)
	{
	  printf("\ngft_conn[ Fact_position].num_A==0--skip it ");
	  print_ft_name( Fact_position);
	}
      //CAZZO 
      Hvar.weight_facts_define_cost+= 1;
      
      Hvar.cost_actions_define_cost+= 10;
      
      Hvar.time_actions_define_cost+= 10;

      n_cost->act_cost+= 10;
      n_cost->act_time+= 10;
      total+= 10; 

      return 1.0;

    }

#ifdef __TEST__
  if (Fact_position < 0)
    {
      printf ("\n 2222 Prec numerica %d", Fact_position);

    }
#endif



  // IVAN prova: a volte introduco delle azioni che hanno come prec il fatto non supportato, in questo caso sfavorisco nettamente l'azione in questione

  if (GpG.penalize_inconsistence_in_relaxed_plan && local_search.apply_stop_in_relaxed_plan==TRUE)
  { 
   if (Fact_position >= 0)
    { 

      if( GpG.stop_remove_act &&  Hvar.temp_removed_act>=0 &&  loc_n_cost.options!=2)
	{

	  if( Fact_position == Hvar.initial_unsup_fact_of_relaxed_plan)
	    {
#ifdef __TEST__
	      printf
		("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
      
#endif
	      Hvar.weight_facts_define_cost= MAX_COST;
      
	      Hvar.cost_actions_define_cost= MAX_COST;
      
	      Hvar.time_actions_define_cost= MAX_COST;

	      n_cost->act_cost= MAX_COST;
	      n_cost->act_time= MAX_COST;
	      total= MAX_COST; 
		
	      // Non esamino ulteriormente gli altri termini di costo dell'elemento del  vicinato 
	      local_search.ls_continue = 0;	

	      if(DEBUG4)
		{
		  printf("\nSTOP FACT to MAXCOST %d, level %d, name ",  Fact_position, level);
		  if(Fact_position>=0)
		    print_ft_name( Fact_position);

		  printf("\n\n");

		}      
	      return ( MAX_COST);

	    }
	}
      else//INSERT ACTION
      if (Hvar.constr->constraint_type == C_T_UNSUP_FACT
	 && Hvar.constr->fact == Fact_position)
       {
#ifdef __TEST__
      printf
	("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");
      
#endif
          Hvar.weight_facts_define_cost= MAX_COST;
      
	  Hvar.cost_actions_define_cost= MAX_COST;
      
	  Hvar.time_actions_define_cost= MAX_COST;

	  n_cost->act_cost= MAX_COST;
	  n_cost->act_time= MAX_COST;
	  total= MAX_COST; 
		
	  // Non esamino ulteriormente gli altri termini di costo dell'elemento del  vicinato 
	  local_search.ls_continue = 0;	

	  if(DEBUG4)
	    {
	      printf("\nSTOP FACT to MAXCOST %d, level %d, name ",  Fact_position, level);
	      if(Fact_position>=0)
		print_ft_name( Fact_position);

	      printf("\n\n");

	    }      
	  return ( MAX_COST);
       }
    }
  //#ifdef __TEST_REACH__
   else  //if (Fact_position < 0) quindi numerico
    if (Hvar.constr->constraint_type ==C_T_UNSUP_NUM_FACT
       && Hvar.constr->fact == -Fact_position)
    {
#ifdef __TEST__
      printf
	("\n ATTENZIONE L'azione considerata aveva come precondizione l'inconsistenza stessa");

#endif
      Hvar.weight_facts_define_cost= MAX_COST;

      Hvar.cost_actions_define_cost= MAX_COST;
      
      Hvar.time_actions_define_cost= MAX_COST;

      n_cost->act_cost= MAX_COST;
      n_cost->act_time= MAX_COST;
      total= MAX_COST; 


      if(DEBUG4)
	    {
	      printf("\nSTOP FACT to MAXCOST %d, level %d, name ",  Fact_position, level);
	      print_cvar_tree(-Fact_position,level);

	      printf("\n\n");

	    }

		      
      return ( MAX_COST);
    }
  }
  //#endif

  inf_noop = NULL;
  if (DEBUG4)
    {
      printf ("\n ||||| DG_COST  Fact %s, position %d, level %d\n",
	      print_ft_name_string (Fact_position, temp_name), Fact_position,
	      level);
    }


  if (level <= 0)
    return 0.0;

  // Cerco il primo livello da cui e' possibile inserire una azione che rendera' il fatto supportato (tramite eventualmente una catena di noop)


  // IV DA SISTEMARE
  if (level > action_level)
    {
    level--;
    }
   
  /* fatto non numerico */
  if (Fact_position >= 0) {
    if (gft_conn[Fact_position].fact_type != IS_DERIVED)
      {
	times=1;
	total = 0.0;
	best_action = -1;
	best_n_cost.weight = MAXFLOAT+100.0;
	best_n_cost.act_cost = MAXFLOAT;
	best_n_cost.act_time = MAXFLOAT;
	
	
	// sceglie l'azione che rende vero Fact con il minimo costo di inserimento, considero anche le noop
	tofix = &gft_conn[Fact_position];
	
	curr_level = level;
	

	if( gft_conn[tofix->position].num_A==1)
	  {
	    best_action=gft_conn[tofix->position].A[0];
	    best_level = curr_level;
	    best_act_type = IS_ACTION;
	    best_n_cost.weight = 1;
	    best_n_cost.act_cost = 1;
	    best_n_cost.act_time =1;

	    if(DEBUG5)
	      printf("\n Only one action with this additive effect: act %d name %s ", best_action, print_op_name_string(best_action, temp_name));
	  }
	else
	for (j = 0; j < gft_conn[tofix->position].num_A; j++)
	  {
	    cel = gft_conn[tofix->position].A[j];
	    
	    if (FALSE && Hvar.temp_removed_act == cel
		&& gft_conn[tofix->position].num_A > 1)
	      {
		if (GpG.orig_weight_time <= 0)
		  {
#ifdef __TEST__
		    printf ("\n Non considera azione %d : ", cel);
		    print_op_name (cel);
#endif
		    continue;
		  }
		else
		  n_cost->weight++;
	      }
	    if (gef_conn[cel].level>=0 || GpG.verify_Af || CHECK_ACTION_POS (cel, curr_level))
	      {
		
		// saetti  
		if (gef_conn[cel].sf 
		    && is_fact_in_delete_effects (cel, tofix->position))
		  continue;
		
		if (tofix->position < 0)	//???   if(cel<0)
		  continue;	//LAZZA
		
		
		
		//CAZZOLONE CHE SUCCEDE???!!!!
		// if (GET_BIT (Hvar.bit_vect_actions, cel))
		
		//		  if (GET_BIT (Hvar.bit_vect_facts, cel))
		//   continue;
		

		if (GpG.save_action_cost_list)
		  cost = evaluate_action_cost_from_list (cel, curr_level, &loc_n_cost, max_time_for_timed_fact, &best_n_cost);
		else
		  cost = best_action_evaluation  (cel, curr_level, &loc_n_cost,max_time_for_timed_fact,  &best_n_cost);

		
		
#ifdef __TEST__
		printf
		  ("\n  loc_n_cost.weight %f loc_n_cost.act_cost %f loc_n_cost.act_time %f",
		   loc_n_cost.weight, loc_n_cost.act_cost,
		   loc_n_cost.act_time);
		
#endif
		
		if (Hvar.temp_removed_act == cel)	//&& gft_conn[tofix->position].num_A>1 )
		  {
#ifdef __TEST__
		    printf ("\n Non considera azione %d : ", cel);
		    print_op_name (cel);
#endif
		    loc_n_cost.weight++;
		  }
		
		// if(GpG.num_solutions>0)
		//          result= compute_relative_weight(&best_n_cost, &loc_n_cost);
		//  else result=1;
		
		if (best_n_cost.weight >= loc_n_cost.weight)
		  //   if((GpG.num_solutions>0 && result>=0) || (GpG.num_solutions<=0 &&best_n_cost.weight>=loc_n_cost.weight) )
		  {
		    
		    if (best_n_cost.weight == loc_n_cost.weight
			&& weight_cost (&best_n_cost) <=
			weight_cost (&loc_n_cost))
		      //          if((GpG.num_solutions>0 && result==0 && MY_RANDOM%2)||(GpG.num_solutions<=0 &&best_n_cost.weight==loc_n_cost.weight && weight_cost(&best_n_cost)<= weight_cost(&loc_n_cost))  )
		      continue;
		    
		    // else ... 
		    
		    best_action = cel;
		    best_level = curr_level;
		    best_act_type = IS_ACTION;
		    best_n_cost.weight = loc_n_cost.weight;
		    best_n_cost.num_actions = loc_n_cost.num_actions;
		    best_n_cost.act_cost = loc_n_cost.act_cost;
		    best_n_cost.act_time = loc_n_cost.act_time;
		    
		    //#ifdef __TEST__
		    if(DEBUG5)
		    printf
		      ("\n\n\n Comp_fact_cost NEW  BEST ACT %s  time %d inc %.2f act_cost %.2f act_time %.2f  ",
		       print_op_name_string (best_action, temp_name),
		       best_level, best_n_cost.weight, best_n_cost.act_cost,
		       best_n_cost.act_time);
		    //#endif
		    
		    if (best_n_cost.weight <= 0)
		      break;	// Non esamino ulteriori candidati 
		  }
		
		
	      }
	    
#ifdef __TEST__
	    else
	      {
		printf
		  ("\n L'azione %s non puo' essere applicata al livello %d, lev: %d",
		   print_op_name_string (cel, temp_name), curr_level,
		   gef_conn[cel].level);
	      }
#endif
	    
	  }
	
	
	
      }
    else
      {

	int num_facts = 0;

	indexed_vect_list *tuple = NULL;
	
	create_gdp_path_for(Fact_position, level, &Hvar.tmp_path);

	if (!GpG.derived_pred_in_preconds)
	  {
	    
	    times  = choose_best_action_for_derived_predicate(&Hvar.tmp_path, Fact_position, level, &best_action, &best_level, action_level);
	    n_cost->weight = times;
	    best_act_type = IS_ACTION;
	    
	    if (n_cost->weight <= 0)
	      return 0.0;
	  }
	else
	  {
	    tuple = dg_choose_best_facts_set(&Hvar.tmp_path, &num_facts, level);
	    
	    if (tuple)
	      {
		int facts[num_facts];
		
		memcpy(facts, tuple->item, num_facts * sizeof(int));
		
		for (j = 0; (j < num_facts) && local_search.ls_continue; j++)
		  {
		    el = facts[j];
		    
		    if (is_fact_supported_in_relaxed_plan (el, level))
		      continue;
		    
		    loc_n_cost.weight = 0.0;
		    loc_n_cost.act_cost = 0.0;
		    loc_n_cost.act_time = 0.0;
		    
		    compute_relaxed_fact_cost (el, level, &loc_n_cost, action_level, 
					       max_time_for_timed_fact);
		  }
	      }
	    
	    return 0.0;
	    
	  }
	
      }
  }
  else
    {

      //      Hvar.num_actions_define_cost+=4;
      Hvar.weight_facts_define_cost += 1;	// ??? 4;
#ifdef __TEST__
      printf ("\n 11111  Azione per precondizione Numerica %d",
	      Fact_position);
#endif

	times=choose_best_action_for_unsup_num_fact (Fact_position, level,
					       &best_action, &best_level,
					       action_level,max_time_for_timed_fact);
	n_cost->weight =times;
	best_act_type = IS_ACTION;
    

      if (n_cost->weight <= 0)
	{
	  //   printf("AA ");
	  return 0.0;
	}

    }


  if (best_action < 0)		//WARNING 
    {
      if (Fact_position < 0)
	return MAX_COST;

      if (inf_noop)
	{
	  best_action = inf_noop->position;
	  best_level = *inf_noop->level;
	  best_act_type = IS_NOOP;

	  n_cost->weight = 1.0;
	  n_cost->act_cost = 1.0;

#ifdef __TEST__
	  printf
	    ("\n ***********************L'unica azione che posso scegliere e' una noop weight %f cost %f",
	     n_cost->weight, n_cost->act_cost);

#endif

	}
      else
	{
	  Hvar.weight_facts_define_cost = MAX_COST;
	  n_cost->weight = MAX_COST;
	  n_cost->act_cost = MAX_COST;
	  n_cost->act_time = MAX_COST;

   
#ifdef __TEST_ITER__

	  get_dg_fact_cost (Fact_position, level, &loc_dg_cost);
#endif
   
#ifdef __TEST__
	  printf
	    ("\nL'unica azione che posso scegliere e' una noop weight %f cost %f",
	     n_cost->weight, n_cost->act_cost);

#endif



	  if(DEBUG5)
	    {
	      printf("\n STOP - no best action found for fact ");
	      print_ft_name( Fact_position);
	   
#ifdef __TEST_ITER__

	      printf("\n ITERATION %d ",cfc_iter);
#endif
   
	    }


	  return (MAX_COST);
	}
      // Definisco il costo per rendere vere le precondizioni non supportate 
    }

  if(DEBUG4)
    if (best_act_type == IS_ACTION)
      printf ("\n\n    BEST_ACTION choosen     %s  time %d pos %d ",
	    print_op_name_string (best_action, temp_name), best_level,
	    best_action);



#ifdef __TEST__1
  //PROVA
  j = get_dg_fact_cost (Fact_position, level, &loc_dg_cost);

  if (loc_dg_cost)
    for (k = 0, n_cost->act_cost = loc_dg_cost->totcost;
	 loc_dg_cost && n_cost->act_cost == loc_dg_cost->totcost;
	 loc_dg_cost = loc_dg_cost->next)
      if (loc_dg_cost->best_act == best_action)
	{
	  k = 1;
	  printf ("1");
	  if (j == best_level)
	    printf ("1");
	  printf (" ");
	}

  if (k == 0)
    printf ("0 ");
#endif


  /***
      Azzerati prima della chiamata di compute_relaxed_fact_cost
      n_cost->weight = 0.0;
      n_cost->act_cost = 0.0;
      n_cost->act_time = 0.0;
  **/





  ///////////////////////
  // MUTEX
  //////////////////////
  total = 1.0;			// Utilizzare invece il costo delee azioni ??? 

  if(GpG.evaluate_threated_supported_preconds_of_neighb_action==2 &&loc_n_cost.options==3 )
    {
      if (Hvar.constr->constraint_type == C_T_UNSUP_FACT && ARE_MUTEX_FT_EF(Hvar.constr->fact, best_action))
	{
	  if(DEBUG5)
	    {
	      printf("\n %d -Penalize neighb element in threat evaluation. Fact %d -- %s ", GpG.count_num_try, Hvar.constr->fact, print_ft_name_string(Hvar.constr->fact,temp_name) );
	      printf("  action %d -- %s ", best_action, print_op_name_string(best_action, temp_name));

	    }
	  Hvar.weight_facts_define_cost+=5.0;
	}

    }

 
  if(GpG.evaluate_mutex_for_action_remotion && loc_n_cost.options==2)
    {
      if(DEBUG5)
	printf("\n Evaluate mutex action at the end of compute_relaxed_fact_cost");

    }
  else
  if(GpG.num_solutions == 0 && GpG.mutex_and_additive_effects)
    mutex = count_mutex_noop_at_start (best_action, best_level);
  else
    mutex = count_mutex_facts (best_action, best_level); 


  Hvar.weight_facts_define_cost +=  GpG.weight_mutex_in_relaxed_plan * mutex;

  total += mutex;


  if(DEBUG5)
    printf("\n Best action MUTEX %f  -- best act %d ",mutex, best_action);




  temp=insert_action_inlist (best_action, Fact_position);
  
  if (temp == 0)	// inserisco subito best action per evitare cicli di inserimento
    {
      Hvar.weight_facts_define_cost++;
      return 1.0;		// Azione precedentem considerata
    }
  else
    if(temp<0)
      {
	Hvar.weight_facts_define_cost = MAX_COST;
	n_cost->weight = MAX_COST;
	n_cost->act_cost = MAX_COST;
	n_cost->act_time = MAX_COST;
	return MAX_COST;
      }
  


  if (Hvar.temp_removed_act == best_action)	//  && gft_conn[tofix->position].num_A>1 )
    {

      Hvar.weight_facts_define_cost += 2.0;
#ifdef __TEST__
      printf ("\n  Considera azione %d  temporaneam rimossa: ", best_action);
      print_op_name (best_action);
#endif

    }



  /////////////////////////////////
  //////////// PRECONDITIONS
  ////////////////////////////////



  // cost  of  Best_action








  /* Inserisco in Hvar.supported_preconds le precondizioni non supportate */

// Precondizioni at start
  for (j = 0, k = 0, prec = 0.0;
       j < gef_conn[best_action].num_PC && local_search.ls_continue; j++)
    {
      el = gef_conn[best_action].PC[j];

      if (el>=0 && is_fact_supported_in_relaxed_plan (el, level))
	insert_supported_preconds(el);

    }

  // Precondizioni overall
  if (gef_conn[best_action].sf != NULL)
    {
      for (j = 0;
	   j < gef_conn[best_action].sf->num_PC_overall
	     && local_search.ls_continue; j++)
	{
	  el = gef_conn[best_action].sf->PC_overall[j];

	  if (is_fact_in_additive_effects_start (best_action, el))
	    {
	      continue;
	    }

	  if (el>=0 && is_fact_supported_in_relaxed_plan (el, level))
	    insert_supported_preconds(el);

	}

      

      for (j = 0;
	   j < gef_conn[best_action].sf->num_PC_end
	     && local_search.ls_continue; j++)
	{
	  el = gef_conn[best_action].sf->PC_end[j];
	  
	  if (is_fact_in_additive_effects_start (best_action, el))
	    continue;


	  if (el>=0 && is_fact_supported_in_relaxed_plan (el, level))
	    insert_supported_preconds(el);

	}
      
      
      
    }


      //Costo  Precondizioni at start
  for (j = 0, k = 0, prec = 0.0;
       j < gef_conn[best_action].num_PC && local_search.ls_continue; j++)
    {
      el = gef_conn[best_action].PC[j];



      if ((el >= 0 && gft_conn[el].level>=0)  ||  CHECK_FACT_POS (el, best_level))
	{

#ifdef __TEST__
	  if (DEBUG3)

	    printf
	      ("\n\n\n %d  *********************** COMPUTE DG MAX COST ACT %s fact %s",
	       ++k, print_op_name_string (best_action, temp_name),
	       print_ft_name_string (el, temp_name));

#endif

	  if (el < 0)
	    {
	      if (is_num_prec_satisfied_in_common_level (el))
		continue;
	    }
	  else if (is_fact_supported_in_relaxed_plan (el, level))
	    {
	      //#ifdef __TEST__
	      if(DEBUG5)
		printf ("\n Level %d Supported fact %s -2", level,
		      print_ft_name_string (el, temp_name));
	      //#endif


	      if (GpG.temporal_plan)
		{

		  if (n_cost->act_time <
		      CONVERT_FACT_TO_NODE (el, level)->time_f)
		    {
		      n_cost->act_time =
			CONVERT_FACT_TO_NODE (el, level)->time_f;

#ifdef __TEST__
		      printf
			("\n Max Time prec. supported fact %d time %.2f ", el,
			 CONVERT_FACT_TO_NODE (el, level)->time_f);
		      print_ft_name (el);
#endif
		    }



		  if (Hvar.time_actions_define_cost < n_cost->act_time)
		    Hvar.time_actions_define_cost = n_cost->act_time;


		}



	      continue;
	    }



	  if (el >= 0 && GpG.accurate_cost >= COMPUTE_DG_LIST_COST
	      && GET_BIT (Hvar.bit_vect_facts, el))
	    {
#ifdef __TEST__
	      printf
		("\nFact  already supported in COMPUTE_DG_LIST_COST, level %d",
		 best_level);
	      print_ft_name (el);
#endif


	      // Il fatto e' supportato da azioni di ACTS, prendo il MAX tra le altre prec dell'azione e l'istante in cui il fatto el sara' supportato (stima fornita da Hvar.estimate_time_facts[el])
		  if (n_cost->act_time <
		      Hvar.estimate_time_facts[el])
		    {
		      n_cost->act_time =Hvar.estimate_time_facts[el];

#ifdef __TEST__
		      printf("\n Max Time fact in Hvar.bit_vect_facts:  fact %d time %.2f ", el,Hvar.estimate_time_facts[el]);
		      print_ft_name (el);
#endif
		    }



		  if (Hvar.time_actions_define_cost < n_cost->act_time)
		    Hvar.time_actions_define_cost = n_cost->act_time;

		  if(GpG.cri_intermediate_levels==DYNAMIC_INTERMEDIATE_REACHAB_INFORM && el>0)
		    {
		      
		      get_dg_fact_cost (el, level, &cri_cost);

		      if(cri_cost!=NULL && cri_cost->num_actions<MAX_INT_COST)
			{
			  if(best_cri_cost==NULL)
			    best_cri_cost=cri_cost;
			  else
			    if( cri_cost->num_actions > best_cri_cost->num_actions ||
				(cri_cost->num_actions == best_cri_cost->num_actions && cri_cost->cost < best_cri_cost->cost)
				)
			      best_cri_cost=cri_cost;
			  
			  
			}
		    }


	      continue;
	    }
	  /*
	    loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
	    Azzero loc_n_cost
	  */
	  loc_n_cost.weight = 0.0;
	  loc_n_cost.act_cost = 0.0;
	  loc_n_cost.act_time = 0.0;

	  loc_n_cost.action=best_action;

	  temp = compute_relaxed_fact_cost (el, level, &loc_n_cost, action_level, max_time_for_timed_fact+ get_action_time (best_action, best_level));

	  if(GpG.cri_intermediate_levels==DYNAMIC_INTERMEDIATE_REACHAB_INFORM && el>0)
	    {
	      
	      get_dg_fact_cost (el, level, &cri_cost);

	      if(cri_cost!=NULL && cri_cost->num_actions<MAX_INT_COST)
		{
		  if(best_cri_cost==NULL)
		    best_cri_cost=cri_cost;
		  else
		    if( cri_cost->num_actions > best_cri_cost->num_actions ||
			(cri_cost->num_actions == best_cri_cost->num_actions && cri_cost->cost < best_cri_cost->cost)
			)
		      best_cri_cost=cri_cost;
		      
		 
		}
	    }



	  if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
	    {


	      if (n_cost->act_time < loc_n_cost.act_time
		  && loc_n_cost.act_time < MAX_COST)
		n_cost->act_time = loc_n_cost.act_time;

#ifdef __TEST__
	      if (DEBUG2)
		{
		  printf
		    ("\n %d  *********************** END COMPUTE DG MAX COST ACT %s cost %.2f weight %.2f act_cost %.2f act_time %.2f  act_duration %.2f fact :",
		     k, print_op_name_string (best_action, temp_name), prec,
		     loc_n_cost.weight, loc_n_cost.act_cost,
		     loc_n_cost.act_time, get_action_time (best_action,
							   best_level));
		  print_ft_name (el);
		}

#endif
	      if (prec < loc_n_cost.weight)
		{
		  prec = loc_n_cost.weight;



#ifdef __TEST__
		  if (DEBUG2)
		    {
		      printf
			("\n %d BEST  MAX COST ACT %s  cost %.2f weight %.2f act_cost %.2f act_time %.2f  fact:",
			 k, print_op_name_string (best_action, temp_name),
			 prec, loc_n_cost.weight, loc_n_cost.act_cost,
			 loc_n_cost.act_time);
		      print_ft_name (el);
		    }
#endif

		}
	    }





	}

#ifdef __TEST__
      else
	printf
	  ("\n ERRORE 1002  Fatto %s non presente al corrispondente livello %d, first level %d",
	   print_ft_name_string (el, temp_name), level - 1,
	   CONVERT_FACT_TO_VERTEX (el)->level);
#endif

      if (Hvar.time_actions_define_cost < n_cost->act_time)
	Hvar.time_actions_define_cost = n_cost->act_time;
    }



  // SISTEMARE gestione COST LIST 

  // Precondizioni overall
  if (gef_conn[best_action].sf != NULL)
    {
      for (j = 0;
	   j < gef_conn[best_action].sf->num_PC_overall
	   && local_search.ls_continue; j++)
	{
	  el = gef_conn[best_action].sf->PC_overall[j];

#ifdef __TEST__
	  printf ("\n %d -- Fact %s prec over all of %s ", j,
		  print_ft_name_string (el, temp_name),
		  print_op_name_string (best_action, temp_name));

#endif


	  //      if(el<0)
	  //    continue; //LAZZA

	  if (is_fact_in_additive_effects_start (best_action, el))
	    {
#ifdef __TEST__

	      printf ("\n Fact is in additice effects at start ");
	      print_ft_name (el);
#endif


	      continue;
	    }

	  /*          if(vectlevel[best_level]->noop_act[el].w_is_used>0) // CHIEDERE
	     {
	     #ifdef __TEST__
	     printf("\n vectlevel[best_level]->noop_act[el].w_is_used>0 ");
	     #endif 
	     continue;
	     }
	   */
	  if (CHECK_FACT_POS (el, best_level))
	    {

#ifdef __TEST__
	      if (DEBUG2)

		printf
		  ("\n %d ***********************+ COMPUTE DG MAX COST ACT %s fact %s PREC OVERALL tot %d",
		   j, print_op_name_string (best_action, temp_name),
		   print_ft_name_string (el, temp_name),
		   gef_conn[best_action].sf->num_PC_overall);

#endif

	      if (el < 0)
		{
		  if (is_num_prec_satisfied_in_common_level (el))
		    continue;
		}
	      else if (is_fact_supported_in_relaxed_plan (el, level))
		{
		  //#ifdef __TEST__
		  if(DEBUG5)
		  printf ("\n Level %d Supported fact %s -3", level,
			  print_ft_name_string (el, temp_name));
		  //#endif



		  if (GpG.temporal_plan && el > 0)
		    {
		      if (n_cost->act_time <
			  CONVERT_FACT_TO_NODE (el, level)->time_f)
			{
			  n_cost->act_time =
			    CONVERT_FACT_TO_NODE (el, level)->time_f;
#ifdef __TEST__
			  printf
			    ("\n Max Time prec. supported fact %d time %.2f ",
			     el, CONVERT_FACT_TO_NODE (el, level)->time_f);
			  print_ft_name (el);
#endif
			}
		    }

		  continue;
		}




	      if (el >= 0 && GpG.accurate_cost >= COMPUTE_DG_LIST_COST
		  && GET_BIT (Hvar.bit_vect_facts, el))
		{
#ifdef __TEST__
		  printf
		    ("\nFact %s already supported in COMPUTE_DG_LIST_COST, level %d",
		     print_ft_name_string (el, temp_name), best_level);
#endif




	      // Il fatto e' supportato da azioni di ACTS, prendo il MAX tra le altre prec dell'azione e l'istante in cui il fatto el sara' supportato (stima fornita da Hvar.estimate_time_facts[el])
		  if (n_cost->act_time <
		      Hvar.estimate_time_facts[el])
		    {
		      n_cost->act_time =Hvar.estimate_time_facts[el];

#ifdef __TEST__
		      printf
			("\n Max Time fact in Hvar.bit_vect_facts:  fact %d time %.2f ", el,
			 Hvar.estimate_time_facts[el]);
		      print_ft_name (el);
#endif
		    }



		  if (Hvar.time_actions_define_cost < n_cost->act_time)
		    Hvar.time_actions_define_cost = n_cost->act_time;

		  if(GpG.cri_intermediate_levels==DYNAMIC_INTERMEDIATE_REACHAB_INFORM && el>0)
		    {
		      
		      get_dg_fact_cost (el, level, &cri_cost);
		      
		      if(cri_cost!=NULL && cri_cost->num_actions<MAX_INT_COST)
			{
			  if(best_cri_cost==NULL)
			    best_cri_cost=cri_cost;
			  else
			    if( cri_cost->num_actions > best_cri_cost->num_actions ||
				(cri_cost->num_actions == best_cri_cost->num_actions && cri_cost->cost < best_cri_cost->cost)
				)
			      best_cri_cost=cri_cost;
			  
			  
			}
		    }


		  continue;
		}
	      /*
		loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		Azzero loc_n_cost
	      */
	      loc_n_cost.weight = 0.0;
	      loc_n_cost.act_cost = 0.0;
	      loc_n_cost.act_time = 0.0;

	      loc_n_cost.action=best_action;

	      temp =
		compute_relaxed_fact_cost (el, level, &loc_n_cost, action_level, max_time_for_timed_fact+ get_action_time (best_action, best_level));

	      if(GpG.cri_intermediate_levels==DYNAMIC_INTERMEDIATE_REACHAB_INFORM && el>0)
		{
	      
		  get_dg_fact_cost (el, level,&cri_cost);

		  if(cri_cost!=NULL && cri_cost->num_actions<MAX_INT_COST)
		    {
		      if(best_cri_cost==NULL)
			best_cri_cost=cri_cost;
		      else
			if( cri_cost->num_actions > best_cri_cost->num_actions ||
			    (cri_cost->num_actions == best_cri_cost->num_actions && cri_cost->cost < best_cri_cost->cost)
			    )
			  best_cri_cost=cri_cost;
		      
		 
		    }
		}


	      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
		{


		  if (n_cost->act_time < loc_n_cost.act_time
		      && loc_n_cost.act_time < MAX_COST)
		    n_cost->act_time = loc_n_cost.act_time;

#ifdef __TEST__
		  if (DEBUG2)
		    {
		      printf
			("\n %d  *********************** END COMPUTE DG MAX COST ACT %s cost %.2f weight %.2f act_cost %.2f act_time %.2f  act_duration %.2f fact :",
			 k, print_op_name_string (best_action, temp_name),
			 prec, loc_n_cost.weight, loc_n_cost.act_cost,
			 loc_n_cost.act_time, get_action_time (best_action,
							       best_level));
		      print_ft_name (el);
		    }

#endif
		  if (prec < loc_n_cost.weight)
		    {
		      prec = loc_n_cost.weight;



#ifdef __TEST__
		      if (DEBUG2)
			{
			  printf
			    ("\n %d BEST  MAX COST ACT %s  cost %.2f weight %.2f act_cost %.2f act_time %.2f  fact:",
			     k, print_op_name_string (best_action, temp_name),
			     prec, loc_n_cost.weight, loc_n_cost.act_cost,
			     loc_n_cost.act_time);
			  print_ft_name (el);
			}
#endif

		    }
		}





	    }

#ifdef __TEST__
	  else
	    printf
	      ("\n ERRORE 1002  Fatto %s non presente al corrispondente livello %d, first level %d",
	       print_ft_name_string (el, temp_name), level - 1,
	       CONVERT_FACT_TO_VERTEX (el)->level);
#endif

	  if (Hvar.time_actions_define_cost < n_cost->act_time)
	    Hvar.time_actions_define_cost = n_cost->act_time;
	}

    }



  // Precondizioni at end
  if (gef_conn[best_action].sf != NULL)
    {
      for (j = 0;
	   j < gef_conn[best_action].sf->num_PC_end
	   && local_search.ls_continue; j++)
	{
	  el = gef_conn[best_action].sf->PC_end[j];

	  //      if(el<0)
	  //        continue; //LAZZA

	  if (is_fact_in_additive_effects_start (best_action, el))
	    continue;

	  if (CHECK_FACT_POS (el, best_level))
	    {

#ifdef __TEST__
	      if (DEBUG2)

		printf("\n %d  *********************** COMPUTE DG MAX COST ACT %s fact %s",
		   ++k, print_op_name_string (best_action, temp_name),
		   print_ft_name_string (el, temp_name));
#endif

	      if (el < 0)
		{
		  if (is_num_prec_satisfied_in_common_level (el))
		    continue;
		}
	      else if (is_fact_supported_in_relaxed_plan (el, level))
		{
		  //#ifdef __TEST__
		  if(DEBUG5)
		    printf ("\n Level %d Supported fact %s -4", level,
			  print_ft_name_string (el, temp_name));
		  //#endif


		  if (GpG.temporal_plan)
		    {

		      if (n_cost->act_time <
			  CONVERT_FACT_TO_NODE (el, level)->time_f-get_action_time (best_action, best_level))
			{
			  n_cost->act_time =
			    CONVERT_FACT_TO_NODE (el, level)->time_f-get_action_time (best_action, best_level);

#ifdef __TEST__
			  printf
			    ("\n Max Time prec. supported fact %d time %.2f ",
			     el, CONVERT_FACT_TO_NODE (el, level)->time_f);
			  print_ft_name (el);
#endif
			}
		    }


		  continue;
		}




	      if (el >= 0 && GpG.accurate_cost >= COMPUTE_DG_LIST_COST
		  && GET_BIT (Hvar.bit_vect_facts, el))
		{
#ifdef __TEST__
		  printf
		    ("\nFact %s already supported in COMPUTE_DG_LIST_COST, level %d",
		     print_ft_name_string (el, temp_name), best_level);
#endif



	      // Il fatto e' supportato da azioni di ACTS, prendo il MAX tra le altre prec dell'azione e l'istante in cui il fatto el sara' supportato (stima fornita da Hvar.estimate_time_facts[el] - get_action_time(best_action, best_level) poiche' la precondizione e' at_end)
		  if (n_cost->act_time <
		      (Hvar.estimate_time_facts[el] - get_action_time(best_action, best_level)))
		    {
		      n_cost->act_time =Hvar.estimate_time_facts[el] - get_action_time(best_action, best_level);

#ifdef __TEST__
		      printf
			("\n Max Time fact in Hvar.bit_vect_facts:  fact %d time %.2f ", el,
			 Hvar.estimate_time_facts[el]-get_action_time(best_action, best_level));
		      print_ft_name (el);
#endif
		    }



		  if (Hvar.time_actions_define_cost < n_cost->act_time-get_action_time(best_action, best_level))
		    Hvar.time_actions_define_cost = n_cost->act_time-get_action_time(best_action, best_level);



		  if(GpG.cri_intermediate_levels==DYNAMIC_INTERMEDIATE_REACHAB_INFORM && el>0)
		    {
	      
		      get_dg_fact_cost (el, level, &cri_cost);
		      
		      if(cri_cost!=NULL && cri_cost->num_actions<MAX_INT_COST)
			{
			  if(best_cri_cost==NULL)
			    best_cri_cost=cri_cost;
			  else
			    if( cri_cost->num_actions > best_cri_cost->num_actions ||
				(cri_cost->num_actions == best_cri_cost->num_actions && cri_cost->cost < best_cri_cost->cost)
				)
			      best_cri_cost=cri_cost;
			  
			  
			}
		    }
		  

		  continue;
		}
	      /*
		loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		Azzero loc_n_cost
	      */
	      loc_n_cost.weight = 0.0;
	      loc_n_cost.act_cost = 0.0;
	      loc_n_cost.act_time = 0.0;
	      loc_n_cost.action=best_action;
	      temp =
		compute_relaxed_fact_cost (el, level, &loc_n_cost, action_level, max_time_for_timed_fact);

	      if(GpG.cri_intermediate_levels==DYNAMIC_INTERMEDIATE_REACHAB_INFORM && el>0 )
		{
		  get_dg_fact_cost (el, level,&cri_cost);
		  
		  if(cri_cost!=NULL && cri_cost->num_actions<MAX_INT_COST)
		    {
		      if(best_cri_cost==NULL)
			best_cri_cost=cri_cost;
		      else
			if( cri_cost->num_actions > best_cri_cost->num_actions ||
			    (cri_cost->num_actions == best_cri_cost->num_actions && cri_cost->cost < best_cri_cost->cost)
			    )
			  best_cri_cost=cri_cost;
		      
		      
		    }
		}



	      if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
		{


		  if (n_cost->act_time < (loc_n_cost.act_time-get_action_time (best_action, best_level))
		      && loc_n_cost.act_time < MAX_COST)
		    n_cost->act_time = loc_n_cost.act_time-get_action_time (best_action, best_level);

#ifdef __TEST__
		  if (DEBUG2)
		    {
		      printf
			("\n %d  *********************** END COMPUTE DG MAX COST ACT %s cost %.2f weight %.2f act_cost %.2f act_time %.2f  act_duration %.2f fact :",
			 k, print_op_name_string (best_action, temp_name),
			 prec, loc_n_cost.weight, loc_n_cost.act_cost,
			 loc_n_cost.act_time, get_action_time (best_action,
							       best_level));
		      print_ft_name (el);
		    }

#endif
		  if (prec < loc_n_cost.weight)
		    {
		      prec = loc_n_cost.weight;



#ifdef __TEST__
		      if (DEBUG2)
			{
			  printf
			    ("\n %d BEST  MAX COST ACT %s  cost %.2f weight %.2f act_cost %.2f act_time %.2f  fact:",
			     k, print_op_name_string (best_action, temp_name),
			     prec, loc_n_cost.weight, loc_n_cost.act_cost,
			     loc_n_cost.act_time);
			  print_ft_name (el);
			}
#endif

		    }
		}






	    }

#ifdef __TEST__
	  else
	    printf
	      ("\n ERRORE 1002  Fatto %s non presente al corrispondente livello %d, first level %d",
	       print_ft_name_string (el, temp_name), level,
	       CONVERT_FACT_TO_VERTEX (el)->level);
#endif

	  if (Hvar.time_actions_define_cost < n_cost->act_time)
	    Hvar.time_actions_define_cost = n_cost->act_time;

	}

    }




  //***************************************************************************************** saetti end


   if (GpG.timed_facts_present && GET_BIT(GpG.has_timed_preconds, best_action))
	{


	  time_Timed_Prec=start_time_respect_to_mutex_constraint(best_action, best_level);
	  if(n_cost->act_time< time_Timed_Prec)
	    {
	      if(DEBUG5)
		printf("\n TF-RplanAct: Update start time of best action %d: %f --> %f",best_action,n_cost->act_time, time_Timed_Prec);
	      n_cost->act_time= time_Timed_Prec;
	    }


	  /*
	    -time_Timed_Prec restituisce l'istante in cui  l'azione puo' iniziare considerando le precondiz temporali
	    - num_Timed_Prec indica il numero di precondizione temporali che non si e' riusciti ad assegnare
	  */
	  time_Timed_Prec = search_for_pc_intervals( n_cost->act_time, best_action, best_level, &num_Timed_Prec);
	  
	  if (num_Timed_Prec > 0)
	    {
	      Hvar.timed_facts_define_cost +=num_Timed_Prec;// * GpG.SearchCost_UnsupTimedFact;
	      if(DEBUG3)
		printf("\nTF-RplanAct: Increase search cost for %d unsupported timed precondition of %s in relaxed plan", num_Timed_Prec, print_op_name_string(best_action, temp_name));
	    }
	  
	  if( time_Timed_Prec>0)
	    {
	      if(n_cost->act_time < time_Timed_Prec)
		{
		  n_cost->act_time = time_Timed_Prec;
		  if(DEBUG3)
		    printf("\nTF-RplanAct: Update start time %.2f of %s", n_cost->act_time, print_op_name_string(best_action, temp_name));
		}	      
	    }
	}


  

   update_supported_precond_for_action(best_action);


   /* Aggiorno il bit array dei fatti minacciati */

   update_threated_facts_in_bitvect(best_action, Hvar.threated_bit_vect_facts);


  /*
    Increase the local execution and temporal cost considering best_act
  */ 
      n_cost->act_cost += get_action_cost (best_action, best_level, NULL);
      n_cost->act_time += get_action_time (best_action, best_level);
 



  // Inserisco temporaneamente l'azione migliore, considero il costo per renderla vera quando le sue precondizioni sono ormai supportate 

  if (Hvar.time_actions_define_cost < n_cost->act_time)
    Hvar.time_actions_define_cost = n_cost->act_time;


  n_cost->weight = total;
  n_cost->best_action=best_action;



  //#ifdef TEST_GR 
  if (DEBUG4)
    printf
      ("\n\n ||| END DG_COST  Fact %s, position %d, level %d\n  total %f PREC %.2f ME %.2f act_cost %.2f act_time %.2f -- Hvar.weight_facts_define_cost %.2f",
       print_ft_name_string (Fact_position, temp_name), Fact_position, level,
       total, prec, mutex, n_cost->act_cost, n_cost->act_time,
       Hvar.weight_facts_define_cost);
  //#endif 




  /* Per ciascuna azione nel piano rilassato calcola 
     l'incremento massimo al costo di ricerca */
  //compute_search_cost_for_timed_facts(best_action, best_level, n_cost->act_time);

  if (GpG.derived_pred_in_preconds) {
    memcpy(temp_dp_precs, vectlevel[best_level] -> gnum_dp_precs, gnum_dp_conn * sizeof(int));
  }


  // Setto effetti di best action

  if (GpG.accurate_cost >= COMPUTE_DG_LIST_COST)
    {				//  insert_action_inlist( best_action );


      if (gef_conn[best_action].sf)
	for (j = 0; j < gef_conn[best_action].sf->num_A_start; j++)
	  {
	    el = gef_conn[best_action].sf->A_start[j];

	    if (el < 0)
	      {
		// Applico  eff in common level
		apply_numeric_effect_in_common_level (el,times);
		continue;	// LAZZA

	      }
	    if (is_fact_in_delete_effects (best_action, el))
	      continue;

	    // E' la prima volta che rendo supportato el e questo viene supportato da best_action al tempo n_cost->act_time (poiche' l'effetto e' at_start

	    if(Hvar.estimate_time_facts[el]<=0)
	      Hvar.estimate_time_facts[el]=n_cost->act_time;


	    if (GpG.derived_pred_in_preconds)
	      calc_new_derived_predicates_from(el, temp_dp_precs, Hvar.bit_vect_facts, ADD_FACT, NULL);

	    SET_BIT (Hvar.bit_vect_facts, el);

   	    if(GpG.cri_intermediate_levels==DYNAMIC_INTERMEDIATE_REACHAB_INFORM)
	      {
	  
		if(best_cri_cost!=NULL&&  best_cri_cost->num_actions<MAX_INT_COST)
		  update_intermediate_reachab_inform(el,best_action, best_cri_cost->num_actions+1,  best_cri_cost->cost+ get_action_cost (best_action, best_level, NULL),  n_cost->act_time - 
						     get_action_time (best_action, best_level) , &vectlevel[level]->level);
		  }

#ifdef __TEST__
	    printf ("\n ''''FACT %d : ", el);
	    print_ft_name (el);
#endif

	  }


      for (j = 0; j < gef_conn[best_action].num_A; j++)
	{
	  el = gef_conn[best_action].A[j];
	  if (el < 0)
	    {
	      // Applico  eff in common level
	      apply_numeric_effect_in_common_level (el,times);
	      continue;		// LAZZA

	    }
    // E' la prima volta che rendo supportato el e questo viene supportato da best_action al tempo n_cost->act_time+ get_action_time(best_action, best_level) (poiche' l'effetto e' at_end

	  if(Hvar.estimate_time_facts[el]<=0)
	    Hvar.estimate_time_facts[el]=n_cost->act_time+ get_action_time(best_action, best_level);

	  if (GpG.derived_pred_in_preconds)
	    calc_new_derived_predicates_from(el, temp_dp_precs, Hvar.bit_vect_facts, ADD_FACT, NULL);

	  SET_BIT (Hvar.bit_vect_facts, el);

	  if(GpG.cri_intermediate_levels==DYNAMIC_INTERMEDIATE_REACHAB_INFORM)
	      {
	  
		if(best_cri_cost!=NULL &&  best_cri_cost->num_actions<MAX_INT_COST)
		  update_intermediate_reachab_inform(el, best_action, best_cri_cost->num_actions+1,  best_cri_cost->cost+ get_action_cost (best_action, best_level, NULL),  n_cost->act_time, 
						     &vectlevel[level]->level);
	      }
#ifdef __TEST__
	  printf ("\n ''''FACT %d : ", el);
	  print_ft_name (el);
#endif
	}


    }




  //  stop = 4;
  stop = 3;

  if (local_search.apply_stop_in_relaxed_plan==TRUE && (Hvar.weight_facts_define_cost+ Hvar.num_actions_define_cost) > local_search.max_act_incons)
    stop--;

  if (GpG.weight_cost <= 0
      || Hvar.cost_actions_define_cost >= local_search.max_act_cost)
    stop--;

  if (GpG.weight_time <= 0
      || Hvar.time_actions_define_cost >= local_search.max_act_time)
    stop--;

  /**
  if (GpG.weight_timed_fa <= 0 ||  Hvar.timed_facts_define_cost > local_search.max_timed_fa)
    stop--;
  **/

  if (stop <= 0)
    {
      //#ifdef __TEST__
      if (DEBUG4)
	printf ("\n Stop compute_dg_cost ");
      //#endif
      local_search.ls_continue = 0;	// Non esamino ulteriormente gli altri termini di costo dell'elemento del  vicinato

      n_cost->best_action=-1;
    }
#ifdef __TEST__
  else
    printf ("\nContinue compute_dg_cost");
#endif

  return total;

}



/* Calcola il numero di volte che l'azione 'i' deve essere inserita per supportare
   la precondizione 'y'*/

int relaxed_set_best_for_compvar(int i,int y)
{

  int j,k;
  DescNumEff *numeric_effect;
  
  
  k=-1;

  for(j=0;j<gef_conn[i].num_numeric_effects;j++)
 
    {

      numeric_effect = &gef_conn[i].numeric_effects[j];

      if(!GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],y))
	continue;

      switch (gcomp_var_effects[numeric_effect->index].operator)
	{
	 
	case INCREASE_OP:
	 
	  k=(int) ceil((Hvar.common_min_values[gcomp_var[y].second_op] - Hvar.common_max_values[gcomp_var[y].first_op])/Hvar.common_max_values[gcomp_var_effects[numeric_effect->index].second_op]);
	  return k;
  		      
	  break;
	  
	case DECREASE_OP:
	 
	
	  k=(int) - ceil((Hvar.common_max_values[gcomp_var[y].second_op] - Hvar.common_min_values[gcomp_var[y].first_op])/Hvar.common_max_values[gcomp_var_effects[numeric_effect->index].second_op]);
	  return k;		      
	  break;
	
	  
	case SCALE_UP_OP:
	case SCALE_DOWN_OP:
	  printf("\nThis version of LPG doesn't support SCALE_UP and SCALE_DOWN effects\n");
	  exit(0);
	  break;
	  
	case ASSIGN_OP:
	 
	  if(gcomp_var[y].operator==LESS_THAN_OR_EQUAL_OP)
	    if(Hvar.common_min_values[gcomp_var_effects[numeric_effect->index].second_op]<=Hvar.common_max_values[gcomp_var[y].second_op])
	       return 1;
	  if(gcomp_var[y].operator==LESS_THAN_OP)
	    if(Hvar.common_min_values[gcomp_var_effects[numeric_effect->index].second_op]<Hvar.common_max_values[gcomp_var[y].second_op])
	      return 1;

	  if(gcomp_var[y].operator==GREATER_OR_EQUAL_OP)
	    if(Hvar.common_max_values[gcomp_var_effects[numeric_effect->index].second_op]>= Hvar.common_min_values[gcomp_var[y].second_op])
	      return 1;

	  if(gcomp_var[y].operator==GREATER_THAN_OP)
	    if(Hvar.common_max_values[gcomp_var_effects[numeric_effect->index].second_op]> Hvar.common_min_values[gcomp_var[y].second_op])
	      return 1;

	  return k;

	  break;
	default:
	  break;
	} 
    }

  
  return  -1;  
}




/* Individiua la migliore azione nella costruzione del piano rilassato, per supportare
   il vincolo numerico in posizione 'Fact_position' e inserisce in 'best_action' la migliore azione */

int
choose_best_action_for_unsup_num_fact (int Fact_position, int level,
				       int *best_action, int *best_level,
				       int action_level, float max_time_for_timed_fact)
{
  int curr_level, j;
  static action_set neighbors;
  auto float total, cost;
  int best_act = -1, best_lev = 0, best_act_type;
  int cel;

  //#ifdef __TEST_REACH__	  
  int k;
  //#endif

  node_cost loc_n_cost, best_n_cost;


#ifdef __TEST__
  printf ("\n ***********************Start level %d end lev %d ", level,
	  level);
#endif


  total = 0.0;
  best_act = -1;
  cost=MAX_COST;
  best_n_cost.weight = MAX_COST;
  best_n_cost.act_cost = MAX_COST;
  best_n_cost.act_time = MAX_COST;
  //qui c'era il ciclo for con curr_level da level a 0
  curr_level = level;
  neighbors.num_A = 0;

  create_neighborhood_for_compvar (Fact_position, 1, 0, &neighbors, 1, level);

  //#ifdef __TEST_REACH__	  
  k=0;
  //#endif

  if(neighbors.num_A==0)
    return -1;
  for (j = 0; j < neighbors.num_A; j++)
    {


      cel = neighbors.A[j];

      //#ifdef __TEST_REACH__
      k= relaxed_set_best_for_compvar(cel,-Fact_position);
	  
      if(k<=0)
	k=1;
      //#endif

      if (Hvar.temp_removed_act == cel && neighbors.num_A > 1)
	{
#ifdef __TEST__
	  printf ("\n Non considera azione %d : ", cel);
	  print_op_name (cel);
#endif
	  continue;
	}
      if (CHECK_ACTION_POS (cel, curr_level))
	{
	  if (GpG.accurate_cost <= COMPUTE_ADD_COST)
	    {
	      cost = fast_insertion_action_cost (cel, curr_level, action_level);	//, &loc_n_cost );
	      //#ifdef __TEST_REACH__
	      cost +=k;
	      //#endif
	      loc_n_cost.act_cost = get_action_cost (cel, level, NULL);
	      loc_n_cost.act_time = get_action_time (cel, level);
	    }
	  else
	    {
	      
	      if (GpG.save_action_cost_list)
		cost = evaluate_action_cost_from_list(cel, curr_level, &loc_n_cost, max_time_for_timed_fact, &best_n_cost);
	      else
		cost = best_action_evaluation  (cel, curr_level, &loc_n_cost, max_time_for_timed_fact, &best_n_cost);
	      //#ifdef __TEST_REACH__
	  //    cost +=k;
	      //#endif
 		loc_n_cost.weight+=k;
	    }


	  if (best_n_cost.weight >= loc_n_cost.weight)
	    {
	      if (best_n_cost.weight == loc_n_cost.weight  && weight_cost (&best_n_cost) <= weight_cost (&loc_n_cost))
		continue;
	      best_act = cel;
	      best_lev = curr_level;
	      best_act_type = IS_ACTION;
	      best_n_cost.weight = loc_n_cost.weight;
	      //#ifdef __TEST_REACH__
	     // ** best_n_cost.weight+=k;
	      //#endif

	      best_n_cost.act_cost = loc_n_cost.act_cost;
	      best_n_cost.act_time = loc_n_cost.act_time;

	      //#ifdef __TEST_REACH__
	      best_n_cost.act_cost = loc_n_cost.act_cost+k*get_action_cost(cel, level, NULL);
	      best_n_cost.act_time = loc_n_cost.act_time+k*get_action_time(cel,level);
	      //#endif

	      //#ifdef __TEST__

	      if(DEBUG5)
	      printf
		("\n\n\n Comp_fact_cost  BEST ACT %s  time %d inc %.2f act_cost %.2f act_time %.2f  ",
		 print_op_name_string (best_act, temp_name), best_lev,
		 best_n_cost.weight, best_n_cost.act_cost,
		 best_n_cost.act_time);
	      //#endif
	      if (best_n_cost.weight <= 0)
		break;		// Non esamino ulteriori candidati 
	    }
	}
#ifdef __TEST__
      else
	{
	  printf
	    ("\n L'azione %s non puo' essere applicata al livello %d, lev: %d",
	     print_op_name_string (cel, temp_name), curr_level,
	     gef_conn[cel].level);
	}
#endif
    }



  *best_action = best_act;
  *best_level = best_lev;

  //#ifdef __TEST_REACH__
  return k;
  //#endif

  return 1.0;
}



void build_relaxed_plan_for_next_goals( int level )
{

  int el, j; 


  if(DEBUG5)
    printf("\n\n\n    START build_relaxed_plan_for_next_goals  level %d ", level);

  if(vectlevel[level]-> step_computed_actions_for_next_goals==GpG.count_num_try)
    return; // Il costo di raggiungibilita' e' stato gia' calcolato


  local_search.apply_stop_in_relaxed_plan=FALSE;
  local_search.ls_continue=TRUE;
  Hvar.cost_actions_define_cost = 0.0;
  Hvar.time_actions_define_cost = 0.0;

  // resetto variabili per calcorare il costo delle precondizioni 
  Hvar.num_actions_define_cost = 0;
  Hvar.num_facts_define_cost = 0;
  Hvar.weight_facts_define_cost = 0.0;
  Hvar.timed_facts_define_cost = 0.0;
  
  reset_bitarray (Hvar.bit_vect_facts, gnum_ft_block);
  reset_bitarray (Hvar.bit_vect_actions, gnum_ef_block);
  
 
  reset_supported_preconds();
  
  //copio i valori del livello di action
  memcpy (Hvar.common_max_values, vectlevel[level]->numeric->values,
	  gnum_comp_var * sizeof (float));

  memcpy (Hvar.common_min_values, vectlevel[level]->numeric->values,
	  gnum_comp_var * sizeof (float));


  reset_bitarray( Hvar.common_level_supported_numeric_preconditions,gnum_block_compvar);


  memcpy(Hvar.initial_relaxed_bit_vect_facts, vectlevel[level] -> fact_vect, gnum_ft_block * sizeof(int));

  memcpy(Hvar.relaxed_bit_vect_preconds, vectlevel[level] -> prec_vect, gnum_ft_block * sizeof(int));


  for (j = 0; j < GpG.num_false_fa; j++)
    {

      if (level > *unsup_fact[j]->level)
	continue;		//inconsistenza ad un livello inferiore

      el=unsup_fact[j]->fact;


      if(!GET_BIT(vectlevel[level]->prec_vect,el))
	continue; // Il fatto non e' precondizione di azioni dei liveli successivi
      
      if (el < 0)
	{
	  if (is_num_prec_satisfied_in_common_level (el))
	    continue;
	}
      else if (is_fact_supported_in_relaxed_plan (el, level))
	{
	  //#ifdef __TEST__
	  if (DEBUG5)
	    printf ("\n Level %d Supported fact %s - 1", level,
		    print_ft_name_string (el, temp_name));
	  //#endif  

	  continue;
	}

      if (el >= 0  && GET_BIT (Hvar.bit_vect_facts, el))
	{
	  //#ifdef __TEST__
	  if(DEBUG5)
	    printf
	    ("\nFact %s already supported in COMPUTE_DG_LIST_COST, level %d",
	     print_ft_name_string (el, temp_name), level);
	  //#endif
	  continue;
	}

      
      /*
	loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
	Azzero loc_n_cost
    
      loc_n_cost.weight = 0.0;
      loc_n_cost.act_cost = 0.0;
      loc_n_cost.act_time = 0.0;

      loc_n_cost.action=GOAL_ACTION;
      compute_relaxed_fact_cost(el, level, &loc_n_cost, level, 0);
      */

      build_fast_relaxed_plan_for_fact(el, level,  level);



    }


  vectlevel[level] ->num_actions_for_next_goals= Hvar.num_actions_define_cost;
  vectlevel[level] ->seach_cost_for_next_goals= Hvar.weight_facts_define_cost + Hvar.num_actions_define_cost;
  vectlevel[level] ->cost_actions_for_next_goals=Hvar.cost_actions_define_cost;
  vectlevel[level] ->step_computed_actions_for_next_goals=GpG.count_num_try;


  if(DEBUG5)
    printf("\n END build  search cost %f num act %d cost %f \n\n\n\n",vectlevel[level] ->seach_cost_for_next_goals,vectlevel[level] ->num_actions_for_next_goals,vectlevel[level] ->cost_actions_for_next_goals );
  
  local_search.apply_stop_in_relaxed_plan=TRUE;
}

void build_relaxed_plan_from_action_for_next_goals(neighb_list neighb_act, node_cost_list n_cost )
{

  int el, level, j;

  register EfConn *act;

  level=neighb_act->act_level;
  act = &gef_conn[neighb_act->act_pos];

  if (neighb_act->constraint_type == C_T_REMOVE_ACTION)
    {

      if(DEBUG5)
	printf("\n\n\n\n START  build REMOVE action %d - %s level %d ", neighb_act->act_pos, print_op_name_string(neighb_act->act_pos,temp_name),neighb_act->act_level);

      build_relaxed_plan_for_next_goals( level+1);
      
      n_cost->weight=vectlevel[level+1] ->seach_cost_for_next_goals;
      n_cost->num_actions= vectlevel[level+1] ->num_actions_for_next_goals;
      n_cost->act_cost= vectlevel[level+1]->cost_actions_for_next_goals;
      
       if(DEBUG5)
	 printf("\n END build  REMOVE search cost %f num act %d cost %f\n\n\n\n",n_cost->weight, n_cost->num_actions, n_cost->act_cost);
      return;
    }




  if(DEBUG5)
    printf("\n\n\n\n START build_relaxed_plan_from_action_for_next_goals action %d - %s level %d ", neighb_act->act_pos, print_op_name_string(neighb_act->act_pos,temp_name),neighb_act->act_level);

  local_search.apply_stop_in_relaxed_plan=FALSE;
  local_search.ls_continue=TRUE;

  Hvar.cost_actions_define_cost = 0.0;
  Hvar.time_actions_define_cost = 0.0;

  // resetto variabili per calcorare il costo delle precondizioni 
  Hvar.num_actions_define_cost = 0;
  Hvar.num_facts_define_cost = 0;
  Hvar.weight_facts_define_cost = 0.0;
  Hvar.timed_facts_define_cost = 0.0;
  
  reset_bitarray (Hvar.bit_vect_facts, gnum_ft_block);
  reset_bitarray (Hvar.bit_vect_actions, gnum_ef_block);
  
  reset_supported_preconds();

  memcpy(Hvar.initial_relaxed_bit_vect_facts, vectlevel[level] -> fact_vect, gnum_ft_block * sizeof(int));

  memcpy(Hvar.relaxed_bit_vect_preconds, vectlevel[level] -> prec_vect, gnum_ft_block * sizeof(int));

  //copio i valori del livello di action
  memcpy (Hvar.common_max_values, vectlevel[level]->numeric->values,
	  gnum_comp_var * sizeof (float));

  memcpy (Hvar.common_min_values, vectlevel[level]->numeric->values,
	  gnum_comp_var * sizeof (float));
  reset_bitarray( Hvar.common_level_supported_numeric_preconditions,gnum_block_compvar);




  // Applico gli effetti di neighb_act


  if (gef_conn[act->position].sf)
    for (j = 0; j < gef_conn[act->position].sf->num_A_start; j++)
      {
	el = gef_conn[act->position].sf->A_start[j];
	if (el < 0)
	  {
	    // Applico  eff in common level 
	    //CAZZO Da sostituire con applicazione effetti normali...
	    apply_numeric_effect_in_common_level (el,1);
	    continue;	// LAZZA
	  }

	if (is_fact_in_delete_effects (act->position, el))
	  continue;


	SET_BIT (Hvar.initial_relaxed_bit_vect_facts, el);

#ifdef __TEST__
	printf ("\n ''''FACT %d : ", el);
	print_ft_name (el);
#endif


      }




  //Rimozionie dei fatti iniziali mutex con act
  remove_action_mutex_facts_in_bitvect(act->position, Hvar.initial_relaxed_bit_vect_facts);




  for (j = 0; j < gef_conn[act->position].num_A; j++)
    {
      el = gef_conn[act->position].A[j];
      if (el < 0)
	{
	  // Applico  eff in common level, 1 volta (l'azione stessa)
	  apply_numeric_effect_in_common_level (el,1);
	  continue;	// LAZZA
	}



      SET_BIT (Hvar.initial_relaxed_bit_vect_facts, el);

#ifdef __TEST__
      printf ("\n ''''FACT %d : ", el);
      print_ft_name (el);
#endif


    }

  for (j = 0; j < GpG.num_false_fa; j++)
    {

      if (level > *unsup_fact[j]->level)
	continue;		//inconsistenza ad un livello inferiore

      el=unsup_fact[j]->fact;

      if(!GET_BIT(vectlevel[level]->prec_vect,el))
	continue; // Il fatto non e' precondizione di azioni dei liveli successivi
      
      if (el < 0)
	{
	  if (is_num_prec_satisfied_in_common_level (el))
	    continue;
	}
      else if (fact_is_supported (el, level))
	{
	  //#ifdef __TEST__
	  if (DEBUG5)
	    printf ("\n Level %d Supported fact %s - 1", level,
		    print_ft_name_string (el, temp_name));
	  //#endif  

	  continue;
	}

      if (el >= 0  && GET_BIT (Hvar.bit_vect_facts, el))
	{
	  //#ifdef __TEST__
	  if(DEBUG5)
	    printf
	    ("\nFact %s already supported in COMPUTE_DG_LIST_COST, level %d",
	     print_ft_name_string (el, temp_name), level);
	  //#endif
	  continue;
	}

      
      /*
	loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
	Azzero loc_n_cost
  
      loc_n_cost.weight = 0.0;
      loc_n_cost.act_cost = 0.0;
      loc_n_cost.act_time = 0.0;
      loc_n_cost.action=GOAL_ACTION;

      compute_relaxed_fact_cost (el, level, &loc_n_cost, level, 0);
      */
      
      build_fast_relaxed_plan_for_fact(el, level,  level);



    }
  n_cost->weight=Hvar.weight_facts_define_cost + Hvar.num_actions_define_cost;
  n_cost->num_actions= Hvar.num_actions_define_cost;
  n_cost->act_cost=Hvar.cost_actions_define_cost;
     
  if(DEBUG5)
    printf("\n END build INSERT search cost %f num act %d cost %f \n\n\n\n",n_cost->weight, n_cost->num_actions, n_cost->act_cost);

  local_search.apply_stop_in_relaxed_plan=TRUE;
}


void reset_supported_preconds()
{

  if(Hvar.num_supported_preconds!=0)  
    reset_bitarray(Hvar.supported_bit_vect_preconds,gnum_ft_block);

  Hvar.num_supported_preconds=0;
  
}


void insert_supported_preconds(int fact)
{
  
  if(GpG.supported_preconds_evaluation==0)
    return;

  if(fact<0)
    return;

  if(GET_BIT(Hvar.supported_bit_vect_preconds,fact))
    Hvar.supported_preconds[fact]++;
  else
    {
      SET_BIT(Hvar.supported_bit_vect_preconds,fact);
      Hvar.supported_preconds[fact]=1;
      Hvar.num_supported_preconds++;
    }

}

void update_supported_precond_for_action(int action)
{
  int i, el;


  if( Hvar.num_supported_preconds==0)
    return;

  for (i = 0; i < gef_conn[action].num_PC; i++)
    {
      el = gef_conn[action].PC[i];
      if (el < 0)
	continue;

      if(GET_BIT(Hvar.supported_bit_vect_preconds,el))
	{
	  Hvar.supported_preconds[el]--;
	  if(Hvar.supported_preconds[el]==0)
	    {
	      Hvar.num_supported_preconds--;
	      RESET_BIT(Hvar.supported_bit_vect_preconds,el);
	    }

	}
    }


  // **** Precondizioni OVERALL
  if (gef_conn[action].sf != NULL)
    {
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{
	  el = gef_conn[action].sf->PC_overall[i];

	  if (el < 0)
	    continue;
		  
	  if(GET_BIT(Hvar.supported_bit_vect_preconds,el))
	    {
	      Hvar.supported_preconds[el]--;
	      if(Hvar.supported_preconds[el]==0)
		{
		  Hvar.num_supported_preconds--;
		  RESET_BIT(Hvar.supported_bit_vect_preconds,el);
		}
		      
	    }
	}



      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	{
	  el = gef_conn[action].sf->PC_end[i];

	  //LAZZA
	  if (el < 0)
	    continue;
		  
	  if(GET_BIT(Hvar.supported_bit_vect_preconds,el))
	    {
	      Hvar.supported_preconds[el]--;
	      if(Hvar.supported_preconds[el]==0)
		{
		  Hvar.num_supported_preconds--;
		  RESET_BIT(Hvar.supported_bit_vect_preconds,el);
		}
	    }
	}


    }


}



int 
build_fast_relaxed_plan_for_fact ( int fact_pos, int level, int orig_level )
{

  // Controllo che le azioni non siano in conflitto con le inconsistenze presenti ai livelli successivi, viceversa incremento num_constr


  int  i, lev1, action, el, me;
  dg_inform_list loc_dg_cost = NULL;
  static float cost;
 
  if(fact_pos<0)
    return 0; //CAZZO Estendere per domini numerici


  if(is_fact_supported_in_relaxed_plan (fact_pos, level))
    return 0;



  lev1 = get_dg_fact_cost (fact_pos, level+1, &loc_dg_cost);


  if(loc_dg_cost==NULL)
    {

      Hvar.weight_facts_define_cost++;
      return 0;
    }


  action = loc_dg_cost->best_act;


  if (action < 0 )
    {
      //      if(action!=INITIAL_ACTION)
	Hvar.weight_facts_define_cost++;

#ifdef __TEST__
      printf ("\n INIT ACTION");
#endif
      return 0;			// azione precedentem. inserita
    }


#ifdef __TEST__
  printf ("\n Action:: %s",print_op_name_string (action, temp_name) );
  printf (" cost %.2f num_act %d duration %.2f for fact %d : ",
	  loc_dg_cost->cost, loc_dg_cost->num_actions, loc_dg_cost->duration,
	  fact_pos);
  print_ft_name (fact_pos);

#endif

 

  i=insert_action_inlist(action,fact_pos);
  if(i==0)
    {


      Hvar.weight_facts_define_cost++;

#ifdef __TEST__
      printf ("\n Insert prec action");
#endif
      return 0;			// azione precedentem. inserita
    }
  else
    if(i<0)
      {
	 Hvar.weight_facts_define_cost=MAX_COST;
	 return MAX_COST;
      }



  if(DEBUG5)
    printf("\n Insert ACTION in relaxed plan %d -- %s ", action, print_op_name_string(action, temp_name));

  if(GpG.verify_inc_choice)
    cost+=1.0;
  else
    cost += get_action_cost (action, level, NULL);


  for (i = 0; i < gef_conn[action].num_PC; i++)
    {
      el = gef_conn[action].PC[i];
      if (el < 0)
	continue;		// LAZZA

      if(GET_BIT (Hvar.bit_vect_facts, el))
	continue;


      if (is_fact_supported_in_relaxed_plan  (el, lev1))
	{
#ifdef __TEST__
	  printf ("\n Supported fact %s lev %d",
		  print_ft_name_string (el, temp_name), level);
#endif

	      SET_BIT (Hvar.bit_vect_facts, el);

	
	  continue;
	}

       build_fast_relaxed_plan_for_fact  ( el, lev1, orig_level);

    }




  if (gef_conn[action].sf)
    for (i = 0; i < gef_conn[action].sf->num_A_start; i++)
      {
	el = gef_conn[action].sf->A_start[i];
	
	if (el < 0)
	  {
	  continue;	
	  }

	if(DEBUG5)
	  printf("\n Insert fact %d-- %s ",el, print_ft_name_string(el, temp_name));
	
	SET_BIT (Hvar.bit_vect_facts, el);

	

      }

  if (gef_conn[action].sf != NULL)
    {
      // Precondizioni OVERALL
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{
	  el = gef_conn[action].sf->PC_overall[i];
	  if (el < 0)
	    continue;		// LAZZA

	  if (is_fact_in_additive_effects_start
	      (action, gef_conn[action].sf->PC_overall[i]))
	    continue;

	  if(GET_BIT (Hvar.bit_vect_facts, el))
	    continue;


	  if (is_fact_supported_in_relaxed_plan  (el, lev1))
	    {
#ifdef __TEST__
	  printf ("\n Supported fact %s lev %d",
		  print_ft_name_string (el, temp_name), level);
#endif

	      SET_BIT (Hvar.bit_vect_facts, el);

	
	      continue;
	    }

	  build_fast_relaxed_plan_for_fact  ( el, lev1, orig_level);




	}

      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	{
	  el = gef_conn[action].sf->PC_end[i];
	  if (el < 0)
	    continue;		// LAZZA
	  if (is_fact_in_additive_effects_start (action, gef_conn[action].sf->PC_end[i]))
	    continue;

	  if(GET_BIT (Hvar.bit_vect_facts, el))
	    continue;


	  if (is_fact_supported_in_relaxed_plan  (el, lev1))
	    {
#ifdef __TEST__
	  printf ("\n Supported fact %s lev %d",
		  print_ft_name_string (el, temp_name), level);
#endif

	      SET_BIT (Hvar.bit_vect_facts, el);

	
	      continue;
	    }

	  build_fast_relaxed_plan_for_fact  ( el, lev1, orig_level);

	}
    }



  for (i = 0; i < gef_conn[action].num_A; i++)
    {
      el = gef_conn[action].A[i];
      if (el < 0)
	{
	  continue;	
	}

      SET_BIT (Hvar.bit_vect_facts, el);


    }
  
  if (FALSE && GpG.inc_choice_type == MIN_LEVEL_MIN_CONSTR_INC)
    { 

       for (  me = 0, i = 0; i < gnum_ft_block; i++)
	 me+=  count_bit1 (CONVERT_ACTION_TO_VERTEX (action)->ft_exclusive_vect[i] & vectlevel[orig_level]->fact_vect[i]);


      if(me>0 && DEBUG5)
	printf("\n  ME %d  act %d -- %s level %d ", me, action, print_op_name_string(action, temp_name), orig_level );
	
    }
  //#ifdef __TEST__
  if(DEBUG5 && initialize)
    {
      printf("\n Fact %d - %s level %d ",  fact_pos, print_ft_name_string( fact_pos, temp_name), level);
      printf ("  Total   cost %f ",  cost);
    }

  //#endif


  return Hvar.num_actions_define_cost;
  
}




int 
compute_relaxed_plan_for_inconsistence ( int fact_pos,int constraint, int level, int orig_level, int initialize)
{

  // Controllo che le azioni non siano in conflitto con le inconsistenze presenti ai livelli successivi, viceversa incremento num_constr

  int  i, lev1, action, el;
  dg_inform_list loc_dg_cost = NULL;
  static int * reachability_inform_for_facts=NULL;
  static float cost;
  static int *depth_actions_in_relaxed_plan=NULL;
  static int max_depth;

  if (initialize==0)
    {
      reset_bitarray (Hvar.bit_vect_actions, gnum_ef_block);
      reset_bitarray (Hvar.bit_vect_facts,gnum_ft_block);
      cost=0.0;
      Hvar.num_actions_define_cost=0;
      Hvar.cost_actions_define_cost=0.0; 
      cost=0.0;

      if(depth_actions_in_relaxed_plan==NULL)
        depth_actions_in_relaxed_plan= (int *) calloc (MAX_LENGTH_H, sizeof (int));

      max_depth=0;
    }
  else
    {
      if(initialize> max_depth)
	max_depth=initialize;
    }


  if( reachability_inform_for_facts==NULL)
    {
      reachability_inform_for_facts= ( int * ) calloc( gnum_ft_conn, sizeof( int ) );
      memset(reachability_inform_for_facts,0,gnum_ft_conn* sizeof( int )); 

    }

#ifdef __TEST__



  if(initialize)
    printf("START ");
  printf (" Compute constr of ");
  print_ft_name (fact_pos);
#endif


  lev1 = get_dg_fact_cost (fact_pos, level+1, &loc_dg_cost);



  action = loc_dg_cost->best_act;


  if (action < 0)
    {

#ifdef __TEST__
      printf ("\n INIT ACTION");
#endif
      return 0;			// azione precedentem. inserita
    }


#ifdef __TEST__
  printf ("\n Action:: %s",print_op_name_string (action, temp_name) );
  printf (" cost %.2f num_act %d duration %.2f for fact %d : ",
	  loc_dg_cost->cost, loc_dg_cost->num_actions, loc_dg_cost->duration,
	  fact_pos);
  print_ft_name (fact_pos);

#endif

  if (GET_BIT (Hvar.bit_vect_actions, action))
    {

#ifdef __TEST__
      printf ("\n Insert prec action");
#endif
      return 0;			// azione precedentem. inserita
    }



  depth_actions_in_relaxed_plan[Hvar.num_actions_define_cost]=initialize;


  if(insert_action_inlist(action,fact_pos)==0)
    return 0;
    

  if(DEBUG5)
    printf("\n Insert ACTION in relaxed plan %d -- %s ", action, print_op_name_string(action, temp_name));

  if(GpG.verify_inc_choice)
    cost+=1.0;
  else
    cost += get_action_cost (action, level, NULL);


  for (i = 0; i < gef_conn[action].num_PC; i++)
    {
      el = gef_conn[action].PC[i];
      if (el < 0)
	continue;		// LAZZA

      if(GET_BIT (Hvar.bit_vect_facts, el))
	continue;


      if (fact_is_supported (el, lev1))
	{
#ifdef __TEST__
	  printf ("\n Supported fact %s lev %d",
		  print_ft_name_string (el, temp_name), level);
#endif

	      SET_BIT (Hvar.bit_vect_facts, el);

	      
	      reachability_inform_for_facts[el]= 0;

	  continue;
	}

       compute_relaxed_plan_for_inconsistence ( el, constraint,lev1, orig_level,  initialize+1);

    }




  if (gef_conn[action].sf)
    for (i = 0; i < gef_conn[action].sf->num_A_start; i++)
      {
	el = gef_conn[action].sf->A_start[i];
	
	if (el < 0)
	  {
	  continue;	
	  }

	if(DEBUG5)
	  printf("\n Insert fact %d-- %s ",el, print_ft_name_string(el, temp_name));
	
	SET_BIT (Hvar.bit_vect_facts, el);

	get_dg_fact_cost (el, orig_level, &loc_dg_cost);
	
	reachability_inform_for_facts[el]= loc_dg_cost->num_actions;

      }

  if (gef_conn[action].sf != NULL)
    {
      // Precondizioni OVERALL
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{
	  el = gef_conn[action].sf->PC_overall[i];
	  if (el < 0)
	    continue;		// LAZZA

	  if (is_fact_in_additive_effects_start
	      (action, gef_conn[action].sf->PC_overall[i]))
	    continue;

	  if(GET_BIT (Hvar.bit_vect_facts, el))
	    continue;


	  if (fact_is_supported (el, lev1) )
	    {
#ifdef __TEST__
	      printf ("\n Supported fact %s lev %d",
		      print_ft_name_string (el, temp_name), level);
#endif

	      SET_BIT (Hvar.bit_vect_facts, el);

	      reachability_inform_for_facts[el]= 0;

	      continue;
	    }

	   compute_relaxed_plan_for_inconsistence ( el,constraint, lev1,  orig_level,  initialize+1);

	}

      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	{
	  el = gef_conn[action].sf->PC_end[i];
	  if (el < 0)
	    continue;		// LAZZA
	  if (is_fact_in_additive_effects_start (action, gef_conn[action].sf->PC_end[i]))
	    continue;

	  if(GET_BIT (Hvar.bit_vect_facts, el))
	    continue;



	  if (fact_is_supported (el, lev1))
	    {
#ifdef __TEST__
	      printf ("\n Supported fact %s lev %d",
		      print_ft_name_string (el, temp_name), level);
#endif


	      SET_BIT (Hvar.bit_vect_facts, el);

	      reachability_inform_for_facts[el]= 0;

	      continue;
	    }

	   compute_relaxed_plan_for_inconsistence( el,constraint,  lev1, orig_level,  initialize+1);
	}
    }



  for (i = 0; i < gef_conn[action].num_A; i++)
    {
      el = gef_conn[action].A[i];
      if (el < 0)
	{
	  continue;	
	}

      SET_BIT (Hvar.bit_vect_facts, el);

      get_dg_fact_cost (el, orig_level, &loc_dg_cost);

      reachability_inform_for_facts[el]= loc_dg_cost->num_actions;

    }
  

#ifdef __TEST__
  if(DEBUG5 && initialize)
    {
      printf("\n Fact %d - %s level %d ",  fact_pos, print_ft_name_string( fact_pos, temp_name), level);
      printf ("  Total   cost %f ",  cost);
    }
#endif




  if(initialize == 0)
    {
      compute_relaxed_plan_for_inconsistence( constraint,constraint, lev1, orig_level,  initialize+1);

    }
  
  return Hvar.num_actions_define_cost;
  
}




int 
fast_relaxed_plan_for_inconsistence ( int fact_pos, int level, int initialize)
{

  // Controllo che le azioni non siano in conflitto con le inconsistenze presenti ai livelli successivi, viceversa incremento num_constr

  int  i,  action, el;
  dg_inform_list loc_dg_cost = NULL;
  static int * reachability_inform_for_facts=NULL;
  static float cost;
  static int *depth_actions_in_relaxed_plan=NULL;
  static int max_depth;

  if (initialize==0)
    {
      reset_bitarray (Hvar.bit_vect_actions, gnum_ef_block);
      reset_bitarray (Hvar.bit_vect_facts,gnum_ft_block);
      cost=0.0;
      Hvar.num_actions_define_cost=0;
      Hvar.cost_actions_define_cost=0.0; 
      cost=0.0;

      if(depth_actions_in_relaxed_plan==NULL)
        depth_actions_in_relaxed_plan= (int *) calloc (MAX_LENGTH_H, sizeof (int));

      max_depth=0;
    }
  else
    {
      if(initialize> max_depth)
	max_depth=initialize;
    }


  if( reachability_inform_for_facts==NULL)
    {
      reachability_inform_for_facts= ( int * ) calloc( gnum_ft_conn, sizeof( int ) );
      memset(reachability_inform_for_facts,0,gnum_ft_conn* sizeof( int )); 

    }

#ifdef __TEST__



  if(initialize)
    printf("START ");
  printf (" Compute constr of ");
  print_ft_name (fact_pos);
#endif


   get_dg_fact_cost (fact_pos, level+1, &loc_dg_cost);



  action = loc_dg_cost->best_act;


  if (action < 0)
    {

#ifdef __TEST__
      printf ("\n INIT ACTION");
#endif
      return 0;			// azione precedentem. inserita
    }


#ifdef __TEST__
  printf ("\n Action:: %s",print_op_name_string (action, temp_name) );
  printf (" cost %.2f num_act %d duration %.2f for fact %d : ",
	  loc_dg_cost->cost, loc_dg_cost->num_actions, loc_dg_cost->duration,
	  fact_pos);
  print_ft_name (fact_pos);

#endif

  if (GET_BIT (Hvar.bit_vect_actions, action))
    {

#ifdef __TEST__
      printf ("\n Insert prec action");
#endif
      return 0;			// azione precedentem. inserita
    }



  depth_actions_in_relaxed_plan[Hvar.num_actions_define_cost]=initialize;


  if(insert_action_inlist(action,fact_pos)==0)
    return 0;
    

  if(DEBUG5)
    printf("\n Insert ACTION in relaxed plan %d -- %s ", action, print_op_name_string(action, temp_name));

  if(GpG.verify_inc_choice)
    cost+=1.0;
  else
    cost += get_action_cost (action, level, NULL);


  for (i = 0; i < gef_conn[action].num_PC; i++)
    {
      el = gef_conn[action].PC[i];
      if (el < 0)
	continue;		// LAZZA

      if(GET_BIT (Hvar.bit_vect_facts, el))
	continue;


      if (fact_is_supported (el, level))
	{
#ifdef __TEST__
	  printf ("\n Supported fact %s lev %d",
		  print_ft_name_string (el, temp_name), level);
#endif

	      SET_BIT (Hvar.bit_vect_facts, el);

	      SET_BIT (Hvar.initial_supported_facts_relaxed_plan_bit_vector , el);

	      reachability_inform_for_facts[el]= 0;

	  continue;
	}

       fast_relaxed_plan_for_inconsistence ( el, level,  initialize+1);

    }




  if (gef_conn[action].sf)
    for (i = 0; i < gef_conn[action].sf->num_A_start; i++)
      {
	el = gef_conn[action].sf->A_start[i];
	
	if (el < 0)
	  {
	  continue;	
	  }

	if(DEBUG5)
	  printf("\n Insert fact %d-- %s ",el, print_ft_name_string(el, temp_name));
	
	SET_BIT (Hvar.bit_vect_facts, el);

	get_dg_fact_cost (el, level, &loc_dg_cost);
	
	reachability_inform_for_facts[el]= loc_dg_cost->num_actions;

      }

  if (gef_conn[action].sf != NULL)
    {
      // Precondizioni OVERALL
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{
	  el = gef_conn[action].sf->PC_overall[i];
	  if (el < 0)
	    continue;		// LAZZA

	  if (is_fact_in_additive_effects_start
	      (action, gef_conn[action].sf->PC_overall[i]))
	    continue;

	  if(GET_BIT (Hvar.bit_vect_facts, el))
	    continue;


	  if (fact_is_supported (el, level) )
	    {
#ifdef __TEST__
	      printf ("\n Supported fact %s lev %d",
		      print_ft_name_string (el, temp_name), level);
#endif

	      SET_BIT (Hvar.bit_vect_facts, el);

	      SET_BIT (Hvar.initial_supported_facts_relaxed_plan_bit_vector , el);

	      reachability_inform_for_facts[el]= 0;

	      continue;
	    }

	   fast_relaxed_plan_for_inconsistence ( el,level,  initialize+1);

	}

      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	{
	  el = gef_conn[action].sf->PC_end[i];
	  if (el < 0)
	    continue;		// LAZZA
	  if (is_fact_in_additive_effects_start (action, gef_conn[action].sf->PC_end[i]))
	    continue;

	  if(GET_BIT (Hvar.bit_vect_facts, el))
	    continue;



	  if (fact_is_supported (el, level))
	    {
#ifdef __TEST__
	      printf ("\n Supported fact %s lev %d",
		      print_ft_name_string (el, temp_name), level);
#endif


	      SET_BIT (Hvar.bit_vect_facts, el);


	      SET_BIT (Hvar.initial_supported_facts_relaxed_plan_bit_vector , el);


	      reachability_inform_for_facts[el]= 0;

	      continue;
	    }

	   fast_relaxed_plan_for_inconsistence( el,level,  initialize+1);
	}
    }



  for (i = 0; i < gef_conn[action].num_A; i++)
    {
      el = gef_conn[action].A[i];
      if (el < 0)
	{
	  continue;	
	}

      SET_BIT (Hvar.bit_vect_facts, el);

      get_dg_fact_cost (el, level, &loc_dg_cost);

      reachability_inform_for_facts[el]= loc_dg_cost->num_actions;

    }
  

#ifdef __TEST__
  if(DEBUG5 && initialize)
    {
      printf("\n Fact %d - %s level %d ",  fact_pos, print_ft_name_string( fact_pos, temp_name), level);
      printf ("  Total   cost %f ",  cost);
    }
#endif




   
  return Hvar.num_actions_define_cost;
  
}



void define_supported_fact_for_relaxed_plan_of_inconsistences(constraints_list const_fact, int initialize)
{

  int i, temp1, level;

  if( GpG.consider_relaxed_plan_for_inconsistences==FALSE )
    return;


  if(const_fact->constraint_type!= C_T_UNSUP_FACT  && const_fact->constraint_type!=C_T_UNSUP_NUM_FACT)
    return;

  
  if(const_fact->constraint_type == C_T_UNSUP_NUM_FACT)
    return; // Per ora non considero inconsistenze numeriche
    
  if(const_fact->constraint_type == C_T_TREATED_CL)
    return; // Per ora non considero threated facts

  level=*const_fact->level ;


  if(const_fact->supported_facts_relaxed_plan_bit_vector==NULL)
    {
      const_fact->supported_facts_relaxed_plan_bit_vector= alloc_vect (gnum_ft_block);
      const_fact->relaxed_plan_actions_bit_vector= alloc_vect (gnum_ef_block);
    }


  if(!initialize)
    {
      // Verifico se i fatti appartenenti al piano rilassato calcolati in precedenza sono ancora validi 

       for (i=0; i < gnum_ft_block; i++)
	  {
	    temp1 = const_fact->supported_facts_relaxed_plan_bit_vector[i] & (!vectlevel[level]->fact_vect[i]);

	    if(temp1)
	      {
		initialize=TRUE; // Un fatto che e' necessario per il piano rilassato non e' piu' vero e quindi ricalcolo piano rilassato nel buovo stato
		break;
	      }
	  }

       if(initialize==FALSE) // Nessun fatto e' stato invalidato
	 return;

    }


  // Construisco piano rilassato per inconsistenza

  reset_bitarray(const_fact->supported_facts_relaxed_plan_bit_vector,gnum_ft_block); 

  Hvar.initial_supported_facts_relaxed_plan_bit_vector=const_fact->supported_facts_relaxed_plan_bit_vector; // Questo bit vecyor viene impostato durante  fast_relaxed_plan_for_inconsistence inserendo i fatti che sono supportati al livello corrente nel piano rilassato
  fast_relaxed_plan_for_inconsistence (const_fact->fact, level, 0);



  memcpy(const_fact->relaxed_plan_actions_bit_vector, Hvar.bit_vect_actions, gnum_ef_block * sizeof(int));


  Hvar.initial_supported_facts_relaxed_plan_bit_vector=NULL; // Azzero il puntatore per evitare accidentali impostazioni
  

}


void search_step_check_supported_fact_in_relaxed_plan_for_inconsistences()
{
  int i;

  if( GpG.consider_relaxed_plan_for_inconsistences==FALSE )
    return;

   for (i = GpG.num_false_fa - 1; i >= 0; i--)
     define_supported_fact_for_relaxed_plan_of_inconsistences(unsup_fact[i], FALSE); // Verifico se i fatti considerati nel piano supportato per calcolare inconssitenza sono supportati altrimenti ricalcolo piano rilassato


   return; //Per ora non considero prec numeriche e threats

 for (i=0;i<GpG.num_false_num_fa;i++)
      define_supported_fact_for_relaxed_plan_of_inconsistences(unsup_num_fact[i], FALSE); // Verifico se i fatti considerati nel piano supportato per calcolare inconssitenza sono supportati altrimenti ricalcolo piano rilassato

 for (i=0;i<GpG.num_false_act;i++) 
   define_supported_fact_for_relaxed_plan_of_inconsistences(treated_c_l[i], FALSE); // Verifico se i fatti considerati nel piano supportato per calcolare inconssitenza sono supportati altrimenti ricalcolo piano rilassato
 
}


void build_total_supported_facts_relaxed_plan_bit_vector(int action, int level)
{

  int i, j;

  if(Hvar.total_supported_facts_relaxed_plan_bit_vector==NULL)
    Hvar.total_supported_facts_relaxed_plan_bit_vector= alloc_vect (gnum_ft_block);
  else
    reset_bitarray(Hvar.total_supported_facts_relaxed_plan_bit_vector,gnum_ft_block); 


   for (i = GpG.num_false_fa - 1; i >= 0; i--)
     if(action<0 || !GET_BIT( unsup_fact[i]->relaxed_plan_actions_bit_vector, action))
       if( level<= *unsup_fact[i]->level && unsup_fact[i]->supported_facts_relaxed_plan_bit_vector)
	 for(j=0; j< gnum_ft_block; j++)
	   Hvar.total_supported_facts_relaxed_plan_bit_vector[j]|=unsup_fact[i]->supported_facts_relaxed_plan_bit_vector[j];

   

   return; //Per ora non considero prec numeriche e threats


   for (i=0;i<GpG.num_false_num_fa;i++) 
    if(action<0 || !GET_BIT(unsup_num_fact[i]->relaxed_plan_actions_bit_vector, action))
     if( level<= *unsup_num_fact[i]->level && unsup_num_fact[i]->supported_facts_relaxed_plan_bit_vector)
       for(j=0; j< gnum_ft_block; j++)
	 Hvar.total_supported_facts_relaxed_plan_bit_vector[j]|=unsup_num_fact[i]->supported_facts_relaxed_plan_bit_vector[j];


   for (i=0;i<GpG.num_false_act;i++) 
    if(action<0 || !GET_BIT(treated_c_l[i]->relaxed_plan_actions_bit_vector, action))
     if( level<= *treated_c_l[i]->level &&  treated_c_l[i]->supported_facts_relaxed_plan_bit_vector)
       for(j=0; j< gnum_ft_block; j++)
	 Hvar.total_supported_facts_relaxed_plan_bit_vector[j]|=treated_c_l[i]->supported_facts_relaxed_plan_bit_vector[j];

}





void verify_supported_fact_in_relaxed_plan_for_inconsistences(int action, int level, int* bit_vect_supp_fact)
{

  int i, j ,k, temp, el, init_p, init_zero;
  register int temp1;
  node_cost loc_n_cost;
  float init_H; 
  if( GpG.consider_relaxed_plan_for_inconsistences==FALSE )
    return;

  if(action<0)// &&GpG.supported_preconds_evaluation==FALSE)
    return;

  if(Hvar.weight_facts_define_cost>=MAX_COST)
    return;

  init_p=GpG.penalize_inconsistence_in_relaxed_plan;
  GpG.penalize_inconsistence_in_relaxed_plan=FALSE;

  init_zero=GpG.zero_num_A;
  GpG.zero_num_A=TRUE;


  if(DEBUG5)
    {
      printf("\nSTART Define cost for supported facts in relaxed plan for inconsistences ");
      printf("\n Action %d  - %s level %d ", action, print_op_name_string(action, temp_name), level);
      
      printf(" Hvar.weight_facts_define_cost %f --- Hvar.num_actions_define_cost %d ",Hvar.weight_facts_define_cost, Hvar.num_actions_define_cost);
    }

  init_H= Hvar.weight_facts_define_cost + Hvar.num_actions_define_cost;

  build_total_supported_facts_relaxed_plan_bit_vector(action, level);
  
  for ( i= j = 0; i < gnum_ft_block; i++, j+=32)
    {

      /***
	  Identifico i fatti che sono veri, appartenenti piani rilassati inconsistenze  livelli successivi, 
	  mutuamente esclusivi con action e non resi veri ne piano rilassato per action
	  
      ***/
      temp1 = Hvar.total_supported_facts_relaxed_plan_bit_vector[i] & vectlevel[level]->fact_vect[i];
      temp=0;
      if(action>=0)
	temp = CONVERT_ACTION_TO_VERTEX (action)->ft_exclusive_vect[i];

      //	if(GpG.supported_preconds_evaluation)
      //	  temp|=Hvar.threated_bit_vect_facts[i];

      temp1 &= temp;

      // Non considero i fatti che sono resi veri nel piano rilassato
      //      temp1 &= (!bit_vect_supp_fact[i]);

       k = 32;

       while (temp1)
	 {
	   k--;
	   if (temp1 & FIRST_1)
	     {	
	       
	       el=j+k;
	       
	       if (DEBUG5)
		 {
		   printf ("\n\n\n  ------------------FACT : %d  ", el);
		   print_ft_name (el);
		   
		 }
	       
	       
	       /*
		 loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		 Azzero loc_n_cost
	       */
	       loc_n_cost.weight = 0.0;
	       loc_n_cost.act_cost = 0.0;
	       loc_n_cost.act_time = 0.0;
	       
	       compute_relaxed_fact_cost (el, level, &loc_n_cost, level, MAXFLOAT);
	     }
	   temp1 <<= 1;
	 }		// while
       
    }	// for
 
  if(DEBUG5)
    {
      printf("\nEND Define cost for supported facts in relaxed plan for inconsistences ");
      printf("\n Action %d  - %s level %d ", action, print_op_name_string(action, temp_name), level);
      
      printf(" Hvar.weight_facts_define_cost %f --- Hvar.num_actions_define_cost %d ",Hvar.weight_facts_define_cost, Hvar.num_actions_define_cost);
      printf(" --- Delta %f ", Hvar.weight_facts_define_cost + Hvar.num_actions_define_cost- init_H);
    }
 


  GpG.penalize_inconsistence_in_relaxed_plan=init_p;
   GpG.zero_num_A=init_zero;

}


void evaluate_mutex_in_relaxed_plan(int action, int level)
{

  int i, j, k, k1;
  register int temp1;
  node_cost loc_n_cost;
  EfConn *act;
  int cond1, cond2;

  if(action<0)
    return;

  act = &gef_conn[ action ];

  for (i = 0, j = 0; j < gnum_ft_conn; i++, j += 32)
    {

      temp1 =vectlevel[level]->fact_vect[i] & (Hvar.relaxed_bit_vect_preconds[i]);

      k = 32;
      while (temp1)
	{
	  k--;
	  if (temp1 & FIRST_1) 
	    {

	      k1 = j + k;
	   
	      if(GpG.no_mutex_with_additive_effects==FALSE)
		cond1=GET_BIT( act->ft_exclusive_vect, (k1));
	      else
		cond1=GET_BIT( act->ft_exclusive_vect, (k1))&& is_fact_in_additive_effects( act->position ,k1)==FALSE;
	      
	      if(cond1==FALSE)
		cond2=(GpG.supported_preconds_evaluation && GET_BIT(Hvar.threated_bit_vect_facts , (k1)) && !GET_BIT(Hvar.bit_vect_facts , (k1)) );
	      else
		cond2=FALSE;
	      
	      if(cond1 || cond2)
		{
		      
#ifdef __TEST__
		  if (DEBUG6)
		    {
		      printf ("\n\n\n %d ------------------FACT : %d  ",
			      diff, k1);
		      print_ft_name (k1);

		    }
#endif

		  /*
		    loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		    Azzero loc_n_cost
		  */
		  loc_n_cost.weight = 0.0;
		  loc_n_cost.act_cost = 0.0;
		  loc_n_cost.act_time = get_action_time (action, level);
		  loc_n_cost.options=0;

		  compute_relaxed_fact_cost (k1, level, &loc_n_cost, level, MAXFLOAT);
		}
	    }
	  temp1 <<= 1;
	}		// while

    }	// for




}

