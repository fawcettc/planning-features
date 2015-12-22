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
 * File: mutex.c
 * Description: computing mutex relations.
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/





#include "lpg.h"
#include "ComputeReachInf.h"
#include "inst_utils.h"
#include "utilities.h"
#include "output.h"
#include "mutex.h"
#include "numeric.h"
#include "derivedpred.h"
#include "inst_utils.h"

#include "LpgOutput.h"

/********************************
 * POSSIBLY TRUE FACTS ANALYSIS *
 ********************************/

/* PER DEBUG: Stampa la matrice di bit EF_EF_mutex */
int print_EF_EF_mutex(int l)
{
  int r = 0, c = 0;
  for (r = 0; r < l; r++) {
    for (c = 0; c < l; c++)
      printf("%1d ",GET_EF_EF_MX_BIT(r, c));
    printf("\n");
  }
  return 0;
}


int are_mutex_ops (int a, int b)
{
  int i, k;

  //se no lowmemory, leggo direttemante dall'array
  if (!GpG.lowmemory)
    {
      i = GET_EF_EF_MX_BIT (a, b);
      return i;
    }
  else

    
    {
      for (i = 0; i < gef_conn[b].num_PC; i++)
	if (GET_BIT(gef_conn[a].ft_exclusive_vect, gef_conn[b].PC[i]))
	  return TRUE;

      if (gef_conn[b].sf)
	{
	  for (i = 0; i < gef_conn[b].sf->num_PC_end; i++)
	    if (GET_BIT(gef_conn[a].ft_exclusive_vect, gef_conn[b].sf->PC_end[i]))
	      return TRUE;

	   for (i = 0; i < gef_conn[b].sf->num_PC_overall; i++)
	     if (GET_BIT(gef_conn[a].ft_exclusive_vect, gef_conn[b].sf->PC_overall[i]))
	       return TRUE;
	}

     for (i = 0; i < gef_conn[a].num_PC; i++)
	if (GET_BIT(gef_conn[b].ft_exclusive_vect, gef_conn[a].PC[i]))
	  return TRUE;

      if (gef_conn[a].sf)
	{
	  for (i = 0; i < gef_conn[a].sf->num_PC_end; i++)
	    if (GET_BIT(gef_conn[b].ft_exclusive_vect, gef_conn[a].sf->PC_end[i]))
	      return TRUE;

	   for (i = 0; i < gef_conn[a].sf->num_PC_overall; i++)
	     if (GET_BIT(gef_conn[b].ft_exclusive_vect, gef_conn[a].sf->PC_overall[i]))
	       return TRUE;
	}
 
     
      if (gef_conn[a].is_numeric && gef_conn[b].is_numeric)
	{
	  //PARTE NUMERICA   
	  /*non ci devono essere intersezioni tra gli lvalues di a e gli rval di b */
	  for (k = 0; k < gnum_fullnum_blocks; k++)
	    {
	      int l_val_block_a, l_val_block_b;

	      l_val_block_a = get_bit_table_block(l_vals, a, k);
	      
	      if (l_val_block_a)
		{
		  //se aggiorno qualcosa che dall'altra parte sto usando a dx dell'aggiornamento
		  if (l_val_block_a & get_bit_table_block(r_vals, b, k))
		    return TRUE;
	      
		  //se aggiorno qualcosa che dall'altra parte sto testando
		  if (l_val_block_a & get_bit_table_block(tested_vars, b, k))
		    return TRUE;

		  l_val_block_b = get_bit_table_block(l_vals, b, k);

		  if (l_val_block_b)
		    {
		      //se testo qualcosa che dall'altra parte sto aggiornando
		      if (get_bit_table_block(tested_vars, a, k) & l_val_block_b)
			return TRUE;

		      //se La^Lb != La* ^ Lb*, allora a e b sono mutex 
		      if ((l_val_block_a & l_val_block_b) !=
			  (get_bit_table_block(lstar_vals, a, k) & get_bit_table_block(lstar_vals, b, k)))
			return TRUE;
		    }
		}
	    }
	}
      
    }
       
  return FALSE;
}


void calc_mutex_num_efs (void)
{

  initialize_vals_tables();
  set_lvals_and_rvals ();
  
#ifdef __TEST_PDDL__
  print_matrs ();
#endif
}





Bool
are_goal_reachable_and_non_mutex (void)
{
  int i, j;

  GpG.init_plan_length=0;

  for (i = 0; i < ggoal_state.num_F; i++)
   
    if (ggoal_state.F[i]>=0 && gft_conn[ggoal_state.F[i]].level < 0)
      {

	if (!GpG.try_suspected_actions)
	  {
	    printf("\nGoal unreachable %d\n",ggoal_state.F[i]);
	    print_ft_name(ggoal_state.F[i]) ;
	    for(j=0;j<gft_conn[ggoal_state.F[i]].num_PC;j++)
	      {
		printf("\nAzione %d   :",gft_conn[ggoal_state.F[i]].PC[j]);
		print_op_name(gft_conn[ggoal_state.F[i]].PC[j]);
		printf("\nPreco non supportate: %d\n", Numeric.ri_prec_vector[gft_conn[ggoal_state.F[i]].PC[j]]);
		
	      }
	  }
#ifdef __TEST_REACH__
	printf("\n\nADDERS\n");
	for(j=0;j<gft_conn[ggoal_state.F[i]].num_A;j++)
	  {
	    printf("\nAzione %d   :",gft_conn[ggoal_state.F[i]].A[j]);
	    print_op_name(gft_conn[ggoal_state.F[i]].A[j]);
	    printf("\nPreco non supportate %d\n", Numeric.ri_prec_vector[gft_conn[ggoal_state.F[i]].A[j]]);
	  }
#endif

	return FALSE;
      }


  for (i = 0; i < ggoal_state.num_F; i++)
  {
    if(ggoal_state.F[i]<0)
      continue;

    //#ifdef __TEST_REACH__
    if((gft_conn[ggoal_state.F[i]].level-1)>GpG.fixpoint_plan_length)
      GpG.fixpoint_plan_length=gft_conn[ggoal_state.F[i]].level-1;
    //#endif

    if(gft_conn[ggoal_state.F[i]].level>GpG.init_plan_length)
      GpG.init_plan_length=gft_conn[ggoal_state.F[i]].level;

    for (j = i + 1; j < ggoal_state.num_F; j++)
      {
	if(ggoal_state.F[j]<0)
	  continue;

	if (GET_BIT (FT_FT_mutex[ggoal_state.F[i]], ggoal_state.F[j]))
	  {

	    if (!GpG.try_suspected_actions)
	      {
		printf("Mutex Goals: ");
		print_ft_name(ggoal_state.F[i]) ;
		printf("--");
		print_ft_name(ggoal_state.F[j]);
	      }

	    return FALSE;
	  }
      }
  }

  GpG.init_plan_length++;
  return TRUE;
}






/*********************************************************************
Funzione che restituisce il numero di precondizioni dell'azione i-esima
che non sono ancora supportate, utilizzando il vettore di bit  fact_vector
che specifica quali fatti sono veri e quali no.

*********************************************************************/
int 
count_unsatisfied_preconds(int action_number,int *fact_vector) 
{ int i=0;  
  int num_unsatisfied_precond=0;
  EfConn *action_considered= &gef_conn[action_number];
  //  /* Preconditions at start */

  for(i = 0;i < action_considered->num_PC; i++)
    {
      if (action_considered->PC[i]>=0 && !(GET_BIT(fact_vector,action_considered->PC[i])))
	num_unsatisfied_precond++;
    }
  

///* Overall and at end Preconditions */
  if (action_considered->sf!=NULL)
    {
      ///* Looking for Overall PC and controllling if they match with Start PC */
      
      for(i = 0;i<action_considered->sf->num_PC_overall;i++)
	{//I fatti numerici non vengono considerati
	  if(action_considered->sf->PC_overall[i]<0)
	    continue;
       if (GET_BIT(fact_vector,action_considered->sf->PC_overall[i]))
         continue;
       
       //Se il fatto e' gia' stato conteggiato nelle preco il contatore non e' incrementato
       if(is_fact_in_preconditions(action_number,action_considered->sf->PC_overall[i]))
	 continue;
       //Se il fatto e' negli effetti additivi at start il contatore non e' incrementato
       if(is_fact_in_additive_effects_start(action_number,action_considered->sf->PC_overall[i]))
	 continue;
       
       num_unsatisfied_precond++;
       
	}	
      
      
      for (i=0; i<action_considered->sf->num_PC_end;i++)
	
	{  //I fatti numerici non vengono considerati
	  if( action_considered->sf->PC_end[i]<0)
	 continue;
	  ///* Looking for End PC and controllling if they match with At Start and Overall PC */
	  if (GET_BIT(fact_vector,action_considered->sf->PC_end[i]))
	    continue;
	  //Se il fatto e' gia' stato conteggiato nelle preco il contatore non e' incrementato
	  if(is_fact_in_preconditions(action_number,action_considered->sf->PC_end[i]))
	    continue;
	 	 	  
	  //Se il fatto e' gia' stato conteggiato nelle preco-overall il contatore non e' incrementato
	  if(is_fact_in_preconditions_overall(action_number,action_considered->sf->PC_end[i]))
	    continue;
	  //Se il fatto e' negli effetti additivi at start il contatore non e' incrementato
	  if(is_fact_in_additive_effects_start(action_number,action_considered->sf->PC_end[i]))
	    continue;	 
	  
	  
	  num_unsatisfied_precond++;
	}
    }
  return num_unsatisfied_precond;
}









/********************************************************************************
Funzione che determina se l'azione i-esima ha delle precondizioni che risultano 
essere mutex tra loro, in questo caso restituisce il valore TRUE, altrimenti
FALSE. La matrice FT_FT_mutex_pass e' la matrice delle mutue esclusioni tra fatti

*******************************************************************************/

int is_action_prec_mutex(int action_number, int **FT_FT_mutex_pass)
{
  int i,j;
EfConn action_considered= gef_conn[action_number];

 for(i=0;i<action_considered.num_PC;i++)

   {
     for(j=i+1;j<action_considered.num_PC-1;j++)
      if(action_considered.PC[i]>=0 && action_considered.PC[j]>=0 &&
        GET_BIT(FT_FT_mutex_pass[action_considered.PC[i]],action_considered.PC[j]))
	return TRUE;

   }
 if (action_considered.sf!=NULL)
   {
     for(i=0;i<action_considered.sf->num_PC_overall-1;i++)
       
       {
	 for(j=i+1;j<action_considered.sf->num_PC_overall;j++)
	   if(action_considered.sf->PC_overall[i]>=0 && action_considered.sf->PC_overall[j]>=0 &&
          GET_BIT(FT_FT_mutex_pass[action_considered.sf->PC_overall[i]],action_considered.sf->PC_overall[j]))
	     return TRUE;
	 
       }
     
     for(i=0;i<action_considered.sf->num_PC_end-1;i++)
       {
	 for(j=i+1;j<action_considered.sf->num_PC_end;j++)
	   if(action_considered.sf->PC_end[i]>=0 && action_considered.sf->PC_end[j] &&
	    GET_BIT(FT_FT_mutex_pass[action_considered.sf->PC_end[i]],action_considered.sf->PC_end[j]))
	   return TRUE;
       
     }
     
   }
 
 return FALSE;
}

/**********************************************************************************************
  Funzione che inizializza il vettore (num_prec_vector) che contiene il numero
  di preconsdizioni(start, end o overall) non supportate, cioe' non ancora rese vere, di tutte le azioni 
  Se num_prec_vector[2]=3 significa che l'azione numero due ha attualmente tre precondizioni
  non supportate
  Questa funzione richiama attraverso un ciclo la funzione count_unsatisfied_precond(i) che restituisce
  il numero di prec. false dell'azione i

**********************************************************************************************/

void  make_actions_num_prec_vector(int *action_num_prec_vector, int *fact_vector)
{
  int i=0;

  for(i=0;i<gnum_ef_conn;i++)
    action_num_prec_vector[i]=count_unsatisfied_preconds(i,fact_vector);

  
}






/**************************************************************************
Funzione che calcola le mutue esclusioni tra fatti (ComputeMutexFacts) che verranno poi
utilizzate per calcolare un insieme di relazioni anche tra le azioni (ComputeMutexActions).
Il puntatore passato (initial_state) contiene l'indirizzo dello stato iniziale da cui partire

Fuzioni richiamate:

alloc_matrix: per alloccare le matrici necessarie a rappresentare le mutue esclusioni

alloc_vect : per alloccare vettori (in particolare quelli di stato)

make_num_prec_vector :Inizializza il vettore (num_prec_vector) che contiene il numero
                      di preconsdizioni(start, end o overall) non supportate, 
                      cioe' non ancora rese vere, di tutte le azioni 

is_action_prec_mutex : controlla se l'azione considerata ha precondizioni
                       che sono mutex tra loro

*********************************************************/

void insert_actions_in_reviews(int fact, int *to_review) {

  int i;

  for (i = 0; i < gft_conn[fact].num_PC; i++) 
    to_review[gft_conn[fact].PC[i]]++;
  
} 

void insert_in_reviews_add(int fact, int *to_review, int skip) {

  int i;

  for (i = 0; i < gft_conn[fact].num_A; i++)
    if (gft_conn[fact].A[i] != skip)
      to_review[gft_conn[fact].A[i]]++;  
} 

void insert_dme(int A, int B)
{

  // Evito di inserire fatti numerici (... cmq non dovrebbe mai succedere)
  if (A < 0 || B < 0)
    return;

  if (!deleted_me)
    deleted_me = (dme *)calloc(max_dme, sizeof(dme));
  if (num_dme >= max_dme-1) {
    max_dme += 500;
    deleted_me = (dme *)realloc(deleted_me, max_dme * sizeof(dme));
  }

  deleted_me[num_dme].A = A;
  deleted_me[num_dme].B = B;
  num_dme++;

  deleted_me[num_dme].A = B;
  deleted_me[num_dme].B = A;
  num_dme++;

}


int review_dme(int *applied) {

  int i, p, pp, act, a, b;
  int changed = FALSE;

  while(num_dme) {

    for (i = num_dme - 1; i >= 0; i--) {
    
      a = deleted_me[i].A;
      b = deleted_me[i].B;

      num_dme--;

      for (p = 0; p < gft_conn[a].num_PC; p++) {
	act = gft_conn[a].PC[p];

	if (!GET_BIT(applied, act))
       	  continue;
	
	if (is_fact_in_delete_effects(act, b)
	    || is_fact_in_delete_effects_start(act, b))
	  continue;
	
	for (pp = 0; pp < gef_conn[act].num_PC; pp++)
	  if ((gef_conn[act].PC[pp] >= 0) 
	      && GET_BIT(FT_FT_mutex[b], gef_conn[act].PC[pp]))
	    break;
	if (pp != gef_conn[act].num_PC)
	  continue;
	
	if (gef_conn[act].sf) {

	  for (pp = 0; pp < gef_conn[act].sf->num_PC_end; pp++)
	    if ((gef_conn[act].sf->PC_end[pp] >= 0)
		&& GET_BIT(FT_FT_mutex[b], gef_conn[act].sf->PC_end[pp]))
	      break;
	  if (pp != gef_conn[act].sf->num_PC_end)
	    continue;

	  for (pp = 0; pp < gef_conn[act].sf->num_PC_overall; pp++)
	    if ((gef_conn[act].sf->PC_overall[pp] >= 0)
		&& GET_BIT(FT_FT_mutex[b], gef_conn[act].sf->PC_overall[pp]))
	      break;
	  if (pp != gef_conn[act].sf->num_PC_overall)
	    continue;
	}
			
	for (pp = 0; pp < gef_conn[act].num_A; pp++) {
	  if ((gef_conn[act].A[pp] >= 0)
	      && GET_BIT(FT_FT_mutex[b], gef_conn[act].A[pp])) {

# ifdef __TEST_REMOVE__
	    printf("\n\nRemoving mutex:");
	    printf("\n  Facts : %s <--> ", print_ft_name_string(b, temp_name));
	    printf("%s", print_ft_name_string(gef_conn[act].A[pp], temp_name));
	    printf("\n  Action : %s", print_op_name_string(act, temp_name));
#endif

	    RESET_BIT(FT_FT_mutex[b], gef_conn[act].A[pp]);
	    RESET_BIT(FT_FT_mutex[gef_conn[act].A[pp]], b);
	    insert_dme(b, gef_conn[act].A[pp]);
	    i++;
	    i++;
	    changed = TRUE;
	    gnum_mutex--;
	  }
	}

	if (gef_conn[act].sf) {
	  for (pp = 0; pp < gef_conn[act].sf->num_A_start; pp++) {
	    if (gef_conn[act].sf->A_start[pp] < 0)
	       continue;
	    if (GET_BIT(FT_FT_mutex[b], gef_conn[act].sf->A_start[pp])) {

# ifdef __TEST_REMOVE__
	      printf("\n\nRemoving mutex:");
	      printf("\n  Facts : %s <--> ", print_ft_name_string(b, temp_name));
	      printf("%s", print_ft_name_string(gef_conn[act].sf->A_start[pp], temp_name));
	      printf("\n  Action : %s", print_op_name_string(act, temp_name));
#endif

	      RESET_BIT(FT_FT_mutex[b], gef_conn[act].sf->A_start[pp]);
	      RESET_BIT(FT_FT_mutex[gef_conn[act].sf->A_start[pp]], b);
	      insert_dme(b, gef_conn[act].sf->A_start[pp]);
	      i++;
	      i++;
	      changed = TRUE;
	      gnum_mutex--;
	    }
	  }
	}

      }   

    } 
  }

  return changed;
  
}

int review_mutex(int *fct, int num, int act) {

  register int j, y, m, p, n, temp;
  int changed = FALSE;
 

  for (j = 0; j < num; j++)
    {
      
      if (fct[j] < 0)
	continue;

      for (m = 0; m < gnum_ft_block; m++)
	{
	  temp = FT_FT_mutex[fct[j]][m];
	  
	  y = 32;
	  while (temp)
	    {
	      y--;
	      
	      if (temp & FIRST_1)
		{
		  n = (m << 5) + y;

		  if (!GET_BIT(FT_FT_mutex[n], fct[j])) {
		    temp <<= 1;
		    continue;
		  }

		  for (p = 0; p < gef_conn[act].num_D; p++)
		    if (n == gef_conn[act].D[p])
		      break;
		  
		  if (p != gef_conn[act].num_D) {
		    temp <<= 1;
		    continue;
		  }

		  
		  for (p = 0; p < gef_conn[act].num_PC; p++)
		    if (gef_conn[act].PC[p] >= 0)
		      {
			if (GET_BIT(FT_FT_mutex[n], gef_conn[act].PC[p]))
			  break;
		      }
		  
		  if (p != gef_conn[act].num_PC)
		    {
		      temp <<= 1;
		      continue;
		    }
		  
		  
		    if (gef_conn[act].sf)
		    {
		      for (p = 0;
			   p < gef_conn[act].sf->num_D_start; p++)
			if (n == gef_conn[act].sf->D_start[p])
			  break;

		      if (p != gef_conn[act].sf->num_D_start)
			{
			  temp <<= 1;
			  continue;
			}
		        
		      for (p = 0; p < gef_conn[act].sf->num_PC_overall; p++)
			if (gef_conn[act].sf->PC_overall[p] >= 0)
			  {
			    if (GET_BIT(FT_FT_mutex[n], gef_conn[act].sf->PC_overall[p]))
			      break;
			  }
		      
		      if (p != gef_conn[act].sf->num_PC_overall)
			{
			  temp <<= 1;
			  continue;
			}
		      
		      for (p = 0; p < gef_conn[act].sf->num_PC_end; p++)
			if (gef_conn[act].sf->PC_end[p] >= 0)
			  {
			    if (GET_BIT(FT_FT_mutex[n], gef_conn[act].sf->PC_end[p]))
			      break;
			  }

		      if (p != gef_conn[act].sf->num_PC_end)
			{
			  temp <<= 1;
			  continue;
			}
		      
		    } 
		  
		  changed = TRUE;
		  
		  RESET_BIT (FT_FT_mutex[fct[j]], n);
		  RESET_BIT (FT_FT_mutex[n], fct[j]);

#ifdef __TEST_REMOVE__
		  printf("\n\nRemoving mutex:");
		  printf("\n  Facts : %s <--> ", print_ft_name_string(n, temp_name));
		  printf("%s", print_ft_name_string(fct[j], temp_name));
		  printf("\n  Action : %s", print_op_name_string(act, temp_name));
#endif
	
		  insert_dme(fct[j], n);
		  	  
		  gnum_mutex--;
		  
		  
		}
	      temp <<= 1;
	    }
	}
    }
  
  return changed;

}




void cut_suspected_ef_conns(void)
{

  int i, last_block, last_ef;

  if (gfirst_suspected_ef_conn == gnum_ef_conn)
    return;

  last_block = (gfirst_suspected_ef_conn >> 5) + 1;
  last_ef = last_block << 5;

  for (i = gfirst_suspected_ef_conn; i < last_ef; i++)
    {
      if (GpG.has_timed_preconds)
	RESET_BIT(GpG.has_timed_preconds, i);
      if (GpG.numeric_actions)
	RESET_BIT(GpG.numeric_actions, i);
    }
  for (i = last_block; i < gnum_ef_block; i++)
    {
      if (GpG.has_timed_preconds)
	GpG.has_timed_preconds[i] = 0;
      if (GpG.numeric_actions)
	GpG.numeric_actions[i] = 0;
    }

  gnum_ef_conn = gfirst_suspected_ef_conn;
  gnum_ef_block = last_block;
  

}






void calc_mutex (State * initial_state)
{
  Bool changed;

  // Bool once_again;
  State A, C;
 
  register int i, j, k, l, m, ll, aus_counter;
  register int y;
  register int temp;
  int num_facts = 0;
  int num_ops = 0;

  // bit vector che indica se l'azione e' stata applicata
  int *applied;

  int *To_be_Executed;
  // bit vector che indica se l'azione e' stata esaminata

  // Vettore che andra' a contenere il numero di precondizioni non soddisfatte
  //per ogni azione
  int *num_prec_vector=NULL;

  int *start_state = NULL;

  /* PREDICATI DERIVATI */
  int *dp_num_prec_vector = NULL;
  int *dp_ef;
  int *dp_vect = NULL;
  int num_dp = 0;
  /* END */


  /**** PT ****/
  int *to_review = NULL;
  /**** PT ****/
 
  Bool apply_next_suspected = FALSE;


#ifdef __TEST_TIME__
  struct tms start, end;
  float total_time; 
  times (&start);
  printf("\n Start C Mutex");
  
#endif

  A.F = (int *)calloc(MAX_STATE, sizeof(int));
  C.F = (int *)calloc(MAX_STATE, sizeof(int));
  A.num_F = C.num_F = 0;
  
  gnum_mutex = 0;

  if (DEBUG5)
    {
      for (i = 0; i < gnum_ef_conn; i++)
	if (gef_conn[i].suspected)
	  printf("\n\nSupected [%d] : %s", i, print_op_name_string(i, temp_name));
    }

  /**** PT ****/
  to_review = alloc_vect(gnum_ef_conn);
  /**** PT ****/

  num_prec_vector=alloc_vect (gnum_ef_conn);
  assert(num_prec_vector);

  applied = alloc_vect (gnum_ef_block);

  // alloco solo se non era gia' stato fatto
  //FT_FT_mutex e' la matrice di bit che rappresenta le mutue eslusioni tra fatti
  //un 1 in posizione (i,j) rappresenta una mutex tra fatto numero i e fatto
  //numero j 
  if (!FT_FT_mutex)
    FT_FT_mutex = alloc_matrix (gnum_ft_conn, gnum_ft_block);
  
  /*
  if (!l_vals)
    l_vals = alloc_matrix (gnum_ef_conn, gnum_fullnum_blocks);
  if (!lstar_vals)
    lstar_vals = alloc_matrix (gnum_ef_conn, gnum_fullnum_blocks);
  if (!r_vals)
    r_vals = alloc_matrix (gnum_ef_conn, gnum_fullnum_blocks);
  if (!tested_vars)
    tested_vars = alloc_matrix (gnum_ef_conn, gnum_fullnum_blocks);
  */

  Numeric.Affects_Matrix=alloc_matrix(gnum_comp_var,gnum_block_compvar);
  
  for(i=0;i<gnum_comp_var;i++)
    {
      add_affects_list(i,Numeric.Affects_Matrix[i]);
    }

  if (GpG.accurate_cost >= 0 &&  Hvar.init_facts_array == NULL)
    {
      Hvar.init_facts_array = (dg_inform_list *) calloc (gnum_ft_conn, sizeof (dg_inform_list));
      Hvar.dg_facts_min_duration = (float *) calloc (gnum_ft_conn, sizeof (float));
      Hvar.bit_vect_facts = alloc_vect (gnum_ft_block);
      Hvar.bit_vect_actions = alloc_vect (gnum_ef_block);
    }


  assert (FT_FT_mutex);

  To_be_Executed = alloc_vect (gnum_ef_block);
  assert(To_be_Executed);
 
  //F e' lo stato,un bit-vector che asserisce quali fatti sono veri, viene aggiornato ad ogni passaggio
  //se e' NULL lo allocco, altrimenti lo resetto
  if(F==NULL) {
    F = alloc_vect (gnum_ft_block);
    assert(F);
  }
  else
    reset_bitarray (F, gnum_ft_block);

  //Variabile che mi definisce il livello a cui sono giunto nel calcolo delle mutex
  GpG.fixpoint_plan_length=0;
  
  for (i = 0; i < gnum_ef_conn; i++)
    {
      gef_conn[i].in_E = FALSE;
      gef_conn[i].level = -1;
    }

  for (i = 0; i < gnum_ft_conn; i++)
    {
      gft_conn[i].in_F = FALSE;
      gft_conn[i].level = -1;
    }

  //Il vettore dei fatti veri viene posto uguale allo stato iniziale (F = I)
  //ed i fatti veri allo stato iniziale vengono memorizzati nella struttura gft_conn
 
  for (i = 0; i < initial_state->num_F; i++)
    {
      SET_BIT (F, initial_state->F[i]);
      //Il fatto viene asserito come vero allo stato iniziale e gli viene assegnato
      //il livello zao, ossia il fatto e' vero inizialmente
      gft_conn[initial_state->F[i]].in_F = TRUE;
      gft_conn[initial_state->F[i]].level = GpG.fixpoint_plan_length;
      //numero dei fatti che possono essere resi veri
      num_facts++;
      if (GpG.accurate_cost >= 0)
	cri_insert_ftcost (initial_state->F[i], 0, 0, 0, INITIAL_ACTION);

    }

  /* PREDICATI DERIVATI */
  if (GpG.derived_predicates) {
    dp_vect = (int *)calloc(gnum_ft_block, sizeof(int));
    assert(dp_vect);
    initialize_dp_num_prec_vector(&dp_num_prec_vector);
    num_dp = calc_all_derived_predicates_from(dp_num_prec_vector, F, RESET_ON, &dp_ef);
    if (num_dp) {
      for (i = 0; i < num_dp; i++) {
	if (dp_ef[i] < 0) {
	  printf("\nWarning : derived predicate marked as \"to delete\" from initial state ?!");
	  RESET_BIT(F, (-dp_ef[i]-1));
	  gft_conn[-dp_ef[i]-1].in_F = FALSE;
	  continue;
	}
	
	gft_conn[dp_ef[i]].in_F = TRUE;
	gft_conn[dp_ef[i]].level = GpG.fixpoint_plan_length;
	num_facts++;
	if (GpG.accurate_cost >= 0)
	  cri_insert_ftcost (dp_ef[i], 0, 0, 0, INITIAL_ACTION);
      }
      free(dp_ef);
      dp_ef = NULL;
    }
    memcpy(dp_vect, F, gnum_ft_block * sizeof(int));
  }
  /* END */
 

  start_state = alloc_vect(gnum_ft_block);
  memcpy(start_state, F, gnum_ft_block * sizeof(int)); 

  //Funzione che inizializza il vettore (num_prec_vector) che contiene il numero
  //di preconsdizioni(start, end o overall) non supportate, cioe' non ancora rese vere, di tutte le azioni 
  //Se num_prec_vector[2]=3 significa che l'azione numero due ha attualmente tre precondizioni
  //non supportate
  //Questa funzione richiama attraverso un ciclo la funzione count_unsatisfied_precond(i) che restituisce
  //il numero di prec. false dell'azione i
  
  make_actions_num_prec_vector(num_prec_vector, F);

  /**
     Copio il vettore del numero di precondizioni non soddisfatte (num_prec_vector) in Numeric per poterlo 
     riutilizzare successivamente per il calcolo della raggiungibilità (in compute_reachability)
  **/
  //#ifdef __TEST_REACH__
  Numeric.ri_prec_vector=alloc_vect (gnum_ef_conn);
  memcpy(Numeric.ri_prec_vector,num_prec_vector, gnum_ef_conn*sizeof(int));
  //#endif

 
  do
    {

      changed = FALSE;

  do
    {
      //Variabile che,se vera, indica che si possono trovare ancora delle mutex,
      // ossia se changed=TRUE M*!=M (M=insieme delle potenziali mutex) o F*!=F
      //(F=insieme dei possibili fatti del problema)
      changed = FALSE;
      reset_bitarray (To_be_Executed, gnum_ef_block);

      for (i = 0; i < gnum_ef_conn; i++) 
	if(!GET_BIT (applied, i)) 
	  if(num_prec_vector[i]==0 && !(gef_conn[i].act_type == TIMED_FACT_ACT) && (gef_conn[i].position >= 0))	 
	    SET_BIT (To_be_Executed, i);
      
#ifdef __TEST_TIME__
      times (&end);total_time=0.0;
      TIME (total_time); 
      printf("\n TIme  %2f", total_time); fflush(stdout);

#endif
      /*per tutte le azioni */
      for (i = 0; i < gnum_ef_conn; i++)
	{

	  A.num_F = 0;
	  C.num_F = 0;

	  /*se l'azione non e' ancora stata applicata... */
	  if(!GET_BIT (applied, i))
	    { 
	      // Se l'azione ha almeno una precondizione non supportata o le sue
	      // precon. sono mutex passa alla prossima poiche' non puo' dar luogo
	      // a nuovi fatti o mutex, in quanto non applicabile
	      if (!GET_BIT (To_be_Executed, i))
		continue;
	      if(is_action_prec_mutex(i,FT_FT_mutex)) {
		continue;
	      }

	      if (i >= gfirst_suspected_ef_conn)
		{ 
		  if (apply_next_suspected)
		    {
#ifdef __TEST__
		      printf("\n\nTryng to apply action: %s\n", print_op_name_string(i, temp_name));
#endif
		      
		      /*
			apply_next_suspected = FALSE ==> rende applicabile una sola azione alla volta
			gef_conn[i].suspected = FALSE ==> l'azione resterà applicabile in ogni caso (nn viene tolta anche se nn aggiunge nuovi fatti)
		      */

		      //apply_next_suspected = FALSE;
		      gef_conn[i].suspected = FALSE;

		    }
		  else
		    {
#ifdef __TEST__
		      printf("\n\nSkip suspected action: %s\n", print_op_name_string(i, temp_name));
#endif
		      continue;
		    }
		}
	      else
		gef_conn[i].suspected = FALSE;

	     
	      /*
		#ifndef __TEST_REACH__
		
		if (GpG.accurate_cost >= 0)
		cri_activate_distgraph_ef (i);
		
		#endif
	      */



#ifdef __TEST_TIME__
	      printf("\n\napply action %d ",i); print_op_name(i);
#endif

	      /*se l'azione non e' ancora stata applicata... */
	      //segnalo di avere applicato l'azione i-esima poiche' essa e' applicabile
	      SET_BIT (applied, i);
	      /*determino i fatti che possono essere raggiunti grazie a questa nuova azione*/
	      /* A= add(a) - F prendo in considerazione i fatti che non appartengono ancora ad F ed apparten
                 gono agli effetti additivi dell'azione i-esima    */
	      for (j = 0; j < gef_conn[i].num_A; j++)
		{
		  /*se il fatto non era ancora stato reso vero */
		  if (gef_conn[i].A[j] >= 0) {
		    if (!GET_BIT (F, gef_conn[i].A[j]))
		      {
			/*lo rende vero adesso */
			gft_conn[gef_conn[i].A[j]].in_F = TRUE;
		       	gft_conn[gef_conn[i].A[j]].level = GpG.fixpoint_plan_length + 1;
			SET_BIT (F, gef_conn[i].A[j]);
			// Se il fatto reso vero era prec. di qualche azione aggiorno il vettore
                        // delle prec. non supportate andando a decrementare la posizione relativa all'azione i
                          for(aus_counter=0;aus_counter< gft_conn[gef_conn[i].A[j]].num_PC;aus_counter++)
			    {
			      if(GpG.temporal_plan)
				{  
				  if(is_fact_in_preconditions_end(gft_conn[gef_conn[i].A[j]].PC[aus_counter], gef_conn[i].A[j])
				     && is_fact_in_additive_effects_start(gft_conn[gef_conn[i].A[j]].PC[aus_counter], gef_conn[i].A[j]))
				    continue;    

				  if(is_fact_in_preconditions_overall(gft_conn[gef_conn[i].A[j]].PC[aus_counter], gef_conn[i].A[j])
				     && is_fact_in_additive_effects_start(gft_conn[gef_conn[i].A[j]].PC[aus_counter], gef_conn[i].A[j]))
				    continue;
				}
			      
                              num_prec_vector[gft_conn[gef_conn[i].A[j]].PC[aus_counter]]--;
			      if(num_prec_vector[gft_conn[gef_conn[i].A[j]].PC[aus_counter]]==0)
				changed=TRUE;
			      
			     }
			/*e lo inserisce in un insieme di appoggio che tiene traccia dei fatti aggiunti*/
			A.F[A.num_F++] = gef_conn[i].A[j];
			num_facts++;
			
			/* PREDICATI DERIVATI */
			if (GpG.derived_predicates) {
			  num_dp = calc_new_derived_predicates_from(A.F[A.num_F - 1], dp_num_prec_vector, dp_vect, ADD_FACT, &dp_ef);
			  if (dp_ef) {
			    for (k = 0; k < num_dp; k++) {
			      if (dp_ef[k] < 0)
				continue;
			      //se il fatto non era ancora stato reso vero
			      if (!GET_BIT (F, dp_ef[k])) {
				//lo rende vero adesso 
				gft_conn[dp_ef[k]].in_F = TRUE;
				gft_conn[dp_ef[k]].level = GpG.fixpoint_plan_length + 1;
				SET_BIT (F, dp_ef[k]);
				//Se il fatto reso vero era prec. di qualche azione aggiorno il vettore
				//delle prec. non supportate
				for(aus_counter=0;aus_counter< gft_conn[dp_ef[k]].num_PC;aus_counter++) { 
				  if(GpG.temporal_plan) {
				    if(is_fact_in_preconditions_end(gft_conn[dp_ef[k]].PC[aus_counter], dp_ef[k])
				       && is_fact_in_additive_effects_start(gft_conn[dp_ef[k]].PC[aus_counter], dp_ef[k]))
				      continue;    
				    if(is_fact_in_preconditions_overall(gft_conn[dp_ef[k]].PC[aus_counter], dp_ef[k])
				       && is_fact_in_additive_effects_start(gft_conn[dp_ef[k]].PC[aus_counter], dp_ef[k]))
				      continue;
				  }
				  num_prec_vector[gft_conn[dp_ef[k]].PC[aus_counter]]--;
				  if (num_prec_vector[gft_conn[dp_ef[k]].PC[aus_counter]]==0)
				    changed=TRUE;
				}
			      }
			    }
			    free(dp_ef);
			    dp_ef = NULL;
			  }
			}
			/* END */
		      }
		    else
		      C.F[C.num_F++] = gef_conn[i].A[j]; 
		  }
		      
		}
	      //lo stesso per gli effetti at start
	      if (gef_conn[i].sf)
		{
		  for (j = 0; j < gef_conn[i].sf->num_A_start; j++)
		    {
		      /*se il fatto non era ancora stato reso vero */
		      if (gef_conn[i].sf->A_start[j] >= 0) {
			if (!GET_BIT (F, gef_conn[i].sf->A_start[j]))
			  {
			    /*lo rende vero adesso */
			    gft_conn[gef_conn[i].sf->A_start[j]].in_F = TRUE;
			    gft_conn[gef_conn[i].sf->A_start[j]].level =
			      GpG.fixpoint_plan_length + 1;
			    SET_BIT (F, gef_conn[i].sf->A_start[j]);
			    //Se il fatto reso vero era prec. di qualche azione aggiorno il vettore
			    //delle prec. non supportate
			    for(aus_counter=0;aus_counter< gft_conn[gef_conn[i].sf->A_start[j]].num_PC;aus_counter++)
                              { 
				if(GpG.temporal_plan)
                                  {
				    if(is_fact_in_preconditions_end(gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter], gef_conn[i].sf->A_start[j])
				       && is_fact_in_additive_effects_start(gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter], gef_conn[i].sf->A_start[j]))
				      continue;    
				    
				    if(is_fact_in_preconditions_overall(gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter], gef_conn[i].sf->A_start[j])
				       && is_fact_in_additive_effects_start(gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter], gef_conn[i].sf->A_start[j]))
				      continue;
				  }
				num_prec_vector[gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter]]--;
				if(num_prec_vector[gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter]]==0)
				  changed=TRUE;
			      }
			     /*e lo inserisce in un insieme di appoggio */
			     A.F[A.num_F++] = gef_conn[i].sf->A_start[j];
			     num_facts++;
			     
			     /* PREDICATI DERIVATI */
			     if (GpG.derived_predicates) {
			       num_dp = calc_new_derived_predicates_from(A.F[A.num_F - 1], dp_num_prec_vector, dp_vect, ADD_FACT, &dp_ef);
			       if (dp_ef) {
				 for (k = 0; k < num_dp; k++) {
				   if (dp_ef[k] < 0)
				     continue;
				   //se il fatto non era ancora stato reso vero
				   if (!GET_BIT (F, dp_ef[k])) {
				     //lo rende vero adesso 
				     gft_conn[dp_ef[k]].in_F = TRUE;
				     gft_conn[dp_ef[k]].level = GpG.fixpoint_plan_length + 1;
				     SET_BIT (F, dp_ef[k]);
				     //Se il fatto reso vero era prec. di qualche azione aggiorno il vettore
				     //delle prec. non supportate
				     for(aus_counter=0;aus_counter< gft_conn[dp_ef[k]].num_PC;aus_counter++) { 
				       if(GpG.temporal_plan) {
					 if(is_fact_in_preconditions_end(gft_conn[dp_ef[k]].PC[aus_counter], dp_ef[k])
					    && is_fact_in_additive_effects_start(gft_conn[dp_ef[k]].PC[aus_counter], dp_ef[k]))
					   continue;    
					 if(is_fact_in_preconditions_overall(gft_conn[dp_ef[k]].PC[aus_counter], dp_ef[k])
					    && is_fact_in_additive_effects_start(gft_conn[dp_ef[k]].PC[aus_counter], dp_ef[k]))
					   continue;
				       }
				       num_prec_vector[gft_conn[dp_ef[k]].PC[aus_counter]]--;
				       if (num_prec_vector[gft_conn[dp_ef[k]].PC[aus_counter]]==0)
					 changed=TRUE;
				     }
				   }
				 }
				 free(dp_ef);
				 dp_ef = NULL;
			       }
			     }
			     /* END */
			  }
			else
			  C.F[C.num_F++] = gef_conn[i].sf -> A_start[j]; 
		      }
		    }
		}

	      	
	      /*se l'azione e' nuova, la conto incrementando il contatore */
	      if (!gef_conn[i].in_E)
		{
		  gef_conn[i].in_E = TRUE;
		  gef_conn[i].level = GpG.fixpoint_plan_length;
		  num_ops++;
		  /*test per confronto con versione che aggiunge direttamente in coda i fatti */
		}
	      for (j = 0; j < A.num_F; j++)
		{
		  for (k = 0; k < gef_conn[i].num_D; k++)
		    {
		      // inserito if che fa in modo di non inserire mutex tra un fatto e se stesso
		      if(A.F[j]==gef_conn [i].D[k])
			continue;

                      // Se la mutex non era stata ancora considerata incremento il contatore delle possibili
                      // mutex e setto i bit della matrice relativi, altrimenti proseguo analizzando
                      // la prossima possibile mutex di M
		      if (GET_BIT (FT_FT_mutex[A.F[j]], gef_conn[i].D[k]))
			continue;
		      
		      if (!GET_BIT (F , gef_conn[i].D[k]))
			continue;
		     
		      gnum_mutex++;
		      /*inserisce la mutex tra il j-esimo fatto di A e il k-esimo effetto cancellante dell'azione i-esima */
		      SET_BIT (FT_FT_mutex[A.F[j]], gef_conn[i].D[k]);
		      /*e viceversa */
		      SET_BIT (FT_FT_mutex[gef_conn[i].D[k]], A.F[j]);
		      
		      insert_in_reviews_add(gef_conn[i].D[k], to_review, i);
		          
#ifdef __TEST_ME__
		      if(A.F[j]== MEA && gef_conn[i].D[k]==MEB)
			{			
			  printf("\n ACT1 "); print_op_name(i);
			}
#endif

		      /*segnala che a questo giro e' stato aggiunto qualcosa, quindi M!=M* o F!=F*  */
		      changed = TRUE;
		    }
		  //stesso discorso per effetti cancellanti at start
		  if (gef_conn[i].sf)
		    {
		      for (k = 0; k < gef_conn[i].sf->num_D_start; k++)
			{// inserito if che fa in modo di non inserire mutex tra un fatto e se stesso
		          if(A.F[j]==gef_conn[i].sf->D_start[k])
		             continue;

			  if (GET_BIT(FT_FT_mutex[A.F[j]], gef_conn[i].sf->D_start[k]))
			    continue;

			  if (!GET_BIT (F , gef_conn[i].sf->D_start[k]))
			    continue;
			  
			  gnum_mutex++;
			  /*inserisce la mutex tra il j-esimo fatto di A e il k-esimo effetto cancellante dell'azione i-esima */
			  SET_BIT (FT_FT_mutex[A.F[j]], gef_conn[i].sf->D_start[k]);
			  /*e viceversa */
			  SET_BIT (FT_FT_mutex[gef_conn[i].sf->D_start[k]], A.F[j]); 

			  insert_in_reviews_add(gef_conn[i].sf->D_start[k], to_review, i);

			  /*segnala che a questo giro e' stato aggiunto qualcosa */


#ifdef __TEST_ME__
			  if(A.F[j]==MEA && gef_conn[i].sf->D_start[k]==MEB)
			    {			
			      printf("\n ACT2 "); print_op_name(i);
			    }
#endif

			  changed = TRUE;
			}
		    }
  
		  /*insert m-e- between new facts and the facts m.e. with the preconds of o */
		  for (k = 0; k < gef_conn[i].num_PC; k++)
		    if ((gef_conn[i].PC[k] >= 0))
		      {
			for (ll = 0, l = 0; l < gnum_ft_block; l++, ll += 32)
			  {
			    temp = FT_FT_mutex[gef_conn[i].PC[k]][l];
			    y = 32;
			    while (temp)
			      {
				y--;
				if (temp & FIRST_1)
				  {
				    m = ll + y;
				    
				    if (A.F[j] != m)
				      {

					/*inserisce mutex tra j-esimo fatto di a e il fatto mutex con le preco di o */					  
					if (!GET_BIT (FT_FT_mutex[A.F[j]], m))
					  { 
					    gnum_mutex++;
					    SET_BIT (FT_FT_mutex[A.F[j]], m);
					    SET_BIT (FT_FT_mutex[m], A.F[j]);
					    
					    insert_in_reviews_add(m, to_review, i);	    

#ifdef __TEST_ME__
					    if(A.F[j]==MEA && m==MEB)
					      {			
						printf("\n ACT3 %d ",i); print_op_name(i);
					      }
#endif

					    /*segnalo l'aggiunta */
					    changed = TRUE;
					  }
				      }
				  }
				temp <<= 1;
			      }
			  }
		      }
		  if (gef_conn[i].sf)
		    {
		      //PER PRECO OVERALL
		      /*insert m-e- between new facts anc the facts m.e. with the preconds of o */
		      for (k = 0; k < gef_conn[i].sf->num_PC_overall; k++)
			if ((gef_conn[i].sf->PC_overall[k] >= 0))
			  {
			    for (ll = 0, l = 0; l < gnum_ft_block;
				 l++, ll += 32)
			      {
				temp =
				  FT_FT_mutex[gef_conn[i].sf->
					      PC_overall[k]][l];
				y = 32;
				while (temp)
				  {
				    y--;
				    if (temp & FIRST_1)
				      {
					m = ll + y;
					
					if (A.F[j] != m)
					  {
                                           if (!GET_BIT (FT_FT_mutex[A.F[j]], m))
					     { 
					       gnum_mutex++;

				        	SET_BIT (FT_FT_mutex[A.F[j]], m);
				        	SET_BIT (FT_FT_mutex[m], A.F[j]);

						insert_in_reviews_add(m, to_review, i);

#ifdef __TEST_ME__
						if(A.F[j]==MEA && m==MEB )
						  {			
						    printf("\n ACT4 "); print_op_name(i);
						  }
#endif
						/*segnalo l'aggiunta */
					        changed = TRUE;
					       }
					  }
				      }
				    temp <<= 1;
				  }
			      }
			  }
		      //PER PRECO AT END
		      /*insert m-e- between new facts anc the facts m.e. with the preconds of o */
		      for (k = 0; k < gef_conn[i].sf->num_PC_end; k++)
			if ((gef_conn[i].sf->PC_end[k] >= 0))
			  {
			    for (ll = 0, l = 0; l < gnum_ft_block;
				 l++, ll += 32)
			      {
				temp =
				  FT_FT_mutex[gef_conn[i].sf->PC_end[k]][l];
				y = 32;
				while (temp)
				  {
				    y--;
				    if (temp & FIRST_1)
				      {
					m = ll + y;
				
					if (A.F[j] != m)
					  {

					    /*inserisce mutex tra j-esimo fatto di a e il fatto mutex con le preco di o */
					    if (!GET_BIT
						(FT_FT_mutex[A.F[j]], m))
					       { 
						 gnum_mutex++;
                                      
					         SET_BIT (FT_FT_mutex[A.F[j]], m);
					         SET_BIT (FT_FT_mutex[m], A.F[j]);
							
						 insert_in_reviews_add(m, to_review, i);

					 
#ifdef __TEST_ME__
						 if(A.F[j]==MEA && m==MEB )
						   {			
						     printf("\n ACT5 "); print_op_name(i);
						   }
#endif
					    /*segnalo l'aggiunta */
					         changed = TRUE;
					       }
					  }
				      }
				    temp <<= 1;
				  }
			      }
			  }
		    }
 
		}

	      //AGGIUNTA: i fatti additivi di questa azione non possono essere mutex tra loro!
              //Vado a fare un controllo sulla matrice delle mutex tra fatti e correggo eventuali
	      //inconsistenze
	      for (j = 0; j < gef_conn[i].num_A; j++)
		for (k = j + 1; k < gef_conn[i].num_A; k++)
		  if ((gef_conn[i].A[j] >= 0) && (gef_conn[i].A[k] >= 0))
		    {
		      if (GET_BIT(FT_FT_mutex[gef_conn[i].A[j]], gef_conn[i].A[k]))
			gnum_mutex--;
		      else
			continue;
	   
		      RESET_BIT (FT_FT_mutex[gef_conn[i].A[j]],
				 gef_conn[i].A[k]);
		      RESET_BIT (FT_FT_mutex[gef_conn[i].A[k]],
				 gef_conn[i].A[j]);

		      insert_dme(gef_conn[i].A[j], gef_conn[i].A[k]);

		      changed = TRUE;

		    
		    }
	      if (gef_conn[i].sf)
		{
		  //gli effetti additivi at start non possono essere mutex tra loro
		  //Vado a fare un controllo sulla matrice delle mutex tra fatti e correggo eventuali
		  //inconsistenze
		  for (j = 0; j < gef_conn[i].sf->num_A_start; j++)
		    for (k = j + 1; k < gef_conn[i].sf->num_A_start; k++)
		      if ((gef_conn[i].sf->A_start[j] >= 0)
			  && (gef_conn[i].sf->A_start[k] >= 0))
			{
			  if (GET_BIT(FT_FT_mutex[gef_conn[i].sf->A_start[j]],
			       gef_conn[i].sf->A_start[k]))
			    gnum_mutex--;
			  else
			    continue;
			  RESET_BIT (FT_FT_mutex[gef_conn[i].sf->A_start[j]],
				     gef_conn[i].sf->A_start[k]);
			  RESET_BIT (FT_FT_mutex[gef_conn[i].sf->A_start[k]],
				     gef_conn[i].sf->A_start[j]);

			  insert_dme(gef_conn[i].sf->A_start[k], gef_conn[i].sf->A_start[j]);

			  changed = TRUE;
						  
			}
		  //nemmeno un effetto start con un effetto end
		  for (j = 0; j < gef_conn[i].sf->num_A_start; j++)
		    for (k = 0; k < gef_conn[i].num_A; k++)
		      if ((gef_conn[i].sf->A_start[j] >= 0)
			  && (gef_conn[i].A[k] >= 0))
			{
			  if (GET_BIT(FT_FT_mutex[gef_conn[i].sf->A_start[j]],
			       gef_conn[i].A[k]))
			    gnum_mutex--;
			  else
			    continue;
			  RESET_BIT (FT_FT_mutex[gef_conn[i].sf->A_start[j]],
				     gef_conn[i].A[k]);
			  RESET_BIT (FT_FT_mutex[gef_conn[i].A[k]],
				     gef_conn[i].sf->A_start[j]);

			  insert_dme( gef_conn[i].A[k], gef_conn[i].sf->A_start[j]);

			  changed = TRUE;
						
			}
		}
	      
	      
	      if (gef_conn[i].suspected)
		{
		  if(A.num_F)
		    {
		      gef_conn[i].suspected = FALSE;
		      to_review[i] = 0;
		    }
		  else
		    {
		      //#ifdef __TEST__
		      printf("\n\nRemove suspected action: %s\n", print_op_name_string(i, temp_name));
		      //#endif
		      gef_conn[i].level = -1;
		    }
		}
	      
	      
	      if (!gef_conn[i].suspected)
		{
		  /* Riconsidero effetti additivi azione */
		  if (review_mutex(C.F, C.num_F, i)==TRUE)
		    changed=TRUE; 
		  if(review_dme(applied) == TRUE)
		    changed=TRUE;
		}
	      /*
	      if (A.num_F > 0) {
		
		SET_BIT(to_review, i);

	      }
	      */

	   } 	       /*fine if !applied */
	}
      
      GpG.fixpoint_plan_length++;
      if (DEBUG2)
	printf ("\n Level %3d:%5d facts, %5d ops and %5d mutex relations",
		GpG.fixpoint_plan_length, num_facts, num_ops, gnum_mutex); 
      
    }
  while (changed);

    // Ricontrollo gli effetti additivi delle sole azioni in to_review
    for (m = 0; m < gnum_ef_conn; m++) {
      if (to_review[m]) {
	to_review[m]--;
	if(GET_BIT(applied,m)) {
	  if (review_mutex(gef_conn[m].A, gef_conn[m].num_A, m)==TRUE)
	    changed=TRUE;   
	  if (gef_conn[m].sf) {
	    if (review_mutex(gef_conn[m].sf->A_start, gef_conn[m].sf->num_A_start, m)==TRUE)
	      changed=TRUE;  
	  }
	}
      }
    }
    // Ricontrollo le mutex che sono state tolte
    if(review_dme(applied) == TRUE)
      changed=TRUE;
    
    if (!changed)
      {
	if (!are_goal_reachable_and_non_mutex ()) 
	  {
	  
	    if (!apply_next_suspected && GpG.try_suspected_actions)
	      {
		apply_next_suspected = changed = TRUE;
		GpG.contraddictory_ef_conn = TRUE;

		/*
		 * Introduco i link fatti->azioni che erano stati omessi
		 */
		add_suspected_ef_conns_effects();

		/*
		 * Ricostruisco il vettore del numero di precondizioni non soddisfatte
		 * (non è aggiornato per le azioni che sono state saltate)
		 */
		make_actions_num_prec_vector(num_prec_vector, F);

		/*
		 * Ricostruisco il vettore delle precondizioni nn soddisfatte dallo
		 * stato iniziale (ho aggiunto link tra fatti e azioni!!)
		 */
		make_actions_num_prec_vector(Numeric.ri_prec_vector, start_state);

		/*
		 * Estendo le azioni applicabili a tutto il gef_conn
		 */
		gfirst_suspected_ef_conn = gnum_ef_conn;

	      }
	    else
	      {
		printf ("\nThe problem is unsolvable since at the fixpoint level the goals are mutex or not reachable\n\n");
		store_plan(-1.0);
		
		exit (0);
	      }
	  }
	else
	  {
	    /*
	     * Taglio le azioni contraddittorie (non servono per raggiungere i goal)
	     */
	    cut_suspected_ef_conns();
	  }
      }
    
    }
  while (changed);
  
  total_ft_ft_mutex = gnum_mutex * 2;
  
  //if (DEBUG1)
    printf("\n total_ft_ft_mutex %d num_ops %d num_facts %d \n", total_ft_ft_mutex, num_ops, num_facts);

  /*
    #ifndef __TEST_REACH__
    if (GpG.accurate_cost >= 0)
    set_init_computed_dg_costs();
    #endif
  */


  free (applied);
  free(num_prec_vector);
  free(to_review);
  free(start_state);
  
  if (GpG.derived_predicates) {
    free(dp_num_prec_vector);
    free(dp_vect);
  }

  free(To_be_Executed);

}







/**********************************************************************************
Funzione che calcola le mutue esclusioni azioni-azioni, azioni-fatti e fatti-azioni
andando ad attuare la ricerca secondo il nuovo algoritmo che segue le azioni
piuttosto che i fatti come avveniva in precedenza
**********************************************************************************/


void
calc_mutex_ops (void)
{
  register int i, j, k, l;
  register int temp, x, y, xx;


  /*allocazioni iniziali potrebbero essere spostate */
  // faccio allocazioni solo se non gia fatte
  if (!FT_EF_mutex)
    FT_EF_mutex = alloc_matrix (gnum_ft_conn, gnum_ef_block);
  if (!EF_FT_mutex)
    EF_FT_mutex = alloc_matrix (gnum_ef_conn, gnum_ft_block);

  if ((!GpG.lowmemory) && (!EF_EF_mutex))
    EF_EF_mutex = alloc_tri_matrix (gnum_ef_conn);

  /*assegnamenti vettori */

  for (i = 0; i < gnum_ft_conn; i++)
    {

#ifdef __TEST__
      int k;
      char *name = (char *) calloc (256, sizeof (char));
      Fact *f;


      strcat (name, INIT_CONN);

      f = &grelevant_facts[i];
      strcat (name, gpredicates[f->predicate]);


      strcat (name, CONN_PLAN);

      for (k = 0; k < garity[f->predicate]; k++)
	{
	  if (f->args[k] >= 0)
	    {
	      strcat (name, gconstants[(f->args)[k]]);
	    }
	  if (k < garity[f->predicate] - 1)
	    {

	      strcat (name, CONN_PLAN);

	      strcat (name, " ");
	    }
	}

      strcat (name, END_CONN);

      gft_conn[i].name = name;
#endif


      gft_conn[i].ft_exclusive_vect = FT_FT_mutex[i];
      gft_conn[i].ef_exclusive_vect = FT_EF_mutex[i];
    }

  for (i = 0; i < gnum_ef_conn; i++)
    {

#ifdef __TEST__
      int k;
      char *name = (char *) calloc (256, sizeof (char));
      Action *a = gop_conn[i].action;


      strcat (name, INIT_CONN);

      strcat (name, a->name);

      for (k = 0; k < a->num_name_vars; k++)
	{

	  strcat (name, CONN_PLAN);

	  strcat (name, gconstants[a->name_inst_table[k]]);
	}


      strcat (name, END_CONN);

      gef_conn[i].name = name;

#endif

      gef_conn[i].ft_exclusive_vect = EF_FT_mutex[i];


    }

  /*mettere gnum_ft_conn -1 nel caso... */

  for (i = 0; i < gnum_ft_conn; i++)
    {
      //MUTEX AZIONI - AZIONI
      /*se due fatti sono mutex, allora lo sono anche le azioni che li hanno come preco */
      /*per ogni fatto, prendo in considerazione i fatti con cui esso e' mutualmente esclusivo 
        Quindi se (p,q) sono mutex, le azioni  A e B tali che p e' preco di A e q e' preco di B
        sono mutex    */
      for (x = GUID_BLOCK (i), xx = x << 5; x < gnum_ft_block; x++, xx += 32)
	{
	  temp = FT_FT_mutex[i][x];
	  y = 32;
	  while (temp)
	    {
	      y--;
	      if (temp & FIRST_1)
		{
		  j = xx + y;
		  if (j <= i)
		    {
		      temp <<= 1;
		      continue;
		    }


		  /*in caso positivo, setta la mutex tra ciascuna delle azioni di cui il primo fatto e' prec e ciascuna delle azioni di cui il secondo fatto e' prec */
		  if (!GpG.lowmemory)
		    {
		      for (k = 0; k < gft_conn[i].num_PC; k++)
			{
			  for (l = 0; l < gft_conn[j].num_PC; l++)
			    {

			      if ( GET_EF_EF_MX_BIT(gft_conn[i].PC[k], gft_conn[j].PC[l]))
				continue;

			      if (DEBUG2)
                                  total_ef_ef_mutex++;

                              SET_EF_EF_MX_BIT (gft_conn[i].PC[k],gft_conn[j].PC[l]);

			    }
			}
		    }

		  /*inoltre, setta la mutex tra il fatto e tutte le azioni che hanno il secondo fatto come precondizione */
		  for (k = 0; k < gft_conn[j].num_PC; k++)
		    {

                      if (GET_BIT (FT_EF_mutex[i], gft_conn[j].PC[k]))
			continue;
		
		      if (DEBUG2)
			{
			  total_ft_ef_mutex++;
			  total_ef_ft_mutex++;
			}
		      
		      SET_BIT (FT_EF_mutex[i], gft_conn[j].PC[k]);

		      //setto direttamente anche la mutex tra azione e fatto
		      SET_BIT (EF_FT_mutex[gft_conn[j].PC[k]], i);
		    }
		  //e viceversa
		  for (k = 0; k < gft_conn[i].num_PC; k++)
		    {
		      if (GET_BIT (FT_EF_mutex[j], gft_conn[i].PC[k]))
			continue;
		      if (DEBUG2)			
			  {
			    total_ft_ef_mutex++;
			    total_ef_ft_mutex++;
			  }

		      SET_BIT (FT_EF_mutex[j], gft_conn[i].PC[k]);

		      //setto direttamente anche la mutex tra azione e fatto
		      SET_BIT (EF_FT_mutex[gft_conn[i].PC[k]], j);
		    }
		}
	      temp <<= 1;
	    }
	}


      //MUTEX FATTI - AZIONI
      /* Per ogni fatto, setto la mutua esclusione tra esso e le azioni di cui esso e' effetto cancellante */
      for (j = 0; j < gft_conn[i].num_D; j++)
	{
	  if (GET_BIT (FT_EF_mutex[i], gft_conn[i].D[j]))
	    continue;

	  if (DEBUG2)
	      {
		total_ft_ef_mutex++;
		total_ef_ft_mutex++;
	      }

	  SET_BIT (FT_EF_mutex[i], gft_conn[i].D[j]);

	  //ricavo direttamente la mutex tra azione e fatto
	  SET_BIT (EF_FT_mutex[gft_conn[i].D[j]], i);
	}
      
    }

  if (!GpG.lowmemory)
    {
      /* Per ogni azione A controllo se una delle sue precondizioni e' effetto cancellante di una qualche azione
	 B, in tal caso A e B sono mutex poiche' vi e' interferenza e la matrice delle mutex viene aggiornata */
       for(i=0;i<gnum_ef_conn;i++)
	{
	  for(j=0;j<gef_conn[i].num_PC;j++)
	    {
	      if(gef_conn[i].PC[j]>=0)
		{

		  for(k=0;k<gft_conn[gef_conn[i].PC[j]].num_D;k++)
		    {
		      if ( gft_conn[gef_conn[i].PC[j]].D[k] >=0)
			{
			  if(GET_EF_EF_MX_BIT(i, gft_conn[gef_conn[i].PC[j]].D[k]))
			    continue;
			  if (DEBUG2)
			    total_ef_ef_mutex++;
			  
			  SET_EF_EF_MX_BIT (i, gft_conn[gef_conn[i].PC[j]].D[k]);
			} 
		    }
		  

		  if (!GpG.durative_actions_in_domain)
		    {
		      /* NEW: Setto come mutuamente esclusive l'azione i e le azioni che hanno
		       *      per effetti additivi le precondizioni at-start di i
		       */
		      for(k=0;k<gft_conn[gef_conn[i].PC[j]].num_A;k++)
			{
			  if ( gft_conn[gef_conn[i].PC[j]].A[k] >=0)
			    {
			      if(GET_EF_EF_MX_BIT(i, gft_conn[gef_conn[i].PC[j]].A[k]))
				continue;
			      if (DEBUG2)
				total_ef_ef_mutex++;
			      
			      SET_EF_EF_MX_BIT (i, gft_conn[gef_conn[i].PC[j]].A[k]);
			    } 
			}
		    }
		}
	      
	      
	    }
	  if(gef_conn[i].sf!=NULL)
	    {
	      for(j=0;j<gef_conn[i].sf->num_PC_end;j++)
		{
		  if(gef_conn[i].sf->PC_end[j]>=0)
		    for(k=0;k<gft_conn[gef_conn[i].sf->PC_end[j]].num_D;k++)
		      { 
			if ( gft_conn[gef_conn[i].sf->PC_end[j]].D[k] >=0 )
			  {
			    if(GET_EF_EF_MX_BIT(i, gft_conn[gef_conn[i].sf->PC_end[j]].D[k]))
			      continue;
			    if (DEBUG2)
			      total_ef_ef_mutex++;
			    
			    SET_EF_EF_MX_BIT (i, gft_conn[gef_conn[i].sf->PC_end[j]].D[k]);
			  }
			
		      }
		  
		}
	      
	      
	      for(j=0;j<gef_conn[i].sf->num_PC_overall;j++)
		{
		  if(gef_conn[i].sf->PC_overall[j]>=0)
		    {

		    for(k=0;k<gft_conn[gef_conn[i].sf->PC_overall[j]].num_D;k++)
		      { 
			if ( gft_conn[gef_conn[i].sf->PC_overall[j]].D[k] >=0)
			  {
			    if (GET_EF_EF_MX_BIT(i,gft_conn[gef_conn[i].sf->PC_overall[j]].D[k]))
			      continue;
			    if (DEBUG2)
			      total_ef_ef_mutex++;
			    
			    SET_EF_EF_MX_BIT (i, gft_conn[gef_conn[i].sf->PC_overall[j]].D[k]);
			  }			
		      }

		    /* NEW: setto come mutuamente esclusive l'azione i e le azioni che hanno
		     *      per effetti additivi le precondizioni overall di i
		     */
		    for(k=0;k<gft_conn[gef_conn[i].sf->PC_overall[j]].num_A;k++)
		      { 
			if ( gft_conn[gef_conn[i].sf->PC_overall[j]].A[k] >=0)
			  {
			    if (GET_EF_EF_MX_BIT(i,gft_conn[gef_conn[i].sf->PC_overall[j]].A[k]))
			      continue;
			    if (DEBUG2)
			      total_ef_ef_mutex++;
			    
			    SET_EF_EF_MX_BIT (i, gft_conn[gef_conn[i].sf->PC_overall[j]].A[k]);
			  }			
		      }
		    
		    }
		  
		}
	      
	      
	      for(j=0;j<gef_conn[i].sf->num_A_start;j++)
		{
		  if(gef_conn[i].sf->A_start[j]>=0)
		    for(k=0;k<gft_conn[gef_conn[i].sf->A_start[j]].num_D;k++)
		      { 
			if ( gft_conn[gef_conn[i].sf->A_start[j]].D[k] >=0)
			  {
			    if (GET_EF_EF_MX_BIT(i, gft_conn[gef_conn[i].sf->A_start[j]].D[k]))
			      continue;
			    if (DEBUG2)
			      total_ef_ef_mutex++;
			    
			    SET_EF_EF_MX_BIT (i, gft_conn[gef_conn[i].sf->A_start[j]].D[k]);
			  }
			
		      }
		  
		}
	      
	    }
	  
	  
	  /*Inoltre controllo se un effetto additivo di una azione A e' effetto cancellante di una qualche azione
	    B, in tal caso A e B sono mutex per effetti inconsistenti e la matrice delle mutex viene aggiornata    */
	  for(j=0;j<gef_conn[i].num_A;j++)
	    {
	      if(gef_conn[i].A[j]>=0)
		for(k=0;k<gft_conn[gef_conn[i].A[j]].num_D;k++)
		  { 
		    if ( gft_conn[gef_conn[i].A[j]].D[k] >=0 )
		      {
			if (GET_EF_EF_MX_BIT(i, gft_conn[gef_conn[i].A[j]].D[k]))
			  continue;
			if (DEBUG2)
			  total_ef_ef_mutex++;
			
			SET_EF_EF_MX_BIT (i, gft_conn[gef_conn[i].A[j]].D[k]);
		      }
		    
		  }
	      	      
	    }
	  
	}

    }
}


/*
 * Funzione ricorsiva che incrementa i vettori (num_tested_positive e num_tested_negative)che mi dicono il numero di 
 * precondizioni per cui la variabile ncvar  contribuisce al raggiungimento rispettivamente crescendo o diminuendo 
 */

void
add_tested_vars_for_cvar (int ncvar, int * num_tested_positive,int * num_tested_negative,int *bitarray, Bool Sign)
{
  if (ncvar == -1)
    return;

  switch (gcomp_var[ncvar].operator )
    {
    case GREATER_THAN_OP:
    case GREATER_OR_EQUAL_OP:
    case EQUAL_OP:
      add_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,TRUE);
      add_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,FALSE);
      break;
      
    case LESS_THAN_OP:
    case LESS_THAN_OR_EQUAL_OP:
      add_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,FALSE);
      add_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,TRUE);
      break;

    case MUL_OP:
    case PLUS_OP:
      add_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      add_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      break;

    case DIV_OP:
    case MINUS_OP:
    case UMINUS_OP:
      add_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      add_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,!Sign);
      break;

    case VARIABLE_OP:
      SET_BIT(bitarray,ncvar);
    
      if(Sign)
	num_tested_positive[ncvar]++;
      else
	num_tested_negative[ncvar]++;
      break;

    default:
      break;
    }
}


/*
 * Funzione ricorsiva che decrementa i vettori (num_tested_positive e num_tested_negative)che mi dicono il numero di 
 * precondizioni per cui la variabile ncvar  contribuisce al raggiungimento rispettivamente crescendo o diminuendo 
 */

void
sub_tested_vars_for_cvar (int ncvar, int * num_tested_positive,int * num_tested_negative,int *bitarray, Bool Sign)
{
  if (ncvar == -1)
    return;

  switch (gcomp_var[ncvar].operator )
    {
    case GREATER_THAN_OP:
    case GREATER_OR_EQUAL_OP:
    case EQUAL_OP:
      sub_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,TRUE);
      sub_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,FALSE);
      break;

    case LESS_THAN_OP:
    case LESS_THAN_OR_EQUAL_OP:
      sub_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,FALSE);
      sub_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,TRUE);
      break;

    case MUL_OP:
    case PLUS_OP:
      sub_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      sub_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      break;

    case DIV_OP:
    case MINUS_OP:
    case UMINUS_OP:
      sub_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      sub_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,!Sign);
      break;

    case VARIABLE_OP:

      if(Sign)
	num_tested_positive[ncvar]--;
      else
	num_tested_negative[ncvar]--;

      if(num_tested_positive[ncvar]<=0 && num_tested_negative[ncvar]<=0)
	RESET_BIT(bitarray,ncvar);
     
      break;

    default:
      break;
    }
}


/*
 * Funzione che determina il numero di precondizioni numeriche non supportate dell'azione action number, 
 * setta inoltre la matrice la matrice Numeric.num_Pc_ef_matrix
 */

int  count_unsatisfied_num_preconds(int action_number,int *num_fact_vector) 
{ int i=0;  
  int num_unsatisfied_num_precond;
  
  EfConn action_considered;

  action_considered= gef_conn[action_number];
  
  num_unsatisfied_num_precond=0;

  //  /* Preconditions at start */
  
      if(Numeric.num_Pc_ef_matrix.bits == NULL)
	{
	  
	  Numeric.num_Pc_ef_matrix.max_row_size = gnum_ef_conn;
	  init_bit_table_const(gnum_ef_conn, &Numeric.num_Pc_ef_matrix.n_bit, 
			       &Numeric.num_Pc_ef_matrix.base, 
			       &Numeric.num_Pc_ef_matrix.bit_row_size);

	  Numeric.num_Pc_ef_matrix.bits = (int_pointer **)calloc(gnum_comp_var, sizeof(int_pointer *));

	}
      
      for(i = 0;i < action_considered.num_PC; i++)
	{
	  if (action_considered.PC[i]<0)
	    {
	    
	      insert_bit_in_bit_table(Numeric.num_Pc_ef_matrix, (- (action_considered.PC[i])), 
				      action_number);
	      if(!GET_BIT(num_fact_vector, (-action_considered.PC[i])))
		num_unsatisfied_num_precond++;
	    }
	  
	}
  


  return num_unsatisfied_num_precond;
}



/*
 * Funzione che esegue il refresh dei vettori vmax e vmin per le variabili midificate, restituisce
 * inoltre il numero di precondizioni passate da falso a vero in questo passaggio
 */ 

int refresh_max_min_value (float * max_value,float * min_value, int * modifieds)
{
  int i,old_value,num_Pc;

  num_Pc=0;
  
 
  //scorrere l'array modifieds e per ogni cvar modificata, rivalutare la regola
  for (i = 0; i < gnum_comp_var; i++)
    if (GET_BIT (modifieds, i))
      {
	switch (gcomp_var[i].operator)
	  {
	  case INCREASE_OP:
	  case DECREASE_OP:
	  case SCALE_UP_OP:
	  case SCALE_DOWN_OP:
	  case ASSIGN_OP:
	  case FIX_NUMBER:
	  case VARIABLE_OP:
	    break;

	  case MUL_OP:
	    max_value[i]= max_value[gcomp_var[i].first_op] *  max_value[gcomp_var[i].second_op];
	    min_value[i]= min_value[gcomp_var[i].first_op] *  min_value[gcomp_var[i].second_op];
	    break;

	  case DIV_OP:
	    max_value[i]= max_value[gcomp_var[i].first_op] /  min_value[gcomp_var[i].second_op];
	    min_value[i]= min_value[gcomp_var[i].first_op] /  max_value[gcomp_var[i].second_op];
	    break;

	  case PLUS_OP:
	    max_value[i]= max_value[gcomp_var[i].first_op] +  max_value[gcomp_var[i].second_op];
	    min_value[i]= min_value[gcomp_var[i].first_op] +  min_value[gcomp_var[i].second_op];
	    break;
	    
	  case MINUS_OP:
	    max_value[i]= max_value[gcomp_var[i].first_op] -  min_value[gcomp_var[i].second_op];
	    min_value[i]= min_value[gcomp_var[i].first_op] -  max_value[gcomp_var[i].second_op];
	    break;
	    
	  case UMINUS_OP:
	    max_value[i]=  - min_value[gcomp_var[i].first_op];
	    min_value[i]=  - max_value[gcomp_var[i].first_op];
	    break;

	  case LESS_THAN_OP:
	    old_value = max_value[i];
	    if(old_value > 0.5)
	      break;
	    
	    max_value[i] = (float) (min_value[gcomp_var[i].first_op] < max_value[gcomp_var[i].second_op]);
	    min_value[i] = (float) (min_value[gcomp_var[i].first_op] < max_value[gcomp_var[i].second_op]);
	    
	    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
	    if ((old_value < 0.5) && ( max_value[i] > 0.5))
	      {
#ifdef __TEST__
		printf("La preco %d passa da falso a vero",i);
#endif
		num_Pc++;
	      }
	    break;

	  case LESS_THAN_OR_EQUAL_OP:
	    
	    old_value = max_value[i];
	    if(old_value > 0.5)
	      break;
	    
	    max_value[i] = (float) (min_value[gcomp_var[i].first_op] <= max_value[gcomp_var[i].second_op]);
	    min_value[i] = (float) (min_value[gcomp_var[i].first_op] <= max_value[gcomp_var[i].second_op]);
	    
	    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
	    if ((old_value < 0.5) && ( max_value[i] > 0.5))
	      {
#ifdef __TEST__
		printf("La preco %d passa da falso a vero",i);
#endif
		num_Pc++;
	      }
	    break;
	    
	  case EQUAL_OP:
	    
	    old_value = max_value[i];
	    if(old_value > 0.5)
	      break;
	    
	    max_value[i] = (float) ((min_value[gcomp_var[i].first_op] <= max_value[gcomp_var[i].second_op] && (max_value[gcomp_var[i].first_op] >= max_value[gcomp_var[i].second_op])) ||
                                    ( max_value[gcomp_var[i].first_op] <= max_value[gcomp_var[i].second_op] && (min_value[gcomp_var[i].first_op] <= min_value[gcomp_var[i].second_op])));

	    min_value[i] = (float) ((min_value[gcomp_var[i].first_op] <= max_value[gcomp_var[i].second_op] && (max_value[gcomp_var[i].first_op] >= max_value[gcomp_var[i].second_op])) ||
                                    ( max_value[gcomp_var[i].first_op] <= max_value[gcomp_var[i].second_op] && (min_value[gcomp_var[i].first_op] <= min_value[gcomp_var[i].second_op])));
	   
	    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
	    if ((old_value < 0.5) && ( max_value[i] > 0.5))
	      {
#ifdef __TEST__
		printf("La preco %d passa da falso a vero",i);
#endif
		
			;
	       num_Pc++;
	      }
	    break;
	    
	  case GREATER_THAN_OP:
	    
	    old_value = max_value[i];
	    if(old_value > 0.5)
	      break;
	    
	    max_value[i] = (float) (max_value[gcomp_var[i].first_op] > min_value[gcomp_var[i].second_op]);
	    min_value[i] = (float) (max_value[gcomp_var[i].first_op] > min_value[gcomp_var[i].second_op]);
	    
	    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
	    if ((old_value < 0.5) && ( max_value[i] > 0.5))
	      {
#ifdef __TEST__
		printf("La preco %d passa da falso a vero",i);
#endif

		num_Pc++;
	      }
	    break;
	    
	  case GREATER_OR_EQUAL_OP:
	    old_value = max_value[i];
	    if(old_value > 0.5)
	      break;
	    
	    max_value[i] = (float) (max_value[gcomp_var[i].first_op] >= min_value[gcomp_var[i].second_op]);
	    min_value[i] = (float) (max_value[gcomp_var[i].first_op] >= min_value[gcomp_var[i].second_op]);
	    
	    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
	    if ((old_value < 0.5) && ( max_value[i] > 0.5))
	      {	
#ifdef __TEST__
		printf("La preco %d passa da falso a vero",i);
#endif
		num_Pc++;
	      }
	    break;
	    
	  default:
	    break;

	  }
	       
	
      }

  return num_Pc;
}


/*
 * Funzione che setta aggiorna i best- increase/decrease/assign facendo un confronto tra quelli attuali e gli effetti 
 * dell'azione i-esima
 */

void set_best_for_compvar(int i,float *vmax, float *vmin)
{

  int y,j,k;
  DescNumEff *numeric_effect;
  DescNumEff *aus_numeric_effect;

  for(j=0;j<gef_conn[i].num_numeric_effects;j++)
 
    {

    
      numeric_effect = &gef_conn[i].numeric_effects[j];
     
      switch (gcomp_var_effects[numeric_effect->index].operator)
	{
	case INCREASE_OP:
	  /*
	   * Se il best-increase non è stato ancora settato viene settato, altrimenti viene confrontato il valore 
	   * del termine a destra dei due, il maggiore diventa/resta il best-increase
	   */
	  for(y=0;y<gnum_comp_var;y++)
	    {
	      if(GET_BIT(Numeric.is_a_Pc,y))
		{
		  if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],y))
		    {
		      if(gcomp_var[y].operator==LESS_THAN_OR_EQUAL_OP||gcomp_var[y].operator==LESS_THAN_OP)		      
			continue;
		      
		      if(Hvar.ri_best_increase_for_compvar[y]<0)
			{
			  if(gcomp_var[y].operator==EQUAL_OP)
			    {
			      Hvar.ri_best_increase_for_compvar[y]=i;
			    }
			  else
			    {			      
			      cri_insert_numeric_ftcost (y, i, numeric_effect->index,INCREASE_OP);
			      
			    }
			}

		      else
			{
			  for(k=0;k<gef_conn[Hvar.ri_best_increase_for_compvar[y]].num_numeric_effects;k++)
			    {
			     
			      
			      aus_numeric_effect=&gef_conn[Hvar.ri_best_increase_for_compvar[y]].numeric_effects[k];
			      if(numeric_effect->lval == aus_numeric_effect->lval)			  
				{
				  if(gcomp_var[y].operator==EQUAL_OP)
				    {
				      if(vmax[gcomp_var_effects[numeric_effect->index].second_op] > vmax[gcomp_var_effects[aus_numeric_effect->index].second_op])
					Hvar.ri_best_increase_for_compvar[y]=i;
				    }
				  else
				    {
				      cri_insert_numeric_ftcost (y, i, numeric_effect->index,INCREASE_OP);
				    }
				  				
				}
			    }
			}			
		    }
		}
		else
		  if(y==numeric_effect->lval )
		    
		    {
		      
		      if(Hvar.ri_best_increase_for_compvar[y]<0)
			{
			  Hvar.ri_best_increase_for_compvar[y]=i;
			  Hvar.ri_max_increase_for_compvar[y]=vmax[gcomp_var_effects[numeric_effect->index].second_op];
			}
		      else
			{
			for(k=0;k<gef_conn[Hvar.ri_best_increase_for_compvar[y]].num_numeric_effects;k++)
			  {
			    
			    aus_numeric_effect=&gef_conn[Hvar.ri_best_increase_for_compvar[y]].numeric_effects[k];
			    if(numeric_effect->lval == aus_numeric_effect->lval)			  
			      if(vmax[gcomp_var_effects[numeric_effect->index].second_op] > vmax[gcomp_var_effects[aus_numeric_effect->index].second_op])
				{
				  Hvar.ri_best_increase_for_compvar[y]=i;
				  Hvar.ri_max_increase_for_compvar[y]=vmax[gcomp_var_effects[numeric_effect->index].second_op];
				}
			  }
			}	


		    }
	      

	    }
		      
	  break;
	
	case DECREASE_OP:
	  /*
	   * Se il best-decrease non è stato ancora settato viene settato, altrimenti viene confrontato il valore 
	   * del termine a destra dei due, il maggiore diventa/resta il best-decrease
	   */
	  for(y=0;y<gnum_comp_var;y++)
	    {
	      if(GET_BIT(Numeric.is_a_Pc,y))
		{
		  if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],y))
		    {
		      if(gcomp_var[y].operator==GREATER_OR_EQUAL_OP||gcomp_var[y].operator==GREATER_THAN_OP)		      
			continue;
		      
		      if(Hvar.ri_best_increase_for_compvar[y]<0)
			{
			  if(gcomp_var[y].operator==EQUAL_OP)
			    {
			      Hvar.ri_best_decrease_for_compvar[y]=i;
			    }
			  else
			    {			      
			      cri_insert_numeric_ftcost (y, i, numeric_effect->index,DECREASE_OP);
			      
			    }
			}

		      else
			{
			  for(k=0;k<gef_conn[Hvar.ri_best_decrease_for_compvar[y]].num_numeric_effects;k++)
			    {
			     			      
			      aus_numeric_effect=&gef_conn[Hvar.ri_best_decrease_for_compvar[y]].numeric_effects[k];
			      if(numeric_effect->lval == aus_numeric_effect->lval)			  
				{
				  if(gcomp_var[y].operator==EQUAL_OP)
				    {
				      if(vmax[gcomp_var_effects[numeric_effect->index].second_op] > vmax[gcomp_var_effects[aus_numeric_effect->index].second_op])
					Hvar.ri_best_decrease_for_compvar[y]=i;
				    }
				  else
				    {
				      cri_insert_numeric_ftcost (y, i, numeric_effect->index,DECREASE_OP);
				    }
				  				
				}
			    }
			}			
		    }
		}
		else
		  if(y==numeric_effect->lval )
		    
		    {
		      
		      if(Hvar.ri_best_decrease_for_compvar[y]<0)
			{
			  Hvar.ri_best_increase_for_compvar[y]=i;
			  Hvar.ri_max_decrease_for_compvar[y]=vmax[gcomp_var_effects[numeric_effect->index].second_op];
			}
		      else
			{
			  for(k=0;k<gef_conn[Hvar.ri_best_increase_for_compvar[y]].num_numeric_effects;k++)
			    {			     
			      
			      aus_numeric_effect=&gef_conn[Hvar.ri_best_increase_for_compvar[y]].numeric_effects[k];
			      if(numeric_effect->lval == aus_numeric_effect->lval)			  
				if(vmax[gcomp_var_effects[numeric_effect->index].second_op] > vmax[gcomp_var_effects[aus_numeric_effect->index].second_op])
				  {
				    Hvar.ri_best_decrease_for_compvar[y]=i;
				    Hvar.ri_max_decrease_for_compvar[y]=vmax[gcomp_var_effects[numeric_effect->index].second_op];
				  }
			    }
			}			      
		      
		    }
	      

	    }
		      
	  break;
	
	  
	case SCALE_UP_OP:
	case SCALE_DOWN_OP:
	  printf("\nThis version of LPG doesn't support SCALE_UP and SCALE_DOWN effects\n");
	  exit(0);
	  break;
	  
	case ASSIGN_OP:
	  /*
	   * Se il best-assign non è stato ancora settato viene settato, altrimenti viene confrontato il valore 
	   * del termine a destra dei due
	   */
	  for(y=0;y<gnum_comp_var;y++)
	    if(GET_BIT(Numeric.is_a_Pc,y)||y==numeric_effect->lval)
	      if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],y))
	      {
		if(Hvar.ri_best_assign_for_compvar[y]<0)
		  {
		    Hvar.ri_best_assign_for_compvar[y]=i;
		    Hvar.ri_max_assign_for_compvar[y]=vmax[gcomp_var_effects[numeric_effect->index].second_op];
		    Hvar.ri_min_assign_for_compvar[y]=vmin[gcomp_var_effects[numeric_effect->index].second_op];
		  }
	
		else
		  {
		    for(k=0;k<gef_conn[Hvar.ri_best_assign_for_compvar[y]].num_numeric_effects;k++)
		      {
		
			aus_numeric_effect=&gef_conn[Hvar.ri_best_assign_for_compvar[y]].numeric_effects[k];
			if(numeric_effect->lval == aus_numeric_effect->lval)
			  {
			    if(vmax[gcomp_var_effects[numeric_effect->index].second_op] > vmax[gcomp_var_effects[aus_numeric_effect->index].second_op])	
			      {
				Hvar.ri_best_assign_for_compvar[y]=i;
				Hvar.ri_max_assign_for_compvar[y]=vmax[gcomp_var_effects[numeric_effect->index].second_op];
			      }
			    
			    if(vmin[gcomp_var_effects[numeric_effect->index].second_op] < vmin[gcomp_var_effects[aus_numeric_effect->index].second_op])
			      {
				Hvar.ri_best_assign_for_compvar[y]=i;
				Hvar.ri_min_assign_for_compvar[y]=vmin[gcomp_var_effects[numeric_effect->index].second_op];
			      }
			  }
			
		      }
		    
		  }
	      }
	  break;
	default:
	  break;
	} 
    }
#ifdef __TEST__  
  printf(" INCREASE\n\n");
  for(j=0;j<gnum_comp_var;j++)
    if(gcomp_var[j].operator==VARIABLE_OP)
      printf("%d: %d  ",j, Hvar.ri_best_increase_for_compvar[j]);
  printf(" \nDECREASE\n\n");
  for(j=0;j<gnum_comp_var;j++)
    if(gcomp_var[j].operator==VARIABLE_OP)
      printf("%d: %d  ",j, Hvar.ri_best_decrease_for_compvar[j]);
  printf(" \nASSIGN\n\n");
  for(j=0;j<gnum_comp_var;j++)
	if(gcomp_var[j].operator==VARIABLE_OP)
	  printf("%d: %d  ",j, Hvar.ri_best_assign_for_compvar[j]);
  printf("\n\n");
#endif
  
  
}


/*
 * Funzione che va ad applicare il best-increase relativo alla variabile num_var
 */

Bool apply_best_increase_for_var(int num_var,float *vmax)
{
  int i;
  DescNumEff *numeric_effect;
  

  if(Hvar.ri_best_increase_for_compvar[num_var]<0)
    return FALSE;
  else
    for(i=0;i<gef_conn[Hvar.ri_best_increase_for_compvar[num_var]].num_numeric_effects;i++)
      {
	numeric_effect = &gef_conn[Hvar.ri_best_increase_for_compvar[num_var]].numeric_effects[i];
	if(numeric_effect->lval == num_var)
	  vmax[num_var]=vmax[num_var]+vmax[gcomp_var_effects[numeric_effect->index].second_op];
      }
  return TRUE;
}

/*
 * Funzione che va ad applicare il best-decrease relativo alla variabile num_var
 */

Bool apply_best_decrease_for_var(int num_var,float *vmax,float *vmin)
{
  int i;
  DescNumEff *numeric_effect;

  if(Hvar.ri_best_decrease_for_compvar[num_var]<0)
    return FALSE;
  else
    for(i=0;i<gef_conn[Hvar.ri_best_decrease_for_compvar[num_var]].num_numeric_effects;i++)
      {
	numeric_effect = &gef_conn[Hvar.ri_best_decrease_for_compvar[num_var]].numeric_effects[i];
	if(numeric_effect->lval == num_var)
	  vmin[num_var]=vmin[num_var]-vmax[gcomp_var_effects[numeric_effect->index].second_op];
      }
  return TRUE;

}

/*
 * Funzione che va ad applicare il best-assign relativo alla variabile num_var
 */
Bool apply_best_assign_for_var(int num_var,float *vmax,float *vmin)
{
 int i;
 DescNumEff *numeric_effect;
 Bool modificated=FALSE;
  if(Hvar.ri_best_assign_for_compvar[num_var]<0)
    return FALSE;
  else
    for(i=0;i<gef_conn[Hvar.ri_best_assign_for_compvar[num_var]].num_numeric_effects;i++)
      {
	numeric_effect = &gef_conn[Hvar.ri_best_assign_for_compvar[num_var]].numeric_effects[i];
	if(numeric_effect->lval == num_var)
	  {
	    if(vmax[gcomp_var_effects[numeric_effect->index].second_op]> vmax[num_var])
	      {
		vmax[num_var]=vmax[gcomp_var_effects[numeric_effect->index].second_op];
		modificated=TRUE;
	      }
	    if(vmin[gcomp_var_effects[numeric_effect->index].second_op]< vmin[num_var])
	      {
		vmin[num_var]=vmin[gcomp_var_effects[numeric_effect->index].second_op];
		modificated=TRUE;
	      }
	  }
      }
  return modificated;


}







/*
 * Funzione che verifica se una nuova precondizione e' stata resa supportata ed in tal caso decrementa il numero di
 * preco da supportare delle azioni che ce l'hanno come preco 
 */

Bool verify_num_preconditions( int * True_num,int *num_Pc_relevant_pos ,int *num_Pc_relevant_neg,
			      int *relevant_vars ,float *vmax ,int num_Pc)
{

  int i,j;
  Bool changed;
      
  changed=FALSE;

  for(i=0;i<gnum_comp_var;i++)
    {
      if(!GET_BIT(Numeric.is_a_Pc,i))
      	continue;
      if(GET_BIT(True_num,i))
	continue;
      /*
       * Scorro tutte le precondizioni
       */
      switch (gcomp_var[i].operator)
	{
	case LESS_THAN_OP:
	case LESS_THAN_OR_EQUAL_OP:
	  /*
	   * Se trovo una nuova preco vera vado a decrementare il numero di preco da supportare
	   * delle azioni di cui è precondizione
	   */
	  if(vmax[i] > 0.5)
	    {
	     
		  SET_BIT(True_num,i);
		  changed=TRUE;
		  for(j=0;j<gnum_ef_conn;j++)
		    {
		      if(check_bit_in_bit_table(Numeric.num_Pc_ef_matrix, i, j))
			{
			  Numeric.ri_prec_vector[j]--;
			  if(Numeric.ri_prec_vector[j]==0)
			    changed=TRUE;
			}
		      
		    }
		  sub_tested_vars_for_cvar (i,num_Pc_relevant_pos ,num_Pc_relevant_neg,relevant_vars, TRUE);
		  		      		  
		
	    }
	  /*
	   * Se invece non e' supportata ed e' una relazione di < o <= non posso raggiungere la condizione di
	   * terminazione se essa ha un best-decrease
	   */
	  else
	    if(Hvar.ri_best_decrease_for_compvar[i] >=0)
	      changed=TRUE;
	  break;
	case GREATER_THAN_OP:
	case GREATER_OR_EQUAL_OP:
	  /*
	   * Se trovo una nuova preco vera vado a decrementare il numero di preco da supportare
	   * delle azioni di cui è precondizione
	   */
	  if(vmax[i] > 0.5)
	    {
	   
		  SET_BIT(True_num,i);
		  changed=TRUE;
		  for(j=0;j<gnum_ef_conn;j++)
		    {
		      if(check_bit_in_bit_table(Numeric.num_Pc_ef_matrix, i, j))
			{
			  Numeric.ri_prec_vector[j]--;
			  if(Numeric.ri_prec_vector[j]==0)
			    changed=TRUE;
			}

		    }
		  sub_tested_vars_for_cvar (i,num_Pc_relevant_pos ,num_Pc_relevant_neg,relevant_vars, TRUE);
		  			      
		  		
	    }
	  /*
	   * Se invece non è supportata ed è una relazione di > o >= non posso raggiungere la condizione di
	   * terminazione se essa ha un best-increase
	   */
	  else
	    if(Hvar.ri_best_increase_for_compvar[i]>=0)
	      changed=TRUE;
	  break;

	case EQUAL_OP:
	  /*
	   * Se trovo una nuova preco vera vado a decrementare il numero di preco da supportare
	   * delle azioni di cui è precondizione
	   */
	  if(vmax[i] > 0.5)
	    {
	      
		  SET_BIT(True_num,i);
		  changed=TRUE;
		  for(j=0;j<gnum_ef_conn;j++)
		    {
		      if(check_bit_in_bit_table(Numeric.num_Pc_ef_matrix, i, j))
			{
			  Numeric.ri_prec_vector[j]--;
			  if(Numeric.ri_prec_vector[j]==0)
			    changed=TRUE;
			}
			      
		    }
		  sub_tested_vars_for_cvar (i,num_Pc_relevant_pos ,num_Pc_relevant_neg,relevant_vars, TRUE);
		  			      
		  
		
	    }
	  /*
	   * Se invece non è supportata ed è una relazione di == non posso raggiungere la condizione di
	   * terminazione se essa ha un best-decrease o un best-increase
	   */
	  else
	    if(Hvar.ri_best_increase_for_compvar[i]>=0 ||Hvar.ri_best_decrease_for_compvar[i]>=0 )
	      changed=TRUE;

	  break;
	default:
	  break;
	  
	  
	}
      
      
    }


  return changed;

}

