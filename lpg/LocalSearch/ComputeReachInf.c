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
 * File: ComputeReachInf.c
 * Description: Compute Reachability Information.
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
#include "numeric.h"
#include "mutex.h"
#include "derivedpred.h"


//#define __TEST_UPD__


void allocate_reachability_compvar_information_data(void)
{

  int i;

  Hvar.init_num_facts_array = (dg_num_inform_list *) calloc (gnum_comp_var, sizeof (dg_num_inform_list));
  
  if(Hvar.common_max_values==NULL)
    Hvar.common_max_values = (float *)calloc(gnum_comp_var,sizeof(float));
  
  if(Hvar.common_min_values==NULL)
    Hvar.common_min_values = (float *)calloc(gnum_comp_var,sizeof(float));
  
  if(Hvar.common_level_supported_numeric_preconditions==NULL)
    Hvar.common_level_supported_numeric_preconditions=alloc_vect (gnum_block_compvar);
  
  Hvar.ri_tot_cost_of_numeric_facts= calloc (gnum_comp_var, sizeof (float));
  Hvar.ri_cost_of_numeric_facts= calloc (gnum_comp_var, sizeof (float));
  Hvar.ri_duration_of_numeric_facts= calloc (gnum_comp_var, sizeof (float));
  Hvar.ri_num_actions_of_numeric_facts= calloc (gnum_comp_var, sizeof (int));
  
  Hvar.ri_best_increase_for_compvar = alloc_vect (gnum_comp_var);
  Hvar.ri_best_decrease_for_compvar = alloc_vect (gnum_comp_var);
  Hvar.ri_best_assign_for_compvar = alloc_vect (gnum_comp_var);
  Hvar.max_values = (float *) calloc (gnum_comp_var, sizeof (float));
  Hvar.min_values = (float *) calloc (gnum_comp_var, sizeof (float));
  Hvar.ri_bit_vect_numeric_facts=alloc_vect (gnum_block_compvar);
  Hvar.ri_bit_vect_supp_numeric_facts=alloc_vect (gnum_block_compvar);
  Hvar.ri_initial_bit_vect_numeric_facts=alloc_vect (gnum_block_compvar);
  
  Hvar.ri_max_increase_for_compvar= (float *) calloc (gnum_comp_var, sizeof (float));
  Hvar.ri_max_decrease_for_compvar= (float *) calloc (gnum_comp_var, sizeof (float));
  Hvar.ri_max_assign_for_compvar= (float *) calloc (gnum_comp_var, sizeof (float));
  Hvar.ri_min_assign_for_compvar= (float *) calloc (gnum_comp_var, sizeof (float));

  memset(Hvar.ri_tot_cost_of_numeric_facts,0,gnum_comp_var*sizeof (float));
  memset(Hvar.ri_cost_of_numeric_facts,0,gnum_comp_var*sizeof (float));
  memset(Hvar.ri_duration_of_numeric_facts,0,gnum_comp_var* sizeof (float));
  memset(Hvar.ri_num_actions_of_numeric_facts,0,gnum_comp_var*sizeof (int));
  memcpy (Hvar.common_max_values,ginitial_state.V ,gnum_comp_var*sizeof (float));
  memcpy (Hvar.common_min_values,ginitial_state.V ,gnum_comp_var*sizeof (float));
  reset_bitarray(Hvar.ri_initial_bit_vect_numeric_facts,gnum_block_compvar);
  memset(Hvar.ri_best_increase_for_compvar, INFINITY ,  gnum_comp_var* sizeof(int));
  memset(Hvar.ri_best_decrease_for_compvar, INFINITY ,  gnum_comp_var* sizeof(int));
  memset(Hvar.ri_best_assign_for_compvar, INFINITY ,  gnum_comp_var* sizeof(int));
  
  for (i = 0; i <  gnum_comp_var; i++) {
    Hvar.ri_max_increase_for_compvar[i] = Hvar.ri_max_decrease_for_compvar[i] =
      Hvar.ri_max_assign_for_compvar[i] = Hvar.ri_min_assign_for_compvar[i] = MIN_NEG_VALUE;
  }
}

/**
 * Name: allocate_reachability_information_data
 * Purpose: Data structures allocation for Compute_reachability_information
 * Type: void
 * Input: None
 * Output: None
 * Main Data Structures: Hvar
 * Main functions used: None
 * Called by: main
 **/

void allocate_reachability_information_data()
{

  int i;

  /**
     Allocation of Data Structures for heuristics
   **/
  if (!Hvar.init_facts_array)
    Hvar.init_facts_array = (dg_inform_list *) calloc (gnum_ft_conn, sizeof (dg_inform_list));

  if (!Hvar.dg_facts_min_duration)
    Hvar.dg_facts_min_duration = (float *) calloc (gnum_ft_conn, sizeof (float));
  
  if (!Hvar.bit_vect_facts)
    Hvar.bit_vect_facts = alloc_vect (gnum_ft_block);

  if (!Hvar.bit_vect_actions)
    Hvar.bit_vect_actions = alloc_vect (gnum_ef_block);
 
  Hvar.local_bit_vect_facts = alloc_vect (gnum_ft_block);
  Hvar.local_bit_vect_actions = alloc_vect (gnum_ef_block);
  
  if(Hvar.estimate_time_facts==NULL) 
    Hvar.estimate_time_facts=(float *)calloc(gnum_ft_conn, sizeof (float));

  Hvar.initial_relaxed_bit_vect_facts = alloc_vect (gnum_ft_block);
  Hvar.threated_bit_vect_facts = alloc_vect (gnum_ft_block);
  Hvar.relaxed_bit_vect_preconds = alloc_vect (gnum_ft_block);
 
  Hvar.list_ef_define_cost = (int *) calloc (MAX_LENGTH_H, sizeof (int));
  Hvar.list_ft_define_cost = (int *) calloc (MAX_LENGTH_H, sizeof (int));

  /** 
      Allocation and Initialization of data structures for compute reachability information
   **/
  Hvar.ri_best_act_for_facts = alloc_vect (gnum_ft_conn);

  Hvar.ri_tot_cost_of_facts= calloc (gnum_ft_conn, sizeof (float));
  Hvar.ri_cost_of_facts = calloc (gnum_ft_conn, sizeof (float));
  Hvar.ri_duration_of_facts = calloc (gnum_ft_conn, sizeof (float));
  Hvar.ri_num_actions_of_facts = calloc (gnum_ft_conn, sizeof (int));

  Hvar.ri_list_ef_define_cost=(int *) calloc (MAX_LENGTH_H, sizeof (int));
 
  Hvar.ri_supp_bit_vect_facts = alloc_vect (gnum_ft_block);

  Hvar.ri_bit_vect_actions = alloc_vect (gnum_ef_block);
 
  Hvar.ri_num_actions_define_cost=0;
  Hvar.ri_num_facts_define_cost=0;

  for (i = 0; i < gnum_ft_conn; i++)
    Hvar.dg_facts_min_duration[i] =  MAX_COST;
  
  //memset(Hvar.dg_facts_min_duration, MAX_COST,  gnum_ft_conn * sizeof(float));

  memset(Hvar.ri_best_act_for_facts, INFINITY ,  gnum_ft_conn* sizeof(int));

  Hvar.ri_num_actions_of_actions=alloc_vect (gnum_ef_conn);
  Hvar.ri_cost_of_actions=  calloc (gnum_ef_conn, sizeof (float));
  
  //memset(Hvar.ri_max_increase_for_compvar, MIN_NEG_VALUE ,  gnum_comp_var* sizeof(float));
  //memset(Hvar.ri_max_decrease_for_compvar, MIN_NEG_VALUE ,  gnum_comp_var* sizeof(float));
  //memset(Hvar.ri_max_assign_for_compvar, MIN_NEG_VALUE ,  gnum_comp_var* sizeof(float));
  //memset(Hvar.ri_min_assign_for_compvar, MIN_NEG_VALUE,  gnum_comp_var* sizeof(float));

  memset(Hvar.ri_tot_cost_of_facts,0,gnum_ft_conn*sizeof (float));
  memset(Hvar.ri_cost_of_facts ,0,gnum_ft_conn* sizeof (float));
  memset(Hvar.ri_duration_of_facts,0,gnum_ft_conn* sizeof (float));
  memset( Hvar.ri_num_actions_of_facts,0,gnum_ft_conn* sizeof (int));

  last_best_act_cost = calloc(gnum_ef_conn, sizeof(last_cost));

  for (i = 0; i < gnum_ef_conn; i++) {
    last_best_act_cost[i].step = INITIALIZE_STEP;
    last_best_act_cost[i].saved_prec = 0;
  }

}



void reset_timed_preconds_in_Hvar()
{
  Hvar.num_tmd_facts_array=0;
  reset_bitarray(Hvar.bit_array_tmd_facts_array, gnum_ft_block);
   
}


void insert_timed_preconds_in_Hvar(int act_pos)
{
  int i,pc;

  for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_start; i++) 
    {
      pc = gef_conn[act_pos].timed_PC -> PC_start[i];
      
      if (pc < 0)
	continue;
     
      if(GET_BIT( Hvar.bit_array_tmd_facts_array,pc))
	continue;

      SET_BIT( Hvar.bit_array_tmd_facts_array,pc);
      
      Hvar.tmd_facts_array[Hvar.num_tmd_facts_array]=pc;

      Hvar.num_tmd_facts_array++;


    }

    // Precondizioni overall
    for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_overall; i++) {
      pc = gef_conn[act_pos].timed_PC -> PC_overall[i];

      if (pc < 0)
	continue;
      
   
      if(GET_BIT( Hvar.bit_array_tmd_facts_array,pc))
	continue;

      SET_BIT( Hvar.bit_array_tmd_facts_array,pc);
      
      Hvar.tmd_facts_array[Hvar.num_tmd_facts_array]=pc;

      Hvar.num_tmd_facts_array++;


    }

   
    // Precondizioni at end
    for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_end; i++) {
      pc = gef_conn[act_pos].timed_PC -> PC_end[i];
      
      if (pc < 0)
	continue;
      
      if(GET_BIT( Hvar.bit_array_tmd_facts_array,pc))
	continue;

      SET_BIT( Hvar.bit_array_tmd_facts_array,pc);
      
      Hvar.tmd_facts_array[Hvar.num_tmd_facts_array]=pc;

      Hvar.num_tmd_facts_array++;


    }


}






void ri_apply_action_effects_to_max_min_value(int action_number, int times)
{

  int i;
  
  DescNumEff *numeric_effect;

  

  for(i=0;i<gef_conn[action_number].num_numeric_effects;i++)
    {
      numeric_effect = &gef_conn[action_number].numeric_effects[i];
    
      
       switch (gcomp_var_effects[numeric_effect->index].operator)
	{
	case INCREASE_OP:
	  Hvar.max_values[numeric_effect->lval] = Hvar.max_values[numeric_effect->lval]+ (times* Hvar.max_values[gcomp_var_effects[numeric_effect->index].second_op]);
	  Hvar.modifieds_values=1;
	  break;

	case DECREASE_OP:
	  Hvar.min_values[numeric_effect->lval] = Hvar.min_values[numeric_effect->lval] - (times* Hvar.max_values[gcomp_var_effects[numeric_effect->index].second_op]);
	  Hvar.modifieds_values=1;
	  break;

	case ASSIGN_OP:
	  if( Hvar.max_values[numeric_effect->lval] < Hvar.max_values[gcomp_var_effects[numeric_effect->index].second_op])
	    {
	      Hvar.max_values[numeric_effect->lval] = Hvar.max_values[gcomp_var_effects[numeric_effect->index].second_op];
	      Hvar.modifieds_values=1;
	    }
	  if( Hvar.min_values[numeric_effect->lval] > Hvar.min_values[gcomp_var_effects[numeric_effect->index].second_op])
	    {
	      Hvar.min_values[numeric_effect->lval] = Hvar.min_values[gcomp_var_effects[numeric_effect->index].second_op];
	      Hvar.modifieds_values=1;
	    }
	  break;
	
	default:
	  break;
	}

    }

}




void ri_refresh_max_min_value (int * modifieds)
{
  int i,old_value;

  
  
 
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
	    Hvar.max_values[i]= Hvar.max_values[gcomp_var[i].first_op] *  Hvar.max_values[gcomp_var[i].second_op];
	    Hvar.min_values[i]= Hvar.min_values[gcomp_var[i].first_op] *  Hvar.min_values[gcomp_var[i].second_op];
	    break;

	  case DIV_OP:
	    Hvar.max_values[i]= Hvar.max_values[gcomp_var[i].first_op] /  Hvar.min_values[gcomp_var[i].second_op];
	    Hvar.min_values[i]= Hvar.min_values[gcomp_var[i].first_op] /  Hvar.max_values[gcomp_var[i].second_op];
	    break;

	  case PLUS_OP:
	    Hvar.max_values[i]= Hvar.max_values[gcomp_var[i].first_op] +  Hvar.max_values[gcomp_var[i].second_op];
	    Hvar.min_values[i]= Hvar.min_values[gcomp_var[i].first_op] +  Hvar.min_values[gcomp_var[i].second_op];
	    break;
	    
	  case MINUS_OP:
	    Hvar.max_values[i]= Hvar.max_values[gcomp_var[i].first_op] -  Hvar.min_values[gcomp_var[i].second_op];
	    Hvar.min_values[i]= Hvar.min_values[gcomp_var[i].first_op] -  Hvar.max_values[gcomp_var[i].second_op];
	    break;
	    
	  case UMINUS_OP:
	    Hvar.max_values[i]=  - Hvar.min_values[gcomp_var[i].first_op];
	    Hvar.min_values[i]=  - Hvar.max_values[gcomp_var[i].first_op];
	    break;

	  case LESS_THAN_OP:
	    old_value = Hvar.max_values[i];
	    if(old_value > 0.5)
	      break;
	    
	    Hvar.max_values[i] = (float) (Hvar.min_values[gcomp_var[i].first_op] < Hvar.max_values[gcomp_var[i].second_op]);
	    Hvar.min_values[i] = (float) (Hvar.min_values[gcomp_var[i].first_op] < Hvar.max_values[gcomp_var[i].second_op]);
	    
	    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
	    if ((old_value < 0.5) && ( Hvar.max_values[i] > 0.5))
	      {
#ifdef __TEST__
		printf("La preco %d passa da falso a vero",i);
#endif
		ri_sub_tested_vars_for_cvar (i,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
		SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,i);
	      }
	    break;

	  case LESS_THAN_OR_EQUAL_OP:
	    
	    old_value = Hvar.max_values[i];
	    if(old_value > 0.5)
	      break;
	    
	    Hvar.max_values[i] = (float) (Hvar.min_values[gcomp_var[i].first_op] <= Hvar.max_values[gcomp_var[i].second_op]);
	    Hvar.min_values[i] = (float) (Hvar.min_values[gcomp_var[i].first_op] <= Hvar.max_values[gcomp_var[i].second_op]);
	    
	    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
	    if ((old_value < 0.5) && ( Hvar.max_values[i] > 0.5))
	      {
#ifdef __TEST__
		printf("La preco %d passa da falso a vero",i);
#endif
		ri_sub_tested_vars_for_cvar (i,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
		SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,i);
	      }
	    break;
	    
	  case EQUAL_OP:
	    
	    old_value = Hvar.max_values[i];
	    if(old_value > 0.5)
	      break;
	    
	    Hvar.max_values[i] = (float) ((Hvar.min_values[gcomp_var[i].first_op] <= Hvar.max_values[gcomp_var[i].second_op] && (Hvar.max_values[gcomp_var[i].first_op] >= Hvar.max_values[gcomp_var[i].second_op])) ||
                                    ( Hvar.max_values[gcomp_var[i].first_op] <= Hvar.max_values[gcomp_var[i].second_op] && (Hvar.min_values[gcomp_var[i].first_op] <= Hvar.min_values[gcomp_var[i].second_op])));

	    Hvar.min_values[i] = (float) ((Hvar.min_values[gcomp_var[i].first_op] <= Hvar.max_values[gcomp_var[i].second_op] && (Hvar.max_values[gcomp_var[i].first_op] >= Hvar.max_values[gcomp_var[i].second_op])) ||
                                    ( Hvar.max_values[gcomp_var[i].first_op] <= Hvar.max_values[gcomp_var[i].second_op] && (Hvar.min_values[gcomp_var[i].first_op] <= Hvar.min_values[gcomp_var[i].second_op])));
	   
	    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
	    if ((old_value < 0.5) && ( Hvar.max_values[i] > 0.5))
	      {
#ifdef __TEST__
		printf("La preco %d passa da falso a vero",i);
#endif
					
	     	ri_sub_tested_vars_for_cvar (i,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
		SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,i);
	      }
	    break;
	    
	  case GREATER_THAN_OP:
	    
	    old_value = Hvar.max_values[i];
	    if(old_value > 0.5)
	      break;
	    
	    Hvar.max_values[i] = (float) (Hvar.max_values[gcomp_var[i].first_op] > Hvar.min_values[gcomp_var[i].second_op]);
	    Hvar.min_values[i] = (float) (Hvar.max_values[gcomp_var[i].first_op] > Hvar.min_values[gcomp_var[i].second_op]);
	    
	    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
	    if ((old_value < 0.5) && ( Hvar.max_values[i] > 0.5))
	      {
#ifdef __TEST__
		printf("La preco %d passa da falso a vero",i);
#endif

	       	ri_sub_tested_vars_for_cvar (i,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
		SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,i);
	      }
	    break;
	    
	  case GREATER_OR_EQUAL_OP:
	    old_value = Hvar.max_values[i];
	    if(old_value > 0.5)
	      break;
	    
	    Hvar.max_values[i] = (float) (Hvar.max_values[gcomp_var[i].first_op] >= Hvar.min_values[gcomp_var[i].second_op]);
	    Hvar.min_values[i] = (float) (Hvar.max_values[gcomp_var[i].first_op] >= Hvar.min_values[gcomp_var[i].second_op]);
	    
	    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
	    if ((old_value < 0.5) && ( Hvar.max_values[i] > 0.5))
	      {	
#ifdef __TEST__
		printf("La preco %d passa da falso a vero",i);
#endif
		ri_sub_tested_vars_for_cvar (i,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
		SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,i);
	      }
	    break;
	    
	  default:
	    break;

	  }
	       
	
      }

}


void
ri_add_tested_vars_for_cvar (int ncvar, int * num_tested_positive,int * num_tested_negative,int *bitarray, Bool Sign)
{
  if (ncvar == -1)
    return;

  switch (gcomp_var[ncvar].operator )
    {
    case GREATER_THAN_OP:
    case GREATER_OR_EQUAL_OP:
    case EQUAL_OP:
      ri_add_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,TRUE);
      ri_add_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,FALSE);
      break;
      
    case LESS_THAN_OP:
    case LESS_THAN_OR_EQUAL_OP:
      ri_add_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,FALSE);
      ri_add_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,TRUE);
      break;

    case MUL_OP:
    case PLUS_OP:
      ri_add_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      ri_add_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      break;

    case DIV_OP:
    case MINUS_OP:
    case UMINUS_OP:
      ri_add_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      ri_add_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,!Sign);
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



void
ri_sub_tested_vars_for_cvar (int ncvar, int * num_tested_positive,int * num_tested_negative,int *bitarray, Bool Sign)
{
  if (ncvar == -1)
    return;

  switch (gcomp_var[ncvar].operator )
    {
    case GREATER_THAN_OP:
    case GREATER_OR_EQUAL_OP:
    case EQUAL_OP:
      ri_sub_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,TRUE);
      ri_sub_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,FALSE);
      break;

    case LESS_THAN_OP:
    case LESS_THAN_OR_EQUAL_OP:
      ri_sub_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,FALSE);
      ri_sub_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,TRUE);
      break;

    case MUL_OP:
    case PLUS_OP:
      ri_sub_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      ri_sub_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      break;

    case DIV_OP:
    case MINUS_OP:
    case UMINUS_OP:
      ri_sub_tested_vars_for_cvar (gcomp_var[ncvar].first_op,num_tested_positive,num_tested_negative,bitarray,Sign);
      ri_sub_tested_vars_for_cvar (gcomp_var[ncvar].second_op,num_tested_positive,num_tested_negative,bitarray,!Sign);
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



/**
 * Name: cri_compute_action_cost
 * Purpose: Utility for Compute Reachability Information:
 *          Set an action to belongs to ACTS
 *          Insert in the set G of the fact that must be supported
 *          the preconditions of the action
 * Main functions used: print_op_name (for debug)
 *                      is_fact_in_delete_effects 
 * Called by: cri_predict_cost_relaxed
 *            cri_compute_fact_cost
 **/

int cri_compute_action_cost (int pos,int times)
{
  int i;

#ifdef __TEST__
  printf ("\n::: Insert ACTION %d in list:", pos);
  print_op_name (pos);
  printf ("\n Hvar.ri_num_actions_define_cost %d", Hvar.ri_num_actions_define_cost);
#endif

  /** 
     Se l'azione è già inserita nella lista la funzione è stata
     richiamata erroneamente,quindi segnala con un errore ed esci
     *
     If the action is already inserted in the set, then signal error 
  **/
  
  if (GET_BIT (Hvar.ri_bit_vect_actions, pos) != 0)
    {
#ifdef __TEST__
      printf ("\n ACTION %d already in list:", pos);
      print_op_name (pos);
      printf ("\n Hvar.ri_num_actions_define_cost %d ", Hvar.ri_num_actions_define_cost);
#endif
      if(times>1) 
	{
	  /**
	     Increase the cost
	   **/


	  Hvar.ri_cost_actions_define_cost += times * get_action_cost (pos, -1, NULL);
  
	  /**
	     And apply num effects
	   **/
	  if(gef_conn[pos].is_numeric)
	    {
	      if(gef_conn[pos].num_numeric_effects>0)
		{
		  ri_apply_action_effects_to_max_min_value(pos,times);
		}
	      
	    }

	}

      return 0;
    }
  
 
  /**
    Controlla se si eccede il numero massimo di azioni inseribili
    *
    Check if the maximum number of actions exceed the lenght 
    of Hvar.ri_list_ef_define_cost
  **/  
  if (Hvar.ri_num_actions_define_cost >= MAX_LENGTH_H) {
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_MAX_LENGTH_H );
#else 
    printf( WAR_MAX_LENGTH_H );
#endif    
    exit (0);
  }
  
  /** 
     Inserisce l'azione nell'insieme delle azioni utilizzate
     *
     Insert the action in the set of the actions used and set the bit-array
  **/
  
  Hvar.ri_list_ef_define_cost[Hvar.ri_num_actions_inserted++] = pos;

  Hvar.ri_num_actions_define_cost+=times;

  SET_BIT (Hvar.ri_bit_vect_actions, pos);

  Hvar.ri_cost_actions_define_cost += times * get_action_cost (pos, -1, NULL);








  /** 
      Inserisci nell'insieme G dei fatti da supportare 
     le precondizioni at start dell'azione "index"
     * 
     Insert in the set G of the fact that must be supported the
     at start precondition of the action "pos"
  **/
  for (i = 0; i < gef_conn[pos].num_PC; i++)
    {
      cri_compute_fact_cost (gef_conn[pos].PC[i]);
    }

  if (gef_conn[pos].sf)
    {
      /** 
	  Inserisci nell'insieme G dei fatti da supportare 
	  le precondizioni over all dell'azione "pos"
	  * 
	  Insert in the set G of the fact that must be supported the
	  over all precondition of the action "pos"
      **/
     for (i = 0; i < gef_conn[pos].sf->num_PC_overall; i++)
       {
	 /** 
	     Se il fatto appartiene agli effetti at_start e' gia' supportato 
	     dall'azione stessa, quindi non viene preso in considerazione
	     *
	     if the fact is an at start effect then it  is already supported
	     by the action "pos" so it doesn't need to be considered
	 **/ 
	 if (!is_fact_in_additive_effects_start
	     (pos, gef_conn[pos].sf->PC_overall[i]))
	   cri_compute_fact_cost(gef_conn[pos].sf->PC_overall[i]);
       }

      /** 
	  Inserisci nell'insieme G dei fatti da supportare 
	  le precondizioni at end dell'azione "pos"
	  * 
	  Insert in the set G of the fact that must be supported the
	  at end precondition of the action "pos"
      **/
      for (i = 0; i < gef_conn[pos].sf->num_PC_end; i++)
	{
	  /**
	     Se il fatto appartiene agli effetti at_start e' gia' 
	     supportato dall'azione stessa, quindi non viene preso 
	     in considerazione
	     *
	     if the fact is an at start effect is already supported
	     by the action "pos" so it doesn't need to be considered
	  **/ 
	  if (!is_fact_in_additive_effects_start(pos, gef_conn[pos].sf->PC_end[i]))
	    cri_compute_fact_cost(gef_conn[pos].sf->PC_end[i]);
	}
    }










  /** 
     Setta come supportati tutti i fatti che sono effetti additivi
     at end dell'azione appena inserita, a tal proposito utilizza il bit
     vector Hvar.ri_supp_bit_vect_facts
     *
     Set the at end additive effects like supported, using bit-array
     Hvar.ri_supp_bit_vect_facts
  **/
  for (i = 0; i < gef_conn[pos].num_A; i++)  //  AT END Effects
    {
      if (gef_conn[pos].A[i] >= 0)
	SET_BIT(Hvar.ri_supp_bit_vect_facts,gef_conn[pos].A[i]);
      // else NUMERIC Effect
    }

  /**
     Setta come supportati tutti i fatti che sono effetti additivi
     at start dell'azione appena inserita  a tal proposito utilizza il bit
     vector Hvar.ri_supp_bit_vect_facts
     *
     Set the at start additive effects like supported, using bit-array
     Hvar.ri_supp_bit_vect_facts
  **/
  if (gef_conn[pos].sf != NULL)
    for (i = 0; i < gef_conn[pos].sf->num_A_start; i++)   //  AT START Effects
      {
	if (is_fact_in_delete_effects (pos, gef_conn[pos].sf->A_start[i]))
	  continue;

	if (gef_conn[pos].sf->A_start[i] >= 0)
	  SET_BIT(Hvar.ri_supp_bit_vect_facts, gef_conn[pos].sf->A_start[i]);
	//else  NUMERIC Effect
      }


  if(gef_conn[pos].is_numeric)
    {
      if(gef_conn[pos].num_numeric_effects>0)
	{
	  ri_apply_action_effects_to_max_min_value(pos,times);
	}

    }

 

  if(GpG.first_execution_cri==0 && GpG.timed_facts_present && GET_BIT(GpG.has_timed_preconds,pos))
    insert_timed_preconds_in_Hvar(pos);

  



#ifdef __TEST__
  printf ("\n:::2 Insert ACTION %d in list:", pos);
  print_op_name (pos);
  printf ("\n Hvar.ri_num_actions_define_cost %d", Hvar.ri_num_actions_define_cost);
#endif

  return 1;

}





/**
 * Name: cri_get_best_action_for_fct
 * Purpose: extract from the Resources_struct the pointer to the 
 *          minimal_cost action step 5 of RequiredActions (JAIR 03)
 * Functions used:
 * Called by: cri_predict_cost_sum
 *            cri_predict_cost_max
 *            cri_predict_duration
 **/

int cri_get_best_action_for_fct (int fact_pos)
{
  dg_inform_list loc_dg_cost;
  /** 
     This function does not consider numeric facts 
  **/
  if (fact_pos < 0)
    return INFINITY;


  if(GpG.cri_initial_or_update<=1 )
    {
      /**
	 Sto calcolando informazioni raggiungibilita' iniziali
	 o dovute ad inserimento di una azione nell'action graph 
      **/



      if( Hvar.ri_best_act_for_facts[fact_pos]==INFINITY) {  
	printf("\nError act for fct %d ",fact_pos);
	print_ft_name(fact_pos);
      }

      /**
	 Ritorna la migliore azione che supporta il fatto in posizione fact_pos
	 *
	 Returns the best action that supports the fact "fact_pos"
      **/ 
      return ( Hvar.ri_best_act_for_facts[fact_pos] );

    }
  else
    {
      /**
	 Update phase
       **/
      
      get_dg_fact_cost(fact_pos, GpG.cri_update_level,  &loc_dg_cost);
      if(loc_dg_cost==NULL)
	return INITIAL_ACTION;
      else
	return loc_dg_cost->best_act;

    }

}

/**
 * Name: reset_cri_list
 * Purpose: Reset the structure for handling reachability informations
 * Main functions used: reset_bitarray (for reset)
 * Called by: cri_predict_cost_relaxed
 *
 * Nome: reset_cri_list
 * Scopo: Resetta la struttura per la
 *        determinazione dei costi di raggiungibilità
 * Funzioni chiamare:  reset_bitarray (per reset)
 * Chiamata da: cri_predict_cost_relaxed
 **/
void reset_cri_list()
{
  Hvar.ri_num_actions_define_cost = 0;
  Hvar.ri_num_actions_inserted = 0;
  Hvar.ri_num_facts_define_cost = 0;
  Hvar.ri_cost_actions_define_cost=0.0;
  Hvar.ri_time_actions_define_cost=0.0;

  reset_bitarray (Hvar.ri_bit_vect_actions, gnum_ef_block);

  //#ifdef __TEST_REACH__
  reset_bitarray (Hvar.ri_bit_vect_numeric_facts, gnum_block_compvar);  
  memcpy(Hvar.ri_bit_vect_numeric_facts,Hvar.ri_initial_bit_vect_numeric_facts,gnum_block_compvar* sizeof(int));
  memcpy(Hvar.ri_bit_vect_supp_numeric_facts,Hvar.ri_initial_bit_vect_numeric_facts,gnum_block_compvar* sizeof(int));
  //#endif


}



/**
 * Nome: cri_insert_action_preconditions 
 * Scopo: Inserisce nell'insieme G dei fatti da supportare 
 *        le precondizioni dell'azione
 * Funzioni chiamate: cri_compute_fact_cost  (per calcolare costo una precondizione)
 * Chiamata da: 
 *
 * Name:  cri_insert_action_preconditions 
 * Purpose: Insert in the set G of the fact that must be supported
 *          the preconditions of the action
 * Main functions used:  cri_compute_fact_cost(in order to compute a precondition cost)
 * Called by: 
 **/
void
cri_insert_action_preconditions (int index)
{
  int i = 0;



 if (GET_BIT (Hvar.ri_bit_vect_actions, index) != 0)
    {
#ifdef __TEST__
      printf ("\n ACTION %d already in list:", index);
      print_op_name (pos);
      printf ("\n Hvar.ri_num_actions_define_cost %d ", Hvar.ri_num_actions_define_cost);
#endif
      return;
    }



  /** 
      Inserisci nell'insieme G dei fatti da supportare 
     le precondizioni at start dell'azione "index"
     * 
     Insert in the set G of the fact that must be supported the
     at start precondition of the action "index"
  **/
  for (i = 0; i < gef_conn[index].num_PC; i++)
    {
      cri_compute_fact_cost (gef_conn[index].PC[i]);
    }

  if (gef_conn[index].sf)
    {
      /** 
	  Inserisci nell'insieme G dei fatti da supportare 
	  le precondizioni over all dell'azione "index"
	  * 
	  Insert in the set G of the fact that must be supported the
	  over all precondition of the action "index"
      **/
     for (i = 0; i < gef_conn[index].sf->num_PC_overall; i++)
       {
	 /** 
	     Se il fatto appartiene agli effetti at_start e' gia' supportato 
	     dall'azione stessa, quindi non viene preso in considerazione
	     *
	     if the fact is an at start effect then it  is already supported
	     by the action "index" so it doesn't need to be considered
	 **/ 
	 if (!is_fact_in_additive_effects_start
	     (index, gef_conn[index].sf->PC_overall[i]))
	   cri_compute_fact_cost(gef_conn[index].sf->PC_overall[i]);
       }

      /** 
	  Inserisci nell'insieme G dei fatti da supportare 
	  le precondizioni at end dell'azione "index"
	  * 
	  Insert in the set G of the fact that must be supported the
	  at end precondition of the action "index"
      **/
      for (i = 0; i < gef_conn[index].sf->num_PC_end; i++)
	{
	  /**
	     Se il fatto appartiene agli effetti at_start e' gia' 
	     supportato dall'azione stessa, quindi non viene preso 
	     in considerazione
	     *
	     if the fact is an at start effect is already supported
	     by the action "index" so it doesn't need to be considered
	  **/ 
	  if (!is_fact_in_additive_effects_start(index, gef_conn[index].sf->PC_end[i]))
	    cri_compute_fact_cost(gef_conn[index].sf->PC_end[i]);
	}
    }

}






void
cri_insert_best_for_comp_var (int index)
{

  int i,k;
  DescNumEff *numeric_effect;


  if(GpG.cri_initial_or_update>0)
    {
      /**
	 Per ragioni di efficienza non aggiorno il best action ed il 
	 best increase ed utilizzo i migliori calcolati  
       **/
      Hvar.ri_num_actions_define_cost+= num_action_for_unsup_num_precondition(index, GpG.cri_update_level+1);

      return;
    }
  //  else
  switch (gcomp_var[index].operator)
    {
    case LESS_THAN_OP:
      
      if(Hvar.ri_best_assign_for_compvar[index]>=0)
	{
	  for(i=0;i<gef_conn[Hvar.ri_best_assign_for_compvar[index]].num_numeric_effects;i++)
	    {
	      numeric_effect=&gef_conn[Hvar.ri_best_assign_for_compvar[index]].numeric_effects[i];
	      if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],gcomp_var[index].first_op))
		{
		  if(Hvar.min_values[gcomp_var_effects[numeric_effect->index].second_op]<Hvar.max_values[gcomp_var[index].second_op])
		    {
	
		      cri_compute_action_cost (Hvar.ri_best_assign_for_compvar[index],1 );
		      SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,index);

		      return;
		    }
		  
		}
	      
	    }
	}
      

      else
	{
	  if(Hvar.ri_best_decrease_for_compvar[index]<0)
	    {
	      
	      if (Hvar.ri_best_decrease_for_compvar[gcomp_var[index].first_op] > Hvar.ri_best_increase_for_compvar[gcomp_var[index].second_op])
		Hvar.ri_best_decrease_for_compvar[index] = Hvar.ri_best_decrease_for_compvar[gcomp_var[index].first_op];
	      else
		Hvar.ri_best_decrease_for_compvar[index] = Hvar.ri_best_increase_for_compvar[gcomp_var[index].second_op];
	      
	      // Utilizzare il best descrease del membro sinistro del confronto
	      if(Hvar.ri_best_decrease_for_compvar[index]<0)
		{
		  MSG_ERROR("\nREACHABILITY ANALISYS ERROR\n");
		  exit(0);
		}
	    }
	  for(i=0;i<gef_conn[Hvar.ri_best_decrease_for_compvar[index]].num_numeric_effects;i++)
	    {
	      numeric_effect=&gef_conn[Hvar.ri_best_decrease_for_compvar[index]].numeric_effects[i];
	      if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],gcomp_var[index].first_op))
		{
		  k= (int) abs(ceil((Hvar.min_values[gcomp_var[index].first_op]+0.05-Hvar.max_values[gcomp_var[index].second_op]) /Hvar.max_values[gcomp_var_effects[numeric_effect->index].second_op]));   
		  if(k==0)
		    k++;  

		  cri_compute_action_cost (Hvar.ri_best_decrease_for_compvar[index],k );
		  //ri_sub_tested_vars_for_cvar (index,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
		  SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,index);
		  return;

		}
	      
	    }
	  
	  
	}
      break;
      

    case LESS_THAN_OR_EQUAL_OP:

      
      if(Hvar.ri_best_assign_for_compvar[index]>=0)
	    {
	      for(i=0;i<gef_conn[Hvar.ri_best_assign_for_compvar[index]].num_numeric_effects;i++)
		{
		  numeric_effect=&gef_conn[Hvar.ri_best_assign_for_compvar[index]].numeric_effects[i];
		  if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],gcomp_var[index].first_op))
		    {
		      if(Hvar.min_values[gcomp_var_effects[numeric_effect->index].second_op]<=Hvar.max_values[gcomp_var[index].second_op])
			{

			   cri_compute_action_cost(Hvar.ri_best_assign_for_compvar[index],1 );
			  //  ri_sub_tested_vars_for_cvar (index,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
			  SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,index);
			  return;
			}

		    }
		  
		}
	    }
      
      
      else
	{
	  if(Hvar.ri_best_decrease_for_compvar[index]<0)
	    { 

	      if (Hvar.ri_best_decrease_for_compvar[gcomp_var[index].first_op] > Hvar.ri_best_increase_for_compvar[gcomp_var[index].second_op])
		Hvar.ri_best_decrease_for_compvar[index] = Hvar.ri_best_decrease_for_compvar[gcomp_var[index].first_op];
	      else
		Hvar.ri_best_decrease_for_compvar[index] = Hvar.ri_best_increase_for_compvar[gcomp_var[index].second_op];
	      // Utilizzare il best descrease del membro sinistro del confronto

	      if(Hvar.ri_best_decrease_for_compvar[index]<0)
		{
		  MSG_ERROR("\nREACHABILITY ANALISYS ERROR\n");
		  exit(0);
		}
	    }
	  for(i=0;i<gef_conn[Hvar.ri_best_decrease_for_compvar[index]].num_numeric_effects;i++)
	    {
	      numeric_effect=&gef_conn[Hvar.ri_best_decrease_for_compvar[index]].numeric_effects[i];
	      if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],gcomp_var[index].first_op))
		{
		  k= (int) abs(ceil((Hvar.min_values[gcomp_var[index].first_op]-Hvar.max_values[gcomp_var[index].second_op]) /Hvar.max_values[gcomp_var_effects[numeric_effect->index].second_op])); 
		  if(k==0)		    
		    k++;  
		   

		  cri_compute_action_cost (Hvar.ri_best_decrease_for_compvar[index],k );
		  //ri_sub_tested_vars_for_cvar (index,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
		  SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,index);
		}
	      
	    }
	  
	  
	}
     
      break;
      
      
    case GREATER_THAN_OP:
      if(Hvar.ri_best_assign_for_compvar[index]>=0)
	{
	  for(i=0;i<gef_conn[Hvar.ri_best_assign_for_compvar[index]].num_numeric_effects;i++)
	    {
	      numeric_effect=&gef_conn[Hvar.ri_best_assign_for_compvar[index]].numeric_effects[i];
	      if(numeric_effect->lval==gcomp_var[index].first_op)
		{
		  if(Hvar.max_values[gcomp_var_effects[numeric_effect->index].second_op] > Hvar.min_values[gcomp_var[index].second_op])
		    {

		       cri_compute_action_cost(Hvar.ri_best_assign_for_compvar[index],1 );
		      //  ri_sub_tested_vars_for_cvar (index,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
		      SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,index);
		      return;
		    }
		  
		}
	      
	    }
	}

      
      else
	{
	  if(Hvar.ri_best_increase_for_compvar[index]<0)
	    {   

	      if (Hvar.ri_best_increase_for_compvar[gcomp_var[index].first_op] > Hvar.ri_best_decrease_for_compvar[gcomp_var[index].second_op])
		Hvar.ri_best_increase_for_compvar[index] = Hvar.ri_best_increase_for_compvar[gcomp_var[index].first_op];
	      else
		Hvar.ri_best_increase_for_compvar[index] = Hvar.ri_best_decrease_for_compvar[gcomp_var[index].second_op];
	      // Utilizzare il best increase del membro sinistro del confronto

	      if(Hvar.ri_best_increase_for_compvar[index]<0)
		{
		  MSG_ERROR("\nREACHABILITY ANALISYS ERROR\n");
		  exit(0);
		}
	    }
	  for(i=0;i<gef_conn[Hvar.ri_best_increase_for_compvar[index]].num_numeric_effects;i++)
	    {
	      numeric_effect=&gef_conn[Hvar.ri_best_increase_for_compvar[index]].numeric_effects[i];
	      if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],gcomp_var[index].first_op))
		{
		  k= (int) abs(ceil((Hvar.max_values[gcomp_var[index].first_op]+0.05-Hvar.min_values[gcomp_var[index].second_op]) /Hvar.max_values[gcomp_var_effects[numeric_effect->index].second_op]));
		  if(k==0)		    
		    k++;


		  cri_compute_action_cost (Hvar.ri_best_increase_for_compvar[index],k );
		  // ri_sub_tested_vars_for_cvar (index,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
		  SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,index);
		}
	      
	    }
	  
	  
	}
      
      break;

    case GREATER_OR_EQUAL_OP:
      if(Hvar.ri_best_assign_for_compvar[index]>=0)
	{
	  for(i=0;i<gef_conn[Hvar.ri_best_assign_for_compvar[index]].num_numeric_effects;i++)
	    {
	      numeric_effect=&gef_conn[Hvar.ri_best_assign_for_compvar[index]].numeric_effects[i];
	      if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],gcomp_var[index].first_op))
		{
		  if(Hvar.max_values[gcomp_var_effects[numeric_effect->index].second_op] >= Hvar.min_values[gcomp_var[index].second_op])
		    {

		      cri_compute_action_cost(Hvar.ri_best_assign_for_compvar[index],1 );
		      //  ri_sub_tested_vars_for_cvar (index,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
		      SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,index);
		      return;
		    }
		  
		}
	      
	    }
	}
      
      
      else
	{
	  if(Hvar.ri_best_increase_for_compvar[index]<0)
	    {  
	      if (Hvar.ri_best_increase_for_compvar[gcomp_var[index].first_op] > Hvar.ri_best_decrease_for_compvar[gcomp_var[index].second_op])
		Hvar.ri_best_increase_for_compvar[index] = Hvar.ri_best_increase_for_compvar[gcomp_var[index].first_op];
	      else
		Hvar.ri_best_increase_for_compvar[index] = Hvar.ri_best_decrease_for_compvar[gcomp_var[index].second_op];
	      // Utilizzare il best increase del membro sinistro del confronto
	      
	      if(Hvar.ri_best_increase_for_compvar[index]<0)
		{
		  MSG_ERROR("\nREACHABILITY ANALISYS ERROR\n");
		  exit(0);
		}
	      
	    }
	  for(i=0;i<gef_conn[Hvar.ri_best_increase_for_compvar[index]].num_numeric_effects;i++)
	    {
	      numeric_effect=&gef_conn[Hvar.ri_best_increase_for_compvar[index]].numeric_effects[i];
	      if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],gcomp_var[index].first_op))
		{
		  k= (int) abs(ceil((Hvar.max_values[gcomp_var[index].first_op]-Hvar.min_values[gcomp_var[index].second_op]) /Hvar.max_values[gcomp_var_effects[numeric_effect->index].second_op]));
		  if(k==0)
		    k++;
		    

		  cri_compute_action_cost(Hvar.ri_best_increase_for_compvar[index],k );
		  // ri_sub_tested_vars_for_cvar (index,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
		  SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,index);
		}
	      
	    }
	      
	  
	}
      
      break;
      
      
    default:
      MSG_ERROR("\nREACHABILITY ANALISYS ERROR -- PRECONDITION TYPE NOT HANDLED YET\n");
      exit(0);
      break;
	  
    }
  

}







/**
 * Nome: cri_compute_fact_cost
 * Scopo: Inserisce nell'insieme ACTS la migliore
 *        azione che supporta il fatto in posizione "index" e 
 *        inserisce nell'insieme G le sue precondizioni 
 * Funzioni chiamate: cri_compute_action_cost
 *                   
 * Chiamata da: cri_predict_cost_relaxed
 *
 * Name: cri_compute_fact_cost
 * Purpose: Insert the best action that can support the fact
 *          "index" in the set ACTS and insert its preconditions
 *          in the set G of the facts that must be supported
 * Functions used: cri_compute_action_cost
 *                
 * Called by: cri_predict_cost_relaxed 
 **/

void
cri_compute_fact_cost (int index)
{
  int best_action;
  
  /**
     if the fact is in add effects of some actions
  **/
  if(index>=0)
    {

      if(gft_conn[index].fact_type==IS_TIMED)
	return;


      if(!GET_BIT(Hvar.ri_supp_bit_vect_facts,index))
	{
	  best_action=cri_get_best_action_for_fct(index);

	  if (best_action!=INITIAL_ACTION && best_action>=0 )
	    {

	      cri_compute_action_cost (best_action,1 );

	    }
	  else
	    {
	      
	      if( best_action!=INITIAL_ACTION && DEBUG3)
		printf("\n Warning: Unsupported fact in the relaxed plan of the reachability information");
	    }
	}
    }
  else
    {

      if(!GET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,-index))
	{
	  if(ri_eval_comp_var (&(gcomp_var[-index]), -index ,Hvar.max_values,Hvar.min_values,TRUE) >0.5)
	    {
	      SET_BIT(Hvar.ri_bit_vect_supp_numeric_facts,-index);
	      // ri_sub_tested_vars_for_cvar (-index,Hvar.num_tested_positive,Hvar.num_tested_negative,Hvar.relevant_vars,TRUE);
	    }
	  else
	    cri_insert_best_for_comp_var (-index);
	}
    }



}



void cri_set_action_cost(int action_number, float cost,int num_actions)
{

  Hvar.ri_cost_of_actions[action_number]=cost;
  Hvar.ri_num_actions_of_actions[action_number]=num_actions;

}

float cri_get_action_cost(int action_number)
{

  return Hvar.ri_cost_of_actions[action_number];

}



/**
 * Nome: cri_predict_cost_relaxed
 * Scopo: calcola il costo dell'azione in esame attraverso un piano rilassato
 * Funzioni chiamate: reset_cri_list (for reset) 
 *                    cri_compute_fact_cost
 *                    cri_compute_action_cost
 * Chiamata da: cri_activate_distgraph_ef
 *              cri_heuristic_for_action
 *
 * Name: cri_predict_cost_relaxed
 * Purpose: compute the cost of the actual action with a relaxed plan where
 *          we insert the action not already applyed by other priors facts
 * Functions used: reset_cri_list (for reset) 
 *                 cri_compute_fact_cost
 *                 cri_compute_action_cost
 * Called by: cri_activate_distgraph_ef
 *            cri_heuristic_for_action
 **/

float cri_predict_cost_relaxed (int action, float *duration_act, int *num_actions)
{
  int i, indx;
  float cost = 0.0, duration = 0.0;

#ifdef __TEST__1
  printf ("\n---------------------------------------");
  printf ("\n Compute action cost : %d ", action);
  print_op_name (gef_conn[action].op);
  printf ("\n");
#endif
  /**
     Resetta le informazioni di raggiungibilita'
     *
     Reset the structure containing reachability informations
  **/
  reset_cri_list();

  /** 
      Inserisce le precondizioni dell'azione nell'insieme dei fatti G
      da supportare e di cui è necessario calcolare il costo di raggiungibilità
      *
      Insert the preconditions of the action in the set G of the facts
      that must be supported 
  **/ 
  indx = 0;

  // AT START Preconditions
  for (i = 0; i < gef_conn[action].num_PC; i++)
    cri_compute_fact_cost (gef_conn[action].PC[i]);

  if (gef_conn[action].sf != NULL)
    {

      // OVERALL Preconditions
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	if (!is_fact_in_additive_effects_start(action, gef_conn[action].sf->PC_overall[i]))
	   cri_compute_fact_cost(gef_conn[action].sf->PC_overall[i]);

      // AT END Preconditions
      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	if (!is_fact_in_additive_effects_start (action, gef_conn[action].sf->PC_end[i]))
	   cri_compute_fact_cost(gef_conn[action].sf->PC_end[i]);
    }





  /**
     Aggiunge l'azione alla lista delle azioni 
     supportate e rende supportati i suoi effetti
     *
     Insert the action in the set ACTS of the actions
     inserted in relaxed plan e support its effects
  **/

  *num_actions = Hvar.ri_num_actions_define_cost +1 ;

  cost = Hvar.ri_cost_actions_define_cost+ get_action_cost(action, -1, NULL);

 

#ifdef __TEST__
  printf ("\n RELAXED COST : %.3f \n", cost);
#endif


  duration = 0.0;
  // Future work: improve temporal action overlapping
  *duration_act = duration;



     
     return (cost);
}


/**
 * Name: cri_predict_cost_sum
 * Purpose: compute the cost of the actual action just like 
 *          a sum of the cost of Preconditions 
 * Functions used: cri_get_best_action_for_fct
 * Called by: cri_activate_distgraph_ef
 *            get_action_cost
 **/

float cri_predict_cost_sum (int action, int *num_actions)
{
  int idx, i;
  float cost, temp;
  int best_act, num_act;
  cost = 0.0;
  num_act=0;

  // Preconditions AT_START
  for (i = 0; i < gef_conn[action].num_PC; i++) { 
    /**
       idx indica la precondizione che stiamo considerando 
       *
       idx represents the precondition that we are considering
    **/
    idx = gef_conn[action].PC[i];
    
    /** 
	Do not consider numeric facts 
    **/
    if (idx < 0)
      {
	if(GpG.cri_initial_or_update==0)
	  { /* Initial CRI */
	    cost += Hvar.ri_cost_of_numeric_facts[-idx];
	    num_act += Hvar.ri_num_actions_of_numeric_facts[-idx];
	  }
	else
	  num_act += num_action_for_unsup_num_precondition(-idx, GpG.cri_update_level+1);

        continue;
      }
    
    /**
       best_act è la migliore azione che supporta il fatto idx 
       *
       best_act is the best action that support the fact idx
    **/
    best_act =  cri_get_best_action_for_fct(idx);
    if ( best_act >= 0)
      {
	/** 
	    aggiunge al costo dell'azione best_act finora 
	    computato il costo del fatto idx ed aggiunge al 
	    numero di azioni quelle necessarie per supportare idx
	    *
	    add the cost of idx and 
	    add the number of actions required to support the fact idx
	**/
	cost += Hvar.ri_cost_of_facts[idx];
	num_act += Hvar.ri_num_actions_of_facts[idx];
	
#ifdef __TEST__
	printf ("\n act-sum ");
	if (best_act >= 0)
	  print_op_name (best_act);
	else
	  printf ("\n INIT-ACT ");
	printf (" cost %f duration %f \n", cost,
		Hvar.ri_duration_of_facts[idx]);
#endif

      }
  } // end for preconditions at start

  if (gef_conn[action].sf != NULL)
    {
      // Preconditions OVERALL
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{
	  /**
	     idx indica la precondizione che stiamo considerando 
	     *
	     idx represents the precondition that we are considering
	  **/
	  idx = gef_conn[action].sf->PC_overall[i];

	  /** 
	      Do not consider numeric facts 
	  **/
	  if (idx < 0)
	    {

	      if(GpG.cri_initial_or_update==0)
		{ /* Initial CRI */
		  cost += Hvar.ri_cost_of_numeric_facts[-idx];
		  num_act += Hvar.ri_num_actions_of_numeric_facts[-idx];
	       }
	      else
		num_act += num_action_for_unsup_num_precondition(-idx, GpG.cri_update_level+1);
	      continue;
	    }

          /**
	     Se il fatto appartiene agli effetti at_start è 
	     già supportato dall'azione stessa, quindi
	     non viene preso in considerazione
	     *
	     if the fact is an at_start effect of the action, then
	     do not consider it
	  **/ 
	  if (is_fact_in_additive_effects_start
	      (action, gef_conn[action].sf->PC_overall[i]))
	    continue;

    
	  /**
	     best_act è la migliore azione che supporta il fatto idx 
	     *
	     best_act is the best action that support the fact idx
	  **/
	  best_act = cri_get_best_action_for_fct (idx);
	  if ( best_act>=0)	 
	    {
	      /**
		 aggiunge al costo dell'azione best_act finora 
		 computato il costo del fatto idx ed aggiunge al 
		 numero di azioni quelle necessarie per supportare idx
		 *
		 add the cost of idx and 
		 add the number of actions required to support the fact idx
	      **/
	      cost +=   Hvar.ri_cost_of_facts[idx];
	      num_act +=   Hvar.ri_num_actions_of_facts[idx];
	      
#ifdef __TEST__
	      printf ("\n act-sum ");
	      if (best_act >= 0)
		print_op_name (best_act);
	      else
		printf ("\n INIT-ACT ");
	      printf (" cost %f duration %f \n", cost,
		      Hvar.ri_duration_of_facts[idx]);
#endif

	    }

	} // end for preconditions overall


      // Preconditions AT_END
      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++) 
	{ 
	  /**
	     idx indica la precondizione che stiamo considerando 
	     *
	     idx represents the precondition that we are considering
	  **/
	  
	  idx = gef_conn[action].sf->PC_end[i];

	  /** 
	      Do not consider numeric facts 
	  **/
	  if (idx < 0)
	    {
	      if(GpG.cri_initial_or_update==0)
		{ /* Initial CRI */
		  cost += Hvar.ri_cost_of_numeric_facts[-idx];
		  num_act += Hvar.ri_num_actions_of_numeric_facts[-idx];
		}
	      else
		num_act += num_action_for_unsup_num_precondition(-idx, GpG.cri_update_level+1);

	      continue;
	    }
	  
          /**
	     Se il fatto appartiene agli effetti at_start è 
	     già supportato dall'azione stessa, quindi
	     non viene preso in considerazione
	     *
	     if the fact is an at_start effect of the same action, then
	     do not consider it
	  **/ 
	  if (is_fact_in_additive_effects_start (action,gef_conn[action].sf->PC_end[i]))
	    continue;

	  /**
	     best_act è la migliore azione che supporta il fatto idx 
	     *
	     best_act is the best action that support the fact idx
	  **/
	  best_act = cri_get_best_action_for_fct (idx);
	  if ( best_act>=0)
	    {
	      /**
		 aggiunge al costo dell'azione best_act finora 
		 computato il costo del fatto idx ed aggiunge al 
		 numero di azioni quelle necessarie per supportare idx
		 *
		 add the cost of idx and 
		 add the number of actions required to support the fact idx
	      **/
	      cost +=   Hvar.ri_cost_of_facts[idx];
	      num_act +=   Hvar.ri_num_actions_of_facts[idx];

#ifdef __TEST__
	      printf ("\n act-sum ");
	      if (best_act >= 0)
		print_op_name (best_act);
	      else
		printf ("\n INIT-ACT ");
	      printf (" cost %f duration %f \n", cost,
		      Hvar.ri_duration_of_facts[idx]);
#endif


	    }

	}
    }
  /**
     Aggiunge al costo dell'azione il costo finora computato 
     equivalente alla somma dei costi delle precondizioni
     *
     Add the cost of the action to the cost of its
     preconditions previously computed
  **/
  temp = get_action_cost (action, -1, NULL);
  cost = cost + temp;
  num_act++; //"action" itself

  *num_actions=num_act;

#ifdef __TEST__
  printf ("ACT COST SUM PRECOND \n ");
  printf ("\n COSTOSUM : %f", cost);
#endif

  return (cost);
}




/**
 * Name: cri_predict_cost_max
 * Scope: compute the cost of the actual action just like as max 
 *        of the cost of Preconditions 
 *
 * Functions used: cri_get_best_action_for_fct
 *                    get_action_cost
 *
 * Called by:: cri_activate_distgraph_ef 
 **/

float cri_predict_cost_max (int action, int *num_actions)
{
  int idx, i;
  float cost, temp;
  int best_act, num_act, num;


  cost = 0.0;
  num_act=0;


  /**
     Preconditions AT_START
  **/
  for(i = 0; i < gef_conn[action].num_PC; i++)
    {
      /**
	 idx indica la precondizione che stiamo considerando 
	 *
	 idx represents the precondition that we are considering
      **/
      idx = gef_conn[action].PC[i];

      /** 
	  Do not consider numeric facts 
      **/
      if (idx < 0)
	{
	
	if(GpG.cri_initial_or_update==0)
	  { /* Initial CRI */
	    if (Hvar.ri_num_actions_of_numeric_facts[-idx] > num_act) 
	    {
	      if(Hvar.ri_best_assign_for_compvar[-idx]<0
		 &&Hvar.ri_best_increase_for_compvar[-idx]<0
		 &&Hvar.ri_best_decrease_for_compvar[-idx]<0)
		{
		  MSG_ERROR("\nERROR REACHABILITY INFORMATION");
		  printf("\nNO BEST INCREASE FOR COMPVAR %d",-idx);
		  //  exit(0); 
		}
	      else
		{
		  cost =   Hvar.ri_cost_of_numeric_facts[-idx];
		  num_act =   Hvar.ri_num_actions_of_numeric_facts[-idx];
		}     
	    }
	  }
	else
	  {  
	    num = num_action_for_unsup_num_precondition(-idx, GpG.cri_update_level+1);
	    if(num>num_act)
	      num_act=num;

	  }
	  continue;
	}
      
      /**
	 best_act è la migliore azione che supporta il fatto idx 
	 *
	 best_act is the best action that support the fact idx
      **/
      if(GET_BIT(Hvar.ri_supp_bit_vect_facts,idx))
	continue;

      best_act = cri_get_best_action_for_fct (idx);

      /**
	 Se l'azione è applicabile ed il numero di azioni 
	 necessarie a supportare il fatto idx supera il massimo 
	 finora incontrato (num_act) setta il costo uguale al costo
	 del fatto idx
	 *
	 if the action is applicable and the number of actions
	 required to support the fact idx exceeded the maximum 
	 computed until now (num_act), then we set the cost equal
	 than the cost of the fact idx
      **/
      if ( best_act >= 0   &&  Hvar.ri_num_actions_of_facts[idx] > num_act) 
	{

	  cost =   Hvar.ri_cost_of_facts[idx];
	  num_act =   Hvar.ri_num_actions_of_facts[idx];
    
#ifdef __TEST__
	  printf ("\n act-max ");
	  print_op_name (best_act);
	  printf (" cost %f  \n", cost );
#endif


	}
    }

  /** 
      Preconditions OVERALL
   **/
  if (gef_conn[action].sf != NULL)
    {
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{
	  /**
	     idx indica la precondizione che stiamo considerando 
	     *
	     idx represents the precondition that we are considering
 	  **/
	  idx = gef_conn[action].sf->PC_overall[i];

	  /** 
	      Do not consider numeric preconditions
	  **/
	  if (idx < 0)
	    {

	      if(GpG.cri_initial_or_update==0)
		{ /* Initial CRI */
		  if(Hvar.ri_best_assign_for_compvar[-idx]<0
		     &&Hvar.ri_best_increase_for_compvar[-idx]<0
		     &&Hvar.ri_best_decrease_for_compvar[-idx]<0)
		    {
		      MSG_ERROR("\nERROR REACHABILITY INFORMATION");
		      printf("\nNO BEST INCREASE FOR COMPVAR %d",-idx);
		      // exit(0); 
		    }
		  else
		    if ( Hvar.ri_num_actions_of_numeric_facts[-idx] > num_act) 
		      {
			cost =   Hvar.ri_cost_of_numeric_facts[-idx];
			num_act =   Hvar.ri_num_actions_of_numeric_facts[-idx];
		  
		      }
		  
		}
	      else
		{  
		  num = num_action_for_unsup_num_precondition(-idx, GpG.cri_update_level+1);
		  if(num>num_act)
		    num_act=num;
		  
	  }
		
	      continue;
	    }
	  
	  /** 
	     Se il fatto appartiene agli effetti at_start è 
	     già supportato dall'azione stessa, quindi
	     non viene preso in considerazione
	     *
	     if the fact is an at_start effect of the action, then
	     do not consider it
	  **/ 
	  if(GET_BIT(Hvar.ri_supp_bit_vect_facts,idx))
	    continue;
	  if (is_fact_in_additive_effects_start
	      (action, gef_conn[action].sf->PC_overall[i]))
	    continue;

	  /**
	     best_act è la migliore azione che supporta il fatto idx 
	     *
	     best_act is the best action that support the fact idx
	  **/
	  best_act =  cri_get_best_action_for_fct(idx);

	  /**
	     Se l'azione è accettabile ed il numero di azioni 
	     necessarie a supportare il fatto idx supera il massimo 
	     finora incontrato (num_act) setta il costo uguale al costo
	     del fatto idx
	     *
	     if the action is acceptable and the number of actions
	     required to support the fact idx exceed the maximum 
	     computed until now (num_act), then set the cost equal
	     than the cost of the fact idx
	  **/
	  if ( best_act>=0   &&  Hvar.ri_num_actions_of_facts[idx] > num_act)
	    {
	      cost =   Hvar.ri_cost_of_facts[idx];
	      num_act =   Hvar.ri_num_actions_of_facts[idx];
    
#ifdef __TEST__
	  printf ("\n act-max ");
	  print_op_name (best_act);
	  printf (" cost %f  \n", cost );
#endif
	    }
	}

      /** 
	  Preconditions AT_END
       **/
      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	{
	  /**
	     idx indica la precondizione che stiamo considerando 
	     *
	     idx represents the precondition that we are considering
 	  **/
	  idx = gef_conn[action].sf->PC_end[i];

	  /** 
	      Do not consider numeric preconditions
	  **/
	  if (idx < 0)
	    {
	      if(GpG.cri_initial_or_update==0)
		{ /* Initial CRI */

		  if(Hvar.ri_best_assign_for_compvar[-idx]<0
		     &&Hvar.ri_best_increase_for_compvar[-idx]<0
		     &&Hvar.ri_best_decrease_for_compvar[-idx]<0)
		    {
		      MSG_ERROR("\nERROR REACHABILITY INFORMATION");
		      printf("NO BEST INCREASE FOR COMPVAR %d",-idx);
		  //  exit(0); 
		    }
		  else
		    if ( Hvar.ri_num_actions_of_numeric_facts[-idx] > num_act) 
		      {
			cost =   Hvar.ri_cost_of_numeric_facts[-idx];
			num_act =   Hvar.ri_num_actions_of_numeric_facts[-idx];		  
		      }
		}
	      else
		{  
		  num = num_action_for_unsup_num_precondition(-idx, GpG.cri_update_level+1);
		  if(num>num_act)
		    num_act=num;
		  
		}

	      continue;
	    }

	  /** 
	     Se il fatto appartiene agli effetti at_start è 
	     già supportato dall'azione stessa, quindi
	     non viene preso in considerazione
	     *
	     if the fact is an at_start effect of the action, then we
	     do not consider it
	  **/ 
	  if(GET_BIT(Hvar.ri_supp_bit_vect_facts,idx))
	    continue;
	  if (is_fact_in_additive_effects_start (action,gef_conn[action].sf->PC_end[i]))
	    continue;

	  /**
	     best_act è la migliore azione che supporta il fatto idx 
	     *
	     best_act is the best action that support the fact idx
	  **/
	  best_act = cri_get_best_action_for_fct (idx);

	  /**
	     Se l'azione è accettabile ed il numero di azioni 
	     necessarie a supportare il fatto idx supera il massimo 
	     finora incontrato (num_act) setta il costo uguale al costo
	     del fatto idx
	     *
	     if the action is acceptable and the number of actions
	     required to support the fact idx exceed the maximum value 
	     computed until now (num_act), then set the cost equal
	     than the cost of the fact idx
	  **/
	  if ( best_act>=0   &&  Hvar.ri_num_actions_of_facts[idx] > num_act)
	    {
	      cost =   Hvar.ri_cost_of_facts[idx];
	      num_act =   Hvar.ri_num_actions_of_facts[idx];
    
#ifdef __TEST__
	  printf ("\n act-max ");
	  print_op_name (best_act);
	  printf (" cost %f  \n", cost );
#endif

	    }
	}

    }
  /**
     Aggiunge al costo dell'azione il costo finora computato 
     equivalente al costo della precondizione che e' supportata
     dal massimo numero di azioni
     *
     Add the cost of the action to the cost of its
     preconditions  previously computed (MAX prec(a))
  **/
  temp = get_action_cost (action, -1, NULL);
  cost += temp;
 num_act++; //"action" itself

  *num_actions=num_act;


#ifdef __TEST__1
  printf ("\n  ");
  print_op_name (action);
  printf (" : ACT POS %d   MAX PRECOND COST  ", action);
  printf (" MAX COST: %f \n", cost);
#endif

  return (cost);
}










/**
 * Nome: cri_predict_duration
 * Scopo: Restituisce l'istante di tempo minimo a cui l'azione di indice 
 * action puo' essere applicabile, facendo il massimo tra gli istanti 
 * in cui le sue precondizioni possono essere supportate
 * Funzioni chiamate: cri_get_best_action_for_fct 
 * Chiamata da: cri_activate_distgraph_ef 
 *
 * Name: cri_predict_duration
 * Purpose: Return the minimum istant in which the action
 * of index "action" can be applied
 * Functions used:  cri_get_best_action_for_fct
 * Called by: cri_activate_distgraph_ef 
 **/
float cri_predict_duration (int action, float *duration_act)
{
  int idx,num;
  int i;
  float maxdur=0.0;
  int best_act;
  float  time_Timed_Prec=0.0;

  /** 
      Preconditions AT_START
   **/
  for (i = 0; i < gef_conn[action].num_PC; i++)
    { 
      /**
	 idx indica la precondizione che stiamo considerando 
	 *
	 idx represents the precondition that we are considering
      **/
      idx = gef_conn[action].PC[i];

      /** 
	  Do not consider numeric preconditions
      **/
      if (idx < 0)
	{
	  //#ifdef __TEST_REACH__
	  if ( Hvar.ri_duration_of_numeric_facts[-idx] > maxdur)
	    maxdur =Hvar.ri_duration_of_numeric_facts[-idx];
	  //#endif
	  continue;
	}

     
      /**
	 best_act è la migliore azione che supporta il fatto idx 
	 *
	 best_act is the best action that support the fact idx
      **/
     best_act = cri_get_best_action_for_fct (idx);
      if ( best_act>=0)
	{ 
	  /**
	     Se l'istante a cui può essere supportato il fatto idx, 
	     e' maggiore del massimo finora computato, setta l'istante
	     di idx come il nuovo massimo
	     *
	     If the tempotal istant in which can be supported the
	     fact idx is greater than the maximum computed until now,
	     then set the idx istant as new maximum
	  **/
	  if ( Hvar.ri_duration_of_facts[idx] > maxdur)
	    {
	      maxdur =Hvar.ri_duration_of_facts[idx];

#ifdef __TEST__
	      printf ("\n acttime ");
	      print_op_name (best_act);
	      printf (" cost %f duration %f \n",Hvar.ri_cost_of_facts[idx], Hvar.ri_duration_of_facts[idx] );
#endif

	    }
	}
    } // end for of the preconditions at_start

  if (gef_conn[action].sf != NULL)
    {
      /** 
	  Preconditions OVERALL
       **/
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{
	  /**
	     idx indica la precondizione che stiamo considerando 
	     *
	     idx represents the precondition that we are considering
	  **/
 	  idx = gef_conn[action].sf->PC_overall[i];

	  /** 
	      Do not consider numeric preconditions
	  **/
	  if (idx < 0)
	    {
	      //#ifdef __TEST_REACH__
	      if ( Hvar.ri_duration_of_numeric_facts[-idx] > maxdur)
		maxdur =Hvar.ri_duration_of_numeric_facts[-idx];
	      //#endif
	      continue;
	    }


	  /** 
	     Se il fatto appartiene agli effetti at_start è 
	     già supportato dall'azione stessa, quindi
	     non viene preso in considerazione
	     *
	     if the fact is an at_start effect of the action, then
	     we do not consider it
	  **/ 
	  if (is_fact_in_additive_effects_start(action, idx))
	    continue;

	  /**
	     best_act è la migliore azione che supporta il fatto idx 
	     *
	     best_act is the best action that support the fact idx
	  **/
	  best_act =cri_get_best_action_for_fct(idx);
	  if ( best_act>=0)	 
	    {
	      /**
		 Se l'istante a cui può essere supportato il fatto "idx", 
		 e' maggiore del massimo finora computato, setta l'istante
		 di idx come il nuovo massimo
		 *
		 If the temporal istant in which can be supported the
		 fact "idx" is greater than the maximum computed until now,
		 then set the idx istant as new maximum
	      **/
	      if (Hvar.ri_duration_of_facts[idx] > maxdur)
		{
		  maxdur = Hvar.ri_duration_of_facts[idx]; 

#ifdef __TEST__
	      printf ("\n acttime ");
	      print_op_name (best_act);
	      printf (" cost %f duration %f \n",Hvar.ri_cost_of_facts[idx], Hvar.ri_duration_of_facts[idx] );
#endif

		}

	    }
	} // end for of the preconditions overall

      /** 
	  Preconditions AT-END
       **/
      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	{
	  /**
	     idx indica la precondizione che stiamo considerando 
	     *
	     idx represents the precondition that we are considering
	  **/
	  idx = gef_conn[action].sf->PC_end[i];

	  /** 
	      Do not consider numeric preconditions
	  **/
	  if (idx < 0)
	    {
	      //#ifdef __TEST_REACH__
	      if ( Hvar.ri_duration_of_numeric_facts[-idx] > maxdur)
		maxdur =Hvar.ri_duration_of_numeric_facts[-idx];
	      //#endif
	      continue;
	    }


	  /** 
	     Se il fatto appartiene agli effetti at_start è 
	     già supportato dall'azione stessa, quindi
	     non viene preso in considerazione
	     *
	     if the fact is an at_start effect of the action, then
	     do not consider it
	  **/ 
	  if (is_fact_in_additive_effects_start(action, idx))
	    continue;

	  /**
	     best_act è la migliore azione che supporta il fatto idx 
	     *
	     best_act is the best action that support the fact idx
	  **/
	  best_act =cri_get_best_action_for_fct(idx);
	  if ( best_act>=0)
	    { 
	      /**
		 Se l'istante a cui può essere supportato il fatto idx
		 meno la durata dell'azione, e' maggiore del massimo 
		 finora calcolato, setta l'istante di idx come il nuovo massimo
		 *
		 If the tempotal istant in which can be supported the
		 fact idx less the duration of the action is greater 
		 than the maximum computed until now, then set the idx 
		 istant like new maximum
	      **/
	      if (Hvar.ri_duration_of_facts[idx] - get_action_time (action, 0) > maxdur)
		{
		  maxdur = Hvar.ri_duration_of_facts[idx] - get_action_time (action, 0);
#ifdef __TEST__
		  printf ("\n acttime ");
		  print_op_name (best_act);
		  printf (" cost %f duration %f \n",Hvar.ri_cost_of_facts[idx], Hvar.ri_duration_of_facts[idx] );

#endif
		}

	    }
	  else if(best_act == INFINITY)
	    { 
	      /**
		 The fact is unreachable
	      **/
	      int j;
	      printf("\n Az level %d con prec non supp: %d   ",gef_conn[action].level ,action );
	      print_op_name(action);
	      printf("\n Preconditions");
	      
	      for (j = 0; j < gef_conn[action].sf->num_PC_end; j++)
		{
		  printf("\n Fact %d :  ",gef_conn[action].sf->PC_end[j]);
		  print_ft_name(gef_conn[action].sf->PC_end[j]);
		}
	    }
	} // end for of the at end preconditions
    }  // end if sf
  
  

  /**
     Timed facts check
  **/
  if(gef_conn[action].timed_PC)
    {

      if (!GET_BIT(GpG.has_timed_preconds, action))
	printf("\nError, no timed facts for action %d",action);


      time_Timed_Prec = search_for_pc_intervals( maxdur, action, GpG.cri_update_level, &num);
      if (num > 0)
	return -1.0;
      else
	if(time_Timed_Prec>maxdur)
	  maxdur=time_Timed_Prec;

    }

#ifdef __TEST__
  printf ("\n  MAX PREC DURATION: %.3f \n", maxdur);
#endif

  *duration_act = maxdur;
  return (maxdur);
}










/**
 * Name: cri_insert_ftcost 
 * Purpose: Set Best_action and its costs for the fact "fact_pos"; used in CRI 
 * Il parametro utilizzato per valutare la migliore azione che supporta 
 * il fatto di indice fact_pos è il numero di azioni necessarie a 
 * supportarlo se num_actions è inferiore al migliore numero di azioni
 * salvato nella struttura  Hvar.ri_num_actions_of_facts i valori
 * di costo (Hvar.ri_cost_of_facts), durata (Hvar.ri_duration_of_facts),
 * migliore azione ( Hvar.ri_best_act_for_facts), costo totale 
 * ( Hvar.ri_tot_cost_of_facts), vengono aggiornati all'interno delle
 * strutture dedicate
 * Main functions used: None 
 * Called by: cri_activate_distgraph_ef
 */
void cri_insert_ftcost (int fact_pos, float cost, float duration, 
			int num_actions,int best_ef)
{
 
  float totcost=0.0;


  /**
     A seconda del parametro utilizzato nella funzione di costo per
     valutare la qualità, setto il costo del fatto
     *
     Regarding the parameter used in the evaluation function for the
     evaluation of the plan quality, set fact cost
  **/ 
      if (GpG.orig_weight_cost)
	totcost = (cost * GpG.orig_weight_cost);

      if (GpG.orig_weight_time)
	totcost += (duration * GpG.orig_weight_time);

      /**
	 Se ho individuato un fatto che non era ancora stato valutato o
	 un numero di azioni che lo supportano inferiore o un numero 
	 di azioni uguale ma un costo inferiore, aggiorno i parametri 
	 inserendo i nuovi valori computati
	 *
	 if the fact is not supported or the corresponding number
	 of actions that support it is less than the previous one
	 (or is equal but the corresponding cost is inferior), then
	 update the parameter of the fact
      **/

  if(Hvar.ri_best_act_for_facts[fact_pos]==INFINITY || 
     Hvar.ri_num_actions_of_facts[fact_pos] > num_actions ||
     (Hvar.ri_num_actions_of_facts[fact_pos]== num_actions  && 
      Hvar.ri_tot_cost_of_facts[fact_pos]> totcost) )
    {
      Hvar.ri_best_act_for_facts[fact_pos]= best_ef;
      Hvar.ri_num_actions_of_facts[fact_pos] = num_actions;

      Hvar.ri_cost_of_facts[fact_pos] = cost;
      Hvar.ri_duration_of_facts[fact_pos] = duration;
      Hvar.ri_tot_cost_of_facts[fact_pos] = totcost;
    }

  /**
     Se siamo alla prima esecuzione e individuo una durata minore,
     inserisco una nuova durata come durata minima
     *
     If this is the first execution and if the fact is supported
     in an inferior time then update the minimum time
  **/
  if (GpG.first_execution_cri==0)
    { 
      if(Hvar.dg_facts_min_duration[fact_pos] > duration)
	Hvar.dg_facts_min_duration[fact_pos] = duration;

      if(Hvar.num_tmd_facts_array!=0)
	{
	  if(gft_conn[fact_pos].tmd_facts_array!=NULL)
	    free(gft_conn[fact_pos].tmd_facts_array);

	  
	  gft_conn[fact_pos].tmd_facts_array=(int *) calloc(Hvar.num_tmd_facts_array, sizeof(int));

	  memcpy(gft_conn[fact_pos].tmd_facts_array, Hvar.tmd_facts_array, Hvar.num_tmd_facts_array*sizeof(int));
	  gft_conn[fact_pos].num_tmd_facts_array=Hvar.num_tmd_facts_array;
	}
      else
	{
	   if(gft_conn[fact_pos].tmd_facts_array!=NULL)
	     free(gft_conn[fact_pos].tmd_facts_array);
	   
	   gft_conn[fact_pos].tmd_facts_array=NULL;
	   
	   gft_conn[fact_pos].num_tmd_facts_array=0;


	}


    }
}



void cri_insert_numeric_ftcost (int fact_pos, int action, int num_eff, int OPERATOR)
{
 
  float totcost=0.0;
  int num_actions;
  float cost=0.0;
  float duration=0.0;
  int k=0;
  /**
     A seconda del parametro utilizzato nella funzione di costo per valutare
     la qualità, setto il costo del fatto
     *
     Regarding the parameter used in the evaluation function for the
     evaluation of the plan quality, set fact cost
  **/ 
     

      /**
	 Se ho individuato un fatto che non era ancora stato valutato o
	 un numero di azioni che lo supportano inferiore o un numero 
	 di azioni uguale ma un costo inferiore, aggiorno i parametri 
	 inserendo i nuovi valori computati
	 *
	 if the fact is not supported or the corresponding number
	 of actions that support it is less than the previous one
	 (or is equal but the corresponding cost is inferior), then
	 update the parameter of the fact
      **/
  if(OPERATOR==INCREASE_OP)
    k=(int) ceil((Hvar.min_values[gcomp_var[fact_pos].second_op] - Hvar.max_values[gcomp_var[fact_pos].first_op])/Hvar.max_values[gcomp_var_effects[num_eff].second_op]);
  if(OPERATOR==DECREASE_OP)
    k=(int) ceil( (Hvar.min_values[gcomp_var[fact_pos].first_op]-Hvar.max_values[gcomp_var[fact_pos].second_op])/Hvar.max_values[gcomp_var_effects[num_eff].second_op]);
  
  if(k<=0)
    k=1;

  num_actions= Hvar.ri_num_actions_of_actions[action]+k;
  cost= Hvar.ri_cost_of_actions[action]+ k * get_action_cost(action, -1, NULL);
  duration=  k * get_action_time(action,0);

  if (GpG.orig_weight_cost)
    totcost = (cost * GpG.orig_weight_cost);
  
  if (GpG.orig_weight_time)
    totcost += (duration * GpG.orig_weight_time);
  
  if(OPERATOR==INCREASE_OP)
    if(Hvar.ri_best_increase_for_compvar[fact_pos]<0 || 
       Hvar.ri_num_actions_of_numeric_facts[fact_pos] > num_actions ||
       (Hvar.ri_num_actions_of_numeric_facts[fact_pos]== num_actions  && 
	Hvar.ri_tot_cost_of_numeric_facts[fact_pos]> totcost) )
      {
	Hvar.ri_best_increase_for_compvar[fact_pos]= action;
	Hvar.ri_num_actions_of_numeric_facts[fact_pos] = num_actions;
	Hvar.ri_cost_of_numeric_facts[fact_pos] = cost;
	Hvar.ri_duration_of_numeric_facts[fact_pos] = duration;
	Hvar.ri_tot_cost_of_numeric_facts[fact_pos] = totcost;
      }

  if(OPERATOR==DECREASE_OP)
    if(Hvar.ri_best_decrease_for_compvar[fact_pos]<0 || 
       Hvar.ri_num_actions_of_numeric_facts[fact_pos] > num_actions ||
       (Hvar.ri_num_actions_of_numeric_facts[fact_pos]== num_actions  && 
	Hvar.ri_tot_cost_of_numeric_facts[fact_pos]> totcost) )
      {
	Hvar.ri_best_decrease_for_compvar[fact_pos]= action;
	Hvar.ri_num_actions_of_numeric_facts[fact_pos] = num_actions;
	Hvar.ri_cost_of_numeric_facts[fact_pos] = cost;
	Hvar.ri_duration_of_numeric_facts[fact_pos] = duration;
	Hvar.ri_tot_cost_of_numeric_facts[fact_pos] = totcost;
      }
  
  
}










/**
 * Nome: cri_activate_distgraph_ef
 * Scopo: Vengono calcolati i costi di raggiungibilità dell'azione
 * di indice index, restituisce l'istante finale in cui termina l'azione
 * o un numero negativo se ci sono limitazioni con i timed facts
 * Funzioni chiamate: cri_predict_duration
 *                     cri_predict_cost_sum
 *                     cri_predict_cost_max
 *                     cri_predict_cost_relaxed
 *                     cri_insert_ftcost
 * Chiamata da: calc_mutex 
 *
 * Name: cri_activate_distgraph_ef
 * Purpose: Compute reachability information for the action  index,
 *   returns the end time of index or a negative value if the action
 *   cannot be applied
 * Functions used: cri_predict_duration
 *                 cri_predict_cost_sum
 *                 cri_predict_cost_max
 *                 cri_predict_cost_relaxed
 *                 cri_insert_ftcost
 * Called by: calc_mutex
 **/

float cri_activate_distgraph_ef (int index, int *fact_vect, int *derived_precs, int level, Bool *changed)
{

  int i, num_actions = 0;
  float cost=0.0, duration=0.0, duration_max=0.0, duration_list=0.0, act_dur=0.0;

  int num_dp, j, *dp_vect = NULL;
  int aus_counter;

  
  if(GpG.first_execution_cri==0 && GpG.timed_facts_present &&  Hvar.num_tmd_facts_array!=0  )
    reset_timed_preconds_in_Hvar();
  
#ifdef __TEST__1
  printf ("\n\n ----");
  print_op_name (index);
  printf ("\n");
#endif

  /**
     calcola l'istante di tempo minimo a cui l'azione index
     puo' essere eseguita
     *
     compute the minimum temporal istant in which the action index
     can be executed
   **/
  cri_predict_duration (index, &duration_max);

  if(duration_max<0)
    {
      if(GET_BIT(GpG.has_timed_preconds,index))
	 return duration_max; /* Not applicable action */
      else
	{
	  printf("\n Error in start time of action %d",index);
	  exit(0);
	}
    }


  if (GpG.cri_evaluate_preconditions >= COMPUTE_DG_LIST_COST )
    {
      /**
	 compute the cost of the action index with a relaxed plan 
      **/
      reset_bitarray (Hvar.ri_supp_bit_vect_facts, gnum_ft_block);
      cost = cri_predict_cost_relaxed (index, &duration_list, &num_actions);
    }
  else if (GpG.cri_evaluate_preconditions == COMPUTE_DG_SUM_COST)
    /**
       compute the cost of the actual action just like 
       a sum of the cost of Preconditions 
     **/
    cost = cri_predict_cost_sum (index,  &num_actions);
  else
    /**
       compute the cost of the actual action just like as max 
       of the cost of Preconditions 
     **/
    cost = cri_predict_cost_max (index,  &num_actions);

  /**
     in order to obtain the duration of the action index
   **/
  act_dur = get_action_time (index, 0);

  if (duration_max >= duration_list)
    duration =  act_dur + duration_max;
  else
    duration = act_dur + duration_list;


  if( GpG.first_execution_cri==0  && GpG.timed_facts_present && 
     GET_BIT(GpG.has_timed_preconds,index) )
    insert_timed_preconds_in_Hvar(index);

  /** 
      AT_START effects 
  **/
  if (gef_conn[index].sf != NULL)
    for (i = 0; i < gef_conn[index].sf->num_A_start; i++)
      {
	/*
	  Se index e' l'unica azione in grado di supportare il fatto (e questo compare negli effetti cancellanti) bisogna considerarla, tuttavia incrementiamo il suo costo di inserimento affinche' se possibile vengano considerate altre azioni come best_action  
	 */
	if (is_fact_in_delete_effects (index, gef_conn[index].sf->A_start[i]))
	  {
	    if (gef_conn[index].sf->A_start[i] >= 0)
	      cri_insert_ftcost (gef_conn[index].sf->A_start[i], MAX_COST, 
			     duration- act_dur, MAX_COST, index);

	//  continue;
	  }
	else
	  if (gef_conn[index].sf->A_start[i] >= 0) {
	    cri_insert_ftcost (gef_conn[index].sf->A_start[i], cost, 
			     duration- act_dur, num_actions, index);

	    // Calcolo dei nuovi predicati derivati e aggiornamento del numero del vettore del numero di precondizioni non supportate
	    if (GpG.derived_predicates) 
	      {
		num_dp = calc_new_derived_predicates_from(gef_conn[index].sf->A_start[i], derived_precs, fact_vect, ADD_FACT, &dp_vect);
		for (j = 0; j < num_dp; j++)
		  if (dp_vect[j] >= 0) 
		    {
		      cri_insert_ftcost (dp_vect[j], cost, duration - act_dur, num_actions, index);
		      /*se il fatto non era ancora stato reso vero */ 
		      gft_conn[dp_vect[j]].in_F = TRUE;
		      gft_conn[dp_vect[j]].level = level + 1;
		      // Se il fatto reso vero era prec. di qualche azione aggiorno il vettore
		      // delle prec. non supportate andando a decrementare la posizione relativa all'azione i
		      
		      if (GpG.derived_pred_in_preconds)
			for(aus_counter = 0; aus_counter < gft_conn[dp_vect[j]].num_PC; aus_counter++)
			  {      
			    Numeric.ri_prec_vector[gft_conn[dp_vect[j]].PC[aus_counter]]--;
			    if(Numeric.ri_prec_vector[gft_conn[dp_vect[j]].PC[aus_counter]]==0)
			      (*changed)=TRUE;
			  }
		    }
	      }
	    
	  }

      }

  /**
     AT_END effects
  **/
  for (i = 0; i < gef_conn[index].num_A; i++)
    {
      if (gef_conn[index].A[i] >= 0)
	cri_insert_ftcost (gef_conn[index].A[i], cost, 
			   duration, num_actions, index);

     
      // Calcolo dei nuovi predicati derivati e aggiornamento del numero del vettore del numero di precondizioni non supportate
      if (GpG.derived_predicates) 
	{
	  num_dp = calc_new_derived_predicates_from(gef_conn[index].A[i], derived_precs, fact_vect, ADD_FACT, &dp_vect);
	  for (j = 0; j < num_dp; j++)
	    if (dp_vect[j] >= 0) {
	      cri_insert_ftcost (dp_vect[j], cost, duration, num_actions, index);
	      /*se il fatto non era ancora stato reso vero */ 
	      gft_conn[dp_vect[j]].in_F = TRUE;
	      gft_conn[dp_vect[j]].level = level + 1;
	      // Se il fatto reso vero era prec. di qualche azione aggiorno il vettore
	      // delle prec. non supportate andando a decrementare la posizione relativa all'azione i
	      
	      if (GpG.derived_pred_in_preconds)
		for(aus_counter = 0; aus_counter < gft_conn[dp_vect[j]].num_PC; aus_counter++)
		  {
		    Numeric.ri_prec_vector[gft_conn[dp_vect[j]].PC[aus_counter]]--;
		    if(Numeric.ri_prec_vector[gft_conn[dp_vect[j]].PC[aus_counter]]==0)
		      (*changed)=TRUE;
		  }
	    }
	  
	}
    }
 
  memcpy(F, fact_vect, gnum_ft_block * sizeof(int));
  
  if (dp_vect)
    free(dp_vect);

  return duration;

}

/**
 * Nome: cri_heuristic_for_action
 * Scopo: aggiorna i valori di raggiungibilità modificati a seguito 
 * dell'inserimento di una azione (di indice action) al livello (level)
 * Funzioni chiamate: ls_insert_fact_inlist
 *                    remove_mutex_facts_in_bitvect_and_update_num_actions
 * Chiamata da: insert_action_in_vectlevel     
 *
 * Name: cri_heuristic_for_action
 * Purpose: update the reachability values modified by the insertion
 * of an action (of index action) at level (level)
 * Functions used:  ls_insert_fact_inlist
 *                    remove_mutex_facts_in_bitvect_and_update_num_actions
 * Called by: insert_action_in_vectlevel     
 **/

inline void cri_heuristic_for_action (int action, int level)
{
  static int *initial_local_bit_vect_facts=NULL;
  register int i, j, k, el=0, fact_pos, skip = FALSE;
  float max_prec_cost, max_prec_duration, new_cost, new_duration;
  int max_prec_num_actions=0;

  int *derived_precs = NULL;
  int n, num_dp = 0,  *dp_vect = NULL;

  if (GpG.derived_predicates && GpG.derived_pred_in_preconds) {
    derived_precs = (int *)calloc(gnum_dp_conn, sizeof(int));
    memcpy(derived_precs, vectlevel[level] -> gnum_dp_precs, gnum_dp_conn * sizeof(int));
  }

  max_prec_cost=0.0;
  max_prec_duration=0.0;
  new_cost=0.0;
  new_duration=0.0;

#ifdef __TEST__
  printf
    ("\n\n\n ######\n  ACTION %d  of level %d name= ",
     action, level);
  print_op_name (action);
  printf ("\n");
#endif

  /**
     Resetta i parametri già instanziati
     *
     Reset the istanciated parameters 
  **/

  GpG.cri_initial_or_update=1;
  GpG.cri_update_level=level;

  reset_bitarray (Hvar.local_bit_vect_facts, gnum_ft_block);
  reset_bitarray (Hvar.local_bit_vect_actions, gnum_ef_block);

  memset(Hvar.ri_best_act_for_facts, INFINITY,  gnum_ft_conn* sizeof(int));
  memset (Hvar.ri_tot_cost_of_facts, 0, gnum_ft_conn * sizeof (float));
  memset (Hvar.ri_cost_of_facts, 0, gnum_ft_conn * sizeof (float));
  memset (Hvar.ri_duration_of_facts, 0, gnum_ft_conn * sizeof (float));
  memset (Hvar.ri_num_actions_of_facts, 0, gnum_ft_conn * sizeof (int));

  reset_bitarray (Hvar.bit_vect_facts, gnum_ft_block);
  reset_bitarray (Hvar.bit_vect_actions, gnum_ef_block);

  Hvar.num_facts_define_cost=0;
  Hvar.num_actions_define_cost = 0;
  Hvar.cost_actions_define_cost=0.0;
  Hvar.time_actions_define_cost=0.0;


  reset_bitarray (Hvar.ri_bit_vect_actions, gnum_ef_block);

  Hvar.ri_num_actions_define_cost = 0;
  Hvar.ri_num_facts_define_cost = 0;
  Hvar.ri_cost_actions_define_cost=0.0;
  Hvar.ri_time_actions_define_cost=0.0;



  if(initial_local_bit_vect_facts==NULL)
    initial_local_bit_vect_facts= alloc_vect (gnum_ft_block);

  /** 
     Setta il bit-vector local_bit_vect_facts con i 
     fatti veri prima di applicare l'azione
     *
     Set bit-array local_bit_vect_facts with the facts that
     are true before the applications of the action
  **/
  memcpy( Hvar.local_bit_vect_facts, vectlevel[level]->fact_vect,gnum_ft_block*sizeof(int)); 


  /** 
     Controlla se le precondizioni at start dell'azione action
     sono supportate nel corrente action subgraph
     *
     Check if the at start preconditions of the action "action"
     are supported in the underlying action subgraph
  **/
  for (i = 0; i < gef_conn[action].num_PC; i++)
    { 
      /* 
	 Non considero precondizioni numeriche
	 *
	 Do not consider numeric preconditions
       */
      if (gef_conn[action].PC[i] < 0)
	continue;
      
      /** 
	  all the at start preconditions must be true in the new state 
       **/

      if (GET_BIT (Hvar.local_bit_vect_facts, gef_conn[action].PC[i]) == 0)
	{
	  /** 
	     Se la precondizione di indice i non è 
	     supportata la considero supportata poichè altrimenti 
	     l'azione non è applicabile
	     *
	     If the precondition of index i is not supported
	     LPG considers it like supported because otherwise
	     the action isn't applicabile
	  **/
	  SET_BIT (Hvar.local_bit_vect_facts, gef_conn[action].PC[i]);

	  /** 
	     Inserisco la precondizione nella lista dei fatti 
	     da considerare 
	     *
	     Insert the precondition in the set of facts to consider
	  **/
	  ls_insert_fact_inlist (gef_conn[action].PC[i]);

	  /** 
	     Rimuovo dalla lista dei fatti attualmente supportati 
	     quelli che sono mutex con le precondizioni dell'azione, 
	     perche' genererebbero uno stato inconsistente
	     *
	     Remove the facts mutex with the preconditions of the
	     action from the set of fact supported, because otherwise
	     the state is inconsistent
	  **/
	  remove_mutex_facts_in_bitvect_and_update_num_actions (gef_conn[action].PC[i], Hvar.local_bit_vect_facts);

	}
      else
	if(GpG.cri_update_all_facts==1)
	  ls_insert_fact_inlist (gef_conn[action].PC[i]);
    }



  if (gef_conn[action].sf)
    {
      /**
	 Controlla se le precondizioni overall dell'azione action 
	 sono supportate
	 *
	 Check if the over all preconditions of the action "action"
	 are supported in the underlying action subgraph
      **/
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{
	  /** 
	     Non considero precondizioni numeriche
	     *
	     Do not consider numeric preconditions
	  **/
	  if (gef_conn[action].sf->PC_overall[i] < 0)
	    continue;

	  /** 
	     Se il fatto appartiene agli effetti at_start è 
	     già supportato dall'azione stessa, quindi
	     non viene preso in considerazione
	     *
	     if the fact is an at_start effect of the action, then
	     do not consider it
	  **/ 
	  if (is_fact_in_additive_effects_start
	      (action, gef_conn[action].sf->PC_overall[i]))
	    continue;

	  /** 
	      all the over all preconditions must be true in the new state 
	  **/
	  if (GET_BIT(Hvar.local_bit_vect_facts, gef_conn[action].sf->PC_overall[i]) == 0)
	    {
	      /** 
		  Se la precondizione di indice i non è 
		  supportata la considero supportata poichè altrimenti 
		  l'azione non è applicabile
		  *
		  If the precondition of index i is not supported
		  LPG considers it like supported because otherwise
		  the action isn't applicabile
	      **/
	      SET_BIT (Hvar.local_bit_vect_facts,
		       gef_conn[action].sf->PC_overall[i]);

	      /** 
		  Inserisco la precondizione nella lista dei fatti 
		  da considerare 
		  *
		  Insert the precondition in the set of facts to consider
	      **/
	      ls_insert_fact_inlist (gef_conn[action].sf->PC_overall[i]);

	      /** 
		  Rimuovo dalla lista dei fatti attualmente supportati 
		  quelli che sono mutex con le precondizioni dell'azione, 
		  perche' genererebbero uno stato inconsistente
		  *
		  Remove the facts mutex with the preconditions of the
		  action from the set of fact supported, because otherwise
		  the state is inconsistent
	      **/
	      remove_mutex_facts_in_bitvect_and_update_num_actions (gef_conn[action].sf->PC_overall[i], Hvar.local_bit_vect_facts);
	    }
	  else
	    if(GpG.cri_update_all_facts==1)
	      ls_insert_fact_inlist (gef_conn[action].sf->PC_overall[i]);
	  
	}
      
      /**
	 Controlla se le precondizioni at end dell'azione action 
	 sono supportate
	 *
	 Check if the at end preconditions of the action "action"
	 are supported in the underlying action subgraph
      **/
      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	{ 
	  /** 
	     Non considero precondizioni numeriche
	     *
	     Do not consider numeric preconditions
	  **/
	  if (gef_conn[action].sf->PC_end[i] < 0)
	    continue;

	  /** 
	     Se il fatto appartiene agli effetti at_start è 
	     già supportato dall'azione stessa, quindi
	     non viene preso in considerazione
	     *
	     if the fact is an at_start effect of the action, then
	     we do not consider it
	  **/ 
	  if(is_fact_in_additive_effects(action,gef_conn[action].sf->PC_end[i]))
	    continue;

	  /** 
	      all the at end preconditions must be true in the new state 
	  **/
	  if (GET_BIT(Hvar.local_bit_vect_facts, gef_conn[action].sf->PC_end[i]) == 0)
	    {
	      /** 
		  Se la precondizione di indice i non è 
		  supportata la considero supportata poichè altrimenti 
		  l'azione non è applicabile
		  *
		  If the precondition of index i is not supported
		  LPG considers it like supported because otherwise
		  the action isn't applicabile
	      **/
	      SET_BIT (Hvar.local_bit_vect_facts,gef_conn[action].sf->PC_end[i]);
	      
	      /** 
		  Inserisco la precondizione nella lista dei fatti 
		  da considerare 
		  *
		  Insert the precondition in the set of facts to consider
	      **/
	      ls_insert_fact_inlist (gef_conn[action].sf->PC_end[i]);

	      /** 
		  Rimuovo dalla lista dei fatti attualmente supportati 
		  quelli che sono mutex con le precondizioni dell'azione, 
		  perche' genererebbero uno stato inconsistente
		  *
		  Remove the facts mutex with the preconditions of the
		  action from the set of fact supported, because otherwise
		  the state is inconsistent
	      **/
	      remove_mutex_facts_in_bitvect_and_update_num_actions (gef_conn[action].sf->PC_end[i], Hvar.local_bit_vect_facts);
	    }
	  else
	    if(GpG.cri_update_all_facts==1)
	      ls_insert_fact_inlist (gef_conn[action].sf->PC_end[i]);
	}
    }
  
  
  /** 
     Considero come supportati gli effetti dell'azione 
     *
     Consider the effects of the action like supported
  **/
  
  /** 
      at start effects
  **/
  if (gef_conn[action].sf)
    for (i = 0; i < gef_conn[action].sf->num_A_start; i++)
      { 
	/** 
	    Non considero effetti numerici
	    *
	    Do not consider numeric effects
	**/
	if (gef_conn[action].sf->A_start[i] < 0)
	  continue;

        /** 
	   Se l'effetto at start e' anche un effetto cancellante at end
	   non lo considero supportato
	   *
	   If the at start effect is also an at end delete effect, then
	   do not consider it like supported
	**/
	if (is_fact_in_delete_effects
	    (action, gef_conn[action].sf->A_start[i]))
	  continue;

	/** 
	    all the at start effects must be true in the new state 
	**/
	if (GET_BIT(Hvar.local_bit_vect_facts, gef_conn[action].sf->A_start[i]) == 0)
	  { 
	    /**
	       Considero vero il fatto supportato da questo effetto additivo 
	       settando il bit corrispondente in local_bit_vect_facts
	       *
	       Consider true the fact supported by this additive effects
	       setting the corresponding bit in local_bit_vect_facts
	    **/
	    
	    if (GpG.derived_predicates && GpG.derived_pred_in_preconds) 
	      {
		
		num_dp =  calc_new_derived_predicates_from(gef_conn[action].sf->A_start[i], derived_precs, 
							   Hvar.local_bit_vect_facts, ADD_FACT, &dp_vect);
		for (k = 0; k < num_dp; k++)
		  if (dp_vect[k] >= 0)
		    ls_insert_fact_inlist(dp_vect[k]);
	      }
	    
	    SET_BIT (Hvar.local_bit_vect_facts,
		     gef_conn[action].sf->A_start[i]);

	    /** 
		Inserisco l'effetto at start nell'insieme dei fatti da considerare 
		*
		Insert the at start effect in the set of facts to consider
	    **/
	    ls_insert_fact_inlist (gef_conn[action].sf->A_start[i]);

	    /** 
		Rimuovo dalla lista dei fatti attualmente supportati 
		quelli che sono mutex con l'effetto at start dell'azione, 
		perche' altrimenti lo stato sarebbe inconsistente
		*
		Remove the facts mutex with the at start effect of the
		action from the set of fact supported, because otherwise
		the state is inconsistent
	    **/
	    remove_mutex_facts_in_bitvect_and_update_num_actions(gef_conn[action].sf->A_start[i], Hvar.local_bit_vect_facts);
	  }
      }

  
  /** 
     at end effects
  **/
  for (i = 0; i < gef_conn[action].num_A; i++)
    { 

      /** 
	  Non considero effetti numerici
	  *
	  Do not consider numeric effects
      **/
      if (gef_conn[action].A[i] < 0)
	continue;
      
      /** 
	  all the at end effects must be true in the new state 
      **/
      if (GET_BIT (Hvar.local_bit_vect_facts, gef_conn[action].A[i]) == 0)		
	{
	  /* Considero vero il fatto supportato da questo effetto additivo 
	     settando il bit corrispondente in local_bit_vect_facts
	     *
	     Consider true the fact supported by this additive effects
	     setting the corresponding bit in local_bit_vect_facts
	  */
	  
	  if (GpG.derived_predicates && GpG.derived_pred_in_preconds) 
	    {
	      
	      num_dp =  calc_new_derived_predicates_from(gef_conn[action].A[i], derived_precs, 
							 Hvar.local_bit_vect_facts, ADD_FACT, &dp_vect);
	      for (k = 0; k < num_dp; k++)
		if (dp_vect[k] >= 0)
		  ls_insert_fact_inlist(dp_vect[k]);
	    }
	  
	  
	  SET_BIT (Hvar.local_bit_vect_facts, gef_conn[action].A[i]);
	  
	  /** 
	      Inserisco l'effetto at end nella lista dei fatti da considerare 
	      *
	      Insert the at end effect in the set of facts to consider
	  **/
	  ls_insert_fact_inlist (gef_conn[action].A[i]);
	  
	  /** 
	      Rimuovo dalla lista dei fatti attualmente supportati 
	      quelli che sono mutex con l'effetto at end dell'azione, 
	      perche' altrimenti lo stato sarebbe inconsistente
	      *
	      Remove the facts mutex with the at end effect of the
	    action from the set of fact supported, because otherwise
	    the state is inconsistent
	  **/
	  remove_mutex_facts_in_bitvect_and_update_num_actions (gef_conn[action].A[i], Hvar.local_bit_vect_facts);
	}
    }
  

  /**
     Copia i valori attuali contenuti nel bit vector Hvar.local_bit_vect_facts
     in initial_local_bit_vect_facts che NON VIENE PIU' MODIFICATO
     *
     Copy the actual values containing in bit-array Hvar.local_bit_vect_facts
     in initial_local_bit_vect_facts that it will not be modified
  **/
  memcpy( initial_local_bit_vect_facts,Hvar.local_bit_vect_facts, gnum_ft_block * sizeof (int));


  /** 
      Now recompute the new heuristics for this state
  **/

  for (i = 0; i < Hvar.num_facts_define_cost; i++)
    {
      fact_pos = Hvar.list_ft_define_cost[i];

      /**
	 Se il fatto era prima supportato ma ora non lo e' piu', allora saltalo
	 *
	 If the fact was previously supported but now is not supported, then skip it
      **/
      if (GET_BIT (Hvar.local_bit_vect_facts, fact_pos) == 0  && Hvar.ri_cost_of_facts[fact_pos] == 0.0)
	continue; // unsupported fact

#ifdef __TEST__1
      printf ("\n\n\n------ Now consider Fact %d   ", fact_pos);
      print_ft_name (fact_pos);
      if( gft_conn[fact_pos].num_PC<=0)
	{
	  printf("\nFact %d Step %d, num add actions %d, name", fact_pos, GpG.count_num_try, gft_conn[fact_pos].num_PC );
	  print_ft_name (fact_pos);
	}
#endif

      /**  
	   Esamina le azioni di cui il fatto e' precondizione
	   *
	   Check the actions of which the fact is precondition
       **/
      for (j = 0; j < gft_conn[fact_pos].num_PC; j++)
	{

	  el = gft_conn[fact_pos].PC[j];

	  /** 
	     Se l'azione ha indice negativo (non accettabile) salta
	     *
	     If the action has negative index (not acceptable), then skip it
	  **/
	  if (el < 0)
	    continue;

#ifdef __TEST__1
	  printf ("\n  Action %d  name= ", el, new_cost, max_prec_cost);
	  print_op_name (el);
	  printf (" has fact %d as precondition  ", fact_pos);
	  print_ft_name (fact_pos);
#endif

	  /**
	     local_bit_vect_actions e' il bit-vector che mi permette 
	     di sapere se l'azione di indice el e' stata precedentemente 
	     esaminata per non eseguire operazioni inutili
	     *
	     local_bit_vect_actions is a bit-array that allow to know
	     if the action of index el was previuoly examined in order
	     to avoid useless operations
	  **/
	  if (GET_BIT (Hvar.local_bit_vect_actions, el)) // check if I have previously examined the action
	    {
#ifdef __TEST__1
	      printf ("\nAction previously examined");
#endif
	      continue;
	    }

	  /* 
	     Se l'azione non è stata precedentemente esaminata
	     *
	     If the action was not previoulsy examined
	   */
	  else
	    {
	      skip = FALSE;

	      max_prec_num_actions = 0;
	      max_prec_duration = max_prec_cost = 0.0;


	      /**
		 Precondizioni AT_START, controllo che siano supportate 
		 altrimenti salto l'azione poichè attualmente non è applicabile
		 *
		 Check if the precondition at start is supported,
		 otherwise skip the action, because is now not applicable
	      **/
	      for (k = 0; k < gef_conn[el].num_PC; k++)	
		/**
		   if its preconditions are supported or previously computed, 
		   then set the additive effects of el
		**/
		{
		  /** 
		     Non considera precondizioni numeriche
		     *
		     Do not consider numeric preconditions
		  **/
		  if (gef_conn[el].PC[k] < 0)
		    continue;
		 
		 
		  /**
		     The precondition is not supported and we have 
		     not previously computed its cost 
		  **/
		  if (Hvar.ri_best_act_for_facts[gef_conn[el].PC[k]] < 0 && 
		      GET_BIT ( initial_local_bit_vect_facts, gef_conn[el].PC[k])==0 )
			{
#ifdef __TEST__1
			  printf ("\n Break, Prec %d not supported ",
				  gef_conn[el].PC[k]);
			  print_ft_name (gef_conn[el].PC[k]);
#endif
			  skip = TRUE;
			  break;
			}
		      else
			{
#ifdef __TEST__1
			  printf
			    ("\n Prec %d Cost %.2f Duration %.2f num actions %d  name ",
			     gef_conn[el].PC[k],
			     Hvar.ri_cost_of_facts[gef_conn[el].PC[k]],
			     Hvar.ri_duration_of_facts[gef_conn[el].PC[k]],
			     Hvar.ri_num_actions_of_facts[gef_conn[el].PC[k]]);
			  print_ft_name (gef_conn[el].PC[k]);
#endif
                          /**
			     Se il costo di tale precondizione supera 
			     il massimo finora computato, assegna al 
			     massimo il nuovo valore
			  **/
			  if (Hvar.ri_cost_of_facts[gef_conn[el].PC[k]] >
			      max_prec_cost)
			    max_prec_cost = Hvar.ri_cost_of_facts[gef_conn[el].PC[k]];

			  if (CONVERT_FACT_TO_NODE(gef_conn[el].PC[k], level)->time_f > max_prec_duration)
			    max_prec_duration = CONVERT_FACT_TO_NODE (gef_conn[el].PC[k], level)->time_f;

			  /** 
			     Se l'istante minimo a cui la precondizione 
			     puo' essere resa supportata supera il massimo 
			     finora computato, assegna al massimo il nuovo 
			     valore
			  **/			  
			  else if (Hvar.
				   ri_duration_of_facts[gef_conn[el].PC[k]] >
				   max_prec_duration)
			    max_prec_duration =
			      Hvar.ri_duration_of_facts[gef_conn[el].PC[k]];
			  /* Se il costo, in termini di azioni, per rendere supporatata la precondizione,
			   *  supera il massimo finora computato, assegna al massimo il nuovo valore
			   */
			  if (Hvar.
			      ri_num_actions_of_facts[gef_conn[el].PC[k]] >
			      max_prec_num_actions)
			    max_prec_num_actions =
			      Hvar.ri_num_actions_of_facts[gef_conn[el].PC[k]];
			}


		}		// for PC AT_START

	      /* Se ho dichiarato che l'azione era da saltare (rendendo skip=TRUE) passo alla prossima 
	       */
	      if (skip)
		continue;	// I do not consider this action

	      /* Precondizioni overall e at end
	       */
	      if (gef_conn[el].sf != NULL)
		{

		  // Precondizioni OVERALL
		  for (k = 0; k < gef_conn[el].sf->num_PC_overall; k++)	
		    //if its preconditions are supported or previously computed I set the additive effects of el
		    {
		      /* Non prendo in considerazione precondizioni numeriche
		       */
		      if (gef_conn[el].sf->PC_overall[k] < 0)
			continue;	// LAZZA
		      /* Se la precondizione si trova negli effetti additivi at start è la stessa azione
		       * a rendere supportata tale precondizione overall
		       */
		      if (is_fact_in_additive_effects_start
			  (el, gef_conn[el].sf->PC_overall[k]))
			continue;

		     
		      //     if (GET_BIT(Hvar.local_bit_vect_facts,   gef_conn[el].sf->PC_overall[k]) != 0)
			

		      /* Precondizioni OVERALL, controllo che siano supportate altrimenti salto l'azione
		       * poichè attualmente non è applicabile
		       */
			  if (Hvar.ri_best_act_for_facts[gef_conn[el].sf->PC_overall[k]] < 0  
			      && GET_BIT ( initial_local_bit_vect_facts,gef_conn[el].sf->PC_overall[k])==0  )
			    {

#ifdef __TEST__1

			      printf ("\n Break, Prec %d not supported ",
				      gef_conn[el].sf->PC_overall[k]);
			      print_ft_name (gef_conn[el].sf->PC_overall[k]);
#endif
			      skip = TRUE;
			      break;
			      // The precondition is not supported and we have not previously compued its cost
			    }
			  else
			    {

#ifdef __TEST__1

			      printf
				("\n Prec %d Cost %.2f Duration %.2f num actions %d  name ",
				 gef_conn[el].sf->PC_overall[k],
				 Hvar.ri_cost_of_facts[gef_conn[el].sf->
						      PC_overall[k]],
				 Hvar.ri_duration_of_facts[gef_conn[el].sf->
							  PC_overall[k]],
				 Hvar.ri_num_actions_of_facts[gef_conn[el].sf->
							     PC_overall[k]]);
			      print_ft_name (gef_conn[el].sf->PC_overall[k]);
#endif

			      /* Se il costo di tale precondizione supera il massimo fimìnora computato,
			       * assegna al massimo il nuovo valore
			       */
			      if (Hvar.
				  ri_cost_of_facts[gef_conn[el].sf->
						  PC_overall[k]] >
				  max_prec_cost)
				max_prec_cost =
				  Hvar.ri_cost_of_facts[gef_conn[el].sf->
						       PC_overall[k]];



			      if (CONVERT_FACT_TO_NODE
				  (gef_conn[el].sf->PC_overall[k],
				   level)->time_f > max_prec_duration)
				max_prec_duration =
				  CONVERT_FACT_TO_NODE (gef_conn[el].sf->
							  PC_overall[k],
							  level)->time_f;

			      /* Se l'istante minimo a cui la precondizione puo' essere resa supportata
			       * supera il massimo finora computato, assegna al massimo il nuovo valore
			       */	
			      else if (Hvar.
				       ri_duration_of_facts[gef_conn[el].sf->
							   PC_overall[k]] >
				       max_prec_duration)
				max_prec_duration =
				  Hvar.ri_duration_of_facts[gef_conn[el].sf->
							   PC_overall[k]];
			      /* Se il costo, in termini di azioni, per rendere supporatata la precondizione,
			       *  supera il massimo finora computato, assegna al massimo il nuovo valore
			       */
			      if (Hvar.
				  ri_num_actions_of_facts[gef_conn[el].sf->
							 PC_overall[k]] >
				  max_prec_num_actions)
				max_prec_num_actions =
				  Hvar.ri_num_actions_of_facts[gef_conn[el].
							      sf->
							      PC_overall[k]];
			    }


		    }		// for PC OVERALL


		  /* Se ho dichiarato che l'azione era da saltare (rendendo skip=TRUE) passo alla prossima 
		   */
		  if (skip)
		    continue;	// I do not consider this action



		  // Precondizioni AT_END
		  for (k = 0; k < gef_conn[el].sf->num_PC_end; k++)	//if its preconditions are supported or previously computed I set the additive effects of el
		    {
		      /* Non prendo in considerazione precondizioni numeriche
		       */
		      if (gef_conn[el].sf->PC_end[k] < 0)
			continue;	// LAZZA

		      /* Se la precondizione si trova negli effetti additivi at starto at end  è la stessa azione
		       * a rendere supportata tale precondizione at end
		       */
		      if (is_fact_in_additive_effects_start(el, gef_conn[el].sf->PC_end[k]))
			continue;
	

		      /* Precondizioni AT END, controllo che siano supportate altrimenti salto l'azione
		       * poichè attualmente non è applicabile
		       */
		      if (Hvar.ri_best_act_for_facts[gef_conn[el].sf->PC_end[k]]< 0  
			  && GET_BIT ( initial_local_bit_vect_facts,gef_conn[el].sf->PC_end[k])==0 )
			    {

#ifdef __TEST__1

			      printf ("\n Break, Prec %d not supported ",gef_conn[el].sf->PC_end[k]);
			      print_ft_name (gef_conn[el].sf->PC_end[k]);
#endif
			      skip = TRUE;
			      break;
			      // The precondition is not supported and we have not previously computed its cost
			    }
			  else
			    {

#ifdef __TEST__1

			      printf
				("\n Prec %d Cost %.2f Duration %.2f num actions %d  name ",
				 gef_conn[el].sf->PC_end[k],
				 Hvar.ri_cost_of_facts[gef_conn[el].sf->
						      PC_end[k]],
				 Hvar.ri_duration_of_facts[gef_conn[el].sf->
							  PC_end[k]],
				 Hvar.ri_num_actions_of_facts[gef_conn[el].sf->
							     PC_end[k]]);
			      print_ft_name (gef_conn[el].sf->PC_end[k]);
#endif

			      /* Se il costo di tale precondizione supera il massimo finora computato,
			       * assegna al massimo il nuovo valore
			       */
			      if (Hvar.
				  ri_cost_of_facts[gef_conn[el].sf->
						  PC_end[k]] > max_prec_cost)
				max_prec_cost =
				  Hvar.ri_cost_of_facts[gef_conn[el].sf->
						       PC_end[k]];

			      if (CONVERT_FACT_TO_NODE
				  (gef_conn[el].sf->PC_end[k],
				   level)->time_f > max_prec_duration)
				max_prec_duration =
				  CONVERT_FACT_TO_NODE (gef_conn[el].sf->
							  PC_end[k],
							  level)->time_f;

			      /* Se l'istante minimo a cui la precondizione puo' essere resa supportata
			       * supera il massimo finora computato, assegna al massimo il nuovo valore
			       */
			      else if (Hvar.
				       ri_duration_of_facts[gef_conn[el].sf->
							   PC_end[k]] -
				       get_action_time (el,
							level) >
				       max_prec_duration)
				max_prec_duration =
				  Hvar.ri_duration_of_facts[gef_conn[el].sf->
							   PC_end[k]] -
				  get_action_time (el, level);
			      /* Se il costo, in termini di azioni, per rendere supporatata la precondizione,
			       *  supera il massimo finora computato, assegna al massimo il nuovo valore
			       */
			      if (Hvar.
				  ri_num_actions_of_facts[gef_conn[el].sf->
							 PC_end[k]] >
				  max_prec_num_actions)
				max_prec_num_actions =
				  Hvar.ri_num_actions_of_facts[gef_conn[el].
							      sf->PC_end[k]];
			    }
			}


		    }		// for PC AT_END

	    }
	

	  /* Se ho dichiarato che l'azione era da saltare (rendendo skip=TRUE) passo alla prossima 
	   */
	  if (skip)
	    continue;		// I do not consider this action


	  /* A seconda del tipo di euristica calcolo i nuovi valori di raggiungibilita'
	   */ 
	  if(GpG.cri_evaluate_preconditions==COMPUTE_DG_LIST_COST)
	    {	
	      /* Copio i valori di initial_local_bit_vect_facts in Hvar.ri_supp_bit_vect_facts,initial_local_bit_vect_facts
	       * per rendere disponibili i fatti attualmente supportati nel calcolo dei nuovi valori
	       */
	      memcpy( Hvar.ri_supp_bit_vect_facts,initial_local_bit_vect_facts, gnum_ft_block * sizeof (int));
	      /*compute the cost of the actual action with a relaxed plan where
	       * we insert the action not already applyed by other priors facts
	       */
	      new_cost=cri_predict_cost_relaxed (el, &new_duration, &max_prec_num_actions);
	     
	    }
	  else
	    {
	      /* Calcolo il nuovo costo
	       */
	      new_cost = max_prec_cost + get_action_cost (el, level, NULL);
	
	      max_prec_num_actions++;
	    }

	  new_duration = max_prec_duration + get_action_time (el, level);

	  /* Segnalo che l'azione e' gia' stata considerata andando a settare il bit a 1 nella posizione
	   * corrispondente (el)
	   */
	  SET_BIT (Hvar.local_bit_vect_actions, el);

#ifdef __TEST__1

	  printf
	    ("\n Now I consider the action %d  new_cost %.2f prec_cost %.2f name= ",
	     el, new_cost, max_prec_cost);
	  print_op_name (el);
#endif
	  /* Rendo supportati i fatti che sono effetti dell'azione considerata che è a questo
	   * punto applicabile ed assegno i valori di raggiungibilità
	   */
	  /* Effetti additivi at end
	   */
	  for (k = 0; k < gef_conn[el].num_A; k++)
	    /* Non prendo in considerazione effetti numerici
	     */
	    if (gef_conn[el].A[k] >= 0)
	      {
		/* Rendo il fatto attualmente supportato
		 */


		if (GpG.derived_predicates && GpG.derived_pred_in_preconds) 
		  {
		    
		    num_dp =  calc_new_derived_predicates_from(gef_conn[el].A[k], derived_precs, 
							       Hvar.local_bit_vect_facts, ADD_FACT, &dp_vect);
		    for (n = 0; n < num_dp; n++)
		      if (dp_vect[n] >= 0) {
			if (GET_BIT(Hvar.bit_vect_facts, dp_vect[n]) == 0
			    || Hvar.ri_num_actions_of_facts[dp_vect[n]] > max_prec_num_actions
			    || (Hvar.ri_num_actions_of_facts[dp_vect[n]] == max_prec_num_actions
				&& (GpG.orig_weight_cost * Hvar.ri_cost_of_facts[dp_vect[n]] +
				    GpG.orig_weight_time * Hvar.ri_duration_of_facts[dp_vect[n]]) >
				(GpG.orig_weight_cost * new_cost + GpG.orig_weight_time * new_duration)))
			  {
			    
#ifdef __TEST__1
			    printf ("\n\n +-+-+-OLD cost of fact  %d : ", dp_vect[n]);
			    print_ft_name (dp_vect[n]);
			    printf (" cost %.2f duration %.2f num_actions %d",
				    Hvar.ri_cost_of_facts[dp_vect[n]],
				    Hvar.ri_duration_of_facts[dp_vect[n]],
				    Hvar.ri_num_actions_of_facts[dp_vect[n]]);
#endif
			    ls_insert_fact_inlist (dp_vect[n]);
			    Hvar.ri_cost_of_facts[dp_vect[n]] = new_cost;
			    Hvar.ri_duration_of_facts[dp_vect[n]] = new_duration;
			    Hvar.ri_num_actions_of_facts[dp_vect[n]] = max_prec_num_actions;
			    Hvar.ri_best_act_for_facts[dp_vect[n]] = el;
#ifdef __TEST__1
			    printf ("\n\n ++++++Set cost of facts %d : ",dp_vect[n]);
			    print_ft_name (dp_vect[n]);
			    printf (" cost %.2f duration %.2f num_actions %d", new_cost, new_duration, Hvar.ri_num_actions_of_facts[dp_vect[n]]);
#endif
			  }
			
		      }
		  }
		


		  SET_BIT(  Hvar.local_bit_vect_facts, gef_conn[el].A[k]);

 
		  /* Se il fatto non è stato ancora preso in considerazione o ho valori
		   * massimi che superano gli attuali aggiorno i  valori di
		   * raggiungibilita'
		   * Utilizzo Hvar.bit_vect_facts poiche' questo definisce i fatti che vengono resi veri durante il processo di raggiungibilita' e viene modificato  da ls_insert_fact_inlist (gef_conn[el].A[k]);
		   */


		if (GET_BIT (Hvar.bit_vect_facts, gef_conn[el].A[k]) == 0
		    || Hvar.ri_num_actions_of_facts[gef_conn[el].A[k]] >
		    max_prec_num_actions
		    || (Hvar.ri_num_actions_of_facts[gef_conn[el].A[k]] ==
			max_prec_num_actions
			&& (GpG.orig_weight_cost *
			    Hvar.ri_cost_of_facts[gef_conn[el].A[k]] +
			    GpG.orig_weight_time *
			    Hvar.ri_duration_of_facts[gef_conn[el].A[k]]) >
			(GpG.orig_weight_cost * new_cost +
			 GpG.orig_weight_time * new_duration)))
		  {
#ifdef __TEST__1
		    printf ("\n\n +-+-+-OLD cost of fact  %d : ",
			    gef_conn[el].A[k]);
		    print_ft_name (gef_conn[el].A[k]);
		    printf (" cost %.2f duration %.2f num_actions %d",
			    Hvar.ri_cost_of_facts[gef_conn[el].A[k]],
			    Hvar.ri_duration_of_facts[gef_conn[el].A[k]],
			    Hvar.ri_num_actions_of_facts[gef_conn[el].A[k]]);
#endif
		    ls_insert_fact_inlist (gef_conn[el].A[k]);
		    Hvar.ri_cost_of_facts[gef_conn[el].A[k]] = new_cost;
		    Hvar.ri_duration_of_facts[gef_conn[el].A[k]] =
		      new_duration;
		    Hvar.ri_num_actions_of_facts[gef_conn[el].A[k]] =
		      max_prec_num_actions;
		    Hvar.ri_best_act_for_facts[gef_conn[el].A[k]] = el;
#ifdef __TEST__1
		    printf ("\n\n ++++++Set cost of facts %d : ",
			    gef_conn[el].A[k]);
		    print_ft_name (gef_conn[el].A[k]);
		    printf (" cost %.2f duration %.2f num_actions %d",
			    new_cost, new_duration,
			    Hvar.ri_num_actions_of_facts[gef_conn[el].A[k]]);
#endif
		  }
#ifdef __TEST__1
		else
		  {
		    printf ("\n  Eff %d  already set, cost %.2f name: ",
			    gef_conn[el].A[k],
			    Hvar.ri_cost_of_facts[gef_conn[el].A[k]]);
		    print_ft_name (gef_conn[el].A[k]);

		  }
#endif


	      }

	  // effetti additivi AT_START
	  if (gef_conn[el].sf)
	    for (k = 0; k < gef_conn[el].sf->num_A_start; k++)
	     /* Non prendo in considerazione effetti numerici
	     */
	      if (gef_conn[el].sf->A_start[k] >= 0)
		{
		  /* Rendo il fatto attualmente supportato
		   */

		  if (GpG.derived_predicates && GpG.derived_pred_in_preconds) 
		    {
		      
		      num_dp =  calc_new_derived_predicates_from(gef_conn[el].sf->A_start[k], derived_precs, 
								 Hvar.local_bit_vect_facts, ADD_FACT, &dp_vect);
		      for (n = 0; n < num_dp; n++)
			if (dp_vect[n] >= 0) {
			  if (GET_BIT(Hvar.bit_vect_facts, dp_vect[n]) == 0
			      || Hvar.ri_num_actions_of_facts[dp_vect[n]] > max_prec_num_actions
			      || (Hvar.ri_num_actions_of_facts[dp_vect[n]] == max_prec_num_actions
				  && (GpG.orig_weight_cost * Hvar.ri_cost_of_facts[dp_vect[n]] +
				      GpG.orig_weight_time * Hvar.ri_duration_of_facts[dp_vect[n]]) >
				  (GpG.orig_weight_cost * new_cost + GpG.orig_weight_time * new_duration)))
			    {
			      
#ifdef __TEST__1
			      printf ("\n\n +-+-+-OLD cost of fact  %d : ", dp_vect[n]);
			      print_ft_name (dp_vect[n]);
			      printf (" cost %.2f duration %.2f num_actions %d",
				      Hvar.ri_cost_of_facts[dp_vect[n]],
				      Hvar.ri_duration_of_facts[dp_vect[n]],
				      Hvar.ri_num_actions_of_facts[dp_vect[n]]);
#endif
			      ls_insert_fact_inlist (dp_vect[n]);
			      Hvar.ri_cost_of_facts[dp_vect[n]] = new_cost;
			      Hvar.ri_duration_of_facts[dp_vect[n]] = new_duration;
			      Hvar.ri_num_actions_of_facts[dp_vect[n]] = max_prec_num_actions;
			      Hvar.ri_best_act_for_facts[dp_vect[n]] = el;
#ifdef __TEST__1
			      printf ("\n\n ++++++Set cost of facts %d : ",dp_vect[n]);
			      print_ft_name (dp_vect[n]);
			      printf (" cost %.2f duration %.2f num_actions %d", new_cost, new_duration, Hvar.ri_num_actions_of_facts[dp_vect[n]]);
#endif
			    }
			  
			}
		    }

		  SET_BIT(  Hvar.local_bit_vect_facts, gef_conn[el].sf->A_start[k]); 

		  /* Se il fatto non è stato ancora preso in considerazione o ho valori
		   * massimi che superano gli attuali aggiorno i  valori di
		   * raggiungibilita'
		   */
		  if (GET_BIT
		      (Hvar.bit_vect_facts, gef_conn[el].sf->A_start[k]) == 0
		      || Hvar.ri_num_actions_of_facts[gef_conn[el].sf->
						     A_start[k]] >
		      max_prec_num_actions
		      || (Hvar.
			  ri_num_actions_of_facts[gef_conn[el].sf->
						 A_start[k]] ==
			  max_prec_num_actions
			  && (GpG.orig_weight_cost *
			      Hvar.ri_cost_of_facts[gef_conn[el].sf->
						   A_start[k]] +
			      GpG.orig_weight_time *
			      Hvar.ri_duration_of_facts[gef_conn[el].sf->
						       A_start[k]]) >
			  (GpG.orig_weight_cost * new_cost +
			   GpG.orig_weight_time * new_duration)))
		    {
		      if (is_fact_in_delete_effects
			  (el, gef_conn[el].sf->A_start[k]))
			continue;
#ifdef __TEST__1
		      printf ("\n\n +-+-+-OLD cost of fact  %d : ",
			      gef_conn[el].sf->A_start[k]);
		      print_ft_name (gef_conn[el].sf->A_start[k]);
		      printf (" cost %.2f duration %.2f num_actions %d",
			      Hvar.ri_cost_of_facts[gef_conn[el].sf->
						   A_start[k]],
			      Hvar.ri_duration_of_facts[gef_conn[el].sf->
						       A_start[k]],
			      Hvar.ri_num_actions_of_facts[gef_conn[el].sf->
							  A_start[k]]);
#endif
		      ls_insert_fact_inlist (gef_conn[el].sf->A_start[k]);
		      Hvar.ri_cost_of_facts[gef_conn[el].sf->A_start[k]] =
			new_cost;
		      Hvar.ri_duration_of_facts[gef_conn[el].sf->A_start[k]] =
			new_duration;
		      Hvar.ri_num_actions_of_facts[gef_conn[el].sf->
						  A_start[k]] =
			max_prec_num_actions;
		      Hvar.ri_best_act_for_facts[gef_conn[el].sf->A_start[k]] =
			el;
#ifdef __TEST__1
		      printf ("\n\n ++++++Set cost of facts %d : ",
			      gef_conn[el].sf->A_start[k]);
		      print_ft_name (gef_conn[el].sf->A_start[k]);
		      printf (" cost %.2f duration %.2f num_actions %d",
			      new_cost, new_duration,
			      Hvar.ri_num_actions_of_facts[gef_conn[el].sf->
							  A_start[k]]);
#endif
		    }
#ifdef __TEST__1
		  else
		    {
		      printf ("\n  Eff %d  already set, cost %.2f name: ",
			      gef_conn[el].sf->A_start[k],
			      Hvar.ri_cost_of_facts[gef_conn[el].sf->
						   A_start[k]]);
		      print_ft_name (gef_conn[el].sf->A_start[k]);

		    }
#endif


		}
	
	}			//ciclo su tutte le azioni
    }    

  if (GpG.derived_predicates && GpG.derived_pred_in_preconds)
    free(derived_precs);
}


/**
 * Nome: cri_heuristic_for_action_numeric_reach
 * Scopo: aggiorna i valori di raggiungibilità modificati a seguito 
 * dell'inserimento di una azione (di indice action) al livello (level)
 * Funzioni chiamate: ls_insert_fact_inlist
 *                    remove_mutex_facts_in_bitvect_and_update_num_actions
 * Chiamata da: insert_action_in_vectlevel     
 *
 * Name: cri_heuristic_for_action_numeric_reach
 * Purpose: update the reachability values modified by the insertion
 * of an action (of index action) at level (level)
 * Functions used:  ls_insert_fact_inlist
 *                    remove_mutex_facts_in_bitvect_and_update_num_actions
 * Called by: insert_action_in_vectlevel     
 **/

inline void cri_heuristic_for_action_numeric_reach (int action, int level)
{
  static int *initial_local_bit_vect_facts=NULL;
  register int i, k, x;
  float max_prec_cost, max_prec_duration, new_cost, new_duration;
  int max_prec_num_actions=0;
  static  int *num_prec_vector=NULL;
  static  int *applied=NULL;
  int aus_counter;
  static int *To_be_Executed=NULL;
  static float *val_max=NULL;
  static float *val_min=NULL;
  Bool changed=FALSE;
 
  static  int *True_num=NULL;
  
 

  max_prec_cost=0.0;
  max_prec_duration=0.0;
  new_cost=0.0;
  new_duration=0.0;

#ifdef __TEST__
  printf
    ("\n\n\n ######\n  ACTION %d  of level %d name= ",
     action, level);
  print_op_name (action);
  printf ("\n");
#endif

  /**
     Resetta i parametri gia' instanziati
     *
     Reset the istanciated parameters 
  **/
  
  reset_bitarray (Hvar.local_bit_vect_facts, gnum_ft_block);

  memset(Hvar.ri_best_act_for_facts, INFINITY,  gnum_ft_conn* sizeof(int));

  memset (Hvar.ri_tot_cost_of_facts, 0, gnum_ft_conn * sizeof (float));
  memset (Hvar.ri_cost_of_facts, 0, gnum_ft_conn * sizeof (float));
  memset (Hvar.ri_duration_of_facts, 0, gnum_ft_conn * sizeof (float));
  memset (Hvar.ri_num_actions_of_facts, 0, gnum_ft_conn * sizeof (int));

  reset_bitarray (Hvar.bit_vect_facts, gnum_ft_block);
  reset_bitarray (Hvar.bit_vect_actions, gnum_ef_block);

  Hvar.num_actions_define_cost = 0;
  Hvar.num_facts_define_cost = 0;
  Hvar.cost_actions_define_cost=0.0;
  Hvar.time_actions_define_cost=0.0;


  reset_bitarray (Hvar.ri_bit_vect_actions, gnum_ef_block);

  Hvar.ri_num_actions_define_cost = 0;
  Hvar.ri_num_actions_inserted = 0;
  Hvar.ri_num_facts_define_cost = 0;
  Hvar.ri_cost_actions_define_cost=0.0;
  Hvar.ri_time_actions_define_cost=0.0;

  if(num_prec_vector==NULL)
    num_prec_vector=alloc_vect(gnum_ef_conn);  
 
    memset (num_prec_vector, INFINITY, gnum_ef_conn * sizeof (int));

  if(applied==NULL)
    applied=alloc_vect(gnum_ef_block);
  else  
    reset_bitarray (applied, gnum_ef_block);

  if(To_be_Executed==NULL)
    To_be_Executed=alloc_vect(gnum_ef_block);
  else
    reset_bitarray (To_be_Executed, gnum_ef_block);

  

  memset(Hvar.ri_best_increase_for_compvar, INFINITY ,  gnum_comp_var* sizeof(int));
  memset(Hvar.ri_best_decrease_for_compvar, INFINITY ,  gnum_comp_var* sizeof(int));
  memset(Hvar.ri_best_assign_for_compvar, INFINITY ,  gnum_comp_var* sizeof(int)); 

  memset(Hvar.ri_tot_cost_of_numeric_facts,0.0,gnum_comp_var*sizeof (float));
  memset(Hvar.ri_cost_of_numeric_facts,0.0,gnum_comp_var*sizeof (float));
  memset(Hvar.ri_duration_of_numeric_facts,0.0,gnum_comp_var* sizeof (float));
  memset(Hvar.ri_num_actions_of_numeric_facts,0.0,gnum_comp_var*sizeof (int));
  reset_bitarray(Hvar.ri_initial_bit_vect_numeric_facts,gnum_block_compvar);

  if(val_max==NULL)
    val_max=(float *) calloc (gnum_comp_var, sizeof (float)); 
  if(val_min==NULL)
    val_min=(float *) calloc (gnum_comp_var, sizeof (float)); 

  memcpy(val_max,vectlevel[level+1]->numeric->values,gnum_comp_var*sizeof (float));
  memcpy(val_min,vectlevel[level+1]->numeric->values,gnum_comp_var*sizeof (float));

  if(True_num==NULL)
    True_num= alloc_vect (gnum_block_compvar);
  



  if(initial_local_bit_vect_facts==NULL)
    initial_local_bit_vect_facts= alloc_vect (gnum_ft_block);

  /** 
     Setta il bit-vector local_bit_vect_facts con i 
     fatti veri prima di applicare l'azione
     *
     Set bit-array local_bit_vect_facts with the facts that
     are true before the applications of the action
  **/
  memcpy( Hvar.local_bit_vect_facts, vectlevel[level]->fact_vect,gnum_ft_block*sizeof(int)); 



 

  /** 
     Controlla se le precondizioni at start dell'azione action
     sono supportate nel corrente action subgraph
     *
     Check if the at start preconditions of the action "action"
     are supported in the underlying action subgraph
  **/
  for (i = 0; i < gef_conn[action].num_PC; i++)
    { 
     
      if (gef_conn[action].PC[i] < 0)
	{
	  /* Se e' supportata  non la considero */
	  if(GET_BIT(Hvar.ri_initial_bit_vect_numeric_facts,-gef_conn[action].PC[i]) || vectlevel[level]->numeric->values[-gef_conn[action].PC[i]]>0.5)
	    continue;

	  if (Numeric.num_Pc_ef_matrix.bits[-gef_conn[action].PC[i]])
	    for(x = 0; x < gnum_ef_block; x++)
	      {
		/* Tutte le azioni che hanno questo fatto come precondizione, 
		   poiche' suppongo che la precondiozne numerica debba essere vera */
		To_be_Executed[x] = To_be_Executed[x] | get_bit_table_block(Numeric.num_Pc_ef_matrix, (-gef_conn[action].PC[i]), x); 
	      }
	  
	  /* La considero vera nello stato corrente */
	  cri_set_init_numeric_fact(-gef_conn[action].PC[i]);
	  continue;
	}
      
      /** 
	  all the at start preconditions must be true in the new state 
       **/

      if (GET_BIT (Hvar.local_bit_vect_facts, gef_conn[action].PC[i]) == 0)
	{
	  /** 
	     Se la precondizione di indice i non è 
	     supportata la considero supportata poichè altrimenti 
	     l'azione non è applicabile
	     *
	     If the precondition of index i is not supported
	     LPG considers it like supported because otherwise
	     the action isn't applicabile
	  **/
	  SET_BIT (Hvar.local_bit_vect_facts, gef_conn[action].PC[i]);
	  for(aus_counter=0;aus_counter< gft_conn[gef_conn[action].PC[i]].num_PC;aus_counter++)
	    {
	      SET_BIT(To_be_Executed,gft_conn[gef_conn[action].PC[i]].PC[aus_counter]);
	    }
	  /** 
	     Inserisco la precondizione nella lista dei fatti 
	     da considerare 
	     *
	     Insert the precondition in the set of facts to consider
	  **/
	  ls_insert_fact_inlist (gef_conn[action].PC[i]);
	  
	  /** 
	     Rimuovo dalla lista dei fatti attualmente supportati 
	     quelli che sono mutex con le precondizioni dell'azione, 
	     perche' genererebbero uno stato inconsistente
	     *
	     Remove the facts mutex with the preconditions of the
	     action from the set of fact supported, because otherwise
	     the state is inconsistent
	  **/
	  remove_mutex_facts_in_bitvect_and_update_num_actions (gef_conn[action].PC[i], Hvar.local_bit_vect_facts);

	}
      else
	if(GpG.cri_update_all_facts==1)
	  {
	    ls_insert_fact_inlist (gef_conn[action].PC[i]);

	  }
    }



  if (gef_conn[action].sf)
    {
      /**
	 Controlla se le precondizioni overall dell'azione action 
	 sono supportate
	 *
	 Check if the over all preconditions of the action "action"
	 are supported in the underlying action subgraph
      **/
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{

	  if (gef_conn[action].sf->PC_overall[i] < 0)
	    {
	      if(GET_BIT(Hvar.ri_initial_bit_vect_numeric_facts,-gef_conn[action].sf->PC_overall[i]) || vectlevel[level]->numeric->values[-gef_conn[action].sf->PC_overall[i]]>0.5)
		continue;

	      if (Numeric.num_Pc_ef_matrix.bits[-gef_conn[action].sf->PC_overall[i]])
		for(x = 0; x < gnum_ef_block; x++)
		  {
		    To_be_Executed[x] = To_be_Executed[x] | get_bit_table_block(Numeric.num_Pc_ef_matrix, (-gef_conn[action].sf->PC_overall[i]),x);
		  }
	      
	      cri_set_init_numeric_fact(-gef_conn[action].sf->PC_overall[i]);
	      
	      continue;
	    }
	  
	  /** 
	     Se il fatto appartiene agli effetti at_start è 
	     già supportato dall'azione stessa, quindi
	     non viene preso in considerazione
	     *
	     if the fact is an at_start effect of the action, then
	     do not consider it
	  **/ 
	  if (is_fact_in_additive_effects_start
	      (action, gef_conn[action].sf->PC_overall[i]))
	    continue;

	  /** 
	      all the over all preconditions must be true in the new state 
	  **/
	  if (GET_BIT(Hvar.local_bit_vect_facts, gef_conn[action].sf->PC_overall[i]) == 0)
	    {
	      /** 
		  Se la precondizione di indice i non è 
		  supportata la considero supportata poichè altrimenti 
		  l'azione non è applicabile
		  *
		  If the precondition of index i is not supported
		  LPG considers it like supported because otherwise
		  the action isn't applicabile
	      **/
	      SET_BIT (Hvar.local_bit_vect_facts,
		       gef_conn[action].sf->PC_overall[i]);

	       for(aus_counter=0;aus_counter< gft_conn[gef_conn[action].sf->PC_overall[i]].num_PC;aus_counter++)
		 {		   
		   SET_BIT(To_be_Executed,gft_conn[gef_conn[action].sf->PC_overall[i]].PC[aus_counter]);
		 }
	      /** 
		  Inserisco la precondizione nella lista dei fatti 
		  da considerare 
		  *
		  Insert the precondition in the set of facts to consider
	      **/
	      ls_insert_fact_inlist (gef_conn[action].sf->PC_overall[i]);

	      /** 
		  Rimuovo dalla lista dei fatti attualmente supportati 
		  quelli che sono mutex con le precondizioni dell'azione, 
		  perche' genererebbero uno stato inconsistente
		  *
		  Remove the facts mutex with the preconditions of the
		  action from the set of fact supported, because otherwise
		  the state is inconsistent
	      **/
	      remove_mutex_facts_in_bitvect_and_update_num_actions (gef_conn[action].sf->PC_overall[i], Hvar.local_bit_vect_facts);
	    }
	  else
	    if(GpG.cri_update_all_facts==1)
	      ls_insert_fact_inlist (gef_conn[action].sf->PC_overall[i]);
	  
	}
      
      /**
	 Controlla se le precondizioni at end dell'azione action 
	 sono supportate
	 *
	 Check if the at end preconditions of the action "action"
	 are supported in the underlying action subgraph
      **/
      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	{ 

	  if (gef_conn[action].sf->PC_end[i] < 0)
	    {
	      if(GET_BIT(Hvar.ri_initial_bit_vect_numeric_facts,-gef_conn[action].sf->PC_end[i])|| vectlevel[level]->numeric->values[-gef_conn[action].sf->PC_end[i]]>0.5)
		continue;

	      if (Numeric.num_Pc_ef_matrix.bits[-gef_conn[action].sf->PC_end[i]])
		for(x = 0; x < gnum_ef_block; x++)
		  {
		    To_be_Executed[x] = To_be_Executed[x] | get_bit_table_block(Numeric.num_Pc_ef_matrix, (-gef_conn[action].sf->PC_end[i]), x);
		  }
	      
	      cri_set_init_numeric_fact(-gef_conn[action].sf->PC_end[i]);
	      continue;
	    }

	  /** 
	     Se il fatto appartiene agli effetti at_start è 
	     già supportato dall'azione stessa, quindi
	     non viene preso in considerazione
	     *
	     if the fact is an at_start effect of the action, then
	     we do not consider it
	  **/ 
	  if(is_fact_in_additive_effects(action,gef_conn[action].sf->PC_end[i]))
	    continue;

	  /** 
	      all the at end preconditions must be true in the new state 
	  **/
	  if (GET_BIT(Hvar.local_bit_vect_facts, gef_conn[action].sf->PC_end[i]) == 0)
	    {
	      /** 
		  Se la precondizione di indice i non è 
		  supportata la considero supportata poichè altrimenti 
		  l'azione non è applicabile
		  *
		  If the precondition of index i is not supported
		  LPG considers it like supported because otherwise
		  the action isn't applicabile
	      **/
	       SET_BIT (Hvar.local_bit_vect_facts,gef_conn[action].sf->PC_end[i]);

	      for(aus_counter=0;aus_counter< gft_conn[gef_conn[action].sf->PC_end[i]].num_PC;aus_counter++)
		{		   
		  SET_BIT(To_be_Executed,gft_conn[gef_conn[action].sf->PC_end[i]].PC[aus_counter]);
		}
	      /** 
		  Inserisco la precondizione nella lista dei fatti 
		  da considerare 
		  *
		  Insert the precondition in the set of facts to consider
	      **/
	      ls_insert_fact_inlist (gef_conn[action].sf->PC_end[i]);
	
	      /** 
		  Rimuovo dalla lista dei fatti attualmente supportati 
		  quelli che sono mutex con le precondizioni dell'azione, 
		  perche' genererebbero uno stato inconsistente
		  *
		  Remove the facts mutex with the preconditions of the
		  action from the set of fact supported, because otherwise
		  the state is inconsistent
	      **/
	      remove_mutex_facts_in_bitvect_and_update_num_actions (gef_conn[action].sf->PC_end[i], Hvar.local_bit_vect_facts);
	    }
	  else
	    if(GpG.cri_update_all_facts==1)
	      ls_insert_fact_inlist (gef_conn[action].sf->PC_end[i]);
	}
    }
  
  
  /** 
     Considero come supportati gli effetti dell'azione 
     *
     Consider the effects of the action like supported
  **/
  
  /** 
     at start effects
  **/
  if (gef_conn[action].sf)
    for (i = 0; i < gef_conn[action].sf->num_A_start; i++)
      { 
	/** 
	    Gli effetti numerici sono gia' inseriti in val_max e val_min
	**/
	if (gef_conn[action].sf->A_start[i] < 0)
	  continue;

        /** 
	   Se l'effetto at start e' anche un effetto cancellante at end
	   non lo considero supportato
	   *
	   If the at start effect is also an at end delete effect, then
	   do not consider it like supported
	**/
	if (is_fact_in_delete_effects
	    (action, gef_conn[action].sf->A_start[i]))
	  continue;

	/** 
	    all the at start effects must be true in the new state 
	**/
	if (GET_BIT(Hvar.local_bit_vect_facts, gef_conn[action].sf->A_start[i]) == 0)
	  { 
	    /**
	       Considero vero il fatto supportato da questo effetto additivo 
	       settando il bit corrispondente in local_bit_vect_facts
	       *
	       Consider true the fact supported by this additive effects
	       setting the corresponding bit in local_bit_vect_facts
	    **/
	    SET_BIT (Hvar.local_bit_vect_facts,
		     gef_conn[action].sf->A_start[i]);

	    for(aus_counter=0;aus_counter< gft_conn[gef_conn[action].sf->A_start[i]].num_PC;aus_counter++)
	      {		   
		SET_BIT(To_be_Executed,gft_conn[gef_conn[action].sf->A_start[i]].PC[aus_counter]);
	      }

	    /** 
		Inserisco l'effetto at start nell'insieme dei fatti da considerare 
		*
		Insert the at start effect in the set of facts to consider
	    **/
	    ls_insert_fact_inlist (gef_conn[action].sf->A_start[i]);

	    /** 
		Rimuovo dalla lista dei fatti attualmente supportati 
		quelli che sono mutex con l'effetto at start dell'azione, 
		perche' altrimenti lo stato sarebbe inconsistente
		*
		Remove the facts mutex with the at start effect of the
		action from the set of fact supported, because otherwise
		the state is inconsistent
	    **/
	    remove_mutex_facts_in_bitvect_and_update_num_actions(gef_conn[action].sf->A_start[i], Hvar.local_bit_vect_facts);
	  }
      }

  
  /** 
     at end effects
  **/
  for (i = 0; i < gef_conn[action].num_A; i++)
    { 

       /** 
	    Gli effetti numerici sono gia' inseriti in val_max e val_min
	**/
      if (gef_conn[action].A[i] < 0)
	continue;
      
      /** 
	  all the at end effects must be true in the new state 
      **/
      if (GET_BIT (Hvar.local_bit_vect_facts, gef_conn[action].A[i]) == 0)		{
	/* Considero vero il fatto supportato da questo effetto additivo 
	   settando il bit corrispondente in local_bit_vect_facts
	   *
	   Consider true the fact supported by this additive effects
	   setting the corresponding bit in local_bit_vect_facts
	*/
	SET_BIT (Hvar.local_bit_vect_facts, gef_conn[action].A[i]);

	for(aus_counter=0;aus_counter< gft_conn[gef_conn[action].A[i]].num_PC;aus_counter++)
	  {		   
	    SET_BIT(To_be_Executed,gft_conn[gef_conn[action].A[i]].PC[aus_counter]);
	  }
	
	/** 
	    Inserisco l'effetto at end nella lista dei fatti da considerare 
	    *
	    Insert the at end effect in the set of facts to consider
	**/
	ls_insert_fact_inlist (gef_conn[action].A[i]);

	/** 
	    Rimuovo dalla lista dei fatti attualmente supportati 
	    quelli che sono mutex con l'effetto at end dell'azione, 
	    perche' altrimenti lo stato sarebbe inconsistente
	    *
	    Remove the facts mutex with the at end effect of the
	    action from the set of fact supported, because otherwise
	    the state is inconsistent
	**/
	remove_mutex_facts_in_bitvect_and_update_num_actions (gef_conn[action].A[i], Hvar.local_bit_vect_facts);
      }
    }

 

  /**
     Copia i valori attuali contenuti nel bit vector Hvar.local_bit_vect_facts
     in initial_local_bit_vect_facts che NON VIENE PIU' MODIFICATO
     *
     Copy the actual values containing in bit-array Hvar.local_bit_vect_facts
     in initial_local_bit_vect_facts that it will not be modified
  **/
  memcpy( initial_local_bit_vect_facts,Hvar.local_bit_vect_facts, gnum_ft_block * sizeof (int));


  /* Verifica le preco numeriche vere e rende applicabili le azioni relative*/
 for(i=0;i<gnum_comp_var;i++)
    {
      if(!GET_BIT(Numeric.is_a_Pc,i))
      	continue;
      if(GET_BIT(Hvar.ri_initial_bit_vect_numeric_facts,i))
      	 continue;
      //Per tutte le precondizioni numeriche
      switch (gcomp_var[i].operator)
	{
	case LESS_THAN_OP:
	case LESS_THAN_OR_EQUAL_OP:
	case EQUAL_OP:
	case GREATER_THAN_OP:
	case GREATER_OR_EQUAL_OP:
	 
	  if(Hvar.max_values[i] > 0.5)
	    {
	      /*
	       *Se la precondizione è vera viene settato a 1 il bit relativo del vettore dei fatti numerici veri
	       */
	      if(vectlevel[level]->numeric->values[i]<0.5) 
		{
		  
		  if (Numeric.num_Pc_ef_matrix.bits[i])
		    for(x = 0; x < gnum_ef_block; x++)
		      {
			To_be_Executed[x] = To_be_Executed[x] | get_bit_table_block(Numeric.num_Pc_ef_matrix, i, x);
		      }
		  
		  cri_set_init_numeric_fact(i);
		}
	      
	    }
	   
	 
	  break;
	default:
	  break;
	}

    }

  /** 
      Now recompute the new heuristics for this state
  **/


 memcpy(True_num , Hvar.ri_initial_bit_vect_numeric_facts,gnum_block_compvar*sizeof(int));


 
 /* Se l'azione deve essere considerata conta il numero di precondizioni non supportate*/
  for(i=0;i<gnum_ef_conn;i++)
    if(GET_BIT(To_be_Executed,i))
      num_prec_vector[i]= count_unsatisfied_preconds(i,initial_local_bit_vect_facts)+ count_unsatisfied_num_preconds(i,True_num);
  


      /**  
	   Esamina le azioni di cui il fatto e' precondizione
	   *
	   Check the actions of which the fact is precondition
       **/
  reset_bitarray (To_be_Executed, gnum_ef_block);
      do
	{

	  changed = FALSE;
	 
	  for (i = 0; i < gnum_ef_conn; i++)
	    if(!GET_BIT (applied, i))
	      if(num_prec_vector[i]==0)
		if(gef_conn[i].level>=0)
		  SET_BIT (To_be_Executed, i);

	  for (i = 0; i < gnum_ef_conn; i++)
	    {
	      
	      if (GET_BIT (applied, i))
		continue;
	      /*se l'azione non e' ancora stata applicata... */
	      if (!GET_BIT (To_be_Executed, i))
		continue;
	    	    	 
	      SET_BIT(applied,i);

	     
	      /* A seconda del tipo di euristica calcolo i nuovi valori di raggiungibilita'
	       */ 
	      if(GpG.cri_evaluate_preconditions==COMPUTE_DG_LIST_COST)
		{	
		  /* Utilizzo il piano rilassato in cui considero anche le componenti numeriche.
		     Copio i valori di initial_local_bit_vect_facts in Hvar.ri_supp_bit_vect_facts,initial_local_bit_vect_facts
		     * per rendere disponibili i fatti attualmente supportati nel calcolo dei nuovi valori
		   */
		  memcpy( Hvar.ri_supp_bit_vect_facts,initial_local_bit_vect_facts, gnum_ft_block * sizeof (int));
		  /*compute the cost of the actual action with a relaxed plan where
		   * we insert the action not already applyed by other priors facts
		   */
		  if(Hvar.modifieds_values>0)
		    {
		      memcpy(Hvar.max_values,vectlevel[level+1]->numeric->values,gnum_comp_var*sizeof (float));
		      memcpy(Hvar.min_values,vectlevel[level+1]->numeric->values,gnum_comp_var*sizeof (float));
		    }
		  Hvar.modifieds_values=0;
		  new_cost=cri_predict_cost_relaxed (i, &new_duration, &max_prec_num_actions);
	     
		}
	      else
		{
		  /* Calcolo il nuovo costo facendo il max tra i costi di raggiungibilita'
		     delle precondizioni, considerando anche quelle numeriche
		   */
		  memcpy( Hvar.ri_supp_bit_vect_facts,initial_local_bit_vect_facts, gnum_ft_block * sizeof (int));
		  new_cost=cri_predict_cost_max(i,&max_prec_num_actions);

		  //  new_cost = max_prec_cost + get_action_cost (i,NULL);
	
		  max_prec_num_actions++;
		}
	      
	      /* Controlla se l'azione 'i' puo' diventare un best_increase, decrease o assign
	       */

	      if(gef_conn[i].is_numeric)
		{
		  //ATTENZIONE ri_set_best_for_compvar computazionelmente MOLTO COSTOSA!!
		  changed=changed || ri_set_best_for_compvar(i,True_num,val_max,val_min,num_prec_vector);
		}

	      //new_duration = max_prec_duration + get_action_time (i, level);

	  /* Segnalo che l'azione e' gia' stata considerata andando a settare il bit a 1 nella posizione
	   * corrispondente (el)
	   */

#ifdef __TEST__1

	  printf
	    ("\n Now I consider the action %d  new_cost %.2f prec_cost %.2f name= ",
	     i, new_cost, max_prec_cost);
	  print_op_name (i);
#endif
	  /* Rendo supportati i fatti che sono effetti dell'azione considerata che è a questo
	   * punto applicabile ed assegno i valori di raggiungibilità
	   */
	  /* Effetti additivi at end
	   */
	  for (k = 0; k < gef_conn[i].num_A; k++)
	    {
	    /* Non prendo in considerazione effetti numerici, poiche' li applico alla fine
	     */
	      if (gef_conn[i].A[k] < 0)
		continue;
	     

	      if (!GET_BIT (Hvar.local_bit_vect_facts, gef_conn[i].A[k]))
		for(aus_counter=0;aus_counter< gft_conn[gef_conn[i].A[k]].num_PC;aus_counter++)
		  {
		    if(num_prec_vector[gft_conn[gef_conn[i].A[k]].PC[aus_counter]]==INFINITY)
		      num_prec_vector[gft_conn[gef_conn[i].A[k]].PC[aus_counter]]= count_unsatisfied_preconds(gft_conn[gef_conn[i].A[k]].PC[aus_counter],Hvar.local_bit_vect_facts)+
			count_unsatisfied_num_preconds(gft_conn[gef_conn[i].A[k]].PC[aus_counter],True_num);
		    
		    if(GpG.temporal_plan)
		      {  if(is_fact_in_preconditions_end(gft_conn[gef_conn[i].A[k]].PC[aus_counter],
							 gef_conn[i].A[k])&&
			    is_fact_in_additive_effects_start(gft_conn[gef_conn[i].A[k]].PC[aus_counter],
							      gef_conn[i].A[k]))
			continue;    
		      
		      if(is_fact_in_preconditions_overall(gft_conn[gef_conn[i].A[k]].PC[aus_counter],
							  gef_conn[i].A[k])&&
			 is_fact_in_additive_effects_start(gft_conn[gef_conn[i].A[k]].PC[aus_counter],
								 gef_conn[i].A[k]))
			continue;
		      }
		    num_prec_vector[gft_conn[gef_conn[i].A[k]].PC[aus_counter]]--;
		    if(num_prec_vector[gft_conn[gef_conn[i].A[k]].PC[aus_counter]]==0)
		      {
			changed=TRUE;
			SET_BIT (To_be_Executed, gft_conn[gef_conn[i].A[k]].PC[aus_counter]);
		      }
		    
		  }



		  /* Rendo il fatto attualmente supportato
		   */
		  SET_BIT(  Hvar.local_bit_vect_facts, gef_conn[i].A[k]);
		  
		  
		  /* Se il fatto non è stato ancora preso in considerazione o ho valori
		   * massimi che superano gli attuali aggiorno i  valori di
		   * raggiungibilita'
		   * Utilizzo Hvar.bit_vect_facts poiche' questo definisce i fatti che vengono resi veri durante il processo di raggiungibilita' e viene modificato  da ls_insert_fact_inlist (gef_conn[el].A[k]);
		   */


		  if ((GET_BIT (Hvar.bit_vect_facts, gef_conn[i].A[k]) == 0)
		      || (Hvar.ri_num_actions_of_facts[gef_conn[i].A[k]] >
			  max_prec_num_actions) ||  Hvar.ri_best_act_for_facts[gef_conn[i].A[k]]<0 )
		    {



#ifdef __TEST__RIINS
		      /* Se sono cambiati dei valori e' possibile riconsiderare nuovamente l'azione
		       */
		    if( Hvar.ri_num_actions_of_facts[gef_conn[i].A[k]] >
			max_prec_num_actions)
		      {

			for(aus_counter=0;aus_counter< gft_conn[gef_conn[i].A[k]].num_PC;aus_counter++)
			  {
			    RESET_BIT(applied,i);
			    changed=TRUE;
			  }
		      }

#endif

#ifdef __TEST__1
		    printf ("\n\n +-+-+-OLD cost of fact  %d : ",
			    gef_conn[i].A[k]);
		    print_ft_name (gef_conn[i].A[k]);
		    printf (" cost %.2f duration %.2f num_actions %d",
			    Hvar.ri_cost_of_facts[gef_conn[i].A[k]],
			    Hvar.ri_duration_of_facts[gef_conn[i].A[k]],
			    Hvar.ri_num_actions_of_facts[gef_conn[i].A[k]]);
#endif

		    ls_insert_fact_inlist (gef_conn[i].A[k]);
		    Hvar.ri_cost_of_facts[gef_conn[i].A[k]] = new_cost;
		    Hvar.ri_duration_of_facts[gef_conn[i].A[k]] =
		      new_duration;
		    Hvar.ri_num_actions_of_facts[gef_conn[i].A[k]] =
		      max_prec_num_actions;
		    Hvar.ri_best_act_for_facts[gef_conn[i].A[k]] = i;

#ifdef __TEST__1
		    printf ("\n\n ++++++Set cost of facts %d : ",
			    gef_conn[i].A[k]);
		    print_ft_name (gef_conn[i].A[k]);
		    printf (" cost %.2f duration %.2f num_actions %d",
			    new_cost, new_duration,
			    Hvar.ri_num_actions_of_facts[gef_conn[i].A[k]]);
#endif
		    }
		
#ifdef __TEST__1
		else
		  {
		    printf ("\n  Eff %d  already set, cost %.2f name: ",
			    gef_conn[i].A[k],
			    Hvar.ri_cost_of_facts[gef_conn[i].A[k]]);
		    print_ft_name (gef_conn[i].A[k]);

		  }
#endif


	    }
	    

	  // effetti additivi AT_START
	  if (gef_conn[i].sf)
	    for (k = 0; k < gef_conn[i].sf->num_A_start; k++)
	     /* Non prendo in considerazione effetti numerici
	     */
	      if (gef_conn[i].sf->A_start[k] >= 0)
		{
		 


		  if (GET_BIT (Hvar.local_bit_vect_facts, gef_conn[i].A[k]) == 0)
		    for(aus_counter=0;aus_counter< gft_conn[gef_conn[i].sf->A_start[k]].num_PC;aus_counter++)
		      { 
			/* Se trovo un'azione che ha il fatto come preco calcolo il numero
			   delle sue precondizioni non supportate
			*/
			if(num_prec_vector[gft_conn[gef_conn[i].sf->A_start[k]].PC[aus_counter]]==INFINITY)
			  num_prec_vector[gft_conn[gef_conn[i].sf->A_start[k]].PC[aus_counter]]= 
			    count_unsatisfied_preconds(gft_conn[gef_conn[i].sf->A_start[k]].PC[aus_counter],Hvar.local_bit_vect_facts)+ 
			    count_unsatisfied_num_preconds(gft_conn[gef_conn[i].sf->A_start[k]].PC[aus_counter],True_num);
			
			if(GpG.temporal_plan)
			  {
			    if(is_fact_in_preconditions_end(gft_conn[gef_conn[i].sf->A_start[k]].PC[aus_counter],
							    gef_conn[i].sf->A_start[k])&&
			       is_fact_in_additive_effects_start(gft_conn[gef_conn[i].sf->A_start[k]].PC[aus_counter],
								 gef_conn[i].A[k]))
			      continue;    
			    
			    if(is_fact_in_preconditions_overall(gft_conn[gef_conn[i].sf->A_start[k]].PC[aus_counter],
								gef_conn[i].sf->A_start[k])&&
			       is_fact_in_additive_effects_start(gft_conn[gef_conn[i].sf->A_start[k]].PC[aus_counter],
								 gef_conn[i].sf->A_start[k]))
			      continue;
			  }
                        num_prec_vector[gft_conn[gef_conn[i].sf->A_start[k]].PC[aus_counter]]--;
			if(num_prec_vector[gft_conn[gef_conn[i].sf->A_start[k]].PC[aus_counter]]==0)
			  {
			    changed=TRUE;
			    SET_BIT (To_be_Executed, gft_conn[gef_conn[i].sf->A_start[k]].PC[aus_counter]);
			  }
		      }

		  /* Rendo il fatto attualmente supportato
		   */
		  SET_BIT(  Hvar.local_bit_vect_facts, gef_conn[i].sf->A_start[k]); 



		  /* Se il fatto non è stato ancora preso in considerazione o ho valori
		   * massimi che superano gli attuali aggiorno i  valori di
		   * raggiungibilita'
		   */
		  if (GET_BIT
		      (Hvar.bit_vect_facts, gef_conn[i].sf->A_start[k]) == 0
		      || Hvar.ri_num_actions_of_facts[gef_conn[i].sf->
						      A_start[k]] >max_prec_num_actions||  
		      Hvar.ri_best_act_for_facts[gef_conn[i].sf->A_start[k]]<0)
		      
		    {
		      if (is_fact_in_delete_effects
			  (i, gef_conn[i].sf->A_start[k]))
			continue;
#ifdef __TEST__RIINS

		    if( Hvar.ri_num_actions_of_facts[gef_conn[i].sf->A_start[k]] >
			max_prec_num_actions)
		      {

			for(aus_counter=0;aus_counter< gft_conn[gef_conn[i].sf->A_start[k]].num_PC;aus_counter++)
			  {
			    RESET_BIT(applied,i);
			    changed=TRUE;
			  }
		      }

#endif
		    



#ifdef __TEST__1
		      printf ("\n\n +-+-+-OLD cost of fact  %d : ",
			      gef_conn[i].sf->A_start[k]);
		      print_ft_name (gef_conn[i].sf->A_start[k]);
		      printf (" cost %.2f duration %.2f num_actions %d",
			      Hvar.ri_cost_of_facts[gef_conn[i].sf->
						   A_start[k]],
			      Hvar.ri_duration_of_facts[gef_conn[i].sf->
						       A_start[k]],
			      Hvar.ri_num_actions_of_facts[gef_conn[i].sf->
							  A_start[k]]);
#endif
		      ls_insert_fact_inlist (gef_conn[i].sf->A_start[k]);
		      Hvar.ri_cost_of_facts[gef_conn[i].sf->A_start[k]] =
			new_cost;
		      Hvar.ri_duration_of_facts[gef_conn[i].sf->A_start[k]] =
			new_duration;
		      Hvar.ri_num_actions_of_facts[gef_conn[i].sf->
						  A_start[k]] =
			max_prec_num_actions;
		      Hvar.ri_best_act_for_facts[gef_conn[i].sf->A_start[k]] =
			i;
#ifdef __TEST__1
		      printf ("\n\n ++++++Set cost of facts %d : ",
			      gef_conn[i].sf->A_start[k]);
		      print_ft_name (gef_conn[i].sf->A_start[k]);
		      printf (" cost %.2f duration %.2f num_actions %d",
			      new_cost, new_duration,
			      Hvar.ri_num_actions_of_facts[gef_conn[i].sf->
							  A_start[k]]);
#endif
		    }
#ifdef __TEST__1
		  else
		    {
		      printf ("\n  Eff %d  already set, cost %.2f name: ",
			      gef_conn[i].sf->A_start[k],
			      Hvar.ri_cost_of_facts[gef_conn[i].sf->
						   A_start[k]]);
		      print_ft_name (gef_conn[i].sf->A_start[k]);

		    }
#endif


		}
	
	    }			//ciclo su tutte le azioni




	}
      while(changed);

      //memcpy(Hvar.ri_bit_vect_numeric_facts,True_num,gnum_block_compvar* sizeof(int));
       // devo reimpostare i fatti di quel livello    
}


/* Determina i nuovi best_increase, decrease, assign considerando gli effetti dell'azione 'action, aggiungendo le preco relative
   all'insieme dei fatti numerici veri aggiornando il numero di precondizioni non supportate delle azioni che hanno questi fatti come precondizioni
*/

Bool ri_set_best_for_compvar(int action, int * True_num,float *vmax, float *vmin,int *num_prec_vector)
{

  int y,j,k,x,aus,ll,l,temp;
  int h,hh,aus2,temp2;
  DescNumEff *numeric_effect;
  DescNumEff *aus_numeric_effect;
  Bool changed;

  changed=FALSE;

  for(j=0;j<gef_conn[action].num_numeric_effects;j++)
 
    {
      numeric_effect = &gef_conn[action].numeric_effects[j];
     
      switch (gcomp_var_effects[numeric_effect->index].operator)
	{
	case INCREASE_OP:
	  /*
	   * Se il best-increase non è stato ancora settato viene settato, altrimenti viene confrontato il valore 
	   * del termine a destra dei due, il maggiore diventa/resta il best-increase
	   */
	  for (ll = 0, l = 0; l < gnum_block_compvar; l++, ll += 32)
	    {
	      temp = Numeric.is_a_Pc[l];
	      aus = 32;
	      while (temp)
		{
		  aus--;
		  if (temp & FIRST_1)
		    {
		      y = ll + aus;

		      if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],y))
			{	  
			  
			  if(gcomp_var[y].operator==LESS_THAN_OR_EQUAL_OP||gcomp_var[y].operator==LESS_THAN_OP)		      
			    continue;
			  
			  if(Hvar.ri_best_increase_for_compvar[y]<0)
			    {
			      
			      if(!GET_BIT(True_num,y))
				{

				  if (Numeric.num_Pc_ef_matrix.bits[y])
				    for (hh = 0, h = 0; h < gnum_ef_block; h++, hh += 32)
				      {
					temp2 = get_bit_table_block(Numeric.num_Pc_ef_matrix, y, h) ;
					aus2 = 32;
					while (temp2)
					  {
					    aus2--;
					    if (temp2 & FIRST_1)
					      {
						x = hh + aus2;
						
						if(num_prec_vector[x]==INFINITY)
						  num_prec_vector[x] = 
						    count_unsatisfied_preconds(x, Hvar.local_bit_vect_facts)+ count_unsatisfied_num_preconds(x,True_num);
						
						num_prec_vector[x]--;
						if(num_prec_vector[x]==0)
						  changed=TRUE;
					      }
					    temp2 <<= 1;
					    
					  }
				      }
				  
				  SET_BIT(True_num,y);  
				  
				}
			      
			      
			      if(gcomp_var[y].operator==EQUAL_OP)
				{
				  Hvar.ri_best_increase_for_compvar[y]=action;
				}
			      else
				{			      
				  cri_insert_numeric_ftcost (y, action, numeric_effect->index,INCREASE_OP);
				  
				}
			    }
			    
			  else
			    {
			      for(k=0;k<gef_conn[Hvar.ri_best_increase_for_compvar[numeric_effect->lval]].num_numeric_effects;k++)
				{
				  if(k==gef_conn[Hvar.ri_best_increase_for_compvar[y]].num_numeric_effects)
				    break;
				  
				  aus_numeric_effect=&gef_conn[Hvar.ri_best_increase_for_compvar[y]].numeric_effects[k];
				  if(numeric_effect->lval == aus_numeric_effect->lval)			  
				    {
				      if(gcomp_var[y].operator==EQUAL_OP)
					{
					  if(vmax[gcomp_var_effects[numeric_effect->index].second_op] > vmax[gcomp_var_effects[aus_numeric_effect->index].second_op])
					    Hvar.ri_best_increase_for_compvar[y]=action;
					}
				      else
					{
					  cri_insert_numeric_ftcost (y, action, numeric_effect->index,INCREASE_OP);
					}
				  				
				    }
				  
				}			
			    }
			}
		    }
		  temp <<= 1;
		}
	    }
		      

		 
		      
	  break;
	  
	case DECREASE_OP:
	  /*
	   * Se il best-decrease non è stato ancora settato viene settato, altrimenti viene confrontato il valore 
	   * del termine a destra dei due, il maggiore diventa/resta il best-decrease
	   */
	  for (ll = 0, l = 0; l < gnum_block_compvar; l++, ll += 32)
	    {
	      temp = Numeric.is_a_Pc[l];
	      aus = 32;
	      while (temp)
		{
		  aus--;
		  if (temp & FIRST_1)
		    {
		      y = ll + aus;
			  
		      if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],y))
			{
		  
			  if(gcomp_var[y].operator==GREATER_OR_EQUAL_OP||gcomp_var[y].operator==GREATER_THAN_OP)		      
			    continue;
			  
			  if(Hvar.ri_best_decrease_for_compvar[y]<0)
			    {
			      
			      if(!GET_BIT(True_num,y))
				{

				  if (Numeric.num_Pc_ef_matrix.bits[y])
				    for (hh = 0, h = 0; h < gnum_ef_block; h++, hh += 32)
				      {
					temp2 = get_bit_table_block(Numeric.num_Pc_ef_matrix, y, h) ;
					aus2 = 32;
					while (temp2)
					  {
					    aus2--;
					    if (temp2 & FIRST_1)
					      {
						x = hh + aus2;
						
						if(num_prec_vector[x]==INFINITY)
						  num_prec_vector[x]= count_unsatisfied_preconds(x,Hvar.local_bit_vect_facts)+ count_unsatisfied_num_preconds(x,True_num);
						
						num_prec_vector[x]--;
						if(num_prec_vector[x]==0)
						  changed=TRUE;
					      }
					    
					    temp2 <<= 1;
					  }
				      }
				  
				  SET_BIT(True_num,y);  
				  
				}
			      
			      
			      if(gcomp_var[y].operator==EQUAL_OP)
				{
				  Hvar.ri_best_decrease_for_compvar[y]=action;
				}
			      else
				{			      
				  cri_insert_numeric_ftcost (y, action, numeric_effect->index,DECREASE_OP);
				  
				}
			    }
			    
			  else
			    {
			      for(k=0;k<gef_conn[Hvar.ri_best_decrease_for_compvar[numeric_effect->lval]].num_numeric_effects;k++)
				{
				  if(k==gef_conn[Hvar.ri_best_decrease_for_compvar[y]].num_numeric_effects)
				    break;
				  
				  aus_numeric_effect=&gef_conn[Hvar.ri_best_decrease_for_compvar[y]].numeric_effects[k];
				  if(numeric_effect->lval == aus_numeric_effect->lval)			  
				    {
				      if(gcomp_var[y].operator==EQUAL_OP)
					{
					  if(vmax[gcomp_var_effects[numeric_effect->index].second_op] < vmax[gcomp_var_effects[aus_numeric_effect->index].second_op])
					    Hvar.ri_best_decrease_for_compvar[y]=action;
					}
				      else
					{
					  cri_insert_numeric_ftcost (y, action, numeric_effect->index,DECREASE_OP);
					}
				  				
				    }
				  
				}			
			    }
			}
		    }
		  temp <<= 1;
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
	    for (ll = 0, l = 0; l < gnum_block_compvar; l++, ll += 32)
	      {
		temp = Numeric.is_a_Pc[l];
		aus = 32;
		while (temp)
		  {
		    aus--;
		    if (temp & FIRST_1)
		    {
		      y = ll + aus;
		      if(GET_BIT(Numeric.Affects_Matrix[numeric_effect->lval],y))	
			{
			  if(Hvar.ri_best_assign_for_compvar[y]<0)
			    {
			      if(!GET_BIT(True_num,y))
				{

				  if (Numeric.num_Pc_ef_matrix.bits[y])
				    for (hh = 0, h = 0; h < gnum_ef_block; h++, hh += 32)
				      {
					temp2 = get_bit_table_block(Numeric.num_Pc_ef_matrix, y, h) ;
					aus2 = 32;
					while (temp2)
					  {
					    aus2--;
					    if (temp2 & FIRST_1)
					      {
						x = hh + aus2;
						
						if(num_prec_vector[x]==INFINITY)
						  num_prec_vector[x]= count_unsatisfied_preconds(x,Hvar.local_bit_vect_facts)+ count_unsatisfied_num_preconds(x,True_num);
						
						num_prec_vector[x]--;
						if(num_prec_vector[x]==0)
						  changed=TRUE;
					      }
					    temp2 <<= 1;
					  }
					
				      }
				  SET_BIT(True_num,y);  
				}
			      Hvar.ri_best_assign_for_compvar[y]=action;
			    }
	
			  else
			    {
			      for(k=0;k<gef_conn[Hvar.ri_best_assign_for_compvar[numeric_effect->lval]].num_numeric_effects;k++)
				{
				  if(k==gef_conn[Hvar.ri_best_assign_for_compvar[y]].num_numeric_effects)
				    break;
				  aus_numeric_effect=&gef_conn[Hvar.ri_best_assign_for_compvar[y]].numeric_effects[k];
				  if(numeric_effect->lval == aus_numeric_effect->lval)
				    {
				      if(vmax[gcomp_var_effects[numeric_effect->index].second_op] > vmax[gcomp_var_effects[aus_numeric_effect->index].second_op])	
					Hvar.ri_best_assign_for_compvar[y]=action;
			    
				      
				      if(vmin[gcomp_var_effects[numeric_effect->index].second_op] < vmin[gcomp_var_effects[aus_numeric_effect->index].second_op])
					Hvar.ri_best_assign_for_compvar[y]=action;
				    }
				  
				}
			      
			    }
			}
		    }
		    temp <<= 1;
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
  
  return changed;  
}


/* Decrementa il numero di precondizioni da supportare per azioni le cui preco numeriche sono state rese vere rispetto a vmax e vmin*/

Bool ri_verify_num_preconditions( int * True_num,int *num_Pc_relevant_pos ,int *num_Pc_relevant_neg,
			      int *relevant_vars ,float *vmax ,float *vmin,int *num_prec_vector)
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
	  if(ri_eval_comp_var (&(gcomp_var[i]),i ,vmax,vmin,TRUE) > 0.5)
	    {
	     
		  SET_BIT(True_num,i);
		  for(j=0;j<gnum_ef_conn;j++)
		    {
		      if(check_bit_in_bit_table(Numeric.num_Pc_ef_matrix, i, j))
			{
			  num_prec_vector[j]--;
			  if(num_prec_vector[j]==0)
			    changed=TRUE;
			}
		      
		    }
		  sub_tested_vars_for_cvar (i,num_Pc_relevant_pos ,num_Pc_relevant_neg,relevant_vars, TRUE);
		 		      
		  
		
	    }
	  /*
	   * Se invece non è supportata ed è una relazione di < o <= non posso raggiungere la condizione di
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
	  if(ri_eval_comp_var (&(gcomp_var[i]),i ,vmax,vmin,TRUE) > 0.5)
	    {
	   
		  SET_BIT(True_num,i);
		  for(j=0;j<gnum_ef_conn;j++)
		    {
		      if(check_bit_in_bit_table(Numeric.num_Pc_ef_matrix, i, j))
			{
			  num_prec_vector[j]--;
			  if(num_prec_vector[j]==0)
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

	  if(ri_eval_comp_var (&(gcomp_var[i]),i ,vmax,vmin,TRUE) > 0.5)
	    {
	      
		  SET_BIT(True_num,i);
		  for(j=0;j<gnum_ef_conn;j++)
		    {
		      if(check_bit_in_bit_table(Numeric.num_Pc_ef_matrix, i, j))
			{
			  num_prec_vector[j]--;
			  if(num_prec_vector[j]==0)
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
	default:
	  break;
	  
	  
	}
      
      
    }


  return changed;

}








void set_init_computed_dg_costs ()
{
   int i;
    static int level_init=-1; 
  dg_inform ** loc_dg_facts_array;

  //#ifdef __TEST_REACH__
  dg_num_inform ** loc_dg_num_facts_array;
  //#endif

  GpG.first_execution_cri++;

    loc_dg_facts_array=Hvar.init_facts_array;

    //#ifdef __TEST_REACH__
    loc_dg_num_facts_array= Hvar.init_num_facts_array;
    //#endif

  for ( i = 0; i < gnum_ft_conn; i++)
      {
         update_dg_fact_list(i, &level_init, Hvar.ri_num_actions_of_facts[i], Hvar.ri_best_act_for_facts[i],Hvar.ri_duration_of_facts[i] ,Hvar.ri_cost_of_facts[i],-1 );

      }

  //#ifdef __TEST_REACH__
  for ( i = 0; i < gnum_comp_var; i++)
    {
      if(!GET_BIT(Numeric.is_a_Pc,i))
	continue;
      loc_dg_num_facts_array[i]  = update_num_dg_fact_list(i, &level_init, Hvar.ri_num_actions_of_numeric_facts[i], Hvar.ri_best_increase_for_compvar[i],Hvar.ri_best_decrease_for_compvar[i],
							   Hvar.ri_best_assign_for_compvar[i],Hvar.ri_duration_of_numeric_facts[i] ,Hvar.ri_cost_of_numeric_facts[i] );
      
    }
  //#endif

 if(DEBUG5)
  print_cri_computed_costs (-1);

}






void remove_mutex_facts_in_bitvect_and_update_num_actions (int fact, int *bit_vect)
{
  int i, k, b_vect, temp1;

  for (i = 0; i < gnum_ft_block; i++)
    {
      b_vect=bit_vect[i];
      b_vect &= ~gft_conn[fact].ft_exclusive_vect[i];

      if(b_vect==bit_vect[i])
	continue; // Nothing to do for this step

      temp1=bit_vect[i] & (~b_vect);
      k = 32;
      while (temp1)
	{
	  k--;
	  if (temp1 & FIRST_1)
	    {
	      Hvar.ri_num_actions_of_facts[(i*32 + k)]=MAXINT;
#ifdef __TEST__
	      printf("\n Reset Fact %d step %d - name", i*32 + k, GpG.count_num_try);
	      print_ft_name(i*32 + k);

#endif

  
	    }

	  temp1 <<= 1;

	}
      bit_vect[i]=b_vect;
	
    }
}





void set_computed_dg_costs (int level)
{
  int i, j, j1, k, temp;
  int act_pos;


 if ( vectlevel[level]->dg_facts_array == NULL )
    {
      vectlevel[level]->dg_facts_array = (dg_inform_list *) calloc (gnum_ft_conn, sizeof (dg_inform_list));
#ifdef __TEST_REACH__
      vectlevel[level]->dg_num_facts_array = (dg_num_inform_list *) calloc (gnum_comp_var, sizeof (dg_num_inform_list));
#endif
      memset (vectlevel[level]->dg_facts_array, 0,     gnum_ft_conn * sizeof (dg_inform_list));
      vectlevel[level]->local_bit_vect_facts = (int *) calloc (gnum_ft_block, sizeof (int));
      memset (vectlevel[level]->local_bit_vect_facts, 0 , gnum_ft_block* sizeof (int));
    }
 act_pos=GET_ACTION_POSITION_OF_LEVEL(level);

  for (j1 = j = 0; j < gnum_ft_conn; j1++, j += 32)
    {

     
	temp = Hvar.bit_vect_facts[j1]; // Hvar.local_bit_vect_facts[j];

	if(GpG.cri_insertion_add_mutex)
	  temp |= CONVERT_ACTION_TO_VERTEX(act_pos)->ft_exclusive_vect[j1];	


	k = 32;
	while (temp)
	  {
	    k--;

	    if (temp & FIRST_1)
	      {
		i = j + k;


		if (i >= gnum_ft_conn)
		  continue;

		if (Hvar.ri_num_actions_of_facts[i] > 0
		    || vectlevel[level]->fact[i].w_is_true > 0)
		  {


		      update_dg_fact_list(i, &vectlevel[level]->level, Hvar.ri_num_actions_of_facts[i], Hvar.ri_best_act_for_facts[i],Hvar.ri_duration_of_facts[i] ,Hvar.ri_cost_of_facts[i],-1 );


#ifdef __TEST__
		    if (DEBUG3)
		      {
			printf ("\n Set cost of fact %s level %d :",
				print_ft_name_string (i, temp_name), level);

			printf
			  ("\n cost %.2f duration %.2f num_actions %d totcost %.2f best_act %s pos %d",
			   vectlevel[level]->dg_facts_array[i]->cost,
			   vectlevel[level]->dg_facts_array[i]->duration,
			   vectlevel[level]->dg_facts_array[i]->num_actions,
			   vectlevel[level]->dg_facts_array[i]->totcost,
			   print_op_name_string (vectlevel[level]->
						 dg_facts_array[i]->best_act,
						 temp_name),
			   vectlevel[level]->dg_facts_array[i]->best_act);
		      }
#endif
		    
		      
		  }
	      }
	    temp <<= 1;
	  }
      }
  //  memcpy (vectlevel[level]->local_bit_vect_facts, Hvar.bit_vect_facts,
  //	  gnum_ft_block * sizeof (int));
    
   
  vectlevel[level]->is_cri_computed=TRUE;

}






void reset_computed_dg_costs (int level)
{
  int i, j, k, j1, temp;

 if( vectlevel[level]->is_cri_computed==FALSE )
   return;

  for (j1 = j = 0; j < gnum_ft_conn; j1++, j += 32)
    {
      temp = vectlevel[level]->local_bit_vect_facts[j1];
      if(temp)
        vectlevel[level]->local_bit_vect_facts[j1] = 0;
      k = 32;
      while (temp)
	{
	  k--;

	  if (temp & FIRST_1)
	    {
	      i = j + k;

	      if (i >= gnum_ft_conn)
		continue;

	      delete_dg_fact_list(i, &vectlevel[level]->level);

	      vectlevel[level]->dg_facts_array[i] = NULL;
	    }
	  temp <<= 1;
	}
    }

#ifdef __TEST__
  for(i=0; i< gnum_ft_conn; i++)
    if(vectlevel[level]->dg_facts_array[i])
      printf("\n dg for fact %d not null", i);
#endif


if(  vectlevel[level]->dg_num_facts_array!=NULL)
  for (j = 0; j <gnum_comp_var; j++)
    {
      if(vectlevel[level]->dg_num_facts_array[j]!=NULL)
	{
	  free_dg_num_inform(vectlevel[level]->dg_num_facts_array[j]);
	  vectlevel[level]->dg_num_facts_array[j]=NULL;
	}
      
    }

 vectlevel[level]->is_cri_computed=FALSE;

}



dg_inform_list get_level_dg_inform (int level, int fact)
{

  return vectlevel[level]->dg_facts_array[fact];

}



/**
 * Nome: cri_update_for_fact
 * Scopo: aggiorna i valori di raggiungibilità modificati a seguito 
 * dell'inserimento di una azione ad un livello precedente di quello
 * corrente (level) che rende vero il fatto (orig_fact)
 * Funzioni chiamate: ls_insert_fact_inlist
 *                    remove_mutex_facts_in_bitvect_and_update_num_actions
 * Chiamata da:??
 *
 * Name:  cri_update_for_fact
 * Purpose: update the reachability information modified by the insertion
 * of an action  at Level(action)< level that makes supported orig_fact
 * Functions used:  ls_insert_fact_inlist
 *                    remove_mutex_facts_in_bitvect_and_update_num_actions
 * Called by: ??
 **/

void  cri_update_for_fact (int orig_fact, int level)
{

  dg_inform_list loc_dg_cost;

  static int *initial_local_bit_vect_facts=NULL;
  int i, j, k, el=0, fact_pos, skip = FALSE, skip_no_up;
  float max_prec_cost, max_prec_duration, new_cost, new_duration;
  int max_prec_num_actions=0, num_facts_define_cost = -1;
  int action, result, num_iter=0;

  if( GpG.cri_update_iterations<=0 )
    return;

  if(GET_ACTION_POSITION_OF_LEVEL(level)<0 || vectlevel[level]->is_cri_computed==FALSE)
    return;


  action=GET_ACTION_POSITION_OF_LEVEL(level);

  max_prec_cost=0.0;
  max_prec_duration=0.0;
  new_cost=0.0;
  new_duration=0.0;

#ifdef __TEST_UPD__
  printf
    ("\n\n\n ######\n  FACT %d  of level %d name= ",
     orig_fact, level);
  print_ft_name (orig_fact);
  printf ("\n");
  printf("Action of level ");
  print_op_name(GET_ACTION_POSITION_OF_LEVEL(level));

#endif



  if(is_fact_in_preconditions(action,orig_fact) || is_fact_in_preconditions_overall(action,orig_fact) ||is_fact_in_preconditions_end (action,orig_fact))
    {

#ifdef __TEST_UPD__
      printf("\n Fact is a precondition of the action in the current level ");
#endif
      return;

    }


  if( ARE_MUTEX_FT_EF(orig_fact ,action) ) 
     {
 
#ifdef __TEST_UPD__     
       printf("\n Action and orig_fact mutex");
#endif
       return;
     }  



  GpG.cri_initial_or_update=2; /** Imposto il valore per calcolo info raggiungilita' dovute al fatto esaminato */ 
  GpG.cri_update_level=level;

  /**
     Resetta i parametri già instanziati
     *
     Reset the instantiated parameters 
  **/

  reset_bitarray (Hvar.local_bit_vect_facts, gnum_ft_block);
  reset_bitarray (Hvar.local_bit_vect_actions, gnum_ef_block);

  reset_bitarray (Hvar.bit_vect_facts, gnum_ft_block);
  reset_bitarray (Hvar.bit_vect_actions, gnum_ef_block);

  Hvar.num_actions_define_cost = 0;
  Hvar.num_facts_define_cost = 0;
  Hvar.cost_actions_define_cost=0.0;
  Hvar.time_actions_define_cost=0.0;


  reset_bitarray (Hvar.ri_bit_vect_actions, gnum_ef_block);

  Hvar.ri_num_actions_define_cost = 0;
  Hvar.ri_num_facts_define_cost = 0;
  Hvar.ri_cost_actions_define_cost=0.0;
  Hvar.ri_time_actions_define_cost=0.0;



  if(initial_local_bit_vect_facts==NULL)
    initial_local_bit_vect_facts= alloc_vect (gnum_ft_block);

  /** 
     Setta il bit-vector local_bit_vect_facts con i 
     fatti veri prima di applicare l'azione
     *
     Set bit-array local_bit_vect_facts with the facts that
     are true before the applications of the action
  **/
  memcpy( Hvar.local_bit_vect_facts, vectlevel[level+1]->fact_vect,gnum_ft_block*sizeof(int)); 



  SET_BIT (Hvar.local_bit_vect_facts, orig_fact);
  
  /** 
      Inserisco orig_fact nell'insieme dei fatti da considerare 
      *
      Insert orig_fact in the set of facts to consider
  **/
  ls_insert_fact_inlist (orig_fact);

  /** 
      Rimuovo dalla lista dei fatti attualmente supportati 
      quelli che sono mutex con orig_fact, 
      perche' altrimenti lo stato sarebbe inconsistente
      *
      Remove the facts mutex with orig_fact 
      from the set of fact supported, because otherwise
      the state is inconsistent
  **/
  remove_mutex_facts_in_bitvect_and_update_num_actions(orig_fact, Hvar.local_bit_vect_facts);
	


  /**
     Copia i valori attuali contenuti nel bit vector Hvar.local_bit_vect_facts
     in initial_local_bit_vect_facts che NON VIENE PIU' MODIFICATO
     *
     Copy the actual values containing in bit-array Hvar.local_bit_vect_facts
     in initial_local_bit_vect_facts that it will not be modified
  **/
  memcpy( initial_local_bit_vect_facts,Hvar.local_bit_vect_facts, gnum_ft_block * sizeof (int));


  /** 
      Now recompute the new heuristics for this state
  **/
  i=0;

  while(num_iter<GpG.cri_update_iterations)
    {

      if(num_facts_define_cost==Hvar.num_facts_define_cost)
	break;

      num_facts_define_cost=Hvar.num_facts_define_cost;

      num_iter++;

  for (; i < num_facts_define_cost; i++)
    {
      fact_pos = Hvar.list_ft_define_cost[i];


#ifdef __TEST_UPD__
      printf ("\n\n\n------ UPDATE Now consider Fact %d   ", fact_pos);
      print_ft_name (fact_pos);
      if( gft_conn[fact_pos].num_PC<=0)
	{
	  printf("\nFact %d Step %d, num add actions %d, name", fact_pos, GpG.count_num_try, gft_conn[fact_pos].num_PC );
	  print_ft_name (fact_pos);
	}
#endif

      /**  
	   Esamina le azioni di cui il fatto e' precondizione
	   *
	   Check the actions of which the fact is precondition
       **/
      for (j = 0; j < gft_conn[fact_pos].num_PC; j++)
	{

	  el = gft_conn[fact_pos].PC[j];

	  /** 
	     Se l'azione ha indice negativo (non accettabile) salta
	     *
	     If the action has negative index (not acceptable), then skip it
	  **/
	  if (el < 0)
	    continue;

#ifdef __TEST_UPD__
	  printf ("\n -------------------------------");
	  printf ("\n  Action %d  name= ", el);
	  print_op_name (el);
	  printf (" has fact %d as precondition  ", fact_pos);
	  print_ft_name (fact_pos);
#endif

	  /**
	     local_bit_vect_actions e' il bit-vector che mi permette 
	     di sapere se l'azione di indice el e' stata precedentemente 
	     esaminata per non eseguire operazioni inutili
	     *
	     local_bit_vect_actions is a bit-array that allow to know
	     if the action of index el was previuoly examined in order
	     to avoid useless operations
	  **/
	  if (GET_BIT (Hvar.local_bit_vect_actions, el)) // check if I have previously examined the action
	    {
#ifdef __TEST_UPD__
	      printf ("\nAction previously examined");
#endif
	      continue;
	    }

	  /* 
	     Se l'azione non è stata precedentemente esaminata
	     *
	     If the action was not previoulsy examined
	   */
	  else
	    {
 /*
      skip determina se l'azione ha precondizioni non supportabili
	
      skip_no_up viene utilizzato per determinare sealmeno una delle
	 precondizioni dell'azione esaminata ha almeno una precondizione con 
	 informazioni di raggiungibilita' influenzate dall'azione 
	 nell'action subgraph al livello corrente
		    
 */
	      skip  = FALSE;
	      skip_no_up = TRUE;
	      
	      max_prec_num_actions = 0;
	      max_prec_duration = max_prec_cost = 0.0;


	      /**
		 Precondizioni AT_START, controllo che siano supportate 
		 altrimenti salto l'azione poichè attualmente non è applicabile
		 *
		 Check if the precondition at start is supported,
		 otherwise skip the action, because is now not applicable
	      **/
	      for (k = 0; k < gef_conn[el].num_PC; k++)	
		{
		/**
		   if its preconditions are supported or previously computed, 
		   then set the additive effects of el
		**/
		
		  /** 
		     Non considera precondizioni numeriche
		     *
		     Do not consider numeric preconditions
		  **/
		  if (gef_conn[el].PC[k] < 0)
		    continue;
		 
		  
		  /**  
		     The precondition is not supported and we have 
		     not previously computed its cost 
		  **/

		  if (  GET_BIT (vectlevel[level]->local_bit_vect_facts, gef_conn[el].PC[k])==0 &&  GET_BIT (Hvar.local_bit_vect_facts, gef_conn[el].PC[k])==0  )
			{
#ifdef __TEST_UPD__
			  printf ("\n Break, Prec %d not supported ",
				  gef_conn[el].PC[k]);
			  print_ft_name (gef_conn[el].PC[k]);
#endif
			  skip = TRUE;
			  break;
			}
		      else
			{
#ifdef __TEST_UPD__

			  if( GET_BIT ( initial_local_bit_vect_facts, gef_conn[el].PC[k])!=0 )
			    {
			      printf("\n Prec %d Cost 0 num actions 0  name ", gef_conn[el].PC[k]);
			      print_ft_name (gef_conn[el].PC[k]);
			    }
			  else
			    {
			      loc_dg_cost= get_level_dg_inform(level, gef_conn[el].PC[k]);

			      if(loc_dg_cost)
				{
				  printf
				    ("\n Prec %d Cost %.2f Duration %.2f num actions %d  name ",
				     gef_conn[el].PC[k],
				     loc_dg_cost->cost,
				     loc_dg_cost->duration,
				     loc_dg_cost->num_actions);
				  print_ft_name (gef_conn[el].PC[k]);
				}
			      else
				{
				  printf("\n No reach inform for ");
				  print_ft_name(gef_conn[el].PC[k]);
				}
			    }
#endif

			  if( GET_BIT ( initial_local_bit_vect_facts, gef_conn[el].PC[k])!=0 )
			    {
			      if (CONVERT_FACT_TO_NODE(gef_conn[el].PC[k], level)->time_f > max_prec_duration)
				max_prec_duration = CONVERT_FACT_TO_NODE (gef_conn[el].PC[k], level)->time_f;

			    }
			  else
			    {

			      loc_dg_cost= get_level_dg_inform(level, gef_conn[el].PC[k]);
			      skip_no_up=FALSE;
 
			      if(loc_dg_cost==NULL)
				{
				  printf("\n Warning RI not computed 1");
				  continue;
				}
                              

                          /**
			     Se il costo di tale precondizione supera 
			     il massimo finora computato, assegna al 
			     massimo il nuovo valore
			  **/
			  if ( loc_dg_cost->cost > max_prec_cost)
			    max_prec_cost = loc_dg_cost->cost;

			  /**
			  if (loc_dg_cost->duration > max_prec_duration)
			    max_prec_duration = loc_dg_cost->duration;
			  **/


			  /* Se il costo, in termini di azioni, per rendere supporatata la precondizione,
			   *  supera il massimo finora computato, assegna al massimo il nuovo valore
			   */

			  if (loc_dg_cost->num_actions > max_prec_num_actions)
			    max_prec_num_actions =loc_dg_cost->num_actions;


			    }
			}
		}		// for PC AT_START
	
	      /* Se ho dichiarato che l'azione era da saltare (rendendo skip=TRUE) passo alla prossima 
	       */
	      if (skip)
		continue;	// I do not consider this action

	      /* Precondizioni overall e at end
	       */
	      if (gef_conn[el].sf != NULL)
		{

		  // Precondizioni OVERALL
		  for (k = 0; k < gef_conn[el].sf->num_PC_overall; k++)	
		    //if its preconditions are supported or previously computed I set the additive effects of el
		    {
		      /* Non prendo in considerazione precondizioni numeriche
		       */
		      if (gef_conn[el].sf->PC_overall[k] < 0)
			continue;	// LAZZA

		      /* Se la precondizione si trova negli effetti additivi at start è la stessa azione
		       * a rendere supportata tale precondizione overall
		       */
		      if (is_fact_in_additive_effects_start
			  (el, gef_conn[el].sf->PC_overall[k]))
			continue;


		      /* Precondizioni OVERALL, controllo che siano supportate altrimenti salto l'azione
		       * poichè attualmente non è applicabile
		       */
		      if (  GET_BIT (vectlevel[level]->local_bit_vect_facts, gef_conn[el].sf->PC_overall[k])==0 && GET_BIT (Hvar.local_bit_vect_facts, gef_conn[el].sf->PC_overall[k])==0 )

			    {

#ifdef __TEST_UPD__

			      printf ("\n Break, Prec %d not supported ",
				      gef_conn[el].sf->PC_overall[k]);
			      print_ft_name (gef_conn[el].sf->PC_overall[k]);
#endif
			      skip = TRUE;
			      break;
			      // The precondition is not supported and we have not previously compued its cost
			    }
			  else
			    {

#ifdef __TEST_UPD__
			      if( GET_BIT ( initial_local_bit_vect_facts,  gef_conn[el].sf->PC_overall[k])!=0 )
			    {
			      printf("\n Prec %d Cost 0 num actions 0  name ", gef_conn[el].PC[k]);
			      print_ft_name ( gef_conn[el].sf->PC_overall[k] );
			    }
			  else
			    {
			      loc_dg_cost= get_level_dg_inform(level,  gef_conn[el].sf->PC_overall[k]);

			      if(loc_dg_cost)
				{
				  printf
				    ("\n Prec %d Cost %.2f Duration %.2f num actions %d  name ",
				     gef_conn[el].sf->PC_overall[k],
				     loc_dg_cost->cost,
				     loc_dg_cost->duration,
				     loc_dg_cost->num_actions);
				  print_ft_name ( gef_conn[el].sf->PC_overall[k]);
				}
			      else
				{
				  printf("\n No reach inform for ");
				  print_ft_name ( gef_conn[el].sf->PC_overall[k]);
				}
			    }
#endif



			  if( GET_BIT ( initial_local_bit_vect_facts, gef_conn[el].sf->PC_overall[k])!=0 )
			    {
			      if (CONVERT_FACT_TO_NODE(gef_conn[el].sf->PC_overall[k], level)->time_f > max_prec_duration)
				max_prec_duration = CONVERT_FACT_TO_NODE (gef_conn[el].sf->PC_overall[k], level)->time_f;

			    }
			  else
			    {
			      loc_dg_cost= get_level_dg_inform(level,  gef_conn[el].sf->PC_overall[k]);
			      skip_no_up=FALSE;
			      if(loc_dg_cost==NULL)
				{
				  printf("\n Warning RI not computed 2");
				  continue;
				}
                               


                          /**
			     Se il costo di tale precondizione supera 
			     il massimo finora computato, assegna al 
			     massimo il nuovo valore
			  **/
			  if ( loc_dg_cost->cost > max_prec_cost)
			    max_prec_cost = loc_dg_cost->cost;

			  /**
			  if (loc_dg_cost->duration > max_prec_duration)
			    max_prec_duration = loc_dg_cost->duration;
			  **/

			  /* Se il costo, in termini di azioni, per rendere supporatata la precondizione,
			   *  supera il massimo finora computato, assegna al massimo il nuovo valore
			   */

			  if (loc_dg_cost->num_actions > max_prec_num_actions)
			    max_prec_num_actions =loc_dg_cost->num_actions;
			}
			    }

		    }		// for PC OVERALL
		    

		  /* Se ho dichiarato che l'azione era da saltare (rendendo skip=TRUE) passo alla prossima 
		   */
		  if (skip)
		    continue;	// I do not consider this action



		  // Precondizioni AT_END
		  for (k = 0; k < gef_conn[el].sf->num_PC_end; k++)	//if its preconditions are supported or previously computed I set the additive effects of el
		    {
		      /* Non prendo in considerazione precondizioni numeriche
		       */
		      if (gef_conn[el].sf->PC_end[k] < 0)
			continue;	// LAZZA

		      /* Se la precondizione si trova negli effetti additivi at starto at end  è la stessa azione
		       * a rendere supportata tale precondizione at end
		       */
		      if (is_fact_in_additive_effects_start(el, gef_conn[el].sf->PC_end[k]))
			continue;
	
		      /* Precondizioni AT END, controllo che siano supportate altrimenti salto l'azione
		       * poichè attualmente non è applicabile
		       */


		      if (  GET_BIT (vectlevel[level]->local_bit_vect_facts, gef_conn[el].sf->PC_end[k])==0 &&  GET_BIT (Hvar.local_bit_vect_facts, gef_conn[el].sf->PC_end[k])==0  )
			{
#ifdef __TEST_UPD__
			  printf ("\n Break, Prec %d not supported ",
				  gef_conn[el].sf->PC_end[k]);
			  print_ft_name (gef_conn[el].sf->PC_end[k]);
#endif
			  skip = TRUE;
			  break;
			}
		      else
			{
#ifdef __TEST_UPD__

			  if( GET_BIT ( initial_local_bit_vect_facts, gef_conn[el].sf->PC_end[k])!=0 )
			    {
			      printf("\n Prec %d Cost 0 num actions 0  name ", gef_conn[el].PC[k]);
			      print_ft_name (gef_conn[el].sf->PC_end[k]);
			    }
			  else
			    {
			      loc_dg_cost= get_level_dg_inform(level, gef_conn[el].sf->PC_end[k] );
			      if(loc_dg_cost)
				{
				  printf
				    ("\n Prec %d Cost %.2f Duration %.2f num actions %d  name ",
				     gef_conn[el].sf->PC_end[k],
				     loc_dg_cost->cost,
				     loc_dg_cost->duration,
				     loc_dg_cost->num_actions);
				  print_ft_name (gef_conn[el].sf->PC_end[k]);
				  
				}
			      else
				{
				  printf("\n No reach inform for ");
				  print_ft_name (gef_conn[el].sf->PC_end[k]);

				}

			    }
#endif

			  if( GET_BIT ( initial_local_bit_vect_facts, gef_conn[el].sf->PC_end[k])!=0 )
			    {
			      if ((CONVERT_FACT_TO_NODE(gef_conn[el].sf->PC_end[k], level)->time_f - get_action_time(el,level)) > max_prec_duration)
				max_prec_duration = CONVERT_FACT_TO_NODE (gef_conn[el].sf->PC_end[k], level)->time_f- get_action_time(el,level);

			    }
			  else
			    {

			      loc_dg_cost= get_level_dg_inform(level, gef_conn[el].sf->PC_end[k]);
			      skip_no_up=FALSE;
			      if(loc_dg_cost==NULL)
				{
				  printf("\n Warning RI not computed 2");
				  continue;
				}
                               


                          /**
			     Se il costo di tale precondizione supera 
			     il massimo finora computato, assegna al 
			     massimo il nuovo valore
			  **/
			  if ( loc_dg_cost->cost > max_prec_cost)
			    max_prec_cost = loc_dg_cost->cost;


			  /****
			  if ((loc_dg_cost->duration -get_action_time(ef, level))> max_prec_duration)
			    max_prec_duration = loc_dg_cost->duration-get_action_time(ef,level);
			  **/


			  /* Se il costo, in termini di azioni, per rendere supporatata la precondizione,
			   *  supera il massimo finora computato, assegna al massimo il nuovo valore
			   */

			  if (loc_dg_cost->num_actions > max_prec_num_actions)
			    max_prec_num_actions =loc_dg_cost->num_actions;
			    }
			}

		    }		// for PC AT_END

		}
	

	  /* Se ho dichiarato che l'azione era da saltare (rendendo skip=TRUE) passo alla prossima 
	   */
	  if (skip)
	    continue;		// I do not consider this action

	  if(skip_no_up)
	    continue;

	  /* A seconda del tipo di euristica calcolo i nuovi valori di raggiungibilita'
	   */ 
	  if(GpG.cri_evaluate_preconditions==COMPUTE_DG_LIST_COST)
	    {	
	      /* Copio i valori di initial_local_bit_vect_facts in Hvar.ri_supp_bit_vect_facts,initial_local_bit_vect_facts
	       * per rendere disponibili i fatti attualmente supportati nel calcolo dei nuovi valori
	       */
	      memcpy( Hvar.ri_supp_bit_vect_facts,initial_local_bit_vect_facts, gnum_ft_block * sizeof (int));
	      /*compute the cost of the actual action with a relaxed plan where
	       * we insert the action not already applyed by other priors facts
	       */
	      new_cost=cri_predict_cost_relaxed (el, &new_duration, &max_prec_num_actions);
	     
	    }
	  else
	    {
	      /* Calcolo il nuovo costo
	       */
	      new_cost = max_prec_cost + get_action_cost (el, level, NULL);
	
	      max_prec_num_actions++;
	    }

	  new_duration = max_prec_duration + get_action_time (el, level);

	  /* Segnalo che l'azione e' gia' stata considerata andando a settare il bit a 1 nella posizione
	   * corrispondente (el)
	   */
	  SET_BIT (Hvar.local_bit_vect_actions, el);

#ifdef __TEST_UPD__

	  printf
	    ("\n Now I consider Effects of  action %d  new_cost %.2f prec_cost %.2f num_actions %d  name= ",
	     el, new_cost, max_prec_cost, max_prec_num_actions );
	  print_op_name (el);
#endif
	  /* Rendo supportati i fatti che sono effetti dell'azione considerata che è a questo
	   * punto applicabile ed assegno i valori di raggiungibilità
	   */
	  /* Effetti additivi at end
	   */
	  for (k = 0; k < gef_conn[el].num_A; k++)
	    /* Non prendo in considerazione effetti numerici
	     */
	    if (gef_conn[el].A[k] >= 0)
	      {
		/* Rendo il fatto attualmente supportato
		 */

		/*
		  Se il fatto e'  stato esaminato precedentemente
		*/
		if(GET_BIT(  Hvar.local_bit_vect_facts, gef_conn[el].A[k]))
		  continue;
		else
		  SET_BIT(  Hvar.local_bit_vect_facts, gef_conn[el].A[k]);

 
		  /* Se il fatto non è stato ancora preso in considerazione o ho valori
		   * massimi che superano gli attuali aggiorno i  valori di
		   * raggiungibilita'
		   */


		  result=update_dg_fact_list( gef_conn[el].A[k] , &vectlevel[level]->level,max_prec_num_actions , el, new_duration ,new_cost,orig_fact );
		  if(result==FALSE) /* Non ho aggiornato inform ragg */
		    continue;

		  ls_insert_fact_inlist (gef_conn[el].A[k]);

#ifdef __TEST_UPD__
		    printf ("\n\n ++++++Set cost of facts %d : ",
			    gef_conn[el].A[k]);
		    print_ft_name (gef_conn[el].A[k]);
		    printf (" cost %.2f duration %.2f num_actions %d",
			    new_cost, new_duration,
			    max_prec_num_actions);
#endif

	      }

	  // effetti additivi AT_START
	  if (gef_conn[el].sf)
	    for (k = 0; k < gef_conn[el].sf->num_A_start; k++)
	     /* Non prendo in considerazione effetti numerici
	     */
	      if (gef_conn[el].sf->A_start[k] >= 0)
		{

		  
		  /* Se il fatto e' stato esaminato precedentemente
		   */
		  if(GET_BIT(  Hvar.local_bit_vect_facts, gef_conn[el].sf->A_start[k]))
		    continue;
		  else/* Rendo il fatto attualmente supportato
		       */
		    SET_BIT(  Hvar.local_bit_vect_facts, gef_conn[el].sf->A_start[k]); 


		  if (is_fact_in_delete_effects(el, gef_conn[el].sf->A_start[k]))
		    continue;


		  /* Se il fatto non è stato ancora preso in considerazione o ho valori
		   * massimi che superano gli attuali aggiorno i  valori di
		   * raggiungibilita'
		   */


		  result=update_dg_fact_list( gef_conn[el].sf->A_start[k] , &vectlevel[level]->level,max_prec_num_actions , el, new_duration-get_action_time(el,level) ,new_cost,orig_fact );

		  if(result==FALSE) /* Non ho aggiornato inform ragg */
		    continue;


		  ls_insert_fact_inlist (gef_conn[el].sf->A_start[k]);

#ifdef __TEST_UPD__
		    printf ("\n\n ++++++Set cost of facts %d : ",
			    gef_conn[el].sf->A_start[k]);
		    print_ft_name (gef_conn[el].sf->A_start[k]);
		    printf (" cost %.2f duration %.2f num_actions %d",
			    new_cost, new_duration-get_action_time(ef,level),
			    max_prec_num_actions);
#endif


		}

	}			//ciclo su tutte le azioni
	}    
  // devo reimpostare i fatti di quel livello
    }
    }

  GpG.cri_initial_or_update=1; /** Reimposto il valore per evitare utilizzo non coretto durante calcolo info raggiungilita' dovute ad inserimento azione */ 

}






void compute_reachability(State * initial_state)
{

  int i,j,aus_counter;
  /*
   * Bit-vector rispettivamente dei fatti veri booleani e numerici
   */ 
  int * True_bool=NULL;
  int * True_num=NULL;

  int *To_be_Executed;
  int *applied;
  /*
   * Bit-vector che mi dice se la variabile numerica i è rilevante al fine di rendere vera una preco
   * numerica (i-esimo bit=1)
   */
  int *relevant_vars=NULL;
  /*
   * Vettori che mi dicono il numero di precondizioni per cui la variabile i contribuisce al raggiungimento
   * rispettivamente crescendo o diminuendo 
   */
  int *num_Pc_relevant_pos=NULL;
  int *num_Pc_relevant_neg=NULL;

  Bool changed=FALSE;

  int level;
  int num_Pc;   
  /*
   * Vettori contenenti rispettivamente i valori massimi e minimiraggiungibili dalle variabili 
   * numeriche
   */
  float *vmax;
  float *vmin;

  float end_time;
  int *modifieds;
  int ll,l,y,temp;

  int *derived_precs = NULL;
  int dp_num, *dp_vect = NULL;
  
 
  /*
   * Fase iniziale
   */  
  applied = alloc_vect (gnum_ef_block);
  To_be_Executed = alloc_vect (gnum_ef_block);  
  True_bool = alloc_vect (gnum_ft_block);
  True_num= alloc_vect (gnum_block_compvar);
  relevant_vars = alloc_vect (gnum_block_compvar);
  num_Pc_relevant_pos= alloc_vect (gnum_comp_var);
  num_Pc_relevant_neg= alloc_vect (gnum_comp_var);

  vmax=	(float *) calloc (gnum_comp_var, sizeof (float)); 
  vmin= (float *) calloc (gnum_comp_var, sizeof (float)); 
  Hvar.tmd_facts_array=	(int *) calloc (gnum_timed_facts , sizeof (int));
  Hvar.bit_array_tmd_facts_array=alloc_vect (gnum_ft_block);
  Hvar.num_tmd_facts_array=0;	

  memcpy(vmax,ginitial_state.V,gnum_comp_var*sizeof(float));
  memcpy(vmin,ginitial_state.V,gnum_comp_var*sizeof(float));

  modifieds= alloc_vect (gnum_block_compvar);
  
  reset_bitarray (F, gnum_ft_block);
  Numeric.is_a_Pc=alloc_vect(gnum_block_compvar);


  //Il vettore dei fatti veri viene posto uguale allo stato iniziale (F = I)
  //ed i fatti veri allo stato iniziale vengono memorizzati nella struttura gft_conn
  
  for (i = 0; i < initial_state->num_F; i++)
    {
      SET_BIT (True_bool, initial_state->F[i]);
      SET_BIT (F, initial_state->F[i]);
      //Il fatto viene asserito come vero allo stato iniziale e gli viene assegnato
      //il livello zero, ossia il fatto e' vero inizialmente   
    }

  if (GpG.derived_predicates) {
    initialize_dp_num_prec_vector(&derived_precs);
    dp_num = calc_all_derived_predicates_from(derived_precs, True_bool, RESET_ON, &dp_vect);

    for (j = 0; j < dp_num; j++) {
      
	if (dp_vect[j] >= 0)
	  for (aus_counter = 0; aus_counter < gft_conn[dp_vect[j]].num_PC; aus_counter++)
	    Numeric.ri_prec_vector[gft_conn[dp_vect[j]].PC[aus_counter]]--;	    
    
    }
  }

  for(i=0;i<gnum_comp_var;i++)
    {
     
      //Per tutte le precondizioni numeriche
      switch (gcomp_var[i].operator)
	{
	case LESS_THAN_OP:
	case LESS_THAN_OR_EQUAL_OP:
	case EQUAL_OP:
	case GREATER_THAN_OP:
	case GREATER_OR_EQUAL_OP:
	  SET_BIT(Numeric.is_a_Pc,i);
	  if(vmax[i] > 0.5)
	    {
	      /*
	       *Se la precondizione è vera viene settato a 1 il bit relativo del vettore dei fatti numerici veri
	       */
	      SET_BIT(True_num,i);
	     
	      cri_set_init_numeric_fact(i);	     
	    }
	   
	  else
	    {
	      /*
	       *Se è falsa vengono determinate le variabili su cui operare x renderla vera
	       */
	      add_tested_vars_for_cvar (i,num_Pc_relevant_pos,num_Pc_relevant_neg,relevant_vars,TRUE);
	      //   ri_add_tested_vars_for_cvar (i, Hvar.initial_num_tested_positive,Hvar.initial_num_tested_negative,Hvar.initial_relevant_vars,TRUE);
	   
	    }
	  break;
	default:
	  break;
	}

    }


 
  Hvar.modifieds_values=1;
  
  /*
   * Viene aggiunto al numero di precondizioni numeriche non supportate per ogni azione al numero
   * di quelle booleane
   */
  for(i=0;i<gnum_ef_conn;i++)
    if(gef_conn[i].is_numeric)
      {
	Numeric.ri_prec_vector[i]=Numeric.ri_prec_vector[i] + count_unsatisfied_num_preconds(i,True_num); 
      }
 
  /*
   * Variabile che indica  il livello minimo  a cui un'azione è applicabile
   */
   level=0;

 do
    {
      /*
       * changed se è false mi indica che è stata raggiunta la condizione di terminazione
       */
      changed = FALSE;
      reset_bitarray (To_be_Executed, gnum_ef_block);
      
      for (i = 0; i < gnum_ef_conn; i++)
	if(!GET_BIT (applied, i))
	  {
	    if(gef_conn[i].level<0)
	      continue;	
	    if(Numeric.ri_prec_vector[i]<=0)
	      {/*
		* Se l'azione non è stata ancora applicata ed è attualmente supportata
		*/
		if(gef_conn[i].level<=level)
		  {
		    /*
		     * Se il suo livello di applicabilità a causa delle mutex è inferiore a quello 
		     * attuale indico che l'azione i è da eseguire
		     */
		    SET_BIT (To_be_Executed, i);   
		    changed=TRUE;	
		  }
		else
		  {
		    /*
		     * Se il suo livello di applicabilità a causa delle mutex è maggiore di quello 
		     * attuale devo comunque proseguire fino al raggiungimento di tale livello, quindi
		     * non posso terminare fino ad allora
		     */
		    changed=TRUE;
		  }
	      }
	  }		  
      /*per tutte le azioni */
      
      /*se l'azione non e' ancora stata applicata... */
      if(changed==TRUE)
      for (ll = 0, l = 0; l < gnum_ef_block; l++, ll += 32)
	{
	  temp = To_be_Executed[l];
	  y = 32;
	  while (temp)
	    {
	      y--;
	      if (temp & FIRST_1)
		{
		  i = ll + y;		  		  
		  { 
		    
		    if (GpG.accurate_cost >= COMPUTE_MAX_COST)
		      {
			if(Hvar.modifieds_values>0)
			  if (GpG.cri_evaluate_preconditions >= COMPUTE_DG_LIST_COST || GpG.verify_init)
			    {
			      memcpy(Hvar.max_values,ginitial_state.V,gnum_comp_var*sizeof(float));
			      memcpy(Hvar.min_values,ginitial_state.V,gnum_comp_var*sizeof(float));
			    }
			
			Hvar.modifieds_values=0;
			end_time= cri_activate_distgraph_ef (i, True_bool, derived_precs, level, &changed);  
			if(end_time>=0)
			  {
			    /* Setto livello applicabilita' azione */
			    gef_conn[i].level = level; 

			  }
			else
			  {
			    /**
			       azione non applicabile
			    **/
			    gef_conn[i].level = -1;
			    SET_BIT (applied, i);
			    continue;
			  }

		      }
		    
		    /*se l'azione non e' ancora stata applicata... */
		    //segnalo di avere applicato l'azione i-esima poiche' essa e' applicabile
		    SET_BIT (applied, i);
		    /*determino i fatti che possono essere raggiunti grazie a questa nuova azione*/
		    /* A= add(a) - F prendo in considerazione i fatti che non appartengono ancora ad F ed apparten
		       gono agli effetti additivi dell'azione i-esima    */
		    
		    for (j = 0; j < gef_conn[i].num_A; j++)
		      {
			/*se il fatto non era ancora stato reso vero */
			if (gef_conn[i].A[j] >= 0)
			  if (!GET_BIT (True_bool, gef_conn[i].A[j]))
			    {     
			      gft_conn[gef_conn[i].A[j]].in_F = TRUE;
			      gft_conn[gef_conn[i].A[j]].level = level + 1;
			      SET_BIT (True_bool, gef_conn[i].A[j]);
			      SET_BIT (F, gef_conn[i].A[j]);
			      // Se il fatto reso vero era prec. di qualche azione aggiorno il vettore
			      // delle prec. non supportate andando a decrementare la posizione relativa all'azione i
			      for(aus_counter=0;aus_counter< gft_conn[gef_conn[i].A[j]].num_PC;aus_counter++)
				{
				  if(GpG.temporal_plan)
				    {  
				      if(is_fact_in_preconditions_end(gft_conn[gef_conn[i].A[j]].PC[aus_counter],
								      gef_conn[i].A[j])&&
					 is_fact_in_additive_effects_start(gft_conn[gef_conn[i].A[j]].PC[aus_counter],
									   gef_conn[i].A[j]))
					continue;    
				      
				      if(is_fact_in_preconditions_overall(gft_conn[gef_conn[i].A[j]].PC[aus_counter],
									  gef_conn[i].A[j])&&
					 is_fact_in_additive_effects_start(gft_conn[gef_conn[i].A[j]].PC[aus_counter],
									   gef_conn[i].A[j]))
					continue;
				    }
				  
				  Numeric.ri_prec_vector[gft_conn[gef_conn[i].A[j]].PC[aus_counter]]--;
				  if(Numeric.ri_prec_vector[gft_conn[gef_conn[i].A[j]].PC[aus_counter]]==0)
				    changed=TRUE;
				  
				}
			      /*e lo inserisce in un insieme di appoggio che tiene traccia dei fatti aggiunti*/
			      
			    }
		      }
		    //lo stesso per gli effetti at start
		    if (gef_conn[i].sf)
		      {
			for (j = 0; j < gef_conn[i].sf->num_A_start; j++)
			  {
			    /*se il fatto non era ancora stato reso vero */
			    if (gef_conn[i].sf->A_start[j] >= 0)
			      if (!GET_BIT (True_bool, gef_conn[i].sf->A_start[j]))
				{
				  /*lo rende vero adesso */
				  gft_conn[gef_conn[i].sf->A_start[j]].in_F = TRUE;
				  gft_conn[gef_conn[i].sf->A_start[j]].level =level ;
				  SET_BIT (True_bool, gef_conn[i].sf->A_start[j]);
				  SET_BIT (F, gef_conn[i].sf->A_start[j]);
				  //Se il fatto reso vero era prec. di qualche azione aggiorno il vettore
				  //delle prec. non supportate
				  for(aus_counter=0;aus_counter< gft_conn[gef_conn[i].sf->A_start[j]].num_PC;aus_counter++)
				    { 
				      if(GpG.temporal_plan)
					{if(is_fact_in_preconditions_end(gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter],
									 gef_conn[i].sf->A_start[j])&&
					    is_fact_in_additive_effects_start(gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter],
									      gef_conn[i].A[j]))
					  continue;    
					
					if(is_fact_in_preconditions_overall(gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter],
									    gef_conn[i].sf->A_start[j])&&
					   is_fact_in_additive_effects_start(gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter],
									     gef_conn[i].sf->A_start[j]))
					  continue;
					}
				      
				      
				      Numeric.ri_prec_vector[gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter]]--;
				      if(Numeric.ri_prec_vector[gft_conn[gef_conn[i].sf->A_start[j]].PC[aus_counter]]==0)
					changed=TRUE;
				    }
				  
				}
			  }
		      }
		    
		    /*
		     * Se l'azione è numerica vado a controllare i suoi effetti per determinare eventuali variazioni
		     * nei best- increase/decrease/assign
		     */ 
		    if(gef_conn[i].is_numeric)
		      {
			set_best_for_compvar(i,vmax,vmin);			
		      }	     
		    
		  }
		}
	      temp <<= 1;
	    }
	}
      /*
       * Resetto il vettore delle variabili modificate che mi permette di velocizzare il refresh
       */
      reset_bitarray (modifieds, gnum_block_compvar);
      
      for(j=0;j<gnum_comp_var;j++)
	{
	  /*
	   * Se ho una variabile attualmente rilevante, ossia che contribuisce a rendere vera una preco
	   */
	  if(GET_BIT(relevant_vars,j))
	    if(gcomp_var[j].operator==VARIABLE_OP)	      
	      {
		/*
		 * Applico il best assign (se modifica i valori minimi o massimi), quindi
		 * applico il best increase se la variabile crescendo può rendere vera una preco,
		 * mentre applico il best decrease se la variabile diminuendo  può rendere vera una preco,
		 * o entrambi
		 */
		apply_best_assign_for_var(j,vmax,vmin);
		if(num_Pc_relevant_pos[j]>0)
		  apply_best_increase_for_var(j,vmax);
		if(num_Pc_relevant_neg[j]>0)
		  apply_best_decrease_for_var(j,vmax,vmin);
		//		for(i=0;i<gnum_block_compvar;i++)
		  add_affects_list(j,modifieds);
	       	
		  
	      }

	}
      /*
       * Faccio il refresh delle variabili in vmax e vmin e determino il numero di preco numeriche
       * che ho reso vero in questo passaggio(valore di ritorno)
       */
      num_Pc=refresh_max_min_value (vmax,vmin,modifieds);
      
      /*
       * Funzione che verifica se una nuova precondizione è stata resa supportata ed in tal caso decrementa il numero di
       * preco da supportare delle azioni che ce l'hanno come preco 
       */
      if( verify_num_preconditions(True_num,num_Pc_relevant_pos ,num_Pc_relevant_neg,relevant_vars,vmax,num_Pc))
	changed=TRUE;
      
      level++; 
    }
 while (changed);

 set_init_computed_dg_costs();
 /*
  * Tutte le azioni che non sono state applicate non sono applicabili, il loro livello è settato a -1
  */
   for (i = 0; i < gnum_ef_conn; i++)
       if (!GET_BIT (applied, i))
	 {
	   gef_conn[i].in_E = FALSE;
	   gef_conn[i].level = -1;
#ifdef __TEST__
	   printf("\naction %d ha level -1\n",i);
#endif
	 }
     /*
    * Settaggio dei valori di raggiungibilità computati
    */ 

   GpG.fixpoint_plan_length=level-1;
 /*
  * Fase finale
  */ 
 free (applied);
 free(To_be_Executed);
 free(True_bool);
 free(True_num);
 free(relevant_vars);  
 free(num_Pc_relevant_pos);
 free(num_Pc_relevant_neg);
 free(vmin);
 free(vmax);
 free(modifieds);
 
}




void cri_set_init_numeric_fact(int fact_pos)
{


  Hvar.ri_tot_cost_of_numeric_facts[fact_pos]=0.0;
  Hvar.ri_cost_of_numeric_facts[fact_pos]=0.0;
  Hvar.ri_duration_of_numeric_facts[fact_pos]=0.0;
  Hvar.ri_num_actions_of_numeric_facts[fact_pos]=0.0;
  SET_BIT(Hvar.ri_initial_bit_vect_numeric_facts,fact_pos);	      

}


void update_intermediate_reachab_inform(int fact, int best_act,  int num_actions, float cost, float duration, int *level)
{
  int insert=FALSE;

  if(GpG.cri_intermediate_levels!= DYNAMIC_INTERMEDIATE_REACHAB_INFORM)
    return;

 

  if(Hvar.intermediate_reachab_facts_array[fact]==NULL)
    {

      Hvar.intermediate_reachab_facts_array[fact]=calloc_dg_inform();   /* creazione nodo da inserire nella lista */ 
      
      insert=TRUE;
    }  
  else
    if( Hvar.intermediate_reachab_facts_array[fact]->search_step!=GpG.count_num_try)
      insert=TRUE;
    else
      if(Hvar.intermediate_reachab_facts_array[fact]->num_actions> num_actions || 
	 (Hvar.intermediate_reachab_facts_array[fact]->num_actions==num_actions &&
	     Hvar.intermediate_reachab_facts_array[fact]->cost< cost ))
	 insert=TRUE;

  if(insert)
    {
      Hvar.intermediate_reachab_facts_array[fact]->num_actions= num_actions;
      Hvar.intermediate_reachab_facts_array[fact]->cost=cost;
      Hvar.intermediate_reachab_facts_array[fact]->best_act=best_act;
      Hvar.intermediate_reachab_facts_array[fact]->duration=duration;
      Hvar.intermediate_reachab_facts_array[fact]->stop=TRUE;
      
      Hvar.intermediate_reachab_facts_array[fact]->search_step=GpG.count_num_try;
      
      Hvar.intermediate_reachab_facts_array[fact]->prev = Hvar.init_facts_array[fact];
      
      Hvar.intermediate_reachab_facts_array[fact]->level=level;
    }



}

int get_intermediate_reachab_inform(int fact, int level, dg_inform_list * loc_dg_cost  )
{
 
  if(Hvar.intermediate_reachab_facts_array==NULL)
    {
      Hvar.intermediate_reachab_facts_array= (dg_inform_list *) calloc (gnum_ft_conn, sizeof (dg_inform_list));
    }
  if( Hvar.intermediate_reachab_facts_array[fact]== NULL || *Hvar.intermediate_reachab_facts_array[fact]->level> level)
    *loc_dg_cost= Hvar.init_facts_array[fact];
  else
    *loc_dg_cost= Hvar.intermediate_reachab_facts_array[fact];

  return level;
}
