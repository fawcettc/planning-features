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
 * File: H_MAX.c
 * Description: heuristic H_MAX.
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/



#include "lpg.h"
#include "inst_utils.h"
#include "H_max.h"
#include "utilities.h"
#include "LpgOutput.h"
#include "output.h"
#include "numeric.h"
#include "H_relaxed.h"
#include "derivedpred.h"


/***************************************
          ACTION FOR HEURISTIC
 ***************************************/





void
remove_temp_action (int act_pos, int level)
{
  int i;
  int k;

  EfConn *act;
  static int first_call = 0, last_action = -1;
  ActNode_list infAction;
  noop_not_in *temp;

  if (first_call == 0)
    {
      // alloco bitvector per fatti 
      new_true_facts = alloc_vect (gnum_ft_block);
      new_false_facts = alloc_vect (gnum_ft_block);
    }

  if (last_action >= 0)
    {
      // azzero opportunamente i blocchi di interi resi precedentemente veri 
      memset (new_true_facts, 0, gnum_ft_block * sizeof (int));

      for (i = 0; i < gef_conn[last_action].num_A; i++)
	{

	  if (gef_conn[last_action].A[i] < 0)
	    continue;

	  new_false_facts[GUID_BLOCK (gef_conn[last_action].A[i])] = 0;
	  
	  if (GpG.derived_predicates) {
	    // azzero i anche i blocchi corrispondenti a predicati derivati
	    for (k = 0; k < gft_conn[gef_conn[last_action].A[i]].num_dp_PC; k++)
	      new_false_facts[GUID_BLOCK((gdp_conn[gft_conn[gef_conn[last_action].A[i]].dp_PC[k]].add))] = 0;

	  }
	  
	  
	}
    }

  last_action = act_pos;
  act = &gef_conn[act_pos];

#ifdef __TEST__

  if (CHECK_ACTION_POSTION_OF_LEVEL (act_pos, level) == FALSE)
    {
      MSG_ERROR ("");
      exit (0);
    }
#endif

  // If the action is in the subgraph, we want to remove it, 
  // else if the action is not in the subgraph, we want to insert it.   
  infAction = GET_ACTION_OF_LEVEL (level);

#ifdef __TEST__
  printf ("\nTEMP RA %s is_used %d time %d pos %d", act->name,
	  infAction->w_is_used, level, infAction->position);
#endif

  for (i = 0; i < gef_conn[last_action].num_A; i++)
    {

      if (gef_conn[last_action].A[i] < 0)
	continue;

      new_false_facts[GUID_BLOCK (gef_conn[last_action].A[i])] |=
	GUID_MASK (gef_conn[last_action].A[i]);
    }


  /*  azioni durative */
  if (gef_conn[last_action].sf != NULL)
    {
      for (i = 0; i < gef_conn[last_action].sf->num_A_start; i++)
	{

	  if (gef_conn[last_action].sf->A_start[i] < 0)
	    continue;

	  new_false_facts[GUID_BLOCK (gef_conn[last_action].sf->A_start[i])]
	    |= GUID_MASK (gef_conn[last_action].sf->A_start[i]);
	}
    }

  temp = infAction->add;
  while (temp != NULL)
    {
      new_true_facts[GUID_BLOCK (temp->position)] |=
	GUID_MASK (temp->position);
      temp = temp->next;
    }

  /* azioni durative */
  if (gef_conn[last_action].sf != NULL)
    {

      for (i = 0; i < gef_conn[last_action].num_D; i++)
	{
	  if (gef_conn[last_action].D[i] < 0)
	    continue;

	  new_true_facts[GUID_BLOCK (gef_conn[last_action].D[i])] |=
	    GUID_MASK (gef_conn[last_action].D[i]);
	}

      for (i = 0; i < gef_conn[last_action].sf->num_D_start; i++)
	{
	  if (is_fact_in_additive_effects
	      (last_action, gef_conn[last_action].sf->D_start[i]))
	    continue;

	  if (gef_conn[last_action].sf->D_start[i] < 0)
	    continue;
	  new_true_facts[GUID_BLOCK (gef_conn[last_action].sf->D_start[i])] |=
	    GUID_MASK (gef_conn[last_action].sf->D_start[i]);

	}
    } /* end azioni durative */

}








inline float
fast_insertion_action_cost (int act_pos, int level, int temp_removed_action)
{
  register int temp, i, *ptr;
  int diff;
  register EfConn *act;
  float total, prec_par, excl_par, add_effect_par;


  /* Define the alpha, beta, gamma coefficents of F() to  
     remove the action act from the action subgraph */
  act = &gef_conn[act_pos];

  prec_par = GpG.prec_par;
  excl_par = GpG.excl_par;
  add_effect_par = GpG.add_effect_par;

  total = 0.0;

  if (DEBUG4)
    printf ("\n\n Evalutate action");

  if (DEBUG3)
    printf ("\nFAST_INSERTION  Act: %s, level. %d",
	    print_op_name_string (act_pos, temp_name), level);

#ifdef __TEST__
  printf ("\nFIC ");
#endif

  /* Counts unsatisfied Preconditions */
  if (prec_par)
    {

      if (level <= temp_removed_action)
	{
	  for (i = 0, temp = 0; i < act->num_precond; i++)
	    temp +=
	      count_bit1 (act->bit_precond[i].uid_mask & (~vectlevel[level]->fact_vect[act->bit_precond[i].uid_block]));

	  /* precondizioni numeriche */
	  for (i = 0; i < act->num_PC; i++)
	    if (act->PC[i] < 0)
	      if (!is_num_prec_satisfied_in_common_level (-act->PC[i]))
		temp++;

	  /* azioni durative */
	  if (act->sf != NULL)
	    {
	      for (i = 0; i < act->sf->num_PC_overall; i++)

		if (act->sf->PC_overall[i] >= 0)
		  {
		    if (vectlevel[level]->fact[act->sf->PC_overall[i]].w_is_true <= 0
			&& !is_fact_in_additive_effects_start (act_pos, act->sf->PC_overall[i]))
		      temp++;
		  }
		else
		  if (!is_num_prec_satisfied_in_common_level(-act->sf->PC_overall[i]))
		    temp++;


	      for (i = 0; i < act->sf->num_PC_end; i++)

		if (act->sf->PC_end[i] >= 0)
		  {
		    if (vectlevel[level]->fact[act->sf->PC_end[i]].w_is_true <= 0 &&
			!is_fact_in_additive_effects_start(act_pos, act->sf->PC_end[i]))
		      temp++;
		  }
		else if (!is_num_prec_satisfied (-act->sf->PC_end[i], level))
		  temp++;

	    }

	}
      else
	for (i = 0, temp = 0; i < act->num_precond; i++)
	  temp +=
	    count_bit1 (act->bit_precond[i].uid_mask &
			(((~vectlevel[level]->fact_vect[act->bit_precond[i].uid_block]) & 
			  (~new_true_facts[act->bit_precond[i].uid_block])) |
			 new_false_facts[act->bit_precond[i].uid_block]));

      total = prec_par * temp;

      if (DEBUG3)
	printf ("\n P: %d", temp);

    }

  if (excl_par)
    {

      if (level <= temp_removed_action)
	{
	  temp = count_mutex_action (act_pos, level);
	}
      else
	for (temp = 0, i = 0; i < gnum_ft_block; i++)
	  if (vectlevel[level]->prec_vect[i])	// Solo se sono diversi da 0 faccio il test 
	    temp += count_bit1 (CONVERT_ACTION_TO_VERTEX (act_pos)->ft_exclusive_vect[i] & ((vectlevel[level]->fact_vect[i] | new_true_facts[i]) & (~new_false_facts[i])) & vectlevel[level]->prec_vect[i]);	// NOOP 

      total += excl_par * temp;


      if (DEBUG3)
	printf ("  ME: %d", temp);

    }
  /* define the cost of Add_effect critics nodes */
  /* a fact is a true critic node if it is precondition of almost an action */
  /* of the next level and it's supported from only one action */

  /* a fact is a false critic node if it is precondition of almost an action */
  /* of the next level and it's not supported */

  if (add_effect_par)
    {
      level++;

      ptr = vectlevel[level]->false_crit_vect;	/* Number of critics fact that should became true; positive aspect */

      if (level <= temp_removed_action)
	{
	  for (i = 0, temp = 0; i < act->num_add_effect; i++)
	    temp +=
	      count_bit1 (act->bit_add_effect[i].
			  uid_mask & *(ptr +
				       act->bit_add_effect[i].uid_block));

	  /* azioni durative */
	  if (act->sf != NULL)
	    {
	      for (i = 0; i < act->sf->num_A_start; i++)
		if (act->sf->A_start[i] >= 0)
		  if (vectlevel[level + 1]->fact[act->sf->A_start[i]].
		      w_is_goal >= 1
		      && vectlevel[level +
				   1]->fact[act->sf->A_start[i]].w_is_true <=
		      0
		      && !is_fact_in_delete_effects (act_pos,
						     act->sf->A_start[i]))
		    temp++;
	    }
	  /* end azioni durative */

	}
      else
	for (i = 0, temp = 0; i < act->num_add_effect; i++)
	  temp +=
	    count_bit1 (act->bit_add_effect[i].
			uid_mask & (*(ptr + act->bit_add_effect[i].uid_block)
				    | (vectlevel[level]->
				       true_crit_vect[act->bit_add_effect[i].
						      uid_block] &
				       new_false_facts[act->bit_add_effect[i].
						       uid_block])));

      total += add_effect_par * temp;
      if (DEBUG3)
	printf ("  Add-E: %d", temp);
    }

  if (FALSE && GpG.Twalkplan && GpG.tabu_length >0)
    {	       
      /* 
	 T_walkgraph: increase the cost function of act if it is in
	 the tabu list 
      */

      diff = GpG.count_num_try - gef_conn[act->position].step;
	  
      if (diff < GpG.tabu_length)
	total += GpG.delta * (GpG.tabu_length - num_try);
    }


  if (DEBUG3)
    printf ("\n -> tot %f", total);


  return (total);
}








/***************************************
            MAX COST HEURISTC
 ***************************************/

// Sezione dedicata alle funzioni di MAX_COST 







// Definisce utilizzando i bit array il costo per rendere vero Fact 
// Quando viene richiamata all'interno di un  max_action_cost prende  
// inconsiderazione anche le azioni utlizzate per render vere tutte le  
// precondizioni dell'azione originaria 

float
compute_max_fact_cost (FctNode_list Fact, node_cost_list n_cost,
		       int action_level)
{

  register int temp, k = 0, j;
  register FtConn *tofix;
  auto float total, cost, prec, mutex, prec_act_cost;
  FctNode_list inf_fact;
  NoopNode_list inf_noop;
  int best_action = -1, best_level = 0, best_act_type = 0, el, cel, level;
  node_cost loc_n_cost, best_n_cost;;


  level = *Fact->level;
  prec_act_cost = 0.0;
  inf_noop = NULL;

#ifdef __TEST__
  if (Fact->action_fact != IS_FACT)
    {
      MSG_ERROR ("compute_max_fact_cost; debug me please");
      exit (0);
    }
#endif


  // Se il fatto e' supportato il costo per renderlo vero e' zero 
  if (fact_is_supported (Fact->position, level) && level <= action_level)
    {

      if (DEBUG4)
	printf ("\n\n Fact supported: %s\n",
		print_ft_name_string (Fact->position, temp_name));

      n_cost->weight = 0.0;
      n_cost->act_cost = 0.0;

      if (GpG.temporal_plan)
	n_cost->act_time = Fact->time_f;


      return (0.0);
    }

  // Il costo e' stato precedentemente calcolato 

  if (DEBUG4)
    {
      printf ("\n ||||| MAX_COST  Fact %s, position %d, level %d",
	      print_ft_name_string (Fact->position, temp_name),
	      Fact->position, level);

    }

  /*
  total = get_fact_cost (Fact->position, *Fact->level, &loc_n_cost);
  if (total >= 0 && total < MAX_COST)
    {

#ifdef __TEST__
      tofix = &gft_conn[Fact->position];
      printf ("\n Fatto %s, weight  %f cost %f time %f",
	      print_ft_name_string (tofix->position, temp_name), total,
	      loc_n_cost.act_cost, loc_n_cost.act_time);
#endif

      n_cost->weight = loc_n_cost.weight;
      n_cost->act_cost = loc_n_cost.act_cost;
      n_cost->act_time = loc_n_cost.act_time;
      return total;
    }
  */
  if (level <= 0)
    return 0;


  total = 0.0;
  best_n_cost.weight = MAX_COST;
  best_n_cost.act_cost = MAX_COST;
  best_n_cost.act_time = MAX_COST;

  // sceglie l'azione che rende vero Fact con il minimo costo di inserimento, considero anche le noop 
  tofix = &gft_conn[Fact->position];

#ifdef __TEST__
  printf ("\n\n <<<<<<<<<<<<<<<<<<<Comp_fact_cost  START %s  time %d pos %d ",
	  print_ft_name_string (tofix->position, temp_name), level,
	  tofix->position);
#endif

  if (level <= 0)
    return 0;

  if (CHECK_NOOP_POS (Fact->position, level - 1))
    {
      if (check_mutex_noop (Fact->position, level - 1) >= 0)
	inf_noop = CONVERT_NOOP_TO_NODE (Fact->position, level - 1);
      else
	{
	  inf_noop = CONVERT_NOOP_TO_NODE (Fact->position, level - 1);	// Used if   best_ation will be NULL 



	  cost = 0.0;

	  if (level >= action_level
	      && CONVERT_FACT_TO_NODE (Fact->position,
					 level - 1)->w_is_true <= 1)
	    cost++;
	  else
	    if (!CONVERT_FACT_TO_NODE (Fact->position, level - 1)->
		w_is_true)
	    cost++;		// Precondizione non supportata  


	  if (best_n_cost.weight >= cost)
	    {

	      loc_n_cost.act_cost = 0.0;
	      loc_n_cost.act_time = 0.0;

	      if (!(best_n_cost.weight == cost && weight_cost (&best_n_cost) < weight_cost (&loc_n_cost)))
		{
		  best_action = inf_noop->position;
		  best_level = *inf_noop->level;
		  best_act_type = IS_NOOP;
		  best_n_cost.weight = cost;
		  best_n_cost.act_cost = loc_n_cost.act_cost;
		  best_n_cost.act_time = loc_n_cost.act_time;

#ifdef __TEST__
		  printf("\n\n Comp_fact_cost  BEST NOOP ACT %s  time %d inc %.2f act_cost %.2f act_time   %.2f ",
		     print_noop_name_string (best_action, temp_name), best_level, best_n_cost.weight, best_n_cost.act_cost, best_n_cost.act_time);
#endif
		}
	    }

	}
    }

  for (j = 0; j < gft_conn[tofix->position].num_A; j++)
    {
      cel = gft_conn[tofix->position].A[j];

      if (is_fact_in_delete_effects (cel, tofix->position))
	continue;

      if (cel < 0)
	continue;

      if (CHECK_ACTION_POS (cel, level - 1))
	{

	  cost = fast_insertion_action_cost (cel, level - 1, action_level);
	  if (best_n_cost.weight >= cost)
	    {

	      loc_n_cost.act_cost = get_action_cost (cel, level - 1, NULL);
	      loc_n_cost.act_time = get_action_time (cel, level - 1);

	      if (best_n_cost.weight == cost
		  && weight_cost (&best_n_cost) <= weight_cost (&loc_n_cost))
		continue;

	      best_action = cel;
	      best_level = level - 1;
	      best_act_type = IS_ACTION;
	      best_n_cost.weight = cost;
	      best_n_cost.act_cost = loc_n_cost.act_cost;
	      best_n_cost.act_time = loc_n_cost.act_time;

#ifdef __TEST__
	      printf
		("\n\n Comp_fact_cost  BEST ACT %s  time %d inc %.2f act_cost %.2f act_time %.2f  ",
		 print_op_name_string (best_action, temp_name), best_level,
		 best_n_cost.weight, best_n_cost.act_cost,
		 best_n_cost.act_time);
#endif

	      if (best_n_cost.weight <= 0)
		break;		// Non esamino ulteriori candidati 
	    }
	}

#ifdef __TEST__
      else
	{
	  printf
	    ("\n L'azione %s non puo' essere applicata al livello %d, lev: %d",
	     print_op_name_string (cel, temp_name), level - 1,
	     gef_conn[cel].level);
	}
#endif

    }

  if (best_action < 0)
    {

      if (inf_noop)
	{
	  best_action = inf_noop->position;
	  best_level = *inf_noop->level;
	  best_act_type = IS_NOOP;

	  n_cost->weight = 1.0;
	  n_cost->act_cost = 1.0;

#ifdef __TEST__
	  printf
	    ("\nL'unica azione che posso scegliere e' una noop weight %f cost %f",
	     n_cost->weight, n_cost->act_cost);
#endif

	}
      else
	{
	  n_cost->weight = MAX_COST;
	  n_cost->act_cost = MAX_COST;

#ifdef __TEST__
	  printf
	    ("\nL'unica azione che posso scegliere e' una noop weight %f cost %f",
	     n_cost->weight, n_cost->act_cost);
#endif

	  return (MAX_COST);
	}
      // Definisco il costo per rendere vere le precondizioni non supportate 
    }

#ifdef __TEST__
  if (best_act_type == IS_ACTION)
    printf ("\n\n     BEST_action   %s  time %d pos %d ",
	    print_op_name_string (best_action, temp_name), best_level,
	    best_action);
  else
    printf ("\n\n     BEST_action   %s  time %d pos %d ",
	    print_noop_name_string (best_action, temp_name), best_level,
	    best_action);
#endif

  n_cost->weight = 0.0;
  n_cost->act_cost = 0.0;
  n_cost->act_time = 0.0;


  if (best_act_type != IS_ACTION)
    {

#ifdef __TEST__
      if (DEBUG3)
	printf
	  ("\n %d +++++++++++ COMPUTE MAX COST ACT %s fact %s act duration 0",
	   ++k, print_noop_name_string (best_action, temp_name),
	   print_ft_name_string (best_action, temp_name));
#endif

      inf_fact = CONVERT_FACT_TO_NODE (best_action, best_level);
      temp = compute_max_fact_cost (inf_fact, &loc_n_cost, action_level);

      if (n_cost->act_cost < loc_n_cost.act_cost
	  && loc_n_cost.act_cost < MAX_COST)
	n_cost->act_cost = loc_n_cost.act_cost;

      if (n_cost->act_time < loc_n_cost.act_time
	  && loc_n_cost.act_time < MAX_COST)
	n_cost->act_time = loc_n_cost.act_time;

      prec = temp;
      n_cost->weight = loc_n_cost.weight;

#ifdef __TEST__
      if (DEBUG3)
	printf
	  ("\n %d +++++++++++++ END COMPUTE MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f ",
	   k, print_noop_name_string (best_action, temp_name),
	   print_ft_name_string (best_action, temp_name), prec,
	   loc_n_cost.weight, loc_n_cost.act_cost, loc_n_cost.act_time);
#endif

    }
  else
    {				// azioni


      // Precondizioni at start
      for (j = 0, k = 0, prec = 0.0; j < gef_conn[best_action].num_PC; j++)
	{
	  el = gef_conn[best_action].PC[j];

	  if (el < 0)
	    continue;

	  if (CHECK_FACT_POS (el, best_level))
	    {

#ifdef __TEST__
	      if (DEBUG3)
		printf ("\n %d +++++++++++ COMPUTE MAX COST ACT %s fact %s",
			++k, print_op_name_string (best_action, temp_name),
			print_ft_name_string (el, temp_name));
#endif

	      inf_fact = CONVERT_FACT_TO_NODE (el, best_level);
	      temp =
		compute_max_fact_cost (inf_fact, &loc_n_cost, action_level);


	      if (GpG.accurate_cost == COMPUTE_MAX_COST)
		{


		  if (n_cost->act_cost < loc_n_cost.act_cost
		      && loc_n_cost.act_cost < MAX_COST)
		    n_cost->act_cost = loc_n_cost.act_cost;

		  if (n_cost->act_time < loc_n_cost.act_time
		      && loc_n_cost.act_time < MAX_COST)
		    n_cost->act_time = loc_n_cost.act_time;

#ifdef __TEST__
		  if (DEBUG2)
		    {
		      if (best_act_type == IS_ACTION)
			printf
			  ("\n %d +++++++++++++ END COMPUTE MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f  act_duration %.2f",
			   k, print_op_name_string (best_action, temp_name),
			   print_ft_name_string (el, temp_name), prec,
			   loc_n_cost.weight, loc_n_cost.act_cost,
			   loc_n_cost.act_time, get_action_time (best_action,
								 best_level));
		      else
			printf
			  ("\n %d +++++++++++++ END COMPUTE MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f",
			   k, print_noop_name_string (best_act_type,
						      temp_name),
			   print_ft_name_string (el, temp_name), prec,
			   loc_n_cost.weight, loc_n_cost.act_cost,
			   loc_n_cost.act_time);
		    }
#endif

		  if (prec < temp)
		    {
		      prec = temp;
		      n_cost->weight = loc_n_cost.weight;


#ifdef __TEST__
		      if (DEBUG2)
			{
			  if (best_act_type == IS_ACTION)
			    printf
			      ("\n %d BEST  MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f ",
			       k, print_op_name_string (best_action,
							temp_name),
			       print_ft_name_string (el, temp_name), prec,
			       n_cost->weight, n_cost->act_cost,
			       n_cost->act_time);
			  else
			    printf
			      ("\n %d BEST  MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f ",
			       k, print_noop_name_string (best_action,
							  temp_name),
			       print_ft_name_string (el, temp_name), prec,
			       n_cost->weight, n_cost->act_cost,
			       n_cost->act_time);
			}
#endif



		      if (FALSE
			  && (temp *=
			      local_search.lamda_prec) >
			  local_search.best_cost)
			{

			  if (DEBUG4)
			    printf ("\n MAX_ACT_COST stop");
			  return temp;	// Ho superato il cost limite e quindi non ricerco ulteriormente 
			}

		    }
		}
	      else if (GpG.accurate_cost == COMPUTE_ADD_COST)
		{
		  if (loc_n_cost.act_cost < MAX_COST)
		    n_cost->act_cost += loc_n_cost.act_cost;
		  if (loc_n_cost.act_time < MAX_COST)
		    n_cost->act_time += loc_n_cost.act_time;


#ifdef __TEST__
		  if (DEBUG2)
		    printf
		      ("\n %d +++++++++++++ END COMPUTE ADD COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f  time  %.2f",
		       k, print_op_name_string (best_action, temp_name),
		       print_ft_name_string (el, temp_name), prec,
		       loc_n_cost.weight, loc_n_cost.act_cost,
		       loc_n_cost.act_time);
#endif

		  prec += temp;
		  n_cost->weight += loc_n_cost.weight;


#ifdef __TEST__
		  if (DEBUG2)
		    printf
		      ("\n %d BEST  ADD COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f ",
		       k, print_op_name_string (best_action, temp_name),
		       print_ft_name_string (el, temp_name), prec,
		       n_cost->weight, n_cost->act_cost, n_cost->act_time);
#endif

		}

	    }

#ifdef __TEST__
	  else
	    printf
	      ("\n ERRORE 1002  Fatto %s non presente al corrispondente livello %d, first level %d",
	       print_ft_name_string (el, temp_name), level - 1,
	       CONVERT_FACT_TO_VERTEX (el)->level);
#endif

	}

      // Precondizioni overall
      if (gef_conn[best_action].sf != NULL)
	{
	  for (j = 0; j < gef_conn[best_action].sf->num_PC_overall; j++)
	    {
	      el = gef_conn[best_action].sf->PC_overall[j];

	      if (el < 0)
		continue;

	      if (is_fact_in_additive_effects_start (best_action, el))
		{
		  printf
		    ("\nskip_precondition: continue... is_fact_in_additive_effects_start");
		  continue;
		}

	      if (CHECK_FACT_POS (el, best_level))
		{

#ifdef __TEST__
		  if (DEBUG2)

		    printf
		      ("\n %d +++++++++++ COMPUTE MAX COST ACT %s fact %s",
		       ++k, print_op_name_string (best_action, temp_name),
		       print_ft_name_string (el, temp_name));
#endif

		  inf_fact = CONVERT_FACT_TO_NODE (el, best_level);
		  temp =
		    compute_max_fact_cost (inf_fact, &loc_n_cost,
					   action_level);


		  if (GpG.accurate_cost == COMPUTE_MAX_COST)
		    {


		      if (n_cost->act_cost < loc_n_cost.act_cost
			  && loc_n_cost.act_cost < MAX_COST)
			n_cost->act_cost = loc_n_cost.act_cost;

		      if (n_cost->act_time < loc_n_cost.act_time
			  && loc_n_cost.act_time < MAX_COST)
			n_cost->act_time = loc_n_cost.act_time;

#ifdef __TEST__
		      if (DEBUG2)
			{
			  if (best_act_type == IS_ACTION)
			    printf
			      ("\n %d +++++++++++++ END COMPUTE MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f  act_duration %.2f",
			       k, print_op_name_string (best_action,
							temp_name),
			       print_ft_name_string (el, temp_name), prec,
			       loc_n_cost.weight, loc_n_cost.act_cost,
			       loc_n_cost.act_time,
			       get_action_time (best_action, best_level));
			  else
			    printf
			      ("\n %d +++++++++++++ END COMPUTE MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f",
			       k, print_noop_name_string (best_act_type,
							  temp_name),
			       print_ft_name_string (el, temp_name), prec,
			       loc_n_cost.weight, loc_n_cost.act_cost,
			       loc_n_cost.act_time);
			}
#endif

		      if (prec < temp)
			{
			  prec = temp;
			  n_cost->weight = loc_n_cost.weight;


#ifdef __TEST__
			  if (DEBUG2)
			    {
			      if (best_act_type == IS_ACTION)
				printf
				  ("\n %d BEST  MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f ",
				   k, print_op_name_string (best_action,
							    temp_name),
				   print_ft_name_string (el, temp_name), prec,
				   n_cost->weight, n_cost->act_cost,
				   n_cost->act_time);
			      else
				printf
				  ("\n %d BEST  MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f ",
				   k, print_noop_name_string (best_action,
							      temp_name),
				   print_ft_name_string (el, temp_name), prec,
				   n_cost->weight, n_cost->act_cost,
				   n_cost->act_time);
			    }
#endif

			  if (FALSE
			      && (temp *=
				  local_search.lamda_prec) >
			      local_search.best_cost)
			    {

			      if (DEBUG4)
				printf ("\n MAX_ACT_COST stop");
			      return temp;	// Ho superato il cost limite e quindi non ricerco ulteriormente 
			    }

			}
		    }
		  else if (GpG.accurate_cost == COMPUTE_ADD_COST)
		    {
		      if (loc_n_cost.act_cost < MAX_COST)
			n_cost->act_cost += loc_n_cost.act_cost;
		      if (loc_n_cost.act_time < MAX_COST)
			n_cost->act_time += loc_n_cost.act_time;


#ifdef __TEST__
		      if (DEBUG2)
			printf
			  ("\n %d +++++++++++++ END COMPUTE ADD COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f  time  %.2f",
			   k, print_op_name_string (best_action, temp_name),
			   print_ft_name_string (el, temp_name), prec,
			   loc_n_cost.weight, loc_n_cost.act_cost,
			   loc_n_cost.act_time);
#endif

		      prec += temp;
		      n_cost->weight += loc_n_cost.weight;


#ifdef __TEST__
		      if (DEBUG2)
			printf
			  ("\n %d BEST  ADD COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f ",
			   k, print_op_name_string (best_action, temp_name),
			   print_ft_name_string (el, temp_name), prec,
			   n_cost->weight, n_cost->act_cost,
			   n_cost->act_time);

#endif

		    }

		}

#ifdef __TEST__
	      else
		printf
		  ("\n ERRORE 1002  Fatto %s non presente al corrispondente livello %d, first level %d",
		   print_ft_name_string (el, temp_name), level - 1,
		   CONVERT_FACT_TO_VERTEX (el)->level);
#endif

	    }

	}




      // Precondizioni at end
      if (gef_conn[best_action].sf != NULL)
	{
	  for (j = 0; j < gef_conn[best_action].sf->num_PC_end; j++)
	    {
	      el = gef_conn[best_action].sf->PC_end[j];

	      if (el < 0)
		continue;

	      if (is_fact_in_additive_effects_start (best_action, el))
		continue;

	      if (CHECK_FACT_POS (el, best_level))
		{

#ifdef __TEST__
		  if (DEBUG2)

		    printf("\n %d +++++++++++ COMPUTE MAX COST ACT %s fact %s",
		       ++k, print_op_name_string (best_action, temp_name),
		       print_ft_name_string (el, temp_name));
#endif


		  inf_fact = CONVERT_FACT_TO_NODE (el, best_level);


		  temp = compute_max_fact_cost (inf_fact, &loc_n_cost, action_level);


		  if (GpG.accurate_cost == COMPUTE_MAX_COST)
		    {
		      if (n_cost->act_cost < loc_n_cost.act_cost  && loc_n_cost.act_cost < MAX_COST)
			n_cost->act_cost = loc_n_cost.act_cost;

		      if (n_cost->act_time < loc_n_cost.act_time  && loc_n_cost.act_time < MAX_COST)
			n_cost->act_time = loc_n_cost.act_time;

#ifdef __TEST__
		      if (DEBUG2)
			{
			  if (best_act_type == IS_ACTION)
			    printf("\n %d +++++++++++++ END COMPUTE MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f  act_duration %.2f",k, print_op_name_string (best_action,temp_name),
			       print_ft_name_string (el, temp_name), prec,
			       loc_n_cost.weight, loc_n_cost.act_cost,
			       loc_n_cost.act_time,
			       get_action_time (best_action, best_level));
			  else
			    printf
			      ("\n %d +++++++++++++ END COMPUTE MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f",
			       k, print_noop_name_string (best_act_type,
							  temp_name),
			       print_ft_name_string (el, temp_name), prec,
			       loc_n_cost.weight, loc_n_cost.act_cost,
			       loc_n_cost.act_time);
			}
#endif

		      if (prec < temp)
			{
			  prec = temp;
			  n_cost->weight = loc_n_cost.weight;


#ifdef __TEST__
			  if (DEBUG2)
			    {
			      if (best_act_type == IS_ACTION)
				printf
				  ("\n %d BEST  MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f ",
				   k, print_op_name_string (best_action,temp_name),
				   print_ft_name_string (el, temp_name), prec,
				   n_cost->weight, n_cost->act_cost,
				   n_cost->act_time);
			      else
				printf
				  ("\n %d BEST  MAX COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f ",
				   k, print_noop_name_string (best_action,temp_name),
				   print_ft_name_string (el, temp_name), prec,n_cost->weight, n_cost->act_cost,
				   n_cost->act_time);
			    }
#endif


			  if (FALSE && (temp *=local_search.lamda_prec) >
			      local_search.best_cost)
			    {

			      if (DEBUG4)
				printf ("\n MAX_ACT_COST stop");
			      return temp;	// Ho superato il cost limite e quindi non ricerco ulteriormente 
			    }

			}
		    }
		  else if (GpG.accurate_cost == COMPUTE_ADD_COST)
		    {
		      if (loc_n_cost.act_cost < MAX_COST)
			n_cost->act_cost += loc_n_cost.act_cost;
		      if (loc_n_cost.act_time < MAX_COST)
			n_cost->act_time += loc_n_cost.act_time;


#ifdef __TEST__
		      if (DEBUG2)
			printf
			  ("\n %d +++++++++++++ END COMPUTE ADD COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f  time  %.2f",
			   k, print_op_name_string (best_action, temp_name),
			   print_ft_name_string (el, temp_name), prec,
			   loc_n_cost.weight, loc_n_cost.act_cost,
			   loc_n_cost.act_time);
#endif

		      prec += temp;
		      n_cost->weight += loc_n_cost.weight;

#ifdef __TEST__
		      if (DEBUG2)
			printf("\n %d BEST  ADD COST ACT %s fact %s cost %.2f weight %.2f act_cost %.2f act_time %.2f ",
			   k, print_op_name_string (best_action, temp_name),
			   print_ft_name_string (el, temp_name), prec,
			   n_cost->weight, n_cost->act_cost,
			   n_cost->act_time);

#endif
		    }

		}

#ifdef __TEST__
	      else
		printf("\n ERRORE 1002  Fatto %s non presente al corrispondente livello %d, first level %d",
		   print_ft_name_string (el, temp_name), level, CONVERT_FACT_TO_VERTEX (el)->level);
#endif

	    }

	}

    }

  if (best_act_type != IS_ACTION)
    {
      total = 0.0;

      mutex = count_mutex_noop (best_action, best_level);
    }
  else
    {
      total = 1.0;

      n_cost->act_cost += get_action_cost (best_action, best_level, NULL);
      n_cost->act_time += get_action_time (best_action, best_level);
      mutex = count_mutex_action (best_action, best_level);

      total += mutex;
    }
  total += prec;

  n_cost->weight = total;


  if (DEBUG4)
    printf
      ("\n\n ||| END MAX_COST  Fact %s, position %d, level %d\n   total %f PREC %.2f ME %.2f act_cost %.2f act_time %.2f ",
       print_ft_name_string (tofix->position, temp_name), tofix->position,
       level, total, prec, mutex, n_cost->act_cost, n_cost->act_time);

  /*
  set_fact_cost (Fact, n_cost);
  */

  return total;

}











/* find the cost function  F(.,.) of removing or adding an action */
float
max_action_cost (neighb_list neighb_act)
{
  register int i, unsat_facts = 0;
  int level, j, diff = 0, next_level;
  register EfConn *act;
  auto float total, prec_par, excl_par, add_effect_par, temp = 0.0, prec, eff;
  FctNode_list inf_fact;
  FctNode fact;
  int el, fact_pos, ind_level;
  auto float precond, mutex, effect, act_cost;	//  LM  
  node_cost loc_n_cost, best_prec_cost, best_eff_cost;

  precond = mutex = effect = act_cost = 0.0;	//  LM 


  level = neighb_act->act_level;
  act = &gef_conn[neighb_act->act_pos];


#ifdef __TEST__
  printf
    ("\n\n ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n MAX ACTION COST level %d action %s duration %f",
     level, print_op_name_string (act->position, temp_name),
     get_action_time (neighb_act->act_pos, level));

  check_plan (GpG.curr_plan_length);
#endif

  total = 0.0;
  /* Define the alpha, beta, gamma coefficents of F() to  
     remove the action act from the action subgraph */

  if (GpG.lm_multilevel) {
    local_search.lamda_prec=vectlevel[level]->lambda_prec[act->position];
    local_search.lamda_me=vectlevel[level]->lambda_me[act->position];
  }
  else {
    local_search.lamda_prec = act->lamda_prec;	//1.0; // GPG3 DA SISTEMARE act->lamda_prec; // Variabili utilizzare per decidere se interrompere la fase di calcolo del costo delle precondizioni e mutex
    local_search.lamda_me = act->lamda_me;
  }
  
  if (neighb_act->constraint_type == C_T_REMOVE_ACTION)
    {				/* ... became unused */
      neighb_act->cost.act_cost =
	(-1) * (get_action_cost (neighb_act->act_pos, level, NULL));
      neighb_act->cost.act_time =
	(-1) * get_action_time (neighb_act->act_pos, level);

      prec_par = GpG.used_prec_par;
      excl_par = GpG.used_excl_par;
      add_effect_par = GpG.used_add_effect_par;
    }
  /*define the alpha, beta, gamma coefficents of F() for  
     add the action act from the action subgraph */
  else
    {				/* ... became used */
      neighb_act->cost.act_cost = get_action_cost (neighb_act->act_pos, neighb_act->act_level, NULL);

      neighb_act->cost.act_time = get_action_time (neighb_act->act_pos, level);

      prec_par = GpG.prec_par;
      excl_par = GpG.excl_par;
      add_effect_par = GpG.add_effect_par;
    }

  if (DEBUG4)
    printf ("\n\n Evalutate action");


  if (DEBUG3)
    printf ("\nMAX COST Act: %s, level %d\n  ", print_op_name_string (act->position, temp_name), level);

  best_prec_cost.weight = 0.0;

  best_prec_cost.act_cost = 0.0;

  best_prec_cost.act_time = 0.0;

  if (GpG.temporal_plan)
    for (ind_level = level; ind_level >= 0; ind_level--)
      {
	if (check_mutex_action (act->position, ind_level) >= 0
	    && vectlevel[ind_level]->action.w_is_used > 0)
	  if (best_prec_cost.act_time <
	      GET_ACTION_OF_LEVEL (ind_level)->time_f)
	    best_prec_cost.act_time = GET_ACTION_OF_LEVEL (ind_level)->time_f;
      }

  /* Counts unsatisfied Preconditions */
  if (prec_par)
    {
      unsat_facts = 0;


      for (prec = 0.0, diff = 0, j = 0; j < gef_conn[act->position].num_PC;
	   j++)
	{
	  el = gef_conn[act->position].PC[j];

	  if (el < 0)
	    {
	      loc_n_cost.weight = 0.0;
	      loc_n_cost.act_cost = 0.0;
	      loc_n_cost.act_time = 0.0;
	      //Costo per rendere vere le precondizioni 
	      //creo un fatto fittizio, tanto le uniche info che servono sono position e level
	      fact.position = el;
	      fact.level = &vectlevel[level]->level;
	      /*
		loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		Azzero loc_n_cost
	      */
	      loc_n_cost.weight = 0.0;
	      loc_n_cost.act_cost = 0.0;
	      loc_n_cost.act_time = 0.0;
	      temp =
		compute_relaxed_fact_cost (fact.position, *fact.level,
				       &loc_n_cost, level, get_action_time (neighb_act->act_pos, level) );
	      if (GpG.accurate_cost == COMPUTE_MAX_COST)
		{
		  if (best_prec_cost.act_cost < loc_n_cost.act_cost
		      && loc_n_cost.act_cost < MAX_COST)
		    best_prec_cost.act_cost = loc_n_cost.act_cost;
		  if (best_prec_cost.act_time < loc_n_cost.act_time
		      && loc_n_cost.act_time < MAX_COST)
		    best_prec_cost.act_time = loc_n_cost.act_time;
		  if (prec < temp && temp < MAX_COST)
		    {
		      prec = temp;
		      best_prec_cost.weight = loc_n_cost.weight;
		    }
		}
	      else if (GpG.accurate_cost == COMPUTE_ADD_COST)
		{
		  prec += temp;
		  best_prec_cost.weight += loc_n_cost.weight;
		  best_prec_cost.act_cost += loc_n_cost.act_cost;
		  best_prec_cost.act_time += loc_n_cost.act_time;
		}
	      continue;

	    }

	  if (CHECK_FACT_POS (el, level))
	    {
	      if (DEBUG4)
		{
		  printf ("\n\n %d +++++ MAX_COST Prec_start  Act %s ",
			  ++diff, print_op_name_string (act->position,
							temp_name));
		  printf ("\n  fact %s\n",
			  print_ft_name_string (el, temp_name));
		}

	      loc_n_cost.weight = 0.0;

	      loc_n_cost.act_cost = 0.0;

	      loc_n_cost.act_time = 0.0;


	      //Costo per rendere vere le precondizioni 
	      inf_fact = CONVERT_FACT_TO_NODE (el, level);
	      temp = compute_max_fact_cost (inf_fact, &loc_n_cost, level);

	      if (GpG.accurate_cost == COMPUTE_MAX_COST
		  && inf_fact->w_is_true <= 0)
		unsat_facts++;

	      if (DEBUG4)
		{
		  printf ("\n\n %d +++ END MAX_COST Prec_start  Act %s ",
			  ++diff, print_op_name_string (act->position,
							temp_name));
		  printf
		    ("\n  fact %s, COST  weight %f cost %f time %f unsatisf_prec %d ",
		     print_ft_name_string (el, temp_name), loc_n_cost.weight,
		     loc_n_cost.act_cost, loc_n_cost.act_time, unsat_facts);
		}

	      if (GpG.accurate_cost == COMPUTE_MAX_COST)
		{

		  if (best_prec_cost.act_cost < loc_n_cost.act_cost
		      && loc_n_cost.act_cost < MAX_COST)
		    best_prec_cost.act_cost = loc_n_cost.act_cost;


		  if (best_prec_cost.act_time < loc_n_cost.act_time
		      && loc_n_cost.act_time < MAX_COST)
		    best_prec_cost.act_time = loc_n_cost.act_time;


		  if (prec < temp && temp < MAX_COST)
		    {

		      prec = temp;
		      best_prec_cost.weight = loc_n_cost.weight;

		      if (FALSE
			  && (temp *=
			      local_search.lamda_prec) >
			  local_search.best_cost)
			return temp;	// Ho superato il cost limite e quindi non ricerco ulteriormente 

		    }
		}
	      else if (GpG.accurate_cost == COMPUTE_ADD_COST)
		{
		  prec += temp;

		  best_prec_cost.weight += loc_n_cost.weight;

		  best_prec_cost.act_cost += loc_n_cost.act_cost;

		  best_prec_cost.act_time += loc_n_cost.act_time;


		}


	    }

#ifdef __TEST__
	  else
	    MSG_ERROR ("Max act cost precond");
#endif

	}


      /* azioni durative */
      // precondizioni overall
      if (gef_conn[act->position].sf != NULL)
	{
	  for (j = 0; j < gef_conn[act->position].sf->num_PC_overall; j++)
	    {
	      el = gef_conn[act->position].sf->PC_overall[j];

	      if (el < 0)
		{

		  loc_n_cost.weight = 0.0;
		  loc_n_cost.act_cost = 0.0;
		  loc_n_cost.act_time = 0.0;
		  //Costo per rendere vere le precondizioni 
		  //creo un fatto fittizio, tanto le uniche info che servono sono position e level
		  fact.position = el;
		  /*
		    loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		    Azzero loc_n_cost
		  */
		  loc_n_cost.weight = 0.0;
		  loc_n_cost.act_cost = 0.0;
		  loc_n_cost.act_time = 0.0;

		  temp = compute_relaxed_fact_cost (fact.position, *fact.level, &loc_n_cost, level, get_action_time (neighb_act->act_pos, level));
		  if (GpG.accurate_cost == COMPUTE_MAX_COST)
		    {
		      if (best_prec_cost.act_cost < loc_n_cost.act_cost
			  && loc_n_cost.act_cost < MAX_COST)
			best_prec_cost.act_cost = loc_n_cost.act_cost;
		      if (best_prec_cost.act_time < loc_n_cost.act_time
			  && loc_n_cost.act_time < MAX_COST)
			best_prec_cost.act_time = loc_n_cost.act_time;
		      if (prec < temp && temp < MAX_COST)
			{
			  prec = temp;
			  best_prec_cost.weight = loc_n_cost.weight;
			}
		    }
		  else if (GpG.accurate_cost == COMPUTE_ADD_COST)
		    {
		      prec += temp;
		      best_prec_cost.weight += loc_n_cost.weight;
		      best_prec_cost.act_cost += loc_n_cost.act_cost;
		      best_prec_cost.act_time += loc_n_cost.act_time;
		    }
		  continue;

		}


	      if (is_fact_in_additive_effects_start (act->position, el))
		continue;

	      if (CHECK_FACT_POS (el, level))
		{
		  if (DEBUG4)
		    {
		      printf ("\n\n %d +++++ MAX_COST Prec_overall  Act %s ",
			      ++diff, print_op_name_string (act->position,
							    temp_name));
		      printf ("\n  fact %s\n",
			      print_ft_name_string (el, temp_name));
		    }

		  loc_n_cost.weight = 0.0;

		  loc_n_cost.act_cost = 0.0;

		  loc_n_cost.act_time = 0.0;


		  //Costo per rendere vere le precondizioni 
		  inf_fact = CONVERT_FACT_TO_NODE (el, level);
		  temp = compute_max_fact_cost (inf_fact, &loc_n_cost, level);

		  if (GpG.accurate_cost == COMPUTE_MAX_COST
		      && inf_fact->w_is_true <= 0)
		    unsat_facts++;

		  if (DEBUG4)
		    {
		      printf
			("\n\n %d +++ END MAX_COST Prec_overall  Act %s ",
			 ++diff, print_op_name_string (act->position,
						       temp_name));
		      printf
			("\n  fact %s, COST  weight %f cost %f time %f unsatisf_prec %d ",
			 print_ft_name_string (el, temp_name),
			 loc_n_cost.weight, loc_n_cost.act_cost,
			 loc_n_cost.act_time, unsat_facts);
		    }

		  if (GpG.accurate_cost == COMPUTE_MAX_COST)
		    {

		      if (best_prec_cost.act_cost < loc_n_cost.act_cost
			  && loc_n_cost.act_cost < MAX_COST)
			best_prec_cost.act_cost = loc_n_cost.act_cost;


		      if (best_prec_cost.act_time < loc_n_cost.act_time
			  && loc_n_cost.act_time < MAX_COST)
			best_prec_cost.act_time = loc_n_cost.act_time;


		      if (prec < temp && temp < MAX_COST)
			{
			  prec = temp;
			  best_prec_cost.weight = loc_n_cost.weight;

			  if (FALSE
			      && (temp *=
				  local_search.lamda_prec) >
			      local_search.best_cost)
			    return temp;	// Ho superato il cost limite e quindi non ricerco ulteriormente 

			}
		    }
		  else if (GpG.accurate_cost == COMPUTE_ADD_COST)
		    {
		      prec += temp;

		      best_prec_cost.weight += loc_n_cost.weight;

		      best_prec_cost.act_cost += loc_n_cost.act_cost;

		      best_prec_cost.act_time += loc_n_cost.act_time;


		    }


		}

#ifdef __TEST__
	      else
		MSG_ERROR ("Max act cost precond");
#endif

	    }

	  // precondizioni at_end
	  for (j = 0; j < gef_conn[act->position].sf->num_PC_end; j++)
	    {
	      el = gef_conn[act->position].sf->PC_end[j];

	      if (el < 0)
		{

		  loc_n_cost.weight = 0.0;
		  loc_n_cost.act_cost = 0.0;
		  loc_n_cost.act_time = 0.0;
		  //Costo per rendere vere le precondizioni 
		  //creo un fatto fittizio, tanto le uniche info che servono sono position e level
		  fact.position = el;
		  /*
		    loc_n_cost indica il costo di ricerca, di esecuzione e istante finale associato all'azione che rende vero il fatto considerato
		    Azzero loc_n_cost
		  */
		  loc_n_cost.weight = 0.0;
		  loc_n_cost.act_cost = 0.0;
		  loc_n_cost.act_time = 0.0;

		  temp =compute_relaxed_fact_cost (fact.position, *fact.level, &loc_n_cost, level, 0.0);
		  if (GpG.accurate_cost == COMPUTE_MAX_COST)
		    {
		      if (best_prec_cost.act_cost < loc_n_cost.act_cost
			  && loc_n_cost.act_cost < MAX_COST)
			best_prec_cost.act_cost = loc_n_cost.act_cost;
		      if (best_prec_cost.act_time < loc_n_cost.act_time
			  && loc_n_cost.act_time < MAX_COST)
			best_prec_cost.act_time = loc_n_cost.act_time;
		      if (prec < temp && temp < MAX_COST)
			{
			  prec = temp;
			  best_prec_cost.weight = loc_n_cost.weight;
			}
		    }
		  else if (GpG.accurate_cost == COMPUTE_ADD_COST)
		    {
		      prec += temp;
		      best_prec_cost.weight += loc_n_cost.weight;
		      best_prec_cost.act_cost += loc_n_cost.act_cost;
		      best_prec_cost.act_time += loc_n_cost.act_time;
		    }
		  continue;

		}

	      if (is_fact_in_additive_effects_start (act->position, el))
		continue;


	      if (CHECK_FACT_POS (el, level))
		{
		  if (DEBUG4)
		    {
		      printf ("\n\n %d +++++ MAX_COST Prec_end  Act %s ",
			      ++diff, print_op_name_string (act->position,
							    temp_name));
		      printf ("\n  fact %s\n",
			      print_ft_name_string (el, temp_name));
		    }

		  loc_n_cost.weight = 0.0;

		  loc_n_cost.act_cost = 0.0;

		  loc_n_cost.act_time = 0.0;


		  //Costo per rendere vere le precondizioni 
		  inf_fact = CONVERT_FACT_TO_NODE (el, level);
		  temp = compute_max_fact_cost (inf_fact, &loc_n_cost, level);

		  if (GpG.accurate_cost == COMPUTE_MAX_COST
		      && inf_fact->w_is_true <= 0)
		    unsat_facts++;

		  if (DEBUG4)
		    {
		      printf ("\n\n %d +++ MAX_COST Prec_end  Act %s ",
			      ++diff, print_op_name_string (act->position,
							    temp_name));
		      printf
			("\n  fact %s, COST  weight %f cost %f time %f unsatisf_prec %d ",
			 print_ft_name_string (el, temp_name),
			 loc_n_cost.weight, loc_n_cost.act_cost,
			 loc_n_cost.act_time, unsat_facts);
		    }

		  if (GpG.accurate_cost == COMPUTE_MAX_COST)
		    {

		      if (best_prec_cost.act_cost < loc_n_cost.act_cost
			  && loc_n_cost.act_cost < MAX_COST)
			best_prec_cost.act_cost = loc_n_cost.act_cost;


		      if (best_prec_cost.act_time < loc_n_cost.act_time
			  && loc_n_cost.act_time < MAX_COST)
			best_prec_cost.act_time = loc_n_cost.act_time;


		      if (prec < temp && temp < MAX_COST)
			{
			  prec = temp;
			  best_prec_cost.weight = loc_n_cost.weight;

			  if (FALSE
			      && (temp *=
				  local_search.lamda_prec) >
			      local_search.best_cost)
			    return temp;	// Ho superato il cost limite e quindi non ricerco ulteriormente 

			}
		    }
		  else if (GpG.accurate_cost == COMPUTE_ADD_COST)
		    {
		      prec += temp;

		      best_prec_cost.weight += loc_n_cost.weight;

		      best_prec_cost.act_cost += loc_n_cost.act_cost;

		      best_prec_cost.act_time += loc_n_cost.act_time;


		    }


		}

#ifdef __TEST__
	      else
		MSG_ERROR ("Max act cost precond");
#endif

	    }
	}

      /* end azioni durative */


      total = prec_par * prec;
      precond = local_search.lamda_prec * total;

      if (DEBUG4)
	printf ("\n\n<< Evalutate precondition END");

      if (DEBUG3)
	printf ("  Temp Num. P: %f", prec);

    }

  /* Counts the number of ME actions with the current one */

  if (excl_par)
    {
      if (DEBUG4)
	{
	  printf ("\n\n %d +++++ MAX_COST Mutex  Act :", ++diff);
	  print_op_name (neighb_act->act_pos);
	}

      temp = count_mutex_action (act->position, level);

      mutex = excl_par * temp;	//  LM 
      total += mutex;
      mutex*= local_search.lamda_me; //LM

    }

  if (DEBUG4)
    printf ("\n\n<< Evalutate mutex END");

  if (DEBUG3)
    printf ("  Temp  ME: %f", temp);




  best_eff_cost.weight = 0.0;

  best_eff_cost.act_cost = 0.0;

  best_eff_cost.act_time = 0.0;

  /* define the cost of Add_effect critics nodes */
  /* a fact is a true critic node if it is precondition of almost an action */
  /* of the next level and it's supported from only one action */

  /* a fact is a false critic node if it is precondition of almost an action */
  /* of the next level and it's not supported */

  if (add_effect_par)
    {
      next_level = level + 1;
      if (neighb_act->constraint_type == C_T_REMOVE_ACTION)
	{

	  unsat_facts = 0;

#ifdef TEST_GR
	  printf ("\n MAX action cost level %d", level);
	  check_plan (GpG.curr_plan_length);
#endif

	  remove_temp_action (neighb_act->act_pos, neighb_act->act_level);	// Rimuovo temporaneamente l'azione per calcolare il costo di rendere veri gli effetti additivi critici 

	}
      eff = 0.0;
      for (i = 0; i < gef_conn[neighb_act->act_pos].num_A; i++)
	{
	  fact_pos = gef_conn[neighb_act->act_pos].A[i];

	  if (fact_pos < 0)
	    continue;

	  loc_n_cost.weight = 0.0;
	  loc_n_cost.act_cost = 0.0;
	  loc_n_cost.act_time = 0.0;

	  if (neighb_act->constraint_type == C_T_REMOVE_ACTION)
	    {

	      if (CONVERT_FACT_TO_NODE (fact_pos, next_level)->w_is_true ==
		  1
		  && CONVERT_FACT_TO_NODE (fact_pos, next_level)->w_is_goal)
		{
		  // Trovo il primo livello in cui questo fatto diventerebbe una precondizione non supportata 

		  if (next_level > GpG.curr_plan_length)
		    {
#ifdef __TEST__
		      if (DEBUG2)
			MSG_ERROR ("Fact precondition of NO action");
#endif
		      continue;

		    }

#ifdef __TEST__
		  else if (DEBUG2)
		    {
		      if (GET_ACTION_POSITION_OF_LEVEL (next_level) >= 0)
			printf
			  ("\n Fact %s precondition of action %s at level %d",
			   print_ft_name_string (fact_pos, temp_name),
			   print_op_name_string (GET_ACTION_POSITION_OF_LEVEL
						 (next_level), temp_name),
			   next_level);
		      else
			printf
			  ("\n Fact %s precondition of no action  at level %d",
			   print_ft_name_string (fact_pos, temp_name),
			   next_level);
		      printf ("\n %d COMPUTE MAX COST EFF ACT %s fact %s",
			      ++diff, print_op_name_string (act->position,
							    temp_name),
			      print_ft_name_string (fact_pos, temp_name));

		    }

#endif
		  if (DEBUG4)
		    {
		      printf ("\n\n %d +++++ MAX_COST End_eff  Act %s",
			      ++diff,
			      print_op_name_string (neighb_act->act_pos,
						    temp_name));
		      printf ("\n  fact %s\n",
			      print_ft_name_string (fact_pos, temp_name));
		    }

		  temp =
		    compute_max_fact_cost (CONVERT_FACT_TO_NODE
					   (fact_pos, next_level),
					   &loc_n_cost, level);

		  if (GpG.accurate_cost == COMPUTE_MAX_COST && CONVERT_FACT_TO_NODE (fact_pos, next_level)->w_is_true <= 1)	// il fatto e' supportato unicamente dalla azione che si vuole rimuovere 
		    unsat_facts++;

		}

	    }
	  else
	    {
	      if (CONVERT_FACT_TO_NODE (fact_pos, next_level)->w_is_true ==
		  0
		  && CONVERT_FACT_TO_NODE (fact_pos, next_level)->w_is_goal)
		{

#ifdef __TEST__
		  if (DEBUG2)
		    printf ("\n %d COMPUTE MAX COST EFF ACT %s fact %s",
			    ++diff, print_op_name_string (act->position,
							  temp_name),
			    print_ft_name_string (fact_pos, temp_name));
#endif

		  if (DEBUG4)
		    {
		      printf ("\n\n %d +++++ MAX_COST End_eff  Act %s",
			      ++diff,
			      print_op_name_string (neighb_act->act_pos,
						    temp_name));
		      printf ("\n  fact %s\n",
			      print_ft_name_string (fact_pos, temp_name));
		    }


		  temp =
		    compute_max_fact_cost (&vectlevel[next_level]->
					   fact[fact_pos], &loc_n_cost,
					   next_level);

		}
	    }

	  if (DEBUG4)
	    {
	      printf ("\n\n %d END MAX_COST End_eff Act: %s ", ++diff,
		      print_op_name_string (neighb_act->act_pos, temp_name));
	      printf ("\n  fact %s, COST  weight %f cost %f time %f",
		      print_ft_name_string (fact_pos, temp_name),
		      loc_n_cost.weight, loc_n_cost.act_cost,
		      loc_n_cost.act_time);
	    }

	  if (GpG.accurate_cost == COMPUTE_MAX_COST)
	    {
	      if (best_eff_cost.act_cost < loc_n_cost.act_cost
		  && loc_n_cost.act_cost < MAX_COST)
		best_eff_cost.act_cost = loc_n_cost.act_cost;


	      if (best_eff_cost.act_time < loc_n_cost.act_time
		  && loc_n_cost.act_time < MAX_COST)
		best_eff_cost.act_time = loc_n_cost.act_time;


	      if (eff < temp && temp < MAX_COST)
		{
		  eff = temp;

		  best_eff_cost.weight = loc_n_cost.weight;


		  effect = temp * local_search.lamda_prec;
		}
	    }
	  else if (GpG.accurate_cost == COMPUTE_ADD_COST)
	    {


	      best_eff_cost.act_cost += loc_n_cost.act_cost;

	      best_eff_cost.act_time += loc_n_cost.act_time;

	      eff += temp;

	      best_eff_cost.weight += loc_n_cost.weight;

	      effect += temp * local_search.lamda_prec;

	    }


	}


      /*  azioni durative */
      // Effetti at start
      if (gef_conn[neighb_act->act_pos].sf != NULL)
	{
	  for (i = 0; i < gef_conn[neighb_act->act_pos].sf->num_A_start; i++)
	    {
	      fact_pos = gef_conn[neighb_act->act_pos].sf->A_start[i];

	      if (is_fact_in_delete_effects (neighb_act->act_pos, fact_pos))
		continue;

	      if (fact_pos < 0)
		continue;

	      loc_n_cost.weight = 0.0;
	      loc_n_cost.act_cost = 0.0;
	      loc_n_cost.act_time = 0.0;

	      if (neighb_act->constraint_type == C_T_REMOVE_ACTION)
		{

		  if (CONVERT_FACT_TO_NODE (fact_pos, next_level)->
		      w_is_true == 1
		      && CONVERT_FACT_TO_NODE (fact_pos,
						 next_level)->w_is_goal)
		    {
		      // Trovo il primo livello in cui questo fatto diventerebbe una precondizione non supportata 

		      if (next_level > GpG.curr_plan_length)
			{
#ifdef __TEST__
			  if (DEBUG2)
			    MSG_ERROR ("Fact precondition of NO action");
#endif
			  continue;

			}

#ifdef __TEST__
		      else if (DEBUG2)
			{
			  if (GET_ACTION_POSITION_OF_LEVEL (next_level) >= 0)
			    printf
			      ("\n Fact %s precondition of action %s at level %d",
			       print_ft_name_string (fact_pos, temp_name),
			       print_op_name_string
			       (GET_ACTION_POSITION_OF_LEVEL (next_level),
				temp_name), next_level);
			  else
			    printf
			      ("\n Fact %s precondition of no action  at level %d",
			       print_ft_name_string (fact_pos, temp_name),
			       next_level);
			  printf ("\n %d COMPUTE MAX COST EFF ACT %s fact %s",
				  ++diff, print_op_name_string (act->position,
								temp_name),
				  print_ft_name_string (fact_pos, temp_name));

			}

#endif


		      if (DEBUG4)
			{
			  printf ("\n\n %d +++++ MAX_COST Start_eff  Act %s",
				  ++diff,
				  print_op_name_string (neighb_act->act_pos,
							temp_name));
			  printf ("\n  fact %s\n",
				  print_ft_name_string (fact_pos, temp_name));
			}


		      temp =
			compute_max_fact_cost (CONVERT_FACT_TO_NODE
					       (fact_pos, next_level),
					       &loc_n_cost, level);

		      if (GpG.accurate_cost == COMPUTE_MAX_COST && CONVERT_FACT_TO_NODE (fact_pos, next_level)->w_is_true <= 1)	// il fatto e' supportato unicamente dalla azione che si vuole rimuovere 
			unsat_facts++;

		    }

		}
	      else
		{
		  if (CONVERT_FACT_TO_NODE (fact_pos, next_level)->
		      w_is_true == 0
		      && CONVERT_FACT_TO_NODE (fact_pos,
						 next_level)->w_is_goal)
		    {

#ifdef __TEST__
		      if (DEBUG2)
			printf ("\n %d COMPUTE MAX COST EFF ACT %s fact %s",
				++diff, print_op_name_string (act->position,
							      temp_name),
				print_ft_name_string (fact_pos, temp_name));
#endif


		      if (DEBUG4)
			{
			  printf ("\n\n %d +++++ MAX_COST Start_eff  Act %s",
				  ++diff,
				  print_op_name_string (neighb_act->act_pos,
							temp_name));
			  printf ("\n  fact %s\n",
				  print_ft_name_string (fact_pos, temp_name));
			}

		      temp =
			compute_max_fact_cost (&vectlevel[next_level]->
					       fact[fact_pos], &loc_n_cost,
					       next_level);

		    }
		}

	      if (DEBUG4)
		{
		  printf ("\n\n %d END MAX_COST Start_eff Act %s ", ++diff,
			  print_op_name_string (neighb_act->act_pos,
						temp_name));
		  printf ("\n  fact %s, COST  weight %f cost %f time %f",
			  print_ft_name_string (fact_pos, temp_name),
			  loc_n_cost.weight, loc_n_cost.act_cost,
			  loc_n_cost.act_time);
		}

	      if (GpG.accurate_cost == COMPUTE_MAX_COST)
		{
		  if (best_eff_cost.act_cost < loc_n_cost.act_cost
		      && loc_n_cost.act_cost < MAX_COST)
		    best_eff_cost.act_cost = loc_n_cost.act_cost;


		  if (best_eff_cost.act_time < loc_n_cost.act_time
		      && loc_n_cost.act_time < MAX_COST)
		    best_eff_cost.act_time = loc_n_cost.act_time;


		  if (eff < temp && temp < MAX_COST)
		    {
		      eff = temp;

		      best_eff_cost.weight = loc_n_cost.weight;


		      effect = temp * local_search.lamda_prec;
		    }
		}
	      else if (GpG.accurate_cost == COMPUTE_ADD_COST)
		{


		  best_eff_cost.act_cost += loc_n_cost.act_cost;

		  best_eff_cost.act_time += loc_n_cost.act_time;

		  eff += temp;

		  best_eff_cost.weight += loc_n_cost.weight;

		  effect += temp * local_search.lamda_prec;

		}


	    }
	}
      /* end azioni durative */

      total += add_effect_par * eff;
      effect *= add_effect_par;	//  LM 

      if (DEBUG4)
	printf ("\n\n<< Evalutate effect END");

      if (DEBUG3)
	printf ("  Temp Add-E: %f, effects %f total %f  ", temp, effect, total );
    }


  // LM Sostituisco il costo ottentuto con i moltiplicatori di lagr a quello 
  // standard se e' impostata la corrispondente modalita' 

  if (GpG.lagrange_multipl)
    total = precond + mutex + effect;

  if (unsat_facts > 1)
    total += (unsat_facts - 1);	// precondiz non supportate - quella di cui si e' fatto il max  

  if (GpG.Twalkplan && GpG.tabu_length >0 && neighb_act->constraint_type == C_T_REMOVE_ACTION)
    {				
      /* 
	 T_walkgraph: increase the cost function of act if it is in
	 the tabu list 
      */      

      diff = GpG.count_num_try - gef_conn[act->position].step;

      if (num_try < GpG.tabu_length)
	total *= GpG.delta * (GpG.tabu_length - num_try);
    }

  if (DEBUG6)
    printf (" -> tot %f", total);


  neighb_act->cost.weight = total;
  neighb_act->cost.act_cost +=
    best_eff_cost.act_cost + best_prec_cost.act_cost;
  neighb_act->cost.act_time +=
    best_eff_cost.act_time + best_prec_cost.act_time;

  if (GpG.num_solutions && neighb_act->constraint_type == C_T_INSERT_ACTION)
    {
      if (GpG.orig_weight_cost > 0 && GpG.best_cost * 1.4 > GpG.total_cost)
	neighb_act->cost.act_cost += get_action_cost (neighb_act->act_pos, neighb_act->act_level, NULL);

      if (GpG.orig_weight_time > 0 && GpG.best_time * 1.4 > GpG.total_time)
	neighb_act->cost.act_time +=
	  (10.0 + get_action_time (neighb_act->act_pos, level));
    }

#ifdef __TEST__
  if (DEBUG2)
    {
      printf ("\n Temp TOTAL COST of %s %f,  ",
	      print_op_name_string (act->position, temp_name), total);
      printf ("\n\n  $$$$$$$ MAX COST inc %.2f cost %.2f time %.2f ",
	      neighb_act->cost.weight, neighb_act->cost.act_cost,
	      neighb_act->cost.act_time);
    }
#endif

#ifdef __TEST__
  check_plan (GpG.curr_plan_length);
#endif

  if (DEBUG4)
    printf ("\n\n<<<< Evalutate action END  Act: %s",
	    print_op_name_string (act->position, temp_name));

  if (DEBUG3)
    printf ("\n -> tot %f", total);

  if (DEBUG4)
    printf
      ("\n--------------------------------------------------------------\n\n");


  return (total);
}
