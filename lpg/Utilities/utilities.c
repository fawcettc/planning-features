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
 * File: utilities.c
 * Description: utilities.
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/



#include <sys/signal.h>
#include <math.h>
#include <values.h>

#ifdef __WINLPG__
#include <time.h>
#endif

#include "lpg.h"
#include "check.h"
#include "mutex.h"
#include "utilities.h"
#include "LocalSearch.h"
#include "ActionSubgraph.h"
#include "output.h"
#include "LpgOutput.h"
#include "LpgTime.h"
#include "numeric.h"
#include "search.h"
#include "inst_utils.h"




/***************************************
            OPTIMIZATION
 ***************************************/




/** OK 03/08/04
 * Name: is_plan_better
 * Scopo: Valuta se la soluzione trovata e' migliore di quelle precedente
 * Tipo: int
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_plan_better
*  Objective: Valutation if the solution found is better than the previous
*  Type: int
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int is_plan_better ()
{
  GpG.store_plan = TRUE;
  /**
     Settiamo la durata totale del piano
     **
     Setting the total duration of the plan 
  **/
  if (GpG.temporal_plan)
    get_total_time_plan ();

  if (GpG.optimize == 0)
    {
      if (DEBUG4)
	printf ("\n\n !!!  Optimize not set => SAVE \n");
      return TRUE;
    }
  /** 
      La prima soluzione deve essere salvata in ogni caso
      **
      The first solution must be saved
  **/
  if (GpG.num_solutions == 0)
    {
      if (DEBUG3)
	printf ("\n\n !!!  Find FIRST solution => SAVE \n");
      return TRUE;
    }
  /**
     Se il piano attuale migliora di TIME_TOLERANCE il best_plan allora il best_plan e' quello attuale
     **
     If the actual plan improves best_plan, then best_plan is the actual
  **/
  if ((GpG.orig_weight_cost * GpG.best_cost + GpG.orig_weight_time * GpG.best_time - TIME_TOLERANCE) >
      (GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time))
    {
      if (DEBUG3)
	printf ("\n\n !!!  Find BETTER solution => SAVE \n");
      return TRUE;
    }
  else
    {
      if ((GpG.orig_weight_cost * GpG.best_cost + GpG.orig_weight_time * GpG.best_time - TIME_TOLERANCE) <
	  (GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time) &&
	  (GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time - TIME_TOLERANCE) < 
	  (GpG.orig_weight_cost * GpG.best_cost + GpG.orig_weight_time * GpG.best_time))
	if (GpG.best_numact > GpG.num_actions)
	  {
	    GpG.store_plan = FALSE;
	    if (DEBUG1)
	      printf("Find EQUAL solution (%.2f), but with LESSER actions %d\n", GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time, GpG.num_actions);
	    return TRUE;
	  }
    }
  
  if (DEBUG3)
    printf ("\n\n !!!  Find WORSE solution => OPTIMIZE \n");
  return FALSE;
  
}



/** OK 03/08/04
 * Name: is_quasi_sol_better
 * Scopo:
 * Tipo: int
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_quasi_sol_better
*  Objective:
*  Type: int
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int is_quasi_sol_better ()
{
  /**
     Se il piano attuale migliora di TIME_TOLERANCE il best_plan allora il best_plan e' quello attuale
     **
     If the actual plan improves best_plan, then best_plan is the actual
  **/
  if (GpG.qs_best_timed_inc > GpG.num_false_tmd_fa ||
      ( GpG.qs_best_timed_inc == GpG.num_false_tmd_fa && 
	GpG.qs_best_numact > GpG.num_actions ) )
    {
      if (DEBUG3)
	printf ("\n\n !!!  Find BETTER quasi-solution \n");
      return TRUE;
    }
  
  if (DEBUG3)
    printf ("\n\n !!!  Find WORSE quasi-solution \n");
  return FALSE;
}




/***************************************
            COST - TIME
 ***************************************/




/** OK 03/08/04
 * Name: weight_cost
 * Scopo:
 * Tipo: float
 * Input: node_cost_list n_cost
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: weight_cost
*  Objective:
*  Type: float
*  Input: node_cost_list n_cost
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
float weight_cost (node_cost_list n_cost)
{

  if (GpG.weight_cost < GpG.weight_time)
    return n_cost->act_time;
  else
    return n_cost->act_cost;
}



/** OK 03/08/04
 * Name: reset_fact_costs
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: reset_fact_costs
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void reset_fact_costs ()
{
  register int i;
  for (i = 0; i < GpG.max_num_facts; i++)
    {
      fact_costs[i].weight = -1.0;
      fact_costs[i].act_cost = -1;
    }
}



/** OK 04/08/04 XXXXX
 * Name: get_fact_cost
 * Scopo:
 * Tipo: float
 * Input: int Fact_pos
 *        int level
 *        node_cost_list n_cost
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: get_fact_cost
*  Objective:
*  Type: float
*  Input: int Fact_pos
*         int level 
*         node_cost_list n_cost
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
/*
float get_fact_cost (int Fact_pos, int level, node_cost_list n_cost)
{
  FctNode_list Fact;
  if (Fact_pos < 0)
    return -1.0;
  Fact = CONVERT_FACT_TO_NODE (Fact_pos, level);
  if (Fact->step != num_try)
    {
      n_cost->weight = -1.0;
      n_cost->act_cost = -1.0;
      n_cost->act_time = 0.0;
      return (-1.0);
    }
  n_cost->weight = Fact->cost.weight;
  n_cost->act_cost = Fact->cost.act_cost;
  n_cost->act_time = Fact->cost.act_time;
  return n_cost->weight;
}
*/


/** OK 03/08/04
 * Name: set_fact_cost
 * Scopo:
 * Tipo: void
 * Input: FctNode_list Fact
 *        node_cost_list n_cost
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: set_fact_cost
*  Objective:
*  Type: void
*  Input: FctNode_list Fact
*         node_cost_list n_cost
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
/*
void set_fact_cost (FctNode_list Fact, node_cost_list n_cost)
{
  Fact->step = num_try;

  Fact->cost.weight = n_cost->weight;
  Fact->cost.act_cost = n_cost->act_cost;
  Fact->cost.act_time = n_cost->act_time;

  if (DEBUG5)
    printf
      ("\n Set COST Fact: %s, level %d\n weight %.2f, cost %.2f, time %.2f",
       print_ft_name_string (Fact->position, temp_name), *Fact->level,
       Fact->cost.weight, Fact->cost.act_cost, Fact->cost.act_time);
}
*/


/** OK 03/08/04
 * Name: get_action_cost
 * Scopo: Per avere il costo di ciascuna azione
 * Tipo: float
 * Input: int pos
 *        int *nullcost
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: get_action_cost
*  Objective: To have the cost of any action
*  Type: float
*  Input: int pos
*         int *nullcost
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
float
get_action_cost (int pos, int level, int *nullcost)
{
  float tot = 0.0;
  float opt_funct_before;
  float opt_funct_after;

  if (nullcost != NULL)
    *nullcost = FALSE;

  if (pos < 0)
    return 0.0;

  if (GET_BIT(GpG.variable_cost_actions, pos) && level >= 0)
    {
      /*
	Rivalutare il costo dell'azione!!
      */

      /*
	salva lo stato corrente prima dell'applicazione dell'azione 
	
	save current status before applyng any action
      */
      memcpy (gcomp_var_value_before,  gcomp_var_value, sizeof (float) * gnum_comp_var);
      memcpy (gcomp_var_value, vectlevel[level]->numeric->values, sizeof(float) * gnum_comp_var);

      /*
	salva il valore corrente della funzione di ottimizzazione 
	
	save current optimization function value
      */
      if(goptimization_exp < 0)
	opt_funct_before = 0.0;
      else
	opt_funct_before = eval_comp_var (&gcomp_var[goptimization_exp], goptimization_exp);
      
      /*
	Applico gli effetti numerici di questa azione allo stato numerico corrente
	
	applies numeric effects of this efconn to the current numeric state
	It is necessary for the following evaluations
      */
      apply_numeric_effects_of_efconn (pos);
      
      /*
	Salva il valore corrente della funzione di ottimizzazione dopo l'applicazione degli effetti numerici 
	
	Save the optimization function value after the evaluation of action's numeric effects
      */
      opt_funct_after = eval_comp_var (&gcomp_var[goptimization_exp], goptimization_exp);
      
      /*
	Valuto il costo dell'azione come differenza del valore della funzione di otttimizzazione
	dopo e prima la sua applicazione
	
	Evaluate actions's cost from current and previous value of the optimization function
      */
      
      gef_conn[pos].cost = opt_funct_after - opt_funct_before;
         
      if (fabs(gef_conn[pos].cost) <= MIN_ACTION_COST)
	gef_conn[pos].cost = MIN_ACTION_COST;

      if(GpG.maximize_plan && gef_conn[pos].cost>0)
	gef_conn[pos].cost *= -1;
            
      /* 
	 Ripristina lo stato numerico iniziale
	 
	 Reload previous numeric state
      */
      memcpy(gcomp_var_value, gcomp_var_value_before, sizeof (int) * gnum_comp_var);
    }
  
  if (GpG.optimize == OPT_ACT_COST)
    tot = gef_conn[pos].cost;
  else if (GpG.optimize == OPT_PLAN_SIMILARITY)
    tot = POSITIVE (gef_conn[pos].cost);
  else
    tot = 1.0;
  if (tot == 0.0)
    {
      tot = MIN_ACTION_COST;
      if (nullcost != NULL)
	*nullcost = TRUE;
    }

  return (tot);
}



/** OK 03/08/04
 * Name: get_cond_action_cost
 * Scopo: Per avere il costo di ciascuna azione condizionale
 * Tipo: float
 * Input: int pos
 *        int *nullcost
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: get_cond_action_cost
*  Objective: To have the cost of any conditional action
*  Type: float
*  Input: int pos
*         int *nullcost
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
float get_cond_action_cost (int pos, int *nullcost)
{
  float tot = 0.0;
  if (nullcost != NULL)
    *nullcost = FALSE;
  if (pos < 0)
    return 0.0;
  if (GpG.optimize == OPT_ACT_COST)
    tot = gcondef_conn[pos].cost;
  else
    if (GpG.optimize == OPT_PLAN_SIMILARITY)
      tot = POSITIVE (gcondef_conn[pos].cost);
    else
      tot = 1.0;
  if (tot == 0.0)
    {
      tot = MIN_ACTION_COST;
      if (nullcost != NULL)
	*nullcost = TRUE;
    }
  return (tot);
}



/** OK 03/08/04
 * Name: get_action_time
 * Scopo: Per avere la durata di ciascuna azione
 * Tipo: float
 * Input: int pos
 *        int level
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: get_action_time
*  Objective: To have the duration of any action
*  Type: float
*  Input: int pos
*         int level
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
float get_action_time (int pos, int level)
{
  float tot;
  if (pos < 0)
    return 0.0;
  if (!GpG.durative_actions_in_domain) 
    return STRIPS_ACTIONS_DURATION;
  /**
     se sono presenti azioni a durata variabile...
     **
     if there are not actions with variable duration...
  **/
  if (GpG.variable_duration && level >= 0)
    /**
       controllo se questa azione e' a durata variabile (check se ho allocato il bit array delle vars che influiscono su duration)
       **
       checking if this action is with variable duration
    **/
    if (vectlevel[level] != NULL && gef_conn[pos].duration_rvals != NULL)
      {

#ifdef __TEST__
	if (DEBUG4)
	  {
	    printf ("\n Action %d duration %.2f ", pos, gef_conn[pos].duration);
	    print_op_name (pos);
	  }
#endif

	eval_comp_var_non_recursive (gef_conn[pos].dur_var_index, vectlevel[level]->numeric->values,
				     vectlevel[level]->numeric->values, level, level);
	gef_conn[pos].duration = vectlevel[level]->numeric->values[gef_conn[pos].dur_var_index];
	gef_conn[pos].duration = ROUND_TO_1_1000 (gef_conn[pos].duration);

#ifdef __TEST__
	if (DEBUG4)
	  printf (" end dur %.2f ", gef_conn[pos].duration);
#endif

      }
  if (GpG.optimize == OPT_ACT_COST)
    tot = gef_conn[pos].duration;
  else if (GpG.optimize == OPT_PLAN_SIMILARITY)
    tot = POSITIVE (gef_conn[pos].duration);
  else
    tot = 1.0;
  return (tot);
}




/***************************************
            GOAL AGENDA
 ***************************************/




/** OK 03/08/04 -----------------
 * Name: vectlevelto_planops
 * Scopo: passa il piano tra le due strutture dati allo scopo di aggiornare la struttura gplan_ops
 *        (vectlevel e gplan_ops)
 * Tipo: void
 * Input: int from_level (livello iniziale)
 *        int to_level (livello finale)
 * Output: nessuno
 * Strutture dati principali: vectlevel[]
 *                            gplan_ops[]
 *                            gnum_plan_ops
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: nessuno
**
*  Name: vectlevelto_planops
*  Objective: the plan between the two structures passes gives in order to modernize the structure to you gplan_ops
*             (vectlevel and gplan_ops)
*  Type: void
*  Input: int from_level (level begins them)
*         int to_level (final level)
*  Output: none
*  Main Data Structures: vectlevel[ ]
*                        gplan_ops[ ]
*                        gnum_plan_ops
*  Main Functions Used:
*  Call gives: none
**/
void vectlevel_to_planops (int from_level, int to_level)
{
  /**
   Variabili intere di appoggio utilizzate per scorrere i livelli del piano
   **
   Variable entire of support used in order to slide the levels of the plan
  **/
  int i, j;
  i = from_level;
  j = from_level;
  /**
   Scorro i livelli del piano
   **
   I slide the levels of the plan
  **/
  while (j < to_level)
    {
      /**
	Se i livelli sono maggiori della lunghezza massima del piano si interrompe
	**
	If the levels are greater of the maximum length of the plan it interrupts
      **/
      if (i >= GpG.max_plan_length)
	break;
      /**
	Se non e' un fatto
	**
	If it is not a fact
      **/
      if (vectlevel[i]->action.position != -1)
	{
	  /**
	    Aggirno la struttura gplan_ops[] assegnadogli alla posizione gnum_plan_ops++ (varibile globale che
	    viene incrementata) l'intero corrispondente alla posizione dell'azione
	    **
	    Aggirno the structure gplan_ops[ ] assegnadogli to the position gnum_plan_ops (varibile total that
	    increasing) the entire correspondent to the position of the action comes
	  **/
	  gplan_ops[gnum_plan_ops++] = vectlevel[i]->action.position;
	  j++;
	}
      i++;
    }
}



/** OK 03/08/04 ------------------
 * Name: forward_propagation
 * Scopo: ricalcolare lo stato dopo l'applicazione delle azioni eseguendole dal livello di partenza
 *        (from_level) al livello finale (to_level). Funziona anche con effetti condizionali
 * Tipo: void
 * Input: int from_level (livello iniziale)
 *        int to_level (livello finale)
 * Output: nessuno
 * Strutture dati principali: gplan_ops[]
 * Funzioni principali utilizzate: result_to_dest
 * Chiamata da: main
**
*  Name: forward_propagation
*  Objective:: recalculate the state after the application of the action execute them from the level of departure
*              (from_level) to the final level (to_level).  It works also with effects conditions them
*  Type: void
*  Input: int from_level (level begins them)
*         int to_level (final level)
*  Output: none
*  Main Data Structures: gplan_ops[ ]
*  Main Functions Used: result_to_dest
*  Call gives: main
**/
void forward_propagation (int from_level, int to_level)
{
  int i;
  /**
    Scorro i livelli del piano ed eseguo l'azione presente nel livello. Ad ogni esecuzione viene riaggiornato
    il piano (fatti noop) e determinati nuovi goal
    **
    I slide the levels of the plan and execute the present action in the level.  To every execution it comes riaggiornato
    the plan (made noop) and determines to you new goal
  **/
  for (i = from_level; i < to_level; i++)
    result_to_dest (&(gplan_states[i + 1]), &(gplan_states[i]), gplan_ops[i]);
}



/** OK 03/08/04
 * Name: add_planactions_to_planactions
 * Scopo: Concatenazione di due piani passati in ingresso con aggiornamento temporale. Il piano plan_to_add viene posto
 *        in coda al pino first_plan
 * Tipo: void
 * Input: PlanAction * plan_to_add (struttura rappresentante il piano da aggiungere)
 *        PlanAction * first_plan (struttura rappresentante il piano originale)
 * Output: nessuno
 * Strutture dati principali: PlanAction
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: main
**
*  Name: add_planactions_to_planactions
*  Objective: Concatenation of two plans passes to you in income with temporal modernization.  The plan plan_to_add comes place
*             in tail to the pine first_plan
*  Type: void
*  Input: PlanAction * plan_to_add (structure representative the plan to add)
*         PlanAction * first_plan (structure representative the plan originates them)
*  Output: none
*  Main Data Structures: PlanAction
*  Main Functions Used: none
*  Call gives: main
**/
void add_planactions_to_planactions (PlanAction * plan_to_add, PlanAction * first_plan)
{
  /**
    Variabili di appoggio
    **
    Variable of support
  **/
  PlanAction *pa;
  float incr_start_time;
  /**
     se il piano da aggiungere e' vuoto, oppure il piano origianale e' vuoto, esce
     **
     if the adding plan is empty, or the original plan is empty, it exit
  **/
  if ((!plan_to_add) || (!first_plan))
    return;
  /**
     trova l'ultima azione del piano first_plan
     **
     Finding the last action of the first_plan plan
  **/
  pa = first_plan;
  while (pa->next)
    pa = pa->next;
  /**
     concatenazione vera e propria
     **
     concatenation
  **/
  pa->next = plan_to_add;
  plan_to_add->previous = pa;
  incr_start_time = pa->start_time + pa->duration;
  for (pa = plan_to_add; pa; pa = pa->next)
    {
      pa->start_time += incr_start_time;
    }
}




/***************************************
            LOAD PLAN
 ***************************************/




/** OK 03/08/04
 * Name: restore_empty_action_graph
 * Scopo: State * start_state
 *        State * end_state
 * Tipo: void
 * Input:
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: restore_empty_action_graph
*  Objective: State * start_state
*             State * end_state
*  Type: void
*  Input:
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void restore_empty_action_graph(State * start_state, State * end_state)
{
  int time, i, j, num, num_unsupported;
  FtConn *vertex_ft;
  FctNode_list fa;
  FctNode_list false_init_facts[MAX_FALSE];

#ifdef __MY_OUTPUT__
  //  if (DEBUG1)
    printf ("\n LOAD QUASI-SOL: ");
#endif

  time = GpG.input_plan_lenght;
  GpG.curr_plan_length = GpG.input_plan_lenght;

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
  
  num_unsupported = 0;
  for (i = 0; i < end_state->num_F; i++)
    if(end_state->F[i]>=0)
    {
      vertex_ft = &gft_conn[end_state->F[i]];
      CONVERT_FACT_TO_VERTEX (end_state->F[i])->lamda_prec = CONVERT_FACT_TO_VERTEX (end_state->F[i])->lamda_me = 1.0;	//  LM
      CONVERT_FACT_TO_NODE (end_state->F[i], time)->w_is_goal = TRUE;
      CONVERT_FACT_TO_NODE (end_state->F[i], time)->w_is_used = TRUE;	/**
									   Usato per la propagazione delle noop
									   **
									   Used for the noop propagation
									**/
      insert_unsup_fact (CONVERT_FACT_TO_NODE (end_state->F[i], time));
      false_init_facts[num_unsupported] = CONVERT_FACT_TO_NODE (end_state->F[i], time);
      num_unsupported++;
      vectlevel[time]->prec_vect[GUID_BLOCK (vertex_ft->position)] |= GUID_MASK (vertex_ft->position);
      vectlevel[time]->false_crit_vect[GUID_BLOCK (vertex_ft->position)] |= GUID_MASK (vertex_ft->position);

      //ci andra' la propagazione indietro delle precondizioni
      backward_precond_propagation (CONVERT_FACT_TO_NODE(end_state->F[i], time));
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
	vectlevel[time]->numeric->w_is_goal[j]++;
	if(!is_num_prec_satisfied (j, time))
	  insert_unsup_numeric_fact( j,time);
      }
  vectlevel[time]->num_prec = num_unsupported;
  GpG.num_prec = num_unsupported;
  if (GpG.temporal_plan)
    GpG.forward_time = 1;

  /* setup the intial facts: lookup global
   * fact strings from fact_table[0]
   */

  for (num = 0, i = 0; i < start_state->num_F; i++, num++)
    {
      vertex_ft = &gft_conn[start_state->F[i]];
      (fa = CONVERT_FACT_TO_NODE (start_state->F[i], 0))->w_is_true = TRUE;
      vectlevel[0]->fact_vect[GUID_BLOCK (vertex_ft->position)] |=
	GUID_MASK (vertex_ft->position);
      if (fa->w_is_goal)
	{
	  vectlevel[0]->true_crit_vect[GUID_BLOCK (vertex_ft->position)] |=
	    (GUID_MASK (vertex_ft->position));
	  vectlevel[0]->false_crit_vect[GUID_BLOCK (vertex_ft->position)] &=
	    ~(GUID_MASK (vertex_ft->position));
	}
      /**
	 propagazione delle noop dei fatti iniziali
	 **
	 propagation of the noop of the initial facts
      **/
      if(GpG.timed_facts_present)
	{
	  if (gft_conn[start_state->F[i]].fact_type == IS_TIMED)
	    continue;
	}
      forward_noop_propagation (start_state->F[i], 0);
      {
	vectlevel[0]->fact[start_state->F[i]].time_f = 0.0;
	vectlevel[0]->fact[start_state->F[i]].action_f = NULL;
	forward_noop_propagation_time (&vectlevel[0]->noop_act[start_state->F[i]]);
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

  vectlevel[0]->num_fact = num;
}
  

  
/** OK 03/08/04
 * Name: load_quasi_sol
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: load_quasi_sol
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void load_quasi_sol()
{
  int i;
  NoopNode_list tofix;
  PlanAction *temp_act;
  if (DEBUG2)
    printf ("\n   ==> Insert action from stored plan in present plan\n ");
  for (temp_act = GpG.gplan_actions, i = 0; temp_act;
       temp_act = temp_act->next, i++)
    {
      if (DEBUG2)
	printf ("\nInitialize->insert action %s  in level %d", print_op_name_string (temp_act->act_pos, temp_name), i);
      GpG.num_false_tot = (GpG.num_false_act + GpG.num_false_fa + GpG.num_false_num_fa + GpG.num_false_tmd_fa);
      if(i>=gef_conn[temp_act->act_pos].level)
	insert_remove_action (temp_act->act_pos, i, C_T_INSERT_ACTION, GpG.approximation_level);
      GpG.num_false_tot =
	(GpG.num_false_act + GpG.num_false_fa + GpG.num_false_num_fa + GpG.num_false_tmd_fa);
    }
  while (GpG.num_false_act > 0)
    {
      tofix = CONVERT_NOOP_TO_NODE (treated_c_l[0]->fact, *treated_c_l[0]->level);
      if (define_neighborhood_for_threats (tofix, GpG.curr_plan_length) <= 0)
	remove_treated_noop (tofix);
    }
  GpG.num_false_tot = (GpG.num_false_act + GpG.num_false_fa + GpG.num_false_num_fa + GpG.num_false_tmd_fa);

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
}



/** OK 03/08/04 -----------------
 * Name: get_index_of_constant
 * Scopo: ricavo l'indice corrispondente a una costante del problema di pianificazione
 * Tipo: int
 * Input: char *egg
 * Output: restituisce l'indice (della struttura gconstants) corrispondente alla costante cercata
 *         -1 in caso che la costante non compaia nella struttura gconstants[]
 * Strutture dati principali: gnum_constants
 *                            gconstants[]
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: init_act_vect
**
*  Name:  get_index_of_constant
*  Objective: Obtaining the index of the constant of the planning problem
*  Type: int
*  Input: char *egg
*  Output: it gives back to the index (of the structure gconstants) correspondent to the tried constant
*          -1 in case that the constant does not appear in the structure gconstants[ ]
*  Main Data Structures: gnum_constants
*  Main Functions Used: none
*  Call gives: init_act_vect
**/
int get_index_of_constant (char *arg)
{
  int i;
  /**
    Scorro la struttura gconstants e confronto ogni suo elemento con quello in esame
    **
    I slide the structure gconstants and every comparison its element with that one in examination
  **/
  for (i = 0; i < gnum_constants; i++)
    {
      if (strcmp (gconstants[i], arg) == SAME)
	return i;
    }
  printf
    ("\n\nget_index_of_constant: constant name %s not found in params\n\n",
     arg);
  exit (1);
  return -1;
}



/** OK 03/08/04 --------------
 * Name: open_plan_file
 * Scopo: Aprire il file di ingresso
 * Tipo: FILE
 * Input: char *file_name
 * Output: Il puntatore al file
 * Strutture dati principali: nessuna
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: load_pddl2_plan
**
*  Name: open_plan_file
*  Objective: Opening the file in input
*  Type: FILE
*  Input: char *file_name
*  Output: The pointer to the file
*  Main Data Structures: none
*  Main Functions Used: none
*  Call gives: load_pddl2_plan
**/
FILE *open_plan_file (char *file_name)
{
  FILE *fp;
  fp = fopen (file_name, "r");
  if (fp == NULL)
    {
      printf ("\nGPG: can't find plan file %s ! \n\n", file_name);
      exit (2);
    }
  return (fp);
}



/** OK 03/08/04 --------------
 * Name: extract_level
 * Scopo: determinare il numero (double) corrispondente alla stringa passata in ingresso. Funzione utilizzata per determinare il
 *        tipo di azione presente nel file (pddl)
 * Tipo: float
 * Input: char *cStr
 * Output: il float corrispondente al puntatore alla stringa
 * Strutture dati principali:
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: init_act_vect
**
*  Name:  extract_level
*  Objective: to determine the number (double) correspondent to tightens in input. Function used to determine the type of action in the file (pddl)
*  Type: float
*  Input: char *cStr
*  Output: float correspondent to the pointer of the string
*  Main Data Structures:
*  Main Functions Used: none
*  Call gives: init_act_vect
 **/
float extract_level (char *cStr)
{
  int n;
  float m;
  char push;
  n = strlen (cStr) - 1;
  push = cStr[n];
  cStr[n] = '\n';
  m = atof (cStr);
  cStr[n] = push;
  return (m);
}



/** OK 03/08/04 --------------
 * Name: get_action_index
 * Scopo: Determinare l'indice (intero) corrispondente ad una azione del problema di pianificazione
 * Tipo: int
 * Input: char *opname
 *        int *index_of_arg
 * Output: l'indice corrispondente ad un'azione
 *         -1 se non e' stato trovata l'azione
 * Strutture dati principali: gef_conn
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: init_act_vect
**
*  Name:  get_action_index
*  Objective: To determine the index (entire) correspondent to one action of the planning problem
*  Type: int
*  Input: char *opname
          int *index_of_arg
*  Output: the index correspondent to an action
*          -1 if the action is not found
*  Main Data Structures: gef_conn
*  Main Functions Used: none
*  Call gives: init_act_vect
**/
int get_action_index (char *opname, int *index_of_arg)
{
  /**
    Variabili di appoggio
    **
    Variable of support
  **/
  int i, j;

  //non ho trovato un modo piu semplice per trovare il nome dell'operatore che scandire tutti i gef_conn...
  //alternativa: passare la stringa e usare print_op_name_string
  //per tutti gli efconn
  /**
    Scandisco le azioni istanziate
    **
    Scanning the set actions
  **/
  for (i = 0; i < gnum_ef_conn; i++)
    {
      /**
	 se nome operatore diverso, passa al prossimo ef_conn
	 **
	 if the name of the operator is different, it goes to the next ef_conn
      **/
      if (strcmp (opname, gop_conn[gef_conn[i].op].action->name) != SAME)
	continue;
      /**
	 confronta gli argomenti
	 **
	 comparing the argoments
      **/
      for (j = 0; j < gop_conn[gef_conn[i].op].action->num_name_vars; j++)
	/**
	   se l'indice degli argomenti nella stessa posizione non coincide, fai break
	   **
	   if the index of the arguments in the same position is not equal, it breaks
	**/
	if (index_of_arg[j] !=
	    gop_conn[gef_conn[i].op].action->name_inst_table[j])
	  break;
      /**
	 se ho finito senza fare break, ho trovato l'ef_conn giusto!!!
	 **
	 if there are no break, we have the correct ef_conn
      **/
      if (j == gop_conn[gef_conn[i].op].action->num_name_vars)
	return i;
    }
  /**
    Se non si trova l'azione
    **
    If the action is not found
  **/
  return -1;
}



/** OK 03/08/04
 * Name: init_act_vect
 * Scopo: Ricavare dal file di ingresso il piano (inserimento di azioni nella struttura plan_actions) da eseguire (tenendo
 *        eventualmente presente la durata delle azioni)
 * Tipo: int
 * Input: char *plan_file
 *        PlanAction ** plan_actions
 *        int start_level
 * Output: Il numero di livelli (int level) del piano
 * Strutture dati principali: GpG
 *                            PlanAction
 * Funzioni principali utilizzate: get_index_of_constant
 *                                 get_action_index
 *                                 insert_action_vect
 * Chiamata da: load_pddl2_plan
**
*  Name: init_act_vect
*  Objective: To obtain from the input file the plan (insertion of actions in the structure plan_actions) to execute (holding
*         eventually present the duration of the actions)
*  Type: int
*  Input: char *plan_file
*         PlanAction ** plan_actions
*         int start_level
*  Output: The number of levels
*  Main Data Structures: GpG
*                        PlanAction
*  Main Functions Used: get_index_of_constant
*                       get_action_index
*                       insert_action_vect
*  Call gives: load_pddl2_plan
**/
int init_act_vect (FILE * fp, PlanAction ** plan_actions, int start_level)
{
  /**
    Variabili di appoggio
    **
    Variable of support
  **/
  float start_time;
  char Str[MAX_LENGTH];
  char opname[MAX_LENGTH];
  char operands[MAX_ARITY][MAX_LENGTH];
  float duration;
  /**
    numero di azioni presenti nel file
    **
    number of actions in the file
  **/
  int num_operands = 0;
  int act_pos;
  /**
    vettore in cui verranno caricate le azioni che costituiranno il piano
    **
    array in which will be loaded the actions that will make the plan
  **/
  int index_of_arg[MAX_ARITY];
  char *cStr, *ptchr;
  int i;
  /**
    Livelli di cui sara' composto il piano
    **
    Number of level of the plan
  **/
  int level = 0;
  /**
    variabile che determinera' se considerare o meno la durata delle azioni
    **
    variable that will determine if to consider or not the duration of the actions
  **/
  Bool no_dur;
  printf("\n Load input plan:\n");
  /**
    Scorro tutto il file fp
    **
    Sliding all the fp file
  **/
  while (!feof (fp))
    {
      cStr = Str;
      /**
	Assegno a cStr una riga del file
	**
	Assigning to cStr one line of the file
      **/
      fgets (cStr, MAX_LENGTH, fp);
      for (i = 0; i < MAX_LENGTH; i++)
	/**
	  Converte in maiuscolo
	  **
	  It converts in capital
	**/
	cStr[i] = toupper (cStr[i]);
      /**
	Se ho una riga vuota o un commento
	**
	If I have one empty line or a comment
      **/
      if ((cStr[0] == ';') || (cStr[0] == '\n') || (cStr[0] == '\0'))
	continue;
      num_operands = 0;
      start_time = extract_level (cStr);
      /**
	Salta il carattere :
	**
	It jumps the character:
      **/
      cStr = strchr (cStr, ':');
      if (cStr == NULL)
	continue;
      cStr++;
      /**
	 skippa parentesi
	 **
	 jumping parenthesis
      **/
      while (TRUE)
	{
	  if ((cStr[0] == '(') || (cStr[0] == ' '))
	    {
	      cStr++;
	      continue;
	    }
	  if (cStr[0] == '\0')
	    {
	      printf ("init_act_vect: opname not found (not even '(' )\n");
	      exit (1);
	    }
	  break;
	}
      /**
	 nome operatore
	 **
	 operator name
      **/
      sscanf (cStr, "%s", opname);
      if (strlen (opname) == 0)
	{
	  printf ("init_act_vect: opname not found\n");
	  exit (1);
	}
      cStr += strlen (opname);
      /**
	 skippa spazi
	 **
	 jumping spaces
      **/
      while (TRUE)
	{
	  if (cStr[0] == ' ')
	    {
	      cStr++;
	      continue;
	    }
	  break;
	}
      /**
	 nome argomenti
	 **
	 argoments name
      **/
      while (TRUE)
	{
	  sscanf (cStr, "%s", operands[num_operands]);
	  /**
	     toglie eventuale parentesi attaccata
	     **
	     removing any possible parenthesis
	  **/
	  for (i = 0; i < strlen (operands[num_operands]); i++)
	    if (operands[num_operands][i] == ')')
	      {
		operands[num_operands][i] = '\0';
		break;
	      }
	  if (strlen (operands[num_operands]) == 0)
	    {
	      printf ("init_act_vect: ')' not found\n");
	      exit (1);
	    }
	  index_of_arg[num_operands] =
	    get_index_of_constant (operands[num_operands]);
	  if (index_of_arg[num_operands] == -1)
	    {
	      printf ("\n\nArg not found in constants table!\n\n");
	      exit (1);
	    }
	  cStr += strlen (operands[num_operands]);
	  num_operands++;
	  /**
	     skippa spazi
	     **
	     jumping spaces
	  **/
	  while (TRUE)
	    {
	      if (cStr[0] == ' ')
		{
		  cStr++;
		  continue;
		}
	      break;
	    }
	  if (cStr[0] == ')')
	    break;
	}
      no_dur = FALSE;
      while (TRUE)
	{
	  if (cStr[0] == '\0')
	    {
	      no_dur = TRUE;
	      break;	 
	    }
	  if (cStr[0] != '[')
	    {
	      cStr++;
	      continue;
	    }
	  break;
	}
      cStr++;
      for (ptchr = cStr;; ptchr++)
	{
	  if (ptchr[0] == ']')
	    {
	      ptchr[0] = '\0';
	      break;
	    }
	  if (ptchr[0] == '\0')
	    {
	      no_dur = TRUE;
	      break;
	    }
	}
      if (no_dur ==TRUE)
	duration = 1;
      else
	duration = atof (cStr);
      /**
	Ricavo la posizione corrispondente all'azione dalla struttura index_of_arg in posizione opname
	**
	Revenue the position correspondent to the action from the structure index_of_arg in position opname
      **/
      act_pos = get_action_index (opname, index_of_arg);
      /**
	Se act_pos non corrisponde ad una azione esce
	**
	If act_pos does not correspond to an action it exits
      **/
      if (act_pos == -1)
	{
	  printf ("\n\naction not found in gef_conns\n\n");
	}
      /**
	Se act_pos e' una azione viene inserita nel piano
	**
	If act_pos is an action, it is inserted in the plan
      **/
      if (act_pos != -1)
	{
	  /**
	    Inserimento nel piano (plan_actions) dell'azione
	    **
	    Insertion in the plan (plan_actions) of the action
	  **/
	  store_action_vect (plan_actions, act_pos, start_time, duration);
	  level++;
#ifdef __RETR
	  printf("\n inserted action : \n");
	  print_op_name(act_pos);
#endif
	}
    }
  {
    PlanAction *p;
    printf ("\n");
    for (p = *plan_actions; p; p = p->next)
      {
	printf ("\n");
	printf ("%5.2f: (", p->start_time);
	print_op_name (p->act_pos);
	printf (") [%5.2f ]", p->duration);
      }
    printf ("\n\n");
  }
  /** 
    Restituisce il numero di livelli del piano 
    **
    It gives back the number of levels of the plan
  **/
  return level;
}



/** OK 03/08/04 -------------------
 * Name: load_pddl2_plan
 * Scopo: Caricare un piano in formato PDDL per adattamento di piani
 * Tipo: int
 * Input: char *plan_file
 *        PlanAction ** plan_actions
 *        int start_level
 * Output: restituisce la lunghezza del piano (numero di livelli) associato al file e alla struttura **plan_action
 * Strutture dati principali: GpG
 *                            PlanAction
 * Funzioni principali utilizzate: open_plan_file
 *                                 init_act_vect
 * Chiamata da: main
**
*  Name: load_pddl2_plan
*  Objective: To load a plan in PDDL format
*  Type: int
*  Input: char * plan_file
*         PlanAction ** plan_actions
*         int start_level
*  Output: returns the lenght of the plan (number of levels) associated at the file and the **plan_action structure
*  Main Data Structures: GpG
*                        PlanAction

*  Main Functions Used: open_plan_file
*                       init_act_vect
*  Call gives:
**/
int load_pddl2_plan (char *plan_file, PlanAction ** plan_actions, int start_level)
{
  /**
    Variabili di appogio
    **
    Variable of appogio
  **/
  int plan_length;
  FILE *pFile;

  /**
    Apertura del file *plan_file
    **
    Opening of the *plan_file file
  **/
  pFile = open_plan_file (plan_file);
  /**
    Caricamento delle azioni presenti nel piano di input
    **
    Loading the actions in the input plan
  **/
  GpG.input_plan_lenght = plan_length =
    init_act_vect (pFile, plan_actions, start_level);
  /**
    Chiusura del file
    **
    Closing file
  **/
  fclose (pFile);
  GpG.initialize = PLAN_ADAPT;
  /**
    Restituisce la lunghezza del piano
    **
    It gives back the length of the plan
  **/
  return (plan_length);
}




/***************************************
           VECTLEVEL - LIST
 ***************************************/




/** OK 03/08/04 -------------------
 * Name: new_PlanAction
 * Scopo: associa i valori ad un elemento PlanAction ove i dati relativi sono passati in ingresso
 * Tipo: PlanAction *
 * Input: int act_pos
 *        float start_time
 *        float duration
 * Output: la struttura PlanAction associata ad una azione
 * Strutture dati principali: PlanAction
 * Funzioni principali utilizzate: get_action_cost
 * Chiamata da: insert_action_vect
**
*  Name:  new_PlanAction
*  Objective: it associates the values to a PlanAction element where data are passed in input
*  Type: PlanAction *
*  Input: int act_pos
*         float start_time
*         float duration
*  Output: the PlanAction structure associated to one action
*  Main Data Structures: PlanAction
*  Main Functions Used: get_action_cost
*  Call gives: insert_action_vect
**/
PlanAction *new_PlanAction (int act_pos, float start_time, float duration)
{
  /**
    Dai dati relativi all'azione assegno i campi della struttura PlanAction
    **
    From data of the action I assign the fields of the PlanAction structure
  **/
  PlanAction *pa = (PlanAction *) calloc (1, sizeof (PlanAction));
  pa->act_pos = act_pos;
  pa->start_time = start_time;
  pa->duration = duration;
  pa->cost = get_action_cost (act_pos, -1, NULL);
  pa->previous = NULL;
  pa->next = NULL;
  return pa;
}



/** OK 03/08/04 -----------------------
 * Name: insert_plact_after
 * Scopo: Inserire una azione (PlanAction * plAct azione successiva) dopo un'altra (PlanAction * pla_before azione precedente)
 *        nella lista plan_actions
 * Tipo: void
 * Input: PlanAction * plAct
  *       PlanAction * pla_before
 * Output: nessuno
 * Strutture dati principali: PlanAction
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: insert_action_vect
**
*  Name:  insert_plact_after
*  Objective: To insert one action (PlanAction *plAct successive action) after another (PlanAction * pla_before previous action)
*  Type: void
*  Input: PlanAction * plAct
*         PlanAction * Pla_before
*  Output: none
*  Main Data Structures: PlanAction
*  Main Functions Used: none
*  Call gives: insert_action_vect
**/
void insert_plact_after (PlanAction * plAct, PlanAction * pla_before)
{
  /**
    Se il primo elemento della lista e' vuoto
    **
    If the first element of the list is empty
  **/
  if (!pla_before)
    return;
  /**
     caso di lista non vuota
     **
     if the list is not empty
  **/
  /**
     prima metto a posto i puntatori del nuovo elemento
     **
     first we works with the pointers of the new element
  **/
  plAct->next = pla_before->next;
  plAct->previous = pla_before;
  /**
     inserimento effettivo
     **
     effective insertion
  **/
  pla_before->next = plAct;
  /**
    Se vi e' un elemento (della lista) successivo a plAct
    **
    If there is an element (of the list) successive to plAct
  **/
  if (plAct->next)
    plAct->next->previous = plAct;
}



/** OK 03/08/04
 * Name: store_action_vect
 * Scopo:
 * Tipo: void
 * Input: PlanAction ** plan_actions
 *        int act_pos
 *        float start_time
 *        float duration
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: store_action_vect
*  Objective:
*  Type: void
*  Input: PlanAction ** plan_actions
*         int act_pos 
*         float start_time 
*         float duration)
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void store_action_vect (PlanAction ** plan_actions, int act_pos, float start_time, float duration)
{
  PlanAction *plAct, *pl;
  plAct = new_PlanAction (act_pos, ROUND_TO_1_1000(start_time), duration);
  /** 
      individuo dove mettere la nuova azione
      **
      indentifying where put the new action
  **/
  if (*plan_actions == NULL)
    {
      *plan_actions = plAct;
      return;
    }
  for (pl = *plan_actions; pl; pl = pl->next)
    if (pl->next)
      {
	if ((plAct->start_time >= pl->start_time)
	    && (plAct->start_time < pl->next->start_time))
	  {
	    insert_plact_after (plAct, pl);
	    return;
	  }
	if (!pl->next)
	  {
	    insert_plact_after (plAct, pl);
	    return;
	  }
      }
    else
      {
	/**
	   caso di inserimento in testa alla lista
	   **
	   inserting in the head of the list
	**/
	if (plAct->start_time < pl->start_time)
	  {
	    plAct->next = *plan_actions;
	    (*plan_actions)->previous = plAct;
	    *plan_actions = plAct;
	    return;
	  }
	if (!pl->next)
	  {
	    insert_plact_after (plAct, pl);
	    return;
	  }
      }
}



/** OK 03/08/04
 * Name: store_temporal_action_vect
 * Scopo:
 * Tipo: void
 * Input: PlanAction ** plan_actions 
 *        int act_pos 
 *        float start_time 
 *        float duration
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: store_temporal_action_vect
*  Objective:
*  Type: void
*  Input: PlanAction ** plan_actions 
*         int act_pos 
*         float start_time 
*         float duration
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void store_temporal_action_vect (PlanAction ** plan_actions, int act_pos, float start_time, float duration)
{
  PlanAction *plAct;
  static PlanAction *pl;
  plAct = new_PlanAction (act_pos, start_time, duration);
  /** 
      individuo dove mettere la nuova azione
      **
      indentifying where put the new action
  **/
  if (*plan_actions == NULL)
    {
      *plan_actions = plAct;
      pl = plAct;
      return;
    }
  insert_plact_after (plAct, pl);
  pl = plAct;
}



/** OK 03/08/04 ------------------
 * Name: free_gplan_actions
 * Scopo: Svuotare la lista di azioni associata a PlanAction
 * Tipo: void
 * Input: PlanAction * gplan_actions
 * Output: nessuno
 * Strutture dati principali: PlanAction
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: store_curr_plan
**
*  Name:  free_gplan_actions
*  Objective: To empty the list of actions associated to PlanAction
*  Type: void
*  Input: PlanAction * gplan_actions
*  Output: none
*  Main Data Structures: PlanAction
*  Main Functions Used: none
*  Call gives: store_curr_plan
**/
void free_gplan_actions (PlanAction * gplan_actions)
{
  /**
    Variabili di appoggio
    **
    Variable of support
  **/
  PlanAction *ptr, *prev_ptr;
  for (prev_ptr = ptr = gplan_actions; ptr;)
    {
      prev_ptr = ptr;
      ptr = ptr->next;
      free (prev_ptr);
    }
}



/***************************************
           SET PARAMETERS
 ***************************************/



/** OK 03/08/04 -----------
 * Name: initialize_preset_values
 * Scopo: Inizializzare le variabili globali relative alla struttura GpG (dichiarata in walkplan.h)
 * Tipo: void
 * Input: nessuno
 * Output: nessuno
 * Strutture dati principali: GpG
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: main
**
*  Name: initialize_preset_values
*  Objective: Initialize the global variables of the GpG structure (declared in walkplan.h)
*  Type: void
*  Input: none
*  Output: none
*  Main Data Structures: GpG
*  Main Functions Used: none
*  Call gives: main
**/
void initialize_preset_values (void)
{
  GpG.static_noise = FALSE;
  GpG.count_escl = TRUE;
  GpG.numerator = GpG.init_numerator = GpG.orig_numerator = 10;
  GpG.max_numerator = 60;
  GpG.denominator = 100;
  GpG.numrestart = 9;
  GpG.numrun = 5;
  GpG.numtry = 500;
  GpG.assign = 0;
  GpG.choose_1_2_level = 0;
  GpG.best_min_inc = 10;
  GpG.min_inc = 10;
  GpG.prec_par = 1.0;
  GpG.excl_par = 1.0;
  GpG.add_effect_par = 0.0;
  GpG.add_effect_goal = 0.0;

  GpG.used_prec_par = 0.0;
  GpG.used_excl_par = 0.0;
  GpG.used_add_effect_par = 1.0;
  GpG.used_add_effect_goal = 1.0;
  GpG.num_act_cons = 100;
  GpG.weight_fact = 1.0;
  
  //MODIFICHE COCCOLI
  GpG.k_weight_false_fa=1.0;
  GpG.k_weight_false_num_fa=1.0;
  GpG.k_weight_false_act=1.0; 
  GpG.k_weight_false_tmd_fa=1.0;
  GpG.nonuniform_random_incosistence_test=0;

  GpG.init_tabu_length = 5;
  GpG.tabu_length = 5;

  GpG.tabuplan_act = TRUE;
  GpG.tabuplan_fct = TRUE;
  GpG.Twalkplan = FALSE;

  GpG.delta = 2;
  GpG.partial_timeout = MAXINT;
  GpG.timeout = MAXINT;

  GpG.search_type = LOCAL;
  GpG.initialize = INIT_EMPTY_PLAN;	// PLAN_ADAPT; //INIT_MIN_GOAL;
  GpG.levels = FALSE;		//MIN_COST
  GpG.double_move = FALSE;
  GpG.num_false_act = 0;
  GpG.num_false_fa = 0;
  GpG.num_false_tot = 0;
  GpG.noopmode = 0;

  GpG.accurate_cost = COMPUTE_DG_LIST_COST;	//  COMPUTE_MAX_COST;  // FAST_COST; //  COMPUTE_MAX_COST; // ACCURATE_COST;  
  GpG.optimize = OPT_ACT_COST;
  GpG.cost = 1.0;
  GpG.best_cost = GpG.qs_best_cost = MAXFLOAT;
  GpG.best_time = GpG.qs_best_time = MAXFLOAT;
  GpG.best_numact = GpG.qs_best_numact = GpG.qs_best_timed_inc  = MAXINT;

  GpG.orig_weight_cost = GpG.weight_cost = 1.0; // -wcost
  GpG.orig_weight_time = GpG.weight_time = 0.0; // -wtime
  GpG.orig_weight_timed_fa = GpG.weight_timed_fa = 1.0;

  GpG.inc_restart = 1.16;
  GpG.increase_type = 0;
  GpG.down_vectlevel = FALSE;
  GpG.max_num_solutions = 0;
  GpG.incr_mutex = TRUE;
  GpG.consider_current_level = TRUE;
  GpG.approximation_level = 1;
  GpG.temporal_plan = FALSE;	// -temporal
  GpG.do_best_first = TRUE;
  GpG.forward_time = 1;

  GpG.initialize_inc_choice=0;

  GpG.timed_facts_present = FALSE;

  GpG.durative_actions_in_domain = FALSE;
  GpG.variable_duration = FALSE;
  GpG.non_strips_domain = FALSE;
  GpG.temp_plan_actions = (PlanAction *) calloc (1, sizeof (PlanAction));
  GpG.inst_duplicate_param = FALSE;
  GpG.advanced_temporal_setting = 0;
  GpG.verbose = TRUE;
  GpG.info_search = 0;
  GpG.noout = FALSE;
  GpG.out_file_name = FALSE;
  GpG.lowmemory = FALSE;
  GpG.max_cputime_for_local_search = 1200.0; // -1.0;
  GpG.max_cputime = 1800.0;
  GpG.constraint_type = TRUE;
  GpG.max_temp_vect=0;
  GpG.total_time_goal = FALSE;
  GpG.verify_init=0;
  GpG.verify_Af=0;
  GpG.verify_inc_choice=0;
  GpG.cri_evaluate_preconditions= COMPUTE_DG_LIST_COST;
  GpG.H_positive_benefits = TRUE;
  GpG.relaxed_examination_type=0;
  GpG.relax_list_fact_cost=FALSE;
  GpG.evaluation_function=1; /* Different types of evaluation function (normalization coeffcients) */

  GpG.high_cost_restrict_neighb = 3; 
  GpG.num_elem_neighb_restrict = 20;
  GpG.neighb_elements_for_level_restrict = 1;

  GpG.number_restrict_neighb = FALSE;
  GpG.hcost_neighb = TRUE;
  GpG.level_restrict_neighb = TRUE;
  GpG.onlysearchcostx1stsol = TRUE;

  GpG.pop = FALSE;

  GpG.store_plan = TRUE;
  /*
    LM
  */
  GpG.lagrange_multipl = FALSE;
  GpG.sqr_s_s = 0.0000005;	// decremento lm per precondizioni 
  GpG.sqr_s_s_me= GpG.sqr_s_s;	 // decremento lm per mutex
  GpG.s_s_step = 0.001;	  // incremento lm per precondizioni 
  GpG.s_s_step_me =  GpG.s_s_step ;  // incremento lm per mutex
  GpG.lm_multilevel = 0;
  GpG.flag_decr_lm_goal=0;
  GpG.goal_lambda=1.0;
  GpG.cri_update_iterations=0;

  Hvar.dg_inform_array=NULL;
  Hvar.dg_delete_array=NULL;
  Hvar.a_start_level=-1; /* L'azione a_start rende veri tutti i fatti iniziali al livello -1 */

  Numeric.ri_prec_vector=NULL;
  Numeric.num_Pc_ef_matrix.bits=NULL;
  Numeric.Affects_Matrix=NULL;

  GpG.verify_action_remotion_negative_numeric_effects=1;
  GpG.verify_negative_numeric_effects=1;
  Hvar.temp_num_level=NULL;
  Hvar.to_control=NULL;

  GpG.SearchCost_UnsupTimedFact=2.0;

  GpG.cri_initial_or_update=0;
  GpG.cri_update_level=0;

  GpG.mutex_and_additive_effects=TRUE;

  GpG.cri_insertion_add_mutex=0;

  GpG.insert_threated_act_in_neighb=TRUE; // Se TRUE viene inserita nel vicinato l'azione che minaccia  il fatto e la cui rimozione lo renderebbe nuovamente vero 
  GpG.last_succ_restart = 0; // last successfull restart

  GpG.orig_accurate_cost = GpG.accurate_cost;
  GpG.remove_actions_in_next_step = FALSE;

  GpG.neighb_with_timed_fa = TRUE;	
  GpG.zero_num_A =FALSE;

  GpG.penalize_inconsistence_in_relaxed_plan=TRUE;

  noop_free_list =NULL;
  
  Hvar.num_supported_preconds=0;
  Hvar.supported_bit_vect_preconds=Hvar.supported_preconds=NULL;
  GpG.supported_preconds_evaluation=1;

  GpG.num_quasi_solution = FALSE;

  GpG.extended_effects_evaluation=FALSE;

  GpG.splitted_actions = FALSE;

  GpG.accurate_numeric_constraint = FALSE;

  GpG.extended_unsupported_facts = TRUE;
  GpG.extended_unsupported_goals=FALSE;

  GpG.reset_extended_unsupported_facts=FALSE;

  GpG.cri_intermediate_levels=STANDARD_INTERMEDIATE_REACHAB_INFORM ;

  GpG.relaxed_neighborhood_evaluation=FALSE;

  GpG.timed_preconditions = FALSE;

  GpG.is_domain_numeric = FALSE;

  GpG.ls_max_num_flips=-1;

  GpG.save_action_cost_list = FALSE;

  GpG.derived_pred_in_preconds = FALSE;
  
  GpG.conditional_effects_enabled = FALSE;

  GpG.choose_random_fact_from_tuple = TRUE;

  GpG.stop_remove_act=0;

  GpG.avoid_best_action_cycles=FALSE;
  Hvar.best_act_insertion_array=NULL;
  Hvar.best_act_for_fact_array=NULL; 
  Hvar.initial_supported_facts_relaxed_plan_bit_vector=NULL;
  Hvar.total_supported_facts_relaxed_plan_bit_vector=NULL;

  GpG.consider_relaxed_plan_for_inconsistences=FALSE;

  GpG.evaluate_threated_supported_preconds_of_neighb_action=FALSE;

  GpG.no_mutex_with_additive_effects=FALSE;
  
  GpG.evaluate_mutex_for_action_remotion=FALSE;

  GpG.orig_inc_choice =  MIN_LEVEL_MIN_ADDITIVE_ACTIONS;

  GpG.inc_choice_type =  MIN_LEVEL_MIN_ADDITIVE_ACTIONS;

  GpG.numeric_actions = NULL;
  GpG.num_numeric_effects = 0;
  
  GpG.numeric_neighbors_in_down_levels = FALSE; 
 
  GpG.weight_mutex_in_relaxed_plan=1.0;

  GpG.hard_numeric_domain = FALSE;

  GpG.contraddictory_ef_conn = FALSE;

  GpG.try_suspected_actions = TRUE;

  GpG.save_quality_plan_with_different_name = 0;

  GpG.exist_numeric_preconds=0;

  GpG.continuous_effects = NULL;

  GpG.variable_cost_actions = NULL;
}



/** OK 03/08/04
 * Name: set_param
 * Scopo:
 * Tipo: int
 * Input: int num_unsat
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: set_param
*  Objective:
*  Type: int
*  Input: int num_unsat
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int set_param (int num_unsat)  
{
   static int position = 0;
   float mean,  var,  diff;
   int i, min,  max;
   static int unsat_vector[UNS_VECT];
   if (GpG.static_noise==TRUE)
     return TRUE;
   if (position < (UNS_VECT-1) )
     {
       unsat_vector[position++] = num_unsat;
       return TRUE;
     }
   else
    {
      unsat_vector[position] = num_unsat;
      position = 0;
      mean = min = max = unsat_vector[0];
      for (i = 1; i < UNS_VECT; i++)
	mean += unsat_vector[i];
      mean /= (UNS_VECT);

      var = 0.0;
      for (i = 0; i < UNS_VECT; i++)
	{
	  if (unsat_vector[i] < min)
	      min = unsat_vector[i];
	  if (unsat_vector[i] > max)
	    max = unsat_vector[i];	    
	  diff = unsat_vector[i] - mean;
	  var += pow (diff, 2.0);
	}
      var /= (UNS_VECT-1);
      if(DEBUG1)
	printf("\n\n#INC: %d VAR: %.2f", GpG.num_false_tot, var);
      if (DEBUG1 && FALSE)
	{
	  printf ("\nMean %3.3f, var %4.3f, min %d , max %d ", mean, var,
		  min, max);
	  printf (" N %d, L %d \n\n", GpG.numerator, GpG.tabu_length);
	}
      if (var > 1.0)
	{
	  /**
	     if(GpG.numerator != GpG.init_numerator)
	     printf("\n -- %d var %f values", GpG.numerator, var);
	     for(i=0;i<UNS_VECT; i++)
	    printf(" %d,",unsat_vector[i]);
	  **/
	  GpG.numerator = GpG.init_numerator;
	  GpG.tabu_length = GpG.init_tabu_length;
	}       
      else
	{
	  if(GpG.numerator<GpG.max_numerator)
	    {
	      GpG.numerator *= 1.5;
	      GpG.tabu_length *= 1.2;
	    }
	  /**
	  printf("++ %d var %f  VALUES", GpG.numerator, var);
	  for(i=0;i<UNS_VECT; i++)
	    printf(" %d,",unsat_vector[i]);
	  **/
	 }
    }
   return TRUE;
 }



/** OK 03/08/04
 * Name: reset_heuristic_parameters
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: reset_heuristic_parameters
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void reset_heuristic_parameters ()
{
  GpG.accurate_cost = GpG.orig_accurate_cost;
  GpG.inc_choice_type = GpG.orig_inc_choice;
  GpG.numerator = GpG.init_numerator = GpG.orig_numerator;
  GpG.last_succ_restart = 0;
  /**
     Settings for Timed Facts
  GpG.num_quasi_solution = 0;
  GpG.qs_best_numact = GpG.qs_best_timed_inc  = MAXINT;
   **/
}



/** OK 03/08/04 -------------
 * Name: set_heuristic_parameters
 * Scopo: Durante la ricerca cambiamo, a seconda delle scansioni trovate e restart effettuati, i parametri della
 *        ricerca locale, quali l'euristica utilizzata e la strategia di scelta dell'inconsistenza
 * Tipo: void
 * Input: int num_run
 *        int num_sol
 * Output: nessuno
 * Strutture dati principali: GpG
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: LocalSearch
**
*  Name: set_heuristic_parameters
*  Objective: During the search we change, based on the scanning found and restart done, the parameters of
*             local search, which the used heuristic and the strategy of chosen of the inconsistence
*  Type: void
*  Input: int num_run
*         int num_sol
*  Output: none
*  Main Data Structures: GpG
*  Main Functions Used: none
*  Call gives:
**/
void set_heuristic_parameters (int num_restart, int num_run)
{
  int exist_num_preconditions = 1;

  if (GpG.num_solutions >= 3 && num_restart > 5 && !exist_num_preconditions)
    {
      if (GpG.accurate_cost == COMPUTE_MAX_COST)
	GpG.accurate_cost = COMPUTE_DG_LIST_COST;
      else if (GpG.accurate_cost == COMPUTE_DG_LIST_COST)
	GpG.accurate_cost = COMPUTE_MAX_COST;
    }
  if (num_restart - GpG.last_succ_restart > 5)
    {
      if (GpG.static_noise == FALSE && (GpG.init_numerator * 1.25 < 40) )
	{
	  GpG.init_numerator *= 1.25;
	}
    }
  else
    GpG.init_numerator = GpG.orig_numerator;

  GpG.numerator =  GpG.init_numerator;

  /**
  if (num_restart > 0 && !(num_restart % 4))
    if (GpG.neighb_with_timed_fa == TRUE)
      GpG.neighb_with_timed_fa = FALSE;
  **/

  /**
    Dopo aver compiuto almeno 5 restart
    **
    After to have completed 5 restart at least
  **/
  if (num_restart > 5)
    {
      if (GpG.accurate_cost == COMPUTE_DG_LIST_COST)
	{
	 /**
	    Si scambia ciclicamente la strategia di scelta dell'inconsistenza
	    **
	    Exchanging cyclically the strategy of chosen of the inconsistenza
	 **/
	  if (GpG.inc_choice_type ==MIN_LEVEL_MIN_ADDITIVE_ACTIONS)
	    GpG.inc_choice_type =MIN_LEVEL_CONSTR_INC;
	  else
	  if (GpG.inc_choice_type ==MIN_LEVEL_CONSTR_INC)
	    GpG.inc_choice_type = MIN_LEVEL_INC;
	  else if (GpG.inc_choice_type == MIN_LEVEL_INC)
	    GpG.inc_choice_type = RANDOM_INC;
	  else
	  if (GpG.inc_choice_type == RANDOM_INC)
	    {
	      if( GpG.exist_numeric_preconds)
		  GpG.inc_choice_type =MIN_LEVEL_INC;
		else
		  GpG.inc_choice_type = MIN_LEVEL_MIN_ADDITIVE_ACTIONS;
	    }
	  /**
	  if (GpG.inc_choice_type == RANDOM_INC)
	    GpG.inc_choice_type = MIN_LEVEL_CONSTR_INC;
	  else if (GpG.inc_choice_type == MIN_LEVEL_CONSTR_INC)
	    GpG.inc_choice_type = MIN_LEVEL_COST_INC;
	  else if (GpG.inc_choice_type == MIN_LEVEL_COST_INC)
	    GpG.inc_choice_type = MIN_LEVEL_INC;
	  else if (GpG.inc_choice_type == MIN_LEVEL_INC)
	    GpG.inc_choice_type = RANDOM_INC;
	  **/

	  //MODIFICHE COCCOLI
	  else if (GpG.inc_choice_type == RANDOM_INCONSISTENCE)
	    GpG.inc_choice_type = MIN_LEVEL_CONSTR_INCONSISTENCE;
	  else if (GpG.inc_choice_type == MIN_LEVEL_CONSTR_INCONSISTENCE)
	    GpG.inc_choice_type = MIN_LEVEL_COST_INCONSISTENCE;
	  else if (GpG.inc_choice_type == MIN_LEVEL_COST_INCONSISTENCE)
	    GpG.inc_choice_type = MIN_LEVEL_INCONSISTENCE;
	  else if (GpG.inc_choice_type == MIN_LEVEL_INCONSISTENCE)
	    GpG.inc_choice_type = RANDOM_INCONSISTENCE;
	}
      else
	{
	  /**
	     Si scambia ciclicamente l'euristica utilizzata
	     **
	     The used heuristic is exchanged cyclical
	  **/
	  if (GpG.inc_choice_type == RANDOM_INC)
	    GpG.inc_choice_type = MIN_LEVEL_INC;
	  else if (GpG.inc_choice_type == MIN_LEVEL_INC)
	    GpG.inc_choice_type = RANDOM_INC;
	}
    }

#ifdef __MY_OUTPUT__
  //  if(DEBUG1)
    printf("RUN: %d RESTART=%d NOISE=%d INC=%d",num_run,  num_restart, GpG.numerator, GpG.inc_choice_type);
#endif
}



/** OK 03/08/04
 * Name: reset_plan_param
 * Scopo:
 * Tipo: void
 * Input: int level 
 *        PlanAction ** plan_actions
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: reset_plan_param
*  Objective:
*  Type: void
*  Input: int level 
*         PlanAction ** plan_actions
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void reset_plan_param (int level, PlanAction ** plan_actions)  
{
  GpG.num_false_tot = GpG.num_false_act + GpG.num_false_fa + GpG.num_false_num_fa + GpG.num_false_tmd_fa;
  GpG.min_inc = GpG.num_false_tot;
  GpG.min_num_actions = GpG.num_actions;
  GpG.found_plan = STORED;
  GpG.curr_plan_length = GpG.input_plan_lenght = level - 1;
}



/** OK 
 * Name: intial_heuristic_param
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: intial_heuristic_param
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void intial_heuristic_param ()
{
  if (DEBUG1)
    printf("\n\nExecution Cost = %.2f, Temporal Cost = %.2f", GpG.orig_weight_cost, GpG.orig_weight_time);
  GpG.weight_time = GpG.orig_weight_time;
  GpG.weight_cost = GpG.orig_weight_cost;
  if (GpG.onlysearchcostx1stsol)
    {
      if (!GpG.timed_facts_present)
	{
	  GpG.weight_time = 0.0;
	  GpG.weight_cost = 0.0;
	  //	  GpG.temporal_plan = FALSE;
	}
      else
	{
	  GpG.numerator = GpG.init_numerator = GpG.orig_numerator = 5;
	}

#ifdef __MY_OUTPUT__
      if (DEBUG0)
	{
	  printf("\n\nForcing Evaluation function weights:\n");
	  printf("\tAction duration %.2f; Action cost %.2f\n\n",GpG.weight_time, GpG.weight_cost);
	}
#endif
   }
  if (GpG.splitted_actions == TRUE)
    {
      GpG.temporal_plan = 1;
      GpG.weight_time = 1.0;
      GpG.weight_cost = 0.0;
    }
  if (GpG.timed_facts_present)
    {
      GpG.orig_inc_choice =  MIN_LEVEL_MIN_TIMED_INC;
      GpG.inc_choice_type =  MIN_LEVEL_MIN_TIMED_INC;
    }
  else if (GpG.derived_pred_in_preconds)
    {
      GpG.orig_inc_choice =  MIN_LEVEL_INC;
      GpG.inc_choice_type =  MIN_LEVEL_INC;
    }
  else if (GpG.inst_duplicate_param ||  GpG.contraddictory_ef_conn)
    {
      GpG.numrun = 1;
    }
}



/***************************************
            MINARRAY
 ***************************************/



/** OK 
 * Name: static int
 * Scopo:
 * Tipo: get_num_condition_array
 * Input: OpConn *op
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: get_num_condition_array
*  Objective:
*  Type: static int
*  Input: OpConn *op
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
static int get_num_condition_array(OpConn *op)
{
  min_array *p;
  int	    num;
  int	    bit;
  num = 0;
  for (p = op->bit_condition; p < &op->bit_condition[op->num_condition]; p++)
    for (bit = 0; bit < 32; bit++)
      if (p->uid_mask & (1 << bit))
	num++;
  return(num);
}



/** OK 
 * Name: copy_compress_bit_array
 * Scopo:
 * Tipo: void
 * Input: min_array *p 
 *        int *store
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: copy_compress_bit_array
*  Objective:
*  Type: void
*  Input: min_array *p
*         int *store
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void copy_compress_bit_array(min_array *p, int *store)
{
  int i;
  for (i = 0; i < NUMINTS; i++)
    if (store[i]) {
      p->uid_block = i;
      p->uid_mask = store[i];
      store[i] = 0;
      p++;
    }
}



/** OK 03/08/04
 * Name: create_min_cond_array
 * Scopo:
 * Tipo: void
 * Input: int v_pos
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: create_min_cond_array
*  Objective: Create min_array for conditional vertex "v" 
*             min_array is useful for find the preconditions nodes and add effects nodes 
*             of an action without using pointers
*  Type: void
*  Input: int v_pos
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void create_min_cond_array (int v_pos)
{
  reverse_bit_array *rbc;
  min_array	    *p;
  OpConn	    *op;
  int		    store[NUMINTS];
  int		    bit;
  int		    num;
  int		    el;
  int		    j;
  int		    cv_pos;
  int		    cef;
  int		    mask;

  if (gnum_ft_block > NUMINTS) {
#ifdef __MY_OUTPUT__
    MSG_ERROR ( WAR_NUMINTS );
#else
    printf( WAR_NUMINTS );
#endif
    exit (1);
  }
  op = &gop_conn[v_pos];
  if (!op->num_I)
    return;
  num = 0;
  memset(store, 0, sizeof(store));
  for (cef = 0;  cef < op->num_I; cef++) {
    for (cv_pos = op->I[cef], j = 0; j < gcondef_conn[cv_pos].num_PC; j++) {
      el = gcondef_conn[cv_pos].PC[j];
      
      if (el >= 0) {
	if (store[GUID_BLOCK (el)] == 0)
	  num++;
	store[GUID_BLOCK (el)] |= GUID_MASK (el);
      }
    }
  }
  op->bit_condition = (min_array *)calloc(num, sizeof (min_array));
  copy_compress_bit_array(op->bit_condition, store);
  op->num_condition = num;
  num = get_num_condition_array(op);
//  printf("\n\nNumero effetti %d", num);
  op->reverse_bit_condition = (reverse_bit_array *)calloc(num, sizeof (reverse_bit_array));
  for (j = 0;  j < num; j++)
    op->reverse_bit_condition[j].cef = calloc(num, sizeof(int));
  for (rbc = op->reverse_bit_condition, p = op->bit_condition;
       p < &op->bit_condition[op->num_condition];
       p++) {
    for (bit = 0; bit < 32; bit++)
      if (p->uid_mask & (1 << bit)) {
	mask = p->uid_mask  & (1 << bit);
	for (j = 0; ((mask >> j) != 1) && (j < 32); j++);
	el = (p->uid_block << 5) + j;
	rbc->fact = el;
//        printf("\nel %d %x %d", p->uid_block, j, rbc->fact);
	rbc++;
      }
  }
  for (cef = 0;  cef < op->num_I; cef++) {
    for (cv_pos = op->I[cef], j = 0; j < gcondef_conn[cv_pos].num_PC; j++) {
      el = gcondef_conn[cv_pos].PC[j];
      for (rbc = op->reverse_bit_condition;
	   rbc < &op->reverse_bit_condition[get_num_condition_array(op)];
	   rbc++)
	if (rbc->fact == el) {
	  rbc->cef[rbc->num_cef] = cv_pos;
//	    printf("\nCondEfConn %d numero = %d", rbc->cef[rbc->num_cef], rbc->num_cef);
	  rbc->num_cef++;
	}
    }
  }
}



/** OK 03/08/04
 * Name: create_min_array
 * Scopo: Data una azione (v_pos) aggiornare (o creare) i campi bit_precond (bit array delle precondizioni) e num_precond
 *        (numero di precondizioni) per le precondizioni associate ad essa.
 *        Data una azione (v_pos) aggiornare (o creare) i campi bit_add_effect (bit array degli effetti additivi) e num_add_effect
 *        (numero di effetti additivi) per gli effetti additivi associati ad essa.
 * Tipo: void
 * Input: int v_pos
 * Output: nessuno
 * Strutture dati principali: gef_conn[]
 * Funzioni principali utilizzate: reset_bitarray
 * Chiamata da: create_all_min_array
**
*  Name:  create_min_array
*  Objective: We have an action (v_pos). We can update (or create) bit_precond (bit array of the preconditions) and num_precond
*             (numbero of precondition) fields, for the preconditions associated
*             With the action we also can update (or create) bit_add_effect (bit array of the additive effects) and num_add_effect
*             (number of the additive effects) fields, for the additive effects associated
*  Type: void
*  Input: int v_pos
*  Output: none
*  Main Data Structures: gef_conn[]
*  Main Functions Used: reset_bitarray
*  Call gives: create_all_min_array
**/
void create_min_array (int v_pos)
{
  int store[NUMINTS];
  register int i;
  int j, num;
  int el;
  int cel;

  /** PRECONDICTIONS **/
  num = 0;
  reset_bitarray (store, NUMINTS);

  if (gnum_ft_block > NUMINTS) {
#ifdef __MY_OUTPUT__
    MSG_ERROR ( WAR_NUMINTS );
#else
    printf( WAR_NUMINTS );
#endif
    exit (1);
  }
  /**
    Scorro le precondizioni associate all'azione v_pos
    **
    Sliding the preconditions associated to the action v_pos
  **/
  for (j = 0; j < gef_conn[v_pos].num_PC; j++)
    {
      el = gef_conn[v_pos].PC[j];
      if (el < 0)
	continue;
      /**
	Aggiorno la posizione del bit array store corrispondente alla posizione della precondizione
	**
	Updating the position of the store bit array correspondent to the position of the precondition
      **/
      if (store[GUID_BLOCK (el)] == 0)
	num++;
      store[GUID_BLOCK (el)] |= GUID_MASK (el);
    }
  /**
    Se il bit_precond e' occupato lo svuoto
    **
    If the bit_precond is full I empty it
  **/
  if (CONVERT_ACTION_TO_VERTEX (v_pos)->bit_precond)
    free (CONVERT_ACTION_TO_VERTEX (v_pos)->bit_precond);
  /**
    Alloco per bit_precond una quantita' di memoria per contenere il min_array store
    **
    Allcocating for bit_precond a quantity of memory to contain the min_array store
  **/
  CONVERT_ACTION_TO_VERTEX (v_pos)->bit_precond =
    (min_array *) malloc (num * sizeof (min_array));
  /**
    Scorro il bit array store e aggiorno il bit_precond associato all'azione v_pos
    **
    Sliding the store bit array and updating the bit_precond associated to the action v_pos
  **/
  for (j = 0, i = 0; j < num && i < NUMINTS; i++)
    if (store[i])
      {
        /**
	  Associo bit_precond[j].uid_block il valore del contatore i
	  **
	  Associating bit_precond[j].uid_block the value of i counter
	**/
	CONVERT_ACTION_TO_VERTEX (v_pos)->bit_precond[j].uid_block = i;
	/**
	  Associo a bit_precond[j].uid_mask la maschera presente nel min_array store in posizione i
	  **
	  Associating to bit_precond[j].uid_mask the mask in the min_array store in position i
	**/
	CONVERT_ACTION_TO_VERTEX (v_pos)->bit_precond[j].uid_mask = store[i];
	j++;
	/**
	  Svuoto il min_array store
	  **
	  I empty the min_array store
	**/
	store[i] = 0;
      }
  /**
    Aggiorno il campo num_precond (corrispondente al numero di precondizioni) dell'azione v_pos
    **
    Updating the field num_precond (correspondent to the number of preconditions) of the action v_pos
  **/
  CONVERT_ACTION_TO_VERTEX (v_pos)->num_precond = num;
  /**
     Effetti additivi
     **
     Add-effect 
  **/
  num = 0;
  /**
    Scorro gli effetti additivi associati all'azione v_pos
    **
    Sliding the additive effects associates to the action v_pos
  **/
  for (j = 0; j < gef_conn[v_pos].num_A; j++)
    {
      cel = gef_conn[v_pos].A[j];
      if (cel < 0)
	continue;
      /**
	Aggiorno il bit array store in base alla posizione dell'azione
	**
	Updating the store bit Array based on the position of the action
      **/
      if (store[GUID_BLOCK (cel)] == 0)
	num++;
      store[GUID_BLOCK (cel)] |= GUID_MASK (cel);
    }
  /**
    Se il bit_add_effect e' occupato lo svouto
    **
    If the bit_add_effect is occupied we empty it
  **/
  if (CONVERT_ACTION_TO_VERTEX (v_pos)->bit_add_effect)
    free (CONVERT_ACTION_TO_VERTEX (v_pos)->bit_add_effect);
  /**
    Alloco a bit_add_effect una quantita' di memoria per contenere il min_array store
    **
    Allocating to bit_add_effect a quantity of memory to contain the min_array store
  **/
  CONVERT_ACTION_TO_VERTEX (v_pos)->bit_add_effect =
    (min_array *) calloc (num, sizeof (min_array));
  /**
    Scorro il bit array store e aggiorno il bit_add_effect associato all'azione v_pos
    **
    Sliding the store bit Array and updating the bit_add_effect associated to the action v_pos
  **/
  for (j = 0, i = 0; j < num && i < NUMINTS; i++)
    if (store[i])
      {
	/**
	  Associo bit_add_effect[j].uid_block il valore del contatore i
	  **
	  Associating bit_add_effect[j].uid_block the value of contatore i
	**/
	CONVERT_ACTION_TO_VERTEX (v_pos)->bit_add_effect[j].uid_block = i;
	/**
	  Associo a bit_add_effect[j].uid_mask la mask presente nel min_array store in posizione i
	  **
	  Associating to bit_add_effect[j].uid_mask the mask in the min_array store in position i
	**/
	CONVERT_ACTION_TO_VERTEX (v_pos)->bit_add_effect[j].uid_mask =
	  store[i];
	j++;
      }
  /**
    Aggiormo il campo num_add_effect (corrispondente al numero di effetti additivi) dell'azione v_pos
    **
    Updating the field num_add_effect (correspondent to the number of additive effects) of the action v_pos
  **/
  CONVERT_ACTION_TO_VERTEX (v_pos)->num_add_effect = num;
}



/** OK 03/08/04 ---------------
 * Name: create_all_min_array
 * Scopo: Per ogni azione aggiornare (o creare) i campi num_precond num_add_effect bit_precond bit_add_effect
 * Tipo: void
 * Input: nessuno
 * Output: nessuno
 * Strutture dati principali: nessuna
 * Funzioni principali utilizzate: create_min_array
 * Chiamata da: main
**
*  Name:  create_all_min_array
*  Objective: For every action updating (or create) the fields num_precond num_add_effect bit_precond bit_add_effect
*  Type: void
*  Input: none
*  Output: none
*  Main Data Structures: none
*  Main Functions Used: create_min_array
*  Call gives: main
**/
void create_all_min_array ()
{
  int i;
  for (i = 0; i < gnum_ef_conn; i++)
    create_min_array (i);
  for (i = 0; i < gnum_op_conn; i++)
    create_min_cond_array (i);
}



/** OK 03/08/04 ------------
 * Name: reset_bitarray
 * Scopo: Porre a zero i bit array *vector di dimensione dim
 * Tipo: void
 * Input: register int *vector
 *        register int dim
 * Output: nessuno
 * Strutture dati principali: nessuna
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: reset_plan
 *              compute_constr_fact
 *              compute_dg_heuristic_for_action
 *              create_min_array
 *              predict_cost_list
 *              dg_action_cost
**
*  Name:  reset_bitarray
*  Objective: Set to zero the bit Array *vector of dimension dim
*  Type: void
*  Input: register int * vector
*         register int dim
*  Output: none
*  Main Data Structures: none
*  Main Functions Used: none
*  Call gives: reset_plan
*              compute_constr_fact
*              compute_dg_heuristic_for_action
*              create_min_array
*              predict_cost_list
*              dg_action_cost
**/
void reset_bitarray (register int *vector, register int dim)
{
  memset(vector, 0, dim * sizeof(int));
}



/** OK 03/08/04 --------------------
 * Name: count_bit1
 * Scopo: Contare i bit uguali a 1 di un intero
 * Tipo: inline int
 * Input: register int mask
 * Output: Il numero di bit diversi uguali a 1
 * Strutture dati principali: nessuna
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: action_eff_cost
 *              count_mutex_noop_at_start
**
*  Name:  count_bit1
*  Objective: To count the bit equal to 1 of an entire
*  Type: inline int
*  Input: register int mask
*  Output: The equal various number of bit to 1
*  Main Data Structures: none
*  Main Functions Used: none
*  Call gives: action_eff_cost
*              count_mutex_noop_at_start
**/
// IVAN static
inline int count_bit1 (register int mask)
{
  /**
    Intero di appoggio
    **
    Integere of support
  **/
  register int num;
  /**
    Se mask e' diverso da 0
    **
    If mask is not equal to 0
  **/
  if (mask)
    {
      num = 0;
      if (mask & FIRST_1)
	{
	  num++;
	  mask &= 0x07fffffff;
	}
      while (mask)
	{
	  while (!(mask & 0x1))
	    mask >>= 1;
	  num++;
	  mask >>= 1;
	}
    }
  else
    return (0);
  return (num);
}



/***************************************
         NEIGHBORHOOD
 ***************************************/



/** OK 03/08/04 ------------------
 * Name: reset_neighborhood
 * Scopo: Porre uguale a zero l'intero num_neighborhood corrispondente al numero di azioni presenti nel vicinato neighb_vect[]
 * Tipo: void
 * Input: nessuno
 * Output: nessuno
 * Strutture dati principali: num_neighborhood
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: choose_actions_treated_fact
 *              choose_num_actions
 *              choose_actions
 *              choose_actions_dg_list
**
*  Name:  reset_neighborhood
*  Objective: To place equal to zero entire num_neighborhood correspondent to the number of actions in neighborhood neighb_vect[ ]
*  Type: void
*  Input: none
*  Output: none
*  Main Data Structures: num_neighborhood
*  Main Functions Used: none
*  Call gives: choose_actions_treated_fact
*              choose_num_actions
*              choose_actions
*              choose_actions_dg_list
**/
void reset_neighborhood ()
{
  num_neighborhood = 0;
}



/** OK 03/08/04 ---------------
 * Name: insert_element_in_neighb
 * Scopo: Inserire un elemento nel vicinato
 * Tipo: void
 * Input: neighb_list n_elem
 * Output: nessuno
 * Strutture dati principali: neighb_vect[]
 *                            num_neighborhood
 * Funzioni principali utilizzate: nessuna
 * Chiamata da:
**
*  Name:  insert_element_in_neighb
*  Objective: To insert an element in the neighbourhood
*  Type: void
*  Input: neighb_list n_elem
*  Output: none
*  Main Data Structures: neighb_vect[ ]
*                        num_neighborhood
*  Main Functions Used:
*  Call gives:
**/
void insert_element_in_neighb (neighb_list n_elem)
{
  if(DEBUG4)
    {
      if (n_elem->constraint_type == C_T_REMOVE_ACTION)
	printf("\n--- REMOTION");
      else
	if (n_elem->constraint_type == C_T_INSERT_ACTION)
	  printf("\n--- INSERTION");
      printf("%s at level %d", print_op_name_string(n_elem->act_pos, temp_name), n_elem->act_level);
    }
  if (neighb_vect[num_neighborhood] == NULL)
    neighb_vect[num_neighborhood] = (neighb_list) malloc (sizeof (neighb));
  memcpy (neighb_vect[num_neighborhood], n_elem, sizeof (neighb));
  /**
    Incremento num_neighborhood corrispondente al numero di azioni inserite nel neighb_vetc[]
    **
    Incrementing num_neighborhood correspondent to the number of actions inserted in the neighb_vetc[ ]
  **/
  num_neighborhood++;
  /**
    Se num_neighborhood e' maggiore del numero massimo segnala errore
    **
    If num_neighborhood is greater of the maximum number it marks error
  **/
  if (num_neighborhood >= MAX_MAX_NODES) {
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_MAX_MAX_NODES );
#else
    printf( WAR_MAX_MAX_NODES );
#endif    
    exit (1);
  } 
  
#ifdef __TEST__
  printf ("\n\n ;;;;;;;;;;;;;;;;;;;;;;; num_neighborhood %d level %d action ",
	  num_neighborhood, n_elem->act_level);
  print_op_name (n_elem->act_pos);
  printf ("\n\n");
#endif
}



/***************************************
           MUTEX FUNCTIONS
 ***************************************/



/** OK 03/08/04 ----------------
 * Name: count_mutex_action
 * Scopo: Determinare quante mutex ha l'azione passata in ingresso (act_pos)
 * Tipo: inline int
 * Input: int act_pos
 *        int level
 * Output: Il numero di mutue esclusioni
 * Strutture dati principali: vectlevel[]
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: dg_action_cost
 *              fast_insertion_action_cost
 *              max_action_cost
**
*  Name:  count_mutex_action
*  Objective: To determine how many mutex has the last action in input (act_pos)
*  Type: inline int
*  Input: int act_pos
*         int level
*  Output: The number of mutual exclusions
*  Main Data Structures: vectlevel[ ]
*  Main Functions Used:
*  Call gives: dg_action_cost
*              fast_insertion_action_cost
*              max_action_cost
**/
inline int count_mutex_action (int act_pos, int level)
{
  /**
    Interi di appoggio
    **
    Integer of support
  **/
  register int i, temp = 0, pos;
  /**
    Associo a pos l'intero corrispondente all'azione presente nel livello level
    **
    I associate to pos the correspondent integer to the present action in the level level
  **/
  if ((pos = GET_ACTION_OF_LEVEL (level)->position) >= 0)
    {
      /**
	 Confronta le due azioni act_pos e pos per vedere se sono mutex , se si incrementa temp
	 **
	 Comparing the two actions act_pos and pos to see if they are mutex, if temp increases
      **/
      temp += ARE_MUTEX_TRI_EF(pos, act_pos); 
    }
  if (GpG.approximation_level < 2)
    return temp;
  /**
    Scorro il vettore dei fatti precondizioni e determino quali precondizioni son mutuamente esclusive con l'azione act_pos
    **
    Sliding the array of the preconditions facts and determine which preconditions are mutually exclusive with the action act_pos
  **/
  for (i = 0; i < gnum_ft_block; i++)
    if (vectlevel[level]->prec_vect[i])	// Solo se sono diversi da 0 faccio il test
      /**
	Incrementa del numero di fatti del livello level veri, precondizioni di azioni in livelli successivi e mutuamente
	esclusivi con l'azione in esame
	**
	It increases the number of true facts of the level level, preconditions of actions in levels succeeded and mutually
	exclusive with the action in examination
      **/
      /**
	Esamina il bit vector per i fatti mutuamente esclusivi con l'azione act_pos e i bit vector dei fatti veri del
	livello level e per i fatti precondizioni dei livelli successivi
	**
	It examines the bit vector for the facts mutually exclusive with the action act_pos and the bit vector of the true facts of
	level level and for the facts preconditions of the levels succeeded
      **/
      temp += count_bit1 (CONVERT_ACTION_TO_VERTEX (act_pos)->ft_exclusive_vect[i] & (vectlevel[level]->fact_vect[i]) & vectlevel[level]->prec_vect[i]);
  /**
    Ritorna il numero di mutex che ha l'azione act_pos con l'azione le noop del livello level
    **
    Returns the number of mutex that has the action act_pos with the action the noop of the level level
  **/
  return temp;
}



/** OK 03/08/04 ---------------------
 * Name: count_mutex_noop
 * Scopo: Determinare quante mutex ha la noop passata in ingresso (noop_pos) con l'azione e i fatti del livello level
 * Tipo: int
 * Input: int noop_pos
 *        int level
 * Output: Il numero di mutue esclusioni
 * Strutture dati principali: vectlevel[]
 * Funzioni principali utilizzate: check_mutex_noop
 *                                 count_bit1
 * Chiamata da: compute_dg_facts_cost
 *              dg_insertion_action_cost
**
*  Name:  count_mutex_noop
*  Objective: To determine how many mutex has the noop in input (noop_pos) with the action and the facts of the level level
*  Type: int
*  Input: int noop_pos
*         int level
*  Output: The number of mutual exclusions
*  Main Data Structures: vectlevel[ ]
*  Main Functions Used: check_mutex_noop
*                       count_bit1
*  Call gives: compute_dg_facts_cost
*              dg_insertion_action_cost
**/
int count_mutex_noop (int noop_pos, int level)
{
  /**
    Interi di appoggio
    **
    Entire of support
  **/
  int i, temp = 0, size;

  if (GpG.derived_predicates)
    size = gnum_base_ft_block;
  else
    size = gnum_ft_block;
  /**
    Se la noop (noop_pos) e' ME con l'azione di level allora incremento il contatore temp
    **
    If noop (noop_pos) is ME with the action of level then increment the counter temp
  **/
  if (check_mutex_noop (noop_pos, level) >= 0)
    temp++;
  /**
    Controllo le ME con le altre noop
    **
    Control ME with the others noop
  **/
  for (i = 0; i < size; i++)
    if (vectlevel[level]->prec_vect[i])	// Solo per i fatti precondizione faccio il test 
      /**
	Confronta il bit vector contenente i fatti mutex con la noop noop_pos e i bit del vettore dei fatti veri del
	livello level e dei fatti precondizioni di azioni in livelli successivi. Incrementa temp
	**
	It compare the bit vector containing the mutex facts with noop_pos and the bit of the array of the true facts of
	level level and of the facts preconditions of actions in successive levels.  It increases temp
      **/
      temp += count_bit1 (CONVERT_NOOP_TO_VERTEX (noop_pos)->ft_exclusive_vect[i] & (vectlevel[level]->fact_vect[i]) & vectlevel[level]->prec_vect[i]);
  /**
    Ritorna il numero di mutex che ha la noop noop_pos con l'azione al livello level e i fatti veri e precondizioni
    di azioni in livelli successivi
    **
    It returns the number of mutex that has noop_pos with the action to the level level and the true facts and preconditions
    of actions in successive levels
  **/
  return temp;
}



/** OK 03/08/04 --------------
 * Name: check_mutex_action
 * Scopo: Determinare la mutua esclusione tra l'azione act_position e l'azione presente nel livello level
 * Tipo: int
 * Input: register int act_position
 *        int level
 * Output: Se vi e' mutua esclusione restituisce la posizione dell'azione presente nel livello level, altrimenti -1.
 * Strutture dati principali: vectlevel[]
 * Funzioni principali utilizzate: are_mutex_ops
 * Chiamata da: temporal_constraints
 *              dg_action_cost
**
*  Name:  check_mutex_action
*  Objective: To determine the mutual exclusion between the action act_position and the action in the level level
*  Type: int
*  Input: register int act_position
*         int level
*  Output: If there is mutual exclusion returns the position of the action in the level level, otherwise -1.
*  Main Data Structures: vectlevel[]
*  Main Functions Used: are_mutex_ops
*  Call gives: temporal_constraints
*              dg_action_cost
**/
int check_mutex_action (register int act_position, int level)
{
  /**
    Associo a act_pos la posizione dell'azione presente nel livello level
    **
    Associating to act_pos the position of the present action in the level level
  **/
  int act_pos = GET_ACTION_POSITION_OF_LEVEL (level);
  /**
    Se le mutex sono precalcolate
    **
    If the mutex they are estimated
  **/
  if (!GpG.lowmemory){
    if (CHECK_ACTION_OF_LEVEL (level)
	&& ARE_MUTEX_TRI_EF(act_position, act_pos))
      /**
	 ritorna act_pos se le due azioni sono mutex
	 **
	 it returns act_pos if the two set in action are mutex
      **/
      return (act_pos);
    else
      /**
	ritorna -1 se non sono mutex
	**
	returns -1 if they are not mutex
      **/
      return (-1);
  }
  else {
    /**
      Controlla la presenza dell'azione nel livello e poi esamina se vi e' mutua esclusione tra  le azioni act_level
      e act_position
      **
      Check of the presence of the action in the level and then it examines if there is mutual exclusion between the actions act_level
      and act_position
    **/
    if( CHECK_ACTION_OF_LEVEL(level) && are_mutex_ops (act_pos, act_position) )	
      /**
	Restituisce la posizione dell'azione nel livello level
	**
	It returns the position of the action in the level level
      **/
      return (act_pos);
    else
      return (-1);
  }
}



/** OK 03/08/04 -----------------
 * Name: check_mutex_noop
 * Scopo: Determinare la mutua esclusione tra la noop position e l'azione presente nel livello level
 * Tipo: int
 * Input: register int position
 *        int level
 * Output: Se vi e' mutua esclusione restituisce la posizione dell'azione presente nel livello level, altrimenti -1.
 * Strutture dati principali: vectlevel[]
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: choose_actions_treated_fact
 *              choose_actions_dg_list
**
*  Name:  check_mutex_noop
*  Objective: To determine the mutual exclusion between noop position and the action in the level level
*  Type: int
*  Input: register int position
*         int level
*  Output: If there is mutual exclusion returns the position of the action in the level level, otherwise -1.
*  Main Data Structures: vectlevel[ ]
*  Main Functions Used:
*  Call gives: choose_actions_treated_fact
*              choose_actions_dg_list
**/
int check_mutex_noop (register int position, int level)
{
  /**
     Associo a act_pos la posizione dell'azione presente nel livello level
     **
     Associating to act_pos the position of the action in the level level
  **/
  int act_pos = GET_ACTION_POSITION_OF_LEVEL (level);

  /**
    Se la noop ha posizione negativa (no noop inserita) errore
    **
    If the noop has negative position (noop not inserted) error
  **/
  if (position < 0) {
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else
    printf( WAR_BUG );
#endif
    printf ("\ncheck_mutex_noop_1");
    exit (0);
  }
  /**
    Controlla la presenza dell'azione nel livello e poi determina se vi e' mutua esclusione con la noop
    **
    Checking the presence of the action in the level and then it determines if there is mutual exclusion with the noop
  **/
  if (CHECK_ACTION_OF_LEVEL (level)
      && (CONVERT_NOOP_TO_VERTEX (position)->
	 ef_exclusive_vect[GUID_BLOCK (act_pos)] & GUID_MASK (act_pos)))
    /**
      Restituisce la posizione dell'azione nel livello level
      **
      It gives back the position of the action in the level level
    **/
    return (act_pos);
  else
    return (-1);
}



/** OK 03/08/04 -------------
 * Name: check_mutex_noop_durative
 * Scopo: Determinare la mutua esclusione tra la noop e l'azione presente nel livello level in domini con azioni durative
 * Tipo: int
 * Input: register int position
 *        int level
 * Output: Se vi e' mutua esclusione restituisce la posizione dell'azione presente nel livello level, altrimenti -1.
 * Strutture dati principali: vectlevel[]
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: forward_noop_propagation
 *              backward_precond_propagation
**
*  Name:  check_mutex_noop_durative
*  Objective: To determine the mutual exclusion between noop and the action in the level level in dominions with durative actions
*  Type: int
*  Input: register int position
*         int level
*  Output: If there is mutual exclusion returns the position of the action in the level level, otherwise -1.
*  Main Data Structures: vectlevel[]
*  Main Functions Used:
*  Call gives: forward_noop_propagation
*              backward_precond_propagation
**/
int check_mutex_noop_durative (register int position, int level)
{
  /**
    Associo a act_pos la posizione dell'azione presente nel livello level
    **
    Associating to act_pos the position of the action in the level level
  **/
  int act_pos = GET_ACTION_POSITION_OF_LEVEL (level);
  
  /**
    Se la noop ha posizione negativa (no noop inserita) ritorna errore
    **
    If the noop it has negative position (noop not inserted) it returns error
  **/
  if (position < 0) {
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_BUG );
#else
    printf( WAR_BUG );
#endif
    printf ("\ncheck_mutex_noop_durative_1");
    exit (0);
  }
  /**
    Se l'azione ha il fatto corrispondente alla NOOP negli effetti cancellanti AT_END allora non e' mutuamente
    esclusiva con la NOOP.
    Controlla la presenza dell'azione nel livello e poi determina se vi e' mutua esclusione con la noop
    **
    If the action has the fact correspondent to the NOOP in cancelling AT_END effects then it is not mutually
    exclusive with the NOOP.
    Checking the presence of the action in the level and then it determines if there is mutual exclusion with the noop
  **/
  if (CHECK_ACTION_OF_LEVEL (level)
      && (CONVERT_NOOP_TO_VERTEX (position)->
	  ef_exclusive_vect[GUID_BLOCK (act_pos)] & GUID_MASK (act_pos))
      && vectlevel[level]->noop_act[position].w_is_overall != ADD_DEL
      && vectlevel[level]->noop_act[position].w_is_overall != NADD_DEL)
    /**
      Restituisce la posizione dell'azione nel livello level
      **
      It gives back the position of the action in the level level
    **/
    return (act_pos);
  else
    return (-1);
}



/** OK 03/08/04
 * Name: count_mutex_facts
 * Scopo:
 * Tipo: int
 * Input: int act_pos 
 *        int level
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: count_mutex_facts
*  Objective:
*  Type: int
*  Input: int act_pos
*         int level
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int count_mutex_facts (int act_pos, int level)
{
  int i, j, count;
  register int k, temp1;
#ifdef __TEST__
  printf ("\nFact mutex ");
#endif

  count = 0;
  for (j=i = 0; i < gnum_ft_block; i++, j+=32)
    if (Hvar.relaxed_bit_vect_preconds[i] || Hvar.supported_bit_vect_preconds[i]) /**
										     Solo se sono diversi da 0 faccio il test 
										     **
										     Only if they are not equal to 0 we can do the test
										  **/
      {
	temp1 =   CONVERT_ACTION_TO_VERTEX (act_pos)->ft_exclusive_vect[i] & Hvar.initial_relaxed_bit_vect_facts[i] &  (Hvar.relaxed_bit_vect_preconds[i]| Hvar.supported_bit_vect_preconds[i]);
	k = 32;
	while (temp1)
	  {
	    k--;
	    if (temp1 & FIRST_1)
	      if(!is_fact_in_additive_effects(act_pos,j+k))
		{
//		   if (!(Hvar.temp_removed_act > 0 && (is_fact_in_preconditions(Hvar.temp_removed_act,j+k) || is_fact_in_preconditions_overall(Hvar.temp_removed_act,j+k) || is_fact_in_preconditions_end(Hvar.temp_removed_act,j+k) ) && vectlevel[level+1]->fact[j+k].w_is_goal == 0 ))
		  //    {
		  count++;
#ifdef __TEST__
		  print_ft_name (j + k);
		  printf (" -- ");
#endif
		  //    }
                }
	    temp1 <<= 1;
	  }
      }
  return count;
}



/** OK 03/08/04 --------
 * Name: count_mutex_noop_at_start
 * Scopo: Determinare il numero di mutue esclusioni tra l'azione act_pos e le precondizioni nel livello level
 * Tipo: int
 * Input: int act_pos
 *        int level
 * Output: Restituisce il numero di mutue esclusioni
 * Strutture dati principali: vectlevel[]
 * Funzioni principali utilizzate: count_bit1
 * Chiamata da: compute_dg_facts_cost
 *              dg_insertion_action_cost
**
*  Name:  count_mutex_noop_at_start
*  Objective: To determine the number of mutual exclusions between the action act_pos and the preconditions in the level level
*  Type: int
*  Input: int act_pos
*         int level
*  Output: It returns the number of mutual exclusions
*  Main Data Structures: vectlevel[ ]
*  Main Functions Used: count_bit1
*  Call gives: compute_dg_facts_cost
*              dg_insertion_action_cost
**/
int count_mutex_noop_at_start (int act_pos, int level)
{
  /** 
    Interi di appoggio 
    **
    Entire of support
  **/
  int i, temp, size;

#ifdef __TEST__
  printf ("\nFact mutex ");

#endif

  if (GpG.derived_predicates)
    size = gnum_base_ft_block;
  else
    size = gnum_ft_block;
  /** 
    Scorro le precondizioni dei fatti del livello level 
    **
    I slide the preconditions of the facts of the level level
  **/
  for (temp = 0, i = 0; i < size; i++)
    if (vectlevel[level]->prec_vect[i])	// Solo se sono diversi da 0 faccio il test 
      {
	/** 
	    Confronta il bit vector contenente i fatti mutex con l'azione act_pos e i bit del vettore dei fatti veri del 
	    livello level e dei fatti precondizionidi azioni nei livelli successivi. Incrementa temp 
	    **
	    It confronts the containing bit vector the facts mutex with the action act_pos and the bit of the carrier of the true facts of
	    level level and of the facts precondizionidi sets in action in the levels succeeded to you.  It increases temp
	**/
	temp +=  count_bit1 (CONVERT_ACTION_TO_VERTEX (act_pos)->ft_exclusive_vect[i] & (vectlevel[level]->fact_vect[i]) & vectlevel[level]->prec_vect[i]);

#ifdef __TEST__
	// Stampo mutex
	{
	  int temp1, k, j;
	  j = i * 32;
	  temp1 =
	    CONVERT_ACTION_TO_VERTEX (act_pos)->ft_exclusive_vect[i] & (vectlevel[level]->fact_vect[i]) & vectlevel[level]->prec_vect[i];
	  k = 32;
	  while (temp1)
	    {
	      k--;
	      if (temp1 & FIRST_1)
		{
		  print_ft_name (j + k);
		  printf (" -- ");
		}
	      temp1 <<= 1;
	    }
	}

#endif
      }
  /**
    Ritorna il numero di mutue esclusioni
    **
    The number of mutual exclusions returns
  **/
  return temp;
}



/***************************************
      FACT - ACTION RELATION
 ***************************************/



/** OK 03/08/04 --------------
 * Name: is_fact_in_additive_effects
 * Scopo: Verificare se un fatto e' effetto additivo AT_END di un'azione
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output: TRUE se il fatto e' un effetto additivo AT_END dell'azione act_pos
 *         FALSE altrimenti
 * Strutture dati principali: gef_conn
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: choose_actions_dg_list
 *              insert_time
 *              compute_constr_fact
 *              backward_precond_propagation
 *              propagation_time
 *              dg_action_cost
 *              forward_noop_remotion_time
 *              predict_cost_list
 *              predict_duration
 *              insert_list_action_preconditions
 *              compute_dg_facts_cost
 *              forward_noop_propagation_time
 *              compute_dg_heuristic_for_action
 *              dg_insertion_action_cost
 *              is_action_applicable
**
*  Name:  is_fact_in_additive_effects
*  Objective: To verify if a fact is an AT_END additive effect of an action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output: TRUE if the fact is an additive AT_END effect of the action act_pos
*  Main Data Structures: gef_conn
*  Main Functions Used: none
*  Call gives: choose_actions_dg_list
*              insert_time
*              compute_constr_fact
*              backward_precond_propagation
*              propagation_time
*              dg_action_cost
*              forward_noop_remotion_time
*              predict_cost_list
*              predict_duration
*              insert_list_action_preconditions
*              compute_dg_facts_cost
*              forward_noop_propagation_time
*              compute_dg_heuristic_for_action
*              dg_insertion_action_cost
*              is_action_applicable
**/
int is_fact_in_additive_effects_of_cond (int act_pos, int fact_pos)
{
  int	*p_end;
  int	*p;
  /**
    Se act_pos < 0 : azione non esistente
    **
    If act_pos < 0 :  not existing action
  **/
  if (act_pos < 0)
    return(FALSE);
  for (p = gcondef_conn[act_pos].A, p_end = &gcondef_conn[act_pos].A[gcondef_conn[act_pos].num_A]; p < p_end; p++)
    if (*p == fact_pos)
      return(TRUE);
  return(FALSE);
}



/** OK 03/08/04 --------------
 * Name: is_fact_in_delete_effects
 * Scopo: Verificare se un fatto e' effetto cancellante AT_END di un'azione condizionale
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output: TRUE se il fatto e' un effetto cancellante dell'azione act_pos
 *         FALSE altrimenti
 * Strutture dati principali: gef_conn
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: noop_remotion_time
 *              choose_actions_dg_list
 *              compute_dg_facts_cost
 *              is_action_applicable
**
*  Name:  is_fact_in_delete_effects
*  Objective: To verify if a fact is a cancelling AT_END effect of a conditional action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output: TRUE if the fact is a cancelling effect of the action act_pos
*  Main Data Structures: gef_conn
*  Main Functions Used: none
*  Call gives: noop_remotion_time
*              choose_actions_dg_list
*              compute_dg_facts_cost
*              is_action_applicable
**/
int is_fact_in_delete_effects_of_cond (int act_pos, int fact_pos)
{
  int	*p_end;
  int	*p;
  /**
    Se act_pos < 0: azione non esistente
    **
    If act_pos < 0:  not existing action
  **/
  if (act_pos < 0)
    return(FALSE);
  for (p = gcondef_conn[act_pos].D, p_end = &gcondef_conn[act_pos].D[gcondef_conn[act_pos].num_D]; p < p_end; p++)
    if (*p == fact_pos)
      return(TRUE);
  return(FALSE);
}



/** OK 03/08/04 ---------------
 * Name: is_fact_in_additive_effects_start
 * Scopo: Verificare se un fatto e' effetto additivo AT_START di un'azione condizionale
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output: TRUE se il fatto e' un effetto additivo AT_START dell'azione act_pos
 *         FALSE altrimenti
 * Strutture dati principali: gef_conn
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: choose_actions_dg_list
 *              insert_time
 *              compute_constr_fact
 *              backward_precond_propagation
 *              propagation_time
 *              dg_action_cost
 *              forward_noop_remotion_time
 *              predict_cost_list
 *              predict_duration
 *              insert_list_action_preconditions
 *              compute_dg_facts_cost
 *              forward_noop_propagation_time
 *              compute_dg_heuristic_for_action
 *              dg_insertion_action_cost
**
*  Name:  is_fact_in_additive_effects_start
*  Objective: To verify if a fact is an additive AT_START  effect of a conditional action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output: TRUE if the fact e' an effect additive AT_START of the action act_pos
*  Main Data Structures: gef_conn
*  Main Functions Used:
*  Call gives: choose_actions_dg_list
*              insert_time
*              compute_constr_fact
*              backward_precond_propagation
*              propagation_time
*              dg_action_cost
*              forward_noop_remotion_time
*              predict_cost_list
*              predict_duration
*              insert_list_action_preconditions
*              compute_dg_facts_cost
*              forward_noop_propagation_time
*              compute_dg_heuristic_for_action
*              dg_insertion_action_cost
**/
int is_fact_in_additive_effects_start_of_cond (int act_pos, int fact_pos)
{
  SpecialFacts	*sf;
  int		*p_end;
  int		*p;
  /**
    Se act_pos < 0: azione non esistente
    **
    If act_pos < 0:  not existing action
  **/
  if (act_pos < 0)
    return(FALSE);
  sf = gcondef_conn[act_pos].sf;
  if (sf == NULL)
    return(FALSE);
  for (p = sf->A_start, p_end = &sf->A_start[sf->num_A_start]; p < p_end; p++)
    if (*p == fact_pos)
      return(TRUE);
  return(FALSE);
}



/** OK 03/08/04 -------------------
 * Name: is_fact_in_delete_effects_start
 * Scopo: Verificare se un fatto e' effetto cancellante AT_START di un'azione condizionale
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output: TRUE se il fatto e' un effetto cancellante AT_START dell'azione act_pos
 *         FALSE altrimenti
 * Strutture dati principali: gef_conn
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: update_time
 *              remove_action_from_vectlevel
 *              insert_time
 *              insert_action_in_vectlevel
**
*  Name:  is_fact_in_delete_effects_start
*  Objective: To verify if a fact is an AT_START cancelling effect of a conditional action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output: TRUE if the fact is a cancelling AT_START effect of the action act_pos
*  Main Data Structures: gef_conn
*  Main Functions Used:
*  Call gives: update_time
*              remove_action_from_vectlevel
*              insert_time
*              insert_action_in_vectlevel
**/
int is_fact_in_delete_effects_start_of_cond (int act_pos, int fact_pos)
{
  SpecialFacts	*sf;
  int		*p_end;
  int		*p;
  /** 
    Se act_pos < 0: azione non esistente 
    **
    If act_pos < 0:  not existing action
  **/
  if (act_pos < 0)
    return(FALSE);
  sf = gcondef_conn[act_pos].sf;
  if (sf == NULL)
    return 0;
  for (p = sf->D_start, p_end = &sf->D_start[sf->num_D_start]; p < p_end; p++)
    if (*p == fact_pos)
      return(TRUE);
  
  return(FALSE);
}



/** OK 03/08/04  ---------------------------
 * Name: is_fact_in_preconditions
 * Scopo: Verificare se un fatto e' precondizione AT-START di un'azione condizionale
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output: TRUE se il fatto e' un precondizione AT-START dell'azione act_pos
 *         FALSE altrimenti
 * Strutture dati principali: gef_conn
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: update_time
 *              choose_actions_dg_list
 *              insert_time
 *              noop_remotion_time
 *              insert_action_in_vectlevel
 *              forward_noop_remotion_time
 *              propagation_time
 *              forward_noop_propagation_time
**
*  Name:  is_fact_in_preconditions
*  Objective: To verify if a fact is an AT_START  precondition of a conditional action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output: TRUE if the fact is an AT_START precondition of the action act_pos
*  Main Data Structures: gef_conn
*  Main Functions Used:
*  Call gives: update_time
*              choose_actions_dg_list
*              insert_time
*              noop_remotion_time
*              insert_action_in_vectlevel
*              forward_noop_remotion_time
*              propagation_time
*              forward_noop_propagation_time
**/
int is_fact_in_preconditions_of_cond (int act_pos, int fact_pos)
{
  int	*p_end;
  int	*p;
  /**
    Se act_pos < 0: azione non esistente 
    **
    If act_pos < 0:  not existing action
  **/
  if (act_pos < 0)
    return(FALSE);
  for (p = gcondef_conn[act_pos].PC, p_end = &gcondef_conn[act_pos].PC[gcondef_conn[act_pos].num_PC]; p < p_end; p++)
    if (*p == fact_pos)
      return(TRUE);
  return(FALSE);
}



/** OK 03/08/04 -------------
 * Name: is_fact_in_preconditions_overall
 * Scopo: Verificare se un fatto e' precondizione OVERALL di un'azione condizionale
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output: TRUE se il fatto e' un precondizione OVERALL dell'azione act_pos
 *         FALSE altrimenti
 * Strutture dati principali: gef_conn
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: update_time
 *              insert_time
 *              choose_actions_dg_list
 *              noop_remotion_time
 *              insert_action_in_vectlevel
 *              forward_noop_remotion_time
 *              propagation_time
 *              forward_noop_propagation_time
**
*  Name:  is_fact_in_preconditions_overall
*  Objective: To verify if a fact is an OVERALL precondition of a conditional action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output: TRUE if the fact is an OVERALL precondition
*  Main Data Structures: gef_conn
*  Main Functions Used:
*  Call gives: update_time
*              insert_time
*              choose_actions_dg_list
*              noop_remotion_time
*              insert_action_in_vectlevel
*              forward_noop_remotion_time
*              propagation_time
*              forward_noop_propagation_time
**/
int is_fact_in_preconditions_overall_of_cond (int act_pos, int fact_pos)
{
  SpecialFacts	*sf;
  int		*p_end;
  int		*p;
  /** 
    Se act_pos < 0: azione non esistente 
    **
    If act_pos < 0:  not existing action
  **/
  if (act_pos < 0)
    return(FALSE);
  sf = gcondef_conn[act_pos].sf;
  if (sf == NULL)
    return 0;
  for (p = sf->PC_overall, p_end = &sf->PC_overall[sf->num_PC_overall]; p < p_end; p++)
    if (*p == fact_pos)
      return(TRUE);
  return(FALSE);
}



/** OK 03/08/04 ------------------
 * Name: is_fact_in_preconditions_end
 * Scopo: Verificare se un fatto e' precondizione AT_END di un'azione condizionale
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output: TRUE se il fatto e' un precondizione AT_END dell'azione act_pos
 *         FALSE altrimenti
 * Strutture dati principali: gef_conn
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: choose_actions_dg_list
 *              choose_actions
 *              check_plan
 *              check_temporal_plan
**
*  Name:  is_fact_in_preconditions_end
*  Objective: To verify if a fact is an AT_END precondition of a conditional action
*  Type: int
*  Input: int act_pos
*         int act_pos
*  Output: TRUE if the fact is an AT_END precondition of the action act_pos
*  Main Data Structures: gef_conn
*  Main Functions Used:
*  Call gives: choose_actions_dg_list
*              choose_actions
*              check_plan
*              check_temporal_plan
**/
int is_fact_in_preconditions_end_of_cond (int act_pos, int fact_pos)
{
  SpecialFacts	*sf;
  int		*p_end;
  int		*p;
  /**
    Se act_pos < 0: azione non esistente
    **
    If act_pos < 0:  not existing action
  **/
  if (act_pos < 0)
    return(FALSE);
  sf = gcondef_conn[act_pos].sf;
  if (sf == NULL)
    return 0;
  for (p = sf->PC_end, p_end = &sf->PC_end[sf->num_PC_end]; p < p_end; p++)
    if (*p == fact_pos)
      return(TRUE);
  return(FALSE);
}



/** OK 03/08/04
 * Name: is_cond_action_applicable
 * Scopo: ritorna 0 se non applicabile 1 se applicabile
 * Tipo: int
 * Input: int level
 *        int pos
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_cond_action_applicable
*  Objective: return 0 if not applicable 1 if applicable
*  Type: int
*  Input: int level
*         int pos
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int is_cond_action_applicable (int level, int pos)
{
  int	     i;
  CondEfConn *cef;
  cef = &gcondef_conn[pos];
  /**
     Le precondizioni AT_START sono supportate
     **
     AT_START preconditions are supported
  **/
  for (i = 0; i < cef->num_PC; i++)
    if (vectlevel[level]->fact[cef->PC[i]].w_is_true <= 0)
      return 0;
  if (cef->sf != NULL) {
    /**
       Le precondizioni OVERALL sono supportate
       **
       OVERALL preconditions are supported
    **/
    for (i = 0; i < cef->sf->num_PC_overall; i++)
      if ((vectlevel[level]->fact[cef->sf->PC_overall[i]].w_is_true <= 0)  &&
	  (!is_fact_in_additive_effects_start_of_cond(pos, cef->sf->PC_overall[i])))
	return 0;
    /**
       Le precondizioni AT_END sono supportate
       **
       AT_END preconditions are supported
    **/
    for (i = 0; i < cef->sf->num_PC_end; i++)
      if ((vectlevel[level]->fact[cef->sf->PC_end[i]].w_is_true <= 0) &&
	  (!is_fact_in_additive_effects_start_of_cond(pos, cef->sf->PC_end[i])))
	return 0;
  }
  return 1;
}



/** OK 03/08/04
 * Name: is_fact_in_additive_effects
 * Scopo: Verifico se un fatto e' effetto additivo AT_END di un'azione
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_fact_in_additive_effects
*  Objective: Verify if a fact is an additive AT_END effect of an action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int is_fact_in_additive_effects (int act_pos, int fact_pos)
{
  register int i;
  if (act_pos < 0)
    return 0;
  for (i = 0; i < gef_conn[act_pos].num_A; i++)
    if (gef_conn[act_pos].A[i] == fact_pos)
      {
#ifdef __TEST1__
	printf ("\n Fact %d is in additive effecs of action %d; Fact  ", fact_pos, act_pos);
	print_ft_name (fact_pos);
	printf ("  action  ");
	print_op_name (act_pos);
#endif
	return TRUE;
      }
  return 0;
}


/** OK 03/08/04
 * Name: is_fact_in_delete_effects
 * Scopo: Verifico se un fatto e' effetto cancellante AT_END di un'azione
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_fact_in_delete_effects
*  Objective: Verify is a fact is a cancelling AT_END effect of an action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int is_fact_in_delete_effects (int act_pos, int fact_pos)
{
  register int i;
  if (act_pos < 0)
    return 0;
  for (i = 0; i < gef_conn[act_pos].num_D; i++)
    if (gef_conn[act_pos].D[i] == fact_pos)
      {

#ifdef __TEST1__
	printf ("\n Fact %d is in del effecs of action %d; Fact  ", fact_pos,
		act_pos);
	print_ft_name (fact_pos);
	printf ("  action  ");
	print_op_name (act_pos);

#endif
	return TRUE;
      }
  return 0;
}



/** OK 03/08/04
 * Name: is_fact_in_additive_effects_start
 * Scopo: Verifico se un fatto e' effetto additivo AT_START di un'azione
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_fact_in_additive_effects_start
*  Objective: Verify if a fact is an additive AT_START effect of an action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int is_fact_in_additive_effects_start (int act_pos, int fact_pos)
{
  register int i;
  if (act_pos < 0)
    return 0;
  if (gef_conn[act_pos].sf == NULL)
    return 0;
  for (i = 0; i < gef_conn[act_pos].sf->num_A_start; i++)
    if (gef_conn[act_pos].sf->A_start[i] == fact_pos)
      {
#ifdef __TEST1__
	printf
	  ("\n Fact %d is in additive effecs at start of action %d; Fact  ",
	   fact_pos, act_pos);
	print_ft_name (fact_pos);
	printf ("  action  ");
	print_op_name (act_pos);

#endif

	return (TRUE);
      }
  return 0;
}



/** OK 03/08/04
 * Name: is_fact_in_delete_effects_start 
 * Scopo: Verifico se un fatto e' effetto cancellante AT_START di un'azione
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_fact_in_delete_effects_start 
*  Objective: Verify if a fact is a cancelling AT_START effect of an action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int is_fact_in_delete_effects_start (int act_pos, int fact_pos)
{
  register int i;
  if (act_pos < 0)
    return 0;
  if (gef_conn[act_pos].sf == NULL)
    return 0;
  for (i = 0; i < gef_conn[act_pos].sf->num_D_start; i++)
    if (gef_conn[act_pos].sf->D_start[i] == fact_pos)
      {
#ifdef __TEST1__
	printf ("\n Fact %d is in del effecs at start of action %d; Fact  ",
		fact_pos, act_pos);
	print_ft_name (fact_pos);
	printf ("  action  ");
	print_op_name (act_pos);

#endif

	return (TRUE);
      }
  return 0;
}



/** OK 03/08/04
 * Name: is_fact_in_preconditions
 * Scopo: Verifico se un fatto e' precondizione AT-START di un'azione
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_fact_in_preconditions
*  Objective: Verify if a fact is an AT_START precondition of an action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int is_fact_in_preconditions (int act_pos, int fact_pos)
{
  register int i;
  if (act_pos < 0)
    return FALSE;
  if (GpG.timed_facts_present) {
    if ((fact_pos >= 0) && (gft_conn[fact_pos].fact_type == IS_TIMED)) {
      if (!gef_conn[act_pos].timed_PC)
	return FALSE;
      for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_start; i++)
	if (gef_conn[act_pos].timed_PC -> PC_start[i] == fact_pos)
	  return TRUE;
      return FALSE;
    }
  }
  for (i = 0; i < gef_conn[act_pos].num_PC; i++)
    if (gef_conn[act_pos].PC[i] == fact_pos)
      {

#ifdef __TEST1__
	printf ("\n Fact %d is in precondition of action %d; Fact  ",
		fact_pos, act_pos);
	print_ft_name (fact_pos);
	printf ("  action  ");
	print_op_name (act_pos);

#endif
	return TRUE;
      }
  return FALSE;
}



/** OK 03/08/04
 * Name: is_fact_in_preconditions_overall
 * Scopo: Verifico se un fatto e' precondizione OVERALL di un'azione 
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_fact_in_preconditions_overall
*  Objective: Verify if a fact is an OVERALL precondition of an action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int is_fact_in_preconditions_overall (int act_pos, int fact_pos)
{
  register int i;
  if (act_pos < 0)
    return FALSE;
  if (GpG.timed_facts_present) {
    if ((fact_pos >= 0) && (gft_conn[fact_pos].fact_type == IS_TIMED)) {
      if (!gef_conn[act_pos].timed_PC)
	return FALSE;
      for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_overall; i++)
	if (gef_conn[act_pos].timed_PC -> PC_overall[i] == fact_pos)
	  return TRUE;
      return FALSE;
    }
  }
  if (gef_conn[act_pos].sf == NULL)
    return 0;
  for (i = 0; i < gef_conn[act_pos].sf->num_PC_overall; i++)
    if (gef_conn[act_pos].sf->PC_overall[i] == fact_pos)
      {
#ifdef __TEST1__
	printf ("\n Fact %d is in prec over all of action %d; Fact  ",
		fact_pos, act_pos);
	print_ft_name (fact_pos);
	printf ("  action  ");
	print_op_name (act_pos);

#endif
	return (TRUE);
      }
  return FALSE;
}



/** OK 03/08/04
 * Name:i is_fact_in_preconditions_end
 * Scopo: Verifico se un fatto e' precondizione AT_END di un'azione
 * Tipo: int
 * Input: int act_pos
 *        int fact_pos
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_fact_in_preconditions_end
*  Objective: Verify if a fact is a AT_END precondition of an action
*  Type: int
*  Input: int act_pos
*         int fact_pos
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int is_fact_in_preconditions_end (int act_pos, int fact_pos)
{
  register int i;
  if (act_pos < 0)
    return FALSE;
  if (GpG.timed_facts_present) {
    if ((fact_pos >= 0) && (gft_conn[fact_pos].fact_type == IS_TIMED)) {
      if (!gef_conn[act_pos].timed_PC)
	return FALSE;
      for (i = 0; i < gef_conn[act_pos].timed_PC -> num_PC_end; i++)
	if (gef_conn[act_pos].timed_PC -> PC_end[i] == fact_pos)
	  return TRUE;
      return FALSE;
    }
  }
  if (gef_conn[act_pos].sf == NULL)
    return 0;
  for (i = 0; i < gef_conn[act_pos].sf->num_PC_end; i++)
    if (gef_conn[act_pos].sf->PC_end[i] == fact_pos)
      {
#ifdef __TEST1__
	printf ("\n Fact %d is in prec end of action %d; Fact  ", fact_pos,
		act_pos);
	print_ft_name (fact_pos);
	printf ("  action  ");
	print_op_name (act_pos);

#endif
	return (TRUE);
      }
  return FALSE;
}



/** OK 03/08/04 -------------------
 * Name: is_action_applicable
 * Scopo: Determinare se un'azione e' applicabile o meno
 * Tipo: int
 * Input: int level
 *        int pos
 * Output: 1 se e' applicabile
 *         0 se non e' applicabile
 * Strutture dati principali: gef_conn[]
 * Funzioni principali utilizzate: is_fact_in_additive_effects_start
 *                                 is_fact_in_delete_effects
 * Chiamata da: nessuno
**
*  Name: is_action_applicable
*  Objective: To determine if an action is applicable or not
*  Type: int
*  Input: int level
*         int pos
*  Output: 1 if is applicable
*          0 if is not applicable
*  Main Data Structures: gef_conn[ ]
*  Main Functions Used: is_fact_in_additive_effects_start
*                       is_fact_in_delete_effects
*  Call gives:
**/
int is_action_applicable (int level, int pos)
{
  /**
    Intero di appoggio
    **
    Integer of support
  **/
  int i;
  /**
    Controlla che tutte le precondizioni dell'azione siano supportate
    **
    It controls that all the preconditions of the action are supported
  **/

  /**
     Le precondizioni AT_START sono supportate
     **
     AT_START preconditions are supported
  **/
  for (i = 0; i < gef_conn[pos].num_PC; i++)
    if (vectlevel[level]->fact[gef_conn[pos].PC[i]].w_is_true <= 0)
      return 0;

  if (gef_conn[pos].sf != NULL) {
    /**
       Le precondizioni OVERALL sono supportate
       **
       OVERALL precondition are supported
    **/
    for (i = 0; i < gef_conn[pos].sf->num_PC_overall; i++)
      if (!is_fact_in_additive_effects_start(pos, gef_conn[pos].sf->PC_overall[i])
	  && vectlevel[level]->fact[gef_conn[pos].sf->PC_overall[i]].w_is_true <= 0)
	return 0;
    /**
       Le precondizioni AT_END sono supportate
       **
       AT_END preconditions are supported
    **/
    for (i = 0; i < gef_conn[pos].sf->num_PC_end; i++)
      if ( (!is_fact_in_additive_effects_start(pos, gef_conn[pos].sf->PC_end[i]))
	  && vectlevel[level]->fact[gef_conn[pos].sf->PC_end[i]].w_is_true <= 0)
	return 0;
  }
  return 1;
}



/** OK 03/08/04
 * Name: fact_is_supported 
 * Scopo: Ritorna TRUE se il fatto è supportato
 * Tipo: int
 * Input: int Fact_position
 *        int Fact_level
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: fact_is_supported 
*  Objective: Return TRUE if the fact is supported,
*  Type: int
*  Input: int Fact_position
*         int Fact_level
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int fact_is_supported (int Fact_position, int Fact_level)
{
  if (Fact_position < 0)
    return (is_num_prec_satisfied (Fact_position, Fact_level));
  if ((vectlevel[Fact_level]->fact_vect[GUID_BLOCK (Fact_position)]) & GUID_MASK (Fact_position))
    return TRUE;
  else
    return FALSE;
}



/** OK 03/08/04
 * Name: is_fact_supported_in_relaxed_plan
 * Scopo: Ritorna TRUE se il fatto è supportato
 * Tipo: int
 * Input: int Fact_position
 *        int Fact_level
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_fact_supported_in_relaxed_plan
*  Objective: Return TRUE if the fact is supported
*  Type: int
*  Input: int Fact_position
*         int Fact_level
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int is_fact_supported_in_relaxed_plan (int Fact_position, int Fact_level)
{
  if (Fact_position < 0)
    return (is_num_prec_satisfied_in_common_level (Fact_position));
  //  if ( GET_BIT (Hvar.bit_vect_facts, Fact_position) || GET_BIT (Hvar.initial_relaxed_bit_vect_facts, Fact_position) )
  if (  GET_BIT (Hvar.initial_relaxed_bit_vect_facts, Fact_position) )
    return TRUE;
  else
    return FALSE;
}



/***************************************
            LINK CAUSALI
 ***************************************/



/** OK 03/08/04 -----------------
 * Name: insert_treated_noop_chain
 * Scopo: Inserire la posizione di una noop nella lista delle noop non inserite per gli effetti additivi
 * Tipo: void
 * Input: inform * act
 *        unsigned int pos
 * Output: nessuno
 * Strutture dati principali: noop_not_in
 *                            inform
 *                            noop_free_list
 * Funzioni principali utilizzate: insert_treated_fact
 * Chiamata da: insert_action_in_vectlevel
**
*  Name:  insert_treated_noop_chain
*  Objective: To insert the position of a noop in the list of the noop not inserted for the additive effects
*  Type: void
*  Input: inform * act
*         unsigned int pos
*  Output: none
*  Main Data Structures: noop_not_in
*                        inform
*                        noop_free_list
*  Main Functions Used: insert_treated_fact
*  Call gives: insert_action_in_vectlevel
**/
void insert_treated_noop_chain (ActNode_list act, unsigned int pos)
{
  /**
    Variabile di appoggio
    **
    Variable of support
  **/
  noop_not_in *new;
  /**
    Se la lista noop_free_list non e' ancora stata allocata alloco memoria
    **
    If the list noop_free_list have not been allocated yet I allocate memory
  **/
  if (noop_free_list == NULL)
    new = (noop_not_in *) calloc (1, sizeof (noop_not_in));
  else
    {
      /**
	Assegno a new il primo elemento della lista noop_free_list
	**
	Check to new the first element of the list noop_free_list
      **/
      new = noop_free_list;
      noop_free_list = noop_free_list->next;
    }
  /**
    Assegno alla posizione di new (position) la posizione della noop passata in ingresso
    **
    Assigning to the position of new (position) the position of the noop passed in input
  **/
  new->position = pos;
  /**
    Se la lista delle noop non inserite (act->treated) e' vuota allora new->next = NULL
    **
    If the list of the noop not inserted (act->treated) is empty then new->next = NULL
  **/
  if (act->treated == NULL)	//init list
    /**
      Pongo il nuovo elemento all'inizio della lista delle noop minacciate dall'azione act
      **
      I place the new element to the beginning of the list of the noop threatened from the action act
    **/
    new->next = NULL;
  else
    /**
      Pongo il nuovo elemento all'inizio della lista delle noop minacciate dall'azione act
      **
      I place the new element to the beginning of the list of the noop threatened from the action act
    **/
    new->next = act->treated;	//update list
  /**
    Aggiorno il puntatore alla lista delle noop minacciate dall'azione act
    **
    Updating the pointer to the list of the noop threatened from the action act
  **/
  act->treated = new;
  /**
    Inserisco il fatto della noop nei fatti non supportati
    **
    Inserting the fact of the noop in the facts not supported
  **/
  insert_treated_fact (act, pos);

#ifdef __TEST__
  if (DEBUG3)
    printf ("\n\n  insert_treated_noop_chain %s action %s time %d",
	    print_noop_name_string (pos, temp_name),
	    print_op_name_string (act->position, temp_name), *act->level);
#endif
}



/***************************************
                ALLOCATE
 ***************************************/



/** OK 03/08/04 ----------------
 * Name: allocate_after_parser
 * Scopo: Settare alcuni parametri e variabili globali
 * Tipo: void
 * Input: nessuno
 * Output: nessuno
 * Strutture dati principali: nessuna
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: main
**
*  Name:  allocate_after_parser
*  Objective: Setting some parameters and global variables
*  Type: void
*  Input: none
*  Output: none
*  Main Data Structures: none
*  Main Functions Used: none
*  Call gives: main
**/
void allocate_after_parser()
{
 
  gcomp_var=(CompositeNumVar *)calloc(MAX_NUM_INITIAL,sizeof(CompositeNumVar));
  memset(gcomp_var, 0, MAX_NUM_INITIAL * sizeof(CompositeNumVar));

  gcomp_var_effects=(CompositeNumVar *)calloc(MAX_NUM_INITIAL,sizeof(CompositeNumVar));
  memset(gcomp_var_effects, 0, MAX_NUM_INITIAL * sizeof(CompositeNumVar));

  gcomp_var_value = (float *)calloc(MAX_NUM_INITIAL, sizeof(float));
  memset (gcomp_var_value, 0, MAX_NUM_INITIAL * sizeof(float));
  
  gcomp_var_value_before = (float *)calloc(MAX_NUM_INITIAL, sizeof(float));
  memset (gcomp_var_value_before, 0, MAX_NUM_INITIAL * sizeof(float));

  gis_inertial = (int *)calloc(((MAX_NUM_INITIAL>>5) + 1), sizeof(int));
  memset (gis_inertial, 0, ((MAX_NUM_INITIAL>>5) + 1) * sizeof(int));

  Hvar.list_ef_define_cost = (int *) calloc (MAX_LENGTH_H, sizeof (int));
  Hvar.list_ft_define_cost = (int *) calloc (MAX_LENGTH_H, sizeof (int));
}



/** OK 03/08/04
 * Name: allocate_data_for_local_search
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: allocate_data_for_local_search
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void allocate_data_for_local_search()
{
  int i, step;
  char *ptr, *ptr1;

  mat_ord = (char **) calloc (MAX_NUM_ACTIONS, sizeof (char *));
  ptr = (char *) calloc (MAX_NUM_ACTIONS * MAX_NUM_ACTIONS, sizeof (char));
  step=MAX_NUM_ACTIONS;

  ptr1 =ptr;
  for (i = 0; i < MAX_NUM_ACTIONS; i++, ptr1 +=  step )
    mat_ord[i] = ptr1;

  act_ord_vect = (ActNode_list *)calloc(MAX_NUM_ACTIONS,sizeof(ActNode_list)); 
  
  prop_level_index = (short *)calloc(MAX_PLAN_LENGTH,sizeof(short));

  remove_act_chain = (ActNode_list *)calloc(MAX_PLAN_LENGTH,sizeof(ActNode_list));
  remove_act_chain_next_step = (ActNode_list *)calloc(MAX_PLAN_LENGTH,sizeof(ActNode_list));
 
  pos_temp_vect = (int *) calloc (MAX_MAX_NODES, sizeof (int));

  fact_costs = (node_cost *) calloc (MAX_MAX_NODES, sizeof (node_cost));

  Hvar.tmp_path.size = 0;
  Hvar.tmp_path.tuple_set = NULL;
  
  gdp_path.size = 0;
  gdp_path.tuple_set = NULL;

  if(GpG.supported_preconds_evaluation)
    {
      Hvar.num_supported_preconds=0;

      Hvar.supported_preconds= (int *)calloc(gnum_ft_conn, sizeof(int));
    }
  Hvar.supported_bit_vect_preconds  = alloc_vect (gnum_ft_block);

  if( GpG.avoid_best_action_cycles )
    {
      if( Hvar.best_act_insertion_array==NULL)
	Hvar.best_act_insertion_array= ( int * ) calloc( gnum_ef_conn, sizeof( int ) );
      if(Hvar.best_act_for_fact_array==NULL) 
	Hvar.best_act_for_fact_array=  ( int * ) calloc( gnum_ef_conn, sizeof( int ) );
    }
  if(GpG.initialize_inc_choice==0 &&   GpG.is_domain_numeric==TRUE)
    GpG.inc_choice_type=GpG.orig_inc_choice=MIN_LEVEL_CONSTR_INC;

}



/***************************************
                 VARIOUS
 ***************************************/



/** OK 03/08/04
 * Name: random_for_debug
 * Scopo:
 * Tipo: int
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: random_for_debug
*  Objective:
*  Type: int
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int random_for_debug()
{
  int rnd;
  rnd=random();
  if(DEBUG5)
    printf("\nrnd=%d   ",rnd);
  return rnd;
}




#ifndef __WINLPG__

/** OK 03/08/04
 * Name: DeltaTime
 * Scopo:
 * Tipo: float
 * Input: struct tms start
 *        struct tms end
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: DeltaTime
*  Objective:
*  Type: float
*  Input: struct tms start
*         struct tms end
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
float DeltaTime (struct tms start, struct tms end)
{
  return ((float) ((end.tms_utime - start.tms_utime + end.tms_stime -
		    start.tms_stime) / 100.0));
}
#else

/** OK 03/08/04
 * Name: DeltaTime
 * Scopo:
 * Tipo: float
 * Input: clock_t start
 *        clock_t end
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: DeltaTime
*  Objective:
*  Type: float
*  Input: clock_t start
*         clock_t end
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
float DeltaTime (clock_t start, clock_t end)
{
  float secs = 0.0;
  secs = (float) (end - start) / (CLK_TCK);
  return secs;
}
#endif



/** OK 03/08/04
 * Name: get_path
 * Scopo:
 * Tipo: void
 * Input: char *full_file_name
 *        char *result
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: get_path
*  Objective:
*  Type: void
*  Input: char *full_file_name
*         char *result
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void get_path (char *full_file_name, char *result)
{
  int last_slash = -1, i;
  for (i = 0; i < strlen (full_file_name); i++)
    if (full_file_name[i] == '/')
      last_slash = i;
  if (last_slash == -1)
    strcpy (result, "./");
  else
    {
      strcpy (result, full_file_name);
      result[last_slash + 1] = '\0';
    }
}



/***************************************
           HELPING FUNCTIONS
 ***************************************/



/** OK 03/08/04
 * Name: output_planner_info
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: output_planner_info
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void output_planner_info (void)
{
  printf ("\n\ntime spent: %7.2f seconds instantiating %d easy, %d hard action templates", gtempl_time, gnum_easy_templates, gnum_hard_mixed_operators);
  printf ("\n            %7.2f seconds reachability analysis, yielding %d facts and %d actions", greach_time, gnum_pp_facts, gnum_actions);
  printf ("\n            %7.2f seconds creating final representation with %d relevant facts", grelev_time, gnum_relevant_facts);
  printf ("\n            %7.2f seconds building connectivity graph", gconn_time);
  printf ("\n            %7.2f seconds creating %d primary vars and %d numeric relations", gnum_time, gnum_fullnum_initial, gnum_comp_var);
  printf ("\n            %7.2f seconds creating %d mutex relations, in %d levels", gmutex_total_time, gnum_mutex, GpG.fixpoint_plan_length);
  printf ("\n            %12.2f seconds for mutex between facts", gmutex_ft_time);
  printf ("\n            %12.2f seconds for other logical mutex", gmutex_ops_time);
  printf ("\n            %12.2f seconds for mutex from numeric effects", gmutex_num_time);
  printf ("\n            %7.2f seconds searching, evaluating %d states, to a max depth of %d", gsearch_time, gevaluated_states, gmax_search_depth);
  printf ("\n            %7.2f seconds total time", gtempl_time + greach_time + grelev_time + gconn_time + gsearch_time + gnum_time + gmutex_total_time);
  printf ("\n\n");
}



/** OK 03/08/04
 * Name: lpg_usage
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: lpg_usage
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void lpg_usage (void)
{
  printf ("\n%s SETTINGS:\n",VERSION);
  printf ("\nNECESSARY SETTINGS\n\n");
  printf ("-o <string>              specifies the file of the operators \n\n");
  printf ("-f <string>              specifies the file of (init/goal) facts\n\n");
  printf ("-n <number>              specifies the desired number of solutions;\n"); 
  printf ("                         alternative options are -speed and -quality\n\n");
  printf ("\nOPTIONAL SETTINGS\n\n");
  printf ("-p <string>              specifies the path for the operator/fact files\n\n");
  printf ("-out <string>            specifies the file name for computed plans\n\n");
  printf ("-noout                   does not save computed plans\n\n");
  //  printf ("-inst_with_contraddicting_objects   includes operator instances with same objects\n");
  //  printf ("                         for different parameters\n\n");
  //  printf ("-h  1|2                  specifies the heuristic function [default 1]\n\n");
  printf ("-v off                   switches off verbose mode\n\n");

  printf ("-search_steps <number>   specifies the number of steps of the first\n");
  printf ("                         restart of the local search [default 500]\n\n");
  printf ("-restarts <number>       specifies the max number of the restarts [default 9]\n\n");
  printf ("-repeats <number>        specifies the maximum number of the repeats [default 5]\n\n");

  printf ("-noise <0..1>            specifies the initial noise value of Walkplan [default 0.10]\n\n");
  printf ("-static_noise            set the noise value to a fixed static value\n\n");
  //  printf ("-tabu_length <number>    sets the length of a simple tabu list [default 5]\n\n");
  printf ("-seed <number>           sets the seed of the random number generator\n\n");
 //  printf ("-i_choice <number>       specifies the inconsistency selection method\n");
  //  printf ("                         [default 22]\n\n");




  printf ("-lowmemory               computes mutex relations between actions at runtime\n\n");

  printf ("-cputime <number>        specifies the maximum CPU-time (in seconds) [default 1800]\n\n");
  printf ("-cputime_localsearch <number>        specifies the maximum CPU-time for \n"); 
  printf ("                         the local search procedure (in seconds) [default 1200] \n\n"); 


  printf ("-nobestfirst             switches off best-first search\n\n");
  printf ("-onlybestfirst           immediately runs best-first search\n\n");

 
  /*  printf ("-AdvancedTime            takes overlapping of actions into account during the\n");
  printf ("                         neighborhood evaluation. This option sometimes leads\n");
  printf ("                         to plans of better quality\n\n");
  */
  /*  printf("-info <num>    run-time information level [ default: 1 ]\n");
     printf("      0     only times\n");
     printf("      1     problem name, planning process infos\n");
     printf("    100     parsed problem data before reduction to PDDL1\n");
     printf("    101     parsed problem data after reduction to PDDL1\n");
     printf("    102     cleaned up ADL problem\n");
     printf("    103     collected string tables\n");
     printf("    104     encoded domain\n");
     printf("    105     predicates inertia info\n");
     printf("    106     splitted initial state\n");
     printf("    107     domain with Wff s normalized\n");
     printf("    108     domain with NOT conds translated\n");
     printf("    109     splitted domain\n");
     printf("    110     cleaned up easy domain\n");
     printf("    111     unaries encoded easy domain\n");
     printf("    112     effects multiplied easy domain\n");
     printf("    113     inertia removed easy domain\n");
     printf("    114     easy action templates\n");
     printf("    115     cleaned up hard domain representation\n");
     printf("    116     mixed hard domain representation\n");
     printf("    117     final hard domain representation\n");
     printf("    118     reachability analysis results\n");
     printf("    119     facts selected as relevant\n");
     printf("    120     final domain and problem representations\n");
     printf("    121     connectivity graph\n");
     printf("    122     fixpoint result on each evaluated state\n");
     printf("    123     1P extracted on each evaluated state\n");
     printf("    124     H set collected for each evaluated state\n");
     printf("    125     False sets of goals <GAM>\n");
     printf("    126     detected ordering constraints leq_h <GAM>\n");
     printf("    127     the Goal Agenda <GAM>\n"); */
  /*   printf("    109     reachability analysis results\n"); */
  /*   printf("    110     final domain representation\n"); */
  /*   printf("    111     connectivity graph\n"); */
  /*   printf("    112     False sets of goals <GAM>\n"); */
  /*   printf("    113     detected ordering constraints leq_h <GAM>\n"); */
  /*   printf("    114     the Goal Agenda <GAM>\n"); */
  /*   printf("    115     fixpoint result on each evaluated state <1Ph>\n"); */
  /*   printf("    116     1P extracted on each evaluated state <1Ph>\n"); */
  /*   printf("    117     H set collected for each evaluated state <1Ph>\n"); */

  printf ("\n ");
}



/***************************************
             COMMAND LINE
 ***************************************/



/** OK 04/08/04
 * Name: process_command_line
 * Scopo:
 * Tipo: Bool
 * Input: int argc
 *        char *argv[]
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: process_command_line
*  Objective:
*  Type: Bool
*  Input:int argc
*        char *argv[]
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
Bool process_command_line (int argc, char *argv[])
{
  char temp[3];
  int i, heuristic;
  float noise;

  gcmd_line.display_info = 1;
  gcmd_line.debug = 0;
  gcmd_line.max_plan_ops = 0;
  gcmd_line.max_cpu_time = 0;
  memset (gcmd_line.out_file_name, 0, MAX_LENGTH  * sizeof(char) );
  memset (gcmd_line.fct_file_name, 0, MAX_LENGTH * sizeof(char));
  memset (gcmd_line.path, 0, MAX_LENGTH * sizeof(char));
  for (i = 1; i < argc; i++)
    {
      if (argv[i][0] != '-')
	continue;
      if (strcmp (argv[i], "-p") == 0)
	strncpy (gcmd_line.path, argv[++i], MAX_LENGTH);
      else if (strcmp (argv[i], "-o") == 0)
	strncpy (gcmd_line.ops_file_name, argv[++i], MAX_LENGTH);
      else if (strcmp (argv[i], "-f") == 0)
	strncpy (gcmd_line.fct_file_name, argv[++i], MAX_LENGTH);
      else if (strcmp (argv[i], "-P") == 0)
	strncpy (gcmd_line.sol_file_name, argv[++i], MAX_LENGTH);
      else if (strcmp (argv[i], "-info") == 0)
	sscanf (argv[++i], "%d", &gcmd_line.display_info);
      else if (strcmp (argv[i], "-d") == 0)
	sscanf (argv[++i], "%d", &gcmd_line.debug);
      else if (strcmp (argv[i], "-L") == 0)
	sscanf (argv[++i], "%d", &gcmd_line.max_plan_ops);
      else if (strcmp (argv[i], "-T") == 0)
	sscanf (argv[++i], "%f", &gcmd_line.max_cpu_time);
      else if (strcmp (argv[i], "-out") == 0)
	{
	  strncpy (gcmd_line.out_file_name, argv[++i], MAX_LENGTH);
	  GpG.out_file_name = TRUE;
	}
      else if (strcmp (argv[i], "-timesteps") == 0)
	{
	  //	  GpG.temporal_plan = TRUE;
	  GpG.orig_weight_time = 1.0;
	  GpG.orig_weight_cost = 0.0;
	}
      else if (strcmp (argv[i], "-AdvancedTime") == 0)
	sscanf (argv[++i], "%d", &GpG.constraint_type);
      else if (strcmp (argv[i], "-wcost") == 0)
	sscanf (argv[++i], "%f", &GpG.orig_weight_cost);
      else if (strcmp (argv[i], "-wtime") == 0)
	sscanf (argv[++i], "%f", &GpG.orig_weight_time);
      else if (strcmp (argv[i], "-heuristic") == 0)
	{
	  sscanf (argv[++i], "%d", &GpG.orig_accurate_cost);
	  GpG.accurate_cost = GpG.orig_accurate_cost;
	}
      else if (strcmp (argv[i], "-num_sol") == 0 || strcmp (argv[i], "-n") == 0)
	{
	  if (GpG.mode == SPEED || GpG.mode == QUALITY)
	    {
	      printf("\n\nWarning: Option -n, -speed, and -quality are mutually exclusive\n\n");
	      exit(0);
	    }
	  GpG.mode = INCREMENTAL;
	  sscanf (argv[++i], "%d", &GpG.max_num_solutions);
	}
      else if (strcmp (argv[i], "-speed") == 0)
	{ 
	  if (GpG.mode == INCREMENTAL || GpG.mode == QUALITY)
	    {
	      printf("\n\nWarning: Option -n, -speed, and -quality are mutually exclusive\n\n");
	      exit(0);
	    }
	  GpG.mode = SPEED;
	  GpG.max_num_solutions = 1;
	}
      else if (strcmp (argv[i], "-quality") == 0)
	{
	  if (GpG.mode == INCREMENTAL || GpG.mode == SPEED)
	    {
	      printf("\n\nWarning: Option -n, -speed, and -quality are mutually exclusive\n\n");
	      exit(0);
	    }
	  GpG.max_num_solutions = 1000;
	  GpG.mode = QUALITY;
	}
      else if (strcmp (argv[i], "-lowmemory") == 0)
	GpG.lowmemory=TRUE;
      else if (strcmp (argv[i], "-total_time_goal") == 0)
	 GpG.total_time_goal = TRUE;
      else if (strcmp (argv[i], "-incchoice") == 0
	       || strcmp (argv[i], "-ichoice") == 0   || strcmp (argv[i], "-i_choice") == 0)
	{
	  sscanf (argv[++i], "%d", &GpG.orig_inc_choice);
	  GpG.inc_choice_type=GpG.orig_inc_choice;
	  GpG.initialize_inc_choice=1;
	}
      //MODIFICHE COCCOLI
      else if (strcmp (argv[i], "-nonuniform_random") == 0)
	GpG.nonuniform_random_incosistence_test = 1;

      else if (strcmp (argv[i], "-seed") == 0)
	sscanf (argv[++i], "%d", &seed);

      else if (strcmp (argv[i], "-numtry") == 0
	       || strcmp (argv[i], "-num_flips") == 0
	       || strcmp (argv[i], "-search_steps") == 0)
	sscanf (argv[++i], "%d", &GpG.numtry);

      else if (strcmp (argv[i], "-numrestart") == 0
	       || strcmp (argv[i], "-restarts") == 0
	       || strcmp (argv[i], "-num_tries") == 0)
	sscanf (argv[++i], "%d", &GpG.numrestart);

      else if (strcmp (argv[i], "-numrepeats") == 0
	       || strcmp (argv[i], "-repeats") == 0 )
	sscanf (argv[++i], "%d", &GpG.numrun);

      else if (strcmp (argv[i], "-info_search") == 0)
	{
	  sscanf (argv[++i], "%d", &GpG.info_search);
#ifndef __TEST__
	  if (GpG.info_search > 6)
	    GpG.info_search = 6;
#endif
	}
      else if (strcmp (argv[i], "-bestfirst") == 0)
	GpG.do_best_first = TRUE;
      else if (strcmp (argv[i], "-nobestfirst") == 0)
	GpG.do_best_first = FALSE;
      else if (strcmp (argv[i], "-h") == 0)
	{
	  if (argv[i+1]!=NULL)
	    {
	      sscanf (argv[++i], "%d", &heuristic);
	      if(heuristic == COMPUTE_MAX_COST)
		GpG.orig_accurate_cost = GpG.accurate_cost = COMPUTE_MAX_COST;
	      else if(heuristic == COMPUTE_FAST_COST)
		GpG.orig_accurate_cost = GpG.accurate_cost = COMPUTE_FAST_COST;
	    }
	}
      else if (strcmp (argv[i], "-adaptfirst") == 0)
	GpG.do_adapt_first = TRUE;
      else if (strcmp (argv[i], "-noout") == 0)
	GpG.noout = TRUE;
      else if (strcmp (argv[i], "-fastadapt") == 0)
	GpG.do_fast_adapt = TRUE;
      else if (strcmp (argv[i], "-onlybestfirst") == 0)
	{
	  GpG.do_best_first = TRUE;
	  GpG.numrestart = 0;
	}
      else if (strcmp (argv[i], "-inst_duplicate_param") == 0
	       || strcmp (argv[i], "-inst_with_contraddicting_objects") == 0
               || strcmp (argv[i], "-same_objects") == 0)
	GpG.inst_duplicate_param = TRUE;
      else if (strcmp (argv[i], "-maximize") == 0)
	GpG.maximize_plan = TRUE;
      else if (strcmp (argv[i], "-pop") == 0)
	GpG.pop = TRUE;
      else if (strcmp (argv[i], "-searchcostx1stsol") == 0)
	GpG.onlysearchcostx1stsol = FALSE;
      else if (strcmp (argv[i], "-onlysearchcostx1stsol") == 0)
	GpG.onlysearchcostx1stsol = TRUE;
      else if (strcmp (argv[i], "-validate") == 0)
	GpG.validate = TRUE;
      else if (strcmp (argv[i], "-noise") == 0)
	{
	  sscanf (argv[++i], "%f", &noise);
	  GpG.orig_numerator = (int) (noise * 100);
	  GpG.numerator =  GpG.orig_numerator;
	  GpG.init_numerator =  GpG.orig_numerator;
	}
      else if (strcmp (argv[i], "-static_noise") == 0)
	GpG.static_noise = TRUE;

      else if (strcmp (argv[i], "-maxnoise") == 0)
	sscanf (argv[++i], "%d", &GpG.max_numerator);

      else if (strcmp (argv[i], "-advanced_temporal_setting") == 0)
	sscanf (argv[++i], "%d", &GpG.advanced_temporal_setting);
      /** 
	  Opzioni per LA
	  **
	  Options for LA
      **/
      else if (strcmp (argv[i], "-lagrange") == 0)
	sscanf (argv[++i], "%d", &GpG.lagrange_multipl);
      else if (strcmp(argv[i], "-lm_multilevel") == 0)
	GpG.lm_multilevel = 1;
      else if (strcmp (argv[i], "-lm_incrprec") == 0)
	sscanf (argv[++i], "%f", &GpG.s_s_step);
      else if (strcmp (argv[i], "-lm_decrprec") == 0)
	sscanf (argv[++i], "%f", &GpG.sqr_s_s);
      else if (strcmp (argv[i], "-lm_incrme") == 0)
	sscanf (argv[++i], "%f", &GpG.s_s_step_me);
      else if (strcmp (argv[i], "-lm_decrme") == 0)
	sscanf (argv[++i], "%f", &GpG.sqr_s_s_me);
      /**
	 fine LA
	 **
	 end LA
      **/
      else if (strcmp (argv[i], "-cputime") == 0)
	sscanf (argv[++i], "%f", &GpG.max_cputime);
      else if (strcmp (argv[i], "-cputime_localsearch") == 0)
	sscanf (argv[++i], "%f", &GpG.max_cputime_for_local_search);
      else if (strcmp (argv[i], "-v") == 0)
	{
	  sscanf (argv[++i], "%s", temp);
	  if (strcmp (temp, "off") == 0)
	    GpG.verbose = FALSE;
	}
      else if (strcmp (argv[i], "-l_rate+") == 0)
	sscanf (argv[++i], "%f", &GpG.s_s_step);
      else if (strcmp (argv[i], "-l_rate-") == 0)
	sscanf (argv[++i], "%f", &GpG.sqr_s_s);
      else if (strcmp (argv[i], "-verifyinit") == 0)
	GpG.verify_init=1;
      else if (strcmp (argv[i], "-verifyAf") == 0)
	GpG.verify_Af=1; 
      else if (strcmp (argv[i], "-verifyincchoice") == 0)
            GpG.verify_inc_choice=0;
      else if (strcmp (argv[i], "-criprecond") == 0)
	sscanf (argv[++i], "%d", &GpG.cri_evaluate_preconditions);
       /** 
	   Compute reachability inform: 6- relaxed plan; 5- max ; 4 sum
	**/
       else if (strcmp (argv[i], "-relaxed_examination") == 0)
	GpG.relaxed_examination_type=1;
       /** 
	  Compute reachab. inform: 0- ricerca in profondita'
	                           1- ricerca in ampiezza
	  **
	  Compute reachab. inform: 0- deep research
	                           1- amplitude research
	**/
       /**
	   Diverse funzioni di valutazione elementi del vicinato
	   1- articolo JAIR
	   2- articolo JAIR senza coefficiente k
	   0- valutaz alternativa non documentata
	**/
      else if (strcmp (argv[i], "-evaluation_function") == 0)
	sscanf (argv[++i], "%d", &GpG.evaluation_function);
       /** 
	   Aggiunta gestione a lista per informazioni raggiungibilita'
	**/
      else if (strcmp (argv[i], "-ri_list") == 0)
	GpG.relax_list_fact_cost=1;
       /** 
	   Aggiunta gestione a lista per informazioni raggiungibilita'
	**/
      else if (strcmp (argv[i], "-verify_action_remotion_negative_numeric_effects") == 0)
	GpG.verify_action_remotion_negative_numeric_effects=1;
      else if (strcmp (argv[i], "-no_action_remotion_negative_numeric_effects") == 0)
	GpG.verify_action_remotion_negative_numeric_effects=0;
      else if (strcmp (argv[i], "-verify_negative_numeric_effects") == 0)
	 GpG.verify_negative_numeric_effects=1;
      else if (strcmp (argv[i], "-no_negative_numeric_effects") == 0)
	 GpG.verify_negative_numeric_effects=0;
      else if (strcmp (argv[i], "-hpar_cut_neighb") == 0)
	sscanf (argv[++i], "%d", &GpG.high_cost_restrict_neighb);
      else if (strcmp (argv[i], "-no_hcut_neighb") == 0)
	GpG.hcost_neighb = FALSE;
      else if (strcmp (argv[i], "-npar_cut_neighb") == 0)
	sscanf (argv[++i], "%d", &GpG.num_elem_neighb_restrict);
      else if (strcmp (argv[i], "-ncut_neighb") == 0)
	GpG.number_restrict_neighb = TRUE;
      else if (strcmp (argv[i], "-no_lcut_neighb") == 0)
	GpG.level_restrict_neighb = FALSE;
      else if (strcmp (argv[i], "-lpar_cut_neighb") == 0)
	sscanf (argv[++i], "%d", &GpG.neighb_elements_for_level_restrict);
      else if (strcmp (argv[i], "-cri_update_iterations") == 0)
	sscanf (argv[++i], "%d", &GpG.cri_update_iterations);
      else if (strcmp (argv[i], "-walkplan") == 0
	       || strcmp (argv[i], "-notabuplan") == 0)
	{
	  GpG.tabuplan_act = FALSE;
	  GpG.tabuplan_fct = FALSE;
	}
      else if (strcmp (argv[i], "-notabu_act") == 0)
	GpG.tabuplan_act = FALSE;
      else if (strcmp (argv[i], "-notabu_fct") == 0)
	GpG.tabuplan_fct = FALSE;
      else if (strcmp (argv[i], "-twalkplan") == 0)
	{
	  GpG.tabuplan_act = FALSE;
	  GpG.tabuplan_fct = FALSE;
	  GpG.Twalkplan = TRUE;
	}
     else if (strcmp (argv[i], "-tabu_length") == 0)
       {
	 sscanf (argv[++i], "%d", &GpG.init_tabu_length);
	 GpG.tabu_length =GpG.init_tabu_length ;
       }

      else if (strcmp (argv[i], "-remove_act_next_step") == 0)
	GpG.remove_actions_in_next_step = TRUE;
      else if (strcmp (argv[i], "-neighb_without_timed_fa") == 0)
	GpG.neighb_with_timed_fa = FALSE;
      else if (strcmp (argv[i], "-zero_num_A") == 0)
	GpG.zero_num_A = TRUE;
      else if (strcmp (argv[i], "-penalize_inconsistence") == 0)
	sscanf (argv[++i], "%d", &GpG.penalize_inconsistence_in_relaxed_plan);
      else if (strcmp (argv[i], "-cri_insertion_add_mutex") == 0)
	GpG.cri_insertion_add_mutex=TRUE;
      else if (strcmp (argv[i], "-extended_effects_evaluation") == 0)
	GpG.extended_effects_evaluation=TRUE; 
      else if (strcmp (argv[i], "-mutex_and_additive_effects") == 0)
	{
	  GpG.mutex_and_additive_effects= FALSE;
	}
      else if (strcmp (argv[i], "-not_supported_preconds_evaluation") == 0)
       GpG.supported_preconds_evaluation=FALSE;
      else if (strcmp (argv[i], "-not_extended_unsupported_facts") == 0)
	GpG.extended_unsupported_facts = FALSE;
      else if (strcmp (argv[i], "-extended_unsupported_goals") == 0)
	GpG.extended_unsupported_goals=TRUE;
      else if (strcmp (argv[i], "-no_insert_threated_act_in_neighb") == 0)
	GpG.insert_threated_act_in_neighb=FALSE;
      else if (strcmp (argv[i], "-reset_extended_unsupported_facts") == 0)
	sscanf (argv[++i], "%d", &GpG.reset_extended_unsupported_facts);
      else if (strcmp (argv[i], "-cri_intermediate_levels") == 0)
	sscanf (argv[++i], "%d", &GpG.cri_intermediate_levels);
      else if (strcmp (argv[i], "-relaxed_neighborhood_evaluation") == 0)
	GpG.relaxed_neighborhood_evaluation=TRUE;
      else if (strcmp (argv[i], "-max_num_flips") == 0)
	sscanf (argv[++i], "%d",  &GpG.ls_max_num_flips);
      else if (strcmp (argv[i], "-fast_best_action_evaluation") == 0)
	GpG.save_action_cost_list=TRUE;
      else if (strcmp (argv[i], "-avoid_best_action_cycles") == 0)
	sscanf (argv[++i], "%d", &GpG.avoid_best_action_cycles);
      else if (strcmp (argv[i], "-max_num_flips") == 0)
       sscanf (argv[++i], "%d",  &GpG.ls_max_num_flips);
      else if (strcmp (argv[i], "-stop_remove_act") == 0)
       GpG.stop_remove_act=1;
      else if (strcmp (argv[i], "-consider_relaxed_plan_for_inconsistences") == 0)
	GpG.consider_relaxed_plan_for_inconsistences=TRUE;
      else if (strcmp (argv[i], "-evaluate_threated_supported_preconds_of_neighb_action") == 0)
	sscanf (argv[++i], "%d", &GpG.evaluate_threated_supported_preconds_of_neighb_action);
      else if (strcmp (argv[i], "-no_mutex_with_additive_effects") == 0)
	GpG.no_mutex_with_additive_effects=TRUE;
      else if (strcmp (argv[i], "-evaluate_mutex_for_action_remotion") == 0)
	GpG.evaluate_mutex_for_action_remotion=TRUE;
      else if (strcmp (argv[i], "-weight_mutex_in_relaxed_plan") == 0)
	sscanf (argv[++i], "%f", &GpG.weight_mutex_in_relaxed_plan);
      else if (strcmp (argv[i], "-numeric_neighbors_in_down_levels") == 0)
	GpG.numeric_neighbors_in_down_levels=TRUE;
      else if (strcmp (argv[i], "-donot_try_suspected_actions") == 0)
	GpG.try_suspected_actions=FALSE;
      else if (strcmp (argv[i], "-ps") == 0)
	strncpy (gpath_sol_file_name, argv[++i], MAX_LENGTH);
      else if (strcmp (argv[i], "-choose_min_numA_fact") == 0)
	GpG.choose_random_fact_from_tuple = FALSE;
      else
	{
	  printf ("\n Unknown option: %s entered\n\n", argv[i]);
	  return FALSE;
	}
    }
  if (GpG.max_num_solutions < 1)
    {
      printf ("\n Please specify the parameter '-n'\n\n");
      return FALSE;
    }
  return TRUE;
}



/** OK 04/08/04
 * Name: is_term_condition_reache
 * Scopo:
 * Tipo: Bool
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: is_term_condition_reache
*  Objective:
*  Type: Bool
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
Bool is_term_condition_reached()
{
  /***
  struct tms cputime;
  float plan_time=0.0;
  

  if(GpG.max_cputime>0.0)
    {
      times (&cputime);    
      // tempo totale dall'inizio programma incluso preprocessing
      plan_time = DeltaTime (glob_start_time, cputime);
      if(plan_time > GpG.max_cputime)
      {
      printf("\n Max cpu time exceeded\n\n");
      exit(0);
      }
      }
  ***/
  switch(GpG.search_type)
    {
    case LOCAL:
      if(GpG.num_solutions == GpG.max_num_solutions)
	return TRUE;
      /**
      if(GpG.num_solutions>0)
	return TRUE;
      
      if(GpG.non_strips_domain)
	return TRUE;
      **/
      if (GpG.do_best_first)
	{
	  GpG.search_type= BEST_FIRST;
	  return FALSE;
	}
      break;
    case BEST_FIRST:
      break;
    default:
      break;
    }
  return TRUE;
}




/** OK 04/08/04
 * Name: remove_mutex_facts_in_bitvec
 * Scopo:
 * Tipo: void
 * Input: int fact
 *        int *bit_vect
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: remove_mutex_facts_in_bitvec
*  Objective:
*  Type: void
*  Input: int fact
*         int *bit_vect
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void remove_mutex_facts_in_bitvect (int fact, int *bit_vect)
{
  int i;
  for (i = 0; i < gnum_ft_block; i++)
    {
      bit_vect[i] &= ~gft_conn[fact].ft_exclusive_vect[i];
    }
}



/** OK 04/08/04
 * Name: remove_action_mutex_facts_in_bitvect
 * Scopo:
 * Tipo: void
 * Input: int action
 *        int *bit_vect
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: remove_action_mutex_facts_in_bitvect
*  Objective:
*  Type: void
*  Input: int action
*         int *bit_vect
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void remove_action_mutex_facts_in_bitvect (int action, int *bit_vect)
{
  int i;
  for (i = 0; i < gnum_ft_block; i++)
    {
      bit_vect[i] &= ~gef_conn[action].ft_exclusive_vect[i];
    }
}



/** OK 
 * Name: update_threated_facts_in_bitvect
 * Scopo:
 * Tipo: void
 * Input: int act_pos
 *        int *bit_vect
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: update_threated_facts_in_bitvect
*  Objective:
*  Type: void
*  Input: int act_pos
*         int *bit_vect
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void update_threated_facts_in_bitvect (int act_pos, int *bit_vect)
{
  int i;
  if(GpG.supported_preconds_evaluation==0)
    return;
  if (act_pos < 0)
    return;
  if (gef_conn[act_pos].sf != NULL)
    for (i = 0; i < gef_conn[act_pos].sf->num_A_start; i++)
      if (gef_conn[act_pos].sf->A_start[i]>=0)
	RESET_BIT(bit_vect,gef_conn[act_pos].sf->A_start[i]);
  for (i = 0; i < gnum_ft_block; i++)
    {
      bit_vect[i] |= gef_conn[act_pos].ft_exclusive_vect[i];
    }
  for (i = 0; i < gef_conn[act_pos].num_A; i++)
    if(gef_conn[act_pos].A[i]>=0)
      RESET_BIT(bit_vect, gef_conn[act_pos].A[i]);
}



/** OK 04/08/04
 * Name: print_act_eff_prec
 * Scopo:
 * Tipo: void
 * Input: int action
 *        int level
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: print_act_eff_prec
*  Objective:
*  Type: void
*  Input: int action
*         int level
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void print_act_eff_prec(int action, int level)
{
  int i,el;
  printf("\n\n$$$Lev %d -ACTION %d -- ",level, action);
  print_op_name(action);
  for (i = 0; i < gef_conn[action].num_PC; i++)
    {
      el = gef_conn[action].PC[i];
      printf("\n Prec %d - %s", el ,print_ft_name_string(el,temp_name));
      if (fact_is_supported (el, level))
	printf(" supported ");
      else
       if (GET_BIT (Hvar.bit_vect_facts, el) )
	 printf("  supported in relaxed plan ");
    }
 if (gef_conn[action].sf != NULL)
    {
      /**
	 Precondizioni OVERALL
	 **
	 OVERALL preconditions
      **/
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{
	  el = gef_conn[action].PC[i];
	  printf("\n Prec over all %d - %s", el ,print_ft_name_string(el,temp_name));
	  if (fact_is_supported (el, level))
	    printf(" supported ");
	  else
	    if (GET_BIT (Hvar.bit_vect_facts, el) )
	      printf("  supported in relaxed plan ");
	}
      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	{
	  el = gef_conn[action].sf->PC_end[i];
	  printf("\n Prec end %d - %s", el ,print_ft_name_string(el,temp_name));
	  if (fact_is_supported (el, level))
	    printf(" supported ");
	  else
	    if (GET_BIT (Hvar.bit_vect_facts, el) )
	      printf("  supported in relaxed plan ");
	}
      for (i = 0; i < gef_conn[action].sf->num_A_start; i++)
	{
	  el = gef_conn[action].sf->A_start[i];
	  printf("\n Effect at start %d - %s", el ,print_ft_name_string(el,temp_name));
	  if (fact_is_supported (el, level))
	    printf(" already supported ");
	  else
	    if (GET_BIT (Hvar.bit_vect_facts, el) )
	      printf("  already supported in relaxed plan ");
	}
    }
 for (i = 0; i < gef_conn[action].num_A; i++)
   {
     el = gef_conn[action].A[i];
     printf("\n Effect at end %d - %s", el ,print_ft_name_string(el,temp_name));
     if (fact_is_supported (el, level))
       printf(" already supported ");
     else
       if (GET_BIT (Hvar.bit_vect_facts, el) )
	 printf("  already supported in relaxed plan ");
   }
}


	
/** OK 04/08/04
 * Name: insert_extended_unsupported_facts_for_action
 * Scopo: Inserisco in extended_unsupported_facts le precondizioni di action non supportate
 * Tipo: void
 * Input: int action
 *        int level
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: insert_extended_unsupported_facts_for_action
*  Objective: Inserting in extended_unsupported_facts the preconditions of action not supported
*  Type: void
*  Input: int action
*         int level
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void insert_extended_unsupported_facts_for_action(int action, int level)
{
  int el, i;
  if(DEBUG5)
    printf("\n\n %d Extended unsupported facts evaluation ", GpG.count_num_try);
  if(level==GpG.curr_plan_length && action<0)
    {
      for (i = 0; i < GpG.curr_goal_state->num_F; i++)
	{
	  if(GpG.curr_goal_state->F[i]>0)
	    Hvar.extended_unsupported_facts[ Hvar.num_extended_unsupported_facts++ ]=GpG.curr_goal_state->F[i];
	}
      return;
    }
  for (i = 0; i < gef_conn[action].num_PC; i++)
    {
      el = gef_conn[action].PC[i];
      if (el < 0)
	continue;
      if(fact_is_supported(el,level)==FALSE)
	{
	  if(DEBUG5)
	    printf("\n %d -- Added %d -- %s ", Hvar.num_extended_unsupported_facts, el , print_ft_name_string(el, temp_name));
	  Hvar.extended_unsupported_facts[ Hvar.num_extended_unsupported_facts++ ]=el;
	}
    }
  if (gef_conn[action].sf != NULL)
    {
      /**
	 Precondizioni OVERALL
	 **
	 OVERALL preconditions
      **/
      for (i = 0; i < gef_conn[action].sf->num_PC_overall; i++)
	{
	  el = gef_conn[action].sf->PC_overall[i];
	  if (el < 0)
	    continue;		// LAZZA
	  if (is_fact_in_additive_effects_start
	      (action, gef_conn[action].sf->PC_overall[i]))
	    continue;
	  if(fact_is_supported(el,level)==FALSE)
	    {  
	      if(DEBUG5)
		printf("\n %d -- Added %d -- %s ", Hvar.num_extended_unsupported_facts, el , print_ft_name_string(el, temp_name));
	      Hvar.extended_unsupported_facts[ Hvar.num_extended_unsupported_facts++ ]=el;
	    }
	}
      for (i = 0; i < gef_conn[action].sf->num_PC_end; i++)
	{
	  el = gef_conn[action].sf->PC_end[i];
	  if (el < 0)
	    continue;		// LAZZA
	  if (is_fact_in_additive_effects_start (action, gef_conn[action].sf->PC_end[i]))
	    continue;
	  if(fact_is_supported(el,level)==FALSE)
	    {
	      if(DEBUG5)
		printf("\n %d -- Added %d -- %s ", Hvar.num_extended_unsupported_facts, el , print_ft_name_string(el, temp_name));
	      Hvar.extended_unsupported_facts[ Hvar.num_extended_unsupported_facts++ ]=el;
	    }
	}
    }
}



/** OK 04/08/04
 * Name: reorder_fact_vect
 * Scopo:
 * Tipo: void
 * Input: int *facts
 *        int numf
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: reorder_fact_vect
*  Objective:
*  Type: void
*  Input: int *facts
*         int numf
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void reorder_fact_vect(int *facts, int numf) {
  int i, j, min, tmp;
  for (i = 0; i < (numf - 1); i++) {
    min = i;
    for (j = i + 1; j < numf; j++) {
      if (facts[j] < 0)
        continue;
      if (facts[min] < 0) {
	min = j;
	continue;
      }
      if (gft_conn[facts[j]].num_A < gft_conn[facts[min]].num_A)
        min = j;
    }
    if (i != min) {
      tmp = facts[i];
      facts[i] = facts[min];
      facts[min] = tmp;
    }
  }
}



/** OK 04/08/04
 * Name: reorder_action_preconditions
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: reorder_action_preconditions
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void reorder_action_preconditions( void ) {
  int i;
  for (i = 0; i < gnum_ef_conn; i++) {
    reorder_fact_vect(gef_conn[i].PC, gef_conn[i].num_PC);
    if (gef_conn[i].sf) {
      reorder_fact_vect(gef_conn[i].sf->PC_overall, gef_conn[i].sf->num_PC_overall);
      reorder_fact_vect(gef_conn[i].sf->PC_end, gef_conn[i].sf->num_PC_end);
    }
  }
}



/** OK 04/08/04
 * Name: compare_neighbors_cost
 * Scopo:
 * Tipo: int
 * Input: neighb **A
 *        neighb **B
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: compare_neighbors_cost
*  Objective:
*  Type: int
*  Input: neighb **A
*         neighb **B
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int compare_neighbors_cost(neighb **A, neighb **B) 
{
  if ((*A)->cost.weight < (*B)->cost.weight)
    return -1;
  else if (fabsf((*A)->cost.weight - (*B)->cost.weight) < MAX_APPROX)
    return 0;
  else
    return 1;
  return 0;
}



/** OK 04/08/04
 * Name: compare_neighbors_level
 * Scopo:
 * Tipo: int
 * Input: neighb **A
 *        neighb **B
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: compare_neighbors_level
*  Objective:
*  Type: int
*  Input: neighb **A
*         neighb **B
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
int compare_neighbors_level(neighb **A, neighb **B) 
{
  if ((*A)->constraint_type == C_T_REMOVE_ACTION
      && (*B)->constraint_type == C_T_INSERT_ACTION)
    return -1;
  else if ((*B)->constraint_type == C_T_REMOVE_ACTION
	   && (*A)->constraint_type == C_T_INSERT_ACTION)
    return 1;
  if ((*A)->act_level < (*B)->act_level)
    return 1;
  else if ((*A)->act_level > (*B)->act_level)
    return -1;
  return 0;
}



/** OK 04/08/04
 * Name: sort_neighbors_for_level
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: sort_neighbors_for_level
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void sort_neighbors_for_level( void ) 
{
  return;
  if (DEBUG5) {
    int i;
    if (DEBUG5)
      printf("\n\nSorting neighbors ...");
    for (i = 0; i < num_neighborhood; i++) {
      if (DEBUG5)
	printf("\n<%d> NEIGHB : %s [%s level %d]", i, print_op_name_string(neighb_vect[i]->act_pos, temp_name),
	       (neighb_vect[i]->constraint_type == C_T_INSERT_ACTION)?"INSERTION":"REMOTION",
	       neighb_vect[i]->act_level);
      if (i>0)
	if (neighb_vect[i]->act_level > neighb_vect[i-1]->act_level)
	  GpG.info_search = 5;
    }
  }
  qsort(neighb_vect, num_neighborhood, sizeof(neighb_list), (void *)compare_neighbors_level);
  if (DEBUG5) {
    int i;
    printf("\n\nSORTED NEIGHBORS:");
    for (i = 0; i < num_neighborhood; i++) {
      printf("\n<%d> NEIGHB : %s [%s level %d]", i, print_op_name_string(neighb_vect[i]->act_pos, temp_name),
	     (neighb_vect[i]->constraint_type == C_T_INSERT_ACTION)?"INSERTION":"REMOTION", 
	     neighb_vect[i]->act_level);
    }
  }
}



/** OK 04/08/04
 * Name: sort_neighbors_for_cost
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: sort_neighbors_for_cost
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void sort_neighbors_for_cost( void )
{
  qsort(neighb_vect, num_neighborhood, sizeof(neighb_list), (void *)compare_neighbors_cost);
}
	

 #ifndef __SUN__

#ifndef __WINLPG__
/*****************************
    LINUX SIGNAL MANAGEMENT
 *****************************/


/** OK 04/08/04
 * Name: seg_fault
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: seg_fault
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void seg_fault()
{
  printf("\nLPG: Segmentation Fault - Seed %d\n", seed);
  exit(1);
}





/** OK 04/08/04
 * Name: so_signal_management
 * Scopo:
 * Tipo: void
 * Input: nessuno
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: so_signal_management
*  Objective:
*  Type: void
*  Input: none
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void so_signal_management()
{
  static struct sigaction saio;           /* definition of signal action */
  saio.sa_handler = seg_fault;
  saio.sa_flags = 0;
  saio.sa_restorer = NULL;
  sigaction(SIGSEGV,&saio,NULL);
}
#endif

#endif


#ifdef __SUN__

float fabsf(float f)
{
  if(f>=0)
    return f;
  else
    return (-f);
}


#endif

#ifdef __WINLPG__

/** OK 04/08/04
 * Name: wintime
 * Scopo:
 * Tipo: void
 * Input: clock_t *t
 * Output:
 * Strutture dati principali:
 * Funzioni principali utilizzate:
 * Chiamata da:
**
*  Name: wintime
*  Objective:
*  Type: void
*  Input: clock_t *t
*  Output:
*  Main Data Structures:
*  Main Functions Used:
*  Call gives:
**/
void wintime(clock_t *t)
{
  (*t) = clock();
}
#endif
