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
 * File: inst_utils.c
 * Description: various functions for isupporting instantiation
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/





#include <math.h>
#include <values.h>
#include "lpg.h"
#include "parse.h"
#include "memory.h"
#include "inst_pre.h"
#include "numeric.h"
#include "inst_utils.h"
#include "output.h"
#include "LpgOutput.h"
#include "utilities.h"
#include "check.h"
#include "numeric.h"
#include "H_relaxed.h"
#include "LocalSearch.h"


int *tmp_dur_rvals = NULL;


void print_compvar_lists(void) { 

  int i;
  IntList *tmp;
  CompositeNumVar *c;

  for (i = 0; i < gnum_comp_var; i++) {

    c = &gcomp_var[i];

    printf("\n\nComposite Numeric Var %d", i);

    printf("\n-----X affects X-----");
    for (tmp = c->affects; tmp; tmp = tmp->next)
      printf("\n  af: %d", tmp->item);
    printf("\n-----X increased by X-----");
    for (tmp = c->increased_by; tmp; tmp = tmp->next)
      printf("\n  inc: %d", tmp->item);
    printf("\n-----X decreased by X-----");
    for (tmp = c->decreased_by; tmp; tmp = tmp->next)
      printf("\n  dec: %d", tmp->item);
    printf("\n-----X changed by X-----");
    for (tmp = c->changed_by; tmp; tmp = tmp->next)
      printf("\n  ch: %d", tmp->item);
        
  }

}
/**
 * Inizializza le dimensioni di una bit table
 **/
int init_bit_table_const(unsigned long int max_size, int *n_bit, int *base, int *bit_row_size) {

  int bit_pos;
  int block_mask;

  /* 
   * Evaluate hash's rows size
   *
   * bit_pos = posizione del bit più significativo di max_size
   * In pratica la tabella ha un numero di righe avente ordine di
   * grandezza pari alla metà dell'ordine di grandezza di max_size
   */
  bit_pos = (int) (log((double)max_size)/M_LN2);
  (*n_bit) = MAX(5, (bit_pos >> 1));
  
  (*bit_row_size) = 0; 
  SET_BIT(bit_row_size, (*n_bit));
  
  /* esprimo BIT_HASH_ROW_SIZE come # di interi da allocare
   */
  (*bit_row_size)--;
  (*bit_row_size) =  ((*bit_row_size) >> 5) + 1;

  block_mask = (int) (log((double)(*bit_row_size))/M_LN2);
  
  (*base) = ((*bit_row_size) << 5) - 1;

  return block_mask;
  
}


/**
 * Inizializza una tabella di bit in table, nella posizione corrispondente alla riga op
 **/
int init_bit_table_row(bit_table table, int op, unsigned long int size) {

  int col_size;
  
  col_size = BIT_COL_SIZE(table, size);

  table.bits[op] = (int_pointer *)calloc(col_size, sizeof(int_pointer));
  
  return col_size;
} 


/**
 * Setta il bit corrispondente al fatto <op, adr> in una tabella di bit
 **/
void insert_bit_in_bit_table(bit_table table, int op, unsigned long int adr) {

  int row;

  if (!table.bits[op]) 
     init_bit_table_row(table, op, table.max_row_size);
  
  row = adr >> table.n_bit;

  if (!table.bits[op][row]) 
    table.bits[op][row] = (int_pointer)calloc(table.bit_row_size, sizeof(int));
  
  SET_BIT(table.bits[op][row], (adr & table.base));

}

/**
 * Resetta il bit corrispondente al fatto <op, adr> in una tabella di bit
 **/
void delete_bit_from_bit_table(bit_table table, int op, unsigned long int adr) {

  int row;

  if (!table.bits[op])
    return;

  row = adr >> table.n_bit;
  
  if (!table.bits[op][row])
    return;

  RESET_BIT(table.bits[op][row], (adr & table.base));

}


/**
 * Controlla il bit corrispondente al fatto <predicate, adr> in una tabella di bit
 **/
Bool check_bit_in_bit_table(bit_table table, int op, unsigned long int adr) {
  
  int row;

  if (!table.bits[op])
    return FALSE;

  row = adr >> table.n_bit;

  if (!table.bits[op][row]) 
    return FALSE;

  return GET_BIT(table.bits[op][row], (adr & table.base));

}


int get_bit_table_block(bit_table table, int op, int pos) {

  int r, c;

  if (!table.bits[op])
    return 0;

  r = pos >> table.div_mask;

  if (!table.bits[op][r]) 
    return 0;

  c = pos & table.mod_mask;

  return (table.bits[op][r][c]);

}



/**
 * Aggiunge ad un operatore delle precondizioni (implicite) di disugualianza tra i propri
 * parametri in modo da nn avere effetti contraddittori
 **/
void add_implicit_preconds(Operator *op) {

  int i;
  Effect *ef1, *ef2;
  Literal *f1, *f2;
  WffNode *prec, *tmp;

  if (GpG.inst_duplicate_param)
    return;
		
  /* For all operator's effects
   */
  for (ef1 = op->effects; ef1; ef1 = ef1->next) {
    
    for (f1 = ef1->effects; f1; f1 = f1->next)
      for (ef2 = ef1; ef2; ef2 = ef2->next)

	/* For all subsequent effects
	 */   
	for (f2 = (ef1==ef2)? f1->next : ef2->effects; f2; f2 = f2->next) {
	  
	  if ((f1->fact.predicate == f2->fact.predicate)
	      && (f1->negated != f2->negated)) {
	    
	    /* skip if one is AT_START and the other is AT_END
	     */
	    
	    //if (f1->is_start_end_ovr != f2->is_start_end_ovr)
	     // continue;
	    
	    /* Add NOT EQ node in op preconditions
	     */


	    for (i = 0; i < garity[f1->fact.predicate]; i++)
	      if (f1->fact.args[i] < 0) {
		
		/* Equals args cannot be different
		 */
		if (f1->fact.args[i] == f2->fact.args[i])
		  continue;

#ifdef __MY_OUTPUT__
		if (DEBUG5) {
		  printf("\n\nOPERATOR %s", op->name);
		  printf("\nEffetti contraddittori :  ");
		  print_Fact(&f1->fact);
		  printf(" --- ");
		  print_Fact(&f2->fact);
		}
#endif

		/* Build not-eq node
		 */		
		prec = new_WffNode(NOT);
		prec->son = new_WffNode(ATOM);
		prec->son->fact = new_Fact();

		if (GpG.try_suspected_actions)
		  prec->son->fact->added_implicit = TRUE;

		prec->son->fact->predicate = -1;
		prec->son->fact->args[0] = f1->fact.args[i];
		prec->son->fact->args[1] = f2->fact.args[i];

		if (DEBUG5) {
		  printf("\nImpongo una disuglualianza tra i parametri : %d e %d", DECODE_VAR(f1->fact.args[i]), DECODE_VAR(f2->fact.args[i]));
		}
		
		/* Append it to operator's preconditions
		 */
		if (op->preconds->connective == AND || op->preconds->connective == OR) {
		  prec->next = op->preconds->sons;
		  op->preconds->sons = prec;
		}
		else {
		  prec->next = op->preconds;
		  tmp = new_WffNode(AND);
		  tmp->sons = prec;
		  op->preconds = tmp;
		}
		
	      }
	    
	  }
	}
  }
  
}




/********************************
 * POSSIBLY TRUE FACTS ANALYSIS *
 ********************************/


/*cerca la stringa passata come parametro tra i nomi degli operatori pddl2: torna il puntatore all'operatore pddl2*/
PlOperator *search_name_in_plops (char *plop_name)
{
  PlOperator *op;

  for (op = gloaded_pl2ops; op; op = op->next)
    if (strcmp (op->name, plop_name) == SAME)
      return op;

  for (op = gderived_pl2predicates; op; op = op->next)
    if (strcmp (op->name, plop_name) == SAME)
      return op;

  return NULL;
}

/*salva il puntatore al ploperator nell'efconn*/
void associate_PlOperator_with_EfConn (void)
{
  int i;

  for (i = 0; i < gnum_ef_conn; i++)
    {
      gef_conn[i].plop =
	search_name_in_plops (gop_conn[gef_conn[i].op].action->name);
      if (!gef_conn[i].plop)
	exit (1);
      gef_conn[i].act_type = gef_conn[i].plop -> ops_type;
      gef_conn[i].start_ef = gef_conn[i].end_ef = -1;
      

      if (gef_conn[i].act_type == TIMED_FACT_ACT)
	gef_conn[i].duration = gef_conn[i].plop -> duration -> value;

      /*a./glloca il posto per i fatti speciali solo se serve */
      if (!gef_conn[i].plop -> is_odd)
	gef_conn[i].sf = NULL;
      else
	if (!gef_conn[i].sf)
	  gef_conn[i].sf = new_SpecialFacts ();
    }
}


/**
 * Individua le precondizioni timed di ogni azione e le sposta in timed_PC
 **/
void extract_timed_preconditions( void ) {

  int i, j, num;
  Bool theres_timed_precs = FALSE;
  IntList *tmp = NULL, *aux = NULL;
  
  for (i = 0; i < gnum_ef_conn; i++) {

    // Precondizioni at_start
    num = 0;
    for (j = 0; j < gef_conn[i].num_PC; j++) {
   
      if (gef_conn[i].PC[j] < 0)
	continue;
      
      if (gft_conn[gef_conn[i].PC[j]].fact_type == IS_TIMED) {

	theres_timed_precs = TRUE;

	num++;
	tmp = new_IntList();
	tmp -> item = gef_conn[i].PC[j];
	tmp -> next = aux;
	aux = tmp;

	gef_conn[i].PC[j] = gef_conn[i].PC[gef_conn[i].num_PC - 1];
	gef_conn[i].num_PC--;
	j--;
      }
    }

    if (num) {
      if (!gef_conn[i].timed_PC)  
	gef_conn[i].timed_PC = (TimedPrecs *)calloc(1, sizeof(TimedPrecs));

      gef_conn[i].timed_PC -> num_PC_start = 0;
      gef_conn[i].timed_PC -> PC_start = (int *)calloc(num, sizeof(int));
      for (tmp = aux; tmp; tmp = tmp -> next)
	gef_conn[i].timed_PC -> PC_start[gef_conn[i].timed_PC -> num_PC_start++] = tmp -> item;
    
      /* Aggiunta dei timed fact alle azioni spezzate */ 
      if (gef_conn[i].act_type == SPLITTED_ACTION) {
	SET_BIT(GpG.has_timed_preconds, gef_conn[i].start_ef);
	if (!gef_conn[gef_conn[i].start_ef].timed_PC) { 
	  gef_conn[gef_conn[i].start_ef].timed_PC = (TimedPrecs *)calloc(1, sizeof(TimedPrecs));
	}
	gef_conn[gef_conn[i].start_ef].timed_PC->num_PC_start =  gef_conn[i].timed_PC->num_PC_start;
	gef_conn[gef_conn[i].start_ef].timed_PC->PC_start = gef_conn[i].timed_PC->PC_start;
      }

    }

    free_intlist(aux);
    aux = NULL;

    if (gef_conn[i].sf) {
      // Precondizioni overall
      num = 0;
      for (j = 0; j < gef_conn[i].sf -> num_PC_overall; j++) {

	if (gef_conn[i].sf -> PC_overall[j] < 0)
	  continue;

	if (gft_conn[gef_conn[i].sf -> PC_overall[j]].fact_type == IS_TIMED) {
	  
	  theres_timed_precs = TRUE;

	  num++;
	  tmp = new_IntList();
	  tmp -> item = gef_conn[i].sf -> PC_overall[j];
	  tmp -> next = aux;
	  aux = tmp;
	  
	  gef_conn[i].sf -> PC_overall[j] = gef_conn[i].sf -> PC_overall[gef_conn[i].sf -> num_PC_overall - 1];
	  gef_conn[i].sf -> num_PC_overall--;
	  j--;
	}
      }

      if (num) {
	if (!gef_conn[i].timed_PC) 
	  gef_conn[i].timed_PC = (TimedPrecs *)calloc(1, sizeof(TimedPrecs));

	gef_conn[i].timed_PC -> num_PC_overall = 0;
	gef_conn[i].timed_PC -> PC_overall = (int *)calloc(num, sizeof(int));
	for (tmp = aux; tmp; tmp = tmp -> next)
	  gef_conn[i].timed_PC -> PC_overall[gef_conn[i].timed_PC -> num_PC_overall++] = tmp -> item;
      
	/* Aggiunta dei timed fact alle azioni spezzate */ 
	if (gef_conn[i].act_type == SPLITTED_ACTION) {
	  SET_BIT(GpG.has_timed_preconds, gef_conn[i].end_ef);
	  if (!gef_conn[gef_conn[i].end_ef].timed_PC) { 
	    gef_conn[gef_conn[i].end_ef].timed_PC = (TimedPrecs *)calloc(1, sizeof(TimedPrecs));
	  }
	  gef_conn[gef_conn[i].end_ef].timed_PC->num_PC_overall =  gef_conn[i].timed_PC->num_PC_overall;
	  gef_conn[gef_conn[i].end_ef].timed_PC->PC_overall = gef_conn[i].timed_PC->PC_overall;
	}

      }
     
      free_intlist(aux);
      aux = NULL;
      
      // Precondizioni at end
      num = 0;
      for (j = 0; j < gef_conn[i].sf -> num_PC_end; j++) {
	
	if (gef_conn[i].sf -> PC_end[j] < 0)
	  continue;
	
	if (gft_conn[gef_conn[i].sf -> PC_end[j]].fact_type == IS_TIMED) {
	  
	  theres_timed_precs = TRUE;

	  num++;
	  tmp = new_IntList();
	  tmp -> item = gef_conn[i].sf -> PC_end[j];
	  tmp -> next = aux;
	  aux = tmp;
	  
	  gef_conn[i].sf -> PC_end[j] = gef_conn[i].sf -> PC_end[gef_conn[i].sf -> num_PC_end - 1];
	  gef_conn[i].sf -> num_PC_end--;
	  j--;
	}
      }
      
     
      if (num) {
	if (!gef_conn[i].timed_PC) 
	  gef_conn[i].timed_PC = (TimedPrecs *)calloc(1, sizeof(TimedPrecs));
	
	gef_conn[i].timed_PC -> num_PC_end = 0;
	gef_conn[i].timed_PC -> PC_end = (int *)calloc(num, sizeof(int));
	for (tmp = aux; tmp; tmp = tmp -> next)
	  gef_conn[i].timed_PC -> PC_end[gef_conn[i].timed_PC -> num_PC_end++] = tmp -> item;

	/* Aggiunta dei timed fact alle azioni spezzate */ 
	if (gef_conn[i].act_type == SPLITTED_ACTION) {
	  SET_BIT(GpG.has_timed_preconds, gef_conn[i].end_ef);
	  if (!gef_conn[gef_conn[i].end_ef].timed_PC) { 
	    gef_conn[gef_conn[i].end_ef].timed_PC = (TimedPrecs *)calloc(1, sizeof(TimedPrecs));
	  }
	  gef_conn[gef_conn[i].end_ef].timed_PC->num_PC_end =  gef_conn[i].timed_PC->num_PC_end;
	  gef_conn[gef_conn[i].end_ef].timed_PC->PC_end = gef_conn[i].timed_PC->PC_end;
	}
      }
     
      free_intlist(aux);
      aux = NULL;
    }

  }

  GpG.timed_preconditions = theres_timed_precs;

  /**
     #ifdef __MY_OUTPUT__
     printf("\n\nTimed preconditions in actions : %s", (GpG.timed_preconditions)?"YES":"NO");
     #endif
  **/


  /*
   * Test actions timed precondition 
   */
#ifdef __TEST__

  printf("\n\nTesting actions timed preconditions...");

  for (i = 0; i < gnum_ef_conn; i++) {
    
    if (GET_BIT(GpG.has_timed_preconds, i) && !gef_conn[i].timed_PC) {
      printf("\nError : actions %s should have timed preconditions.", print_op_name_string(i, temp_name));
      continue;
    }

    if (!GET_BIT(GpG.has_timed_preconds, i) && gef_conn[i].timed_PC) {
      printf("\nError : actions %s shouldn't have timed preconditions.", print_op_name_string(i, temp_name));
      continue;
    }

    for (j = 0; j < gef_conn[i].num_PC; j++)
      if (gft_conn[gef_conn[i].PC[j]].fact_type == IS_TIMED)
	printf("\nError : timed fact %s in PC array.", print_ft_name_string(gef_conn[i].PC[j], temp_name));
    if (gef_conn[i].sf) {
      for (j = 0; j < gef_conn[i].sf->num_PC_overall; j++)
	if (gft_conn[gef_conn[i].sf->PC_overall[j]].fact_type == IS_TIMED)
	  printf("\nError : timed fact %s in PC_overall array.", print_ft_name_string(gef_conn[i].sf->PC_overall[j], temp_name));
      for (j = 0; j < gef_conn[i].sf->num_PC_end; j++)
	if (gft_conn[gef_conn[i].sf->PC_end[j]].fact_type == IS_TIMED)
	  printf("\nError : timed fact %s in PC_end array.", print_ft_name_string(gef_conn[i].sf->PC_end[j], temp_name));
    }
    if (gef_conn[i].timed_PC) {
      for (j = 0; j < gef_conn[i].timed_PC->num_PC_start; j++)
	if (gft_conn[gef_conn[i].timed_PC->PC_start[j]].fact_type != IS_TIMED)
	  printf("\nError : not timed fact %s in timed_PC->PC_start array.", print_ft_name_string(gef_conn[i].timed_PC->PC_start[j], temp_name));
      for (j = 0; j < gef_conn[i].timed_PC->num_PC_overall; j++)
	if (gft_conn[gef_conn[i].timed_PC->PC_overall[j]].fact_type != IS_TIMED)
	  printf("\nError : not timed fact %s in timed_PC->PC_overall array.", print_ft_name_string(gef_conn[i].timed_PC->PC_overall[j], temp_name));
      for (j = 0; j < gef_conn[i].timed_PC->num_PC_end; j++)
	if (gft_conn[gef_conn[i].timed_PC->PC_end[j]].fact_type != IS_TIMED)
	  printf("\nError : not timed fact %s in timed_PC->PC_end array.", print_ft_name_string(gef_conn[i].timed_PC->PC_end[j], temp_name));
    }

    
  }

#endif

  
}




/**
 * Invalida le azioni inutili
 */
void check_actions_utility( void ) {

  int i, act, next;
  EfConn *action;

  for (act = 0; act < gnum_ef_conn; act++) {
    
    next = 0;
    action = &gef_conn[act];
    
    // Effetti at end
    for (i = 0; i < action->num_A; i++) {
      // Fatti booleani
      if (action->A[i] >= 0) { 
	if (!is_fact_in_preconditions(action->position, action->A[i])
	    && !is_fact_in_preconditions_end(action->position, action->A[i])
	    && !is_fact_in_preconditions_overall(action->position, action->A[i])) {
	  next = 1;
	  break;
	}
      }
      // Numerici
      else {
	
	// Check numerico ??
      
	next = 1;
	break;
      }

      if (next)
	continue;

    }
    
    // Effetti at start
    if (action->sf)
      for (i = 0; i < action->sf->num_A_start; i++) {
	if (action->sf->A_start[i] >= 0) {
	  if (!is_fact_in_preconditions(action->position, action->sf->A_start[i])
	      && (!is_fact_in_preconditions_overall(action->position, action->sf->A_start[i]))) {
	    next = 1;
	    break;
	  }
	  
	}
	else {
	  
	  // Check numerico ??
	  next = 1;
	  break;
	}
      }

    if (next) 
      continue;

    if (DEBUG5)
      printf("\nAzione inutile : %s", print_op_name_string(action -> position, temp_name));
    
    action -> position = -1;
  }

}





/* crea il vettore delle relazioni numeriche */
void add_composite_vars (int from_ef_conn, int to_ef_conn)
{
  int i = 0;

  // per pulizia azzero i value delle cvar di assegnamento
  for (i = 0; i < gnum_comp_var; i++)
    {
      switch (gcomp_var[i].operator)
	{
	case INCREASE_OP:
	case DECREASE_OP:
	case SCALE_UP_OP:
	case SCALE_DOWN_OP:
	case ASSIGN_OP:
	  MSG_ERROR("ERRORE PARTE NUMERICA \n");
	  exit(0);
	  break;

	default:

	  break;
	}
    }

  

  // salva le espressioni numeriche nel vettore delle espressioni numeriche
  index_duration_exps (from_ef_conn, to_ef_conn);

  /* aggiunge l'espressione legata alla metrica di valutazione del piano */
  /* l'indice tornato deve essere salvato in una var globale!!! */
  goptimization_exp = index_in_cvars_of_expression (gmetric_exp, -1);
  if(goptimization_exp < 0 )
    GpG.is_metric_present = FALSE;
  else
    {
      GpG.is_metric_present = TRUE;

      if (gmetric_exp->sons->sons->connective == TOTAL_TIME_CONN &&
	  gmetric_exp->sons->sons->next == NULL)
	GpG.is_metric_onlytemporal = TRUE;
      else
	GpG.is_metric_onlytemporal = FALSE;
    }


  /* Impostazione parametro per massimizzazione di risorsa numerica */
  if (gmetric_exp && gmetric_exp->sons && gmetric_exp->sons->connective==MAXIMIZE_CONN)
    GpG.maximize_plan=TRUE;
  
  /* adds effects to comp vars */
  add_effects_to_comp_vars (from_ef_conn, to_ef_conn);

  /* adds preconds to comp vars */
  add_preconds_to_comp_vars (from_ef_conn, to_ef_conn);

  /* adds conditional effect to comp vars */
  add_cond_effects_to_comp_vars();

  /* calculate the duration of each action */
  calc_duration_of_actions (from_ef_conn, to_ef_conn);

  /* calcola il costo statico delle azioni */
  calc_cost_of_actions (from_ef_conn, to_ef_conn);
  
  /*calcola il costo degli effetti condizionali delle azioni */
  calc_cost_of_cond_actions();

  gnum_block_compvar = gnum_comp_var / 32 + 1;

  if ((gnum_comp_var > 3) || (gnum_comp_var_effects > 0))
    {
      if(gnum_comp_var_effects > 0)
	GpG.is_domain_numeric = TRUE;
      else
	GpG.is_domain_numeric = 2;

      
      if (!GpG.numeric_actions)
	GpG.numeric_actions = alloc_vect(gnum_ef_block);
    }

  if ( gcmd_line.display_info == 122 ) {
    print_efconn();
    print_numeric_effect();
    print_cond_efconn();
    print_numeric_cond_effect();
  }
#ifdef _TEST_COND
  test_cond_effect();
#endif

#ifdef _TEST_HASH
  printf ("\n\nch.totali %d check completi %d\n\n", tot, compl);
#endif
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Spostamento dei special fact di tipo
			  numerico utilizzati negli effeti condizionali
	PARAMETER	: cef	effetto in cui aggiungere gli effetti numerici
			  e	descrizione effetto o condizione when
	RETURN		:
-----------------------------------------------------------------
*/
void add_numeric_cond_effects_to_comp_vars(CondEfConn *cef, PlNode *e)
{
	PlNode		*n;

	if (e->connective == AND)
		e = e->sons;

	for (; e; e = e->next) {
		if ((e->connective == AT_START_CONN) || (e->connective == AT_END_CONN) || (e->connective == OVER_ALL_CONN))
			n = e->sons;
		else
			n = e;

		switch (n->connective) {
// vefifica condizioni numeriche
		case BIN_COMP:
			switch (e->connective) {
			case OVER_ALL_CONN:
				if (cef->sf == NULL)
					cef->sf = new_SpecialFacts();
				cef->sf->PC_overall = realloc(cef->sf->PC_overall, cef->sf->num_PC_overall + 1);
				cef->sf->PC_overall[cef->sf->num_PC_overall++] = -index_in_cvars_of_expression(n->sons, cef->ef);
		  		break;
			case AT_END_CONN:
				if (cef->sf == NULL)
					cef->sf = new_SpecialFacts();
				cef->sf->PC_end = realloc(cef->sf->PC_end, cef->sf->num_PC_end + 1);
				cef->sf->PC_end[cef->sf->num_PC_end++] =  -index_in_cvars_of_expression(n->sons, cef->ef);
				break;
			default:
				cef->PC = realloc(cef->PC, cef->num_PC + 1);
				cef->PC[cef->num_PC++] = -index_in_cvars_of_expression(n->sons, cef->ef);
				break;
			}
			break;

// vefifica effetti numerici
		case INCREASE_CONN:
		case DECREASE_CONN:
		case SCALE_UP_CONN:
		case SCALE_DOWN_CONN:
		case ASSIGN_CONN:
			if (e->connective == AT_START_CONN) {
				if (cef->sf == NULL)
					cef->sf = new_SpecialFacts();
				cef->sf->A_start = realloc(cef->sf->A_start, cef->sf->num_A_start + 1);
				cef->sf->A_start[cef->sf->num_A_start++] = -index_in_cvars_of_expression (n, cef->ef);
			} else {
				cef->A[cef->num_A++] = -index_in_cvars_of_expression (n, cef->ef);
			}
			break;

		default:
			break;
		}
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Verifica se il fatto è booleano
	PARAMETER	: pln	nodo fatto
	RETURN		: TRUE	fatto booleano
			  FALSE	no booleano
-----------------------------------------------------------------
*/
int is_bool_fact(PlNode *pln)
{
	if (pln == NULL)
		return(FALSE);

	if (pln->connective == NOT)
		return(TRUE);
	if (pln->connective == ATOM)
		return(TRUE);

	return(FALSE);
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Spostamento dei special fact di tipo
			  numerico utilizzati negli effeti condizionali
	PARAMETER	: cef	effetto in cui aggiungere gli effetti numerici
			  e	descrizione effetto when
	RETURN		:
-----------------------------------------------------------------
*/
void add_cond_effects_to_comp_vars_precond(CondEfConn *cef, PlNode *e)
{
	int	only_one;
	int	pos;

	if (e->connective == AND) {
		e = e->sons;
		only_one = FALSE;
	} else {
		only_one = TRUE;
	}

	for (; e; e = e->next) {
		if (!is_bool_fact(e) && is_bool_fact(e->sons)) {
			pos = get_fct_pos_from_plnode(e->sons, cef->plop, cef->op, cef->PC, cef->num_PC);
			if (pos != -1) {

				// precondizione at_end condizionale
				if (e->connective == AT_END_CONN) {
					if (cef->sf == NULL)
						cef->sf = new_SpecialFacts();
					cef->sf->PC_end = realloc(cef->sf->PC_end, cef->sf->num_PC_end + 1);
					cef->sf->PC_end[(cef->sf->num_PC_end)++] = cef->PC[pos];
					cef->PC[pos] = cef->PC[--(cef->num_PC)];
				}

				// precondizione over_all condizionale
				if (e->connective == OVER_ALL_CONN) {
					if (cef->sf == NULL)
						cef->sf = new_SpecialFacts();
					cef->sf->PC_overall = realloc(cef->sf->PC_overall, cef->sf->num_PC_overall + 1);
					cef->sf->PC_overall[(cef->sf->num_PC_overall)++] = cef->PC[pos];
					cef->PC[pos] = cef->PC[--(cef->num_PC)];
				}
			}
		}
		if (cef->num_PC == 0)
			cef->PC = NULL;
		if (only_one == TRUE)
			break;		// fine ciclo
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Spostamento dei special fact di tipo
			  numerico utilizzati negli effeti condizionali
	PARAMETER	: cef	effetto in cui aggiungere gli effetti numerici
			  e	descrizione effetto when
	RETURN		:
-----------------------------------------------------------------
*/
void add_cond_effects_to_comp_vars_effect(CondEfConn *cef, PlNode *e)
{
	PlNode	*tmpnode;
	int	pos;

	if (e->connective == AND)
		e = e->sons;

	for (; e; e = e->next) {
		if ((e->connective == AT_START_CONN) && (is_bool_fact(e->sons))) {
			if (e->sons->connective == ATOM) {
				tmpnode = new_PlNode(NOT);
				tmpnode->sons = e->sons;
			} else {
				tmpnode = e->sons;
			}
			// effetto at_start cancellante condizionale
			pos = get_fct_pos_from_plnode(tmpnode, cef->plop, cef->op, cef->D, cef->num_D);
			if (pos != -1) {
				if (cef->sf == NULL)
					cef->sf = new_SpecialFacts();
				cef->sf->D_start = realloc(cef->sf->D_start, cef->sf->num_D_start + 1);
				cef->sf->D_start[(cef->sf->num_D_start)++] = cef->D[pos];
				cef->D[pos] = cef->D[--(cef->num_D)];
			}
			// effetto at_start additivo condizionale
			pos = get_fct_pos_from_plnode(tmpnode, cef->plop, cef->op, cef->A, cef->num_A);
			if (pos != -1) {
				if (cef->sf == NULL)
					cef->sf = new_SpecialFacts();
				cef->sf->A_start = realloc(cef->sf->A_start, cef->sf->num_A_start + 1);
				cef->sf->A_start[(cef->sf->num_A_start)++] = cef->A[pos];
				cef->A[pos] = cef->A[--(cef->num_A)];
			}

			// effetto at_start cancellante condizionale
			pos = get_fct_pos_from_plnode(tmpnode->sons, cef->plop, cef->op, cef->D, cef->num_D);
			if (pos != -1) {
				if (cef->sf == NULL)
					cef->sf = new_SpecialFacts();
				cef->sf->D_start = realloc(cef->sf->D_start, cef->sf->num_D_start + 1);
				cef->sf->D_start[(cef->sf->num_D_start)++] = cef->D[pos];
				cef->D[pos] = cef->D[--(cef->num_D)];
			}
			// effetto at_start additivo condizionale
			pos = get_fct_pos_from_plnode(tmpnode->sons, cef->plop, cef->op, cef->A, cef->num_A);
			if (pos != -1) {
				if (cef->sf == NULL)
					cef->sf = new_SpecialFacts();
				cef->sf->A_start = realloc(cef->sf->A_start, cef->sf->num_A_start + 1);
				cef->sf->A_start[(cef->sf->num_A_start)++] = cef->A[pos];
				cef->A[pos] = cef->A[--(cef->num_A)];
			}
			if (e->sons->connective == ATOM) {
				tmpnode->sons = NULL;
				free_PlNode(tmpnode);
			}
		}
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Rimuove i fatti dummy dalla lista di fatti
	PARAMETER	: fct		inizio array fatti
			  num_fct	puntatore numero fatti
	RETURN		:
-----------------------------------------------------------------
*/
void remove_dummy_pred(int *fct, int *num_fct)
{
	int		*p;

	for (p = fct; p < &fct[*num_fct]; p++)
		if ((*p > 0) &&
			(grelevant_facts[*p].predicate >= 0) &&
			strstr(gpredicates[grelevant_facts[*p].predicate], DUMMY_PRED_STRING) != 0)
			*p = fct[--(*num_fct)];
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Dato un effetyto condizionale, ritorna
			  la sua posizione all'interno del file
			  delle azioni
	PARAMETER	: cef	Effetto condizionale
	RETURN		: posizione all'interno del file delle azioni
-----------------------------------------------------------------
*/
int get_condeffect_pln_pos(CondEfConn *cef)
{
	int	i;

	for (i = 0; i < gef_conn[cef->ef].num_I; i++)
		if ((gef_conn[cef->ef].I[i]) == (cef - gcondef_conn))
			return(gef_conn[cef->ef].num_I - i - 1);

	fprintf(stderr, "Effetto condizionale %d non trovato in Pl2Operator\n", cef - gcondef_conn);
	exit(1);
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Spostamento dei special fact utilizzati
			  negli effeti condizionali
	PARAMETER	:
	RETURN		:
-----------------------------------------------------------------
*/
void add_cond_effects_to_comp_vars (void)
{
	CondEfConn	*cef;
	PlNode		*effects;
	PlNode		*e;
	int		num_cond_effect;

	// per ogni azione, inserisce gli effetti numerici
	for (cef = gcondef_conn; cef < &gcondef_conn[gnum_condef_conn]; cef++) {

		remove_dummy_pred(cef->PC, &cef->num_PC);
		remove_dummy_pred(cef->A, &cef->num_A);
		remove_dummy_pred(cef->D, &cef->num_D);

		// puntatore agli effetti dell'operatore corrispondente
		effects = cef->plop->effects;
		if (effects->connective == AND)
			effects = effects->sons;

		// per ogni effetto dell'azione
		num_cond_effect = 0;
		for (e = effects; e; e = e->next) {
			if (e->connective == WHEN) {
				if (get_condeffect_pln_pos(cef) == num_cond_effect) {
					add_cond_effects_to_comp_vars_precond(cef, e->sons);
					add_cond_effects_to_comp_vars_effect(cef, e->sons->next);

					add_numeric_cond_effects_to_comp_vars(cef, e->sons);		// condizioni
					add_numeric_cond_effects_to_comp_vars(cef, e->sons->next);	// effetti
				}
				num_cond_effect++;
			}
		}
	}
}



void
add_effects_to_comp_vars (int from_ef_conn, int to_ef_conn)
{
  int i, pos, fct;
  PlNode *effects;
  PlNode *n;
  PlNode *e;

  /* per ogni azione, inserisce gli effetti numerici */
  for (i = from_ef_conn; i < to_ef_conn; i++)
    {
      remove_dummy_pred(gef_conn[i].A, &gef_conn[i].num_A);
      remove_dummy_pred(gef_conn[i].D, &gef_conn[i].num_D);

      /* puntatore agli effetti dell'operatore corrispondente */
      effects = gef_conn[i].plop->effects;

      if (effects->connective == AND)
	effects = effects->sons;
      /* per ogni effetto dell'azione */
      for (n = effects; n; n = n->next)
	{
	  e = n;
	  /* effetto at_start cancellante, di tipo bool : individuare e spostare in D_start */
	  /* effetto at_start additivo, di tipo bool    : ibdividuare e spostare in A_start */
	  /* effetto at_end numerico                    :  aggiungere in A o A_start */

	  /* effetto at_start cancellante, di tipo bool : individuare e spostare in D_start */
	  if ((e->connective == AT_START_CONN) && (e->sons->connective == NOT))
	    {
	      /*ricavo la posizione del fatto corrente */
	      pos =
		get_fct_pos_from_plnode (n->sons, gef_conn[i].plop, gef_conn[i].op, gef_conn[i].D, gef_conn[i].num_D);
	      if (pos == -1)
		{
#ifdef __TEST__
		  if (DEBUG2)
		    printf("\n\n1 fact generated by plnode wasn't found among the effects\n\n");
#endif
		  continue;
		  exit (1);
		}
	      fct = gef_conn[i].D[pos];
	      /* sposta l'elemento in ultima posizione nell'array dei fatti cancellanti al posto di quello da togliere */
	      /* contemporaneamente decrementa il numero di effetti cancellanti che avvengono alla fine (num_D) */
	      gef_conn[i].D[pos] = gef_conn[i].D[--gef_conn[i].num_D];
	      /* salva l'indice del fatto booleano cancellante che avviene AT_START ed incrementa num_D_start */
	      gef_conn[i].sf->D_start[gef_conn[i].sf->num_D_start++] = fct;
	    }
	  
	  /* 
	     effetto additivo at_end : controllare che nn compaia nelle preconditioni 
	  */
	  if ((e->connective == AT_END_CONN) && (e->sons->connective == ATOM)) 
	    {
	      /*ricavo la posizione del fatto corrente */
	      pos =
		get_fct_pos_from_plnode (n->sons, gef_conn[i].plop, gef_conn[i].op, gef_conn[i].A,
					 gef_conn[i].num_A);
	      if (pos == -1)
		{
#ifdef __TEST__
		  if (DEBUG2)
		    printf("\n\n2 fact generated by plnode wasn't found among the effects\n\n");
#endif
		  continue;
		  exit (1);
		}
	      
	      fct = gef_conn[i].A[pos];

	     /*Effetto additivo At-end*/
	      /* Rimuovo l'azione del vettore gft_conn[...].A solo se il fatto è nelle precondizioni */
	      if (is_fact_in_preconditions(i, fct) || is_fact_in_preconditions_overall(i, fct) || is_fact_in_preconditions_end(i, fct)) {
		for (pos = 0; (pos < gft_conn[fct].num_A) && (i != gft_conn[fct].A[pos]); pos++);
		if ((pos >= 0) && (pos < gft_conn[fct].num_A))
		  gft_conn[fct].A[pos] = gft_conn[fct].A[--gft_conn[fct].num_A];
	      }
	      
	    }
	  

	  /* 
	     effetto at_start additivo, di tipo bool    : individuare e spostare in A_start 
	     e controllare che non compaia nelle precondizioni dell'azione 
	  */
	  if ((e->connective == AT_START_CONN) && (e->sons->connective == ATOM))
	    {
	      /*ricavo la posizione del fatto corrente */
	      pos =
		get_fct_pos_from_plnode (n->sons, gef_conn[i].plop, gef_conn[i].op, gef_conn[i].A,
					 gef_conn[i].num_A);
	      if (pos == -1)
		{
#ifdef __TEST__
		  if (DEBUG2)
		    printf("\n\n2 fact generated by plnode wasn't found among the effects\n\n");
#endif
		  continue;
		  exit (1);
		}
	      fct = gef_conn[i].A[pos];
	      /* sposta l'elemento in ultima posizione nell'array dei fatti additivi al posto di quello da togliere */
	      /* contemporaneamente decrementa il numero di effetti additivi che avvengono alla fine (num_A) */
	      gef_conn[i].A[pos] = gef_conn[i].A[--gef_conn[i].num_A];
	      /* salva l'indice del fatto booleano additivo che avviene AT_START ed incrementa num_A_start */
	      gef_conn[i].sf->A_start[gef_conn[i].sf->num_A_start++] = fct;

	      /*Effetto additivo At-start*/
	      /* Rimuovo l'azione del vettore gft_conn[...].A solo se il fatto è nelle precondizioni at-start */
	      if (is_fact_in_preconditions(i, fct)) {
		for (pos = 0; (pos < gft_conn[fct].num_A) && (i != gft_conn[fct].A[pos]); pos++);
		if ((pos >= 0) && (pos < gft_conn[fct].num_A))
		  gft_conn[fct].A[pos] = gft_conn[fct].A[--gft_conn[fct].num_A];
	      }

	    }

	  /* se effetto booleano, non deve fare altro (att:effetti condiz. non gestiti!) */
	  if ((n->connective == AT_START_CONN) || (n->connective == AT_END_CONN) || (n->connective == OVER_ALL_CONN))
	    e = n->sons;

	  switch (e->connective) {
	  case ATOM:
	  case NOT:
	  case WHEN:
		break;

	  case INCREASE_CONN:
	  case DECREASE_CONN:
	  case SCALE_UP_CONN:
	  case SCALE_DOWN_CONN:
	  case ASSIGN_CONN:
		// effetto numerico                    :  aggiungere in A o A_start
		// se incontro uno di questi connective, passo ad aggiungere le composite vars
		if (n->connective == AT_START_CONN)
			// scandisco tutta l'espressione (cioe, nodo INCREASE compreso)
			gef_conn[i].sf->A_start[gef_conn[i].sf->num_A_start++] = -index_in_cvars_of_expression (e, i);
		if ((n->connective == AT_END_CONN) || (e->connective == n->connective))	{// 2^ disg. per azione non durativa
			// scandisco tutta l'espressione (cioe, nodo INCREASE compreso)
			gef_conn[i].A[gef_conn[i].num_A++] = -index_in_cvars_of_expression (e, i);
		}
		break;

	  default:
	    continue;
	    if (e->connective == ALL || e->connective == EX)
	      continue;
	    
	    fprintf(stderr, "\n\nadd_effects_to_comp_vars: Unexpected node: \n");
	    print_PlNode (e, 0);
	    exit (1);
	  }
	}
    }
}

void
add_preconds_to_comp_vars (int from_ef_conn, int to_ef_conn)
{
  int i, pos, fct;
  PlNode *n;
  PlNode *e;
  PlNode *preconds;

  /*per ogni azione, inserisce le precondizioni numeriche */
  for (i = from_ef_conn; i < to_ef_conn; i++)
    {
      if (!gef_conn[i].plop -> preconds)
	continue;
      gef_conn[i].num_PC = gef_conn[i].num_PC;
      /* puntatore alle preco dell'operatore corrispondente */
      preconds = gef_conn[i].plop->preconds;
      if (preconds->connective == AND)
	preconds = preconds->sons;

      /*per ogni preco dell'azione */
      for (n = preconds; n; n = n->next)
	{
	  e = n;

	  /* preco overall, di tipo bool       : individuare e spostare in PC_overall */
	  /* preco at_end, di tipo bool        : individuare e spostare in PC_end */
	  /* preco numerica                    :  aggiungere in PC, PC_overall, PC_end */

	  /* preco overall, di tipo bool       : individuare e spostare in PC_overall */
	  if ((e->connective == OVER_ALL_CONN)
	      && (e->sons->connective == ATOM))
	    {
	      /*ricavo la posizione del fatto corrente */
	      pos = get_fct_pos_from_plnode (n->sons, gef_conn[i].plop, gef_conn[i].op, gef_conn[i].PC, gef_conn[i].num_PC);
	      if (pos == -1)
		{
		  if (DEBUG2)
		    printf("\n\n3 fact generated by plnode wasn't found among the effects\n\n");
		  continue;
		  //exit(1);
		}
	      fct = gef_conn[i].PC[pos];
	      /* sposta l'elemento in ultima posizione nell'array dei fatti al posto di quello da togliere */
	      /* contemporaneamente decrementa il numero di fatti che avvengono alla fine (num_) */
	      gef_conn[i].PC[pos] = gef_conn[i].PC[--gef_conn[i].num_PC];
	      /* salva l'indice del fatto booleano -fct- ed incrementa num_*_*  */
	      gef_conn[i].sf->PC_overall[gef_conn[i].sf->num_PC_overall++] = fct;
	    }


	  /* preco at_end, di tipo bool        : individuare e spostare in PC_end */
	  if ((e->connective == AT_END_CONN) && (e->sons->connective == ATOM))
	    {
	      /*ricavo la posizione del fatto corrente */
	      pos = get_fct_pos_from_plnode (n->sons, gef_conn[i].plop, gef_conn[i].op, gef_conn[i].PC, gef_conn[i].num_PC);
	      if (pos == -1)
		{
#ifdef __TEST__
		  if (DEBUG2)
		    printf("\n\n4 fact generated by plnode wasn't found among the effects\n\n");
#endif
		  continue;
		  exit (1);
		}
	      fct = gef_conn[i].PC[pos];
	      /* sposta l'elemento in ultima posizione nell'array dei fatti al posto di quello da togliere */
	      /* contemporaneamente decrementa il numero di fatti che avvengono alla fine (num_) */
	      gef_conn[i].PC[pos] = gef_conn[i].PC[--gef_conn[i].num_PC];
	      /* salva l'indice del fatto booleano -fct- ed incrementa num_*_*  */
	      gef_conn[i].sf->PC_end[gef_conn[i].sf->num_PC_end++] = fct;
	    }


	  /* se preco booleano, non deve fare altro */
	  if ((n->connective == AT_START_CONN) || (n->connective == AT_END_CONN) || (n->connective == OVER_ALL_CONN))
	    e = n->sons;
	  if ((e->connective == ATOM) || (e->connective == NOT))
	    continue;

	  /* preco numerica                    :  aggiungere in PC, PC_overall, PC_end */
	  /* se incontro uno di questi connective, passo ad aggiungere le composite vars */
	  if (e->connective == BIN_COMP)
	    {
	      e = e->sons;
	      switch (n->connective)
		{
		case OVER_ALL_CONN:
		  gef_conn[i].sf->PC_overall[gef_conn[i].sf->num_PC_overall++] =
		    -index_in_cvars_of_expression (e, i);
		  break;
		case AT_END_CONN:
		  gef_conn[i].sf->PC_end[gef_conn[i].sf->num_PC_end++] =  -index_in_cvars_of_expression (e, i);
		  break;
		default:
		  gef_conn[i].PC[gef_conn[i].num_PC++] = -index_in_cvars_of_expression (e, i);
		}
	    }
	  else
	    {
	      continue;
	      if (e->connective == ALL || e->connective == EX)
		continue;

	      printf ("\n\nadd_preconds_to_comp_vars: Unexpected node: \n");
	      print_PlNode (e, 0);
	      exit (1);
	    }
	}
    }
}



void
calc_duration_of_actions (int from_ef_conn, int to_ef_conn)
{
  int i, ind;
  PlNode *duration;
  PlOperator *plop;

  for (plop = gloaded_pl2ops; plop; plop = plop->next)
    if (plop->duration)
      {
	GpG.durative_actions_in_domain = TRUE;
	break;
      }
    if (GpG.durative_actions_in_domain)
      GpG.min_action_time = MAXFLOAT;
    else
      GpG.min_action_time = STRIPS_ACTIONS_DURATION;
  /*per ogni azione, inserisce le precondizioni numeriche */
  for (i = from_ef_conn; i < to_ef_conn; i++)
    {
      if (!GpG.durative_actions_in_domain) {
	gef_conn[i].duration = STRIPS_ACTIONS_DURATION;
	continue;
      }
      /* inserisce l'espressione della durata per poterla valutare */
      duration = gef_conn[i].plop->duration;
      /*solo durate prefissate: la durata a discrezione del planner non viene usata */
      if (duration)
	{
	  if (duration->sons->sons->connective != EQUAL_CONN)
	    {
	      printf ("\n\nDuration inequalities are not supported by this version\n\n");
	      exit (1);
	    }
	  /* per poter assegnare la durata devo costruire la/e cvar e/o determinarne l'indice del nodo padre nelle gcompvar */
	  ind = index_in_cvars_of_expression (duration->sons->sons->sons->next, i);
	  gef_conn[i].duration = eval_comp_var (&gcomp_var[ind], ind);

	  gef_conn[i].duration = ROUND_TO_1_1000 (gef_conn[i].duration);

	  //Salvo nel gef_conn l'indice dell'espressione
	  gef_conn[i].dur_var_index = ind;

	}
      /**
      if (gef_conn[i].duration < MIN_ACTION_DURATION)
	gef_conn[i].duration = MIN_ACTION_DURATION;
      **/
      if (gef_conn[i].duration < GpG.min_action_time)
	GpG.min_action_time = gef_conn[i].duration;
    }
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Per ogni fatto numerico aggiunge alla
			  lista l'effetto condizionali (se lo modifica)
	PARAMETER	: cef	puntatore ad CondEfConn
	RETURN		:
-----------------------------------------------------------------
*/
void cvar_modified_by_condef_conn(CondEfConn *cef)
{
	CompositeNumVar	*gve;
	int		init_vect[MAX_FUNCTIONS];
	int		num_functions;
	int		*already_added;
	int		fct_index;
	int		i;
	int		*fact_array;
	int		size;

	num_functions = 0;
	already_added = alloc_vect(max_num_value / 32 + 1);

	if (cef->sf == NULL) {
		size = cef->num_A;
		fact_array = malloc(size * sizeof(int));
		memcpy(&fact_array[0], cef->A, cef->num_A * sizeof(int));
	} else {
		size = cef->num_A + cef->sf->num_A_start;
		fact_array = malloc(size * sizeof(int));
		memcpy(&fact_array[0], cef->A, cef->num_A * sizeof(int));
		memcpy(&fact_array[cef->num_A], cef->sf->A_start, cef->sf->num_A_start * sizeof(int));
	}

	for (i = 0; i < size; i++) {
		if (fact_array[i] < 0) {
#ifdef __TEST__
			printf("\n Effect %d ", fact_array[i]);
			print_ft_name_effect(fact_array[i]);
#endif
			gve = &gcomp_var_effects[-fact_array[i]];

			init_vect[num_functions++] = gve->first_op;
			if (num_functions > MAX_FUNCTIONS) {
				printf("\n Increase MAX_FUNCTIONS");
				exit(1);
			}

			if (gve->operator == ASSIGN_OP) {
				fct_index = gve->first_op;
				if(!GET_BIT(already_added, fct_index)) {
					SET_BIT (already_added, fct_index);
					add_condefconn_to_decrease_list_of (cef - gcondef_conn, fct_index);
					add_condefconn_to_increase_list_of (cef - gcondef_conn, fct_index);
				}
			}
		}
	}

	for (i = 0; i <num_functions; i++) {
		fct_index = init_vect[i];

		if (GET_BIT(already_added, fct_index))
			continue;

		if (fabsf (GCOMP_VAR_VALUE(fct_index) - GCOMP_VAR_VALUE_BEFORE(fct_index)) < MIN_VALUE)
			continue;
		// se il valore e' diminuito, segnala che questa cvar e' decrementata dall'efconn corrente
		if (GCOMP_VAR_VALUE(fct_index) < GCOMP_VAR_VALUE_BEFORE(fct_index) )
			add_condefconn_to_decrease_list_of (cef - gcondef_conn, fct_index);
		// se il valore e' aumentato, segnala che questa cvar e' incrementata dall'efconn corrente
		if (GCOMP_VAR_VALUE(fct_index) >= GCOMP_VAR_VALUE_BEFORE(fct_index))
			add_condefconn_to_increase_list_of (cef - gcondef_conn, fct_index);
	}
	free(already_added);
	free(fact_array);
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Calcola il costo di ogni effetto condizionale
	PARAMETER	:
	RETURN		:
-----------------------------------------------------------------
*/
void calc_cost_of_cond_actions (void)
{
	CondEfConn	*cef;
	float		opt_funct_before;

	// salva lo stato corrente prima dell'applicazione dell'azione
	memcpy (gcomp_var_value_before, gcomp_var_value, sizeof (float) * gnum_comp_var);
	
	// salva il valore corrente della funzione di ottimizzazione
	if (goptimization_exp < 0)
	  opt_funct_before = 0.0;
	else
	  opt_funct_before = eval_comp_var(&gcomp_var[goptimization_exp], goptimization_exp);
	
	// per ogni azione, applico i suoi effetti e guardo quello che succede alla funzione da ottimizzare
	for (cef = gcondef_conn; cef < &gcondef_conn[gnum_condef_conn]; cef++) {
#ifdef __TEST__
	  printf ("\n\n\nAction %d :", cef - gcondef_conn);
	  print_op_name (cef->op);
#endif

		apply_numeric_effects_of_condefconn(cef - gcondef_conn);// applies num effects of this efconn

// salva il valore della funzione di ottimizzazione dopo l'applicazione degli effetti numerici
		if (goptimization_exp >= 0)
			cef->cost = eval_comp_var(&gcomp_var[goptimization_exp], goptimization_exp) - opt_funct_before;
		else
			cef->cost = 1.0;

		if ((GpG.maximize_plan) && (cef->cost > 0))
			cef->cost = -cef->cost;

		/**
		if ((cef->cost <= MIN_ACTION_COST) && (cef->cost >= 0))
			cef->cost = MIN_ACTION_COST;
		**/

		cvar_modified_by_condef_conn(cef);
		// ripristina lo stato numerico iniziale
		memcpy(gcomp_var_value, gcomp_var_value_before, sizeof (int) * gnum_comp_var);
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Per ogni fatto numerico aggiunge alla
			  lista l'effetto condizionali (se lo modifica)
	PARAMETER	: cef	puntatore ad EfConn
	RETURN		: TRUE se l'azione influisce sulla metrica 
	                  altrimenti FALSE
-----------------------------------------------------------------
*/
Bool cvar_modified_by_ef_conn(EfConn *ef)
{
  CompositeNumVar	*gve;
  int		init_vect[MAX_FUNCTIONS];
  int		num_functions;
  int		*already_added;
  int		fct_index;
  int		i;
  int		*fact_array;
  int		size;
  int           metric_affected = FALSE;
  IntList       *tmp;
  
  num_functions = 0;
  already_added = alloc_vect((max_num_value >> 5) + 1);
  
  if (ef->sf == NULL) 
    {
      size = ef->num_A;
      fact_array = malloc(size * sizeof(int));
      memcpy(&fact_array[0], ef->A, ef->num_A * sizeof(int));
    } 
  else 
    {
      size = ef->num_A + ef->sf->num_A_start;
      fact_array = malloc(size * sizeof(int));
      memcpy(&fact_array[0], ef->A, ef->num_A * sizeof(int));
      memcpy(&fact_array[ef->num_A], ef->sf->A_start, ef->sf->num_A_start * sizeof(int));
    }
  
  for (i = 0; i < size; i++) 
    {
      if (fact_array[i] < 0) 
	{
	  
#ifdef __TEST__
	  printf("\n Effect %d ", fact_array[i]);
	  print_ft_name_effect(fact_array[i]);
#endif
	  gve = &gcomp_var_effects[-fact_array[i]];
	  
	  if (gve->in_metric)
	    {	    
	      /*
		Questa azione influisce sulla metrica
		
		This action affect metric
	      */
	      metric_affected = TRUE;

	      tmp = new_IntList();
	      tmp->item = i;
	      tmp->next = ef->metric_vars;
	      ef->metric_vars = tmp;
	    }

	  init_vect[num_functions++] = gve->first_op;
	  if (num_functions > MAX_FUNCTIONS) 
	    {
	      printf("\n Increase MAX_FUNCTIONS");
	      exit(1);
	    }
	  
	  switch(gve->operator)
	  {
          case INCREASE_OP:
	    if (gcomp_var[gve->second_op].operator != FIX_NUMBER
		|| GCOMP_VAR_VALUE(gve->second_op) != 0.0)
	    {
	      fct_index = gve->first_op;
	      
	      if(!GET_BIT(already_added, fct_index)) 
		{
		  SET_BIT (already_added, fct_index);
		  add_efconn_to_increase_list_of (ef - gef_conn, fct_index);
		}
	    }
	    break;
	  case SCALE_UP_OP:
	    if (gcomp_var[gve->second_op].operator != FIX_NUMBER
		|| GCOMP_VAR_VALUE(gve->second_op) != 1.0)
	    {
	      fct_index = gve->first_op;
	      
	      if(!GET_BIT(already_added, fct_index)) 
		{
		  SET_BIT (already_added, fct_index);
		  add_efconn_to_increase_list_of (ef - gef_conn, fct_index);
		}
	    }
	    break;
 	  case DECREASE_OP:
	    if (gcomp_var[gve->second_op].operator != FIX_NUMBER
		|| GCOMP_VAR_VALUE(gve->second_op) != 0.0)
	    {
	      fct_index = gve->first_op;
	      
	      if(!GET_BIT(already_added, fct_index)) 
		{
		  SET_BIT (already_added, fct_index);
		  add_efconn_to_decrease_list_of (ef - gef_conn, fct_index);
		}
	    }
	    break;
	  case SCALE_DOWN_OP:
	    if (gcomp_var[gve->second_op].operator != FIX_NUMBER
		|| GCOMP_VAR_VALUE(gve->second_op) != 1.0)
	    {
	      fct_index = gve->first_op;
	      
	      if(!GET_BIT(already_added, fct_index)) 
		{
		  SET_BIT (already_added, fct_index);
		  add_efconn_to_decrease_list_of (ef - gef_conn, fct_index);
		}
	    }
	    break;
	  case ASSIGN_OP:
	    fct_index = gve->first_op;
	    
	    if(!GET_BIT(already_added, fct_index)) 
		{
		  SET_BIT (already_added, fct_index);
		  add_efconn_to_decrease_list_of (ef - gef_conn, fct_index);
		  add_efconn_to_increase_list_of (ef - gef_conn, fct_index);
		}
	    break;
	  default:
	    break;
	  }
	}
    }
  
  for (i = 0; i <num_functions; i++) 
    {
      fct_index = init_vect[i];
      
      if (GET_BIT(already_added, fct_index))
	continue;
      
      if (fabsf (GCOMP_VAR_VALUE(fct_index) - GCOMP_VAR_VALUE_BEFORE(fct_index)) < MIN_VALUE)
	continue;
      // se il valore e' diminuito, segnala che questa cvar e' decrementata dall'efconn corrente
      if (GCOMP_VAR_VALUE(fct_index) < GCOMP_VAR_VALUE_BEFORE(fct_index) )
	add_efconn_to_decrease_list_of (ef - gef_conn, fct_index);
      // se il valore e' aumentato, segnala che questa cvar e' incrementata dall'efconn corrente
      if (GCOMP_VAR_VALUE(fct_index) >= GCOMP_VAR_VALUE_BEFORE(fct_index))
	add_efconn_to_increase_list_of (ef - gef_conn, fct_index);
    }
  
  free(already_added);
  free(fact_array);
  
  return metric_affected;
}







void remove_efconn_from_increase_list_of (int n_ef, int cvar)
{
  IntList *tmp, *aux;

  if (!gcomp_var[cvar].increased_by)
    return;

  if (gcomp_var[cvar].increased_by->item == n_ef)
    {
      aux = gcomp_var[cvar].increased_by;
      gcomp_var[cvar].increased_by = aux->next;
      aux->next = NULL;
      free_intlist(aux);
    }
  else
    {
      for (tmp = gcomp_var[cvar].increased_by; tmp->next; tmp = tmp->next)
	{
	  if (tmp->next->item == n_ef)
	    {
	      aux = tmp->next;
	      tmp->next = tmp->next->next;
	      aux->next = NULL;
	      free_intlist(aux);
	      return;
	    } 
	}
    }
}





void remove_efconn_from_decrease_list_of (int n_ef, int cvar)
{
  IntList *tmp, *aux;

  if (!gcomp_var[cvar].decreased_by)
    return;

  if (gcomp_var[cvar].decreased_by->item == n_ef)
    {
      aux = gcomp_var[cvar].decreased_by;
      gcomp_var[cvar].decreased_by = aux->next;
      aux->next = NULL;
      free_intlist(aux);
    }
  else
    {
      for (tmp = gcomp_var[cvar].decreased_by; tmp->next; tmp = tmp->next)
	{
	  if (tmp->next->item == n_ef)
	    {
	      aux = tmp->next;
	      tmp->next = tmp->next->next;
	      aux->next = NULL;
	      free_intlist(aux);
	      return;
	    } 
	}
    }
}





void check_cvar_modified_by_ef_conn(EfConn *ef)
{
  CompositeNumVar	*gve;
  int		i;
  int		*fact_array;
  int		size;
  
  if (ef->sf == NULL) 
    {
      size = ef->num_A;
      fact_array = malloc(size * sizeof(int));
      memcpy(&fact_array[0], ef->A, ef->num_A * sizeof(int));
    } 
  else 
    {
      size = ef->num_A + ef->sf->num_A_start;
      fact_array = malloc(size * sizeof(int));
      memcpy(&fact_array[0], ef->A, ef->num_A * sizeof(int));
      memcpy(&fact_array[ef->num_A], ef->sf->A_start, ef->sf->num_A_start * sizeof(int));
    }
  
  for (i = 0; i < size; i++) 
    {
      if (fact_array[i] < 0) 
	{
	  
#ifdef __TEST__
	  printf("\n Effect %d ", fact_array[i]);
	  print_ft_name_effect(fact_array[i]);
#endif
	  gve = &gcomp_var_effects[-fact_array[i]];
	  
	  switch(gve->operator)
	    {
	    case INCREASE_OP:
	      if (GET_BIT(gis_inertial, gve->second_op)
		  && GCOMP_VAR_VALUE(gve->second_op) == 0.0)
		remove_efconn_from_increase_list_of (ef - gef_conn,  gve->first_op);
	      break;
	    case SCALE_UP_OP:
	      if (GET_BIT(gis_inertial, gve->second_op)
		  && GCOMP_VAR_VALUE(gve->second_op) == 1.0)
		remove_efconn_from_increase_list_of (ef - gef_conn,  gve->first_op);
	      break;
	    case DECREASE_OP:
	      if (GET_BIT(gis_inertial, gve->second_op)
		  && GCOMP_VAR_VALUE(gve->second_op) == 0.0)
		remove_efconn_from_decrease_list_of (ef - gef_conn,  gve->first_op);
	      break;
	    case SCALE_DOWN_OP:
	      if (GET_BIT(gis_inertial, gve->second_op)
		  && GCOMP_VAR_VALUE(gve->second_op) == 1.0)
		remove_efconn_from_decrease_list_of (ef - gef_conn,  gve->first_op);
	      break;
	    case ASSIGN_OP:
	      break;
	    default:
	      break;
	    }
	}
    }
  
  free(fact_array);
  
}




void calc_cost_of_actions (int from_ef_conn, int to_ef_conn)
{
  int i;
  float opt_funct_before;
  float opt_funct_after;
  Bool metric_affected;

  /*
    Setto tutti costi a STRIPS_ACTION_COST se non è definita nessuna metrica
    
    Set all costs to STRIPS_ACTION_COST if there's no metric definition
  */
  if (DEBUG2)
    printf("\n\nCOST OF ACTIONS FROM %d TO %d", from_ef_conn, to_ef_conn);

  if (!GpG.is_metric_present)
    {
      for (i = from_ef_conn; i < to_ef_conn; i++)
	gef_conn[i].cost = STRIPS_ACTIONS_COST;

      return;
    }

  /*
    salva lo stato corrente prima dell'applicazione dell'azione 
    
    save current status before applyng any action
  */
  memcpy (gcomp_var_value_before,  gcomp_var_value, sizeof (float) * gnum_comp_var);

  /*
    salva il valore corrente della funzione di ottimizzazione 
  
    save current optimization function value
  */
  if(goptimization_exp < 0)
    opt_funct_before = 0.0;
  else
    opt_funct_before = eval_comp_var (&gcomp_var[goptimization_exp], goptimization_exp);
  
  for (i = from_ef_conn; i < to_ef_conn; i++)
    {

      /*
	Applico gli effetti numerici di questa azione allo stato numerico corrente

	applies numeric effects of this efconn to the current numeric state
	It is necessary for the following evaluations
      */
      apply_numeric_effects_of_efconn (i);

      gef_conn[i].cost = 0;

      /*
	Setto le variabili modificate da questa azione e controllo se essa ha effetti sulla metrica

	Set the numeric variables affected by this action and check if the metric is affected
      */
      metric_affected = cvar_modified_by_ef_conn(&gef_conn[i]);

      if (!metric_affected) {
	/*
	  Se l'azione non modifica la metrica la salto e ripristini lo stato precedente

	  If metric is not affected by this action reload previous state and skip this action
	*/

        gef_conn[i].cost = MIN_ACTION_COST;
	      
	memcpy(gcomp_var_value, gcomp_var_value_before, sizeof (int) * gnum_comp_var);
	continue;
      }
      
#ifdef __TEST__
      printf ("\nAction %d :", i);
      print_op_name (gef_conn[i].op);
#endif

      if(goptimization_exp >= 0)
	{
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

	  gef_conn[i].cost = opt_funct_after - opt_funct_before;
	}
      else
	gef_conn[i].cost = 1.0;
      
      if(GpG.maximize_plan && gef_conn[i].cost>0)
	gef_conn[i].cost *= -1;
      
      if (fabs(gef_conn[i].cost) <= MIN_ACTION_COST)
	gef_conn[i].cost = MIN_ACTION_COST;
            
      /* 
	 Ripristina lo stato numerico iniziale
	 
	 Reload previous numeric state
      */
      memcpy(gcomp_var_value, gcomp_var_value_before, sizeof (int) * gnum_comp_var);
      
    }
  
  if (DEBUG2)
    {
      for (i = from_ef_conn; i < to_ef_conn; i++)
	printf("\n\nAzione : %d : %s : COST : %.2f", i, print_op_name_string(i, temp_name), gef_conn[i].cost);
    }

#ifdef __TEST__

  printf("\n Action costs:\n");
  for (i = 0; i < gnum_ef_conn; i++)
    {

      printf ("\nAction %d :", i);
      print_op_name (gef_conn[i].op);
      printf(":     %.2f",get_action_cost(i));
    }

#endif

}

void
apply_numeric_effects_of_efconn (int index)
{
  EfConn *ef;
  int *p;

  // applica gli effetti at end
  ef = &gef_conn[index];
  for (p = ef->A; p < &ef->A[ef->num_A]; p++)
    if (*p < 0)
      eval_comp_var (&gcomp_var_effects[-(*p)], -(*p));
  
  if (ef->sf == NULL)
    return;
  
  // applica gli effetti at start se esistono
  for (p = ef->sf->A_start; p < &ef->sf->A_start[ef->sf->num_A_start]; p++)
    if (*p < 0)
      eval_comp_var (&gcomp_var_effects[-(*p)], -(*p));
  
  /*  int j;
  // gli effetti numerici hanno indice che va da num_A e total_num_A, non ha senso partire da zero
  
  for (j = 0; j < gef_conn[index].num_A; j++)
  {
  if (gef_conn[index].A[j] < 0)
  
  eval_comp_var (&gcomp_var_effects[-gef_conn[index].A[j]],-gef_conn[index].A[j]);
  }
  */
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: applica i fatti numerici dell'effetto condizionale
	PARAMETER	: index	indice dell'effetto condizionale
	RETURN		:
-----------------------------------------------------------------
*/
void apply_numeric_effects_of_condefconn (int index)
{
	CondEfConn	*cef;
	int		*p;

// applica gli effetti at end
	cef = &gcondef_conn[index];
	for (p = cef->A; p < &cef->A[cef->num_A]; p++)
		if (*p < 0)
			eval_comp_var (&gcomp_var_effects[-(*p)], -(*p));

	if (cef->sf == NULL)
		return;

// applica gli effetti at start se esistono
	for (p = cef->sf->A_start; p < &cef->sf->A_start[cef->sf->num_A_start]; p++)
		if (*p < 0)
			eval_comp_var (&gcomp_var_effects[-(*p)], -(*p));
}

/**
 * Ridimensiona i vettori relativi alle variabili numeriche
 **/
void resize_num_var_vects() {

  int *temp_inertial;

  /*
    Rialloco i vettori realtivi alle variabili numeriche, tranne gfullnum_initial (fatti numerici iniziali) che ovviamente
    non cresce più dopo la fase di instanziazione iniziale (inst_pre.c)

    gcomp_var_effects cresce in modo indipendente dagli altri vettori, quindi potrei riallocarlo in un
    ciclo a parte. Lo faccio qui perchè in realtà mantiene sempre lo stesso ordine di grandezza di gcomp_var.
  */

  if ((gnum_comp_var >= (max_num_value - 1)) || (gnum_comp_var_effects >= (max_num_value - 1))) {
    max_num_value += MAX_NUM_INC;

    gcomp_var = (CompositeNumVar *) realloc(gcomp_var, max_num_value * sizeof(CompositeNumVar));
    memset ( &gcomp_var[max_num_value - MAX_NUM_INC] , 0, MAX_NUM_INC * sizeof(CompositeNumVar) );

    gcomp_var_value = (float *) realloc(gcomp_var_value, max_num_value * sizeof(float));
    memset ( &gcomp_var_value[max_num_value - MAX_NUM_INC] , 0, MAX_NUM_INC * sizeof(float) );

    gcomp_var_value_before = (float *) realloc(gcomp_var_value_before, max_num_value * sizeof(float));
    memset ( &gcomp_var_value_before[max_num_value - MAX_NUM_INC] , 0, MAX_NUM_INC * sizeof(float) );

    gcomp_var_effects = (CompositeNumVar *) realloc(gcomp_var_effects, max_num_value * sizeof(CompositeNumVar));
    memset ( &gcomp_var_effects[max_num_value - MAX_NUM_INC], 0, MAX_NUM_INC * sizeof(CompositeNumVar));

    /*
      NB !!! Faccio così perchè gis_inertial è un bitvector.
      Se facessi come per gli altri vettori, la memset potrebbe resettare blocchi già
      parzialmente utilizzati, perchè dovrei necessariamente resettare un numero intero
      di byte.
    */
    temp_inertial = (int *)calloc((max_num_value>>5) + 1, sizeof(int));
    memcpy(temp_inertial, gis_inertial, ((max_num_value - MAX_NUM_INC)>>5) * sizeof(int));
    free(gis_inertial);
    gis_inertial = temp_inertial;
    /***********/
  }

}

int scan_all_cnum_vars(CompositeNumVar *vect, CompositeNumVar *cv, int num, float cv_value) {

  int i;
  CompositeNumVar *tmp;

  for (i = 0; i < num; i++) {
    tmp = &vect[i];
    if (tmp->operator == cv->operator
	&& tmp->first_op == cv->first_op
	&& tmp->second_op == cv->second_op) {

      if (cv->operator == FIX_NUMBER) {
	if( GCOMP_VAR_VALUE(i) ==  cv_value)
	  return i;
      }
      else
	return i;

    }
  }

  return 0;

}

/*pln: nodo che descrive l'espressione, ind: numero dell'azione considerata*/
int
index_in_cvars_of_expression (PlNode * pln, int ind)
{
  static int call = 0;
  CompositeNumVar *cvar = NULL;
  float cvar_value = 0.0, cvar_value_before = 0.0;

  int found;
  
#ifdef __TEST__
  int pos;
#endif

  if (!pln)
    return -1;
  call++;

  cvar = new_CompositeNumVar(0);
  
  if (ind < 0) cvar -> in_metric = TRUE;

  switch (pln->connective)
    {
    case F_EXP:
    case F_EXP_T:
    case METRIC_CONN:
      free(cvar);
      return index_in_cvars_of_expression (pln->sons, ind);
    
    case LESS_THAN_CONN:
    case LESS_THAN_OR_EQUAL_CONN:
    case GREATER_THAN_CONN:
    case GREATER_OR_EQUAL_CONN:
    case EQUAL_CONN:
    case MINIMIZE_CONN:
    case MAXIMIZE_CONN:

      cvar->operator = op_from_conn (pln->connective);
      cvar->first_op = index_in_cvars_of_expression (pln->sons, ind);
      cvar->second_op = index_in_cvars_of_expression (pln->sons->next, ind);
      cvar->in_metric = cvar->in_metric || gcomp_var[cvar->first_op].in_metric 
	|| gcomp_var[cvar->second_op].in_metric;
      cvar_value = eval_comp_var (cvar, -1);
      cvar_value_before = cvar_value;
      found = search_cvar_in_cvars (cvar, cvar_value );

      /*gia' presente: ritorno l'indice che ho trovato */
      if (found != -1)
	{

	  //se almeno uno dei due e' non inerziale, la combinazione e' non inerziale
	  if ((!GET_BIT (gis_inertial, cvar->first_op)) || (!GET_BIT (gis_inertial, cvar->second_op)))
	    sub_affects_list (found,gis_inertial);
	  free(cvar);
	  return found;
	}

#ifdef __TEST__
      else {
	pos = scan_all_cnum_vars(gcomp_var, cvar, gnum_comp_var, cvar_value);
	if (pos)
	  printf("\nCvar error: NumVar not found in hash_table (exists at %d)", pos);
      }
#endif

      //se almeno uno dei due e' non inerziale, la combinazione e' non inerziale
      if ((!GET_BIT (gis_inertial, cvar->first_op))
	  || (!GET_BIT (gis_inertial, cvar->second_op)))
	sub_affects_list (gnum_comp_var,gis_inertial);

      /*se non la trovo, l'aggiungo copiando cvar al posto giusto */
      GCOMP_VAR_VALUE(gnum_comp_var)= cvar_value;
      GCOMP_VAR_VALUE_BEFORE(gnum_comp_var)= cvar_value_before;
      //  hash
      cvar->position = gnum_comp_var;
      copy_compvar (&(gcomp_var[gnum_comp_var]), cvar);
       insert_cvar_in_hash(&gcomp_var[gnum_comp_var]);
      /*segnalo che la cvar appena creata e' influenzata dai due operandi */
      add_index_to_affect_list_of (gnum_comp_var, cvar->first_op);
      add_index_to_affect_list_of (gnum_comp_var, cvar->second_op);
      gnum_comp_var++;
      resize_num_var_vects();
      return (gnum_comp_var - 1);
      break;

      /*modifica: increase e decrease,assign,scaleup e down non aggiornano la lista delle affects */
    case INCREASE_CONN:
    case DECREASE_CONN:
    case ASSIGN_CONN:
    case SCALE_UP_CONN:
    case SCALE_DOWN_CONN:
      cvar->operator = op_from_conn (pln->connective);
      cvar->first_op = index_in_cvars_of_expression (pln->sons, ind);
      cvar->second_op = index_in_cvars_of_expression (pln->sons->next, ind);
      cvar->in_metric = cvar->in_metric || gcomp_var[cvar->first_op].in_metric || gcomp_var[cvar->second_op].in_metric;

      //aggiunta per segnalare info statiche
      found = search_cvar_in_cvars_effects(cvar, cvar_value);

      /*gia' presente: ritorno l'indice che ho trovato */
      if (found != -1)
	{

	  //marco questo nodo come dinamico
	  sub_affects_list (cvar->first_op,gis_inertial);
	  free(cvar);
	  return found;
	}

#ifdef __TEST__
      else {
	pos = scan_all_cnum_vars(gcomp_var_effects, cvar, gnum_comp_var_effects, cvar_value);
      	if (pos)
	  printf("\nCvar effects error : NumVar not found in hash_table (exists at %d)", pos);
      }
#endif

      sub_affects_list (cvar->first_op,gis_inertial);

      /*
	NB: incremento gli effects prima di inserire la cvar nella hash table!!
	(i fatti numerici avranno indici negativi a partire da -1)
      */
      gnum_comp_var_effects++;
      cvar->position = gnum_comp_var_effects;
      copy_compvar (&(gcomp_var_effects[gnum_comp_var_effects]), cvar);
      insert_cvar_in_hash_effects(&gcomp_var_effects[gnum_comp_var_effects]);

      resize_num_var_vects();
      return (gnum_comp_var_effects);

    case PLUS_CONN:
    case MINUS_CONN:
    case MUL_CONN:
    case DIV_CONN:
      cvar->operator = op_from_conn (pln->connective);
      cvar->first_op = index_in_cvars_of_expression (pln->sons, ind);
      cvar->second_op = index_in_cvars_of_expression (pln->sons->next, ind);
      cvar->in_metric = cvar->in_metric || gcomp_var[cvar->first_op].in_metric 
	|| gcomp_var[cvar->second_op].in_metric;
      cvar_value = eval_comp_var (cvar, -1);
      cvar_value_before = cvar_value;
      found = search_cvar_in_cvars (cvar, cvar_value);
      /*gia' presente: ritorno l'indice che ho trovato */
      if (found != -1)
	{
	 
	  //se almeno uno dei due e' non inerziale, la combinazione e' non inerziale
	  if ((!GET_BIT (gis_inertial, cvar->first_op))
	      || (!GET_BIT (gis_inertial, cvar->second_op)))
	    sub_affects_list (found,gis_inertial);
	  free(cvar);
	  return found;
	}

#ifdef __TEST__
      else {
	pos = scan_all_cnum_vars(gcomp_var, cvar, gnum_comp_var, cvar_value);
	if (pos)
	  printf("\nCvar error: NumVar not found in hash_table (exists at %d)", pos);
      }
#endif
      

      //se almeno uno dei due e' non inerziale, la combinazione e' non inerziale
      if ((!GET_BIT (gis_inertial, cvar->first_op))
	  || (!GET_BIT (gis_inertial, cvar->second_op)))
	sub_affects_list (gnum_comp_var,gis_inertial);

      /*se non la trovo, l'aggiungo copiando cvar al posto giusto */
      GCOMP_VAR_VALUE(gnum_comp_var)= cvar_value;
      GCOMP_VAR_VALUE_BEFORE(gnum_comp_var)= cvar_value_before;

      // hash
      cvar->position = gnum_comp_var;
      copy_compvar (&(gcomp_var[gnum_comp_var]), cvar);
      insert_cvar_in_hash(&gcomp_var[gnum_comp_var]);

      /*segnalo che la cvar appena creata e' influenzata dai due operandi */
      add_index_to_affect_list_of (gnum_comp_var, cvar->first_op);
      add_index_to_affect_list_of (gnum_comp_var, cvar->second_op);
      gnum_comp_var++;
      resize_num_var_vects();

      return (gnum_comp_var - 1);

    case UMINUS_CONN:
      cvar->operator = op_from_conn (pln->connective);
      cvar->first_op = index_in_cvars_of_expression (pln->sons, ind);
      cvar->in_metric = cvar->in_metric || gcomp_var[cvar->first_op].in_metric;
      cvar->second_op = -1;
      cvar_value = eval_comp_var (cvar, -1);
      cvar_value_before = cvar_value;
      found = search_cvar_in_cvars (cvar, cvar_value);

      /*gia' presente: ritorno l'indice che ho trovato */
      if (found != -1)
	{

	  //se first non inerziale, anche la cvar e' non inerzial
	  if (!GET_BIT (gis_inertial, cvar->first_op))
	    sub_affects_list (found,gis_inertial);
	  free(cvar);
	  return found;
	}

#ifdef __TEST__
      else {
	pos = scan_all_cnum_vars(gcomp_var, cvar, gnum_comp_var, cvar_value);
	if (pos)
	  printf("\nCvar error: NumVar not found in hash_table (exists at %d)", pos);
      }
#endif


      if (!GET_BIT (gis_inertial, cvar->first_op))
	sub_affects_list (gnum_comp_var,gis_inertial);
      /*se non la trovo, l'aggiungo copiando cvar al posto giusto */
      GCOMP_VAR_VALUE(gnum_comp_var)= cvar_value;
      GCOMP_VAR_VALUE_BEFORE(gnum_comp_var)= cvar_value_before;

      // hash
      cvar->position = gnum_comp_var;
      copy_compvar (&(gcomp_var[gnum_comp_var]), cvar);
      insert_cvar_in_hash(&gcomp_var[gnum_comp_var]);
      /*segnalo che la cvar appena creata e' influenzata dai due operandi */
      add_index_to_affect_list_of (gnum_comp_var, cvar->first_op);
      gnum_comp_var++;
      resize_num_var_vects();
      return (gnum_comp_var - 1);

    case DURATION_VAR_ATOM:
      if (gef_conn[ind].dur_var_index == -1)
	printf ("\n\nwarning! shouldn't be -1\n\n");
      return gef_conn[ind].dur_var_index;

    case FN_HEAD:
      /*dal figlio di questo nodo ricava la numvar che poi ricerchero' tra le grandezze primarie */
      cvar->operator = VARIABLE_OP;
      cvar->first_op = get_numvar_index_of_fn_head (pln, ind);
      cvar->in_metric = cvar->in_metric || gcomp_var[cvar->first_op].in_metric;
      cvar->second_op = -1;


      //se non ho trovato la variabile (first_op=-1), non ha senso valutare il nodo cvar
      if (cvar->first_op == -1)
	{
	  cvar_value =-1e6;  // XXXXX // 0.0; // -1e6;
	  printf("\nWarning variable ");
	  print_PlNode(pln, ind);
	  printf("  not found initialization to 0; action:  ");
	  print_op_name(ind);
	}
      else
	cvar_value = eval_comp_var (cvar, cvar->first_op);
      
      cvar_value_before = cvar_value;
      found = search_cvar_in_cvars (cvar, cvar_value);
      /*gia' presente: ritorno l'indice che ho trovato */
      if (found != -1) {

	free(cvar);
	return found;
      }

#ifdef __TEST__
      else {
	pos = scan_all_cnum_vars(gcomp_var, cvar, gnum_comp_var, cvar_value);
	if (pos)
	  printf("\nCvar error: NumVar not found in hash_table (exists at %d)", pos);
      }
#endif

      /*se non la trovo, l'aggiungo copiando cvar al posto giusto */
      GCOMP_VAR_VALUE(gnum_comp_var)= cvar_value;
      GCOMP_VAR_VALUE_BEFORE(gnum_comp_var)= cvar_value_before;
      // hash
      cvar->position = gnum_comp_var;
      copy_compvar (&(gcomp_var[gnum_comp_var]), cvar);
      insert_cvar_in_hash(&gcomp_var[gnum_comp_var]);
      gnum_comp_var++;
      resize_num_var_vects();
      return (gnum_comp_var - 1);

    case NUM_EXP:
    case ATOM:
      cvar->operator = FIX_NUMBER;
      cvar->first_op = -1;
      cvar->second_op = -1;
      cvar_value = evaluate_exp (pln);
      cvar_value_before = cvar_value;
      found = search_cvar_in_cvars (cvar, cvar_value);
      /*gia' presente: ritorno l'indice che ho trovato */
      if (found != -1) {

	free(cvar);
	return found;
      }

      /*se non la trovo, l'aggiungo copiando cvar al posto giusto */
      GCOMP_VAR_VALUE(gnum_comp_var)= cvar_value;
      GCOMP_VAR_VALUE_BEFORE(gnum_comp_var)= cvar_value_before;

      // hash
      cvar->position = gnum_comp_var;
      copy_compvar (&(gcomp_var[gnum_comp_var]), cvar);
      insert_cvar_in_hash(&gcomp_var[gnum_comp_var]);
      gnum_comp_var++;
      resize_num_var_vects();
      SET_BIT(gis_inertial, cvar->position);
      return (gnum_comp_var - 1);

    case TOTAL_TIME_CONN:
      sub_affects_list (TOTAL_TIME_FUNCTION_INDEX,gis_inertial);
      if (ind < 0)
	gcomp_var[TOTAL_TIME_FUNCTION_INDEX].in_metric = TRUE;
     
      return TOTAL_TIME_FUNCTION_INDEX;

    case TIME_VAR:
      cvar->operator = TIME_VAR_OP;
      cvar->first_op = -1;
      cvar->second_op = -1;
      found = search_cvar_in_cvars (cvar, cvar_value);
      /*gia' presente: ritorno l'indice che ho trovato */
      if (found != -1) {
	free(cvar);
	return found;
      }

      // hash
      cvar->position = gnum_comp_var;
      copy_compvar (&(gcomp_var[gnum_comp_var]), cvar);
      insert_cvar_in_hash(&gcomp_var[gnum_comp_var]);
      gnum_comp_var++;
      resize_num_var_vects();
      return (gnum_comp_var - 1);

    default:
      printf ("\n\nindex_in_cvars_of_expression: shouldnt get here\n\n");
      exit (1);
      return -1;
    }
}



float
eval_comp_var (CompositeNumVar * cv, int index)
{
  float tmp, cv_value;
  /* molto simile alla evaluate_exp */
  /*attenzione: deve lavorare sui value before... per poi aggiornare tutto assieme!! */
  switch (cv->operator)
    {
    case FIX_NUMBER:
    case VARIABLE_OP:
      if(index<0)
	{
	  if(index==-1)
	    printf("\n Warning in eval_comp_var index <0 : %d", index);
	  return 0.0;
	}
      else
	return GCOMP_VAR_VALUE(index);
      break;
    case MUL_OP:
      return eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op) *	eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op);
      break;
    case DIV_OP:
      tmp = eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op);
      if (tmp == 0)
	printf ("\n\nWARNING: Division by zero in eval_comp_var\n\n");
      return eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op) / tmp;
      break;
    case PLUS_OP:
      return eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op) +	eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op);
      break;
    case MINUS_OP:
      return eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op) -	eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op);
      break;
    case UMINUS_OP:
      return -eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op);
      break;
    case INCREASE_OP:
      GCOMP_VAR_VALUE(cv->first_op) += eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op);
      cv_value = GCOMP_VAR_VALUE(cv->first_op);
      return cv_value;
      break;
    case DECREASE_OP:
      GCOMP_VAR_VALUE(cv->first_op) -=eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op);
      cv_value = GCOMP_VAR_VALUE( cv->first_op );
      return cv_value;
      break;
    case SCALE_UP_OP:
      GCOMP_VAR_VALUE( cv->first_op ) *= eval_comp_var (&(gcomp_var[cv->second_op]),cv->second_op);
      cv_value = GCOMP_VAR_VALUE( cv->first_op ) ;
      return cv_value;
      break;
    case SCALE_DOWN_OP:
      GCOMP_VAR_VALUE( cv->first_op ) /= eval_comp_var (&(gcomp_var[cv->second_op]),cv->second_op);
      cv_value =GCOMP_VAR_VALUE( cv->first_op );
      return cv_value;
      break;
    case ASSIGN_OP:
      cv_value = eval_comp_var (&(gcomp_var[cv->second_op]),cv->second_op);
      GCOMP_VAR_VALUE(cv->first_op) = cv_value;
      break;
    case MINIMIZE_OP:
      return eval_comp_var (&(gcomp_var[cv->first_op]),cv->first_op);
    case MAXIMIZE_OP:
      return -eval_comp_var (&(gcomp_var[cv->first_op]),cv->first_op);
    case EQUAL_OP:
      cv_value = (eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op) == eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op));
      if(index>=0)
	GCOMP_VAR_VALUE(index)=cv_value;
      return cv_value;
    case GREATER_THAN_OP:
      cv_value = (eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op) > eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op));
      if(index>=0)
	GCOMP_VAR_VALUE(index)=cv_value;
      return cv_value;
    case GREATER_OR_EQUAL_OP:
      cv_value = (eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op) >= eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op));
      if(index>=0)
	GCOMP_VAR_VALUE(index)=cv_value;
      return cv_value;
    case LESS_THAN_OP:
      cv_value = (eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op) < eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op));
      if(index>=0)
	GCOMP_VAR_VALUE(index)=cv_value;
      return cv_value;
    case LESS_THAN_OR_EQUAL_OP:
      cv_value = (eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op ) <= eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op));
      if(index>=0)
	GCOMP_VAR_VALUE(index)=cv_value;
      return cv_value;


      /** SISTEMARE **/
    case TIME_VAR_OP:
      return 0;

    default:
      printf ("\nOperator %d not yet supported in expression evaluation\n\n", cv->operator);
      exit (1);
      return -1;
      break;
    }

  return 0;
}





int
search_cvar_in_cvars (CompositeNumVar * cv, float cv_value)
{
  int hash_index;
  CompositeNumVar *to_check;
  IntList *cvars;
  int result=-1;

  /*se non risulta nella tabella hash, sicuramente non c'e': torno -1 */
  tot++;

  hash_index = cvar_hash_index (cv);

  if (cvar_hash_table[hash_index]<0)
    return -1;

  compl++;

  to_check = NULL;

  // hash
  cvars = gcomp_var[cvar_hash_table[hash_index]].next;
  to_check = &gcomp_var[cvar_hash_table[hash_index]];
  while (to_check)
    {

      if ((to_check->operator == cv->operator)
	  && (to_check->first_op == cv->first_op)
	  && (to_check->second_op == cv->second_op)) {
	if (to_check->operator == FIX_NUMBER) {
	  if( GCOMP_VAR_VALUE(to_check->position) ==  cv_value) {
	    result = to_check->position;
	    break;
	  }
	}
	else {
	  if (cv->in_metric) to_check->in_metric = TRUE;
	  result = to_check->position;
	  break;
	}
      }

      if (cvars) {
	to_check =  &gcomp_var[cvars -> item];
	cvars = cvars -> next;
      }
      else
	to_check = NULL;
    }

  return result;
  //end hash

}



int
search_cvar_in_cvars_effects (CompositeNumVar * cv, float cv_value)
{
  int hash_index;
  CompositeNumVar *to_check;
  IntList *cvars;
  int result=-1;

/*se non risulta nella tabella hash, sicuramente non c'e': torno -1 */
  hash_index = cvar_hash_index_effects (cv);

  if (cvar_hash_table_effects[hash_index]<0)
    return -1;

  cvars = gcomp_var_effects[cvar_hash_table_effects[hash_index]].next;
  to_check = &gcomp_var_effects[cvar_hash_table_effects[hash_index]];
  while (to_check)
    {
      if ((to_check->operator == cv->operator)
	  && (to_check->first_op == cv->first_op)
	  && (to_check->second_op == cv->second_op)) {
	if (cv->in_metric) to_check->in_metric = TRUE;
	result=to_check -> position;
	break;
      }

      if (cvars) {
	to_check =  &gcomp_var_effects[cvars -> item];
	cvars = cvars -> next;
      }
      else
	to_check = NULL;
    }


  return result;
  //end hash


}


void
copy_compvar (CompositeNumVar * dest, CompositeNumVar * src)
{
  
  static int thiscall = 0;

  thiscall++;
  
  //memcpy(dest, src, sizeof(CompositeNumVar));

  dest->position = src->position;
  dest->operator = src->operator;
  dest->first_op = src->first_op;
  dest->second_op = src->second_op;
  dest->in_metric = src->in_metric;

}

void check_numvars(void) {

  int i, m, n;
  indexed_int_list *tmp;
 
  n = m = 0;
  for (i = 0; i < HASH_SIZE; i++) {
    
    m = 0;
    if (numvar_hash_table[i] == NULL) 
      n++;
    else {
      for (tmp = numvar_hash_table[i]; tmp; tmp = tmp->next)
	m++;
      printf("\nPosition %d num vars %d", i, m);
    }
  }
  
  printf("\nVoid positions : %d", n);
  fflush(stdout);
  exit(0);

}

int
get_numvar_index_of_fn_head (PlNode * p, int index)
{
  static NumVar tmpvar;
  int a, j;

  create_numvar_from_fn_head (&tmpvar, p, index);

  a = retrieve_numvar_position(&tmpvar);
  if (a >= 0) {
    return a;
  }

  /**
    {
      printf ("\n\n\nwarning: NumVar not found!\n\n");
      print_NumVar (&tmpvar, -1, -1);
    }
  **/

  if (gnum_fullnum_initial >= max_fullnum_initial - 1) {
    max_fullnum_initial += MAX_NUM_INC;
    gfullnum_initial =  (NumVar **) realloc (gfullnum_initial, max_num_value * sizeof(NumVar *));
    memset (&gfullnum_initial[max_num_value - MAX_NUM_INC], 0, MAX_NUM_INC * sizeof(NumVar *));
  }

  gfullnum_initial[gnum_fullnum_initial] = (NumVar *) malloc (sizeof (NumVar));
  memset(gfullnum_initial[gnum_fullnum_initial], 0, sizeof (NumVar));
  
  gfullnum_initial[gnum_fullnum_initial]->function=tmpvar.function;
  
  for (j = 0; j < gfunarity[tmpvar.function]; j++)
    gfullnum_initial[gnum_fullnum_initial]->args[j] = tmpvar.args[j];

  insert_numvar_in_hash_table(gfullnum_initial[gnum_fullnum_initial], gnum_fullnum_initial);

  make_compvar (&(gcomp_var[gnum_comp_var]), gnum_comp_var, gfullnum_initial[gnum_fullnum_initial]  , gnum_fullnum_initial);
  gcomp_var[gnum_comp_var].position = gnum_comp_var;
  GCOMP_VAR_VALUE(gnum_comp_var)=0.0;
  
  insert_cvar_in_hash (&(gcomp_var[gnum_comp_var]));
  
  gnum_comp_var++;
  gnum_fullnum_initial++;
  
  resize_num_var_vects();

  return (gnum_fullnum_initial-1);
}

void
create_numvar_from_fn_head (NumVar * ret, PlNode * plnvar, int i)
{
  TokenList *tl;
  int arg = 0;
  int ind;
  Token name;

  /*ricavo l'indice della funzione */
  ret->function = index_in_function_table_of (plnvar->atom->item);
  for (tl = plnvar->atom->next; tl; tl = tl->next)
    {
      /*
         es op. (fly ?plane ?from ?to)
         es (decrease (fuel ?plane) (capacity ?plane))
         sto analizzando (capacity ?plane))
         ricavo stringa tl="?plane"
         devo cercare tra i parametri del ploperator(che QUI nn conosco!!!)  l'indice dll'argomento attuale
         in qs caso indice=0
         xxx= l'indice dell'oggetto in posizione 0 dell'azione istanziata corrispondente (che qui nn conosco!)
         ret->args[ind++]=xxx
       */
      name = tl->item;

      if(i==-1)// PER SUPPORTARE metriche con funzioni a piu' di zero argomenti
      {
	  ret->args[arg++]=index_in_objects_table_of(name);
	  continue;
      }

      ind = get_index_of_arg (name, gef_conn[i].plop);

      if (ind>=0)
	ret->args[arg++] =
	  gop_conn[gef_conn[i].op].action->name_inst_table[ind];
      else
	ret->args[arg++] =get_index_of_constant(name);
    }

}

/*cerca nella tabella dei nomi delle funzioni quella indicata dalla stringa */
int
index_in_function_table_of (char *funct_name)
{
  int i;
  for (i = 0; i < gnum_functions; i++)
    {
      if (strcmp (funct_name, gfunctions[i]) == SAME)
	return i;
    }
  printf ("\n\nFunction name %s not found in function table\n\n", funct_name);
  exit (1);
  return -1;
}

/*cerca nella tabella dei nomi degli oggetti  quello indicato dalla stringa */
int
index_in_objects_table_of (char *obj_name)
{
  int i;
  for (i = 0; i < gnum_constants; i++)
    {
      if (strcmp (obj_name, gconstants[i]) == SAME)
	return i;
    }
  printf ("\n\nObject name %s not found in objects table\n\n", obj_name);
  exit (1);
  return -1;
}


/* dato un nome di argomento (es. ?plane), ritorna la sua posizione (0=prima) all'interno dei parametri dell'operatore*/
int
get_index_of_arg (char *arg, PlOperator *plop)
{
  TypedList *parms;
  TypedList *n;
  int i = 0;

  parms = plop->parse_params;
  for (n = parms; n; n = n->next)
    {
      if (strcmp (n->name, arg) == SAME)
	return i;
      i++;
    }
  return -1;
}


int
get_index_of_pred (char *arg)
{
  int i;
  char *not_arg;

  for (i = 0; i < gnum_predicates; i++)
    if (strcmp (gpredicates[i], arg) == SAME)
      return i;

  // verifica se il predicato arg è stato trasformato in NOT-arg
  
  if (memcmp (arg, STR_NOT_MINUS, strlen(STR_NOT_MINUS)) == 0) {
    not_arg = arg + strlen(STR_NOT_MINUS);
    for (i = 0; i < gnum_predicates; i++)
      if (strcmp (gpredicates[i], not_arg) == SAME)
	return i;
  }
  

  printf ("\n\nPred name %s not found in params\n\n", arg);
  exit (1);
  return -1;
}


OPERATOR_TYPE
op_from_conn (Connective c)
{
  switch (c)
    {
    case MUL_CONN:
      return MUL_OP;
    case DIV_CONN:
      return DIV_OP;
    case PLUS_CONN:
      return PLUS_OP;
    case MINUS_CONN:
      return MINUS_OP;
    case UMINUS_CONN:
      return UMINUS_OP;
    case INCREASE_CONN:
      return INCREASE_OP;
    case DECREASE_CONN:
      return DECREASE_OP;
    case SCALE_UP_CONN:
      return SCALE_UP_OP;
    case SCALE_DOWN_CONN:
      return SCALE_DOWN_OP;
    case ASSIGN_CONN:
      return ASSIGN_OP;
    case LESS_THAN_CONN:
      return LESS_THAN_OP;
    case LESS_THAN_OR_EQUAL_CONN:
      return LESS_THAN_OR_EQUAL_OP;
    case EQUAL_CONN:
      return EQUAL_OP;
    case GREATER_THAN_CONN:
      return GREATER_THAN_OP;
    case GREATER_OR_EQUAL_CONN:
      return GREATER_OR_EQUAL_OP;
    case MINIMIZE_CONN:
      return MINIMIZE_OP;
    case MAXIMIZE_CONN:
      return MAXIMIZE_OP;
    default:
      printf ("\n\nNot defined\n\n");
      exit (1);
    }
  return -1;
}


void
set_used_vars_in_duration_exp (int efconn, int ncvar)
{ 
  if (ncvar == -1)
    return;
  switch (gcomp_var[ncvar].operator )
    {
    case MUL_OP:
    case DIV_OP:
    case MINUS_OP:
    case UMINUS_OP:
    case PLUS_OP:
    case EQUAL_OP:
      set_used_vars_in_duration_exp (efconn, gcomp_var[ncvar].first_op);
      set_used_vars_in_duration_exp (efconn, gcomp_var[ncvar].second_op);
      break;
    case VARIABLE_OP:
      
      tmp_dur_rvals[gef_conn[efconn].num_duration_rvals++] = gcomp_var[ncvar].first_op;
      
      /*
      if (!gef_conn[efconn].duration_rvals)
	gef_conn[efconn].duration_rvals = alloc_vect (gnum_comp_var / 32 + 1);
      SET_BIT (gef_conn[efconn].duration_rvals, gcomp_var[ncvar].first_op);
      */

      break;
    case FIX_NUMBER:
      break;
    default:
      printf ("\n\nwrong cvar\n\n");
      fflush (stdout);
      assert (0);
      exit (1);
      break;
    }
}







void set_inertial_vars(void)
{
  int i;
  Bool changed = TRUE;
  CompositeNumVar *cv;

  while (changed)
    {
      changed = FALSE;
      
      /**
       * Salto le prime 3 variabile (sono quelle inserite dal pianificatore
       * DUMMY, TOTAL_COST e TOTAL_TIME e vengono gestite in modo diverso)
       **/
      for (i = 3; i < gnum_comp_var; i++)
	{
	  if (GET_BIT(gis_inertial, i))
	    continue;
	  
	  cv = &gcomp_var[i];

	  switch (cv->operator)
	    {
	    case FIX_NUMBER:
	      SET_BIT(gis_inertial, i);
	      changed = TRUE;
	      break;
	    case EQUAL_OP:
	    case GREATER_THAN_OP:
	    case GREATER_OR_EQUAL_OP:
	    case LESS_THAN_OP:
	    case LESS_THAN_OR_EQUAL_OP:
	      if (GET_BIT(gis_inertial, cv->second_op) && GET_BIT(gis_inertial, cv->first_op))
		{
		  SET_BIT(gis_inertial, i);
		  changed = TRUE;
		}
	      break;
	    case MUL_OP:
	    case DIV_OP:
	    case PLUS_OP:
	    case MINUS_OP:
	      if (GET_BIT(gis_inertial, cv->second_op) && GET_BIT(gis_inertial, cv->first_op))
		{
		  SET_BIT(gis_inertial, i);
		  changed = TRUE;
		}
	      break;
	    case UMINUS_OP:
	    case MINIMIZE_OP:
	    case MAXIMIZE_OP:
	      if (GET_BIT(gis_inertial, cv->first_op))
		{
		  SET_BIT(gis_inertial, i);
		  changed = TRUE;
		}
	      break;
	    case VARIABLE_OP:
	      if (!cv->increased_by && 
		  !cv->decreased_by &&
		  !cv->conditional_increased_by &&
		  !cv->conditional_decreased_by &&
		  !cv->changed_by)
		{
		  SET_BIT(gis_inertial, i);
		  changed = TRUE;
		}
	      break;
	    default:
	      break;
	    }
	}
    } 
}






//in una singola passata, sostituisce nell'array gcomp_var le variabili inerziali
//e le combinazioni di variabili inerziali con numeri
void
propagate_inertias (void)
{
  int i;
  IntList *tmp;
  CompositeNumVar *cv;

  if (tmp_dur_rvals)
    free(tmp_dur_rvals);
   
  tmp_dur_rvals = alloc_vect(max_num_value);
  GpG.variable_cost_actions = alloc_vect(gnum_ef_block);
  
  set_inertial_vars();

  for (i = 0; i < gnum_comp_var; i++)
    {
      //se la cvar e' dinamica, non devo fare nulla, salta alla prossima
      if (!GET_BIT (gis_inertial, i))
	continue;
      cv = &gcomp_var[i];
      switch (cv->operator)
	{
	case FIX_NUMBER:
	  //non serve fare altro
	  break;
	case EQUAL_OP:
	case GREATER_THAN_OP:
	case GREATER_OR_EQUAL_OP:
	case LESS_THAN_OP:
	case LESS_THAN_OR_EQUAL_OP:
	  cv->operator= FIX_NUMBER;
	  cv->first_op = -1;
	  cv->second_op = -1;
	  GCOMP_VAR_VALUE(i)= eval_comp_var (cv, i);
	  cv->affects = free_intlist (cv->affects);
	  
	  //le intlist decreased_by e increased_by dovrebbero gia' essere null!!
	  break;
	case MUL_OP:
	case DIV_OP:
	case PLUS_OP:
	case MINUS_OP:
	case UMINUS_OP:
	case MINIMIZE_OP:
	case MAXIMIZE_OP:
	case VARIABLE_OP:
	  cv->operator= FIX_NUMBER;
	  cv->first_op = -1;
	  cv->second_op = -1;
	  cv->affects = free_intlist (cv->affects);
	  //le intlist decreased_by e increased_by dovrebbero gia' essere null!!
	  break;
	default:
	  printf ("\n\nOP not supported by Propagate_inertias\n\n");
	  exit (1);
	  break;
	}
    }
  //controllo che tutte le durate siano fisse
  GpG.variable_duration = FALSE;
  for (i = 0; i < gnum_ef_conn; i++)
    {
      gef_conn[i].num_duration_rvals = 0;
      gef_conn[i].duration_rvals = NULL;

      if (!GET_BIT (gis_inertial, gef_conn[i].dur_var_index))
	{
	  GpG.variable_duration = TRUE;
	  //costruisco il vettore che indica quali sono le var che influiscono sulla durata di quest'azione
	  set_used_vars_in_duration_exp (i, gef_conn[i].dur_var_index);
	  gef_conn[i].duration_rvals = (int *)calloc(gef_conn[i].num_duration_rvals, sizeof(int));
	  assert(gef_conn[i].duration_rvals);
	  memcpy(gef_conn[i].duration_rvals, tmp_dur_rvals, gef_conn[i].num_duration_rvals * sizeof(int));

	}
      
      for (tmp = gef_conn[i].metric_vars; tmp; tmp = tmp->next)
	if (!GET_BIT(gis_inertial, tmp->item))
	  {
	    SET_BIT(GpG.variable_cost_actions, i);
	    break;
	  }
    
      check_cvar_modified_by_ef_conn(&gef_conn[i]);
    }
}

int
get_num_of_effects_of (int index, TimeSpec ts, Bool is_additive)
{
  if (gef_conn[index].plop)
    {
      if (ts == AT_START_TIME)
	{
	  if (is_additive)
	    return gef_conn[index].plop->num_effects_start;
	  else
	    return gef_conn[index].plop->num_deleffects_start;
	}
      if (ts == AT_END_TIME)
	return gef_conn[index].plop->num_numeric_effects_end;
      printf ("\n\nor AT_START neither AT_END!!!\n\n");
      exit (1);
    }
  gef_conn[index].plop = search_name_in_plops (gop_conn[gef_conn[index].op].action->name);
  if (!gef_conn[index].plop)
    {
      printf ("\n\nop not found?!!!\n\n");
      exit (1);
    }
  /*alloca il posto per i fatti speciali solo se serve */
  if (!gef_conn[index].plop -> is_odd)
    gef_conn[index].sf = NULL;
  else
    if (!gef_conn[index].sf)
      gef_conn[index].sf = new_SpecialFacts ();

  if (ts == AT_START_TIME)
    {
      if (is_additive)
	return gef_conn[index].plop->num_effects_start;
      else
	return gef_conn[index].plop->num_deleffects_start;
    }
  if (ts == AT_END_TIME)
    return gef_conn[index].plop->num_numeric_effects_end;
  printf ("\n\nor AT_START neither AT_END!!!\n\n");
  exit (1);
}

int
get_num_of_preconds_of (int index, TimeSpec ts)
{
  if (gef_conn[index].plop)
    {
      switch (ts)
	{
	case AT_START_TIME:
	  return gef_conn[index].plop->num_numeric_preconds_start;
	  break;
	case AT_END_TIME:
	  return gef_conn[index].plop->num_preconds_end;
	  break;
	case OVER_ALL_TIME:
	  return gef_conn[index].plop->num_preconds_overall;
	  break;
	default:
	  printf ("\n\nor AT_START neither AT_END neither OVER_ALL!!!\n\n");
	  exit (1);
	}
    }
  gef_conn[index].plop =
    search_name_in_plops (gop_conn[gef_conn[index].op].action->name);
  if (!gef_conn[index].plop)
    {
      printf ("\n\nop not found?!!!\n\n");
      exit (1);
    }
  /*alloca il posto per i fatti speciali solo se serve */
  if (!gef_conn[index].plop -> is_odd)
    gef_conn[index].sf = NULL;
  else
    if (!gef_conn[index].sf)
      gef_conn[index].sf = new_SpecialFacts ();

  if (ts == AT_START_TIME)
    return gef_conn[index].plop->num_numeric_preconds_start;
  if (ts == AT_END_TIME)
    return gef_conn[index].plop->num_preconds_end;
  if (ts == OVER_ALL_TIME)
    return gef_conn[index].plop->num_preconds_overall;
  printf ("\n\nor AT_START neither AT_END neither OVER_ALL!!!\n\n");
  exit (1);
}


void
add_index_to_affect_list_of (int affected_cvar, int affecting_cvar)
{
  IntList *tmpil;
  tmpil = new_IntList ();
  tmpil->item = affected_cvar;

  if(affecting_cvar>=0)
  {
     tmpil->next = gcomp_var[affecting_cvar].affects;
     gcomp_var[affecting_cvar].affects = tmpil;
  }
  else
    {
      tmpil->next =NULL;

    }
}


void
add_efconn_to_increase_list_of (int n_ef, int cvar)
{
  IntList *tmpil;
  tmpil = new_IntList ();
  tmpil->item = n_ef;
  tmpil->next = gcomp_var[cvar].increased_by;
  gcomp_var[cvar].increased_by = tmpil;

#ifdef __TEST__
  printf ("\n Increase ");
  print_cvar_tree (cvar, -1);
  print_op_name (gef_conn[n_ef].op);
  printf ("\n");
#endif
}

void
add_efconn_to_decrease_list_of (int n_ef, int cvar)
{
  IntList *tmpil;
  tmpil = new_IntList ();
  tmpil->item = n_ef;
  tmpil->next = gcomp_var[cvar].decreased_by;
  gcomp_var[cvar].decreased_by = tmpil;

#ifdef __TEST__
  printf ("\n Decrease ");
  print_cvar_tree (cvar, -1);
  print_op_name (gef_conn[n_ef].op);
  printf ("\n");
#endif


}

/*
-----------------------------------------------------------------
	DESCRIPTION	: aggiunge al fatto numerico l'effetto
			  condizionale che incrementa il fatto stesso
	PARAMETER	: n_cef	indice dell'effetto condizionale
			  cvar	indice fatto numerico
	RETURN		:
-----------------------------------------------------------------
*/
void add_condefconn_to_increase_list_of (int n_cef, int cvar)
{
	IntList *tmpil;

	tmpil = new_IntList ();
	tmpil->item = n_cef;
	tmpil->next = gcomp_var[cvar].conditional_increased_by;
	gcomp_var[cvar].conditional_increased_by = tmpil;
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: aggiunge al fatto numerico l'effetto
			  condizionale che decrementa il fatto stesso
	PARAMETER	: n_cef	indice dell'effetto condizionale
			  cvar	indice fatto numerico
	RETURN		:
-----------------------------------------------------------------
*/
void add_condefconn_to_decrease_list_of (int n_cef, int cvar)
{
	IntList *tmpil;

	tmpil = new_IntList ();
	tmpil->item = n_cef;
	tmpil->next = gcomp_var[cvar].conditional_decreased_by;
	gcomp_var[cvar].conditional_decreased_by = tmpil;
}

/*
  dato:
   - pln, il fatto puntato da pln
   - plop, PlOperator di riferimento
   - op, operatore di riferimento
   - start, l'indirizzo dell'array in cui cercare il fatto descritto da pln
   - max, la lunghezza di quest'ultimo array
  ritorna:
   - l'indice di tale fatto nell'array
*/
//int get_fct_pos_from_plnode (PlNode * pln, int gef_index, int *start, int max)
int get_fct_pos_from_plnode (PlNode * pln, PlOperator *plop, int op, int *start, int max)
{
  char String[MAX_LENGTH];
  int ind, i, j;
  int *cur;
  TokenList *tl;
  int cnt = 0;
  Fact node_f;
  Fact *gef_f;

#ifdef _TEST_GET_FCT
  printf ("\n####get_fct_pos_from_plnode: ");
  print_op_name (op);
#endif

  String[0] = 0;
  if (pln->connective == NOT) {
    pln = pln->sons;
    strcpy(String, STR_NOT_MINUS);
  }
  if (pln->connective == ATOM)
    {
      /*nome del predicato */
      strcat (String, pln->atom->item);
      /*trova l'indice del predicato nella tabella dei predicati */
      node_f.predicate = get_index_of_pred (String);
      /* salva in node_f anche l'indice di ciascun argomento del predicato */
      for (tl = pln->atom->next; tl; tl = tl->next)
	{
	  /* trova la posizione del parametro ?x tra i parametri del ploperator */
	  ind = get_index_of_arg (tl->item, plop);
	  if (ind != -1)
	    /*ricava il numero di oggetto usato in qs particolare istanziazione e lo salva nel Fact node_f */
	    node_f.args[cnt++] =
	      gop_conn[op].action->inst_table[ind];
	  else
	    //aggiunta per il caso in cui nella definizione dell'operatore venga usato un argomento istanziato e non una variabile
	    for (j = 0; j < gnum_constants; j++)
	      if (strcmp (tl->item, gconstants[j]) == SAME)
		{
		  node_f.args[cnt++] = j;
		  break;
		}
	}
#ifdef _TEST_GET_FCT
      printf ("\nFatto da trovare: ");
      print_Fact (&node_f);
#endif

      for (ind = 0; ind < max; ind++)
	{

	  /*aggiorna il puntatore al fatto corrente, preso dall'array nel gef_conn, cosi' come indicato nei params */
	  /* prendo il puntatore start, gli sommo ind, e in quella posizione leggo il valore che usero' come indice
	     in grelevant_facts
	   */


	  cur = start + ind;
	  gef_f = &grelevant_facts[*cur];

#ifdef _TEST_GET_FCT
	  printf ("\nFatto %d ", ind);
	  print_Fact (gef_f);
	  printf (" == ");
	  print_Fact (&grelevant_facts[*cur]);
#endif
	  if (node_f.predicate != gef_f->predicate)
	    continue;

	  for (i = 0; i < garity[node_f.predicate]; i++)
	    if (node_f.args[i] != gef_f->args[i])
	      break;

	  if (i == garity[node_f.predicate])
	    {
#ifdef _TEST_GET_FCT
	      printf ("----OK MATCHED return: %d\n", ind);
#endif
	      return ind;
	    }
	  else
	    continue;
	}
    }
  else
    {
      printf("\n\nget_fct_pos_from_plnode: PlNode is not a boolean fact\n\n");
      exit (1);
    }
  if (DEBUG2)
    {
      printf ("\n\nget_fct_pos_from_plnode: Fact not found: ");
      print_Fact (&node_f);
    }

#ifdef _TEST_GET_FCT1
  printf ("\n\nAction: ");
  print_op_name (op);
  i = gef_index;
  printf ("\n----------PCS START:");
  for (j = 0; j < gef_conn[i].num_PC; j++)
    {
      printf ("\n");
      print_ft_name (gef_conn[i].PC[j]);
    }
  if (gef_conn[i].sf)
    {
      printf ("\n----------PCS OVERALL:");
      for (j = 0; j < gef_conn[i].sf->num_PC_overall; j++)
	{
	  printf ("\n");
	  print_ft_name (gef_conn[i].sf->PC_overall[j]);
	}
      printf ("\n----------PCS END:");
      for (j = 0; j < gef_conn[i].sf->num_PC_end; j++)
	{
	  printf ("\n");
	  print_ft_name (gef_conn[i].sf->PC_end[j]);
	}
      printf ("\n----------ADDS START:");
      for (j = 0; j < gef_conn[i].sf->num_A_start; j++)
	{
	  printf ("\n");
	  print_ft_name (gef_conn[i].sf->A_start[j]);
	}
    }
  printf ("\n----------ADDS END:");
  for (j = 0; j < gef_conn[i].num_A; j++)
    {
      printf ("\n");
      print_ft_name (gef_conn[i].A[j]);
    }
  if (gef_conn[i].sf)
    {
      printf ("\n----------DELS START:");
      for (j = 0; j < gef_conn[i].sf->num_D_start; j++)
	{
	  printf ("\n");
	  print_ft_name (gef_conn[i].sf->D_start[j]);
	}
    }
  printf ("\n----------DELS END:");
  for (j = 0; j < gef_conn[i].num_D; j++)
    {
      printf ("\n");
      print_ft_name (gef_conn[i].D[j]);
    }
  printf ("\n----------IMPLIEDS:");
  for (j = 0; j < gef_conn[i].num_I; j++)
    {
      printf ("\nimplied effect %d of op %d: ",gef_conn[i].I[j], gef_conn[gef_conn[i].I[j]].op);
      print_op_name (gef_conn[gef_conn[i].I[j]].op);
    }
  printf ("\n");
#endif
  return -1;
}


int
cvar_hash_index (CompositeNumVar * cv)
{
  return (cv->operator + abs (cv->first_op) * 2563 + abs (cv->second_op) * 2563 * 2563) % BIGPRIME % HASH_SIZE;
}


int
cvar_hash_index_effects (CompositeNumVar * cv)
{
  return (cv->operator + abs (cv->first_op) * 2563 + abs (cv->second_op) * 2563 * 2563) % BIGPRIME % HASH_SIZE;
}


/**
 * Hash table for num variables
 **/
void reset_numvar_hash_table() {

  /* All pointers to NULL
   */
  memset (numvar_hash_table, 0, HASH_SIZE * sizeof(indexed_int_list *));
}

int numvar_adress(NumVar * v) {

  unsigned long int r = 0;
  int b = 1, i;

  for ( i = gfunarity[v->function] - 1; i > -1; i-- ) {
    r += b * v->args[i];
    b *= gnum_constants;
  }

  r += v->function;

  return r;

}

void insert_numvar_in_hash_table(NumVar *v, int item) {

  int adr, hadr;
  indexed_int_list *tmp;
  
  adr = numvar_adress(v);
  hadr = adr % HASH_SIZE;

  tmp = (indexed_int_list *)malloc(sizeof(indexed_int_list));
  tmp -> op = v -> function;
  tmp -> adr = adr;
  tmp -> item = item;
  tmp -> next = numvar_hash_table[hadr];
  numvar_hash_table[hadr] = tmp;

}

int retrieve_numvar_position(NumVar *v) {
  
  int adr, hadr;
  indexed_int_list *tmp;
  
  adr = numvar_adress(v);
  hadr = adr % HASH_SIZE;
  
  for (tmp = numvar_hash_table[hadr]; tmp; tmp = tmp->next) {
    if ((tmp -> adr == adr)
	&& (tmp -> op == v -> function))
      /* Found
       */
      return tmp -> item;
  }
  
  /* Not found
   */
  return -1;
}

/**
 * END
 **/

void reset_cvar_hash_table()
{
  memset (cvar_hash_table, -1, HASH_SIZE * sizeof (int));

}

void reset_cvar_hash_table_effects()
{
  memset (cvar_hash_table_effects, -1, HASH_SIZE * sizeof (int));

}


#ifdef __TEST__
void check_cvar_hash_table()
{
  int i;
  for(i=0;i<HASH_SIZE;i++)
    if(!(cvar_hash_table[i]==-1 ||(cvar_hash_table[i]>=0 && cvar_hash_table[i]<=gnum_comp_var)))
      printf("\nERROR cvar_hash_table gnum_compvar %d  pos %d  value %d  ",gnum_comp_var,i,cvar_hash_table[i] );

}
#endif


void
insert_cvar_in_hash (CompositeNumVar * cv)
{
  int hash_index;
  IntList *tmp;

  if (gnum_comp_var > max_num_value) {
    printf("\nNumeric variables exceed num var array. Check allocation.\n");
    exit(1);
  }

  hash_index = cvar_hash_index (cv);

  if(cvar_hash_table[hash_index]<0){

    // e' il primo elemento in questa hash position
    cvar_hash_table[hash_index]=cv->position;
    cv->next=NULL;
  }
  else{
    // ci sono gia' elementi in questa hash position
    tmp = new_IntList();
    tmp -> item = cv->position;
    tmp -> next = gcomp_var[cvar_hash_table[hash_index]].next;
    gcomp_var[cvar_hash_table[hash_index]].next = tmp;
  }

#ifdef __TEST__
{
   int i;
   check_cvar_hash_table();
   for(i=0;i<gnum_comp_var;i++) {
     if(gcomp_var[i].position != i)
       printf("\nError gcomp pos: pos %d  index %d",gcomp_var[i].position, i );

     tmp = NULL;
     if (cvar_hash_table[hash_index] >= 0 )
       tmp = gcomp_var[cvar_hash_table[hash_index]].next;
     for (tmp = tmp; tmp; tmp = tmp -> next)
       if (gcomp_var[tmp->item].position != tmp->item)
	 printf("ERROR %d %d", tmp->item, gcomp_var[tmp->item].position);
   }
}
#endif


}

void
insert_cvar_in_hash_effects (CompositeNumVar * cv)
{
  int hash_index;
  IntList *tmp;

  if (gnum_comp_var_effects > max_num_value) {
    printf("\nNumeric variables exceed num var array. Check allocation.\n");
    exit(1);
  }
  
  hash_index = cvar_hash_index_effects (cv);

  if(cvar_hash_table_effects[hash_index]<0){

    // e' il primo elemento in questa hash position
    cvar_hash_table_effects[hash_index]=cv->position;
    cv->next=NULL;
  }
  else{
    // ci sono gia' elementi in questa hash position
    tmp = new_IntList();
    tmp -> item = cv->position;
    tmp -> next = gcomp_var_effects[cvar_hash_table_effects[hash_index]].next;
    gcomp_var_effects[cvar_hash_table_effects[hash_index]].next = tmp;
  }

#ifdef __TEST__
  {
    int i;
    check_cvar_hash_table();
    for(i=0;i<gnum_comp_var;i++) {
      if(gcomp_var[i].position != i)
	printf("\nError gcomp pos: pos %d  index %d",gcomp_var[i].position, i );
      
      tmp = NULL;
      if (cvar_hash_table[hash_index] >= 0 )
	tmp = gcomp_var[cvar_hash_table[hash_index]].next;
      for (tmp = tmp; tmp; tmp = tmp -> next)
	if (gcomp_var[tmp->item].position != tmp->item)
	  printf("ERROR %d %d", tmp->item, gcomp_var[tmp->item].position);
    }
    
  }
#endif
  
  
}

void
set_tested_vars_for_cvar (int ef, int ncvar)
{
  if (ncvar == -1)
    return;

  //if (!tested_vars)
    //tested_vars = alloc_matrix (gnum_ef_conn, gnum_fullnum_blocks);


  switch (gcomp_var[ncvar].operator )
    {
    case MUL_OP:
    case DIV_OP:
    case MINUS_OP:
    case UMINUS_OP:
    case PLUS_OP:
    case EQUAL_OP:
    case GREATER_THAN_OP:
    case GREATER_OR_EQUAL_OP:
    case LESS_THAN_OP:
    case LESS_THAN_OR_EQUAL_OP:
      set_tested_vars_for_cvar (ef, gcomp_var[ncvar].first_op);
      set_tested_vars_for_cvar (ef, gcomp_var[ncvar].second_op);
      break;
    case VARIABLE_OP:
      //SET_BIT (tested_vars[ef], gcomp_var[ncvar].first_op);
      insert_bit_in_bit_table(tested_vars, ef, gcomp_var[ncvar].first_op);
      break;
    case FIX_NUMBER:
      break;
    default:
      printf ("\n\nwrong cvar\n\n");
      fflush (stdout);
      assert (0);
      exit (1);
      break;
    }
}



void initialize_vals_tables(void) {

  int n_bit, bit_row_size, base;
  unsigned long int max_size;
  int bit_block_mask;
  int mask[1];

  mask[0] = 0;

  max_size = gnum_fullnum_initial;

  bit_block_mask = init_bit_table_const(max_size, &n_bit, &base, &bit_row_size);
  
  l_vals.bits = (int_pointer **)calloc(gnum_ef_conn, sizeof(int_pointer *));
  assert(l_vals.bits);

  r_vals.bits = (int_pointer **)calloc(gnum_ef_conn, sizeof(int_pointer *));
  assert(r_vals.bits);
  
  lstar_vals.bits = (int_pointer **)calloc(gnum_ef_conn, sizeof(int_pointer *));
  assert(lstar_vals.bits);
  
  tested_vars.bits = (int_pointer **)calloc(gnum_ef_conn, sizeof(int_pointer *));
  assert(tested_vars.bits);
 
  l_vals.max_row_size = r_vals.max_row_size = 
    lstar_vals.max_row_size = tested_vars.max_row_size = max_size;
  
  l_vals.bit_row_size = r_vals.bit_row_size = 
    lstar_vals.bit_row_size = tested_vars.bit_row_size = bit_row_size;
  
  l_vals.n_bit = r_vals.n_bit = lstar_vals.n_bit = tested_vars.n_bit = n_bit;
  
  l_vals.base = r_vals.base = lstar_vals.base = tested_vars.base = base;

  SET_BIT(mask, bit_block_mask);
  mask[0]--;

  l_vals.div_mask = r_vals.div_mask = 
    lstar_vals.div_mask = tested_vars.div_mask = bit_block_mask;

  l_vals.mod_mask = r_vals.mod_mask = 
    lstar_vals.mod_mask = tested_vars.mod_mask = mask[0];
  
}




void
set_lvals_and_rvals (void)
{
  int i, j, k, b, bext, to_check, temp, tempext,  y, yext;
  Bool is_star_val;

  if (!GpG.is_domain_numeric)
    return;

  if (DEBUG1)
    printf("\n\nMean numeric effects per eff_conn: %.2f", (float)GpG.num_numeric_effects / gnum_ef_conn);

  if (((float)GpG.num_numeric_effects / gnum_ef_conn) < NUMERIC_EF_RATE)
    {
      if (DEBUG1) 
	printf("\nNumeric neighbors in down levels: ON\n");

      GpG.numeric_neighbors_in_down_levels = TRUE;

    }
  else  
    {
      if (DEBUG1) 
	printf("\nNumeric neighbors in down levels: OFF\n");
      
      GpG.hard_numeric_domain = TRUE;
    }


  /*calcolo lvals[i] e rvals[i] */
  for(bext = 0; bext < gnum_ef_block; bext++)
    {	
     
      tempext = GpG.numeric_actions[bext];
      
      yext = 32;
      
      while (tempext) 
	{ 
	  
	  yext--;
	  
	  if (tempext & FIRST_1)
	    {
	      
	      i = (bext << 5) + yext;
	      
	      for (j = 0; j < gef_conn[i].num_PC; j++)
		if (gef_conn[i].PC[j] < 0)
		  {
		    set_tested_vars_for_cvar (i, -gef_conn[i].PC[j]);
		  }
      
	      if (gef_conn[i].sf)
		{
		  for (j = 0; j < gef_conn[i].sf->num_PC_overall; j++)
		    if (gef_conn[i].sf->PC_overall[j] < 0)
		      {
			set_tested_vars_for_cvar(i, -gef_conn[i].sf->PC_overall[j]);
		      }

		  for (j = 0; j < gef_conn[i].sf->num_PC_end; j++)
		    if (gef_conn[i].sf->PC_end[j] < 0)
		      {
			set_tested_vars_for_cvar (i, -gef_conn[i].sf->PC_end[j]);
		      }
		}
      
	      for (j = 0; j < gef_conn[i].num_A; j++)
		if (gef_conn[i].A[j] < 0)
		  {
		    set_rvals_for_cvar(i, gcomp_var_effects[-gef_conn[i].A[j]].second_op);
		  }
	      
	      if (gef_conn[i].sf)
		{
		  for (j = 0; j < gef_conn[i].sf->num_A_start; j++)
		    if (gef_conn[i].sf->A_start[j] < 0)
		      {
			set_rvals_for_cvar(i, gcomp_var_effects[-gef_conn[i].sf->A_start[j]].second_op);
		      }
		}
	      
	    }

	  tempext <<= 1;

	}
    }

  for(bext = 0; bext < gnum_ef_block; bext++)
    {	
      
      tempext = GpG.numeric_actions[bext];
      
      yext = 32;
      
      while (tempext) 
	{ 
	  
	  yext--;
	  
	  if (tempext & FIRST_1)
	    {
	      
	      i = (bext << 5) + yext;
	      
	      for (j = 0; j < gef_conn[i].num_A; j++)
		
		if (gef_conn[i].A[j] < 0)	   
		  {   
		    is_star_val = FALSE;
		    
		    to_check = gcomp_var[gcomp_var_effects[-gef_conn[i].A[j]].first_op].first_op;
		    
		    insert_bit_in_bit_table(l_vals, i, to_check);
		    
		    if ((gcomp_var_effects[-gef_conn[i].A[j]].operator == INCREASE_OP)
			|| (gcomp_var_effects[-gef_conn[i].A[j]].operator == DECREASE_OP))
		      {
			insert_bit_in_bit_table(lstar_vals, i, to_check);
			is_star_val=TRUE;
		      }
		    
		    if(!GpG.lowmemory)
		      {
			for(b = 0; b < gnum_ef_block; b++)
			  {	
			    
			    temp = GpG.numeric_actions[b];
			    
			    y = 32;
			    
			    while (temp) 
			      { 
				
				y--;
				
				if (temp & FIRST_1)
				  {
				    
				    k = (b << 5) + y;
				    
				    if (GET_EF_EF_MX_BIT (i, k))
				      {
					temp <<= 1;
					continue;
				      }
				    
				    if (!gef_conn[k].is_numeric)
				      {
					temp <<= 1;
					continue;
				      }
				    
				    if (check_bit_in_bit_table(tested_vars, k, to_check))
				      {
					SET_EF_EF_MX_BIT (i, k);
					temp <<= 1;
					continue;
				      }
				    
				    if (check_bit_in_bit_table(r_vals, k, to_check))
				      {
					SET_EF_EF_MX_BIT (i, k);
					temp <<= 1;
					continue;
				      }
				    
				    if (k >= i) 
				      {
					temp <<= 1;
					continue;
				      }
				    
				    if (check_bit_in_bit_table(l_vals, k, to_check)) 
				      {
					
					if(is_star_val)
					  {
					    if (!check_bit_in_bit_table(lstar_vals, k, to_check))
					      {
						SET_EF_EF_MX_BIT (i, k);
						temp <<= 1;
						continue;
					      }
					  }		    
					else
					  {
					    if (check_bit_in_bit_table(lstar_vals, k, to_check))  
					      {
						SET_EF_EF_MX_BIT (i, k);
						temp <<= 1;
						continue;
					      } 
					  }
					
					if (check_bit_in_bit_table(tested_vars, i, to_check))
					  {
					    SET_EF_EF_MX_BIT (i, k);
					    temp <<= 1;
					    continue;
					  }
					
				      }
				  }
				
				temp <<= 1;
				
			      }
			  }
		      }
		  }
	      
	      
	      if (gef_conn[i].sf)
		
		for (j = 0; j < gef_conn[i].sf->num_A_start; j++)
		  
		  if (gef_conn[i].sf->A_start[j] < 0)
		    {
		      is_star_val = FALSE;
		      
		      to_check = gcomp_var[gcomp_var_effects[-gef_conn[i].sf->A_start[j]].first_op].first_op;
		      
		      insert_bit_in_bit_table(l_vals, i, to_check);
		      
		      if ((gcomp_var_effects[-gef_conn[i].sf->A_start[j]].operator == INCREASE_OP)
			  || (gcomp_var_effects[-gef_conn[i].sf->A_start[j]].operator == DECREASE_OP))
			{
			  insert_bit_in_bit_table(lstar_vals, i, to_check);
			  is_star_val=TRUE;
			}
		      
		      if(!GpG.lowmemory)
			{
			  for(b = 0; b < gnum_ef_block; b++)
			    {	
			      
			      temp = GpG.numeric_actions[b];
			      
			      y = 32;
			      
			      while (temp) 
				{ 
				  
				  y--;
				  
				  if (temp & FIRST_1)
				    {
				      k = (b << 5) + y;
				      
				      if (GET_EF_EF_MX_BIT (i, k))
					{
					  temp <<= 1;
					  continue;
					}
				      
				      if (!gef_conn[k].is_numeric)
					{
					  temp <<= 1;
					  continue;
					}
				      
				      if (check_bit_in_bit_table(tested_vars, k, to_check))
					{
					  SET_EF_EF_MX_BIT (i, k);
					  temp <<= 1;
					  continue;
					}
				      
				      if (check_bit_in_bit_table(r_vals, k, to_check))
					{
					  SET_EF_EF_MX_BIT (i, k);
					  temp <<= 1;
					  continue;
					}
				      
				      if (k >= i) 
					{
					  temp <<= 1;
					  continue;
					}
				      
				      if (check_bit_in_bit_table(l_vals, k, to_check)) 
					{
					  
					  if(is_star_val)
					    {
					      if (!check_bit_in_bit_table(lstar_vals, k, to_check))
						{
						  SET_EF_EF_MX_BIT (i, k);
						  temp <<= 1;
						  continue;
						}
					    }		    
					  else
					    {
					      if (check_bit_in_bit_table(lstar_vals, k, to_check))  
						{
						  SET_EF_EF_MX_BIT (i, k);
						  temp <<= 1;
						  continue;
						} 
					    }
					  
					  if (check_bit_in_bit_table(tested_vars, i, to_check))
					    {
					      SET_EF_EF_MX_BIT (i, k);
					      temp <<= 1;
					      continue;
					    }
					  
					}
				    }
				  
				  temp <<= 1;
				  
				}
			    }
			}
		    }
	      
	      // valori testati dall'azione
	      
#if FALSE
	      printf ("\n\n-----------------------------------------\nAzione: ");
	      print_op_name (gef_conn[i].op);
	      printf ("\n-------------TESTED VARS:");
	      for (j = 0; j < gnum_fullnum_initial; j++)
		//if (GET_BIT (l_vals[i], j))
		if (check_bit_in_bit_table(tested_vars, i, j))
		  {
		    printf ("\n");
		    print_NumVar (gfullnum_initial[j], j, -1);
		  }
	      printf ("\n-------------LVALS:");
	      for (j = 0; j < gnum_fullnum_initial; j++)
		//if (GET_BIT (l_vals[i], j))
		if (check_bit_in_bit_table(l_vals, i, j))
		  {
		    printf ("\n");
		    print_NumVar (gfullnum_initial[j], j, -1);
		  }
	      printf ("\n-------------L*VALS:");
	      for (j = 0; j < gnum_fullnum_initial; j++)
		//if (GET_BIT (lstar_vals[i], j))
		if (check_bit_in_bit_table(lstar_vals, i, j))  
		  {
		    printf ("\n");
		    print_NumVar (gfullnum_initial[j], j, -1);
		  }
	      printf ("\n-------------RVALS:");
	      for (j = 0; j < gnum_fullnum_initial; j++)
		//if (GET_BIT (r_vals[i], j))
		if (check_bit_in_bit_table(r_vals, i, j))  
		  {
		    printf ("\n");
		    print_NumVar (gfullnum_initial[j], j, -1);
		  }
#endif
	    }

	  tempext <<= 1;

	}
    }
  
}



void
set_rvals_for_cvar (int ef, int ncvar)
{
  if (ncvar == -1)
    return;

  switch (gcomp_var[ncvar].operator )
    {
    case MUL_OP:
    case DIV_OP:
    case MINUS_OP:
    case UMINUS_OP:
    case PLUS_OP:
      set_rvals_for_cvar (ef, gcomp_var[ncvar].first_op);
      set_rvals_for_cvar (ef, gcomp_var[ncvar].second_op);
      break;
    case VARIABLE_OP:
      //SET_BIT (r_vals[ef], gcomp_var[ncvar].first_op);
      insert_bit_in_bit_table(r_vals, ef, gcomp_var[ncvar].first_op);
      break;
    case FIX_NUMBER:
      break;
    case TIME_VAR_OP:
      break;
    default:
      printf ("\n\nset_rvals_for_cvar:wrong cvar\n\n");
      exit (1);
      break;
    }
}


Bool is_time_var_in_compvar(int ncvar)
{

  switch (gcomp_var[ncvar].operator )
    {
    case MUL_OP:
    case DIV_OP:
    case MINUS_OP:
    case UMINUS_OP:
    case PLUS_OP:
      return 
	(is_time_var_in_compvar(gcomp_var[ncvar].first_op)
	 ||
	 is_time_var_in_compvar(gcomp_var[ncvar].second_op));
    case VARIABLE_OP:
      return FALSE;
    case FIX_NUMBER:
      return FALSE;
    case TIME_VAR_OP:
      return TRUE;
    default:
      return FALSE;
    }

}




Bool is_time_var_in_compvar_effects(int ncvar)
{

  switch (gcomp_var_effects[ncvar].operator )
    {
    case INCREASE_OP:
    case DECREASE_OP:
      return 
	(is_time_var_in_compvar(gcomp_var_effects[ncvar].first_op)
	 ||
	 is_time_var_in_compvar(gcomp_var_effects[ncvar].second_op));
    default:
      return FALSE;
    }

}




void set_continuous_effects(void)
{

  int i;

  GpG.continuous_effects = alloc_vect(gnum_block_compvar);

  for (i = 0; i < gnum_comp_var_effects; i++)
    if (is_time_var_in_compvar_effects(i))
      {
	SET_BIT(GpG.continuous_effects, i);
	
	if (TRUE || DEBUG3)
	  {
	    printf("\ncontinuous effect : %d", i);
	    
	  }
	
      }
}





/*alloca una matrice di rows x cols interi*/
int **alloc_matrix (int rows, int cols)
{
  int **matrix;
  int *ptr;
  register  int i;

  /*per non ricalcolare ogni volta il numero di byte */
  matrix = (int **) calloc (rows , sizeof (int *));
  assert (matrix);
  ptr=(int *) calloc (rows*cols,sizeof (int));

  assert (ptr);

  memset (ptr, 0, rows*cols* sizeof (int));

  matrix[0]=ptr;
  for (i = 1; i < rows; i++)
    matrix[i] = (int *) (matrix[i-1] + cols);

  return matrix;
}


/** 
 * Nome: alloc_tri_matrix
 * Alloca una matrice triangolare inferiore di interi di <l> righe 
 * La riga i-esima ha lunghezza pari a (i / 32) + 1 interi
 **/

int **alloc_tri_matrix(int l) 
{
  int **matrix = NULL;
  int *ptr = NULL;
  int i;
  int aux = 0;
  int size = 0;

  matrix = (int **) calloc(l, sizeof(int *));
  assert(matrix);

  aux = l >> 5;
  /* dimensione della matrice (in termini di quanti interi deve contenere) 
   * size = aux * (aux + 1) * 16 + (l % 32) * (aux + 1) 
   */
  size = (aux * (aux + 1)) << 4;
  size += (l&31) * (aux + 1);

  ptr = (int *) calloc(size, sizeof(int));
  assert(ptr);
  memset(ptr, 0, size * sizeof(int)); 
  matrix[0] = ptr;
  for (i = 1, aux = 1; i < l; i++) {
    matrix[i] = (int *) (matrix[i-1] + aux);
    aux = (i >> 5) + 1;                     //# di interi allocati in questa riga
  }

  return matrix;
}

int *alloc_vect (int n_els)
{
  int *vect;

  vect = (int *) calloc (n_els, sizeof (int));

  if (vect == NULL) {
    MSG_ERROR(WAR_NO_MEMORY);
    exit;
  }

  assert (vect);
  memset (vect, 0, n_els * sizeof (int));
  return vect;
}


void index_duration_exps (int from_ef_conn, int to_ef_conn)
{
  int i;
  PlNode *duration;
  PlOperator *plop;

  for (plop = gloaded_pl2ops; plop; plop = plop->next)
    if (plop->duration)
      {
	GpG.durative_actions_in_domain = TRUE;
	break;
      }
  if (!GpG.durative_actions_in_domain)
    return;
  /*per ogni azione, inserisce le precondizioni numeriche */
  for (i = from_ef_conn; i < to_ef_conn; i++)
    {
      /* inserisce l'espressione della durata per poterla valutare */
      duration = gef_conn[i].plop->duration;
      /*solo durate prefissate: la durata a discrezione del planner non viene usata */
      if (duration)
	{
	  if (duration->sons->sons->connective != EQUAL_CONN)
	    {
	      printf("\n\nDuration inequalities are not supported by this version\n\n");
	      exit (1);
	    }

 if (duration->sons->sons->connective == INCREASE_CONN ||duration->sons->sons->connective == DECREASE_CONN||duration->sons->sons->connective == SCALE_UP_CONN||duration->sons->sons->connective == SCALE_DOWN_CONN)
   {
     exit(0);
   }	
  /* per poter assegnare la durata devo costruire la/e cvar e/o determinarne l'indice del nodo padre nelle gcompvar */
	  //Salvo nel gef_conn l'indice dell'espressione
	  gef_conn[i].dur_var_index = index_in_cvars_of_expression (duration->sons->sons->sons->next, i);
	}
    }
}




void make_numgoal_state(PlNode *list)
{


  PlNode *tmp;

  for(tmp=list; tmp; tmp=tmp->next)
    ggoal_state.F[ggoal_state.num_F++]=  -index_in_cvars_of_expression(tmp, -1);


}








int position_in_functions_table (char *str)
{
  int i;

  for (i = 0; i < gnum_functions; i++) {
    if (str == gfunctions[i] || strcmp (str, gfunctions[i]) == SAME) {
      break;
    }
  }

  return (i == gnum_functions) ? -1 : i;
}




void make_NumVar (NumVar * f, PlNode * n, int num_vars)
{
  int m, i;
  TokenList *t;

  f->function = position_in_functions_table (n->atom->item);
  if (f->function == -1) {
    printf ("\nundeclared function %s used in domain definition\n\n", n->atom->item);
    exit (1);
  }

  m = 0;
  for (t = n->atom->next; t; t = t->next) {
    if (t->item[0] == '?') {
      for (i = num_vars - 1; i > -1; i--) {
	/* downwards, to always get most recent declaration/quantification
	 * of that variable
	 */
	if (lvar_names[i] == t->item || strcmp (lvar_names[i], t->item) == SAME) {
	  break;
	}
      }
      if (i == -1) {
	printf("\nundeclared variable %s in literal %s. check input files\n\n",t->item, n->atom->item);
	exit (1);
      }
      if (f->function != -1 && lvar_types[i] != gfunctions_args_type[f->function][m] &&
	  !is_subtype (lvar_types[i],gfunctions_args_type[f->function][m])) {
	printf("\ntype of var %s does not match type of arg %d of function %s\n\n",lvar_names[i], m, gfunctions[f->function]);
	exit (1);
      }
      f->args[m] = ENCODE_VAR (i);
    }
    else {
      if ((f->args[m] = position_in_constants_table (t->item)) == -1) {
	printf ("\nunknown constant %s in literal %s. check input files\n\n", t->item, n->atom->item);
	exit (1);
      }
      if (f->function != -1 && !gis_member[f->args[m]][gfunctions_args_type[f->function][m]]) {
	printf ("\ntype mismatch: constant %s as arg %d of %s. check input files\n\n",gconstants[f->args[m]], m, gfunctions[f->function]);
	exit (1);
      }
    }
    m++;
  }
  if (f->function == -1) {
    if (m != 2) {
      printf("\nfound eq - function with %d arguments. check input files\n\n",m);
      exit (1);
    }
  }
  else {
    if (m != gfunarity[f->function]) {
      printf("\nfunction %s is declared to have %d (not %d) arguments. check input files\n\n", gfunctions[f->function], gfunarity[f->function], m);
      exit (1);
    }
  }
}


void make_VarAssign (NumVar * f, PlNode * n, int num_vars)
{
  if (n->connective != EQUAL_CONN) {
    /* can't happen after previous syntax check. Oh well, whatever...
     */
    printf ("\nillegal (empty) atom used in domain. check input files\n\n");
    exit (1);
  }

  if (n->connective == EQUAL_CONN) {
    /*	xxx qui devo inventarmi qualcosa.-... :)*/
    make_NumVar (f, n->sons, num_vars);
    f->value = evaluate_exp (n->sons->next);
  } 
}

void make_compvar (CompositeNumVar * c, int c_index, NumVar * nv, int nv_index)
{
  /* tipo VARIABLE (grandezza principale) */
  c->operator = VARIABLE_OP;
  /*solo il primo operatore e' significativo e indica il valore nella tabella delle grandezze principali */
  c->first_op = nv_index;
  /*secondo op non significativo */
  c->second_op = -1;
  /*copio il valore dalla numvar */
  GCOMP_VAR_VALUE(c_index) = nv->value; // c->value = nv->value;
  /*salvo nella grandezza il principale il suo indice nell'array delle grandezze composte */
  nv->gcomp_var_index = c_index;
}



float evaluate_exp (PlNode * n)
{
  switch (n->connective) {
  case NUM_EXP:
    return evaluate_exp (n->sons);
  case ATOM:
    return atof (n->atom->item);
    break;
  case MUL_CONN:
    return evaluate_exp (n->sons) * evaluate_exp (n->sons->next);
    break;
  case DIV_CONN:
    return evaluate_exp (n->sons) / evaluate_exp (n->sons->next);
    break;
  case PLUS_CONN:
    return evaluate_exp (n->sons) + evaluate_exp (n->sons->next);
    break;
  case MINUS_CONN:
    return evaluate_exp (n->sons) - evaluate_exp (n->sons->next);
    break;
  case UMINUS_CONN:
    return -evaluate_exp (n->sons);
    break;
  default:
    printf("\nConnective %d not yet supported in expression evaluation\n\n",n->connective);
    exit (1);
    return -1;
    break;
  }
  return 0;
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Aggiunge un and iniziale agli effetti
			  degli operatori se questi non ne hanno
			  che utilizzano i fatti
	PARAMETER	: void
	RETURN		: void
-----------------------------------------------------------------
*/
void add_and_effect(PlOperator *operators)
{
	PlOperator	*o;
	PlNode		*sons;

	for (o = operators; o; o = o->next) {
		if (o->effects->connective != AND) {
			sons = o->effects;
			o->effects = new_PlNode(AND);
			o->effects->sons = sons;
		}
	}
}

void add_dummy_effects (PlOperator * operators)
{
  PlOperator *o;
  PlNode *e, *ef, *eff, *last;
  Bool t = FALSE;

  for (o = operators; o; o = o->next) {
    if (o->effects) {
      t = FALSE;
      last = NULL;

      ef = o->effects;
      if (ef->connective == AND)
	ef = ef->sons;
      for (e = ef; e; e = e->next) {
	if (!e->next)
	  last = e;
	eff = e;
	if ((eff->connective == AT_START_CONN) || (eff->connective == AT_END_CONN) || (eff->connective == OVER_ALL_CONN))
	  eff = eff->sons;
	if ((eff->connective == ATOM) || (eff->connective == NOT)) {
	  t = TRUE;
	  break;
	}
      }
      if (!t) {
	add_dummy (last);
      }
    }
  }
}


void add_dummy (PlNode * pln)
{
  if (!pln) {
    printf ("\n\nNull PLNODE!!!\n\n");
    exit (1);
  }
  pln->next = new_PlNode (ATOM);
  pln->next->atom = new_TokenList ();
  pln->next->atom->item = new_Token (strlen (DUMMY_PRED_STRING) + 1);
  strcpy (pln->next->atom->item, DUMMY_PRED_STRING);
  pln->next->atom->next = NULL;
}






PlNode *cp_PlNode (PlNode *pln)
{

  PlNode *result = (PlNode *) calloc (1, sizeof (PlNode));
  CHECK_PTR (result);

  result->connective =pln->connective ;


  result->atom = copy_TokenList(pln->atom );

  if(pln->sons != NULL)
  result->sons = cp_PlNode (pln->sons);
 if(pln->next != NULL)
  result->next = cp_PlNode (pln->next);

  return result;

}

void cp_PlNode2list (PlNode *pln, PlNode **list )
{
  PlNode *tmp;

  tmp=*list;
  *list=cp_PlNode (pln);
  (*list)->next=tmp;
}



NumVar *new_NumVar (void)
{

  NumVar *result = (NumVar *) calloc (1, sizeof (NumVar));
  CHECK_PTR (result);
  
  memset(result, 0, sizeof(NumVar));

  return result;

}

CompositeNumVar *new_CompositeNumVar (OPERATOR_TYPE op)
{

  CompositeNumVar *result = (CompositeNumVar *) calloc (1, sizeof (CompositeNumVar));
  CHECK_PTR (result);

  memset(result, 0, sizeof(CompositeNumVar));

  result->operator = op;

  result->in_metric = FALSE;

  return result;

}

SpecialFacts *
new_SpecialFacts (void)
{

  SpecialFacts *result = (SpecialFacts *) calloc (1, sizeof (SpecialFacts));
  CHECK_PTR (result);

  memset(result, 0, sizeof(SpecialFacts));

  return result;

}

IntList *new_IntList (void)
{

  IntList *result = (IntList *) calloc (1, sizeof (IntList));
  CHECK_PTR (result);

  memset(result, 0, sizeof(IntList));

  return result;

}



//in base alla metrica di valutazione del piano
void set_cost_and_time_coeffs (void)
{
  int father_cvar;

  //trovo il nodo padre della funzione total-time nelle cvar
  //assumo che total-time compaia una sola volta nella funzione di ottimizzazione
  if (gcomp_var[TOTAL_TIME_FUNCTION_INDEX].affects)
    {
      GpG.temporal_plan = TRUE;
      father_cvar = gcomp_var[TOTAL_TIME_FUNCTION_INDEX].affects->item;
    }

  else
    {
      GpG.orig_weight_time = 0.0;
      GpG.orig_weight_cost = 1.0;
      return;
    }

  //CALCOLO DI GpG.orig_weight_time
  //se il padre e' un '*', e l'altro coeff. e' un numero, questo e' il coefficiente cercato
  if (gcomp_var[father_cvar].operator == MUL_OP)
    {
      //se il primo fattore e' total time e il secondo e' un numero, il secondo e' il coeff. temporale cercato
      if ((gcomp_var[father_cvar].first_op == TOTAL_TIME_FUNCTION_INDEX) &&
	  (gcomp_var[gcomp_var[father_cvar].second_op].operator = FIX_NUMBER))
	{
	  GpG.orig_weight_time =GCOMP_VAR_VALUE(gcomp_var[father_cvar].second_op);
	  GpG.temporal_plan = TRUE;
	}
      //se il secondo fattore e' total-time e il primo e' un numero, allora il primo e' il coeff. temporale cercato
      else
	if ((gcomp_var[father_cvar].second_op == TOTAL_TIME_FUNCTION_INDEX) && (gcomp_var[gcomp_var[father_cvar].first_op].
	     operator = FIX_NUMBER))
	{
	  GpG.orig_weight_time =GCOMP_VAR_VALUE(gcomp_var[father_cvar].first_op);
	  GpG.temporal_plan = TRUE;
	}
      //se l'altro fattore non e' un numero, assegno 1 d'ufficio
      else
	{
	  GpG.orig_weight_time = 1;
	  GpG.temporal_plan = TRUE;
	}
    }
  //se non c'era niente che moltiplica MUL_OP, assegno 1
  else
    GpG.orig_weight_time = 1;

  //CALCOLO DI GpG.orig_weight_cost
  // risalgo di un nodo (solo se MUL_OP)
  if (gcomp_var[father_cvar].operator == MUL_OP)
    father_cvar = gcomp_var[father_cvar].affects->item;
  if (gcomp_var[father_cvar].operator == MINIMIZE_OP)
    GpG.orig_weight_cost = 0;
  else
    GpG.orig_weight_cost = 1;

  if (GpG.orig_weight_time != 1)
    GpG.temporal_plan = TRUE;

}



/**
 * SPLITTED ACTIONS
 **/
void create_new_split_precond(int start_ef, int end_ef) {

  int pos;

  if (gextended_ft_conn >= max_num_ftconn) {
    max_num_ftconn += MAX_EF_FT_INCREASE;
    gft_conn = (FtConn *)realloc(gft_conn, max_num_ftconn * sizeof(FtConn));
    memset(&gft_conn[gextended_ft_conn], 0, max_num_ftconn - gextended_ft_conn);
  }

  pos = gextended_ft_conn;
  gextended_ft_conn++;

  /* 
     Aggiungo un fatto fittizio agli effetti dell'azione start_ef. Questo fatto è 
     precondizione at-start ed effetto cancellante at-start dell'azione end_ef. 
  */
  gef_conn[start_ef].A[gef_conn[start_ef].num_A - 1] = 
    gef_conn[end_ef].PC[gef_conn[end_ef].num_PC - 1] = 
    gef_conn[end_ef].sf->D_start[gef_conn[end_ef].sf->num_D_start - 1] = pos;

  gft_conn[pos].num_PC = 1;
  gft_conn[pos].PC = (int *)calloc(gft_conn[pos].num_PC, sizeof(int));
  gft_conn[pos].PC[gft_conn[pos].num_PC - 1] = end_ef;
  gft_conn[pos].num_A = 1;
  gft_conn[pos].A = (int *)calloc(gft_conn[pos].num_A, sizeof(int));
  gft_conn[pos].num_D = 0;
  gft_conn[pos].A[gft_conn[pos].num_A - 1] = start_ef;
  gft_conn[pos].rand = MY_RANDOM % BIG_INT;
  gft_conn[pos].position = pos;
  gft_conn[pos].fact_type = IS_SPL_PREC;
  gft_conn[pos].tmd_facts_array = NULL;
  gft_conn[pos].num_tmd_facts_array = 0;

}

int insert_ef_in_efconn(EfConn *ef) {
  
  int i, j;
  int num_block;

  if (gextended_ef_conn >= max_num_efconn) {
    max_num_efconn += MAX_EF_FT_INCREASE;
    gef_conn = (EfConn *)realloc(gef_conn, max_num_efconn * sizeof(EfConn));
    memset(&gef_conn[gextended_ef_conn], 0, max_num_efconn - gextended_ef_conn);
  }

  ef->position = gextended_ef_conn;
  gef_conn[gextended_ef_conn++] = (*ef);
  create_descnumeff_of_efconn(gextended_ef_conn - 1);

  num_block = gextended_ef_block;
  gextended_ef_block = (gextended_ef_conn >> 5) + 1;

  if (gextended_ef_block > num_block)
    {
      if (GpG.numeric_actions)
	{
	  GpG.numeric_actions = (int *)realloc(GpG.numeric_actions, gextended_ef_block * sizeof(int));
	  memset(&GpG.numeric_actions[num_block], 0, (gextended_ef_block - num_block) * sizeof(int)); 
	}
    }

  i = ef->position;
  //Verifica se ci sono precondizioni nmeriche
  for (j = 0; j < gef_conn[i].num_PC; j++)
    if (gef_conn[i].PC[j] < 0) {
      gef_conn[i].is_numeric = TRUE;
      SET_BIT(GpG.numeric_actions, i);
      gef_conn[i].has_numeric_precs = TRUE;
      return (gextended_ef_conn - 1);
    }

  //Verifica se ci sono effetti numerici
  if (gef_conn[i].num_numeric_effects > 0) {
    gef_conn[i].is_numeric = TRUE;
    SET_BIT(GpG.numeric_actions, i);
    return (gextended_ef_conn - 1);
  }
  
  //Verifica odd cond & effects(pc_overall,pc_end,A_start)
  if (gef_conn[i].sf)
    {
      //Verifica se ci sono precondizioni overall nmeriche
      for (j = 0; j < gef_conn[i].sf->num_PC_overall; j++)
	if (gef_conn[i].sf->PC_overall[j] < 0) {
	  gef_conn[i].is_numeric = TRUE;
	  SET_BIT(GpG.numeric_actions, i);
	  gef_conn[i].has_numeric_precs = TRUE;
	  return (gextended_ef_conn - 1);
	}
      //Verifica se ci sono precondizioni at end nmeriche
      for (j = 0; j < gef_conn[i].sf->num_PC_end; j++)
	if (gef_conn[i].sf->PC_end[j] < 0) {
	  gef_conn[i].is_numeric = TRUE;
	  SET_BIT(GpG.numeric_actions, i);
	  gef_conn[i].has_numeric_precs = TRUE;
	  return (gextended_ef_conn - 1);
	}
    }
  
  return (gextended_ef_conn - 1);
}

void split_ef_conn(int act_pos) {

  EfConn ef;
  int prova=0;

  if (DEBUG1)
    printf("\n\nSPLIT (%d) %s", act_pos, print_op_name_string(act_pos, temp_name));

  GpG.splitted_actions = TRUE;

  gef_conn[act_pos].act_type = SPLITTED_ACTION;

  // Componente at-start
  memset(&ef, 0, sizeof(EfConn));
  ef.num_PC = gef_conn[act_pos].num_PC;
  ef.PC = gef_conn[act_pos].PC;

  ef.num_A = gef_conn[act_pos].sf->num_A_start + 1;
  ef.A = (int *)calloc(ef.num_A, sizeof(int));
  memcpy(ef.A, gef_conn[act_pos].sf->A_start, gef_conn[act_pos].sf->num_A_start * sizeof(int));

  ef.num_D = gef_conn[act_pos].sf->num_D_start;
  ef.D = gef_conn[act_pos].sf->D_start;

  ef.act_type = START_SPLITTED;
  ef.op = act_pos;
  ef.plop = gef_conn[act_pos].plop;
  ef.start_ef = ef.end_ef = -1;
  ef.timed_PC = NULL;

  prova = insert_ef_in_efconn(&ef);
  gef_conn[act_pos].start_ef = prova;

  //Componente at-end
  memset(&ef, 0, sizeof(EfConn));
  ef.num_PC = 1;
  ef.PC = (int *)calloc(ef.num_PC, sizeof(int));
  ef.sf = (SpecialFacts *)calloc(1, sizeof(SpecialFacts));
  ef.num_A = gef_conn[act_pos].num_A;
  ef.A = gef_conn[act_pos].A;
  ef.sf->num_PC_end = gef_conn[act_pos].sf->num_PC_end;
  ef.sf->PC_end = gef_conn[act_pos].sf->PC_end;
  ef.sf->num_PC_overall = gef_conn[act_pos].sf->num_PC_overall;
  ef.sf->PC_overall = gef_conn[act_pos].sf->PC_overall;
  ef.num_D = gef_conn[act_pos].num_D;
  ef.D = gef_conn[act_pos].D;
  ef.sf->num_D_start = 1;
  ef.sf->D_start = (int *)calloc(ef.sf->num_D_start, sizeof(int));

  ef.duration = gef_conn[act_pos].duration;
  ef.dur_var_index = gef_conn[act_pos].dur_var_index;
  ef.duration_rvals = gef_conn[act_pos].duration_rvals;
  ef.num_duration_rvals =  gef_conn[act_pos].num_duration_rvals;
  ef.act_type = END_SPLITTED;
  ef.op = act_pos;
  ef.plop = gef_conn[act_pos].plop;
  ef.start_ef = ef.end_ef = -1;
  ef.timed_PC = NULL;

  prova = insert_ef_in_efconn(&ef);
  gef_conn[act_pos].end_ef = prova;


  create_new_split_precond(gef_conn[act_pos].start_ef, gef_conn[act_pos].end_ef);

  if (DEBUG1) {
    printf("\n  into: START %d END %d", gef_conn[act_pos].start_ef, gef_conn[act_pos].end_ef);
  }

}


void split_actions( void ) {

  int i, j, k;
  
  max_num_efconn = gnum_ef_conn;
  gextended_ef_conn = gnum_ef_conn;
  gextended_ef_block = gnum_ef_block;

  for (i = 0; i < gnum_ef_conn; i++) {
    if (gef_conn[i].sf) {

      for (j = 0; j < gef_conn[i].sf->num_A_start; j++) 
	if (is_fact_in_delete_effects(i, gef_conn[i].sf->A_start[j])
	    && (gft_conn[gef_conn[i].sf->A_start[j]].num_PC > 0)) {
	  split_ef_conn(i);
	  // goto next action
	  break;
	}
	
      if (!gef_conn[i].is_numeric)
	continue;

      for (j = 0; j < gef_conn[i].num_numeric_effects - 1; j++) {
	for (k = j + 1; k < gef_conn[i].num_numeric_effects; k++) {

	  if ((gef_conn[i].numeric_effects[j].lval 
	       == gef_conn[i].numeric_effects[k].lval)
	      && (gef_conn[i].numeric_effects[j].is_at_start 
		  != gef_conn[i].numeric_effects[k].is_at_start)) {
	    split_ef_conn(i);
	    break;
	  }
	}
	// goto next action
	if (k < gef_conn[i].num_numeric_effects)
	  break;
      }
    }
  }
}



/*
 * Aggiunge alle strutture ft_conn gli indici delle azioni
 * che erano state saltate perchè contraddittorie
 */
void add_suspected_ef_conns_effects( void )
{

  int i, j, el;

  for ( i = gfirst_suspected_ef_conn; i < gnum_ef_conn; i++ ) {

#ifdef __TEST__        
    printf("\n\nUpdating effects of %s", print_op_name_string(i, temp_name));
#endif

    /*
     * Precondizioni at start
     */
    for (j = 0; j < gef_conn[i].num_PC; j++) 
      {

	el = gef_conn[i].PC[j];
	
	if (el < 0)
	  continue;

	gft_conn[el].PC[gft_conn[el].num_PC++] = i;
      }
   

    /*
     *  Effetti cancellanti at end
     */
    for (j = 0; j < gef_conn[i].num_D; j++) 
      {

	el = gef_conn[i].D[j];

	if (el < 0)
	  continue;

	gft_conn[el].D[gft_conn[el].num_D++] = i;
      }


    /* 
     * Azioni durative
     */
    if (gef_conn[i].sf)
      {


	/*
	 * Precondizioni overall
	 */
	for ( j = 0; j < gef_conn[i].sf->num_PC_overall; j++ ) 
	  {

	    el = gef_conn[i].sf->PC_overall[j];

	    if (el < 0)
	      continue;
	    
	    gft_conn[el].PC[gft_conn[el].num_PC++] = i;
	  }


	/*
	 * Precondizioni at end
	 */
	for ( j = 0; j < gef_conn[i].sf->num_PC_end; j++ ) 
	  {

	    el = gef_conn[i].sf->PC_end[j];

	    if (el < 0)
	      continue;
	    
	    gft_conn[el].PC[gft_conn[el].num_PC++] = i;
	  }
	

	/*
	 * Effetti additivi at start
	 */
	for ( j = 0; j < gef_conn[i].sf->num_A_start; j++ ) 
	  {

	    el = gef_conn[i].sf->A_start[j];

	    if (el < 0)
	      continue;
	
	    if (is_fact_in_preconditions(i, gef_conn[i].sf->A_start[j])
		|| is_fact_in_preconditions_overall(i, gef_conn[i].sf->A_start[j]))
	      continue;
	    
	    gft_conn[el].A[gft_conn[el].num_A++] = i;
	  }


	/*
	 * Effetti cancellanti at start
	 */
	for ( j = 0; j < gef_conn[i].sf->num_D_start; j++ ) 
	  {
	    
	    el = gef_conn[i].sf->D_start[j];
	      
	      if (el < 0)
		continue;
	    
	    gft_conn[el].D[gft_conn[el].num_D++] = i;
	  }
	
      }


    /*
     * Effetti additivi at end
     */
    for (j = 0; j < gef_conn[i].num_A; j++) 
      {
	
	el = gef_conn[i].A[j];
	
	if (el < 0)
	  continue;
      
	if (!GpG.non_strips_domain)
	  {
	    if (is_fact_in_preconditions(i, gef_conn[i].A[j]))
	      continue;
	  }
	else
	  {
	    if (is_fact_in_preconditions_overall(i, gef_conn[i].A[j])
		|| is_fact_in_preconditions_end(i, gef_conn[i].A[j]))
	      continue;
	  }
	
	gft_conn[el].A[gft_conn[el].num_A++] = i;
      }
 
  }

  /*
   * Rievaluate numeric effects and preconds 
   */
  add_composite_vars (gfirst_suspected_ef_conn, gnum_ef_conn);
  set_numeric_flag();
  propagate_inertias();

#ifdef __TEST__
  for (i = 0; i < gnum_ef_conn; i++)
    {
      for (j = 0; j < gef_conn[i].num_A; j++)
	{
	  int k;

	  for (k = 0; k < gft_conn[gef_conn[i].A[j]].num_A; k++)
	    {
	      if (gft_conn[gef_conn[i].A[j]].A[k] == i)
		break;
	    }
	  
	  if (k == gft_conn[gef_conn[i].A[j]].num_A)
	    {
	      printf("\n\nERROR : fact %d <-> action %d ", gef_conn[i].A[j], i);
	      print_ft_name(gef_conn[i].A[j]);
	      printf(" <->");
	      print_op_name(i);
	    }
	}
    }
#endif

}
