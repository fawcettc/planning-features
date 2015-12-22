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
 * File: numeric.c
 * Description: Numeric values manager for the LPG planner.
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/



#include <math.h>
#include "lpg.h"
#include "numeric.h"
#include "utilities.h"
#include "LpgOutput.h"
#include "inst_utils.h"
#include "H_relaxed.h"
#include "LocalSearch.h"
#include "ActionSubgraph.h"
#include "LpgTime.h"
#include "ComputeReachInf.h"
#include "memory.h"
#include "mutex.h"


//#define __TEST_MIXED__
int is_var_in_prec_cvar(int var, int cvar_index) {

  if ( cvar_index < 0 )
    cvar_index *= -1;

  if (var < 0) {
    if (DEBUG1)
      printf("\nWarning : negative var indexes passed to is_var_in_prec_cvar");
    return FALSE;
  }

  switch (gcomp_var[cvar_index].operator)
    {
    case UMINUS_OP:
      return is_var_in_prec_cvar(var, gcomp_var[cvar_index].first_op);
    case MUL_OP:
    case DIV_OP:
    case MINUS_OP:
    case PLUS_OP:
    case EQUAL_OP:
    case GREATER_THAN_OP:
    case GREATER_OR_EQUAL_OP:
    case LESS_THAN_OP:
    case LESS_THAN_OR_EQUAL_OP:
      return (is_var_in_prec_cvar(var, gcomp_var[cvar_index].first_op) || is_var_in_prec_cvar(var, gcomp_var[cvar_index].second_op));
    case VARIABLE_OP:
      return (gcomp_var[cvar_index].first_op == var);
    case FIX_NUMBER:
      return FALSE;
    default:
      if (DEBUG1) 
	printf ("\n\nwrong cvar [%d] : found operator %d \n\n", cvar_index, gcomp_var[cvar_index].operator);      
      return FALSE;
    }
}




int is_var_in_eff_cvar(int var, int cvar_index) {

  if ( cvar_index < 0 )
    cvar_index *= -1;

  if (var < 0) {
    if (DEBUG1)
      printf("\nWarning : negative var indexes passed to is_var_in_eff_cvar");
    return FALSE;
  }

  switch (gcomp_var_effects[cvar_index].operator)
    {
    case INCREASE_CONN:
    case DECREASE_CONN:
    case ASSIGN_CONN:
    case SCALE_UP_CONN:
    case SCALE_DOWN_CONN:
      return (is_var_in_prec_cvar(var, gcomp_var[cvar_index].first_op) || is_var_in_prec_cvar(var, gcomp_var[cvar_index].second_op));
    default:
      if (DEBUG1) 
	printf ("\n\nwrong cvar [%d] : found operator %d \n\n", cvar_index, gcomp_var_effects[cvar_index].operator);      
      return FALSE;
    }
}



void sub_affects_list (int cv_index, int *bitarray)
{
  IntList *il;
  RESET_BIT (bitarray, cv_index);
  for (il = gcomp_var[cv_index].affects; il; il = il->next)
    {
      if(GET_BIT(bitarray, il->item))
	{
	  RESET_BIT (bitarray, il->item);
	  sub_affects_list(il->item,bitarray);	
	}
    }
}



//aggiunge la affect list della cvar che ho ricalcolato al bit array delle cvar modificate
void add_affects_list (int cv_index, int *bitarray)
{
  IntList *il;
  SET_BIT (bitarray, cv_index);
  for (il = gcomp_var[cv_index].affects; il; il = il->next)
    /* if(!GET_BIT(bitarray, il->item)) */
    {
      SET_BIT (bitarray, il->item);
      add_affects_list(il->item,bitarray);
      
    }
}


//inserisce le cvar dinamiche tra gli rvals diquesto effetto numerico (PRIMARIE O COMPOSTE)
void search_for_dynamic_vals_in_exp (int cvar_ind, DescNumEff * descnumeff)
{
  CompositeNumVar *cv;
  //puntatore all'oggetto cvar
  cv = &gcomp_var[cvar_ind];

  //se il primo operando ha un indice valido (!=-1) ed e' dinamico, inseriscilo e visita il sottoalbero
  if ((cv->first_op != -1) && (!GET_BIT (gis_inertial, cv->first_op)))
    {
      //inserimento 
      descnumeff->rvals[descnumeff->num_rvals++] = cv->first_op;
      if (descnumeff->num_rvals >= MAX_R_VALS)
	{
	  printf ("\n\nMax number of Rvals reached; increase max_r_vals\n\n");
	  exit (1);
	}

      if (cvar_ind != cv->first_op)
	search_for_dynamic_vals_in_exp (cv->first_op, descnumeff);   }
  //operazione analoga per il secondo operando 
  if ((cv->second_op != -1) && (!GET_BIT (gis_inertial, cv->second_op)))
    {
      //inserimento
      descnumeff->rvals[descnumeff->num_rvals++] = cv->second_op;
      if (descnumeff->num_rvals >= MAX_R_VALS)
	{
	  printf ("\n\nMax number of Rvals reached; increase max_r_vals\n\n");
	  exit (1);
	}

      if (cvar_ind != cv->second_op)
	search_for_dynamic_vals_in_exp (cv->second_op, descnumeff);
    }
  //la terminazione e' garantita in quanto le variabili primarie hanno indice -1
}

//compila il nod descnumeff richiesto
void create_descnum_for_numeff_of (DescNumEff * descnumeff, int cvar_index,
			      int ef_conn, Bool is_at_start)
{
  CompositeNumVar *cv;
  //puntatore all'oggetto cvar
  cv = &gcomp_var_effects[-cvar_index];
  //salva nel descrittore l'indice della regola
  descnumeff->index = -cvar_index;
  //salva l' l-value
  descnumeff->lval = cv->first_op;
  //Bool che indica se l'effetto si verifica at-start o at-end
  descnumeff->is_at_start = is_at_start;
  //salva nell'array tutti gli rvals dinamici che compaiono a destra dell'uguale
  search_for_dynamic_vals_in_exp (cv->second_op, descnumeff);
}


//crea la descrizione dell'effetto numerico numero index
void create_descnumeff_of_efconn (int index)
{
  int ef;
  int num_numeric_effects = 0;
  int n_ef = 0;
  //conta gli effetti numerici dell'efconn
  //  conta effetti at end

  for (ef = 0; ef < gef_conn[index].num_A; ef++)
    //minore di zero indica che si tratta di un effetto numerico
    if (gef_conn[index].A[ef] < 0)
      num_numeric_effects++;
  //  conta effetti at start
  if (gef_conn[index].sf)
    for (ef = 0; ef < gef_conn[index].sf->num_A_start; ef++)
      //minore di zero indica che si tratta di un effetto numerico
      if (gef_conn[index].sf->A_start[ef] < 0)
	num_numeric_effects++;
  //salva il numero nella struttura gef_conn
  gef_conn[index].num_numeric_effects = num_numeric_effects;
  //se non ci sono effetti numerici ho finito
  if (num_numeric_effects == 0)
    return;
  //alloca se necessario lo spazio per i singoli descrittori  
  gef_conn[index].numeric_effects =
    (DescNumEff *) calloc (num_numeric_effects, sizeof (DescNumEff));

  //crea il descrittore per tutti gli effetti numerici
  for (ef = 0; ef < gef_conn[index].num_A; ef++)
    if (gef_conn[index].A[ef] < 0)
      create_descnum_for_numeff_of (&gef_conn[index].numeric_effects[n_ef++],
				    gef_conn[index].A[ef], index, FALSE);
  if (gef_conn[index].sf)
    for (ef = 0; ef < gef_conn[index].sf->num_A_start; ef++)
      if (gef_conn[index].sf->A_start[ef] < 0)
	create_descnum_for_numeff_of (&gef_conn[index].numeric_effects[n_ef++],gef_conn[index].sf->A_start[ef], index,TRUE);

  GpG.num_numeric_effects += gef_conn[index].num_numeric_effects;
  
}

//compila il campo numeric_effects di ciascuno degli efconn
void create_descnumeff_of_efconns (void)
{
  int i;
  //questa funzione crea direttamente la descrizione per tutte le azioni
  //in alternativa si puo' decidere di chiamare la create_descnumeff_of_efconn solo al
  //momento di inserire nel piano per la prima volta quella azione
  for (i = 0; i < gnum_ef_conn; i++)
    create_descnumeff_of_efconn (i);
}



//in base all'effetto applicato setto quale variabile ha cambiato valore
//fatto per INCAPSULARE i DATI
void set_modified_var (int act_pos, int level, int num_eff)
{
  //setto un array diverso secondo il flag is_at_start
  if (gef_conn[act_pos].numeric_effects[num_eff].is_at_start)
    {
      if(!GET_BIT (vectlevel[level]->numeric->modified_vars_start, gef_conn[act_pos].numeric_effects[num_eff].lval))
	{
	  SET_BIT (vectlevel[level]->numeric->modified_vars_start, gef_conn[act_pos].numeric_effects[num_eff].lval);
	  add_affects_list( gef_conn[act_pos].numeric_effects[num_eff].lval,vectlevel[level]->numeric->modified_vars_start);
	}
      
    }
  else
    {
      if(!GET_BIT (vectlevel[level]->numeric->modified_vars_end, gef_conn[act_pos].numeric_effects[num_eff].lval))
	{  
	  add_affects_list( gef_conn[act_pos].numeric_effects[num_eff].lval,vectlevel[level]->numeric->modified_vars_end);
	  SET_BIT (vectlevel[level]->numeric->modified_vars_end, gef_conn[act_pos].numeric_effects[num_eff].lval);
	}
    }
}

//applica l'effetto numerico i-esimo
void apply_numeric_effect_at_end (int act_pos, int level, int num_eff)
{
  DescNumEff *numeric_effect;
  int num_numeric_effs;

  //preliminari
  numeric_effect = &gef_conn[act_pos].numeric_effects[num_eff];
  num_numeric_effs = gef_conn[act_pos].num_numeric_effects;
  //1a. applico gli effetti numerici aggiornando direttamente i valori del livello level+1
  eval_comp_var_non_recursive_effects (
				//regola da applicare
				numeric_effect->index,
				//valori di ingresso,
				vectlevel[level+1]->numeric->values,
				//valori di uscita
				vectlevel[level + 1]->numeric->values,
				level, level + 1);
  //1b. setto cosa e' cambiato nell'array modified_vars_end(o start)
  //era level, messo level+1
  set_modified_var (act_pos, level + 1, num_eff);
}


void
apply_numeric_effect_at_start1  (int act_pos, int level, int num_eff)
{
  DescNumEff *numeric_effect;
  int num_numeric_effs;

  //preliminari
  numeric_effect = &gef_conn[act_pos].numeric_effects[num_eff];
  num_numeric_effs = gef_conn[act_pos].num_numeric_effects;

  vectlevel[level]->effect_at_start_present = TRUE;

  //1a. applico gli effetti numerici aggiornando direttamente i valori del livello level+1
  eval_comp_var_non_recursive_effects (
				//regola da applicare
				numeric_effect->index,
				//valori di ingresso,
				vectlevel[level]->numeric->values,
				//valori di uscita
				vectlevel[level]->numeric->values_after_start,
				level, level);

  memcpy (vectlevel[level + 1]->numeric->values,
	  vectlevel[level]->numeric->values_after_start,
	  gnum_comp_var * sizeof (float));
  refresh_cvars (level + 1);
  //1b. setto cosa e' cambiato nell'array modified_vars_end(o start)
  set_modified_var (act_pos, level + 1, num_eff);

//ENDLAZZA
}



void
apply_numeric_effect_at_start(int act_pos, int level, int num_eff)
{
  DescNumEff *numeric_effect;
  int num_numeric_effs;

  //preliminari
  numeric_effect = &gef_conn[act_pos].numeric_effects[num_eff];
  num_numeric_effs = gef_conn[act_pos].num_numeric_effects;

  vectlevel[level]->effect_at_start_present = TRUE;

  //1a. applico gli effetti numerici aggiornando direttamente i valori del livello level+1
  eval_comp_var_non_recursive_effects (
				//regola da applicare
				numeric_effect->index,
				//valori di ingresso,
				vectlevel[level]->numeric->values,
				//valori di uscita
				vectlevel[level]->numeric->values_after_start,
				level, level);  
  
  set_modified_var (act_pos, level, num_eff);
  //1b. setto cosa e' cambiato nell'array modified_vars_end(o start)
  set_modified_var (act_pos, level + 1, num_eff);
//ENDLAZZA
}



//setta a 1 tutti i bit dell'array used_vars che corrispondono ad una var modificata da uno degli effetti
void set_usedvars_array (int act_pos, int level)
{
  int i, j;
  DescNumEff *numeric_effs;
  int num_numeric_effs;
  int *usedvars = vectlevel[level]->numeric->used_vars;

  //preliminari
  numeric_effs = gef_conn[act_pos].numeric_effects;
  num_numeric_effs = gef_conn[act_pos].num_numeric_effects;
  //se ci sono effetti numerici
  if (numeric_effs)
    //allora per ciascuno di essi
    for (i = 0; i < num_numeric_effs; i++)
      //metti un 1 per ciascuno dei suoi rvals
      for (j = 0; j < numeric_effs[i].num_rvals; j++)
	SET_BIT (usedvars, numeric_effs[i].rvals[j]);
}


//applica gli effetti numerici di un'azione
void
apply_numeric_effects_of_action (int act_pos, int level)
{
  int i;
  DescNumEff *numeric_effs;
  int num_numeric_effs;
  Bool at_start_effs = FALSE;

  //preliminari
  assert (0 <= act_pos);
  assert (act_pos < gnum_ef_conn);
  assert (0 <= level);
  assert (level < GpG.curr_plan_length);
  assert (vectlevel[level]);
  assert (vectlevel[level]->numeric);

  //azzero array fatti da inserire/rimuovere
  insert_values_unsup_num_fact (0, -1, -1);


  numeric_effs = gef_conn[act_pos].numeric_effects;
  num_numeric_effs = gef_conn[act_pos].num_numeric_effects;
  //0. Aggiorna il bit array used_vars del livello  
  set_usedvars_array (act_pos, level);
  //1. Per ciascuno degli effetti numerici dell'azione act_pos    
  memset(vectlevel[level+1]->numeric->modified_vars_start,0,gnum_block_compvar*sizeof(int));
  memset(vectlevel[level+1]->numeric->modified_vars_end,0,gnum_block_compvar*sizeof(int));

  if (numeric_effs)
    {

      for (i = 0; i < num_numeric_effs; i++)
	if (numeric_effs[i].is_at_start) {
	  apply_numeric_effect_at_start (act_pos, level, i);
	  apply_numeric_effect_at_end (act_pos, level, i);
	  at_start_effs = TRUE;
	}
     
      if (at_start_effs)
	// Aggiorno solo le grandezze modificate at_start  
	refresh_cvars_at_start (level);
     
      for (i = 0; i < num_numeric_effs; i++)
	if (!numeric_effs[i].is_at_start) 
	  apply_numeric_effect_at_end (act_pos, level, i);

      //2. ricalcola tutte le grandezze del livello level+1 che dipendono da grandezze che hanno subito modifiche
      refresh_cvars (level + 1);
      // propagazione dal livello after start al livello successivo
      //richiama la propagazione dei valori da variare da questo livello in poi
      propagate_cvars (level + 1, GpG.curr_plan_length);
      //control_numeric_of_plan();
      // printf("APPLY\n");




    }
  
  //lancia inserimento/rimozione fatti numerici da array unsup_num_fact
  insert_values_unsup_num_fact (2, -1, -1);
}



//rimuove gli effetti numerici di un'azione
void
remove_numeric_effects_of_action (int act_pos, int level)
{
  int l1;
  DescNumEff *numeric_effs;
  int num_numeric_effs;

  //preliminari
  assert (0 <= act_pos);
  assert (act_pos < gnum_ef_conn);
  assert (0 <= level);
  assert (level < GpG.curr_plan_length);
  assert (vectlevel[level]);
  assert (vectlevel[level]->numeric);

  //azzero array fatti da inserire/rimuovere
  insert_values_unsup_num_fact (0, -1, -1);

  l1 = level + 1;
  numeric_effs = gef_conn[act_pos].numeric_effects;
  num_numeric_effs = gef_conn[act_pos].num_numeric_effects;
  
    memset (vectlevel[level]->numeric->used_vars, 0,  sizeof (int) * gnum_block_compvar);
    memset (vectlevel[level+1]->numeric->modified_vars_start, 0,  sizeof (int) * gnum_block_compvar);
    memset (vectlevel[level+1]->numeric->modified_vars_end, 0,   sizeof (int) * gnum_block_compvar);
    memcpy (vectlevel[level + 1]->numeric->values_after_start, vectlevel[level]->numeric->values_after_start, gnum_comp_var * sizeof (float));

  //1. Per ciascuno degli effetti numerici dell'azione act_pos    
   if (numeric_effs)
    {
      //      vectlevel[level]->effect_at_start_present = FALSE;
      //Copia valori numerici dal level al level+1
      //printf("REMOVE\n");
      copy_num_values_from_level_to_level (level, l1, TRUE);
      // propagazione dei valori da variare da questo livello in poi
      propagate_cvars (level+1, GpG.curr_plan_length);
      //control_numeric_of_plan();
      // memcpy (vectlevel[level+1]->numeric->modified_vars_start,vectlevel[level]->numeric->modified_vars_start ,  sizeof (int) * gnum_block_compvar);
      //memcpy (vectlevel[level+1]->numeric->modified_vars_end, vectlevel[level]->numeric->modified_vars_end,   sizeof (int) * gnum_block_compvar);

    }
   

   
 
  //lancia inserimento/rimozione fatti numerici da array unsup_num_fact
  insert_values_unsup_num_fact (2, -1, -1);
  
  
}



void eval_comp_var_non_recursive (int cv_index, float *in_vect, float *out_vect, int in_level, int out_level)
{
  int first_op = gcomp_var[cv_index].first_op;
  int second_op = gcomp_var[cv_index].second_op;
  float old_value;

  //versione non ricorsiva della eval_comp_var
  switch (gcomp_var[cv_index].operator)
    {
    case INCREASE_OP:
      out_vect[first_op] = in_vect[first_op] + in_vect[second_op];
      MSG_ERROR("OPERATORE ERRATO");
      break;
    case DECREASE_OP:
      out_vect[first_op] = in_vect[first_op] - in_vect[second_op];
      MSG_ERROR("OPERATORE ERRATO");
      break;
    case SCALE_UP_OP:
      out_vect[first_op] = in_vect[first_op] * in_vect[second_op];
      MSG_ERROR("OPERATORE ERRATO");
      break;
    case SCALE_DOWN_OP:
      out_vect[first_op] = in_vect[first_op] / in_vect[second_op];
      MSG_ERROR("OPERATORE ERRATO");
      break;
    case ASSIGN_OP:
      out_vect[first_op] = in_vect[second_op];
      MSG_ERROR("OPEREATORE ERRATO");
      break;
    case MUL_OP:
      out_vect[cv_index] = in_vect[first_op] * in_vect[second_op];
      break;
    case DIV_OP:
      out_vect[cv_index] = in_vect[first_op] / in_vect[second_op];
      break;
    case PLUS_OP:
      out_vect[cv_index] = in_vect[first_op] + in_vect[second_op];
      break;
    case MINUS_OP:
      out_vect[cv_index] = in_vect[first_op] - in_vect[second_op];
      break;
    case UMINUS_OP:
      out_vect[cv_index] = -in_vect[first_op];
      break;
    case LESS_THAN_OP:
      old_value = in_vect[cv_index];
      //old_value = vectlevel[in_level-1]->numeric->values[cv_index];
      out_vect[cv_index] = (float) (in_vect[first_op] < in_vect[second_op]);
      //Da vero a falso
      if ((old_value > 0.5) && (out_vect[cv_index] < 0.5))
	{
#ifdef _TEST_NUM_PREC_
	  printf ("\nConfronto: (liv.%d)", out_level);
	  print_cvar_tree (cv_index, out_level);
	  printf (" da vero a falso");
#endif
	  insert_values_unsup_num_fact (1, cv_index, out_level);

	}

      //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
      if ((old_value < 0.5) && (out_vect[cv_index] > 0.5))
	{
#ifdef _TEST_NUM_PREC_
	  printf ("\nConfronto: (liv.%d)", out_level);
	  print_cvar_tree (cv_index, out_level);
	  printf (" DA FALSO A VERO");
#endif
	  insert_values_unsup_num_fact (1, cv_index, out_level);
	}
      break;
    case LESS_THAN_OR_EQUAL_OP:
      old_value = in_vect[cv_index];
      //old_value =   vectlevel[in_level-1]->numeric->values[cv_index];
      out_vect[cv_index] = (float) (in_vect[first_op] <= in_vect[second_op]);
      //Da vero a falso
      if ((old_value > 0.5) && (out_vect[cv_index] < 0.5))
	{
#ifdef _TEST_NUM_PREC_
	  printf ("\nConfronto: (liv.%d)", out_level);
	  print_cvar_tree (cv_index, out_level);
	  printf (" da vero a falso");
#endif
	  insert_values_unsup_num_fact (1, cv_index, out_level);
	}

      //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
      if ((old_value < 0.5) && (out_vect[cv_index] > 0.5))
	{
#ifdef _TEST_NUM_PREC_
	  printf ("\nConfronto: (liv.%d)", out_level);
	  print_cvar_tree (cv_index, out_level);
	  printf (" DA FALSO A VERO");
#endif
	  insert_values_unsup_num_fact (1, cv_index, out_level);
	}
      break;
    case EQUAL_OP:
      old_value = in_vect[cv_index];
      //old_value =  vectlevel[in_level-1]->numeric->values[cv_index];
      out_vect[cv_index] =
	(float) (in_vect[first_op] - in_vect[second_op]) <= MAX_APPROX;
      //Da vero a falso
      if ((old_value > 0.5) && (out_vect[cv_index] < 0.5))
	{
#ifdef _TEST_NUM_PREC_
	  printf ("\nConfronto: (liv.%d)", out_level);
	  print_cvar_tree (cv_index, out_level);
	  printf (" da vero a falso");
#endif
	  insert_values_unsup_num_fact (1, cv_index, out_level);

	}

      //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
      if ((old_value < 0.5) && (out_vect[cv_index] > 0.5))
	{
#ifdef _TEST_NUM_PREC_
	  printf ("\nConfronto: (liv.%d)", out_level);
	  print_cvar_tree (cv_index, out_level);
	  printf (" DA FALSO A VERO");
#endif
	  insert_values_unsup_num_fact (1, cv_index, out_level);
	}
      break;
    case GREATER_THAN_OP:
      old_value = in_vect[cv_index];
      //old_value = vectlevel[in_level-1]->numeric->values[cv_index] ;
      out_vect[cv_index] = (float) (in_vect[first_op] > in_vect[second_op]);
      //Da vero a falso
      if ((old_value > 0.5) && (out_vect[cv_index] < 0.5))
	{
#ifdef _TEST_NUM_PREC_
	  printf ("\nConfronto: (liv.%d)", out_level);
	  print_cvar_tree (cv_index, out_level);
	  printf (" da vero a falso");
#endif
	  insert_values_unsup_num_fact (1, cv_index, out_level);

	}

      //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
      if ((old_value < 0.5) && (out_vect[cv_index] > 0.5))
	{
#ifdef _TEST_NUM_PREC_
	  printf ("\nConfronto: (liv.%d)", out_level);
	  print_cvar_tree (cv_index, out_level);
	  printf (" DA FALSO A VERO");
#endif
	  insert_values_unsup_num_fact (1, cv_index, out_level);
	}
      break;
    case GREATER_OR_EQUAL_OP:
      old_value = in_vect[cv_index];
      //old_value = vectlevel[in_level-1]->numeric->values[cv_index] ;
      out_vect[cv_index] = (float) (in_vect[first_op] >= in_vect[second_op]);
      //Da vero a falso
      if ((old_value > 0.5) && (out_vect[cv_index] < 0.5))
	{
#ifdef _TEST_NUM_PREC_
	  printf ("\nConfronto: (liv.%d)", out_level);
	  print_cvar_tree (cv_index, out_level);
	  printf (" da vero a falso");
#endif
	  insert_values_unsup_num_fact (1, cv_index, out_level);

	}

      //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
      if ((old_value < 0.5) && (out_vect[cv_index] > 0.5))
	{
#ifdef _TEST_NUM_PREC_
	  printf ("\nConfronto: (liv.%d)", out_level);
	  print_cvar_tree (cv_index, out_level);
	  printf (" DA FALSO A VERO");
#endif
	  insert_values_unsup_num_fact (1, cv_index, out_level);
	}
      break;
    default:
      break;
    }
}



void refresh(float *values, int *modifieds, int level)
{
  int i;
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
	    
	    MSG_ERROR("PARTE NUMERICA ERRATA");
	    exit(0);
	    break;
	  case FIX_NUMBER:
	  case VARIABLE_OP:
	    break;
	  default:
	    eval_comp_var_non_recursive (i, values, values, level, level);
	    break;
	  }
      }
  reset_bitarray (modifieds, gnum_block_compvar);
}


//ricalcola le variabili derivate che e' necessario ricalcolare
void refresh_cvars(int level)
{
  int i;
  int *modifieds;
  //copia locale degli array modifieds
 
    modifieds = (int *) calloc (gnum_block_compvar, sizeof (int));
  //devo rinfrescare le variabili del livello level sulla base dell'array modified vars del livello level-1
  //intanto, se level=0, c'e' qualche problema, e lo segnalo
  if (level <= 0)
    {
      printf ("ERR: refresh_cvars(): level can't be <= 0");
      exit (1);
    }

  //che si tratti di un effetto end o uno start, appiattisco tutto su di unico array
  for (i = 0; i < gnum_block_compvar; i++)
    modifieds[i] = vectlevel[level]->numeric->modified_vars_start[i] | vectlevel[level]->numeric->modified_vars_end[i];
 
  refresh(vectlevel[level]->numeric->values, modifieds, level);
  
  free (modifieds);
}




//ricalcola le variabili derivate che e' necessario ricalcolare
void refresh_cvars_at_start (int level)
{
  int i;
  int *modifieds;
  //copia locale degli array modifieds
 
  modifieds = (int *) calloc (gnum_block_compvar, sizeof (int));
  //devo rinfrescare le variabili del livello level sulla base dell'array modified vars del livello level-1
  //intanto, se level=0, c'e' qualche problema, e lo segnalo
  if (level < 0)
    {
      printf ("ERR: refresh_cvars(): level can't be <= 0");
      exit (1);
    }

  //che si tratti di un effetto end o uno start, appiattisco tutto su di unico array
  for (i = 0; i < gnum_block_compvar; i++)
    modifieds[i] = vectlevel[level]->numeric->modified_vars_start[i];

  refresh(vectlevel[level]->numeric->values_after_start, modifieds, level);

  free (modifieds);
}



//tramite una singola passata, stabilisce quali sono gli effetti da applicare
Bool which_effects (int level, int *to_propagate, int *to_apply)
{
  int i, j;
  int action_pos = vectlevel[level]->action.position;
  Bool action_to_do;
  DescNumEff *num_eff;

  action_to_do=FALSE;

  for (i = 0; i < gef_conn[action_pos].num_numeric_effects; i++)
    {
      num_eff = &(gef_conn[action_pos].numeric_effects[i]);
      //se il lval di questo effetto e' da ricalcolare, segnala questo effetto come da ricalcolare
   
	  if ( GET_BIT(to_propagate,num_eff->lval))
	    {  
	      action_to_do=TRUE;
	      SET_BIT (to_apply, i);
	      add_affects_list(num_eff->lval,to_propagate);
	      
	    }
       
	
      //stessa cosa se uno degli rval e' da ricalcolare
      for (j = 0; j < num_eff->num_rvals; j++)
	{
	  if (GET_BIT (to_propagate, num_eff->rvals[j]))
	    {
	      SET_BIT (to_apply, i);
	      add_affects_list(num_eff->lval,to_propagate);
	      action_to_do=TRUE;
	      break;
	  }
	}
    }


  return action_to_do;

}

void eval_comp_var_non_recursive_effects (int cv_index, float *in_vect, float *out_vect, int in_level, int out_level)
{
  int first_op = gcomp_var_effects[cv_index].first_op;
  int second_op = gcomp_var_effects[cv_index].second_op;

  //versione non ricorsiva della eval_comp_var
  switch (gcomp_var_effects[cv_index].operator)
    {
    case INCREASE_OP:
      out_vect[first_op] = in_vect[first_op] + in_vect[second_op];
      break;
    case DECREASE_OP:
      out_vect[first_op] = in_vect[first_op] - in_vect[second_op];
      break;
    case SCALE_UP_OP:
      out_vect[first_op] = in_vect[first_op] * in_vect[second_op];
      break;
    case SCALE_DOWN_OP:      
      out_vect[first_op] = in_vect[first_op] / in_vect[second_op];
      break;
    case ASSIGN_OP:
      out_vect[first_op] = in_vect[second_op];
      break;
    default:
      MSG_ERROR("Parte numerica errata: OPERATORE");
      exit(0);
      break;
    }
  return;
}









void propagate_cvars (int level_from, int level_to)
{
  int level, i, ind,j;  
  int *to_be_applied;
  int *to_copy;
  int *modifieds;
  int action_pos;
  float dur_before = 0.0, dur_after, dur_act_follow, old_value;
  DescNumEff *numeric_effs;
  int num_numeric_effs;

  Bool action_to_do;
  Bool at_start_pres=FALSE;

  //check di validita' dei parametri
  if ((level_from < 0) || (level_to < 0) || (level_to < level_from))
    {
      printf ("\n\nIncorrect parameters\nlevel_from=%d; level_to=%d\n\n",
	      level_from, level_to);
      exit (1);
    }



  //  printf("Level_from: %d Level_to: %d\n\n", level_from, level_to);
  //alloca lo spazio per l'array di bit che usero' per i calcoli a bit
 
  

  modifieds = (int *) calloc (gnum_block_compvar, sizeof (int));
 
  //array di bit che indica se l'effetto e' da applicare o meno


  for(i=0;i<gnum_block_compvar;i++)
      modifieds[i]=vectlevel[level_from]->numeric->modified_vars_start[i] | vectlevel[level_from]->numeric->modified_vars_end[i];


  if(level_from==level_to)
    {
      for(i=0;i<gnum_comp_var;i++)
	if(GET_BIT(modifieds,i))
	  {
	    vectlevel[level_from]->numeric->values_after_start[i]=vectlevel[level_from]->numeric->values[i];
	    
	  }
      return;
    }
 
   to_copy = (int *) calloc (gnum_block_compvar, sizeof (int));
   to_be_applied = (int *) calloc (MAX_NUM_EFFS / 32 + 1, sizeof (int));

   memset(to_copy, 0,  gnum_block_compvar*sizeof(int));
   
   for (level = level_from; level < level_to; level = level++)
     {
      //se l'azione e' in corso di rimozione, mi fermo
      //serve per rimozioni a catena con remove_prec_act
      if (vectlevel[level]->action.being_removed)
	break;
      //indice dell'azione di questo livello
      action_pos = vectlevel[level]->action.position;
      if (action_pos < 0 )  //|| !(gef_conn[action_pos].is_numeric))
	{
	  memset(vectlevel[level+1]->numeric->modified_vars_start,0,gnum_block_compvar*sizeof(int));
	  memset(vectlevel[level+1]->numeric->modified_vars_end,0,gnum_block_compvar*sizeof(int));
	  copy_num_values_from_level_to_level (level, level + 1, TRUE);
	  for(i=0;i<gnum_block_compvar;i++)
	    modifieds[i]= modifieds[i] |( vectlevel[level+1]->numeric->modified_vars_start[i] | vectlevel[level+1]->numeric->modified_vars_end[i]);

	  continue;
	  
	}



      
      //preazzero array
      
      
      for (i = 0; i < gnum_block_compvar; i++)
	{
	  to_copy[i]=to_copy[i] | modifieds[i];
	}

    
      
      //prima propago tutti quelli da ricalcolare
      //1.come prima cosa devo determinare quali sono gli effetti da ricalcolare
      action_to_do=FALSE;
      at_start_pres=FALSE;
      memset(to_be_applied, 0,  (MAX_NUM_EFFS / 32 + 1)*sizeof(int));
      action_to_do=which_effects (level, to_copy ,to_be_applied);
      
      
      
#ifdef SAFER_BUT_SLOWER
      if (GET_ACTION_POSITION_OF_LEVEL (level)>=0 && CONVERT_ACTION_TO_VERTEX (GET_ACTION_POSITION_OF_LEVEL (level))->
	  duration_rvals != NULL)
	insert_propagation_list (GET_ACTION_OF_LEVEL (level));
#endif


      //guardo la durata dell'azione al livello dopo; se cambia, poi inseriro' in lista
      if (level < level_to - 1)
	if (GET_ACTION_POSITION_OF_LEVEL (level + 1)>=0 && 
	    CONVERT_ACTION_TO_VERTEX(GET_ACTION_POSITION_OF_LEVEL (level + 1))->duration_rvals !=NULL)
	  dur_before = get_action_time (vectlevel[level + 1]->action.position,
					level+1 );
      
      // pre_dur_before=dur_before;
      if(action_to_do)
	{
	  
	  numeric_effs = gef_conn[action_pos].numeric_effects;
	  num_numeric_effs = gef_conn[action_pos].num_numeric_effects;
	  if (num_numeric_effs<=0)
	    printf("ERROR");
	  //1. Per ciascuno degli effetti numerici dell'azione act_pos    
	  if (num_numeric_effs>0)
	    {
	      
	      for (i = 0; i < num_numeric_effs; i++)
		{
		  if (GET_BIT(to_be_applied,i) &&  ((gef_conn[action_pos].numeric_effects [i]).is_at_start))
		    {
		      if(!at_start_pres)
			for(j=0;j<gnum_comp_var;j++)
			  if(GET_BIT(to_copy,j))
			    {
			      vectlevel[level]->numeric->values_after_start[j]=vectlevel[level]->numeric->values[j];
			      
			    } 		
		      
		      apply_numeric_effect_at_start (action_pos, level, i);
		      
		      SET_BIT(modifieds,((&(gef_conn[action_pos].numeric_effects[i])))->lval);
		      add_affects_list((&(gef_conn[action_pos].numeric_effects[i]))->lval,modifieds);
		      at_start_pres=TRUE;
		     
		      
		    }
		  
		}
	      
	      
	      if(at_start_pres)
		{
		  for(i=0;i<gnum_comp_var;i++)
		    if(GET_BIT(to_copy,i))
		      {
			switch(gcomp_var[i].operator)
			  {
			  case LESS_THAN_OP:
			  case LESS_THAN_OR_EQUAL_OP:
			  case EQUAL_OP:
			  case GREATER_THAN_OP:
			  case GREATER_OR_EQUAL_OP:
			    old_value = vectlevel[level+1]->numeric->values[i]; 
			    
			    //Da vero a falso
			    if ((old_value > 0.5) && (vectlevel[level]->numeric->values_after_start[i] < 0.5))
			      {
				
				insert_values_unsup_num_fact (1,i, level+1);
				
			      }
			    
			    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
			    if ((old_value < 0.5) && ( vectlevel[level]->numeric->values_after_start[i]> 0.5))
			      {				
				insert_values_unsup_num_fact (1, i,level+1);
			      }
			    break;
			    
			  default:
			    break;
			    
			  }
			vectlevel[level+1]->numeric->values[i]=vectlevel[level]->numeric->values_after_start[i];
			
		      }		 
 
		}

	      else
		{
		  for(i=0;i<gnum_comp_var;i++)
		    if(GET_BIT(to_copy,i))
		      {
			switch(gcomp_var[i].operator)
			  {
			  case LESS_THAN_OP:
			  case LESS_THAN_OR_EQUAL_OP:
			  case EQUAL_OP:
			  case GREATER_THAN_OP:
			  case GREATER_OR_EQUAL_OP:
			    old_value = vectlevel[level+1]->numeric->values[i];
			    
			    //Da vero a falso
			    if ((old_value > 0.5) && (vectlevel[level]->numeric->values[i] < 0.5))
			      {
				
				insert_values_unsup_num_fact (1,i, level+1);
				
			      }
			    
			    //Da falso a vero: rimuovo il fatto dall'array dei fatti non supportati
			    if ((old_value < 0.5) && ( vectlevel[level]->numeric->values[i]> 0.5))
			      {				
				insert_values_unsup_num_fact (1, i,level+1);
			      }
			    
			  default:			   
			    break;

			  }
			vectlevel[level+1]->numeric->values[i]=vectlevel[level]->numeric->values[i];
			vectlevel[level]->numeric->values_after_start[i]=vectlevel[level]->numeric->values[i];
			
		      }
		  
		}
	      
	      
	      
	      
	      //memcpy(vectlevel[level]->numeric->values_after_start,vectlevel[level]->numeric->values,gnum_comp_var*sizeof(float));
	      
		  

		
	      
	      // refresh_cvars(level+1);
	      
	      for (i = 0; i < num_numeric_effs; i++)
		if (GET_BIT(to_be_applied,i) && (!(gef_conn[action_pos].numeric_effects[i]).is_at_start))
		  {
		    apply_numeric_effect_at_end (action_pos, level, i);
		    SET_BIT(modifieds,((&(gef_conn[action_pos].numeric_effects[i]))->lval));
		    add_affects_list((&(gef_conn[action_pos].numeric_effects[i]))->lval,modifieds);
		  }
	    }

	  // refresh_cvars(level+1);

	}
      
      
      else
	{
	  for(i=0;i<gnum_comp_var;i++)
	    if(GET_BIT(to_copy,i))
	      {
		vectlevel[level+1]->numeric->values[i]=vectlevel[level]->numeric->values[i];
	      }

	
	  for(i=0;i<gnum_comp_var;i++)
	    if(GET_BIT(to_copy,i))
	      {
		vectlevel[level]->numeric->values_after_start[i]=vectlevel[level]->numeric->values[i];
		
	      }

	  //memcpy(vectlevel[level+1]->numeric->values_after_start,vectlevel[level+1]->numeric->values,gnum_comp_var*sizeof(float));
	  
	}
	  
      refresh_cvars(level+1);
	 

    
      
        

      //2b. qui manca la propagazione dai values at_start al livello successivo!
      //3.copio i valori che basta copiare
      //4. ricalcola le grandezze del livello level+1 che dipendono da grandezze che hanno subito modifiche
      
      //ricontrollo la durata dell'azione al livello dopo; se cambia inserisco la lista
      if (level < level_to - 1)
	if (GET_ACTION_POSITION_OF_LEVEL(level + 1)>=0  &&
	    CONVERT_ACTION_TO_VERTEX(GET_ACTION_POSITION_OF_LEVEL (level + 1))->duration_rvals != NULL)
	  {
	    dur_after =
	      get_action_time (vectlevel[level + 1]->action.position,
			       level + 1);
	    if ((fabsf (dur_after - dur_before) > MIN_DELTA_TIME)
		&& GpG.temporal_plan)
	      {
		insert_propagation_list (GET_ACTION_OF_LEVEL (level));
		
		if (GpG.constraint_type!=0) // vincolo di ordinamento piu' restrittivo
		  for (ind = 0; ind < num_act_ord; ind++)
		    if (mat_ord[GET_ACTION_OF_LEVEL (level)->ord_pos][ind] == EA_EB__SA_SB)
		      {
			dur_act_follow= get_action_time(act_ord_vect[ind]->position, *act_ord_vect[ind]->level);
			if ( ( dur_before <  dur_act_follow && dur_after > dur_act_follow )
			     || ( dur_before > dur_act_follow &&  dur_after < dur_act_follow ) )
			  insert_propagation_list (act_ord_vect[ind]);
		      }
	      }
	    
	    if ((fabsf (dur_after - dur_before) > MIN_DELTA_TIME)
		&& GpG.temporal_plan == 0)
	      printf
		("\nWarning! This problem should be restarted with -temporal 1 option\n");
	  }

      // pre_dur_after=dur_after;
#ifdef TEST_LAZZA
      memcpy(vectlevel[level+1]->numeric->values,vectlevel[level]->numeric->values,gnum_comp_var*sizeof(float));
      memcpy(vectlevel[level]->numeric->values_after_start,vectlevel[level]->numeric->values,gnum_comp_var*sizeof(float));




      //2.applico questi effetti
       for (i = 0; i < gef_conn[action_pos].num_numeric_effects; i++)
	 if ((gef_conn[action_pos].numeric_effects[i]).is_at_start)
	   {
	     apply_numeric_effect_at_start (action_pos, level, i);
	     apply_numeric_effect_at_end (action_pos, level, i);
	   }
	 
       for (i = 0; i < gef_conn[action_pos].num_numeric_effects; i++)
	 if ((!gef_conn[action_pos].numeric_effects[i]).is_at_start)
	   apply_numeric_effect_at_end (action_pos, level, i);
	   
      

       //2b. qui manca la propagazione dai values at_start al livello successivo!
       //3.copio i valori che basta copiare
       //4. ricalcola le grandezze del livello level+1 che dipendono da grandezze che hanno subito modifiche

       refresh_cvars (level + 1);
#endif
       //ricontrollo la durata dell'azione al livello dopo; se cambia inserisco la lista
     
   
     

    } //for(level...


  
  for(i=0;i<gnum_comp_var;i++)
    if(GET_BIT(modifieds,i))
      {
	vectlevel[level_to]->numeric->values_after_start[i]=vectlevel[level_to]->numeric->values[i];
	
      }



  free(modifieds);
  free (to_copy);
  free (to_be_applied);

}



Bool is_num_prec_satisfied (int cvar, int level)
{
 
  if (cvar < 0)
    cvar = -cvar;
  
#ifdef __TEST__
  if ((fabsf (vectlevel[level]->numeric->values[cvar] - 1)) < MAX_APPROX)
    {
      printf ("\n Precondizione num supportata ");
      print_cvar_tree (cvar, level);
    }
  else
    {
      printf ("\n  Precondizione num non  supportata  ");
      print_cvar_tree (cvar, level);
    }
#endif

  return ((fabsf (vectlevel[level]->numeric->values[cvar] - 1)) < MAX_APPROX);
}


Bool is_num_prec_satisfied_after_start (int cvar, int level)
{
  if (cvar < 0)
    cvar = -cvar;

#ifdef __TEST__
  if ((fabsf (vectlevel[level]->numeric->values_after_start[cvar] - 1)) < MAX_APPROX)
    {
      printf ("\n Precondizione num supportata ");
      print_cvar_tree (cvar, level);
    }
  else
    {
      printf ("\n  Precondizione num non  supportata  ");
      print_cvar_tree (cvar, level);
    }
#endif

  return ((fabsf (vectlevel[level]->numeric->values_after_start[cvar] - 1)) < MAX_APPROX);
}


void apply_numeric_effect_to(int act_pos, int num_eff, float *in_vect, float *out_vect, int *modified)
{
  DescNumEff *numeric_effect;
  int num_numeric_effs;

  numeric_effect = &gef_conn[act_pos].numeric_effects[num_eff];
  num_numeric_effs = gef_conn[act_pos].num_numeric_effects;

  eval_comp_var_non_recursive_effects (numeric_effect->index, in_vect, out_vect, -1, -1); 
  
  if(!GET_BIT (modified, numeric_effect->lval))
    {
      SET_BIT (modified, numeric_effect->lval);
      add_affects_list(numeric_effect->lval, modified);
    }
}


/* 
   Controlla se una precondizione numerica è soddisfatta in seguito 
   all'applicazione dell'azione act al livello level

   valori tornati:
   0 : la precondizione resta sempre soddisfatta
   1 : la precondizione non è soddisfatta dopo l'inizio di act
   2 : la precondizione non è soddisfatta alla fine di act
*/
int is_num_prec_unsatisfied_applying_action(int cvar, TimeSpec prec_time, int level, int act) 
{
  int i, res = 0;
  float *temp_values;
  int *modified;

  if(cvar < 0)
    cvar *= -1; //CHIEDERE PAOLO

  modified = alloc_vect(gnum_block_compvar);
  temp_values = (float *)calloc(gnum_comp_var, sizeof(float));

  switch (prec_time) {
  case AT_START_TIME:
    memcpy(temp_values, vectlevel[level]->numeric->values, gnum_comp_var * sizeof(int));
    break;
  case AT_END_TIME:
    memcpy(temp_values, vectlevel[level]->numeric->values_after_start, gnum_comp_var * sizeof(int));
    break;
  default:
    return 1;
  }

  for (i = 0; i < gef_conn[act].num_numeric_effects; i++)
    if (gef_conn[act].numeric_effects[i].is_at_start) 
      // L'effetto at-start di B modifica i valori after-start al livello level
      apply_numeric_effect_to (act, i, temp_values, temp_values, modified);
  
  refresh(temp_values, modified, -1);
  
  if ((fabsf (temp_values[cvar])) < MAX_APPROX)
    res = 1;
  else {
    for (i = 0; i < gef_conn[act].num_numeric_effects; i++)
      if (!gef_conn[act].numeric_effects[i].is_at_start) 
	// L'effetto at-start di B modifica i valori after-start al livello level
	apply_numeric_effect_to (act, i, temp_values, temp_values, modified);
    
    refresh(temp_values, modified, -1);
    
    if ((fabsf (temp_values[cvar])) < MAX_APPROX)
      res = 2;
  }

  free(modified);
  free(temp_values);
  
  return res;
  
}



Bool is_num_prec_satisfied_in_common_level (int cvar)
{
  float value;
  cvar = abs (cvar);
  assert (cvar >= 0);

  if (cvar >= max_num_value) {

#ifdef __MY_OUTPUT__
    printf("\nWarning (is_num_prec_satisfied_in_common_level) : \"cvar\" exceeds max numeric variable number. [cvar = %d <-> MAX = %d]", cvar, max_num_value);
#endif 

    return FALSE;
  }

  /*
  if (cvar >= max_num_value ) {
    max_num_value += MAX_NUM_INC;
   
    gcomp_var = (CompositeNumVar *) realloc(gcomp_var, max_num_value * sizeof(CompositeNumVar));
    memset ( &gcomp_var[max_num_value - MAX_NUM_INC] , 0, MAX_NUM_INC * sizeof(CompositeNumVar));
    
    gcomp_var_value = (float *) realloc(gcomp_var_value, max_num_value * sizeof(float));
    memset ( &gcomp_var_value[max_num_value - MAX_NUM_INC] , 0, MAX_NUM_INC * sizeof(float));
    
    gcomp_var_value_before = (float *) realloc(gcomp_var_value_before, max_num_value * sizeof(float));
    memset ( &gcomp_var_value_before[max_num_value - MAX_NUM_INC] , 0, MAX_NUM_INC * sizeof(float));
    
    gis_inertial = (int*) realloc (gis_inertial, (max_num_value / 32) * sizeof(int));
    memset (&gis_inertial[ (max_num_value - MAX_NUM_INC) / 32], 0, (MAX_NUM_INC / 32) * sizeof(int));
  }
  */

  if( GET_BIT( Hvar.common_level_supported_numeric_preconditions, cvar))
    return TRUE;


  if (Hvar.common_max_values[cvar]>0.5)
    {

      SET_BIT( Hvar.common_level_supported_numeric_preconditions, cvar);


      if (DEBUG4)
	{
	  printf ("\n Supported num prec in common level");
	  print_cvar_tree (cvar, 0);
	}
      return TRUE;

    }

  else
    {
      
      value = ri_eval_comp_var (&gcomp_var[cvar], cvar ,Hvar.common_max_values,Hvar.common_min_values,TRUE);
      
      if( value >0.5)
	{
	  SET_BIT( Hvar.common_level_supported_numeric_preconditions, cvar);


	  if (DEBUG4)
	    {
	      printf ("\n Supported num prec in common level");
	      print_cvar_tree (cvar, 0);
	    }
	  return TRUE;

	}
      else
	{
	  if (DEBUG4)
	    {
	      printf ("\n Not supported num prec in common level");
	      print_cvar_tree (cvar, 0);
	    }
	  return FALSE;
	}
    }
  

}





//applica l'effetto numerico i-esimo
inline void apply_numeric_effect_in_common_level (int num_eff, int times)
{
  int first_op;
  int second_op;  

  num_eff = -num_eff;
  assert (num_eff >= 0);

  first_op = gcomp_var_effects[num_eff].first_op;
  second_op = gcomp_var_effects[num_eff].second_op;

  //versione non ricorsiva della eval_comp_var
  switch (gcomp_var_effects[num_eff].operator)
    {
    case INCREASE_OP:

      Hvar.common_max_values[first_op]+=(times*Hvar.common_max_values[second_op]);

      break;
    case DECREASE_OP:
 
      Hvar.common_min_values[first_op]-=(times*Hvar.common_max_values[second_op]);
      break;
    case SCALE_UP_OP:
  
      Hvar.common_max_values[first_op]*=times*Hvar.common_max_values[second_op];
      break;
    case SCALE_DOWN_OP:
   
      Hvar.common_min_values[first_op]/=times*Hvar.common_max_values[second_op];
      break;
    case ASSIGN_OP:
      if( Hvar.common_max_values[first_op]<Hvar.common_max_values[second_op])
	{
	
	  Hvar.common_max_values[first_op]=Hvar.common_max_values[second_op];
       
	}

      if( Hvar.common_min_values[first_op]>Hvar.common_min_values[second_op])
	{
	
	  Hvar.common_min_values[first_op]=Hvar.common_min_values[second_op];
       
	}

      break;

    case MUL_OP:
      MSG_ERROR("OPERATORE ERRATO");
      exit(0);
     
      break;
    case DIV_OP:
      MSG_ERROR("OPERATORE ERRATO");
      exit(0);
      
      break;
    case PLUS_OP:
      MSG_ERROR("OPERATORE ERRATO");
      exit(0);
     
      break;
    case MINUS_OP:
      MSG_ERROR("OPERATORE ERRATO");
      exit(0);
      
      break;
    case UMINUS_OP:
      MSG_ERROR("OPERATORE ERRATO");
      exit(0);
     
      break;
    case LESS_THAN_OP:
      MSG_ERROR("OPERATORE ERRATO");
      exit(0);

      break;
    case LESS_THAN_OR_EQUAL_OP:
      MSG_ERROR("OPERATORE ERRATO");
      exit(0);
  
      break;
    case EQUAL_OP:
      MSG_ERROR("OPERATORE ERRATO");
      exit(0);
    
      break;
    case GREATER_THAN_OP:
      MSG_ERROR("OPERATORE ERRATO");
      exit(0);
      
      break;
    case GREATER_OR_EQUAL_OP:
      MSG_ERROR("OPERATORE ERRATO");
      exit(0);
  
      break;
    default:

      printf ("\nWarning7448\n");
      MSG_ERROR("OPERATORE ERRATO");
      exit(0);
      break;
    }

  

#ifdef __NO_COMMON_UPDATE__


  // X BETTINI io non farei aggiornamento

      for (i = 0; i < gnum_comp_var; i++)
	{
	
	  if(!GET_BIT(Numeric.Affects_Matrix[gcomp_var_effects[num_eff].first_op],i))
	    continue;
	  first_op = gcomp_var[i].first_op;
	  second_op = gcomp_var[i].second_op;
  
	  
	  
	  switch (gcomp_var[i].operator)
	    {
	    case INCREASE_OP:
	    case DECREASE_OP:
	    case SCALE_UP_OP:
	    case SCALE_DOWN_OP:
	    case ASSIGN_OP:
	    case FIX_NUMBER:
	    case VARIABLE_OP:
	    case MINIMIZE_OP:
	    case MAXIMIZE_OP:	
	      break;
	      
	    case MUL_OP:
	      Hvar.common_max_values[i] = Hvar.common_max_values[first_op] *Hvar.common_max_values[second_op];
	      Hvar.common_min_values[i] = Hvar.common_min_values[first_op] *Hvar.common_min_values[second_op];
	      break;
	    case DIV_OP:
	      Hvar.common_max_values[i] = Hvar.common_max_values[first_op] /Hvar.common_min_values[second_op];
	      Hvar.common_min_values[i] = Hvar.common_min_values[first_op] /Hvar.common_max_values[second_op];
	      break;
	    case PLUS_OP:
	      Hvar.common_max_values[i] = Hvar.common_max_values[first_op] +Hvar.common_max_values[second_op];
	      Hvar.common_min_values[i] = Hvar.common_min_values[first_op] +Hvar.common_min_values[second_op];
	      break;
	    case MINUS_OP:
	      Hvar.common_max_values[i] = Hvar.common_max_values[first_op] -Hvar.common_min_values[second_op];
	      Hvar.common_min_values[i] = Hvar.common_min_values[first_op] -Hvar.common_max_values[second_op];
	      break;
	    case UMINUS_OP:
	      Hvar.common_max_values[i] = -Hvar.common_min_values[first_op];
	      Hvar.common_min_values[i] = -Hvar.common_max_values[first_op];
	      break;
	    case LESS_THAN_OP:
	      if (Hvar.common_max_values[i] > 0.5)
		continue;
	      Hvar.common_max_values[i]  = (float) (Hvar.common_min_values[first_op] < Hvar.common_max_values[second_op]);
	      break;
	    case LESS_THAN_OR_EQUAL_OP:
	      if ( Hvar.common_max_values[i]> 0.5)
		continue;
	      Hvar.common_max_values[i]  = (float) (Hvar.common_min_values[first_op] <= Hvar.common_max_values[second_op]);
	      break;
	    case EQUAL_OP:
	      if (Hvar.common_max_values[i] > 0.5)
		continue;
	      Hvar.common_max_values[i] = (float) ((Hvar.common_min_values[gcomp_var[i].first_op] <= Hvar.common_max_values[gcomp_var[i].second_op] && 
						    (Hvar.common_max_values[gcomp_var[i].first_op] >= Hvar.common_max_values[gcomp_var[i].second_op])) ||
						   (Hvar.common_max_values[gcomp_var[i].first_op] <= Hvar.common_max_values[gcomp_var[i].second_op] && 
						    (Hvar.common_min_values[gcomp_var[i].first_op] <= Hvar.common_min_values[gcomp_var[i].second_op])));
		
	      break;
	    case GREATER_THAN_OP:
	      if (Hvar.common_max_values[i] > 0.5)
		continue;
	      Hvar.common_max_values[i]  = (float) (Hvar.common_max_values[first_op] > Hvar.common_min_values[second_op]);
	      break;
	    case GREATER_OR_EQUAL_OP:
	      if ( Hvar.common_max_values[i]> 0.5)
		continue;
	      Hvar.common_max_values[i]  = (float) (Hvar.common_min_values[first_op] >= Hvar.common_max_values[second_op]);
	      break;
	    default:
	      printf ("\nWarning37448\n");
	      break;
	    }

	}
#endif

}



float try_num_eff_in_level (int cv_index, float *in_vect, float *out_vect,Bool effect)
{
  CompositeNumVar *cv;
  int first_op ;
  int second_op ;
  float tmp;

  assert (cv_index >= 0);
  if (effect)
    {
      cv = &gcomp_var_effects[cv_index];
      first_op = gcomp_var_effects[cv_index].first_op;
      second_op = gcomp_var_effects[cv_index].second_op;
    }
  else
    {
      cv = &gcomp_var[cv_index];
      //printf("\n cv index: %d", cv_index);
      
      first_op = gcomp_var[cv_index].first_op;
      second_op = gcomp_var[cv_index].second_op;
    }
  switch (cv->operator)
    {
    case FIX_NUMBER:
    case VARIABLE_OP:
      out_vect[cv_index] = in_vect[cv_index];
      return out_vect[cv_index];
      break;
    case MUL_OP:
      out_vect[cv_index] =
	try_num_eff_in_level (first_op, in_vect, out_vect,FALSE) * try_num_eff_in_level(second_op, in_vect, out_vect,FALSE);
      return out_vect[cv_index];
      break;
    case DIV_OP:
      tmp = try_num_eff_in_level (second_op, in_vect, out_vect,FALSE);
      if (tmp == 0)
	{
	  printf ("\n\nWARNING: Division by zero in try_num_eff\n\n");
	  out_vect[cv_index] = 0;
	  return out_vect[cv_index];
	}
      out_vect[cv_index] =
	try_num_eff_in_level (first_op, in_vect, out_vect,FALSE) / tmp;
      return out_vect[cv_index];
    case PLUS_OP:
      out_vect[cv_index] =
	try_num_eff_in_level (first_op, in_vect, out_vect,FALSE) + try_num_eff_in_level (second_op, in_vect, out_vect,FALSE);
      return out_vect[cv_index];
      break;
    case MINUS_OP:
      out_vect[cv_index] =
	try_num_eff_in_level (first_op, in_vect, out_vect,FALSE) - try_num_eff_in_level (second_op, in_vect, out_vect,FALSE);
      return out_vect[cv_index];
      break;
    case UMINUS_OP:
      out_vect[cv_index] = -try_num_eff_in_level (first_op, in_vect, out_vect,FALSE);
      return out_vect[cv_index];
      break;
    case INCREASE_OP:
      out_vect[first_op] += try_num_eff_in_level (second_op, in_vect, out_vect,FALSE);
      return out_vect[first_op];
      break;
    case DECREASE_OP:
      out_vect[first_op] -= try_num_eff_in_level (second_op, in_vect, out_vect,FALSE);
      return out_vect[first_op];
      break;
    case SCALE_UP_OP:
      out_vect[first_op] *= try_num_eff_in_level (second_op, in_vect, out_vect,FALSE);
      return out_vect[first_op];
      break;
    case SCALE_DOWN_OP:
      out_vect[first_op] /= try_num_eff_in_level (second_op, in_vect, out_vect,FALSE);
      return out_vect[first_op];
      break;
    case ASSIGN_OP:
      out_vect[first_op] = try_num_eff_in_level (second_op, in_vect, out_vect,FALSE);
      return out_vect[first_op];
      break;
    default:
      printf ("\n\nnot considered\n\n");
      exit (2);
      break;
    }

  return 0;
}



//per ogni ef_conn, setta il flag is_numeric; da chiamarsi dopo la add_composite_vars
void set_numeric_flag ()
{
  int i, j;

  for (i = 0; i < gnum_ef_conn; i++)
    {
      //Verifica se ci sono precondizioni nmeriche
      for (j = 0; j < gef_conn[i].num_PC; j++)
	if (gef_conn[i].PC[j] < 0)
	  break;
      if (j != gef_conn[i].num_PC)
	{
	  gef_conn[i].is_numeric = TRUE;
	  GpG.numeric_precs_present = TRUE;
	  SET_BIT(GpG.numeric_actions, i);
	  gef_conn[i].has_numeric_precs = TRUE;
	  continue;
	}
      //Verifica se ci sono effetti numerici
      for (j = 0; j < gef_conn[i].num_A; j++)
	if (gef_conn[i].A[j] < 0)
	  break;
      if (j != gef_conn[i].num_A)
	{
	  gef_conn[i].is_numeric = TRUE;
	  SET_BIT(GpG.numeric_actions, i);
	  continue;
	}
      //Verifica odd cond & effects(pc_overall,pc_end,A_start)
      if (gef_conn[i].sf)
	{
	  //Verifica se ci sono precondizioni overall nmeriche
	  for (j = 0; j < gef_conn[i].sf->num_PC_overall; j++)
	    if (gef_conn[i].sf->PC_overall[j] < 0)
	      break;
	  if (j != gef_conn[i].sf->num_PC_overall)
	    {
	      GpG.numeric_precs_present = TRUE;
	      gef_conn[i].is_numeric = TRUE;
	      SET_BIT(GpG.numeric_actions, i);
	      gef_conn[i].has_numeric_precs = TRUE;
	      continue;
	    }
	  //Verifica se ci sono precondizioni at end nmeriche
	  for (j = 0; j < gef_conn[i].sf->num_PC_end; j++)
	    if (gef_conn[i].sf->PC_end[j] < 0)
	      break;
	  if (j != gef_conn[i].sf->num_PC_end)
	    {
	      GpG.numeric_precs_present = TRUE;
	      gef_conn[i].is_numeric = TRUE;
	      SET_BIT(GpG.numeric_actions, i);
	      gef_conn[i].has_numeric_precs = TRUE;
	      continue;
	    }
	  //Verifica se ci sono effetti at start numerici
	  for (j = 0; j < gef_conn[i].sf->num_A_start; j++)
	    if (gef_conn[i].sf->A_start[j] < 0)
	      break;
	  if (j != gef_conn[i].sf->num_A_start)
	    {
	      gef_conn[i].is_numeric = TRUE;
	      SET_BIT(GpG.numeric_actions, i);
	      continue;
	    }
	}
    }
}


void copy_num_values_from_level_to_level (int level_from, int level_to, Bool check_variations)
{
  int i;
  float old_value, new_value;
  //Copia valori numerici dal level_from al level_to

  // printf("\n\nparams : level_from : %d, level_to : %d, check : %s", level_from, level_to, (check_variations)?"ON":"OFF");

  if (check_variations)
    {
      for (i = 0; i < gnum_comp_var; i++)
	{	  
	  //Setto il bit modified dei valori che cambiano
	  if ((fabsf
	       (vectlevel[level_to]->numeric->values[i] -
		vectlevel[level_from]->numeric->values[i])) > MAX_APPROX )
	    {
	      SET_BIT (vectlevel[level_to]->numeric->modified_vars_end, i);
	      add_affects_list(i,vectlevel[level_to]->numeric->modified_vars_end);
	      
	      switch (gcomp_var[i].operator)
		{
		case LESS_THAN_OP:
		case LESS_THAN_OR_EQUAL_OP:
		case EQUAL_OP:
		case GREATER_THAN_OP:
		case GREATER_OR_EQUAL_OP:
		  old_value = vectlevel[level_to]->numeric->values[i];
		  new_value = vectlevel[level_from]->numeric->values[i];
		  //Da vero a falso
		  if ((old_value > 0.5) && (new_value < 0.5))
		    {
#ifdef _TEST_NUM_PREC_
		      printf ("\nxConfronto: (liv.%d)", level_to);
		      print_cvar_tree (i, level_to);
		      printf (" da vero a falso");
#endif
		      insert_values_unsup_num_fact (1, i, level_to);

		    }
		  break;
		default:
		  break;
		}
	      
	    }
	  
	  if(GET_BIT (vectlevel[level_to]->numeric->modified_vars_end, i))
	    continue;

	  if ((fabsf
	       (vectlevel[level_to]->numeric->values_after_start[i] -
		vectlevel[level_from]->numeric->values_after_start[i])) >
	      MAX_APPROX)
	    {
	      switch (gcomp_var[i].operator)
		{
		case LESS_THAN_OP:
		case LESS_THAN_OR_EQUAL_OP:
		case EQUAL_OP:
		case GREATER_THAN_OP:
		case GREATER_OR_EQUAL_OP:
		  old_value = vectlevel[level_to]->numeric->values[i];
		  new_value = vectlevel[level_from]->numeric->values[i];
		  //Da vero a falso
		  if ((old_value > 0.5) && (new_value < 0.5))
		    {
#ifdef _TEST_NUM_PREC_
		      printf ("\nxConfronto: (liv.%d)", level_to);
		      print_cvar_tree (i, level_to);
		      printf (" da vero a falso");
#endif
		      insert_values_unsup_num_fact (1, i, level_to);

		    }
		  break;
		default:
		  break;
		}
	      
	      SET_BIT (vectlevel[level_to]->numeric->modified_vars_start, i);
	      add_affects_list(i,vectlevel[level_to]->numeric->modified_vars_start);
	    }
	  
	}
    }

    memcpy(vectlevel[level_from]->numeric->values_after_start,vectlevel[level_from]->numeric->values,gnum_comp_var*sizeof(float));
    memcpy(vectlevel[level_to]->numeric->values,vectlevel[level_from]->numeric->values,gnum_comp_var*sizeof(float));
    memcpy(vectlevel[level_to]->numeric->values_after_start,vectlevel[level_from]->numeric->values_after_start,gnum_comp_var*sizeof(float));
    memset (vectlevel[level_from]->numeric->w_is_goal, 0, gnum_comp_var * sizeof (short));
    memcpy (vectlevel[level_to]->numeric->w_is_used,  vectlevel[level_from]->numeric->w_is_used, sizeof (short) * gnum_comp_var);

}




IntList *copy_intlist (IntList * src)
{
  IntList *tmpil;
  IntList *ret;
  IntList *el;
  IntList *prev = NULL;

  ret = NULL;
  if (src == NULL)
    return NULL;
  for (tmpil = src; tmpil; tmpil = tmpil->next)
    {
      el = new_IntList ();
      if (tmpil == src)
	ret = el;
      el->item = tmpil->item;
      if (prev)
	prev->next = el;
      prev = el;
    }
  return ret;
}


void add_intlist_to_intlist (IntList * to_queue, IntList ** first_list)
{
  IntList *tmpil;
  IntList *copy_il;

  copy_il = copy_intlist (to_queue);
  if (!*first_list)
    {
      *first_list = copy_il;
      return;
    }
  //toglie dalla lista copy gli elementi che sono gia' presenti in *first_list
  //va a pescare l'ultimo elemento della lista
  for (tmpil = *first_list; tmpil; tmpil = tmpil->next)
    if (!tmpil->next)
      {
	tmpil->next = copy_il;
	break;
      }
}



void make_false_all_checks_on_not_init (void)
{
  int i;
  IntList *il;
  IntList *tmpil;

  CompositeNumVar *cv;
  for (i = 0; i < gnum_comp_var; i++)
    {
      cv = &gcomp_var[i];
      if ((cv->operator== VARIABLE_OP) && (cv->first_op == -1))
	{
	  il = copy_intlist (cv->affects);
	  //aggiungo in coda tutti gli affects 
	  for (tmpil = il; tmpil; tmpil = tmpil->next)
	    add_intlist_to_intlist (gcomp_var[tmpil->item].affects, &il);
	  for (tmpil = il; tmpil; tmpil = tmpil->next)
	    {
	      switch (gcomp_var[tmpil->item].operator )
		{
		case EQUAL_OP:
		case GREATER_THAN_OP:
		case GREATER_OR_EQUAL_OP:
		case LESS_THAN_OP:
		case LESS_THAN_OR_EQUAL_OP:
		  gcomp_var[tmpil->item].operator= FIX_NUMBER;
		  gcomp_var[tmpil->item].first_op = -1;
		  gcomp_var[tmpil->item].second_op = -1;
		  GCOMP_VAR_VALUE(tmpil->item) =0.0;
		  gcomp_var[tmpil->item].affects = free_intlist (gcomp_var[tmpil->item].affects);

		  SET_BIT (gis_inertial, tmpil->item);
		  break;
		default:
		  break;
		}
	    }
	}
    }
}





void insert_unsup_numeric_fact (int cv_index, int level)
{
  if (GET_BIT (gis_inertial, cv_index))
    {
      if (DEBUG3)
	{
	  printf ("\nERROR: inertial fact insert in unsup list\n");
	  print_cvar_tree (cv_index, level);
	  printf ("\n");
	  fflush (stdout);
	}
    }

  if (DEBUG4)
    {
      printf ("\n New False Numeric Fact: \n ");
      print_cvar_tree (cv_index, level);
      printf ("\n level %d, position %d", level, cv_index);
    }

#ifdef _TEST_NUM_PREC_
  printf ("\n#####INSERITA PRECO NUM NON SODD liv.%d:", level);
  print_cvar_tree (cv_index, level);
  printf ("\n");
#endif

  if (vectlevel[level]->numeric->false_position[cv_index] >= 0)
    {
#ifdef __TEST__
      printf ("warn: il fatto che volevo inserire [ ");
      print_cvar_tree (cv_index, level);
      printf
	(" ]e' gia stato inserito (false_position>0): non lo inserisco nuovamente!");
#endif
#ifdef _TEST_NUM_PREC_
      printf ("\ngia inserita");
      print_unsup_num_facts ();
#endif
      return;
    }

  if (unsup_num_fact[GpG.num_false_num_fa] == NULL)
    unsup_num_fact[GpG.num_false_num_fa] =
      (constraints_list) malloc (sizeof (constraints));
  unsup_num_fact[GpG.num_false_num_fa]->fact = cv_index;
  unsup_num_fact[GpG.num_false_num_fa]->action = -1;
  unsup_num_fact[GpG.num_false_num_fa]->constraint_type = C_T_UNSUP_NUM_FACT;
  unsup_num_fact[GpG.num_false_num_fa]->level = &(vectlevel[level]->level);
  vectlevel[level]->numeric->false_position[cv_index] = GpG.num_false_num_fa;
  unsup_num_fact[GpG.num_false_num_fa]->supported_facts_relaxed_plan_bit_vector=NULL;
  unsup_num_fact[GpG.num_false_num_fa]->relaxed_plan_actions_bit_vector=NULL;

  define_supported_fact_for_relaxed_plan_of_inconsistences(unsup_num_fact[GpG.num_false_num_fa], TRUE);

  GpG.num_false_num_fa++;

  if (GpG.num_false_num_fa >= MAX_FALSE){
#ifdef __MY_OUTPUT__
    MSG_ERROR( WAR_MAX_FALSE );
#else
    printf( WAR_MAX_FALSE );
#endif    
    exit (1);
  }


#ifdef __TEST__
  printf ("\n INSERISCO FALSE  fact %s, false_actions %d false_fact %d level %d pos %d",
	  print_ft_name_string (-cv_index, temp_name), GpG.num_false_act, GpG.num_false_num_fa, level, GpG.num_false_num_fa - 1);
#endif

#ifdef _TEST_NUM_PREC_
  printf ("\nOra ho %d fatti num unsup", GpG.num_false_num_fa);
  print_unsup_num_facts ();
#endif




}






//rimuove un fatto dall'array dei fatti non supportati
void remove_unsup_num_fact (int position)
{
  int removed_fct;
  int removed_fct_level;


  if (GpG.num_false_num_fa == 0)
    return;
  if (position < 0)
    return;
  assert (position < GpG.num_false_num_fa);
  if (!unsup_num_fact[position])
    return;
  removed_fct = unsup_num_fact[position]->fact;
  removed_fct_level = *unsup_num_fact[position]->level;



  if (DEBUG4)
    {
      printf ("\n New True Numeric Fact: \n ");
      print_cvar_tree (position, removed_fct_level);
      printf ("\n level %d, position %d", removed_fct_level, position);
    }

  //il fatto non compariva tra i fatti non supportati, esco subito
  if (vectlevel[removed_fct_level]->numeric->false_position[removed_fct] == -1)
    return;
  //metto a -1 la false_position del fatto da togliere
  vectlevel[removed_fct_level]->numeric->false_position[removed_fct] = -1;

  //copio quello in ultima posizione su quello da togliere , sempre se questo non era l'ultimo
  if ((GpG.num_false_num_fa > 1) && (position < GpG.num_false_num_fa - 1))
    {
      unsup_num_fact[position]->fact = unsup_num_fact[GpG.num_false_num_fa - 1]->fact;
      vectlevel[*(unsup_num_fact[GpG.num_false_num_fa - 1]->level)]->numeric->false_position[unsup_num_fact[GpG.num_false_num_fa - 1]->fact] = position;
      unsup_num_fact[position]->action = unsup_num_fact[GpG.num_false_num_fa - 1]->action;
      unsup_num_fact[position]->constraint_type = unsup_num_fact[GpG.num_false_num_fa - 1]->constraint_type;
      unsup_num_fact[position]->level =	unsup_num_fact[GpG.num_false_num_fa - 1]->level;
    }
  //decremento il numero di fatti numerici non supportati
  GpG.num_false_num_fa--;
#ifdef _TEST_NUM_PREC
  printf ("\nNuova false position di %d: %d", removed_fct,
	  vectlevel[removed_fct_level]->numeric->false_position[removed_fct]);
  printf ("\nOra ho %d fatti num unsup", GpG.num_false_num_fa);
  print_unsup_num_facts ();
#endif
  assert (GpG.num_false_num_fa >= 0);

}



int fix_unsup_num_fact (constraints_list unsup_numeric_fact, int num)
{
  int num_min, num_neg, choice;
  float best = 0.0;
  EfConn *act;
  int level;
 
  assert (unsup_numeric_fact != NULL);

  if (DEBUG2)
    {
      printf("\n\n###INC CHOICE:\n  Unsupported numeric fact: position %d, level %d \n  fact name : ",
	     unsup_numeric_fact->fact, *unsup_numeric_fact->level);
      print_cvar_tree (unsup_numeric_fact->fact, *unsup_numeric_fact->level);
      printf ("\n");
    }

  if (DEBUG5)
    {
      int is_not_satisfied;
#ifdef _TEST_NUM_PREC
      printf ("\n Cerco di fare la fix di ");
      print_cvar_tree (unsup_numeric_fact->fact, *unsup_numeric_fact->level);
      printf (", livello %d\n", *unsup_numeric_fact->level);
#endif
      is_not_satisfied = !is_num_prec_satisfied (unsup_numeric_fact->fact,*unsup_numeric_fact->level);
      if (!is_not_satisfied)
	if(DEBUG6)
	  print_num_levels_and_actions ();
    }

  if (num <= 0)
    {
      if (GpG.tabuplan_act)
	{
	  if(DEBUG1)
	    printf("\nWarning: Neighborhood empty");
	  return -1;
	}
      else
	{
#ifdef __TEST__
	  fprintf (stderr, "\n RIMUOVO INCONSISTENZA FACT %d ATTENZIONE!!", unsup_numeric_fact->fact);

	  remove_unsup_num_fact (vectlevel[*unsup_numeric_fact->level]->numeric->false_position[unsup_numeric_fact->fact]);
#endif
	  restart_MetricMinimizeCost ();
	  return (FALSE);
	}
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

  choice = -1;
  
  if (( MY_RANDOM % GpG.denominator) < GpG.numerator)
    {
      choice = MY_RANDOM % num;
      if (DEBUG1)
	printf("\n Random choice= %d",choice);
      
      neighb_vect[choice]->cost.weight=0.0;
      neighb_vect[choice]->cost.act_cost=0.0;
      neighb_vect[choice]->cost.act_time=0.0;
    }

  if (choice < 0) {
  if (num > 1)

    best = find_min (unsup_numeric_fact, pos_temp_vect, num, &num_min, &num_neg);
  else
    {
      num_min = 1;
      pos_temp_vect[0] = 0;
    }

  GpG.is_lm = 0;		// LM Per default NON considero la configuraz. corrente come un minimo locale


  if (num == 1)
    choice = 0;
  else if (best > 0)
    {
      GpG.is_lm = 1;		// LM Siamo in un minimo locale

      if (num_min == 1)
	choice = pos_temp_vect[0];
      else
	choice = pos_temp_vect[(MY_RANDOM % num_min)];
    }
  else
    {
      if (num_neg == 1)
	choice = pos_temp_vect[0];
      else if ((MY_RANDOM % GpG.denominator) < GpG.numerator)
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
      printf ("\n\n=== Action choosen unsup numeric fact: %s, level %d \n     Incons %.3f   Cost %.3f   Time %.3f ",
	      print_op_name_string (act->position, temp_name), level, neighb_vect[choice]->cost.weight, neighb_vect[choice]->cost.act_cost,
	      neighb_vect[choice]->cost.act_time);

      if (DEBUG3)
	print_actions_in_subgraph ();
    }




#ifdef __TEST__
  printf ("\n Act choosen  %s lev %d ", CONVERT_ACTION_TO_VERTEX (neighb_vect[choice]->act_pos)->name, neighb_vect[choice]->act_level);
#endif


#ifdef _TEST_NUM_PREC
  {
    printf (" con ");
    print_op_name (neighb_vect[choice]->act_pos);
  }
#endif
  //qui va la chiamata alla insert_remove_action, vedi come ho fatto per fix_unsup_fact


#ifdef __TEST_MIXED__
  printf("\n Inserisci azione da inserire/rimuovere ");
  fflush (stdout);
  scanf("%d",&choice);
#endif


  choice = insert_remove_action (neighb_vect[choice]->act_pos, neighb_vect[choice]->act_level,
				 neighb_vect[choice]->constraint_type, GpG.approximation_level);
  return choice;
}



void check_false_position ()
{
  int j, k = 0;
  Bool present[max_num_value];

  memset (present, 0, max_num_value * sizeof (Bool));
  while (TRUE)
    {
      if (vectlevel[k])
	for (j = 0; j < max_num_value; j++)
	  {
	    int f_p = vectlevel[k]->numeric->false_position[j];
	    assert (f_p >= -1);
	    assert (f_p < GpG.num_false_num_fa);
	    //verifico l'assenza di doppioni
	    if (f_p != -1)
	      {
		if (present[f_p] == TRUE)
		  assert (0);
		else
		  present[f_p] = TRUE;
	      }
	  }
      else
	break;
      k++;
    }
  //verifico corrispondenza
  for (j = 0; j < GpG.num_false_num_fa; j++)
    assert (j == vectlevel[*unsup_num_fact[j]->level]->numeric->false_position[unsup_num_fact[j]->fact]);
}



int define_neighborhood_for_numeric_actions (constraints_list unsup_numeric_fact, int initialize)
{
  static action_set neighbors;
 
  if (initialize != 0)
    {
      // reset_fact_costs();
      reset_neighborhood ();
    }

  verify_cri_until_level(*unsup_numeric_fact->level);
  
  //determino il vicinato del fatto numerico
  neighbors.num_A = 0;

  create_neighborhood_for_compvar (unsup_numeric_fact->fact, 1, 0, &neighbors, 1, *unsup_numeric_fact->level);
  
  define_neighborhood_for_compvar_in_down_level (unsup_numeric_fact->fact, &neighbors, *unsup_numeric_fact->level);
  
  //aggiunta per rimuovere l'azione che richiede questo fatto numerico non supportato
  create_remotion_neighborhood_for_compvar (unsup_numeric_fact->fact, *unsup_numeric_fact->level);

#ifdef __TEST__
  printf ("Neighborhood for num. fact %d level %d: ",
	  unsup_numeric_fact->fact, *unsup_numeric_fact->level);
  print_cvar_tree (unsup_numeric_fact->fact, *unsup_numeric_fact->level);
  for (i = 0; i < neighbors.num_A; i++)
    {
      printf ("\nA%3d: %3d", i, neighbors.A[i]);
      print_op_name (neighbors.A[i]);
    }
#endif
  //fine aggiunta per rimuovere l'azione che richiede questo fatto numerico non supportato
  return num_neighborhood;
}



//rimuove le inconsistenze che in realta' non sono tali dall'array unsup_num_fact
void clean_unsup_num_fact ()
{
  int i;

  for (i = 0; i < GpG.num_false_num_fa; i++)
    if (is_num_prec_satisfied
	(unsup_num_fact[i]->fact, *unsup_num_fact[i]->level))
      remove_unsup_num_fact (i);
}



int choose_min_cost_unsup_num_fact ()
{
  int i, best = 0, min_level = 0;
  float min = 100000.0; 

  GpG.exist_numeric_preconds=TRUE;

  if (GpG.inc_choice_type == MAX_LEVEL_INC)
    min_level = 0;
  else
    min_level = 100000; // if (GpG.inc_choice_type == MIN_LEVEL_INC || GpG.inc_choice_type == MIN_LEVEL_COST_INC  || GpG.inc_choice_type == MIN_LEVEL_CONSTR_INC || GpG.inc_choice_type == MIN_COST_INC)


  if (GpG.inc_choice_type == MAX_COST_INC)
    min = 0.0;
  else
     min = 100000.0; //if (GpG.inc_choice_type == MIN_COST_INC || GpG.inc_choice_type == MIN_LEVEL_COST_INC)


  for (i = GpG.num_false_num_fa - 1; i >= 0; i--)
    {


      if (GpG.inc_choice_type == MAX_LEVEL_INC || GpG.inc_choice_type == MAX_COST_INC)
	{

	  if (min_level < *unsup_num_fact[i]->level)
	    {
	      min_level = *unsup_num_fact[i]->level;
	      best = i;
	    }
	}
      else
      // Per ora e' solo in base al livello
	//      if (GpG.inc_choice_type == MIN_LEVEL_INC || GpG.inc_choice_type == MIN_LEVEL_COST_INC
	//  || GpG.inc_choice_type == MIN_LEVEL_CONSTR_INC || GpG.inc_choice_type == MIN_COST_INC)
	{

	  if (min_level > *unsup_num_fact[i]->level || (min_level == *unsup_num_fact[i]->level && MY_RANDOM % 2))
	    {
	      min_level = *unsup_num_fact[i]->level;
	      best = i;
	    }
	}

      /****
DA ESTENDERE CON INFO RAGG NUMERICA
      else if (GpG.inc_choice_type == MIN_LEVEL_COST_INC)
	{

	  if (min_level > *unsup_num_fact[i]->level)
	    {
	      min_level = *unsup_num_fact[i]->level;
	      best = i;
	      get_dg_fact_cost (unsup_num_fact[i]->fact, *unsup_num_fact[i]->level, &loc_dg_cost);
	      min = loc_dg_cost->totcost;
	    }
	  else if (min_level == *unsup_num_fact[i]->level)
	    {

	      get_dg_fact_cost (unsup_num_fact[i]->fact, *unsup_num_fact[i]->level, &loc_dg_cost);
	      if (min > loc_dg_cost->totcost
		  || (min == loc_dg_cost->totcost && MY_RANDOM & FIRST_1))
		{
		  min = loc_dg_cost->totcost;
		  best = i;
		}



	    }
	}
      else if (GpG.inc_choice_type == MIN_LEVEL_CONSTR_INC)
	{

	   if (min_level > *unsup_num_fact[i]->level)
	    {
	      min_level = *unsup_num_fact[i]->level;
	      best = i;
	      min_constr =compute_constr_fact (unsup_num_fact[i]->fact, unsup_num_fact[i]->fact, *unsup_num_fact[i]->level, 1, *unsup_num_fact[i]->level, &min );

	     
           }
	  else if (min_level == *unsup_num_fact[i]->level)
	    {

	      curr_min_constr =	compute_constr_fact (unsup_num_fact[i]->fact, unsup_num_fact[i]->fact, *unsup_num_fact[i]->level , 1, *unsup_num_fact[i]->level, &tot);
	   
	      if (min_constr < curr_min_constr || (min_constr == curr_min_constr
						   && (min > tot || (min == tot && (MY_RANDOM % 2)))))
		{
		  min = tot;
		  best = i;
		  min_constr = curr_min_constr;
		}
	    }
	}
      ****/
 

      /***********

DA ESTENDERE CON INFO RAGG NUMERICA
      else if (GpG.inc_choice_type == MAX_COST_INC)
	{

	  get_dg_fact_cost (unsup_num_fact[i]->fact, *unsup_num_fact[i]->level , &loc_dg_cost);
	  if (min < loc_dg_cost->totcost || (MY_RANDOM % 2))
	    {
	      min = loc_dg_cost->totcost;
	      best = i;
	    }
	}
      ****/

    }


  return best;
}


void insert_values_unsup_num_fact (int status, int fact, int level)
{
  static int num_facts = 0;
  static int *fct_pos = NULL;
  static int *fct_level = NULL;
  static Bool semaforo_verde = TRUE;
  int i, l;

  if (!fct_pos)
    fct_pos = calloc(max_num_value, sizeof(int));
  if (!fct_level)
    fct_level = calloc(max_num_value, sizeof(int));

  assert (status < 3);
  switch (status)
    {
    case 0:
      assert (semaforo_verde);
      assert (fact < 0);
      assert (level < 0);
      //azzeramento
      num_facts = 0;
      semaforo_verde = FALSE;
      break;

    case 1:
      assert (fact >= 0);

      if (level < 0)
	return;

      //      assert (level >= 0);
      //inserimento di un nuovo fatto numerico
      assert (num_facts < max_num_value);
      for (i = 0; i < num_facts; i++)
	if (fct_pos[i] == fact)
	  break;
      //se il fatto era gia' dentro tengo il minimo livello
      if ((i != num_facts) && (num_facts != 0))
	fct_level[i] = MIN (level, fct_level[i]);
      else
	{
	  fct_pos[num_facts] = fact;
	  fct_level[num_facts] = level;
	  num_facts++;
	}
      break;

      //eventuale inserimento/rimozione
    case 2:
      assert (fact < 0);
      assert (level < 0);
      //per tutti i fatti inseriti in qs. lista
      for (i = 0; i < num_facts; i++)
	{
	  int f = fct_pos[i];
	  for (l = fct_level[i]; l <= GpG.curr_plan_length; l++)
	    if (vectlevel[l]->numeric->w_is_goal[f])
	      {
		if (is_num_prec_satisfied (f, l))
		  {
		    if (vectlevel[l]->numeric->false_position[f] >= 0)
		      remove_unsup_num_fact (vectlevel[l]->numeric->false_position[f]);
		  }
		else
		  {
		    if (vectlevel[l]->numeric->false_position[f] < 0)
		      insert_unsup_numeric_fact (f, l);
		  }
	      }
	}
      //per sicurezza
      num_facts = 0;
      semaforo_verde = TRUE;
      break;
    }
}

//tolgo dalla lista delle azioni tutte quelle azioni che a causa di precondizioni numeriche maai verificabili o valori non inizializzati , non verranno mai verificate
void remove_unappliable_actions ()
{
  int i, j;
  gis_not_appliable = calloc (gnum_ef_conn / 32 + 1, sizeof (int));
  for (i = 0; i < gnum_ef_conn; i++)
    {
      //START
      for (j = 0; j < gef_conn[i].num_PC; j++)
	{
	  if (gef_conn[i].PC[j] < 0)
	    if (gcomp_var[-gef_conn[i].PC[j]].operator == FIX_NUMBER)
	      if (GCOMP_VAR_VALUE(-gef_conn[i].PC[j]) < 0.5)
		{
		  SET_BIT (gis_not_appliable, i);
		  break;
		}
	}
      //toglierlo una volta e' piu che sufficiente
      if (j != gef_conn[i].num_PC)
	continue;
      if (gef_conn[i].sf)
	{
	  //OVERALL
	  for (j = 0; j < gef_conn[i].sf->num_PC_overall; j++)
	    {
	      if (gef_conn[i].sf->PC_overall[j] < 0)
		if (gcomp_var[-gef_conn[i].sf->PC_overall[j]].operator == FIX_NUMBER)
		  if (GCOMP_VAR_VALUE(-gef_conn[i].sf->PC_overall[j]) < 0.5)
		    {
		      SET_BIT (gis_not_appliable, i);
		      break;
		    }
	    }
	  //toglierlo una volta e' piu che sufficiente
	  if (j != gef_conn[i].sf->num_PC_overall)
	    continue;
	  //END
	  for (j = 0; j < gef_conn[i].sf->num_PC_end; j++)
	    {
	      if (gef_conn[i].sf->PC_end[j] < 0)
		if (gcomp_var[-gef_conn[i].sf->PC_end[j]].operator == FIX_NUMBER)
		  if (GCOMP_VAR_VALUE(-gef_conn[i].sf->PC_end[j]) < 0.5)
		    {
		      SET_BIT (gis_not_appliable, i);
		      break;
		    }
	    }
	  //toglierlo una volta e' piu che sufficiente
	  if (j != gef_conn[i].sf->num_PC_end)
	    continue;
	}
    }
}



void print_intlist (IntList * il)
{
  IntList *tmpil;

  printf ("\nINTLIST: ");
  for (tmpil = il; tmpil; tmpil = tmpil->next)
    printf ("%5d", tmpil->item);
}


/********
 * Funzione ricorsiva che attua la propagazione inversa per determinare
 * il valore di una variabile numerica
 *******/

float
ri_eval_comp_var (CompositeNumVar * cv, int index ,float *max_values,float *min_values,Bool Sign)
{
  float tmp, cv_value;
  /* molto simile alla evaluate_exp */
  /*attenzione: deve lavorare sui value before... per poi aggiornare tutto assieme!! */
  switch (cv->operator)
    {
    case FIX_NUMBER:
    case VARIABLE_OP:
      if(Sign)
	return max_values[index];
      else
	return min_values[index];
      break;
    case MUL_OP:
      return ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,Sign) *	ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,Sign);
      break;
    case DIV_OP:
      tmp = ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,!Sign);
      if (tmp == 0)
	printf ("\n\nWARNING: Division by zero in ri_eval_comp_var\n\n");
      return ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,Sign) / tmp;
      break;
    case PLUS_OP:
      return ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,Sign) +	ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,Sign);
      break;
    case MINUS_OP:
      return ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,Sign) -	ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,!Sign);
      break;
    case UMINUS_OP:
      return -ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,!Sign);
      break;
  
    case GREATER_THAN_OP:
      cv_value = (ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,TRUE) > ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,FALSE));
      return cv_value;
    case GREATER_OR_EQUAL_OP:
      cv_value = (ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,TRUE) >= ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,FALSE));
    
      return cv_value;
    case LESS_THAN_OP:
      cv_value = (ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,FALSE) < ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,TRUE));
      
      return cv_value;
    case LESS_THAN_OR_EQUAL_OP:
      cv_value = (ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,FALSE ) <= ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,TRUE));
      
      return cv_value;

    case INCREASE_OP:
      return (ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,TRUE ) + ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,TRUE));
    case DECREASE_OP:
      return (ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,TRUE ) - ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,TRUE));
    case SCALE_UP_OP:
      return (ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,TRUE ) * ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,TRUE));
    case SCALE_DOWN_OP:
      return (ri_eval_comp_var (&(gcomp_var[cv->first_op]), cv->first_op,max_values,min_values,TRUE ) / ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,TRUE));
    case ASSIGN_OP:
      return  ri_eval_comp_var (&(gcomp_var[cv->second_op]), cv->second_op,max_values,min_values,TRUE);
    default:
      MSG_ERROR ("\nOperator not yet supported in expression evaluation\n\n");
      printf("Operator: %d \n\n",cv->operator);
      exit (1);
      return -1;
      break;
    }

  return 0;
}




/********
 * Funzione che mi dice se l'inserimento dell'azione di indice action_pos a livello 
 * down_level rende supportata la preco numerica di indice index a livello level
 ********/

Bool does_action_support_numeric_precond_in_down_level(int index,int action_pos, int level, int down_level)
{



  int act_num,k,j;
  
  DescNumEff *numeric_effect;
  static float *num_value2=NULL;
  static int *modifie=NULL;

  if (!CHECK_ACTION_POS(action_pos, down_level))
    return FALSE;

  if (modifie==NULL)
    modifie = calloc(gnum_block_compvar, sizeof(int));
  if (num_value2 == NULL)
    num_value2= (float*) calloc(gnum_comp_var, sizeof (float));

 
  if(down_level<(level-1))
    {

      act_num=GET_ACTION_POSITION_OF_LEVEL(down_level);
      if(act_num<0)
	return TRUE;

      if(!gef_conn[act_num].is_numeric)
	return TRUE;

      for(k=0;k<gef_conn[act_num].num_numeric_effects;k++)
	{
	  numeric_effect = &gef_conn[act_num].numeric_effects[k];

	 if ((*numeric_effect).lval==gcomp_var[index].first_op)
	   {
	   
	    break;
	   }
	  
	}

      if(k==gef_conn[act_num].num_numeric_effects || k==0)
	return TRUE;
     

    }
 



  memcpy(num_value2, vectlevel[down_level]->numeric->values, sizeof (float) * gnum_comp_var);
  
 
  for(k=0;k<gef_conn[action_pos].num_numeric_effects;k++)
    {	   
      numeric_effect = &gef_conn[action_pos].numeric_effects[k];
      if ((*numeric_effect).is_at_start)
	{
	  eval_comp_var_non_recursive_effects ((*numeric_effect).index,num_value2,num_value2,0,0);	
	  
	}
    }
  
	                                                     
  
  for(k=0;k<gef_conn[action_pos].num_numeric_effects;k++)
    {	   
      numeric_effect = &gef_conn[action_pos].numeric_effects[k];
      if (!((*numeric_effect).is_at_start))
	{
	  eval_comp_var_non_recursive_effects ((*numeric_effect).index,num_value2,num_value2,0,0);	
	  
	}
      
    }
  
 
  
  for(j=down_level;j<level;j++)
    {
     

      act_num=GET_ACTION_POSITION_OF_LEVEL(j);
      if(act_num<0)
	continue;
      
      if(!gef_conn[act_num].is_numeric)
	continue;
  
      for(k=0;k<gnum_block_compvar;k++)
	modifie[k] = vectlevel[j]->numeric->modified_vars_start[k] | 
	  vectlevel[j]->numeric->modified_vars_end[k];
      
      
      if(!(GET_BIT(modifie,index)))
	continue;
      
      
      for(k=0;k<gef_conn[act_num].num_numeric_effects;k++)
	{	   
	  numeric_effect = &gef_conn[act_num].numeric_effects[k];
	  if ((*numeric_effect).is_at_start)
	    {
	      if((gcomp_var_effects[(*numeric_effect).index].operator==ASSIGN_OP) &&  ((*numeric_effect).lval==gcomp_var[index].first_op))
		return FALSE;

	      eval_comp_var_non_recursive_effects ((*numeric_effect).index,num_value2,num_value2,0,0);	
	      
	    }
		 
	}
	     
      
      for(k=0;k<gef_conn[act_num].num_numeric_effects;k++)
	{	   
	  numeric_effect = &gef_conn[act_num].numeric_effects[k];
	  if (!((*numeric_effect).is_at_start))
	    {
	     if((gcomp_var_effects[(*numeric_effect).index].operator==ASSIGN_OP) &&  ((*numeric_effect).lval==gcomp_var[index].first_op))
		return FALSE;

	      eval_comp_var_non_recursive_effects ((*numeric_effect).index,num_value2,num_value2,0,0);	
	      
	    }
	  
	}
    }
  
  if(ri_eval_comp_var (&gcomp_var[index],index ,num_value2,num_value2,TRUE)>0.5)
    return TRUE;
	     
  return FALSE;



}








