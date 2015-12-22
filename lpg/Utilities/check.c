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
 * File: check.c
 * Description: check functions.
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/





#include <math.h>
#include <values.h>

#ifdef __WINLPG__
#include <time.h>
#endif

#include "lpg.h"
#include "ActionSubgraph.h"
#include "numeric.h"
#include "utilities.h"
#include "LpgOutput.h"
#include "output.h"
#include "derivedpred.h"
#include "inst_utils.h"
#include "LpgTime.h"


extern int total_ft_ef_mutex, total_ef_ft_mutex, total_ef_ef_mutex, total_ft_ft_mutex;


/****************************************
        EFFETTI CONDIZIONALI
***************************************/


/******************************************************************************
 *                               PROTOTYPE                                    *
 ******************************************************************************/

/******************************************************************************
 *                             GLOBAL VARIABLES                               *
 ******************************************************************************/

char delimitatore[] = "*******************************************************************************";

/******************************************************************************
 *                                FUNCTION                                    *
 ******************************************************************************/

/*
-----------------------------------------------------------------
	DESCRIPTION	: Verifica dell'allocazione di vettori
	PARAMETER	:
	RETURN		:
-----------------------------------------------------------------
*/
static void test_vect(int *vect, int num)
{
	if ((vect == NULL) && (num != 0)) {
		fprintf(stderr, "Array con %d elementi e puntatore == NULL\n", num);
		exit(1);
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Verifica dell'allocazione di specialfacts
	PARAMETER	:
	RETURN		:
-----------------------------------------------------------------
*/
static void test_sf(SpecialFacts *sf)
{
	if (sf == NULL)
		return;

	test_vect(sf->PC_overall, sf->num_PC_overall);
	test_vect(sf->PC_end, sf->num_PC_end);
	test_vect(sf->A_start, sf->num_A_start);
	test_vect(sf->D_start, sf->num_D_start);
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Verifica se un fatto è presente nella
			  lista dei fatti
	PARAMETER	: fct_list	* a lista fatti
			  num_fct	numero fatti
			  fct		fatto da trovare
	RETURN		: TRUE	Fatto presente
			  FALSE	Fatto non presente
-----------------------------------------------------------------
*/
static int find_fct(int *fct_list, int num_fct, int fct)
{
	int	*p;

	for (p = fct_list; p < &fct_list[num_fct]; p++)
		if (*p == fct)
			return(TRUE);

	return(FALSE);
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Verifica della presenza nelle condizioni
			  dei CondEfConn dei fatti nelle corrette
			  posizioni
	PARAMETER	: cef	* a effetto condizionale istanziato
			  pln	* a descrizione precondizioni effetto
			  	condizionale
	RETURN		:
-----------------------------------------------------------------
*/
static void test_pddl2_cond_condition(CondEfConn *cef, PlNode *pln)
{
	PlNode	*test_pln;
	PlNode	*e;
	int	only_one;

	if (pln == NULL) {
		fprintf(stderr, "Precondizioni dell'effetto condizionale %d = NULL\n", cef - gcondef_conn);
		exit(1);
	}

	if (pln->connective == AND) {
		pln = pln->sons;
		only_one = FALSE;
	} else {
		only_one = TRUE;
	}

	for (e = pln; e; e = e->next) {
		test_pln = e;
		switch(e->connective) {
		case AT_START_CONN:
			test_pln = e->sons;
		case BIN_COMP:
			if (!is_bool_fact(test_pln)) {		// fatti numerici
				if (!find_fct(cef->PC, cef->num_PC, -index_in_cvars_of_expression(test_pln->sons, cef->ef))) {
					fprintf(stderr, "Condizione numerica AT_START non trovata\n");
					print_PlNode(test_pln, 0);
					exit(1);
				}
			}
			break;

		case AT_END_CONN:
			test_pln = e->sons;
			if (!is_bool_fact(test_pln)) {	// fatti booleani
				if (!find_fct(cef->sf->PC_end,
					cef->sf->num_PC_end,
					-index_in_cvars_of_expression(test_pln->sons, cef->ef))) {
					fprintf(stderr, "Condizione numerica AT_END non trovata\n");
					print_PlNode(test_pln, 0);
					exit(1);
				}
			}
			break;

		case OVER_ALL_CONN:
			test_pln = e->sons;
			if (!is_bool_fact(test_pln)) {	// fatti booleani
				if (!find_fct(cef->sf->PC_overall,
					cef->sf->num_PC_overall,
					-index_in_cvars_of_expression(test_pln->sons, cef->ef))) {
					fprintf(stderr, "Condizione numerica OVERALL non trovata\n");
					print_PlNode(test_pln, 0);
					exit(1);
				}
			}
			break;

		case ATOM:
		case NOT:
			break;

		default:
			fprintf(stderr, "Fatto non valido\n");
			print_PlNode(e, 0);
			exit(1);
		}

		if (only_one == TRUE)
			break;		// fine ciclo
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Verifica della presenza negli effetti
			  dei CondEfConn dei fatti nelle corrette
			  posizioni
	PARAMETER	: cef	* a effetto condizionale istanziato
			  pln	* a descrizione effetto condizionale
	RETURN		:
-----------------------------------------------------------------
*/
static void test_pddl2_cond_effect(CondEfConn *cef, PlNode *pln)
{
	PlNode	*test_pln;
	PlNode	*e;
	int	num_fct;
	int	*fct;

	if (pln == NULL) {
		fprintf(stderr, "Effetti dell'effetto condizionale %d = NULL\n", cef - gcondef_conn);
		exit(1);
	}

	if (pln->connective == AND)
		pln = pln->sons;

	for (e = pln; e; e = e->next) {
		test_pln = e;
		switch(e->connective) {
		case AT_START_CONN:
			test_pln = e->sons;
			if (is_bool_fact(test_pln)) {	// fatti booleani A_start
				switch (test_pln->connective) {
				case NOT:
					test_pln = test_pln->sons;
					fct = cef->sf->D_start;
					num_fct = cef->sf->num_D_start;
					break;
				case ATOM:
					fct = cef->sf->A_start;
					num_fct = cef->sf->num_A_start;
					break;
				default:
					fprintf(stderr, "Fatto non valido\n");
					print_PlNode(test_pln, 0);
					exit(1);
				}

				if (get_fct_pos_from_plnode(test_pln, cef->plop, cef->op, fct, num_fct) == -1) {
					fprintf(stderr, "Effetto AT_START non trovato\n");
					print_PlNode(test_pln, 0);
					exit(1);
				}
			} else {	// fatti numerici A_start
				if (!find_fct(cef->sf->A_start,
					cef->sf->num_A_start,
					-index_in_cvars_of_expression(test_pln, cef->ef))) {
					fprintf(stderr, "Effetto numerico AT_START non trovato\n");
					print_PlNode(test_pln, 0);
					exit(1);
				}
			}
			break;

		case AT_END_CONN:
			test_pln = e->sons;
		case ATOM:
		case NOT:
			if (is_bool_fact(test_pln)) {	// fatti booleani A
				switch (test_pln->connective) {
				case NOT:
					test_pln = test_pln->sons;
					fct = cef->D;
					num_fct = cef->num_D;
					break;
				case ATOM:
					fct = cef->A;
					num_fct = cef->num_A;
					break;
				default:
					fprintf(stderr, "Fatto non valido\n");
					print_PlNode(test_pln, 0);
					exit(1);
				}

				if (get_fct_pos_from_plnode(test_pln, cef->plop, cef->op, fct, num_fct) == -1) {
					fprintf(stderr, "Effetto AT_END non trovato\n");
					print_PlNode(test_pln, 0);
					exit(1);
				}
			} else {	// fatti numerici A
				if (!find_fct(cef->A, cef->num_A, -index_in_cvars_of_expression(test_pln, cef->ef))) {
					fprintf(stderr, "Effetto numerico AT_START non trovato\n");
					print_PlNode(test_pln, 0);
					exit(1);
				}
			}
			break;

		case INCREASE_CONN:
		case DECREASE_CONN:
		case SCALE_UP_CONN:
		case SCALE_DOWN_CONN:
		case ASSIGN_CONN:
			if (!find_fct(cef->A, cef->num_A, -index_in_cvars_of_expression(test_pln, cef->ef))) {
				fprintf(stderr, "Effetto numerico non trovato\n");
				print_PlNode(test_pln, 0);
				exit(1);
			}
			break;

		default:
			fprintf(stderr, "Fatto non valido\n");
			print_PlNode(e, 0);
			exit(1);
		}
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Verifica della presenza nel PlOperator
			  del CondEfConn passato
	PARAMETER	: cef	* a descrizione effetto condizionale
	RETURN		: PlNode che descrive l'effetto condizionale
			  NULL	non trovato
-----------------------------------------------------------------
*/
static PlNode *test_find_cond_in_pddl2(CondEfConn *cef)
{
	PlNode		*effects;
	PlNode		*e;
	PlNode		*pln;
	int		num_cond_effect;
	int		trovato;

	effects = cef->plop->effects;
	if (effects == NULL) {
		fprintf(stderr, "gcondef_conn[%d].plop->effects == NULL\n", cef - gcondef_conn);
		exit(1);
	}

	effects = cef->plop->effects;
	if (effects->connective == AND)
		effects = effects->sons;

	pln = NULL;
	trovato = 0;
	num_cond_effect = 0;
	// per ogni effetto dell'azione
	for (e = effects; e; e = e->next) {
		if (e->connective == WHEN) {
			if (get_condeffect_pln_pos(cef) == num_cond_effect) {
				printf("Effetto condizionale %d trovato in Pl2Operator\n", cef - gcondef_conn);
				trovato++;
				pln = e;
			}
			num_cond_effect++;
		}
	}
	if (trovato != 1) {
		fprintf(stderr, "Effetto condizionale %d trovato %d volte in Pl2Operator\n", cef - gcondef_conn, trovato);
		print_PlNode(cef->plop->effects, 0);
		exit(1);
	}

	return(pln);
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Verifica della presenza nei CondEfConn
			  dei fatti nelle corrette posizioni
	PARAMETER	:
	RETURN		:
-----------------------------------------------------------------
*/
static void test_pddl2_cond_action()
{
	CondEfConn	*cef;
	PlNode		*pln;

	for (cef = gcondef_conn; cef < &gcondef_conn[gnum_condef_conn]; cef++) {
		if (cef->plop == NULL) {
			fprintf(stderr, "gcondef_conn[%d].plop == NULL\n", cef - gcondef_conn);
			exit(1);
		}
		test_vect(cef->PC, cef->num_PC);
		test_vect(cef->A, cef->num_A);
		test_vect(cef->D, cef->num_D);
		test_sf(cef->sf);

		pln = test_find_cond_in_pddl2(cef);
		test_pddl2_cond_condition(cef, pln->sons);
		test_pddl2_cond_effect(cef, pln->sons->next);
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Test dell'istanziazione degli effetti
			  condizionali
	PARAMETER	:
	RETURN		:
-----------------------------------------------------------------
*/
void test_cond_effect()
{
	printf("\n\n%s\n", delimitatore);
	printf("Inizio sezione debug effetti condizionali\n\n");

	test_pddl2_cond_action();

	printf("\nFine sezione debug effetti condizionali\n");
	printf("%s\n", delimitatore);
}





void check_prev_and_next_links(void) {

  int indlevel, nlev, last = -1, prev, next;

  printf("\n\nCheck previous and next levels links (levels : %d) ...", GpG.curr_plan_length);

  for (indlevel = 0; indlevel < GpG.curr_plan_length; indlevel++) {

    prev = get_prev(indlevel);
    next = get_next(indlevel);

    if (prev != last)
       printf("\nError level %d : previous is %d, should be %d", indlevel, prev, last);

    if ((indlevel == 0) || CHECK_ACTION_OF_LEVEL(indlevel))
      last = indlevel;

    for (nlev = indlevel + 1; nlev < next; nlev++)
      if (CHECK_ACTION_OF_LEVEL(nlev))
        printf("\nError level %d : next is %d, should be %d", indlevel, next, nlev);

    if (nlev < next)
      continue;

    if (next >= GpG.curr_plan_length)
      continue;

    if(!CHECK_ACTION_OF_LEVEL(next))
      printf("\nError level %d : next is an empty level (%d)", indlevel, next);

  }

}



/**
 * Confronta FT_FT_mutex con la temp_mutex per vedere se ci sono differenze
 **/
int check_ft_ft_mutex(int **temp_ft_ft_mutex, int **or_mutex) {

  int i, j, k;
  int res = 0;

  for (i = 0; i < gnum_ft_conn; i++) {
    for (j = 0; j < gnum_ft_block; j++) {
      if (temp_ft_ft_mutex[i][j] == or_mutex[i][j]) {
	continue;
      }
      
      printf("\n Fact mutex ERROR");
      fflush(stdout);
      
      for (k = 0; k < gnum_ft_conn; k++) {
	if ((GET_BIT(temp_ft_ft_mutex[i], k)) != (GET_BIT(or_mutex[i], k))) {
	  
	  printf("\nMutex error, facts %d %s - %d ",i , print_ft_name_string(i, temp_name), k);
	  print_ft_name(k);
	  printf("  Should%sbe mutex.", (GET_BIT(or_mutex[i], k))?" ":" not ");
	  fflush(stdout);
	  
	  res++;
	}
      }
      break;
    }
  }

  printf("\n done. %d ERRORS FOUND.", res);
  fflush(stdout);
 
  return res;

}


int
check_time_and_length (int plan_ops_num)
{
  float elapsed_time = 0;

#ifndef __WINLPG__
  struct tms end_time;
#else
  clock_t end_time;
#endif

/*verifica lunghezza piano*/
  if ((gcmd_line.max_plan_ops != 0)
      && (plan_ops_num >= gcmd_line.max_plan_ops))
    {
      printf ("\nError: max plan length reached\n\n");
      exit (1);
    }
/*verifica tempo impiegato*/
  times (&end_time);

#ifndef __WINLPG__
  elapsed_time = (float) ((end_time.tms_utime - glob_start_time.tms_utime +
			   end_time.tms_stime -
			   glob_start_time.tms_stime) / 100.0);
#else
  elapsed_time = DeltaTime(glob_start_time, end_time);
#endif

  if ((gcmd_line.max_cpu_time != 0)
      && (elapsed_time >= gcmd_line.max_cpu_time))
    {
      printf ("\nError: max cpu-time reached\n\n");
      exit (1);
    }
  return 1;
}



void check_rules_at(int level) {

  int i, j, c;

  for (i = 0; i < gnum_ft_conn; i++) {
    if (vectlevel[level]->fact[i].w_is_derived_true > 0) {
      c = 0;
      for (j = 0; j < gft_conn[i].num_dp_A; j++) {
	c += (GET_BIT(vectlevel[level]->active_rules, gft_conn[i].dp_A[j]) != 0);
      }
      if (c != vectlevel[level]->fact[i].w_is_derived_true)
	printf("\n\nEEE: Level %d Fact: (%d) %s has derived_true %d but count %d", level, i, print_ft_name_string(i, temp_name), vectlevel[level]->fact[i].w_is_derived_true, c);
    }
  }
  
}

void compare_rules_and_derived_at(int l1, int l2) {
  int i, j, c1, c2;
  
  for (i = 0; i < gnum_ft_conn; i++) {
    if (vectlevel[l1]->fact[i].w_is_derived_true != vectlevel[l2]->fact[i].w_is_derived_true) {
      printf("\n\nEEE: Fact (%d) : %s Level %d: %d Leve %d: %d", i, print_ft_name_string(i, temp_name), l1, vectlevel[l1]->fact[i].w_is_derived_true, l2, vectlevel[l2]->fact[i].w_is_derived_true);
      c1 = c2 = 0;
      for (j = 0; j < gft_conn[i].num_dp_A; j++) {
	c1 += (GET_BIT(vectlevel[l1]->active_rules, gft_conn[i].dp_A[j]) != 0);
      	c2 += (GET_BIT(vectlevel[l2]->active_rules, gft_conn[i].dp_A[j]) != 0);
      }
      printf("\nActive rules : Level %d: %d Level %d: %d", l1, c1, l2, c2);
    }
  }

  for (i = 0; i < gnum_dp_conn; i++) {
    if ((GET_BIT(vectlevel[l1]->active_rules, i) != 0) != (GET_BIT(vectlevel[l2]->active_rules, i) != 0))
      printf("\n\nEEE: RULE (%d) : Level %d: %d Level %d: %d", i, l1, GET_BIT(vectlevel[l1]->active_rules, i), l2, GET_BIT(vectlevel[l2]->active_rules, i));
  }

}




// check plan for durative action
int
check_plan (int max_time)
{
  int level, pos, true, error, temp;
  unsigned int uid_block, uid_mask;
  FctNode_list fact;
  NoopNode_list noop;
  FtConn *vertex_noop;
  int num_dp;
  int *fact_vect = NULL, *dp = NULL, i, j;
  
  if (GpG.derived_predicates) 
    fact_vect = (int *)calloc(gnum_ft_block, sizeof(int));

  /* Se non e' settato __TEST__ non fa niente */

  if (max_time != GpG.curr_plan_length)
    printf ("\nCheck Plan max_time error... %d %d", max_time,
	    GpG.curr_plan_length);
  max_time = GpG.curr_plan_length;

  printf ("\nCheck Plan... %s:%d, max %d", __FILE__, __LINE__,
	  GpG.curr_plan_length);

  for (level = 0; level <= max_time && level < GpG.max_plan_length; level++)

    {
      
      if (GpG.derived_predicates
	  && (GpG.derived_pred_in_preconds || (level == GpG.curr_plan_length))) {
	memcpy(fact_vect, vectlevel[level] -> fact_vect, gnum_ft_block * sizeof(int));
        num_dp = calc_all_derived_predicates(level, RESET_ON, &dp);
	if (num_dp) {
	  for (i = 0; i <= gnum_ft_conn; i++)
	    if (gft_conn[i].fact_type == IS_DERIVED) {
	      if (GET_BIT(vectlevel[level] -> fact_vect, i) != (vectlevel[level]->fact[i].w_is_true != 0))
		printf("\nLEVEL %d - Derived Fact error : %s", level, print_ft_name_string(i, temp_name));
	      if ((GET_BIT(vectlevel[level] -> fact_vect, i) != 0) != (GET_BIT(fact_vect, i) != 0)) {
		printf("\nLevel %d :: derived fact error : fact ", level);
		print_ft_name(i);
		printf("(%d) is %s.", i, (GET_BIT(fact_vect, i) != 0)?"TRUE should be FALSE":"FALSE should be TRUE");
		for (j = 0; j < gft_conn[i].num_dp_A; j++) {
		  printf("\nPRECONDIZIONI : ");
		  for (pos = 0; pos < gdp_conn[gft_conn[i].dp_A[j]].num_PC; pos++) {
		    printf("[%d]", gdp_conn[gft_conn[i].dp_A[j]].PC[pos]);
		    print_ft_name(gdp_conn[gft_conn[i].dp_A[j]].PC[pos]);
		    printf(" (%d) %d ", (GET_BIT(fact_vect, gdp_conn[gft_conn[i].dp_A[j]].PC[pos])?1:0),
			   (GET_BIT(vectlevel[level]->fact_vect, gdp_conn[gft_conn[i].dp_A[j]].PC[pos])?1:0));
		  }	
		}
		printf(" ...fixed!");
	      }
	    }
	  free(dp);
	  dp = NULL;
	}
      }

      if (vectlevel[level]->modified || vectlevel[level]->level != level)
	printf ("\n MODIFIED %d, vectlevel %d, level %d",
		vectlevel[level]->modified, vectlevel[level]->level, level);
      if (vectlevel[level]->level != level)

	{
	  printf ("\n ERROR level %d\n", level);
	  exit (0);
	}
      for (pos = 0; pos < gnum_ft_conn; pos++)
	if (CHECK_FACT_POS (pos, level))

	  {
	    error = 0;
	    fact = &vectlevel[level]->fact[pos];
	    uid_block = GUID_BLOCK (pos);
	    uid_mask = GUID_MASK (pos);
	    
	    if (gft_conn[pos].fact_type != IS_DERIVED)
	    if (fact->w_is_true && level > 0)
	      {
		temp = 0;

		// Check if it is supported
		if (is_fact_in_additive_effects
		    (GET_ACTION_POSITION_OF_LEVEL (level - 1), pos))
		  temp++;
		if (CHECK_NOOP_POS (pos, level - 1))

		  {
		    if (CONVERT_NOOP_TO_NODE (pos, level - 1)
			&& CONVERT_NOOP_TO_NODE (pos, level - 1)->w_is_used)
		      temp++;
		  }

		else
		  if (is_fact_in_additive_effects_start
		      (GET_ACTION_POSITION_OF_LEVEL (level - 1), pos)
		      &&
		      !is_fact_in_delete_effects
		      (GET_ACTION_POSITION_OF_LEVEL (level - 1), pos))
		  temp++;
		if (temp != fact->w_is_true)
		  printf ("\nFact error %s w_is_true %d count %d level %d ",
			  print_ft_name_string (pos, temp_name),
			  fact->w_is_true, temp, level);
	      }
	    if (fact->w_is_goal && level < max_time)

	      {	
		temp = 0;

		// Check if w_is_goal is ok
		if (CHECK_ACTION_OF_LEVEL (level)
		    &&
		    is_fact_in_preconditions (GET_ACTION_POSITION_OF_LEVEL
					      (level), pos)
		    && GET_ACTION_OF_LEVEL (level)->w_is_goal)
		  temp++;
		if (CHECK_ACTION_OF_LEVEL (level)
		    &&
		    is_fact_in_preconditions_overall
		    (GET_ACTION_POSITION_OF_LEVEL (level), pos)
		    && GET_ACTION_OF_LEVEL (level)->w_is_goal
		    && CONVERT_NOOP_TO_NODE (pos,
					       level)->w_is_overall !=
		    ADD_DEL
		    && CONVERT_NOOP_TO_NODE (pos,
					       level)->w_is_overall !=
		    ADD_NDEL)
		  temp++;
		if (CHECK_NOOP_POS (pos, level)
		    && CONVERT_NOOP_TO_NODE (pos, level)->w_is_goal)
		  temp++;
		if (level > 1 && CHECK_ACTION_OF_LEVEL (level - 1)
		    &&
		    is_fact_in_preconditions_end
		    (GET_ACTION_POSITION_OF_LEVEL (level), pos)
		    && GET_ACTION_OF_LEVEL (level)->w_is_goal
		    && CONVERT_NOOP_TO_NODE (pos,
					       level)->w_is_overall !=
		    DEL_ADD
		    && CONVERT_NOOP_TO_NODE (pos,
					       level)->w_is_overall !=
		    ADD_NDEL
		    &&
		    !is_fact_in_additive_effects
		    (GET_ACTION_POSITION_OF_LEVEL (level - 1), pos))
		  temp++;

		if (!GpG.derived_predicates) {
		if (level >= GpG.curr_plan_length)

		  {
		    if (fact->w_is_goal > 1
			&&
			!is_fact_in_preconditions_end
			(GET_ACTION_POSITION_OF_LEVEL (level), pos))
		      printf
			("\nFact error %s Goal  w_is_goal %d count %d level %d ",
			 print_ft_name_string (pos, temp_name),
			 fact->w_is_goal, temp, level);
		  }

		else if (temp != fact->w_is_goal)

		  {
		    printf ("\nFact error %s w_is_goal %d count %d level %d ",
			    print_ft_name_string (pos, temp_name),
			    fact->w_is_goal, temp, level);
		    if (GET_ACTION_OF_LEVEL (level)->w_is_goal
			&&
			(is_fact_in_preconditions
			 (GET_ACTION_POSITION_OF_LEVEL (level), pos)
			 ||
			 is_fact_in_preconditions_overall
			 (GET_ACTION_POSITION_OF_LEVEL (level), pos)))
		      printf
			("\nAction at level %d:   name %s w_is_goal %d pos %d",
			 level,
			 print_op_name_string (GET_ACTION_OF_LEVEL (level)->
					       position, temp_name),
			 GET_ACTION_OF_LEVEL (level)->w_is_goal,
			 GET_ACTION_OF_LEVEL (level)->position);
		    if (CHECK_ACTION_OF_LEVEL (level) && level > 1
			&&
			is_fact_in_preconditions_end
			(GET_ACTION_POSITION_OF_LEVEL (level), pos))
		      printf ("Action at level %d:   name %s %d %d", level,
			      print_op_name_string (GET_ACTION_OF_LEVEL
						    (level)->position,
						    temp_name),
			      GET_ACTION_OF_LEVEL (level)->w_is_goal,
			      GET_ACTION_OF_LEVEL (level)->position);
		    if (CONVERT_NOOP_TO_NODE (pos, level)->w_is_goal)
		      printf
			("\nNoop:   name %s  w_is_goal %d pos %d min-level %d",
			 print_noop_name_string (pos, temp_name),
			 CONVERT_NOOP_TO_NODE (pos, level)->w_is_goal,
			 CONVERT_NOOP_TO_NODE (pos, level)->position,
			 gft_conn[pos].level);
		  }
		}
	      }
	    true = (vectlevel[level]->fact_vect[uid_block] & uid_mask);
	    if ((fact->w_is_true != 0) != (true != 0))
	      printf ("\nFact error %s w_is_true %d bit %d  level %d position %d",
		      print_ft_name_string (pos, temp_name), fact->w_is_true,
		      true, level, pos);
	    true = vectlevel[level]->prec_vect[uid_block] & uid_mask;
	    if ((fact->w_is_goal > 0) != (true != 0))
	      printf ("\nFact error %s w_is_goal %d bit %d level %d ",
		      print_ft_name_string (pos, temp_name), fact->w_is_goal,
		      true, level);
	    true = vectlevel[level]->false_crit_vect[uid_block] & uid_mask;
	    if ((fact->w_is_goal && fact->w_is_true == 0) != (true != 0))
	      printf
		("\nFact error False critic %s w_is_goal %d w_is_true %d bit %d  level %d",
		 print_ft_name_string (pos, temp_name), fact->w_is_goal,
		 fact->w_is_true, true, level);
	    true = vectlevel[level]->true_crit_vect[uid_block] & uid_mask;
	    if ((fact->w_is_goal && fact->w_is_true == 1) != (true != 0))
	      printf
		("\nFact error True critic %s w_is_goal %d w_is_true %d bit %d level %d ",
		 print_ft_name_string (pos, temp_name), fact->w_is_goal,
		 fact->w_is_true, true, level);
	  }
      if (level >= max_time)
	break;
      for (pos = 0; pos < gnum_ft_conn; pos++)
	if (CHECK_NOOP_POS (pos, level))

	  {
	    error = 0;
	    noop = &vectlevel[level]->noop_act[pos];
	    vertex_noop = &gnoop_conn[pos];
	    uid_block = GUID_BLOCK (pos);
	    uid_mask = GUID_MASK (pos);
	    true = vectlevel[level]->noop_act_vect[uid_block] & uid_mask;
	    if ((noop->w_is_used > 0) != (true != 0))
	      printf ("\nNoop error %s w_is_used %d bit %d  level %d",
		      print_noop_name_string (pos, temp_name), noop->w_is_used,
		      true, level);
	    true = vectlevel[level]->noop_prec_act_vect[uid_block] & uid_mask;
	    if ((noop->w_is_goal > 0) != (true != 0))
	      printf ("\nNoop error %s w_is_goal %d bit %d  level %d",
		      print_noop_name_string (pos, temp_name),
		      noop->w_is_goal, true, level);
	    if (noop->w_is_used
		&& (noop->w_is_overall == DEL_ADD
		    || noop->w_is_overall == DEL_NADD))
	      printf
		("\nNoop error: DEL_START noop used -  noop %s w_is_used %d w_is_overall %d level %d",
		 print_noop_name_string (pos, temp_name), noop->w_is_used,
		 noop->w_is_overall, level);
	    if (!noop->w_is_used
		&& (noop->w_is_overall == ADD_DEL
		    || noop->w_is_overall == ADD_NDEL))
	      printf
		("\nNoop error: ADD_START noop not used -  noop %s w_is_used %d w_is_overall %d level %d",
		 print_noop_name_string (pos, temp_name), noop->w_is_used,
		 noop->w_is_overall, level);
	    if (!noop->w_is_used && noop->w_is_overall == NADD_DEL
		&& vectlevel[level]->fact[pos].w_is_true)
	      printf
		("\nNoop error: NADD_DEL noop used fact true -  noop %s w_is_used %d w_is_overall %d level %d",
		 print_noop_name_string (pos, temp_name), noop->w_is_used,
		 noop->w_is_overall, level);
	    if (noop->w_is_used && noop->w_is_overall == NADD_DEL
		&& !vectlevel[level]->fact[pos].w_is_true)
	      printf
		("\nNoop error: NADD_DEL noop used fact false -  noop %s w_is_used %d w_is_overall %d level %d",
		 print_noop_name_string (pos, temp_name), noop->w_is_used,
		 noop->w_is_overall, level);
	  }
    }
  printf ("\n");

  if (GpG.derived_predicates)
    free(fact_vect);
  
  return 0;
}


void
check_action_f ()
{

  int ind, level, posact, posA, posB, type, savelev, i;
  float max_time=0;
  
  for (level = 0; level <= GpG.curr_plan_length; level++)
    {
      /*  Esaminiamo tutti i fatti di ciascun livello */
      for (ind = 0; ind < gnum_ft_conn; ind++)
	{
	  if(vectlevel[level]->fact[ind].w_is_true <= 0)
	    {
	      if (vectlevel[level]->fact[ind].action_f != NULL )
		printf("\nERR 1: act_f :: %s lev %d", print_ft_name_string(vectlevel[level]->fact[ind].position,temp_name), level);
	    }
	  else
	    {
	      if (vectlevel[level]->fact[ind].action_f == NULL && vectlevel[level]->fact[ind].time_f > 0.0)
		printf("\nERR 2: act_f :: %s lev %d", print_ft_name_string(vectlevel[level]->fact[ind].position,temp_name), level);


	      else
		{
		  if (vectlevel[level]->fact[ind].action_f != NULL)
		    {
		      posact = vectlevel[level]->fact[ind].action_f->position;
		      
		      if (!is_fact_in_additive_effects_start(posact,ind) && !is_fact_in_additive_effects(posact,ind) )
			{
			  printf("\nERR 5");
			}
		    }
		}
	      
	    }

	  if(level < GpG.curr_plan_length)
	    {
	    if(vectlevel[level]->noop_act[ind].w_is_used <= 0)
	    {
	      if (vectlevel[level]->noop_act[ind].action_f != NULL )
		printf("\nERR 3: act_f :: %s lev %d", print_ft_name_string(vectlevel[level]->noop_act[ind].position,temp_name), level);
	    }
	  else
	    {
	      if (vectlevel[level]->noop_act[ind].action_f == NULL && vectlevel[level]->noop_act[ind].time_f > 0.0)
		printf("\nERR 4: act_f :: %s lev %d", print_ft_name_string(vectlevel[level]->noop_act[ind].position,temp_name), level);
	      else
		{
		  if (vectlevel[level]->fact[ind].action_f != NULL)
		    {
		      posact = vectlevel[level]->fact[ind].action_f->position;
		      
		      if (!is_fact_in_additive_effects_start(posact,ind) && !is_fact_in_additive_effects(posact,ind) )
			{
			  printf("\nERR 6");
			}
		      /**
		      else
			{
			  for (k = vectlevel[level]->fact[ind].action_f->level; k < level ; k++ )
			    xxxxxxxxxxxxxxxxxx
			}
		      **/
		    }
		}
	      
	    }
	    }
	}
    }


  for(level=0; level < GpG.curr_plan_length; level++)
    {

      savelev=-1;
      max_time=0;

      posA = GET_ACTION_POSITION_OF_LEVEL(level);

      if (posA < 0)
	continue;

      for(i=0; i< level; i++)
	{
	  posB = GET_ACTION_POSITION_OF_LEVEL(i);

	  if (posB < 0)
	    continue;

	  type=get_constraint_type(posB, i, posA, level);

	  if (type == EA_SB) 
	    /** 
		l'azione B deve iniziare dopo la fine dell'azione A
		**
		the action B begins after the end of the action A
	    **/
	    {
	      if (max_time < GET_ACTION_OF_LEVEL(i)->time_f)
		{
		  max_time = GET_ACTION_OF_LEVEL(i)->time_f;
		  savelev = i;
		}
	    }
	  else 
	    {
	      if (type == EA_EB) 
		/** 
		    l'azione B deve finire dopo la fine di A
		    **
		    the action B ends after the end of the action A 
		**/
		{
		  if (max_time < GET_ACTION_OF_LEVEL(i)->time_f - get_action_time (posB, level) )
		    {
		      max_time = GET_ACTION_OF_LEVEL(i)->time_f - get_action_time (posB, level);
		      savelev = i;
		    }
		}
	      else
		if (type == SA_SB) 
		  /** 
		      l'azione B deve iniziare dopo l'inizio di A
		      **
		      the action B begins after the beginning of the action A
		  **/
		  {
		    if (max_time < GET_ACTION_OF_LEVEL(i)->time_f - get_action_time (GET_ACTION_OF_LEVEL(i)->position, *GET_ACTION_OF_LEVEL(i)->level ) )
		      {
			max_time = GET_ACTION_OF_LEVEL(i)->time_f - get_action_time (GET_ACTION_OF_LEVEL(i)->position, *GET_ACTION_OF_LEVEL(i)->level );
			savelev = i;
		      }
		  }
		else
		  {
		    if (type == SA_EB) 
		      /** 
			  l'azione B deve finire dopo l'inizio di A
			  **
			  The action B ends after the beginning of A 
		      **/
		      {
			if (max_time < GET_ACTION_OF_LEVEL(i)->time_f - get_action_time (GET_ACTION_OF_LEVEL(i)->position, *GET_ACTION_OF_LEVEL(i)->level )- get_action_time (posB, level)  )
			  {
			    max_time = GET_ACTION_OF_LEVEL(i)->time_f - get_action_time (GET_ACTION_OF_LEVEL(i)->position, *GET_ACTION_OF_LEVEL(i)->level ) - get_action_time (posB, level) ;
			    savelev = i;
			  }
		      }
		    else
		      {
			if (type == EA_EB__SA_SB)
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
			    if(get_action_time(posB, level ) < get_action_time(GET_ACTION_OF_LEVEL(i)->position, *GET_ACTION_OF_LEVEL(i)->level ))
			      {
				// EA_EB
				if (max_time < GET_ACTION_OF_LEVEL(i)->time_f - get_action_time (posB, level) )
				  {
				    max_time = GET_ACTION_OF_LEVEL(i)->time_f - get_action_time (posB, level);
				    savelev = i;
				  }
			      }
			    else // SA_SB
			      {
				if (max_time < GET_ACTION_OF_LEVEL(i)->time_f - get_action_time (GET_ACTION_OF_LEVEL(i)->position, *GET_ACTION_OF_LEVEL(i)->level ) )
				  {
				    max_time = GET_ACTION_OF_LEVEL(i)->time_f - get_action_time (GET_ACTION_OF_LEVEL(i)->position, *GET_ACTION_OF_LEVEL(i)->level );
				    savelev = i;
				  }
			      }
			  }
			
		      }
		    
		  }
	    }
	}
      if (fabs(max_time + get_action_time (posA, level) - GET_ACTION_OF_LEVEL(level)->time_f) < MIN_DELTA_TIME )
	{
	  if (savelev >0)
	    {
	      if (savelev != *GET_ACTION_OF_LEVEL(level)->action_f->level)
		{
		  printf("\nERR act_f AZ: %s %d lev: %d", print_op_name_string(posA,temp_name), posA, level);
		  printf("ha action_f %s %d lev: %d", print_op_name_string(GET_ACTION_OF_LEVEL(level)->action_f->position,temp_name), GET_ACTION_OF_LEVEL(level)->action_f->position, *GET_ACTION_OF_LEVEL(level)->action_f->level);
		  printf("ma ordinata con %s %d lev: %d", print_op_name_string(GET_ACTION_OF_LEVEL(savelev)->position,temp_name), GET_ACTION_OF_LEVEL(savelev)->position, *GET_ACTION_OF_LEVEL(savelev)->level);
		}
	    }
	  else
	    {
	      if(GET_ACTION_OF_LEVEL(level)->action_f !=NULL)
		printf("Err act_f !=NULL %s %d", print_op_name_string(GET_ACTION_POSITION_OF_LEVEL(level),temp_name),level);
	    }

	}
      /**
      else
	{
	  if (gef_conn[GET_ACTION_POSITION_OF_LEVEL(level)].timed_PC==NULL)
	    printf("\nWarning: %s lev: %d :: maxtime: %.2f time: %.2f", print_op_name_string(posA,temp_name), level, max_time+ get_action_time (posA, level), GET_ACTION_OF_LEVEL(level)->time_f);
	  
	}
	**/


    }
}







/* Verifica dei vincoli temporali del piano parziale */

void
check_temporal_plan ()
{
  int ind, level, indPrec, indlevel, indinc, skip, i, j, k;

  FctNode_list TempFact; 
  ActNode_list infAction, TempAct;

  Timed_list timedFct;



  
  /* Se non e' settato __TEST__ non fa niente */

  printf ("\nCheck temporal plan...");

  /*  Esaminiamo tutti i livelli */
  for (level = 0; level < GpG.curr_plan_length; level++)
    {
      /*  Esaminiamo tutti i fatti di ciascun livello */
      
      for (ind = 0; ind < gnum_ft_conn; ind++)
	{
	  TempFact = &vectlevel[level]->fact[ind];

	  if (TempFact->w_is_true)
	    {

	      if (TempFact->time_f < 0)
		printf
		  ("\nERROR true fact1: time_f %s  level: %d time %.2f",
		   print_ft_name_string(ind,temp_name), level,
		   TempFact->time_f);

	      if (TempFact->time_f == 0.0 && gft_conn[ind].level > 0)
		{

		  for (indlevel = level - 1; indlevel > 0; indlevel--)
		    {

		      if (CHECK_FACT_POS (ind, indlevel) < 0)
			break;

		      if (vectlevel[indlevel]->fact[ind].w_is_true <= 0)
			break;

		      if (vectlevel[indlevel]->fact[ind].time_f > 0)
			break;

		      if (is_fact_in_delete_effects_start
			  (GET_ACTION_POSITION_OF_LEVEL (indlevel), ind)
			  ||
			  is_fact_in_delete_effects
			  (GET_ACTION_POSITION_OF_LEVEL (indlevel), ind))
			break;

		    }

		  skip=FALSE;
		  for(indinc=0; indinc < GpG.num_false_tmd_fa; indinc++)
		    if(TempFact->action_f)
		    if(is_fact_in_preconditions (TempFact->action_f->position, unsup_tmd_facts[indinc]->fact) || is_fact_in_preconditions_overall (TempFact->action_f->position, unsup_tmd_facts[indinc]->fact) ||
		       is_fact_in_preconditions_end (TempFact->action_f->position, unsup_tmd_facts[indinc]->fact))
		      skip=TRUE;

		  if(!skip)
		  if (!is_fact_in_additive_effects_start(GET_ACTION_POSITION_OF_LEVEL (indlevel), ind) || (GET_ACTION_OF_LEVEL (indlevel)->time_f - get_action_time (GET_ACTION_POSITION_OF_LEVEL(indlevel), indlevel)) > 0)
		    printf
		      ("\nERROR true fact2: time_f %s  level: %d time %.2f",
		       print_ft_name_string(ind,temp_name), level,
		       TempFact->time_f);
		}


	      if (TempFact->action_f == NULL && level != 0)
		printf
		  ("\nERRORE true fact: action_f %s  level: %d time %.2f",
		   print_ft_name_string(ind,temp_name), *TempFact->level,
		   TempFact->time_f);
	      else
		if (level != 0 && *TempFact->action_f->level != level-1 )
		  printf("\nERROR true fact: action_f %s  level: %d time %.2f act_level %d",
			     print_ft_name_string(ind,temp_name), *TempFact->level,
			 TempFact->time_f,*TempFact->action_f->level);	
	    }

	  else
	    {
	      if (TempFact->time_f > 0.0
		  &&
		  !(is_fact_in_preconditions
		    (GET_ACTION_POSITION_OF_LEVEL (level), ind)
		    ||
		    is_fact_in_preconditions_overall
		    (GET_ACTION_POSITION_OF_LEVEL (level), ind)
		    ||
		    is_fact_in_preconditions_end (GET_ACTION_POSITION_OF_LEVEL
						  (level), ind)))

		printf
		  ("\nERROR false fact3: time_f %s [%d] level: %d time %.2f",
		   print_ft_name_string(ind,temp_name), ind ,*TempFact->level,
		   TempFact->time_f);

	      if (TempFact->action_f != NULL)
		printf
		  ("\nERROR false fact4: action_f %s  level: %d time %.2f",
		   print_ft_name_string(ind,temp_name), *TempFact->level,
		   TempFact->time_f);
	    }

	  if (TempFact->w_is_true == 1 && TempFact->action_f != NULL
	      && TempFact->time_f != TempFact->action_f->time_f )
	    {
	      skip=FALSE;
	      for(indinc=0; indinc < GpG.num_false_tmd_fa; indinc++)
		if(is_fact_in_preconditions (TempFact->action_f->position, unsup_tmd_facts[indinc]->fact) || is_fact_in_preconditions_overall (TempFact->action_f->position, unsup_tmd_facts[indinc]->fact) ||
		   is_fact_in_preconditions_end (TempFact->action_f->position, unsup_tmd_facts[indinc]->fact))
		  skip=TRUE;

	      if(!skip)
		{
		  printf
		    ("\nERROR 3 fact %s   level: %d time %.2f action_f pos %d action_f time  %.2f  ",
		     print_ft_name_string(ind,temp_name), *TempFact->level,
		     TempFact->time_f, TempFact->action_f->position,
		     TempFact->action_f->time_f);
		  
		  printf (" \n%s level %d w_is_used %d ",
			  print_noop_name_string (TempFact->action_f->position, temp_name),
			  *TempFact->action_f->level, TempFact->action_f->w_is_used);
		}
	    }
	  
	}

      /*  Esaminiamo l'azione del livello */
      ind = GET_ACTION_POSITION_OF_LEVEL (level);

      if (ind >= 0)
	{

	  if ((TempAct = GET_ACTION_OF_LEVEL (level))->w_is_used)
	    {

	      if (TempAct->time_f <= 0.0)
		printf ("\nERROR action used: %s  level: %d time %.2f",
			print_op_name_string(ind,temp_name), *TempAct->level,
			TempAct->time_f);

	      if(TempAct->action_f != NULL && GpG.constraint_type == 0)
		if(TempAct->time_f - get_action_time (ind, level) - TempAct->action_f->time_f > TIME_TOLERANCE || -(TempAct->time_f - get_action_time (ind, level) - TempAct->action_f->time_f) > TIME_TOLERANCE)
		  {
		    printf("\nERROR on action_f value action used: %s level %d stat_time %.10f ", print_op_name_string(ind,temp_name), *TempAct->level, TempAct->time_f - get_action_time (ind, level));
		    printf("preceding action: %s level: %d time_f: %.10f", print_op_name_string(GET_ACTION_POSITION_OF_LEVEL (*TempAct->action_f->level),temp_name), *TempAct->action_f->level, TempAct->action_f->time_f);
		  }
	    }

	  else
	    {
	      if (TempAct->time_f > 0.0)
		printf
		  ("\nERROR action not used: %s  level: %d time %.2f",
		   print_op_name_string(ind,temp_name), *TempAct->level,
		   TempAct->time_f);
	    }

	  /*  Esaminiamo che le azioni nel piano abbiano tempo maggiore o uguale alle proprie precondizioni at_start */
	  for (indPrec = 0; indPrec < gef_conn[ind].num_PC; indPrec++)
	    {
	      if (gef_conn[ind].PC[indPrec] < 0)
		continue;

	      if (TempAct->time_f <
		vectlevel[level]->fact[gef_conn[ind].PC[indPrec]].time_f +
		get_action_time (ind, level) - TIME_TOLERANCE)
	      {
		printf ("\nERROR action used: %s end-time %.2f",
			print_op_name_string (ind, temp_name),
			TempAct->time_f);
		printf ("  with precondition %s at time %.2f in level %d",
			print_ft_name_string (gef_conn[ind].PC[indPrec],
					      temp_name),
			vectlevel[level]->fact[gef_conn[ind].PC[indPrec]].
			time_f, *TempAct->level);
	      }
	    }
	  /*  Esaminiamo che le azioni nel piano abbiano tempo maggiore o uguale alle proprie precondizioni overall */
	  if (gef_conn[ind].sf)
	    for (indPrec = 0; indPrec < gef_conn[ind].sf->num_PC_overall;
		 indPrec++)
	      {
	      if (gef_conn[ind].sf->PC_overall[indPrec] < 0)
		continue;

	      if (TempAct->time_f <
		  vectlevel[level]->fact[gef_conn[ind].sf->
					 PC_overall[indPrec]].time_f +
		  get_action_time (ind, level) - TIME_TOLERANCE)
		{
		  printf ("\nERROR action used: %s end-time %.2f",
			  print_op_name_string (ind, temp_name),
			  TempAct->time_f);
		  printf
		    ("  with precondition %s at time %.2f in level %d",
		     print_ft_name_string (gef_conn[ind].sf->
					   PC_overall[indPrec], temp_name),
		     vectlevel[level]->fact[gef_conn[ind].sf->
					    PC_overall[indPrec]].time_f,
		     *TempAct->level);
		}
	      }
	}

      /*  Esaminiamo che le noop del livello */
      for (ind = 0; ind < GpG.max_num_facts; ind++)
	{
	if(CHECK_NOOP_POS(ind,level))
	  {
	    skip=FALSE;
	    for(indinc=0; indinc < GpG.num_false_tmd_fa; indinc++)
	      if(vectlevel[level]->fact[ind].action_f)
	      if(is_fact_in_preconditions (vectlevel[level]->fact[ind].action_f->position, unsup_tmd_facts[indinc]->fact) || is_fact_in_preconditions_overall (vectlevel[level]->fact[ind].action_f->position, unsup_tmd_facts[indinc]->fact) ||
		 is_fact_in_preconditions_end (vectlevel[level]->fact[ind].action_f->position, unsup_tmd_facts[indinc]->fact))
		skip=TRUE;

	    if(!skip && vectlevel[level]->noop_act[ind].w_is_used && vectlevel[level]->noop_act[ind].time_f<0.0)
	      printf("\nERROR noop %s %d  level %d  time_f %.3f",print_noop_name_string(ind,temp_name), ind, level, vectlevel[level]->noop_act[ind].time_f);
	  }
	}
    }


  /*
    For external timed literals:
    Check actions associated to the timed literals
  */
  for (i=0; i < gnum_timed_facts; i++)
    for (j=0; j < gnum_tmd_interval[i]; j++)
      {
	timedFct = &gtimed_fct_vect[i][j];
	
	for (k=0; k < timedFct->num_act_PC; k++)
	  {	    
	    infAction = GET_ACTION_OF_LEVEL(*timedFct->levels[k]);

	    if (infAction->position <0)
	      {
		printf("\nError TL1: Action at level %d does not exists for %s", *infAction->level, print_ft_name_string(timedFct->position,temp_name));
		continue;
	      }
	    
	    if(!(is_fact_in_preconditions(infAction->position, timedFct->position) || is_fact_in_preconditions_overall(infAction->position, timedFct->position) || is_fact_in_preconditions_end(infAction->position, timedFct->position)))
	      {
		printf("\nError TL2: Action %s at level %d", print_op_name_string(infAction->position,temp_name), *infAction->level);
		printf("has not Timed Literals %s as precondition",print_ft_name_string(timedFct->position,temp_name));
	      }
	  }
      }

  for (i = 0; i < GpG.curr_plan_length; i++) {
    infAction = GET_ACTION_OF_LEVEL(i);
    if ((infAction -> position >= 0) && (infAction -> PC_interval != NULL))
      for (j = 0; j < gnum_timed_facts; j++) {
	if (infAction -> PC_interval[j] >= 0) {
	  timedFct = &gtimed_fct_vect[j][infAction -> PC_interval[j]];
	  for (k = 0; (k < timedFct -> num_act_PC) && (timedFct -> levels[k] != infAction -> level); k++);
	  if (k == timedFct -> num_act_PC)
	    {
	      printf("\nError TL3 : l'azione %s è associata a  ", print_op_name_string(infAction -> position, temp_name));
	      printf(" %s al livello %d", print_ft_name_string(timedFct -> position, temp_name), *infAction -> level);
	      printf(" ma non viceversa.");
	      printf("\nNUM TRY = %d\n", GpG.count_num_try);
	    }
	}
      }
  } 

}



/* Verifichimo che nel vettore delle azioni inserite l'indice e il livello siano gli stessi */

void
check_act_ord_vect ()
{

  int ind;


  for (ind = 0; ind < num_act_ord; ind++)
    if (act_ord_vect[ind] != NULL)
      if (act_ord_vect[ind]->ord_pos != ind)
	printf ("\nERROR ACT_ORD_VECT");

}



/* Verifichiamo che per ogni elemento non nullo della matrice, l'azione sulla riga preceda l'azione sulla colonna */

void
check_matrix ()
{

  int i, j;


  for (i = 0; i < num_act_ord; i++)

    for (j = 0; j < num_act_ord; j++)
      {
	if (mat_ord[i][j] != 0
	    && *act_ord_vect[i]->level >= *act_ord_vect[j]->level)
	  printf ("\nERROR MATRIX CONSTRAINT MANAGEMENT");
      }

}



/* Verifichiamo che la propagation_list sia stata resettata correttamente */

void
check_prop_level_index ()
{

  int ind;


  for (ind = 0; ind <= GpG.curr_plan_length; ind++)
    if (prop_level_index[ind] != -1)
      printf ("\nERROR PROP_LEVEL_INDEX");


}


// numeric

// Verifica prec numeriche
void check_num_prec()
{

  int level, i, el ,position;

  

  for(level=0; level<GpG.curr_plan_length; level++)
    {

      //Check unsatisfied numeric preconds
      if(CHECK_ACTION_OF_LEVEL(level))
	{
	  
	  position=GET_ACTION_POSITION_OF_LEVEL(level);
	  
	  for (i = 0; i < gef_conn[position].num_PC; i++)
	    {
	      el = gef_conn[position].PC[i];
	      if (el < 0)
		{
		if(!is_num_prec_satisfied(-el,level) && vectlevel[level]->numeric->false_position[-el] < 0)
		  {
#ifdef __MY_OUTPUT__
		    printf("\n Error unsup numfact %d lev %d step %d", -el, level, GpG.count_num_try);
#endif
		    insert_unsup_numeric_fact (-el, level);
		  }
		}
	      else
		if(!fact_is_supported (el,level) && vectlevel[level]->fact[el].false_position <0 && 
		   gft_conn[el].fact_type != IS_TIMED)
		  {
		  insert_unsup_fact (&vectlevel[level]->fact[el]);
#ifdef __MY_OUTPUT__
		  printf("\n Error unsup Fact %d lev %d step %d", el, level, GpG.count_num_try);
#endif
		  }
	    }
	      if (gef_conn[position].sf != NULL)
		{
		  for (i = 0; i < gef_conn[position].sf->num_PC_overall; i++)
		    {
		      el = gef_conn[position].sf->PC_overall[i];
		      if (el < 0)
			{
			  if(!is_num_prec_satisfied(-el,level) && vectlevel[level]->numeric->false_position[-el] < 0)
			    {
#ifdef __MY_OUTPUT__
			      printf("\n Error unsup numfact %d lev %d ", -el, level);
#endif
			      insert_unsup_numeric_fact (-el, level );
			    }
			}
		      else
			if(!fact_is_supported (el,level) && vectlevel[level]->fact[el].false_position <0 && 
			   gft_conn[el].fact_type != IS_TIMED)
			  {
			    insert_unsup_fact (&vectlevel[level]->fact[el]);
#ifdef __MY_OUTPUT__
			    printf("\n Error unsup Fact %d lev %d step %d", el, level, GpG.count_num_try);
#endif
			  }
		    }
		      for (i = 0; i < gef_conn[position].sf->num_PC_end; i++)
			{
			  el = gef_conn[position].sf->PC_end[i];
			  if (el < 0)
			    {
			    if(!is_num_prec_satisfied(-el,level) && vectlevel[level+1]->numeric->false_position[-el] < 0)
			      {
#ifdef __MY_OUTPUT__
				printf("\n -numfact %d lev %d ", -el, level);
#endif
				insert_unsup_numeric_fact (-el, level);
			      }

			    }
			  else
			    if(!fact_is_supported (el,level) && vectlevel[level]->fact[el].false_position <0 &&
			       gft_conn[el].fact_type != IS_TIMED)
			      {
				insert_unsup_fact (&vectlevel[level]->fact[el]);
#ifdef __MY_OUTPUT__
				printf("\n Error unsup Fact %d  %s lev %d step %d action of level ", el, print_ft_name_string(el, temp_name), level, GpG.count_num_try);
				print_op_name(vectlevel[level]->action.position);

				my_print_plan_all(GpG.curr_plan_length);
#endif
			      }
			  
			}
		}
	}


    }
}


void
check_consistency (int level)
{
  int i;
  float *values;

  CompositeNumVar *cv;
  values = vectlevel[level]->numeric->values;

  for (i = 0; i < gnum_comp_var; i++)
    {
      cv = &gcomp_var[i];
      switch (cv->operator)
	{
	case MUL_OP:
	  if ((values[i] - (values[cv->first_op] * values[cv->second_op])) >
	      MAX_APPROX)
	    {
	      printf ("\n\n inconsistency in cvars array");
	      printf ("\nop: *");
	      printf ("\nfirst   : %5d:%8f", cv->first_op,
		      values[cv->first_op]);
	      printf ("\nsecond  : %5d:%8f", cv->second_op,
		      values[cv->second_op]);
	      printf ("\ncorrect : %f",
		      values[cv->first_op] * values[cv->second_op]);
	      printf ("\nreported: %f\n\n", values[i]);
	      assert (0);
	      exit (1);
	    }
	  break;
	case DIV_OP:
	  if (values[cv->second_op] == 0)
	    {
	      printf ("\n\n check_consistency: div by 0\n\n");
	      exit (1);
	    }
	  if ((values[i] - (values[cv->first_op] / values[cv->second_op])) >
	      MAX_APPROX)
	    {
	      printf ("\n\n inconsistency in cvars array\n\n");
	      printf ("\nop: /");
	      printf ("\nfirst   : %5d:%8f", cv->first_op,
		      values[cv->first_op]);
	      printf ("\nsecond  : %5d:%8f", cv->second_op,
		      values[cv->second_op]);
	      printf ("\ncorrect : %f",
		      values[cv->first_op] / values[cv->second_op]);
	      printf ("\nreported: %f\n\n", values[i]);
	      assert (0);
	      exit (1);
	    }
	  break;
	case PLUS_OP:
	  if ((values[i] - (values[cv->first_op] + values[cv->second_op])) >
	      MAX_APPROX)
	    {
	      printf ("\n\n inconsistency in cvars array\n\n");
	      printf ("\nop: +");
	      printf ("\nfirst   : %5d:%8f", cv->first_op,
		      values[cv->first_op]);
	      printf ("\nsecond  : %5d:%8f", cv->second_op,
		      values[cv->second_op]);
	      printf ("\ncorrect : %5f",
		      values[cv->first_op] + values[cv->second_op]);
	      printf ("\nreported: %5f\n\n", values[i]);
	      assert (0);
	      exit (1);
	    }
	  break;
	case MINUS_OP:
	  if ((values[i] - (values[cv->first_op] - values[cv->second_op])) >
	      MAX_APPROX)
	    {
	      printf ("\n\n inconsistency in cvars array\n\n");
	      printf ("\nop: -");
	      printf ("\nfirst   : %5d:%8f", cv->first_op,
		      values[cv->first_op]);
	      printf ("\nsecond  : %5d:%8f", cv->second_op,
		      values[cv->second_op]);
	      printf ("\ncorrect : %f",
		      values[cv->first_op] - values[cv->second_op]);
	      printf ("\nreported: %f\n\n", values[i]);
	      assert (0);
	      exit (1);
	    }
	  break;
	case UMINUS_OP:
	  if ((values[i] + values[cv->first_op]) > MAX_APPROX)
	    {
	      printf ("\n\n inconsistency in cvars array\n\n");
	      printf ("\nop: unary -");
	      printf ("\nfirst   : %5d:%8f", cv->first_op,
		      values[cv->first_op]);
	      printf ("\nsecond  : %5d:%8f", cv->second_op,
		      values[cv->second_op]);
	      printf ("\ncorrect : %f", -values[cv->first_op]);
	      printf ("\nreported: %f\n\n", values[i]);
	      assert (0);
	      exit (1);
	    }
	  break;
	case LESS_THAN_OP:
	  if (((values[i] < 0.5)
	       && (values[cv->first_op] < values[cv->second_op]))
	      || ((values[i] > 0.5)
		  && (values[cv->first_op] >= values[cv->second_op])))
	    {
	      printf ("\n\n inconsistency in cvars array\n\n");
	      printf ("\nop: <");
	      printf ("\nfirst   : %5d:%8f", cv->first_op,
		      values[cv->first_op]);
	      printf ("\nsecond  : %5d:%8f", cv->second_op,
		      values[cv->second_op]);
	      printf ("\ncorrect : %f",
		      (float) (values[cv->first_op] < values[cv->second_op]));
	      printf ("\nreported: %f\n\n", values[i]);
	      assert (0);
	      exit (1);
	    }
	  break;
	case LESS_THAN_OR_EQUAL_OP:
	  if (((values[i] < 0.5)
	       && (values[cv->first_op] <= values[cv->second_op]))
	      || ((values[i] > 0.5)
		  && (values[cv->first_op] > values[cv->second_op])))
	    {
	      printf ("\n\n inconsistency in cvars array\n\n");
	      printf ("\nop: <=");
	      printf ("\nfirst   : %5d:%8f", cv->first_op,
		      values[cv->first_op]);
	      printf ("\nsecond  : %5d:%8f", cv->second_op,
		      values[cv->second_op]);
	      printf ("\ncorrect : %d",
		      (values[cv->first_op] <= values[cv->second_op]));
	      printf ("\nreported: %f\n\n", values[i]);
	      assert (0);
	      exit (1);
	    }
	  break;
	case EQUAL_OP:
	  if (((values[i] < 0.5)
	       && ((values[cv->first_op] - values[cv->second_op]) <
		   MAX_APPROX)) || ((values[i] > 0.5)
				    &&
				    ((values[cv->first_op] -
				      values[cv->second_op]) > MAX_APPROX)))
	    {
	      printf ("\n\n inconsistency in cvars array\n\n");
	      printf ("\nop: =");
	      printf ("\nfirst   : %5d:%8f", cv->first_op,
		      values[cv->first_op]);
	      printf ("\nsecond  : %5d:%8f", cv->second_op,
		      values[cv->second_op]);
	      printf ("\ncorrect : %d",
		      ((values[cv->first_op] - values[cv->second_op]) <
		       MAX_APPROX));
	      printf ("\nreported: %f\n\n", values[i]);
	      assert (0);
	      exit (1);
	    }
	  break;
	case GREATER_THAN_OP:
	  if (((values[i] < 0.5)
	       && (values[cv->first_op] > values[cv->second_op]))
	      || ((values[i] > 0.5)
		  && (values[cv->first_op] <= values[cv->second_op])))
	    {
	      printf ("\n\n inconsistency in cvars array\n\n");
	      printf ("\nop: >");
	      printf ("\nfirst   : %5d:%8f", cv->first_op,
		      values[cv->first_op]);
	      printf ("\nsecond  : %5d:%8f", cv->second_op,
		      values[cv->second_op]);
	      printf ("\ncorrect : %d",
		      (values[cv->first_op] > values[cv->second_op]));
	      printf ("\nreported: %f\n\n", values[i]);
	      assert (0);
	      exit (1);
	    }
	  break;
	case GREATER_OR_EQUAL_OP:
	  if (((values[i] < 0.5)
	       && (values[cv->first_op] >= values[cv->second_op]))
	      || ((values[i] > 0.5)
		  && (values[cv->first_op] < values[cv->second_op])))
	    {
	      printf ("\n\n inconsistency in cvars array, pos %d\n\n", i);
	      printf ("\nop: >");
	      printf ("\nfirst   : %5d:%8f", cv->first_op,
		      values[cv->first_op]);
	      printf ("\nsecond  : %5d:%8f", cv->second_op,
		      values[cv->second_op]);
	      printf ("\ncorrect : %d",
		      (values[cv->first_op] >= values[cv->second_op]));
	      printf ("\nreported: %f\n\n", values[i]);
	      assert (0);
	      exit (1);
	    }
	  break;
	  //per i precedenti, forse mettere un check se il valore del float e' 1.0 se vero e 0.0 se falso
	case INCREASE_OP:
	case DECREASE_OP:
	case SCALE_UP_OP:
	case SCALE_DOWN_OP:
	case ASSIGN_OP:
	case MINIMIZE_OP:
	case MAXIMIZE_OP:
	case FIX_NUMBER:
	case VARIABLE_OP:
	  //no need to check anything
	  break;
	default:
	  printf ("\nOperator %d not yet supported in consistency check\n\n",
		  cv->operator);

	  break;
	}
    }
}


//BET
void
eval_comp_var_non_recursive_bet (int cv_index, float *in_vect, float *out_vect)
{
  int first_op = gcomp_var[cv_index].first_op;
  int second_op = gcomp_var[cv_index].second_op;
  float old_value;
 

 
  switch (gcomp_var[cv_index].operator)
    {
    
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
      old_value = out_vect[cv_index];
      out_vect[cv_index] = (float) (in_vect[first_op] < in_vect[second_op]);
     
      break;
    case LESS_THAN_OR_EQUAL_OP:
      old_value = out_vect[cv_index];
      out_vect[cv_index] = (float) (in_vect[first_op] <= in_vect[second_op]);
     
      break;
    case EQUAL_OP:
      old_value = out_vect[cv_index];
      out_vect[cv_index] =
	(float) (in_vect[first_op] - in_vect[second_op]) <= MAX_APPROX;
     
      break;
    case GREATER_THAN_OP:
      old_value = out_vect[cv_index];
      out_vect[cv_index] = (float) (in_vect[first_op] > in_vect[second_op]);
      break;
    case GREATER_OR_EQUAL_OP:
      old_value = out_vect[cv_index];
      out_vect[cv_index] = (float) (in_vect[first_op] >= in_vect[second_op]);
    
      break;
    default:
      
      break;
    }

  return;
}



void
refresh_cvars_bet (float *input_vector)
{
  
  int i;
  
  for (i = 0; i < gnum_comp_var; i++)
    { 
    //LAZZA
    switch (gcomp_var[i].operator)
      {
      case INCREASE_OP:
      case DECREASE_OP:
      case SCALE_UP_OP:
      case SCALE_DOWN_OP:
      case ASSIGN_OP:
	MSG_ERROR("ERRORE PARTE NUMERICA");
	exit(0);
	break;
      default:
	
	eval_comp_var_non_recursive_bet (
					 //regola da applicare
					 i,
					 //valori di ingresso,
					 input_vector,
					 //valori di uscita
					 input_vector);
	
      }
    }
  return;

}




void control_numeric_of_plan()

{
  int act_num;
  int act_counter;
  int i,j;
  float *num_value;
  int num_error;
  
  
 DescNumEff *numeric_effect=NULL;
 

 num_error=0;
 act_counter=0;
 num_value= (float*) calloc (max_num_value, sizeof (float));

 //printf("\n\n\n\npippo");







 for (i = 0; i < gnum_comp_var; i++)
   {
     
     num_value[i] = ginitial_state.V[i];
     if(num_value[i]!=vectlevel[0]->numeric->values[i])
       printf("\n VARIABILE %d che vale %2f ma dovrebbe valere %2f\n al livello %d \n", i,vectlevel[0]->numeric->values[i],
	      num_value[i], 0);
     
   }
 
 for(j=0;j<GpG.curr_plan_length;j++)
   
   {

     act_num=GET_ACTION_POSITION_OF_LEVEL(j);
     //if(!gef_conn[act_num].is_numeric)
     //  continue;

     if(act_num>=0)
       {
	 /***
	 for (i = 0; i < gef_conn[act_num].num_PC; i++)
	   if (gef_conn[act_num].PC[i] < 0)
	     if(num_value[-gef_conn[act_num].PC[i]] < 0.1)
	        printf("\nErrore: Precondizione numerica non supportata, azione %d, precondizione numerica %d\n", act_num, -gef_conn[act_num].PC[i]);

	 */	 
	 
	 if(gef_conn[act_num].is_numeric)	 
	   for(i=0;i<gef_conn[act_num].num_numeric_effects;i++)
	     {	   
	       numeric_effect = &gef_conn[act_num].numeric_effects[i];
	       
	       
	       if ((*numeric_effect).is_at_start)
		 {
		   
		   //	 printf("ESEGUO EFFETTO AT START %d",(*numeric_effect).index);	     
		   numeric_effect = &gef_conn[act_num].numeric_effects[i];
		   numeric_effect = &gef_conn[act_num].numeric_effects[i];
		   /*******************     
		   printf("ESEGUO EFFETTO AT START %d   tipo:",(*numeric_effect).index);
		   if(gcomp_var_effects[(*numeric_effect).index].operator==INCREASE_OP)
		   printf("INCREASE");
		   else 
		   printf("DECREASE");
		   
		   printf("\nAzione: %d", act_num);
		   printf("\n\nEffetto :%d \n ",(*numeric_effect).index);
		   
		   if ((*numeric_effect).is_at_start)
		   printf("E' at start");
		   printf(" \nTipo var1: %d  FIRTS_OP: %d SECOND_OP: %d  Tipo var2: %d FIRST_OP:%d SECOND_OP:%d", gcomp_var[gcomp_var_effects[(*numeric_effect).index].first_op].operator,gcomp_var[gcomp_var_effects[(*numeric_effect).index].first_op].first_op,gcomp_var[gcomp_var_effects[(*numeric_effect).index].first_op].second_op,
		   gcomp_var[gcomp_var_effects[(*numeric_effect).index].second_op].operator,gcomp_var[gcomp_var_effects[(*numeric_effect).index].second_op].first_op,gcomp_var[gcomp_var_effects[(*numeric_effect).index].second_op].second_op );
		   
		   printf("\nBET LIVELLO: %d \nVariabile 1:%d   Valore1:%2f Variablile2: %d Valore2: %2f  Operatore: %d\n" ,j, gcomp_var_effects[(*numeric_effect).index].first_op, num_value[gcomp_var_effects[(*numeric_effect).index].first_op], 	
		   gcomp_var_effects[(*numeric_effect).index].second_op ,num_value[gcomp_var_effects[(*numeric_effect).index].second_op],
		   gcomp_var_effects[(*numeric_effect).index].operator);
		   printf("\nLAZZA LIVELLO: %d \nVariabile 1: %d Valore1: %2f Variablile2: %d Valore2: %2f  Operatore: %d\n" ,j, gcomp_var_effects[(*numeric_effect).index].first_op, 
		   vectlevel[j]->numeric->values[gcomp_var_effects[(*numeric_effect).index].first_op], 	
		   gcomp_var_effects[(*numeric_effect).index].second_op,vectlevel[j]->numeric->values[gcomp_var_effects[(*numeric_effect).index].second_op],
		   gcomp_var_effects[(*numeric_effect).index].operator);


		 **************/
		   eval_comp_var_non_recursive_effects ((*numeric_effect).index,num_value,num_value,0,0);	
	   
		   /*************
			printf("\nBET LIVELLO: %d \nVariabile 1:%d   Valore1:%2f Variablile2: %d Valore2: %2f  Operatore: %d\n" ,j+1, gcomp_var_effects[(*numeric_effect).index].first_op, num_value[gcomp_var_effects[(*numeric_effect).index].first_op], 	
			gcomp_var_effects[(*numeric_effect).index].second_op ,num_value[gcomp_var_effects[(*numeric_effect).index].second_op],
			gcomp_var_effects[(*numeric_effect).index].operator);
			printf("\nLAZZA LIVELLO: %d \nVariabile 1: %d Valore1: %2f Variablile2: %d Valore2: %2f  Operatore: %d\n" ,j+1, gcomp_var_effects[(*numeric_effect).index].first_op, 
			vectlevel[j+1]->numeric->values[gcomp_var_effects[(*numeric_effect).index].first_op], 	
			gcomp_var_effects[(*numeric_effect).index].second_op,vectlevel[j]->numeric->values[gcomp_var_effects[(*numeric_effect).index].second_op],
			gcomp_var_effects[(*numeric_effect).index].operator);   
			
		   ************/

	       }


	   }

	 refresh_cvars_bet (num_value);

	 if(gef_conn[act_num].sf)
	   {
	     for (i = 0; i < gef_conn[act_num].sf->num_PC_overall; i++)
	       if (gef_conn[act_num].sf->PC_overall[i] < 0)
		 if(num_value[-gef_conn[act_num].sf->PC_overall[i]] < 0.5)
		   printf("\nErrore: Precondizione numerica non supportata, azione %d, precondizione numerica %d\n", act_num, -gef_conn[act_num].PC[i]);

	     for (i = 0; i < gef_conn[act_num].sf->num_PC_end; i++)
	       if (gef_conn[act_num].sf->PC_end[i] < 0)
		 if(num_value[-gef_conn[act_num].sf->PC_end[i]] < 0.5)
		   printf("\nErrore: Precondizione numerica non supportata, azione %d, precondizione numerica %d\n", act_num, -gef_conn[act_num].PC[i]);
	     
	   }
	 if(gef_conn[act_num].is_numeric)	
	   for(i=0;i<gef_conn[act_num].num_numeric_effects;i++)
	     {	   
	       if ((*numeric_effect).is_at_start)
		 continue;
	       numeric_effect = &gef_conn[act_num].numeric_effects[i];
	       numeric_effect = &gef_conn[act_num].numeric_effects[i];
	       /*************
		   printf("ESEGUO EFFETTO AT END %d   tipo:",(*numeric_effect).index);
		   if(gcomp_var_effects[(*numeric_effect).index].operator==INCREASE_OP)
		   printf("INCREASE");
		   else 
		   printf("DECREASE");
		   
		   printf("\nAzione: %d", act_num);
		   printf("\n\nEffetto :%d \n ",(*numeric_effect).index);
		   
		   if ((*numeric_effect).is_at_start)
		   printf("E' at start");
		   printf(" \nTipo var1: %d  FIRTS_OP: %d SECOND_OP: %d  Tipo var2: %d FIRST_OP:%d SECOND_OP:%d", gcomp_var[gcomp_var_effects[(*numeric_effect).index].first_op].operator,gcomp_var[gcomp_var_effects[(*numeric_effect).index].first_op].first_op,gcomp_var[gcomp_var_effects[(*numeric_effect).index].first_op].second_op,
		   gcomp_var[gcomp_var_effects[(*numeric_effect).index].second_op].operator,gcomp_var[gcomp_var_effects[(*numeric_effect).index].second_op].first_op,gcomp_var[gcomp_var_effects[(*numeric_effect).index].second_op].second_op );
		   
		   printf("\nBET LIVELLO: %d \nVariabile 1:%d   Valore1:%2f Variablile2: %d Valore2: %2f  Operatore: %d\n" ,j, gcomp_var_effects[(*numeric_effect).index].first_op, num_value[gcomp_var_effects[(*numeric_effect).index].first_op], 	
		   gcomp_var_effects[(*numeric_effect).index].second_op ,num_value[gcomp_var_effects[(*numeric_effect).index].second_op],
		   gcomp_var_effects[(*numeric_effect).index].operator);
		   printf("\nLAZZA LIVELLO: %d \nVariabile 1: %d Valore1: %2f Variablile2: %d Valore2: %2f  Operatore: %d\n" ,j, gcomp_var_effects[(*numeric_effect).index].first_op, 
		   vectlevel[j]->numeric->values[gcomp_var_effects[(*numeric_effect).index].first_op], 	
		   gcomp_var_effects[(*numeric_effect).index].second_op,vectlevel[j]->numeric->values[gcomp_var_effects[(*numeric_effect).index].second_op],
		   gcomp_var_effects[(*numeric_effect).index].operator);
	     ************/
	     if (!(*numeric_effect).is_at_start)
	       eval_comp_var_non_recursive_effects ((*numeric_effect).index,num_value,num_value,0,0);
	       /*************
			printf("\nBET LIVELLO: %d \nVariabile 1:%d   Valore1:%2f Variablile2: %d Valore2: %2f  Operatore: %d\n" ,j+1, gcomp_var_effects[(*numeric_effect).index].first_op, num_value[gcomp_var_effects[(*numeric_effect).index].first_op], 	
			gcomp_var_effects[(*numeric_effect).index].second_op ,num_value[gcomp_var_effects[(*numeric_effect).index].second_op],
			gcomp_var_effects[(*numeric_effect).index].operator);
			printf("\nLAZZA LIVELLO: %d \nVariabile 1: %d Valore1: %2f Variablile2: %d Valore2: %2f  Operatore: %d\n" ,j+1, gcomp_var_effects[(*numeric_effect).index].first_op, 
			vectlevel[j+1]->numeric->values[gcomp_var_effects[(*numeric_effect).index].first_op], 	
			gcomp_var_effects[(*numeric_effect).index].second_op,vectlevel[j]->numeric->values[gcomp_var_effects[(*numeric_effect).index].second_op],
			gcomp_var_effects[(*numeric_effect).index].operator);   
	       ************/ 
	     
	     }
	 
	 refresh_cvars_bet (num_value);
       }
     
     for(i=0;i< gnum_comp_var;i++)
       {
	 if(num_value[i]!=vectlevel[j+1]->numeric->values[i])
	   { 
	     printf("\nERRORE SULLA VARIABILE %d che vale %2f ma dovrebbe valere %2f\n al livello %d \n", i,vectlevel[j+1]->numeric->values[i],
		    num_value[i], j+1);
	     printf("OPERATOR: %d \n FIRST_OP: num  %d  value: %2f \n SECOND_OP: num %d value: %2f \n",gcomp_var[i].operator,gcomp_var[i].first_op,
		    vectlevel[j+1]->numeric->values[gcomp_var[i].first_op],
		    gcomp_var[i].second_op,
		    vectlevel[j+1]->numeric->values[gcomp_var[i].second_op]);
	     num_value[i]=vectlevel[j+1]->numeric->values[i];
	     //printf("\n gnum_comp_var : %d",gnum_comp_var);
	     
	     num_error++;
	     
	     exit(0);
	     
	   break;
	   }

	 if(num_value[i]!=vectlevel[j+1]->numeric->values_after_start[i])
	   { 
	     printf("\nERRORE SULLA VARIABILE START %d che vale %2f ma dovrebbe valere %2f\n al livello %d \n", i,vectlevel[j+1]->numeric->values_after_start[i],
		    num_value[i], j+1);
	     printf("OPERATOR: %d \n FIRST_OP: num  %d  value: %2f \n SECOND_OP: num %d value: %2f \n",gcomp_var[i].operator,gcomp_var[i].first_op,
		    vectlevel[j+1]->numeric->values_after_start[gcomp_var[i].first_op],
		    gcomp_var[i].second_op,
		    vectlevel[j+1]->numeric->values_after_start[gcomp_var[i].second_op]);
	     num_value[i]=vectlevel[j+1]->numeric->values_after_start[i];
	     //printf("\n gnum_comp_var : %d",gnum_comp_var);
	     
	     num_error++;
	     
	     exit(0);
	     
	   break;
	   }
       }
     
   }
 /*****
 for(i=0;i< gnum_comp_var;i++)
   {

     if(num_value[i]!=vectlevel[j+1]->numeric->values_after_start[i])
       { 
	 printf("\nERRORE SULLA VARIABILE START %d che vale %2f ma dovrebbe valere %2f\n al livello %d \n", i,vectlevel[j+1]->numeric->values_after_start[i],
		num_value[i], j+1);
	 printf("OPERATOR: %d \n FIRST_OP: num  %d  value: %2f \n SECOND_OP: num %d value: %2f \n",gcomp_var[i].operator,gcomp_var[i].first_op,
		vectlevel[j+1]->numeric->values_after_start[gcomp_var[i].first_op],
		gcomp_var[i].second_op,
		vectlevel[j+1]->numeric->values_after_start[gcomp_var[i].second_op]);
	 num_value[i]=vectlevel[j+1]->numeric->values_after_start[i];
	 //printf("\n gnum_comp_var : %d",gnum_comp_var);
	 
	 num_error++;
	     
	 exit(0);
	 
	 break;
       }
     
   }
 *****/
 
 if(num_error==0);
 else
   printf("\n Ci sono %d errori!!!\n\n",num_error);
 
 return;
 
}




void print_action_precs(void) {

  int i, j;

  for (i = 0; i < gnum_ef_conn; i++) {
    
    printf("\n\nPRECONDITION OF ACTION : %d", i);

    for (j = 0; j < gef_conn[i].num_PC; j++)
      printf("\n   start: %d", gef_conn[i].PC[j]);

    if (gef_conn[i].sf) {

      for (j = 0; j < gef_conn[i].sf->num_PC_overall; j++)
	printf("\n   overall: %d", gef_conn[i].sf->PC_overall[j]);

      for (j = 0; j < gef_conn[i].sf->num_PC_end; j++)
	printf("\n   end: %d", gef_conn[i].sf->PC_end[j]);
    }
    
  }

}
 


Bool check_cpu_time(float *plan_time)
{
  
#ifndef __ONLY_ONE_PLANNER__
  if (GpG.mode == QUALITY)
#else
    if (GpG.save_quality_plan_with_different_name == 0)
#endif
      
      {
	times (&glob_end_time);
	
	gtotal_time = DeltaTime(glob_start_time, glob_end_time);
	
	if (GpG.max_cputime_for_local_search > 0.0 && GpG.num_solutions == 0) // facciamo partire il BEST FIRST solo se non si e' ancora trovata una soluzione
	  {
	    //		      times(&GpG.cputime);
	    /* tempo totale dall'inizio programma incluso preprocessing*/
	    if (!GpG.timed_facts_present && !GpG.numeric_precs_present && !GpG.derived_predicates) /* altrimenti il best first non funziona*/
	      if (gtotal_time > GpG.max_cputime_for_local_search) 
		{
		  printf("\n\nMax time exceeded for Local Search\n\n");
		  printf("\n\nTime: %f\n\n", gtotal_time);
		  return TRUE;
		}
	  }
	
	if (gtotal_time > gmax_cpu_time_for_quality_mode)
	  {
	    
	    times(&GpG.cputime);
	    (*plan_time) = DeltaTime (search_start, search_end);
	    
	    if (GpG.num_solutions > 0)
	      {
		
#ifdef __ONLY_ONE_PLANNER__
		if (GpG.mode == QUALITY)
#endif
		  print_actions_in_temporal_plan ();
		
		printf ("\nSolution found:\nTotal time:      %.2f\nSearch time:     %.2f\nActions:         %d\nExecution cost:  %.2f\nDuration:        %.3f\nPlan quality:    %.3f", 
			gtotal_time, *plan_time, plan_info_for_quality_mode.num_actions, plan_info_for_quality_mode.total_cost, plan_info_for_quality_mode.total_time, 
			plan_info_for_quality_mode.metricvalue);
		
#ifdef __ONLY_ONE_PLANNER__
		printf ("\n     Plan file:");
		if (GpG.out_file_name)
		  {
#ifndef __WINLPG__
		    printf ("       quality%s_1.SOL\n\n", gcmd_line.out_file_name);
#else
		    printf ("       %squality%s.SOL\n\n",  gpath_sol_file_name, gfct_file_name);
#endif
		  }
		
		else
		  {
#ifndef __WINLPG__
		    printf ("       qualityplan_%s.SOL\n\n", gcmd_line.fct_file_name);
#else
		    printf ("       %squalityplan_%s.SOL\n\n", gpath_sol_file_name, gfct_file_name);
#endif
		  }
#else
		printf ("\n     Plan file:");
		if (GpG.out_file_name)
		  {
#ifndef __WINLPG__
		    printf ("       %s_1.SOL\n\n", gcmd_line.out_file_name);
#else
		    printf ("       %s%s.SOL\n\n", gpath_sol_file_name, gfct_file_name);
#endif
		  }
		else
		  {
#ifndef __WINLPG__
		    printf ("       plan_%s_1.SOL\n\n", gcmd_line.fct_file_name);
#else
		    printf ("       %splan_%s.SOL\n\n", gpath_sol_file_name, gfct_file_name);
#endif
		  }
#endif
		
		
#ifdef __ONLY_ONE_PLANNER__
		GpG.save_quality_plan_with_different_name = 1;
#endif
		
		store_plan(*plan_time);
		
#ifdef __ONLY_ONE_PLANNER__
		GpG.save_quality_plan_with_different_name = 2;
#endif
		
	      }
	    
	    
#ifndef __ONLY_ONE_PLANNER__
	    printf("\n\nDo not use option -quality for better solutions.\n\n");
	    exit(0);
#endif
	  }
      }
    else
      {
	if (GpG.max_cputime_for_local_search>0.0 || GpG.max_cputime > 0.0) // facciamo partire il BEST FIRST solo se non si e' ancora trovata una soluzione
	  {
	    
	    times (&glob_end_time);
	    
	    gtotal_time = DeltaTime(glob_start_time, glob_end_time);
	    
	    /* Total time from start, including pre-processing time*/
	    if (gtotal_time > GpG.max_cputime) 
	      {
		printf("\n\nMax time exceeded.\n\n");
		printf("\n\nTime: %f\n\n", gtotal_time);
		exit(0);
	      }
	    
	    if (!GpG.timed_facts_present && !GpG.numeric_precs_present && !GpG.derived_predicates) /* altrimenti il best first non funziona*/
	      if (gtotal_time > GpG.max_cputime_for_local_search) 
		{
		  printf("\n\nMax time exceeded for LocalSearch\n\n");
		  printf("\n\nTime: %f\n\n", *plan_time);
		  return TRUE;
		}
	  }
	
      }


  return FALSE;
  
}









