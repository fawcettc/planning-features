/*********************************************************************
 * (C) Copyright 2000 Albert Ludwigs University Freiburg
 *     Institute of Computer Science
 *
 * All rights reserved. Use of this software is permitted for 
 * non-commercial research purposes, and it may be copied only 
 * for that use.  All copies must include this copyright message.
 * This software is made available AS IS, and neither the authors
 * nor the  Albert Ludwigs University Freiburg make any warranty
 * about the software or its performance. 
 *********************************************************************/

/**
  The following parts of this file have been modified by the 
  LPG developers (DEA - University of Brescia):

  Included libraries:
  - lpg.h
  - inst_utils.h
  - check.h

  New variables and data struntures:
  - int lp1;
  - int largs1[MAX_VARS];
  - int these_args[MAX_VARS];
  - int numero, kk, kkk;
  - WffNode *precs, *n;

  New functions:
  - fact_adress1

  Modified functions:
  - perform_reachability_analysis
  - create_final_goal_state
  - set_relevants_in_wff
  - build_connectivity_graph
**/










/*********************************************************************
 * File: inst_final.c
 * Description: final domain representation functions
 *
 *
 * Author: Joerg Hoffmann 2000
 *
 *********************************************************************/








#include <math.h>
#include "ff.h"

#include "output.h"
#include "memory.h"

#include "inst_pre.h"
#include "inst_hard.h"
#include "inst_final.h"

/*
 * DEA - University of Brescia
 */

#include <values.h>
#include "lpg.h" 
#include "inst_utils.h"
#include "check.h"

#include "LpgOutput.h"
#include "utilities.h"

/*
 * End of DEA
 */




/********************************
 * POSSIBLY TRUE FACTS ANALYSIS *
 ********************************/








/* local globals for this part
 */

#define FACTS_HASH_SIZE 10000

indexed_int_list *facts_hash[FACTS_HASH_SIZE];

bit_table lpos, nlneg, luse;

/*
int_pointer lpos[MAX_PREDICATES];
int_pointer lneg[MAX_PREDICATES];
int_pointer luse[MAX_PREDICATES];
*/
//int_pointer lindex[MAX_PREDICATES];

int lp;
int largs[MAX_VARS];
/*
 * DEA - University of Brescia
 */

int lp1;
int largs1[MAX_VARS];
int these_args[MAX_VARS];

Action *susp_a_idx = NULL;
EasyTemplate *susp_t_idx = NULL;


/*
 * End of DEA
 */


/**
 * Inizializza le tabelle lpos, luse e nlneg usate per tenere traccia di quali
 * fatti possono essere positivi, usati e negativi. 
 * In nlneg vengono segnati i fatti che NON possono essere negativi.
 **/
void init_bit_hash_tables( void ) {

  int i, max_arity = 0;
  int n_bit, bit_row_size, base;
  unsigned long int max_size;

  /* Evaluate max predicates arity
   */
  for (i = 0; i < gnum_predicates; i++)
    if (garity[i] > max_arity) 
      max_arity = garity[i];
  
  /* Evaluate max predicates size
   */

  max_size = 1;
  for (i = 0; i < max_arity; i++)
    max_size *= gnum_constants;

  max_size = max_arity * max_size;

  init_bit_table_const(max_size, &n_bit, &base, &bit_row_size);

  lpos.bits = (int_pointer **)calloc(gnum_predicates, sizeof(int_pointer *));
  assert(lpos.bits);
    
  nlneg.bits = (int_pointer **)calloc(gnum_predicates, sizeof(int_pointer *));
  assert(nlneg.bits);
  
  luse.bits = (int_pointer **)calloc(gnum_predicates, sizeof(int_pointer *));
  assert(luse.bits);
  
  lpos.max_row_size = nlneg.max_row_size = luse.max_row_size = max_size;
  lpos.bit_row_size = nlneg.bit_row_size = luse.bit_row_size = bit_row_size;
  lpos.n_bit = nlneg.n_bit = luse.n_bit = n_bit;
  lpos.base = nlneg.base = luse.base = base;
  
}


/**
 * Inizializza l'hash table per l'instanziazione dei fatti
 **/
void init_facts_hash( void ) {
  
  memset(facts_hash, 0, FACTS_HASH_SIZE * sizeof(indexed_int_list *));
 
}


/**
 * Inserisce un nuovo fatto nell'hash table
 **/
void insert_fact_in_hash(int p, unsigned long int adr) {

  int hadr;
  indexed_int_list *tmp;

  adr += p;
  hadr = adr % FACTS_HASH_SIZE;

  tmp = (indexed_int_list *)calloc(1, sizeof(indexed_int_list));
  tmp->op = p;
  tmp->adr = adr;
  tmp->item = gnum_relevant_facts;  
  tmp->next = facts_hash[hadr];
  facts_hash[hadr] = tmp;
}


/**
 * Recupera dall'hash table l'indice di un fatto instanziato 
 * nel vettore dei relevant facts;
 **/
int retrieve_fact_index(int p, unsigned long int adr, indexed_int_list **where) {

  int hadr;
  indexed_int_list *tmp;

  adr += p;
  hadr = adr % FACTS_HASH_SIZE;

  for (tmp =  facts_hash[hadr]; tmp; tmp = tmp -> next)
    if ((tmp -> op == p) && (tmp -> adr == adr)) {
      if (where)
	*where = tmp;
      return (tmp -> item);
    }

  if (where)
    *where = NULL;
  return -1;

}







void collect_facts(void)
{
  
  Action *a;
  NormOperator *no;
  NormEffect *ne;
  unsigned long int adr;
  int i, j, count;
  PseudoAction *pa;
  PseudoActionEffect *pae;
  Action **a_pointer;
  
  if (GpG.derived_predicates)
    count = 0;
  else
    count = 1;
  /* mark all deleted facts; such facts, that are also pos, are relevant.
   */
  for (a_pointer = &gactions; count < 2; a_pointer = &gdpactions, count++) {
    for ( a = (*a_pointer); a && (a != susp_a_idx); a = a->next ) {
      if ( a->norm_operator ) {
	no = a->norm_operator;
	
	for ( ne = no->effects; ne; ne = ne->next ) {
	  for ( i = 0; i < ne->num_dels; i++ ) {
	    lp = ne->dels[i].predicate;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      largs[j] = ( ne->dels[i].args[j] >= 0 ) ?
		ne->dels[i].args[j] : a->inst_table[DECODE_VAR( ne->dels[i].args[j] )];
	    }
	    adr = fact_adress();
	    
	    /*
	     lneg[lp][adr] = 1;
	    */

	    delete_bit_from_bit_table(nlneg, lp, adr);
	    	    
	    /*
	    if ( lpos[lp][adr] &&
		 !luse[lp][adr] ) 
	    */

	    if (check_bit_in_bit_table(lpos, lp, adr)
		&& !check_bit_in_bit_table(luse, lp, adr)) {
	      /*
	      luse[lp][adr] = 1;
	      */

	      insert_bit_in_bit_table(luse, lp, adr);
	      
	      if ( gnum_relevant_facts == MAX_RELEVANT_FACTS ) {
		printf("\nincrease MAX_RELEVANT_FACTS! (current value: %d)\n\n",
		       MAX_RELEVANT_FACTS);
		exit( 1 );
	      }
	      grelevant_facts[gnum_relevant_facts].predicate = lp;
	      for ( j = 0; j < garity[lp]; j++ ) {
		grelevant_facts[gnum_relevant_facts].args[j] = largs[j];
	      }
	      
	      //lindex[lp][adr] = gnum_relevant_facts;
	      insert_fact_in_hash(lp, adr); 	            
	      gnum_relevant_facts++;
	      	      
	    }
	  }
	}
      } else {
	pa = a->pseudo_action;
	
	for ( pae = pa->effects; pae; pae = pae->next ) {
	  for ( i = 0; i < pae->num_dels; i++ ) {
	    lp = pae->dels[i].predicate;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      largs[j] = pae->dels[i].args[j];
	    }
	    adr = fact_adress();
	    
	    /*
	    lneg[lp][adr] = 1;
	    */
	    
	    delete_bit_from_bit_table(nlneg, lp, adr);
	    
	    /*
	    if ( lpos[lp][adr] &&
		 !luse[lp][adr] )
	    */

	    if (check_bit_in_bit_table(lpos, lp, adr)
		&& !check_bit_in_bit_table(luse, lp, adr)) {
	   
	      /*
	      luse[lp][adr] = 1;
	      */

	      insert_bit_in_bit_table(luse, lp, adr);
	      
	      if ( gnum_relevant_facts == MAX_RELEVANT_FACTS ) {
		printf("\nincrease MAX_RELEVANT_FACTS! (current value: %d)\n\n",
		       MAX_RELEVANT_FACTS);
		exit( 1 );
	      }
	      grelevant_facts[gnum_relevant_facts].predicate = lp;
	      for ( j = 0; j < garity[lp]; j++ ) {
		grelevant_facts[gnum_relevant_facts].args[j] = largs[j];
	      }

	      //lindex[lp][adr] = gnum_relevant_facts;
	      insert_fact_in_hash(lp, adr);
	      gnum_relevant_facts++;
	      	      
	    }
	  }
	}
      }
    }
  }

}









void perform_reachability_analysis( void )

{

  unsigned long int size, adr;
  int i, j, k, num, act_dp;
  Bool *fixpoint, fix_act, fix_dp;
  Facts *f;
  NormOperator *no;
  EasyTemplate *t1 = NULL, *t2 = NULL;
  NormEffect *ne;
  Action *tmp, *a;
  Bool *had_hard_template;
  PseudoAction *pa;
  PseudoActionEffect *pae;
  Action **outactions = NULL;
  EasyTemplate **et = NULL;
  int *num_act = NULL;

/*
 * DEA - University of Brescia
 */
  int numero, kk, kkk;
  WffNode *precs, *n;
  
  Bool changed;

  changed = TRUE;

  num_act=NULL;

  t1=NULL;

  et=NULL;

  outactions=NULL;

/*
 * End of DEA
 */

  gactions = NULL;
  gnum_actions = 0;
  gdpactions = NULL;
  gnum_dp_actions = 0;

  init_facts_hash();
  init_bit_hash_tables();

  for ( i = 0; i < gnum_predicates; i++ ) {
    size =  1;
    for ( j = 0; j < garity[i]; j++ ) {
      size *= gnum_constants;
    }

    size = garity[i] * size;

    /*
    lpos[i] = ( int_pointer ) calloc( size, sizeof( int ) );
    lneg[i] = ( int_pointer ) calloc( size, sizeof( int ) );
    luse[i] = ( int_pointer ) calloc( size, sizeof( int ) );
    */
    
    init_bit_table_row(lpos, i, size);
    init_bit_table_row(nlneg, i, size);
    init_bit_table_row(luse, i, size);

    //lindex[i] = ( int_pointer ) calloc( size, sizeof( int ) );

    for ( j = 0; j < size; j++ ) {
      /*
      lpos[i][j] = 0;
      lneg[i][j] = 1;// all facts but initials are poss. negative 
      luse[i][j] = 0;
      */
      
      //lindex[i][j] = -1;
    }
  }

  had_hard_template = ( Bool * ) calloc( gnum_hard_templates + gnum_hard_dp_templates, sizeof( Bool ) );
  for ( i = 0; i < (gnum_hard_templates + gnum_hard_dp_templates); i++ ) {
    had_hard_template[i] = FALSE;
  }

  /* mark initial facts as possibly positive, not poss. negative
   */
  for ( i = 0; i < gnum_predicates; i++ ) {
    lp = i;
    for ( j = 0; j < gnum_initial_predicate[i]; j++ ) {
      for ( k = 0; k < garity[i]; k++ ) {
	largs[k] = ginitial_predicate[i][j].args[k];
      }
      adr = fact_adress();
      
      /*
      lpos[lp][adr] = 1;
      lneg[lp][adr] = 0;
      */
      insert_bit_in_bit_table(lpos, lp, adr);
      insert_bit_in_bit_table(nlneg, lp, adr);
    }
  }

  /* compute fixpoint
   */
  fix_act = FALSE;
  fix_dp = !GpG.derived_predicates;
  act_dp = 0;
 
  while (!(fix_act && fix_dp)) {
    /*
     * DEA - University of Brescia
     */
    
    
    /*geasy_templates: action list (instantious operator) 
     */

    if (gcmd_line.display_info == 121)
      {
	numero = 0;
	for (t1 = geasy_templates; t1; t1 = t1->next)
	  numero++;
	
	printf ("\nLe geasy_templates sono %d, le gnum_actions %d", numero, gnum_actions);
      }
    /*
     * End of DEA
     */

    /* assign next layer of easy templates to possibly positive fixpoint
     */

#ifdef __DEBUG_DP_SWITCH__
    printf("\nSwitch to %s", (changed)?"Actions":"Derived");
#endif

    if (changed) {
      act_dp = 0;
      outactions = &gactions;
      num_act = &gnum_actions;
      et = &geasy_templates;
      fixpoint = &fix_act;
      if (gnum_easy_dp_templates || gnum_hard_dp_templates) {
	changed = !changed;

#ifdef __DEBUG_DP_SWITCH__
	printf("\nChange next %s", (changed)?"NO":"YES");
#endif

      }
    }
    else {
      act_dp = 1;
      outactions = &gdpactions;
      num_act = &gnum_dp_actions;
      et = &geasy_dp_templates;
      fixpoint = &fix_dp;
      changed = !changed;
    }

    (*fixpoint) = TRUE;
    
    t1 = *et;
    
    while ( t1 ) {

      no = t1->op;
      for ( i = 0; i < no->num_preconds; i++ ) {
	lp = no->preconds[i].predicate;
	for ( j = 0; j < garity[lp]; j++ ) {
	  largs[j] = ( no->preconds[i].args[j] >= 0 ) ?
	    no->preconds[i].args[j] : t1->inst_table[DECODE_VAR( no->preconds[i].args[j] )];
	}
	
/*
 * DEA - University of Brescia
 */

	//se questa precondizione compare anche tra gli effetti additivi, allora considerala raggiunta
	//ATTENZIONE: non e' esattamente corretto; questo check e' volto a gestire il caso di una precondizione over all o at end
	//che viene realizzata attraverso un effetto at start - senza qs check l'azione non risulta applicabile
	//il problema e' che qui non introduco i check su overall, end, etc: basta che una preco compaia anche tra gli effetti e la considero raggiunta
	//ATTENZIONE: saltare questo check se il corrispondente PlOperator e' is_odd
	for (kk = 0; kk < no->effects->num_adds; kk++)
	  {
	    int this_pred = no->effects->adds[kk].predicate;
	    
	    if(no->effects->num_adds>MAX_VARS)
	      {
#ifdef __MY_OUTPUT__
		MSG_ERROR ( WAR_MAX_VARS );
#else
		printf( WAR_MAX_VARS );
#endif    
		exit (1);
	      }	
	    for (kkk = 0; kkk < garity[this_pred]; kkk++)
	      these_args[kkk] = (no->effects->adds[kk].args[kkk] >= 0) ?
		no->effects->adds[kk].args[kkk] : t1->
		inst_table[DECODE_VAR(no->effects->adds[kk].args[kkk])];
	    //cerco la preco corrente tra gli effetti additivi
	    //il predicato non coincide: provo con il prossimo effetto
	    if (this_pred != lp)
	      continue;
	    //controllo tutti gli argomenti
	    for (kkk = 0; kkk < garity[this_pred]; kkk++)
	      //se ce n'e' almeno uno diverso, non e' lo stesso fatto
	      if (these_args[kkk] != largs[kkk])
		break;
	    // se tutti gli argomenti sono uguali controllo il numero di argomenti
	    // questo if e' vero se e' lo stesso fatto: l'ho trovato quindi esco
	    if (kkk == garity[this_pred])
	      break;
	  }
	//se non ho fatto passare tutti gli effetti, significa che ho trovato la preco tra gli effetti additivi: considero raggiunta la preco, passa a controllare la prossima
	if (kk != no->effects->num_adds)
	  continue;
	/* se tale preco non e' raggiunta, esci e vai a qui1 */

/*
 * End of DEA
 */
	/*
	if ( !lpos[lp][fact_adress()] ) {
	  break;
	*/

	if (!check_bit_in_bit_table(lpos, lp, fact_adress()))
	  break;
	
      }

      if ( i < no->num_preconds ) {
	t1 = t1->next;
	continue;
      }


/*
 * DEA - University of Brescia
 */

	  //ulteriore check: verifico che un predicato inerziale sia effettivamente presente nei fatti iniziali, altrimenti l'azione non e' applicabile
	  //problema rilevato con Rovers/SimpleTime
	  precs = no->operator-> preconds;
	  if (precs->connective == AND)
	    precs = precs->sons;
	  for (n = precs; n; n = n->next)
	    {
	      //mi e' capitato di trovare un nodo not, con son predicato -1. boh? (problema:Satellite/numeric)
	      if (n->fact == NULL)
		continue;
	      // Skip equals preconds
	      if (n->fact->predicate < 0)
		continue;
	      /*lp=numero di predicato della preco i-esima */
	      lp = n->fact->predicate;
	      /*per ciascuno degli argomenti della precondizione */
	      for (j = 0; j < garity[lp]; j++)
		{
		  /* CONTROLLARE */
		  if (n->fact->args[j] >= 0)
		    largs[j] = n->fact->args[j];
		  else
		    largs[j] = no->operator->removed[DECODE_VAR(n->fact->args[j])] ? 
		      no->inst_table[DECODE_VAR(n->fact->args[j])] :
		      t1->inst_table[DECODE_VAR (n->fact->args[j])];
		      
		  //largs[j] =(n->fact->args[j] >= 0 ) ? n->fact->args[j]: t1->inst_table[DECODE_VAR (n->fact->args[j])];
		}
	      adr = fact_adress ();
	      //CHECK1 chiesto da Ivan: se il fatto e' non inerziale e non compare tra le preconds del normoperator, da errore!
	      //INIZIO CHECK1
	      if (gis_added[lp] || gis_deleted[lp])
		{
		  for (i = 0; i < no->num_preconds; i++)
		    {
		      /*lp=numero di predicato della preco i-esima */
		      lp1 = no->preconds[i].predicate;
		      /*per ciascuno degli argomenti della precondizione */
		      for (j = 0; j < garity[lp1]; j++)
			{
			  /* non ho colto qui perche' ci sono 2 casi, comunque mette in largs[k] il numero di ciascun oggetto */
			  largs1[j] = (no->preconds[i].args[j] >= 0) ?
			    no->preconds[i].args[j] : t1->
			    inst_table[DECODE_VAR (no->preconds[i].args[j])];
			}
		      if ((lp == lp1) && (adr == fact_adress1 ()))
			break;
		    }
		  if (i == no->num_preconds)
		    {
		      if(DEBUG3)
			{			
			  printf ("\nAttenzione: uno dei fatti non inerziali non compare tra le preconds del normoperator!\n");
			  fflush (stdout);
			}
		      assert (0);
		    }
		}
	      //FINE CHECK1
	      //se questo fatto viene aggiunto, non e' necessario verificarlo -> passo al prossimo
	      if (gis_added[lp])
		continue;
	      //Se il fatto non e' stato raggiunto, non posso applicare l'azione: esco dal for
	      /*
	      if (!lpos[lp][fact_adress ()])
		break;
	      */
	      
	      if (!check_bit_in_bit_table(lpos, lp, fact_adress()))
		break;
	    
	    }
	  //se ho fatto un break prima di finire le preco, significa che un predicato inerziale non compare nei fatti iniziali   
	  if (n != NULL)
	    {
	      //passo quindi ad esaminare la prossima azione
	      t1 = t1->next;
	      continue;
	    }

/*
 * End of DEA
 */

      num = 0;
      for ( ne = no->effects; ne; ne = ne->next ) {
	num++;
	/* currently, simply ignore effect conditions and assume
	 * they will all be made true eventually.
	 */
	for ( i = 0; i < ne->num_adds; i++ ) {
	  lp = ne->adds[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = ( ne->adds[i].args[j] >= 0 ) ?
	      ne->adds[i].args[j] : t1->inst_table[DECODE_VAR( ne->adds[i].args[j] )];
	  }
	  adr = fact_adress();
	  /*
	  if ( !lpos[lp][adr] )
	  */

	  if (!check_bit_in_bit_table(lpos, lp,  fact_adress())) {
	    /* new relevant fact! (added non initial)
	     */

	    /*
	    lpos[lp][adr] = 1;
	    lneg[lp][adr] = 1;
	    luse[lp][adr] = 1;
	    */
	    
	    insert_bit_in_bit_table(lpos, lp, adr);
	    insert_bit_in_bit_table(luse, lp, adr);
	    delete_bit_from_bit_table(nlneg, lp, adr);
    
	    if ( gnum_relevant_facts == MAX_RELEVANT_FACTS ) {
	      printf("\ntoo many relevant facts! increase MAX_RELEVANT_FACTS (currently %d)\n\n",
		     MAX_RELEVANT_FACTS);
	      exit( 1 );
	    }
	    grelevant_facts[gnum_relevant_facts].predicate = lp;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      grelevant_facts[gnum_relevant_facts].args[j] = largs[j];
	    }

	    //lindex[lp][adr] = gnum_relevant_facts;
	    insert_fact_in_hash(lp, adr);
	    gnum_relevant_facts++;
	   
	    (*fixpoint) = FALSE;
	  }
	}
      }

    
/*
 * DEA - University of Brescia
 */
      check_time_and_length (0);	/* con zero non controlla la lunghezza */

/*
 * End of DEA
 */
  
      tmp = new_Action();
      tmp->suspected = t1->suspected;
      tmp->norm_operator = no;
      for ( i = 0; i < no->num_vars; i++ ) {
	tmp->inst_table[i] = t1->inst_table[i];
      }
      tmp->name = no->operator->name;
      tmp->num_name_vars = no->operator->number_of_real_params;
      make_name_inst_table_from_NormOperator( tmp, no, t1 );
      tmp->next = (*outactions);
      tmp->num_effects = num;
      (*outactions) = tmp;
      (*num_act)++;

      t2 = t1->next;
      if ( t1->next ) {
	t1->next->prev = t1->prev;
      }
      if ( t1->prev ) {
	t1->prev->next = t1->next;
      } 
      else {
	(*et) = t1->next;
      }
      free_single_EasyTemplate( t1 );
      t1 = t2;
    }

    /* now assign all hard templates that have not been transformed
     * to actions yet.
     */
    for ( i =  act_dp * gnum_hard_templates; i < gnum_hard_templates + (act_dp * gnum_hard_dp_templates); i++ ) {
      if ( had_hard_template[i] ) {
	continue;
      }
      if (i < gnum_hard_templates)
	pa = ghard_templates[i];
      else
	pa = ghard_dp_templates[i - gnum_hard_templates];
 
      for ( j = 0; j < pa->num_preconds; j++ ) {
	lp = pa->preconds[j].predicate;
	for ( k = 0; k < garity[lp]; k++ ) {
	  largs[k] = pa->preconds[j].args[k];
	}
	/*
	if ( !lpos[lp][fact_adress()] ) {
	  break;
	*/
	
	if (!check_bit_in_bit_table(lpos, lp, fact_adress()))
	  break;
	
      }

      if ( j < pa->num_preconds ) {
	continue;
      }

      for ( pae = pa->effects; pae; pae = pae->next ) {
	/* currently, simply ignore effect conditions and assume
	 * they will all be made true eventually.
	 */
	for ( j = 0; j < pae->num_adds; j++ ) {
	  lp = pae->adds[j].predicate;
	  for ( k = 0; k < garity[lp]; k++ ) {
	    largs[k] = pae->adds[j].args[k];
	  }

	  adr = fact_adress();
	  
	  /*
	    if ( !lpos[lp][adr] )
	  */
	  
	  if (!check_bit_in_bit_table(lpos, lp, adr)) {
	    /* new relevant fact! (added non initial)
	     */

	    /*
	    lpos[lp][adr] = 1;
	    lneg[lp][adr] = 1;
	    luse[lp][adr] = 1;
	    */

	    insert_bit_in_bit_table(lpos, lp, adr);
	    insert_bit_in_bit_table(luse, lp, adr);
	    delete_bit_from_bit_table(nlneg, lp, adr);

	    if ( gnum_relevant_facts == MAX_RELEVANT_FACTS ) {
	      printf("\ntoo many relevant facts! increase MAX_RELEVANT_FACTS (currently %d)\n\n",
		     MAX_RELEVANT_FACTS);
	      exit( 1 );
	    }
	    grelevant_facts[gnum_relevant_facts].predicate = lp;
	    for ( k = 0; k < garity[lp]; k++ ) {
	      grelevant_facts[gnum_relevant_facts].args[k] = largs[k];
	    }

	    //lindex[lp][adr] = gnum_relevant_facts;
	    insert_fact_in_hash(lp, adr);
	    gnum_relevant_facts++;
	   	   
	    (*fixpoint) = FALSE;
	  }
	}
      }

/*
 * DEA - University of Brescia
 */
      check_time_and_length (0);	/* con zero non controlla la lunghezza */

/*
 * End of DEA
 */

  
      tmp = new_Action();

      /* Hard suspected not implemented yet
       */
      tmp->suspected = FALSE;

      tmp->pseudo_action = pa;
      for ( j = 0; j < pa->operator->num_vars; j++ ) {
	tmp->inst_table[j] = pa->inst_table[j];
      }
      tmp->name = pa->operator->name;
      tmp->num_name_vars = pa->operator->number_of_real_params;
      make_name_inst_table_from_PseudoAction( tmp, pa );
      tmp->next = (*outactions);
      tmp->num_effects = pa->num_effects;
      (*outactions) = tmp;
      (*num_act)++;

      had_hard_template[i] = TRUE;
    }

    if (fix_act && fix_dp)
      {

	collect_facts();

	if (GpG.try_suspected_actions && gsuspected_easy_templates)
	  {
	    
	    for (susp_t_idx = gsuspected_easy_templates;
		 susp_t_idx->next;
		 susp_t_idx = susp_t_idx->next);
	    
	    /* Append suspected templates to easy_templates list...
	     */
	    susp_t_idx->next = geasy_templates;

	    if (geasy_templates)
	      geasy_templates->prev = susp_t_idx;

	    geasy_templates = gsuspected_easy_templates;
	    gsuspected_easy_templates = NULL;
	   
	    /* Save pointer to the last action inserted...
	     */
	    susp_a_idx = gactions;

	    (*fixpoint) = FALSE;
	    changed = TRUE;
	  }
      }

  }

  /* If suspected templates have been instantiating
   * move suspected actions at the end of the list
   */
  if (gactions && susp_t_idx && susp_a_idx)
    {
      for (tmp = gactions; tmp->next; tmp = tmp->next);
      tmp->next = gactions;
      for (tmp = gactions; tmp->next != susp_a_idx; tmp = tmp->next);
      tmp->next = NULL;
      gactions = susp_a_idx;
    }


/*
 * DEA - University of Brescia
 */
 if (gcmd_line.display_info == 121)
   {
     numero = 0;
     for (t1 = geasy_templates; t1; t1 = t1->next)
       numero++;

     printf ("\nLe geasy_templates sono %d, le gnum_actions %d", numero, gnum_actions);
   }
/*
 * End of DEA
 */

  free( had_hard_template );

  gnum_pp_facts = gnum_initial + gnum_relevant_facts;

  if (gcmd_line.display_info == 118 ) {
    printf("\nreachability analysys came up with:");

    printf("\n\npossibly positive facts:");
    for ( f = ginitial; f; f = f->next ) {
      printf("\n");
      print_Fact( f->fact );
    }
    for ( i = 0; i < gnum_relevant_facts; i++ ) {
      printf("\n");
      print_Fact( &(grelevant_facts[i]) );
    }

    printf("\n\nthis yields these %d action templates:", gnum_actions);
    for ( i = 0; i < gnum_operators; i++ ) {
      printf("\n\noperator %s:", goperators[i]->name);
      for ( a = gactions; a; a = a->next ) {
	if ( ( a->norm_operator && 
	       a->norm_operator->operator !=  goperators[i] ) ||
	     ( a->pseudo_action &&
	       a->pseudo_action->operator !=  goperators[i] ) ) {
	  continue;
	}
	printf("\ntemplate: ");
	for ( j = 0; j < goperators[i]->number_of_real_params; j++ ) {
	  printf("%s", gconstants[a->name_inst_table[j]]);
	  if ( j < goperators[i]->num_vars-1 ) {
	    printf(" ");
	  }
	}
      }
    }
    printf("\n\n");
  }

}



unsigned long int fact_adress( void )

{

  unsigned long int r = 0;
  int b = 1, i;

  for ( i = garity[lp] - 1; i > -1; i-- ) {
    r += b * largs[i];
    b *= gnum_constants;
  }

  return r;

}



void make_name_inst_table_from_NormOperator( Action *a, NormOperator *o, EasyTemplate *t )

{

  int i, r = 0, m = 0;

  for ( i = 0; i < o->operator->number_of_real_params; i++ ) {
    if ( o->num_removed_vars > r &&
	 o->removed_vars[r] == i ) {
      /* this var has been removed in NormOp;
       * insert type constraint constant
       *
       * at least one there, as empty typed pars ops are removed
       */
      a->name_inst_table[i] = gtype_consts[o->type_removed_vars[r]][0];
      r++;
    } else {
      /* this par corresponds to par m  in NormOp
       */
      a->name_inst_table[i] = t->inst_table[m];
      m++;
    }
  }

}



void make_name_inst_table_from_PseudoAction( Action *a, PseudoAction *pa )

{

  int i;

  for ( i = 0; i < pa->operator->number_of_real_params; i++ ) {
    a->name_inst_table[i] = pa->inst_table[i];
  }

}


















/***********************************************************
 * RELEVANCE ANALYSIS AND FINAL DOMAIN AND PROBLEM CLEANUP *
 ***********************************************************/


/**
 * Raggruppa i predicati derivati in fondo all'array dei relevant facts
 **/

void optimize_dp_facts_position( void ) {

  unsigned long int adr;
  int i, j, k;
  indexed_int_list *tmp;
  Fact fi, fj;

  i = 0;
  j = gnum_relevant_facts - 1;

  while (i < j) {

    for (i = i; (i < j) && (gpredicates_type[grelevant_facts[i].predicate] != IS_DERIVED); i++);
    for (j = j; (j > i) && (gpredicates_type[grelevant_facts[j].predicate] != IS_BASE); j--);

    if (i < j) {

      fi = grelevant_facts[i];
      fj = grelevant_facts[j];

      grelevant_facts[i] = fj;
      grelevant_facts[j] = fi;

      lp = fi.predicate;
      for (k = 0; k < garity[lp]; k++)
	largs[k] = fi.args[k];
      adr = fact_adress();
      retrieve_fact_index(lp, adr, &tmp);
      tmp -> item = j;

      lp = fj.predicate;
      for (k = 0; k < garity[lp]; k++)
	largs[k] = fj.args[k];
      adr = fact_adress();
      retrieve_fact_index(lp, adr, &tmp);
      tmp -> item = i;
      
    }
    
    i++;
    j--;
    
  }
  
}


/* counts effects for later allocation
 */
int lnum_effects;

/* counts conditional effects for later allocation
 */
int lnum_cond_effects;





void collect_relevant_facts( void )

{

  Action *a;
  NormOperator *no;
  NormEffect *ne;
  unsigned long int adr;
  int i, j;
  PseudoAction *pa;
  PseudoActionEffect *pae;
  Facts *add_initial;
  Fact tmp_fact;
  int k, real_precs;
  Bool changed;

  
  if ( gcmd_line.display_info == 119 ) {
    printf("\n\nfacts selected as relevant:\n\n");
    for ( i = 0; i < gnum_relevant_facts; i++ ) {
      printf("\n%d: ", i);
      print_Fact( &(grelevant_facts[i]) );
    }
  }

  changed = TRUE;

  while (changed) {
    changed = FALSE;

    for (a = gdpactions; a; a = a->next) {
      if ( a->norm_operator ) {
	no = a->norm_operator;
	
	if (no->effects == NULL)
	  continue;

	real_precs = no->num_preconds;
	for (k = 0; k  < no->num_preconds; k++) {
	  tmp_fact.predicate = lp = no->preconds[k].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    tmp_fact.args[j] = largs[j] = ( no->preconds[k].args[j] >= 0 ) ?
	      no->preconds[k].args[j] : a->inst_table[DECODE_VAR( no->preconds[k].args[j] )];
	  }
	  
	  adr = fact_adress();
	  if (check_bit_in_bit_table(nlneg, lp, adr))
	    real_precs--;
	}
	
	if (real_precs > 0)
	  continue;

	changed = TRUE;

	for ( ne = no->effects; ne; ne = ne->next ) {
	  for ( i = 0; i < ne->num_adds; i++ ) {
	    tmp_fact.predicate = lp = ne->adds[i].predicate;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      tmp_fact.args[j] = largs[j] = ( ne->adds[i].args[j] >= 0 ) ?
		ne->adds[i].args[j] : a->inst_table[DECODE_VAR( ne->adds[i].args[j] )];
	    }
	

#ifdef __TEST_PD__
	    printf("\nElimino %s\n", print_ft_name_string( retrieve_fact_index(lp, adr, NULL), temp_name ));
#endif	    

	    adr = fact_adress();
	    insert_bit_in_bit_table(nlneg, lp, adr);
	    add_initial = new_Facts();
	    memcpy(add_initial->fact, &tmp_fact, sizeof(Fact));
	    add_initial->next = ginitial;
	    ginitial = add_initial;
	    
	  }
	}

	no->effects = NULL;
	
      }
      else {
	pa = a->pseudo_action;
	
	if (pa->effects == NULL)
	  continue;

	real_precs = pa->num_preconds;
	for (k = 0; k  < pa->num_preconds; k++) {
	  tmp_fact.predicate = lp = pa->preconds[k].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    tmp_fact.args[j] = largs[j] = ( pa->preconds[k].args[j] >= 0 ) ?
	      pa->preconds[k].args[j] : a->inst_table[DECODE_VAR( pa->preconds[k].args[j] )];
	  }
	  
	  adr = fact_adress();
	  if (check_bit_in_bit_table(nlneg, lp, adr))
	    real_precs--;
	}
	
	if (real_precs > 0)
	  continue;
	
	changed = TRUE;

	for ( pae = pa->effects; pae; pae = pae->next ) {
	  for ( i = 0; i < pae->num_adds; i++ ) {
	    tmp_fact.predicate = lp = pae->adds[i].predicate;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      tmp_fact.args[j] = largs[j] = pae->adds[i].args[j];
	    }
	    adr = fact_adress();

#ifdef __TEST_PD__   
	    printf("\nElimino %s\n", print_ft_name_string( retrieve_fact_index(lp, adr, NULL), temp_name ));
#endif	    

	    insert_bit_in_bit_table(nlneg, lp, adr);
	    add_initial = new_Facts();
	    memcpy(add_initial->fact, &tmp_fact, sizeof(Fact));
	    add_initial->next = ginitial;
	    ginitial = add_initial;
	  }
	}
	
	pa->effects = NULL;
      }
    }
  }
    
  lnum_effects = 0;

  /* IFDEF DP */
  if (GpG.derived_predicates)
    optimize_dp_facts_position();
  /* ENDIF */

  create_final_goal_state();
  create_final_initial_state();
  create_final_actions();

  if ( gcmd_line.display_info == 120 ) {
    printf("\n\nfinal domain representation is:\n\n");
    for ( i = 0; i < gnum_operators; i++ ) {
      printf("\n\n------------------operator %s-----------\n\n", goperators[i]->name);
      for ( a = gactions; a; a = a->next ) {
	if ( ( !a->norm_operator &&
	       !a->pseudo_action ) ||
	     ( a->norm_operator && 
	       a->norm_operator->operator != goperators[i] ) ||
	     ( a->pseudo_action &&
	       a->pseudo_action->operator != goperators[i] ) ) {
	  continue;
	}
	print_Action( a );
      }
    }
    printf("\n\n--------------------GOAL REACHED ops-----------\n\n");
    for ( a = gactions; a; a = a->next ) {
      if ( !a->norm_operator &&
	   !a->pseudo_action ) {
	print_Action( a );
      }
    }

    printf("\n\nfinal initial state is:\n\n");
    for ( i = 0; i < ginitial_state.num_F; i++ ) {
      print_ft_name( ginitial_state.F[i] );
      printf("\n");
    }
    printf("\n\nfinal goal state is:\n\n");
    for ( i = 0; i < ggoal_state.num_F; i++ ) {
      print_ft_name( ggoal_state.F[i] );
      printf("\n");
    }
  }

}



void create_final_goal_state( void )

{

  WffNode *w, *ww;
  unsigned long int adr;
  int m, i;
  Action *tmp;

/*
 * DEA - University of Brescia
 */
  // set_relevants_in_wff( &ggoal );
  if (set_relevants_in_wff (&ggoal))
    return;
/*
 * End of DEA
 */
  cleanup_wff( &ggoal );
  if ( ggoal->connective == TRU ) {
/*
 * DEA - University of Brescia
 */
    //    printf("\nff: goal can be simplified to TRUE. The empty plan solves it\n\n");
    printf ("\n%s: goal can be simplified to TRUE. The empty plan solves it\n\n", NAMEPRG);
/*
 * End of DEA
 */
    exit( 1 );
  }
  if ( ggoal->connective == FAL ) {
/*
 * DEA - University of Brescia
 */
    if (!GpG.inst_duplicate_param)
      {
#ifdef __MY_OUTPUT__
	printf("\n%s: create_final_goal_state(): goal can be simplified to FALSE. \n    Please run %s with option  '-inst_with_contraddicting_objects' \n\n", NAMEPRG, NAMEPRG);
#else
	printf("\nGoals of the planning problem can not be reached.\nPlease try to run with '-inst_with_contraddicting_objects'\n\n");
#endif
      }
    else
      {
	printf("\n%s: create_final_goal_state(): goal can be simplified to FALSE.\n    No plan will solve it\n\n", NAMEPRG);
	
      } 

    store_plan(-1.0);

    /*
     * End of DEA
     */
   
    exit( 1 );
  }

  switch ( ggoal->connective ) {
  case OR:
    if ( gnum_relevant_facts == MAX_RELEVANT_FACTS ) {
      printf("\nincrease MAX_RELEVANT_FACTS! (current value: %d)\n\n",
	     MAX_RELEVANT_FACTS);
      exit( 1 );
    }
    grelevant_facts[gnum_relevant_facts].predicate = -3;
    gnum_relevant_facts++;
    for ( w = ggoal->sons; w; w = w->next ) {
      tmp = new_Action();
      tmp->suspected = FALSE;
      if ( w->connective == AND ) {
	m = 0;
	for ( ww = w->sons; ww; ww = ww->next ) m++;
	tmp->preconds = ( int * ) calloc( m, sizeof( int ) );
	tmp->num_preconds = 0;
	for ( ww = w->sons; ww; ww = ww->next ) {
	  lp = ww->fact->predicate;
	  for ( i = 0; i < garity[lp]; i++ ) {
	    largs[i] = ww->fact->args[i];
	  }
	  adr = fact_adress();
	  //tmp->preconds[tmp->num_preconds++] = lindex[lp][adr];
	  tmp->preconds[tmp->num_preconds++] = retrieve_fact_index(lp, adr, NULL);
	}
      } else {
	tmp->preconds = ( int * ) calloc( 1, sizeof( int ) );
	tmp->num_preconds = 1;
	lp = w->fact->predicate;
	for ( i = 0; i < garity[lp]; i++ ) {
	  largs[i] = w->fact->args[i];
	}
	adr = fact_adress();
	//tmp->preconds[0] = lindex[lp][adr];
	tmp->preconds[0] = retrieve_fact_index(lp, adr, NULL);
      }
      tmp->effects = ( ActionEffect * ) calloc( 1, sizeof( ActionEffect ) );
      tmp->num_effects = 1;
      tmp->effects[0].conditions = NULL;
      tmp->effects[0].num_conditions = 0;
      tmp->effects[0].dels = NULL;
      tmp->effects[0].num_dels = 0;
      tmp->effects[0].adds = ( int * ) calloc( 1, sizeof( int ) );
      tmp->effects[0].adds[0] = gnum_relevant_facts - 1;
      tmp->effects[0].num_adds = 1;
      tmp->next = gactions;
      gactions = tmp;
      gnum_actions++;
      lnum_effects++;
    }
    ggoal_state.F[0] = gnum_relevant_facts - 1;
    ggoal_state.num_F = 1;
    break;
  case AND:
    for ( w = ggoal->sons; w; w = w->next ) {
      lp = w->fact->predicate;
      for ( i = 0; i < garity[lp]; i++ ) {
	largs[i] = w->fact->args[i];
      }
      adr = fact_adress();
      //ggoal_state.F[ggoal_state.num_F++] = lindex[lp][adr];
      ggoal_state.F[ggoal_state.num_F++] = retrieve_fact_index(lp, adr, NULL);
    }
    break;
  case ATOM:
    ggoal_state.num_F = 1;
    lp = ggoal->fact->predicate;
    for ( i = 0; i < garity[lp]; i++ ) {
      largs[i] = ggoal->fact->args[i];
    }
    adr = fact_adress();
    //ggoal_state.F[0] = lindex[lp][adr];
    ggoal_state.F[0] = retrieve_fact_index(lp, adr, NULL);
    break;
  default:
    printf("\n\nwon't get here: non ATOM,AND,OR in fully simplified goal\n\n");
    exit( 1 );
  }

}


/*
 * DEA - University of Brescia
 */
// void set_relevants_in_wff( WffNode **w )
int  set_relevants_in_wff( WffNode **w )
/*
 * End of DEA
 */

{

  WffNode *i;
  unsigned long int adr;
  int j;

  switch ( (*w)->connective ) {
  case AND:
  case OR:
    for ( i = (*w)->sons; i; i = i->next ) {
      set_relevants_in_wff( &i );
    }
    break;
  case ATOM:
    /* no equalities, as fully instantiated
     */
    lp = (*w)->fact->predicate;
    for ( j = 0; j < garity[lp]; j++ ) {
      largs[j] = (*w)->fact->args[j];
    }
    adr = fact_adress();

    /*
    if ( !lneg[lp][adr] )
    */
    if (check_bit_in_bit_table(nlneg, lp, adr)) {
      (*w)->connective = TRU;
      free( (*w)->fact );
      (*w)->fact = NULL;
      break;
    }
    
    /*
    if ( !lpos[lp][adr] )
    */ 

    if (!check_bit_in_bit_table(lpos, lp, adr)) {

      if (DEBUG3)
	{
	  printf("\nNOT POSSIBLY POSITIVE FACT : %s", gpredicates[lp]);
	  
	  for (j = 0; j <  garity[lp]; j++)
	    printf(" %s", gconstants[largs[j]]);
	}

      (*w)->connective = FAL;
      free( (*w)->fact );
      (*w)->fact = NULL;
      break;
    }
    break;
  default:
    printf("\n\nwon't get here: non NOT,OR,AND in goal set relevants\n\n");
/*
 * DEA - University of Brescia
 */
    return 1;
    //    exit( 1 );
/*
 * End of DEA
 */
  }
/*
 * DEA - University of Brescia
 */
  return 0;
/*
 * End of DEA
 */

}



void create_final_initial_state( void )

{

  Facts *f;
  unsigned long int adr;
  int i;

  for ( f = ginitial; f; f = f->next ) {
    lp = f->fact->predicate;
    for ( i = 0; i < garity[lp]; i++ ) {
      largs[i] = f->fact->args[i];
    }
    adr = fact_adress();

    /*
    if ( !lneg[lp][adr] )
    */
    
    if (check_bit_in_bit_table(nlneg, lp, adr)) {
      /* non deleted ini */
      continue;
    }

    if ( ginitial_state.num_F == MAX_STATE ) {
      printf("\ntoo many initial facts! increase MAX_STATE(%d)\n\n",
	     MAX_STATE);
      exit( 1 );
    }

    //ginitial_state.F[ginitial_state.num_F++] = lindex[lp][adr];
    ginitial_state.F[ginitial_state.num_F++] = retrieve_fact_index(lp, adr, NULL);
  }
 
}



void create_final_actions( void )

{

  Action *a;
  NormOperator *no;
  NormEffect *ne;
  unsigned long int adr;
  int i, j, h, count;
  PseudoAction *pa;
  PseudoActionEffect *pae;

  Action **a_pointer;

  count = 0;
  for (a_pointer = &gactions; count < 2; a_pointer = &gdpactions, count++) {
    for ( a = (*a_pointer); a; a = a->next ) {
      if ( a->norm_operator ) {
	/* action comes from an easy template NormOp
	 */
	no = a->norm_operator;
	
	if ( no->num_preconds > 0 ) {
	  a->preconds = ( int * ) calloc( no->num_preconds, sizeof( int ) );
	}
	a->num_preconds = 0;
	for ( i = 0; i < no->num_preconds; i++ ) {
	  lp = no->preconds[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = ( no->preconds[i].args[j] >= 0 ) ?
	      no->preconds[i].args[j] : a->inst_table[DECODE_VAR( no->preconds[i].args[j] )];
	  }
	  adr = fact_adress();

	  /* preconds are lpos in all cases due to reachability analysis
	   */

	  /*
	  if ( !lneg[lp][adr] )
	  */

	  if (check_bit_in_bit_table(nlneg, lp, adr)) {
	    continue;
	  }
	  
	  //a->preconds[a->num_preconds++] = lindex[lp][adr];
	  a->preconds[a->num_preconds++] = retrieve_fact_index(lp, adr, NULL); 
	}
	
	if ( a->num_effects > 0 ) {
	  a->effects = ( ActionEffect * ) calloc( a->num_effects, sizeof( ActionEffect ) );
	}
	a->num_effects = 0;
	for ( ne = no->effects; ne; ne = ne->next ) {
	  if ( ne->num_conditions > 0 ) {
	    a->effects[a->num_effects].conditions =
	      ( int * ) calloc( ne->num_conditions, sizeof( int ) );
	  }
	  a->effects[a->num_effects].num_conditions = 0;
	  
	  for ( i = 0; i < ne->num_conditions; i++ ) {
	    lp = ne->conditions[i].predicate;
	    h = ( lp < 0 ) ? 2 : garity[lp];
	    for ( j = 0; j < h; j++ ) {
	      largs[j] = ( ne->conditions[i].args[j] >= 0 ) ?
		ne->conditions[i].args[j] : a->inst_table[DECODE_VAR( ne->conditions[i].args[j] )];
	    }
	    if ( lp >= 0 ) {
	      adr = fact_adress();
	      
	      /*
	      if ( !lpos[lp][adr] )
	      */
	      
	      if (!check_bit_in_bit_table(lpos, lp, adr)) {
		/* condition not reachable: skip effect */
		break;
	       
	      }
	      
	      /*
	      if ( !lneg[lp][adr] )
	      */ 
	      
	      if (check_bit_in_bit_table(nlneg, lp, adr)) {
		/* condition always true: skip it */
		continue;
	      }
	      //a->effects[a->num_effects].conditions[a->effects[a->num_effects].num_conditions++] =
	      //lindex[lp][adr];
	      a->effects[a->num_effects].conditions[a->effects[a->num_effects].num_conditions++] =
		retrieve_fact_index(lp, adr, NULL);

	    } else {
	      if ( lp == -2 ) {
		if ( largs[0] == largs[1] ) break;
	      } else {
		if ( largs[0] != largs[1] ) break;
	      }
	    }
	  }
	  
	  if ( i < ne->num_conditions ) {/* found unreachable condition: free condition space */
	    free( a->effects[a->num_effects].conditions );
	    continue;
	  }
	  
	  /* now create the add and del effects.
	   */
	  if ( ne->num_adds > 0 ) {
	    a->effects[a->num_effects].adds = ( int * ) calloc( ne->num_adds, sizeof( int ) );
	  }
	  a->effects[a->num_effects].num_adds = 0;
	  for ( i = 0; i < ne->num_adds; i++ ) {
	    lp = ne->adds[i].predicate;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      largs[j] = ( ne->adds[i].args[j] >= 0 ) ?
		ne->adds[i].args[j] : a->inst_table[DECODE_VAR( ne->adds[i].args[j] )];
	    }
	    adr = fact_adress();
	    
	    /*
	      if ( !lneg[lp][adr] )
	    */

	    if (check_bit_in_bit_table(nlneg, lp, adr)) {
	      /* effect always true: skip it */
	      continue;
	    }
	    
	    //a->effects[a->num_effects].adds[a->effects[a->num_effects].num_adds++] = lindex[lp][adr];
	    a->effects[a->num_effects].adds[a->effects[a->num_effects].num_adds++] = retrieve_fact_index(lp, adr, NULL);
	  }
	  
	  if ( ne->num_dels > 0 ) {
	    a->effects[a->num_effects].dels = ( int * ) calloc( ne->num_dels, sizeof( int ) );
	  }
	  a->effects[a->num_effects].num_dels = 0;
	  for ( i = 0; i < ne->num_dels; i++ ) {
	    lp = ne->dels[i].predicate;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      largs[j] = ( ne->dels[i].args[j] >= 0 ) ?
		ne->dels[i].args[j] : a->inst_table[DECODE_VAR( ne->dels[i].args[j] )];
	    }
	    adr = fact_adress();
	    
	    /*
	    if ( !lpos[lp][adr] ) 
	    */ 

	    if (!check_bit_in_bit_table(lpos, lp, adr)) {
	      /* effect always false: skip it */
	      continue;
	    }
	    
	    //a->effects[a->num_effects].dels[a->effects[a->num_effects].num_dels++] = lindex[lp][adr];
	    a->effects[a->num_effects].dels[a->effects[a->num_effects].num_dels++] = retrieve_fact_index(lp, adr, NULL);
	  }
	  
	  /* this effect is OK. go to next one in NormOp.
	   */
	  a->num_effects++;
	  lnum_effects++;
	}
	continue;
      }
      if ( a->pseudo_action ) {
	/* action is result of a PseudoAction
	 */
	pa = a->pseudo_action;

	if ( pa->num_preconds > 0 ) {
	  a->preconds = ( int * ) calloc( pa->num_preconds, sizeof( int ) );
	}
	a->num_preconds = 0;
	for ( i = 0; i < pa->num_preconds; i++ ) {
	  lp = pa->preconds[i].predicate;
	  for ( j = 0; j < garity[lp]; j++ ) {
	    largs[j] = pa->preconds[i].args[j];
	  }
	  adr = fact_adress();
	  
	  /* preconds are lpos in all cases due to reachability analysis
	   */
	  
	  /*
	  if ( !lneg[lp][adr] )
	  */

	  if (check_bit_in_bit_table(nlneg, lp, adr)) {
	    continue;
	  }
	  
	  //a->preconds[a->num_preconds++] = lindex[lp][adr];
	  a->preconds[a->num_preconds++] = retrieve_fact_index(lp, adr, NULL);
	}
	
	if ( a->num_effects > 0) {
	  a->effects = ( ActionEffect * ) calloc( a->num_effects, sizeof( ActionEffect ) );
	}
	a->num_effects = 0;
	for ( pae = pa->effects; pae; pae = pae->next ) {
	  if ( pae->num_conditions > 0 ) {
	    a->effects[a->num_effects].conditions =
	      ( int * ) calloc( pae->num_conditions, sizeof( int ) );
	  }
	  a->effects[a->num_effects].num_conditions = 0;
	  
	  for ( i = 0; i < pae->num_conditions; i++ ) {
	    lp = pae->conditions[i].predicate;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      largs[j] = pae->conditions[i].args[j];
	    }
	    adr = fact_adress();
	    

	    /*
	    if ( !lpos[lp][adr] )
	    */

	    if (!check_bit_in_bit_table(lpos, lp, adr)) {
	      /* condition not reachable: skip effect */
	      break;
	    }
	    
	    /*
	    if ( !lneg[lp][adr] )
	    */

	    if (check_bit_in_bit_table(nlneg, lp, adr)) {
	      /* condition always true: skip it */
	      continue;
	    }
	    
	    //a->effects[a->num_effects].conditions[a->effects[a->num_effects].num_conditions++] =
	    //lindex[lp][adr];
	    a->effects[a->num_effects].conditions[a->effects[a->num_effects].num_conditions++] =
	      retrieve_fact_index(lp, adr, NULL);

	  }
	  
	  if ( i < pae->num_conditions ) {/* found unreachable condition: free condition space */
	    free( a->effects[a->num_effects].conditions );
	    continue;
	  }
	  
	  /* now create the add and del effects.
	   */
	  if ( pae->num_adds > 0 ) {
	    a->effects[a->num_effects].adds = ( int * ) calloc( pae->num_adds, sizeof( int ) );
	  }
	  a->effects[a->num_effects].num_adds = 0;
	  for ( i = 0; i < pae->num_adds; i++ ) {
	    lp = pae->adds[i].predicate;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      largs[j] = pae->adds[i].args[j];
	    }
	    adr = fact_adress();
	    
	    /*
	    if ( !lneg[lp][adr] )
	    */
	    
	    if (check_bit_in_bit_table(nlneg, lp, adr)) {
	      /* effect always true: skip it */
	      continue;
	    }
	    
	    //a->effects[a->num_effects].adds[a->effects[a->num_effects].num_adds++] = lindex[lp][adr];
	    a->effects[a->num_effects].adds[a->effects[a->num_effects].num_adds++] = retrieve_fact_index(lp, adr, NULL);
	  }
	  
	  if ( pae->num_dels > 0 ) {
	    a->effects[a->num_effects].dels = ( int * ) calloc( pae->num_dels, sizeof( int ) );
	  }
	  a->effects[a->num_effects].num_dels = 0;
	  for ( i = 0; i < pae->num_dels; i++ ) {
	    lp = pae->dels[i].predicate;
	    for ( j = 0; j < garity[lp]; j++ ) {
	      largs[j] = pae->dels[i].args[j];
	    }
	    adr = fact_adress();
	    
	    /*
	    if ( !lpos[lp][adr] )
	    */

	    if (!check_bit_in_bit_table(lpos, lp, adr)) {
	      /* effect always false: skip it */
	      continue;
	    }
	    
	    // a->effects[a->num_effects].dels[a->effects[a->num_effects].num_dels++] = lindex[lp][adr];
	    a->effects[a->num_effects].dels[a->effects[a->num_effects].num_dels++] = retrieve_fact_index(lp, adr, NULL);
	  }
	  
	  /* this effect is OK. go to next one in PseudoAction.
	   */
	  a->num_effects++;
	  lnum_effects++;
	}
      }/* end of if clause for PseudoAction */
      /* if action was neither normop, nor pseudo action determined,
       * then it is an artificial action due to disjunctive goal
       * conditions.
       *
       * these are already in final form.
       */
    }/* end for all actions ! */

  } /* END FOR BOTH ACTIONS AND DERIVED PREDICATES  */

}












/**************************************************
 * CONNECTIVITY GRAPH. ULTRA CLEAN REPRESENTATION *
 **************************************************/












/*
-----------------------------------------------------------------
	DESCRIPTION	: Verifica se le azioni condizionali sono abilitate
	PARAMETER	:
	RETURN		: TRUE Effetti condizionali abilitate
			  FALSE Effetti condizionali disabilitati
-----------------------------------------------------------------
*/
int cond_eff_is_enabled()
{
  return(GpG.conditional_effects_enabled);
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Calcola il numero di effetti condizionali
			  che utilizzano i fatti
	PARAMETER	: void
	RETURN		: void
-----------------------------------------------------------------
*/
void calc_num_conditional_fact()
{
	CondEfConn	*cef;
	int		i;

	for (cef = gcondef_conn; cef < &gcondef_conn[gnum_condef_conn]; cef++) {
		for ( i = 0; i < cef->num_PC; i++ )
			gcondft_conn[cef->PC[i]].num_PC++;
		for ( i = 0; i < cef->num_A; i++ )
			gcondft_conn[cef->A[i]].num_A++;
		for ( i = 0; i < cef->num_D; i++ )
			gcondft_conn[cef->D[i]].num_D++;
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: alloca lo spazio per la struttura gcondft_conn
	PARAMETER	: void
	RETURN		: void
-----------------------------------------------------------------
*/
void new_conditional_fact()
{
	CondFtConn	*cft;

	for (cft = gcondft_conn; cft < &gcondft_conn[gnum_condft_conn]; cft++ ) {
		if (cft->num_PC)
			cft->PC = (int *)calloc(cft->num_PC, sizeof(int));
		cft->num_PC = 0;
		if (cft->num_A)
			cft->A = (int *)calloc(cft->num_A, sizeof(int));
		cft->num_A = 0;
		if (cft->num_D)
			cft->D = (int *)calloc(cft->num_D, sizeof(int));
		cft->num_D = 0;
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: crea la struttura gcondft_conn
	PARAMETER	: void
	RETURN		: void
-----------------------------------------------------------------
*/
void create_conditional_fact()
{
	CondEfConn	*cef;
	int		j;

	calc_num_conditional_fact();
	new_conditional_fact();

	for (cef = gcondef_conn; cef < &gcondef_conn[gnum_condef_conn]; cef++) {
		for ( j = 0; j < cef->num_PC; j++ )
			gcondft_conn[cef->PC[j]].PC[gcondft_conn[cef->PC[j]].num_PC++] = cef - gcondef_conn;
		for ( j = 0; j < cef->num_A; j++ )
			gcondft_conn[cef->A[j]].A[gcondft_conn[cef->A[j]].num_A++] = cef - gcondef_conn;
		for ( j = 0; j < cef->num_D; j++ )
			gcondft_conn[cef->D[j]].D[gcondft_conn[cef->D[j]].num_D++] = cef - gcondef_conn;
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Calcola il numero di effetti condizionali
	PARAMETER	: void
	RETURN		: void
-----------------------------------------------------------------
*/
void calc_num_cond_action(void)
{
	Action		*a;
	ActionEffect	*e;

	if (cond_eff_is_enabled()) {
		for (lnum_cond_effects = 0, a = gactions; a; a = a->next)
			for (e = a->effects; e <= &(a->effects[a->num_effects - 1]); e++)
				if (e->conditions)
					lnum_cond_effects++;
	} else
		lnum_cond_effects = 0;
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Crea un effetto in EfConn
	PARAMETER	: *ce	CondEfConn in cui inserire
			   nc	Numero precondizioni
			   na	Numero effetti additivi
			   nd	Numero effetti cancellanti
	RETURN		: void
-----------------------------------------------------------------
*/
void new_ef_conn(EfConn *e, int nc, int na, int nd)
{
	int	tmpnum;

	tmpnum = get_num_of_effects_of(e->op, AT_END_TIME, 1);
	e->A = (int *)calloc(na + tmpnum, sizeof(int));
	e->D = (int *)calloc(nd, sizeof(int));

	tmpnum = get_num_of_effects_of(e->op, AT_START_TIME, 1);
	if (tmpnum) {
		if (e->sf == NULL)
			e->sf = new_SpecialFacts();
		e->sf->A_start = (int *)calloc(tmpnum, sizeof (int));
	}

	tmpnum = get_num_of_effects_of(e->op, AT_START_TIME, 0);
	if (tmpnum) {
		if (e->sf == NULL)
			e->sf = new_SpecialFacts();
		e->sf->D_start =(int *)calloc(tmpnum, sizeof (int));
	}

	tmpnum = get_num_of_preconds_of(e->op, AT_START_TIME);
	e->PC = (int *)calloc(nc + tmpnum, sizeof(int));
//	e->PC = (int *)calloc(e->num_conditions + a->num_preconds + tmpnum, sizeof(int));

	tmpnum = get_num_of_preconds_of(e->op, OVER_ALL_TIME);
	if (tmpnum) {
		if (e->sf == NULL)
			e->sf = new_SpecialFacts();
		e->sf->PC_overall = (int *)calloc(tmpnum, sizeof(int));
	}

	tmpnum = get_num_of_preconds_of(e->op, AT_END_TIME);
	if (tmpnum) {
		if (e->sf == NULL)
			e->sf = new_SpecialFacts();
		e->sf->PC_end = (int *)calloc(tmpnum, sizeof(int));
	}
	
	e->suspected = FALSE;

}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Crea un effetto condizionali in CondEfConn
	PARAMETER	: *ce	CondEfConn in cui inserire
			   nc	Numero condizioni
			   na	Numero effetti additivi
			   nd	Numero effetti cancellanti
	RETURN		: void
-----------------------------------------------------------------
*/
void new_condef_conn(CondEfConn *ce, int nc, int na, int nd)
{
	int	tmpnum;

	tmpnum = get_num_of_effects_of(ce->op, AT_END_TIME, 1);
	ce->A = (int *)calloc(na + tmpnum, sizeof(int));

	tmpnum = get_num_of_preconds_of(ce->op, AT_START_TIME);
	ce->PC = (int *)calloc(nc + tmpnum, sizeof(int));

	ce->D = (int *)calloc(nd, sizeof(int));

	ce->plop = gef_conn[ce->op].plop;
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Verifica se un effetto di una azione è
			  condizionale (se abilitato)
	PARAMETER	: *a	Azione
			   effect Effetto
	RETURN		: TRUE Effetto condizionale
			  FALSE Non è effetto condizionale
-----------------------------------------------------------------
*/
int is_implied_effect(Action *a, int effect)
{
	if (a->num_effects == 1)
		return(FALSE);

	if ((cond_eff_is_enabled()) && (a->effects[effect].num_conditions))
		return(TRUE);
	else
		return(FALSE);
}

void build_connectivity_graph( void )
{

  int i, j, k, l, n_op, n_ef, n_cef, m, na, nd;
  Action *a;
  int *same_effects, sn;
  Bool *had_effects;
  ActionEffect *e, *e_;
  int num;
  int *fact;


/*
 * DEA - University of Brescia
 */
  //  struct timeb tp;

  int sizeofgop, sizeofgef, sizeofgft;

  sizeofgop = 0;
  sizeofgef = 0;
  sizeofgft = 0;

  //  ftime( &tp );
  //  srandom( tp.millitm );

  srandom(seed);

/*
 * End of DEA
 */


  gnum_ft_conn = gnum_relevant_facts;
/*
 * DEA - University of Brescia
 */
  gnum_ft_block = gnum_ft_conn / 32 + 1;
/*
 * End of DEA
 */
  calc_num_cond_action();
  gnum_op_conn = gnum_actions;
  gnum_condft_conn = gnum_ft_conn;
  gft_conn = ( FtConn * ) calloc( gnum_ft_conn, sizeof( FtConn ) );
  gop_conn = ( OpConn * ) calloc( gnum_op_conn, sizeof( OpConn ) );
  gef_conn = ( EfConn * ) calloc( lnum_effects, sizeof( EfConn ) );
  gcondft_conn = ( CondFtConn * ) calloc( gnum_condft_conn, sizeof( CondFtConn ) );
  gcondef_conn = ( CondEfConn * ) calloc( lnum_cond_effects, sizeof( CondEfConn ) );
  gnum_ef_conn = 0;
  gnum_condef_conn = 0;

  same_effects = ( int * ) calloc( lnum_effects, sizeof( int ) );
  had_effects = ( Bool * ) calloc( lnum_effects, sizeof( Bool ) );

  for ( i = 0; i < gnum_ft_conn; i++ ) {
    gft_conn[i].num_PC = 0;
    gft_conn[i].num_A = 0;
    gft_conn[i].num_D = 0;
    gft_conn[i].num_dp_A = 0;
    gft_conn[i].num_dp_D = 0;
    gft_conn[i].num_dp_PC = 0;
    gft_conn[i].dp_PC = NULL;
    gft_conn[i].dp_A = NULL;
    gft_conn[i].dp_D = NULL;
    gft_conn[i].fact_type = IS_BASE;
    gft_conn[i].tmd_facts_array = NULL;
    gft_conn[i].num_tmd_facts_array = 0;
   
/*
 * DEA - University of Brescia
 */
    // gft_conn[i].rand = random () % BIG_INT;
   gft_conn[i].rand = MY_RANDOM % BIG_INT;
/*
 * End of DEA
 */
  }

  for ( i = 0; i < gnum_op_conn; i++ ) {
    gop_conn[i].num_E = 0;
  }


  /*
    EfConns reset
  */
  for ( i = 0; i < lnum_effects; i++ ) {
    gef_conn[i].num_PC = 0;
    gef_conn[i].num_A = 0;
    gef_conn[i].num_D = 0;
    gef_conn[i].num_I = 0;
    gef_conn[i].timed_PC = NULL;
    gef_conn[i].suspected = FALSE;
    gef_conn[i].is_numeric = gef_conn[i].has_numeric_precs = FALSE;
    gef_conn[i].metric_vars = NULL;
  }

  gfirst_suspected_ef_conn = 0;

  n_op = 0;
  n_ef = 0;
  n_cef = 0;
  for ( a = gactions; a; a = a->next ) {

    gop_conn[n_op].action = a;

    gop_conn[n_op].E = ( int * ) calloc( a->num_effects, sizeof( int ) );
    gop_conn[n_op].I = ( int * ) calloc( a->num_effects, sizeof( int ) );
    for ( i = 0; i < a->num_effects; i++ ) {
      had_effects[i] = FALSE;
    }
    for ( i = 0; i < a->num_effects; i++ ) {
      if ( had_effects[i] ) {
	continue;
      }
      had_effects[i] = TRUE;
      e = &(a->effects[i]);
      if (is_implied_effect(a, i))
	gop_conn[n_op].I[gop_conn[n_op].num_I++] = n_cef;
      else
	gop_conn[n_op].E[gop_conn[n_op].num_E++] = n_ef;

      gef_conn[n_ef].op = n_op;

      sn = 0;
      for ( j = i + 1; j < a->num_effects; j++ ) {
	if ( had_effects[j] ) {
	  continue;
	}
	e_ = &(a->effects[j]);
	/* check conditions
	 */
	for ( k = 0; k < e_->num_conditions; k++ ) {
	  for ( l = 0; l < e->num_conditions; l++ ) {
	    if ( e_->conditions[k] == e->conditions[l] ) {
	      break;
	    }
	  }
	  if ( l == e->num_conditions ) {
	    break;
	  }
	}
	if ( k < e_->num_conditions ) {
	  continue;
	}
	if ( e->num_conditions == e_->num_conditions ) {
	  same_effects[sn++] = j;
	}
      }

      na = e->num_adds;
      nd = e->num_dels;
      for ( j = 0; j < sn; j++ ) {
	na += a->effects[same_effects[j]].num_adds;
	nd += a->effects[same_effects[j]].num_dels;
      }
/*
 * DEA - University of Brescia
 */
      if (is_implied_effect(a, i)) {		// creazione nuovo effetto condizionale (se esiste)
//	gcondef_conn[n_cef].ef = n_ef;
	gcondef_conn[n_cef].ef = n_op;		// n operator = n_effect
	gcondef_conn[n_cef].op = n_op;
	new_condef_conn(&gcondef_conn[n_cef], e->num_conditions, na, nd);
      } else {
	new_ef_conn(&gef_conn[n_ef], e->num_conditions + a->num_preconds, na, nd);
      }
/*
 * End of DEA
 */
      fact = is_implied_effect(a, i) ? gcondef_conn[n_cef].A : gef_conn[n_ef].A;
      for ( num = 0, j = 0; j < e->num_adds; j++ ) {
	for ( k = 0; k < num; k++ ) {
	  if ( fact[k] == e->adds[j] ) break;
	}
	if ( k < num ) continue;
	if (is_implied_effect(a, i))
	  gcondef_conn[n_cef].A[gcondef_conn[n_cef].num_A++] = e->adds[j];
	else
	  gef_conn[n_ef].A[gef_conn[n_ef].num_A++] = e->adds[j];
	num++;
      }
      fact = is_implied_effect(a, i) ? gcondef_conn[n_cef].D : gef_conn[n_ef].D;
      for ( num = 0, j = 0; j < e->num_dels; j++ ) {
	for ( k = 0; k < num; k++ ) {
	  if ( fact[k] == e->dels[j] ) break;
	}
	if ( k < num ) continue;
	if (is_implied_effect(a, i))
	  gcondef_conn[n_cef].D[gcondef_conn[n_cef].num_D++] = e->dels[j];
	else
	  gef_conn[n_ef].D[gef_conn[n_ef].num_D++] = e->dels[j];
	num++;
      }
      for ( j = 0; j < sn; j++ ) {
	e_ = &(a->effects[same_effects[j]]);
	fact = is_implied_effect(a, i) ? gcondef_conn[n_cef].A : gef_conn[n_ef].A;
	num = is_implied_effect(a, i) ? gcondef_conn[n_cef].num_A : gef_conn[n_ef].num_A;
	for ( l = 0; l < e_->num_adds; l++ ) {
	  for ( k = 0; k < num; k++ ) {
	    if ( fact[k] == e_->adds[l] ) break;
	  }
	  if ( k < num ) continue;
	  if (is_implied_effect(a, i))
	    gcondef_conn[n_cef].A[gcondef_conn[n_cef].num_A++] = e_->adds[l];
	  else
	    gef_conn[n_ef].A[gef_conn[n_ef].num_A++] = e_->adds[l];
	  num++;
	}
	fact = is_implied_effect(a, i) ? gcondef_conn[n_cef].D : gef_conn[n_ef].D;
	num = is_implied_effect(a, i) ? gcondef_conn[n_cef].num_D : gef_conn[n_ef].num_D;
	for ( l = 0; l < e_->num_dels; l++ ) {
	  for ( k = 0; k < num; k++ ) {
	    if ( fact[k] == e_->dels[l] ) break;
	  }
	  if ( k < num ) continue;
	  if (is_implied_effect(a, i))
	    gcondef_conn[n_cef].D[gcondef_conn[n_cef].num_D++] = e_->dels[l];
	  else
	    gef_conn[n_ef].D[gef_conn[n_ef].num_D++] = e_->dels[l];
	  num++;
	}
      }
      a->effects[i].ef_conn_pos = n_op;
      if (is_implied_effect(a, i))
	a->effects[i].condef_conn_pos = n_cef;
      else
	a->effects[i].condef_conn_pos = -1;

      for ( j = 0; j < sn; j++ ) {
	had_effects[same_effects[j]] = TRUE;
	a->effects[same_effects[j]].ef_conn_pos = n_ef;
      }
   
      if (!is_implied_effect(a, i))
	for ( j = 0; j < a->num_preconds; j++ ) {
	  for ( k = 0; k < gef_conn[n_ef].num_PC; k++ ) {
	    if ( gef_conn[n_ef].PC[k] == a->preconds[j] ) break;
	  }
	  if ( k < gef_conn[n_ef].num_PC ) continue;
	  gef_conn[n_ef].PC[gef_conn[n_ef].num_PC++] = a->preconds[j];
        }
      fact = is_implied_effect(a, i) ? gcondef_conn[n_cef].PC : gef_conn[n_ef].PC;
      num = is_implied_effect(a, i) ? 0 : gef_conn[n_ef].num_PC;
      for ( j = 0; j < e->num_conditions; j++ ) {
	for ( k = 0; k < num; k++ ) {
	  if ( fact[k] == e->conditions[j] ) break;
	}
	if ( k < num ) continue;
	if (is_implied_effect(a, i))
	  gcondef_conn[n_cef].PC[gcondef_conn[n_cef].num_PC++] = e->conditions[j];
	else
	  gef_conn[n_ef].PC[gef_conn[n_ef].num_PC++] = e->conditions[j];
	num++;
      }

      if (is_implied_effect(a, i)) {
	n_cef++;
	gnum_condef_conn++;
      } else {
	n_ef++;

	if (a->suspected)
	  {
	    gef_conn[gnum_ef_conn].suspected = TRUE;
	    if (!gfirst_suspected_ef_conn)
	      gfirst_suspected_ef_conn = gnum_ef_conn;
	  }
	
	gnum_ef_conn++;
      }
    }/* ende all a->effects */

    /* setup implied effects info
     */
    if (cond_eff_is_enabled()) {
	gef_conn[n_ef - 1].I = gop_conn[n_op].I;
	gef_conn[n_ef - 1].num_I = gop_conn[n_op].num_I;
    } else {
      if ( a->num_effects > 1 ) {
        m = 0;
        for ( i = a->effects[0].ef_conn_pos; i < n_ef - 1; i++ ) {
	  for ( j = i+1; j < n_ef; j++ ) {
	    // i ==> j ?
	    for ( k = 0; k < gef_conn[j].num_PC; k++ ) {
	      for ( l = 0; l < gef_conn[i].num_PC; l++ ) {
	        if ( gef_conn[i].PC[l] == gef_conn[j].PC[k] ) break;
	      }
	      if ( l == gef_conn[i].num_PC ) break;
	    }
	    if ( k == gef_conn[j].num_PC ) {
	      gef_conn[i].num_I++;
	    }
	    // j ==> i ?
	    for ( k = 0; k < gef_conn[i].num_PC; k++ ) {
	      for ( l = 0; l < gef_conn[j].num_PC; l++ ) {
	        if ( gef_conn[j].PC[l] == gef_conn[i].PC[k] ) break;
	      }
	      if ( l == gef_conn[j].num_PC ) break;
	    }
	    if ( k == gef_conn[i].num_PC ) {
	      gef_conn[j].num_I++;
	    }
	  }
        }
        for ( i = a->effects[0].ef_conn_pos; i < n_ef; i++ ) {
	  gef_conn[i].I = ( int * ) calloc( gef_conn[i].num_I, sizeof( int ) );
	  gef_conn[i].num_I = 0;
        }
        for ( i = a->effects[0].ef_conn_pos; i < n_ef - 1; i++ ) {
	  for ( j = i+1; j < n_ef; j++ ) {
	    // i ==> j ?
	    for ( k = 0; k < gef_conn[j].num_PC; k++ ) {
	      for ( l = 0; l < gef_conn[i].num_PC; l++ ) {
	        if ( gef_conn[i].PC[l] == gef_conn[j].PC[k] ) break;
	      }
	      if ( l == gef_conn[i].num_PC ) break;
	    }
	    if ( k == gef_conn[j].num_PC ) {
	      gef_conn[i].I[gef_conn[i].num_I++] = j;
	    }
	    // j ==> i ?
	    for ( k = 0; k < gef_conn[i].num_PC; k++ ) {
	      for ( l = 0; l < gef_conn[j].num_PC; l++ ) {
	        if ( gef_conn[j].PC[l] == gef_conn[i].PC[k] ) break;
	      }
	      if ( l == gef_conn[j].num_PC ) break;
	    }
	    if ( k == gef_conn[i].num_PC ) {
	      gef_conn[j].I[gef_conn[j].num_I++] = i;
	    }
	  }
        }
      }
    }

    /* first sweep: only count the space we need for the fact arrays !
     */
    if ( a->num_effects > 0 ) {
      for ( i = a->effects[0].ef_conn_pos; i < n_ef; i++ ) {
	for ( j = 0; j < gef_conn[i].num_PC; j++ ) {
	  gft_conn[gef_conn[i].PC[j]].num_PC++;
	}
	for ( j = 0; j < gef_conn[i].num_A; j++ ) {
	  gft_conn[gef_conn[i].A[j]].num_A++;
	}
	for ( j = 0; j < gef_conn[i].num_D; j++ ) {
	  gft_conn[gef_conn[i].D[j]].num_D++;
	}
      }
    }

    n_op++;
  }

  for ( i = 0; i < gnum_ft_conn; i++ ) {
    gft_conn[i].PC = ( int * ) calloc( gft_conn[i].num_PC, sizeof( int ) );
    gft_conn[i].num_PC = 0;
    gft_conn[i].A = ( int * ) calloc( gft_conn[i].num_A, sizeof( int ) );
    gft_conn[i].num_A = 0;
    gft_conn[i].D = ( int * ) calloc( gft_conn[i].num_D, sizeof( int ) );
    gft_conn[i].num_D = 0;

    gft_conn[i].is_global_goal = FALSE;
  }

  for ( i = 0; i < ggoal_state.num_F; i++ ) {
    gft_conn[ggoal_state.F[i]].is_global_goal = TRUE;
  }

  if (!gfirst_suspected_ef_conn)
    gfirst_suspected_ef_conn = gnum_ef_conn;

  for ( i = 0; i < gfirst_suspected_ef_conn; i++ ) {
    
    for ( j = 0; j < gef_conn[i].num_PC; j++ ) {
      gft_conn[gef_conn[i].PC[j]].PC[gft_conn[gef_conn[i].PC[j]].num_PC++] = i;
    }
    for ( j = 0; j < gef_conn[i].num_A; j++ ) {

      /*
       * Non inserisco l'azione tra quelle che supportano l'effetto se esso compare
       * anche nelle precondizioni dell'azione e se il dominio è strips 
       * (quindi precondizioni at-start e effetti at-end)
       */
      if (!GpG.non_strips_domain 
	  && is_fact_in_preconditions(i, gef_conn[i].A[j]))
	continue;
      
      gft_conn[gef_conn[i].A[j]].A[gft_conn[gef_conn[i].A[j]].num_A++] = i;
    }
    for ( j = 0; j < gef_conn[i].num_D; j++ ) {
      gft_conn[gef_conn[i].D[j]].D[gft_conn[gef_conn[i].D[j]].num_D++] = i;
    }
  }

  create_conditional_fact();

  free( same_effects );
  free( had_effects );
  if ( gcmd_line.display_info == 121 ) {
    printf("\n\ncreated connectivity graph as follows:");

    printf("\n\n------------------OP ARRAY:-----------------------");
    for ( i = 0; i < gnum_op_conn; i++ ) {
/*
 * DEA - University of Brescia
 */
      sizeofgop += sizeof (gop_conn[i]) + sizeof (int) * (gop_conn[i].num_E - 1);
/*
 * End of DEA
 */
      printf("\n\nOP: ");
      print_op_name( i );
      printf("\n----------EFFS:");
      for ( j = 0; j < gop_conn[i].num_E; j++ ) {
	printf("\neffect %d", gop_conn[i].E[j]);
      }
      for ( j = 0; j < gop_conn[i].num_I; j++ ) {
	printf("\nimplied effect %d", gop_conn[i].I[j]);
      }
/*
 * DEA - University of Brescia
 */
	  printf ("\nSIZE = %d", sizeof (gop_conn[i]) + sizeof (int) * (gop_conn[i].num_E - 1));
/*
 * End of DEA
 */
    }

    printf("\n\n-------------------EFFECT ARRAY:----------------------");
    for ( i = 0; i < gnum_ef_conn; i++ ) {
/*
 * DEA - University of Brescia
 */
      sizeofgef += sizeof (gef_conn[i]) + sizeof (int) * (gef_conn[i].num_PC - 1) +
	sizeof (int) * (gef_conn[i].num_A - 1) + sizeof (int) * (gef_conn[i].num_D - 1);
/*
 * End of DEA
 */
      printf("\n\neffect %d of op %d: ", i, gef_conn[i].op);
      print_op_name( gef_conn[i].op );
      printf("\n----------PCS:");
      for ( j = 0; j < gef_conn[i].num_PC; j++ ) {
	printf("\n");
	print_ft_name( gef_conn[i].PC[j] );
      }
      printf("\n----------ADDS:");
      for ( j = 0; j < gef_conn[i].num_A; j++ ) {
	printf("\n");
	print_ft_name( gef_conn[i].A[j] );
      }
      printf("\n----------DELS:");
      for ( j = 0; j < gef_conn[i].num_D; j++ ) {
	printf("\n");
	print_ft_name( gef_conn[i].D[j] );
      }
      printf("\n----------IMPLIEDS:");
      for ( j = 0; j < gef_conn[i].num_I; j++ ) {
        if (cond_eff_is_enabled()) {
	  printf("\nimplied effect %d of op %d: ",
	         gef_conn[i].I[j], gef_conn[i].op);
	  print_op_name( gef_conn[i].op );
	} else {
	  printf("\nimplied effect %d of op %d: ",
	         gef_conn[i].I[j], gef_conn[gef_conn[i].I[j]].op);
	  print_op_name( gef_conn[gef_conn[i].I[j]].op );
	}
      }
    }

    printf("\n\n----------------CONDITIONAL EFFECT ARRAY:-------------------");
    for ( i = 0; i < gnum_condef_conn; i++ ) {
      printf("\n\nimplied effect %d of op: %d (base ef: %d) ",
		i,
		gcondef_conn[i].op,
		gcondef_conn[i].ef);
      print_op_name( gcondef_conn[i].op );
      printf("\n----------PCS:");
      for ( j = 0; j < gcondef_conn[i].num_PC; j++ ) {
	printf("\n");
	print_ft_name( gcondef_conn[i].PC[j] );
      }
      printf("\n----------ADDS:");
      for ( j = 0; j < gcondef_conn[i].num_A; j++ ) {
	printf("\n");
	print_ft_name( gcondef_conn[i].A[j] );
      }
      printf("\n----------DELS:");
      for ( j = 0; j < gcondef_conn[i].num_D; j++ ) {
	printf("\n");
	print_ft_name( gcondef_conn[i].D[j] );
      }
    }

    printf("\n\n----------------------FT ARRAY:-----------------------------");
    for ( i = 0; i < gnum_ft_conn; i++ ) {
/*
 * DEA - University of Brescia
 */
      sizeofgft += sizeof (gft_conn[i]) + sizeof (int) * (gft_conn[i].num_PC - 1) +
	sizeof (int) * (gft_conn[i].num_A - 1) + sizeof (int) * (gft_conn[i].num_D - 1);
      //      printf("\n\nFT: ");
      printf ("\n ----------------- \n\n %d FT: ", i);
/*
 * End of DEA
 */
      print_ft_name( i );
      printf(" rand: %d", gft_conn[i].rand);
      printf("\n----------PRE COND OF:");
      for ( j = 0; j < gft_conn[i].num_PC; j++ ) {
	printf("\neffect %d", gft_conn[i].PC[j]);
      }
      printf("\n----------ADD BY:");
      for ( j = 0; j < gft_conn[i].num_A; j++ ) {
	printf("\neffect %d", gft_conn[i].A[j]);
      }
      printf("\n----------DEL BY:");
      for ( j = 0; j < gft_conn[i].num_D; j++ ) {
	printf("\neffect %d", gft_conn[i].D[j]);
      }
/*
 * DEA - University of Brescia
 */
      printf ("\nSIZE= %d", sizeof (gft_conn[i]) + sizeof (int) * (gft_conn[i].num_PC - 1) +
	      sizeof (int) * (gft_conn[i].num_A - 1) + sizeof (int) * (gft_conn[i].num_D - 1));
/*
 * End of DEA
 */
    }
    printf("\n\n------------------CONDITIONAL FT ARRAY:---------------------");
    for ( i = 0; i < gnum_condft_conn; i++ ) {
/*
 * DEA - University of Brescia
 */
      printf ("\n ----------------- \n\n %d FT: ", i);
/*
 * End of DEA
 */
      print_ft_name( i );
      printf("\n----------PRE COND OF:");
      for ( j = 0; j < gcondft_conn[i].num_PC; j++ ) {
	printf("\nimplied effect %d", gcondft_conn[i].PC[j]);
      }
      printf("\n----------ADD BY:");
      for ( j = 0; j < gcondft_conn[i].num_A; j++ ) {
	printf("\nimplied effect %d", gcondft_conn[i].A[j]);
      }
      printf("\n----------DEL BY:");
      for ( j = 0; j < gcondft_conn[i].num_D; j++ ) {
	printf("\nimplied effect %d", gcondft_conn[i].D[j]);
      }
/*
 * DEA - University of Brescia
 */
      printf ("\nSIZE= %d", sizeof (gcondft_conn[i]) + sizeof (int) * (gcondft_conn[i].num_PC - 1) +
	      sizeof (int) * (gcondft_conn[i].num_A - 1) + sizeof (int) * (gcondft_conn[i].num_D - 1));
/*
 * End of DEA
 */
    }



  printf("Connection graph 1\n");


  }




/*
 * DEA - University of Brescia
 */

  gnum_ef_block = gnum_ef_conn / 32 + 1;
  
  for (i = 0; i < gnum_ft_conn; i++)
    gft_conn[i].position = i;

  for (i = 0; i < gnum_ef_conn; i++)
    gef_conn[i].position = i;
  
  gextended_ef_conn = max_num_efconn = gnum_ef_conn;
  gextended_ft_conn = max_num_ftconn = gnum_ft_conn;

  if ((gnum_ef_conn > MAX_EF_MUTEX_SIZE) && (!GpG.lowmemory)) {
    if (DEBUG0) 
      printf("\nSwitch to lowmemory mode...\n");
    GpG.lowmemory = TRUE;
  }
  
  if (DEBUG0)
    {
      
      printf ("Number of actions             : %7d", gnum_ef_conn);
      printf ("\nNumber of conditional actions : %7d", gnum_condef_conn);
      printf ("\nNumber of facts               : %7d", gnum_ft_conn);
      fflush(stdout);
    }

  if (gcmd_line.display_info == 121)
    {
      printf ("\nDim. azioni    (gop_conn): %7d", sizeofgop);
      printf ("\nDim. 'effetti' (gef_conn): %7d", sizeofgef);
      printf ("\nDim. fatti     (gft_conn): %7d", sizeofgft);
    }

 /*
 * End of DEA
 */
   
}




/*
 * DEA - University of Brescia
 */

unsigned long int
fact_adress1 (void)
{

  unsigned long int r = 0;
  int b = 1, i;

  for (i = garity[lp1] - 1; i > -1; i--)
    {
      r += b * largs1[i];
      b *= gnum_constants;
    }

  return r;

}


/**
 * Cerca in gef_conn le azioni corrispondenti a timed facts (azioni fittizie), le ordina temporalmente e salva gli indici
 * corrispondenti in gtimed_facts_idx
 **/
void search_timed_facts_idx( void ) {
  int i, j, k,  count;
  gtimed_facts_idx = (int *) calloc(gnum_tmd_init_fcts, sizeof(int));
  count = 0;
  for (i = 0; i < gnum_ef_conn; i++) {
    if (gef_conn[i].act_type == TIMED_FACT_ACT) {
      for (j = 0; (j < count) && (gef_conn[i].plop -> duration -> value > gef_conn[gtimed_facts_idx[j]].plop -> duration -> value); j++); 
      if (j < count) {
	//sposta gli elementi del vettore in avanti 
	for (k = count; k > j; k--)
	  gtimed_facts_idx[k] = gtimed_facts_idx[k - 1];
      }  
      //inserisce l'indice del timed fact nel vettore
      gtimed_facts_idx[j] = i;   
      count++;
    }
  }
  if (count != gnum_tmd_init_fcts) {
    printf("\nsearch_timed_facts_idx() - error: wrong number of timed facts in gef_conn.");
    exit(1);
  }
}

/**
 * Costruisce la matrice dei timed facts (gtimed_fct_vect). Ogni riga corrisponde ad un timed fact distinto
 * ogni colonna corrisponde ad un diverso intervallo. Gli intervalli (colonne) sono ordinati temporalmente. 
 * Aggiorna gft_conn marcando i fatti timed con IS_TIMED e setta il bitarray GpG.has_timed_preconds
 * marcando i bit corrispondenti ad azione che hanno preconditioni timed.
 *
 * Build timed facts intervals vector
 **/
void make_timed_fct_vector( void ) {

  int i, j, k, l, num, num_timed, num_diff;
  int *facts = NULL;
  Timed_fct tmp, *timed_vect;

  // Alloco e resetto il bitvector per marcare i fatti timed
  GpG.fact_is_timed = (int *)calloc(gnum_ft_block, sizeof(int));
  assert(GpG.fact_is_timed);
  memset(GpG.fact_is_timed, 0, gnum_ft_block * sizeof(int));

  // Conto i timed facts
  facts = (int *)calloc(gnum_ft_block, sizeof(int));
  memset(facts, 0, gnum_ft_block * sizeof(int));
  num = 0;
  for (i = 0; i < gnum_tmd_init_fcts; i++) {
    num += gef_conn[gtimed_facts_idx[i]].num_A;
    for (j = 0; j < gef_conn[gtimed_facts_idx[i]].num_A; j++)
      SET_BIT(facts, gef_conn[gtimed_facts_idx[i]].A[j]);
    for (j = 0; j < gef_conn[gtimed_facts_idx[i]].num_D; j++) {
      if (!GET_BIT(facts, gef_conn[gtimed_facts_idx[i]].D[j])) {
	SET_BIT(facts, gef_conn[gtimed_facts_idx[i]].D[j]);
	num++;
      }
    }
  }
  free(facts);

  // Alloco memoria per il vettore degli intervalli
  timed_vect = (Timed_fct *)calloc(num + 1, sizeof(Timed_fct));
  memset(timed_vect, 0, (num + 1) * sizeof(Timed_fct));

  num_timed = 0;

  // Per ogni azione fittizia (Timed fact)
  for (i = 0; i < gnum_tmd_init_fcts; i++) {
    // Per ogni effetto additivo
    for (j = 0; j < gef_conn[gtimed_facts_idx[i]].num_A; j++) {
      for (k = 0; k < num_timed; k++)
	if ((gef_conn[gtimed_facts_idx[i]].A[j] == timed_vect[k].position) &&
	    (gef_conn[gtimed_facts_idx[i]].duration < timed_vect[k].end_time) &&
	    (timed_vect[k].start_time < 0))
	  break;
      // Completo le informazioni dell'intervallo
      if (k < num_timed) {
	timed_vect[k].start_time = gef_conn[gtimed_facts_idx[i]].duration;
	timed_vect[k].duration = timed_vect[k].end_time - timed_vect[k].start_time;
      }
      // Oppure creo un nuovo intervallo e salvo lo start_time
      else {
	// Marco questo fatto come TIMED
	gft_conn[gef_conn[gtimed_facts_idx[i]].A[j]].fact_type = IS_TIMED;
	SET_BIT(GpG.fact_is_timed, gef_conn[gtimed_facts_idx[i]].A[j]);
	tmp.position = gef_conn[gtimed_facts_idx[i]].A[j];
	tmp.start_time = gef_conn[gtimed_facts_idx[i]].duration;
	tmp.end_time = -1;
	tmp.duration = -1;
	tmp.levels = NULL;
	tmp.num_act_PC = 0;
	tmp.slack = MAXFLOAT;
	timed_vect[num_timed++] = tmp;
      }
    }
    // Per ogni effetto cancellante
    for (j = 0; j < gef_conn[gtimed_facts_idx[i]].num_D; j++) {
      for (k = 0; k < num_timed; k++)
	if ((gef_conn[gtimed_facts_idx[i]].D[j] == timed_vect[k].position) &&
	    (gef_conn[gtimed_facts_idx[i]].duration > timed_vect[k].start_time)
	    && (timed_vect[k].end_time < 0))
	  break;
      // Completo le informazioni dell'intervallo
      if (k < num_timed) {
	timed_vect[k].end_time = gef_conn[gtimed_facts_idx[i]].duration;
	timed_vect[k].duration = timed_vect[k].end_time - timed_vect[k].start_time;
      }
      // Oppure creo un nuovo intervallo e salvo l'end_time
      else {
	// Marco questo fatto come TIMED
	gft_conn[gef_conn[gtimed_facts_idx[i]].D[j]].fact_type = IS_TIMED;
	SET_BIT(GpG.fact_is_timed, gef_conn[gtimed_facts_idx[i]].D[j]);
	tmp.position = gef_conn[gtimed_facts_idx[i]].D[j];
	tmp.end_time = gef_conn[gtimed_facts_idx[i]].duration;
	tmp.start_time = -1;
	tmp.duration = -1;
	tmp.levels = NULL;
	tmp.num_act_PC = 0;
	tmp.slack = MAXFLOAT;
	timed_vect[num_timed++] = tmp;
      }
    }
  }

  if (num_timed != num)
    printf("Error : count %d timed facts but %d expected.", num_timed, num);

  // Riordino il vettore mettendo in posizioni contigue gli intervalli riferiti allo stesso fatto
  // e mantenendo gli ordinamenti temporali.
  i = 0;
  while (i < num_timed) {
    for (j = i + 1; (j < num_timed) && (timed_vect[i].position == timed_vect[j].position); j++);
    if (j < num_timed) {
      for (k = j + 1; (k < num_timed) && (timed_vect[i].position != timed_vect[k].position); k++);
      if (k < num_timed) {
	// Shifto in avanti di un posto gli intervalli da j in poi
	for (l = num_timed; l > j; l--)
	  timed_vect[l] = timed_vect[l - 1];
	// Porto il timed_vect[k] nella posizione corretta (k + 1 xkè è stato spostato in avanti)
	timed_vect[j] = timed_vect[k + 1];
	// Shifto indietro di un posto gli intervalli da k + 1 in poi
	for (l = k + 1; l < num_timed; l++)
	  timed_vect[l] = timed_vect[l + 1];
	// Passo al prossimo elemento
	i = j;
      }
      else i++;
    }
    else i++;
  }

  // Costruisco la matrice definitiva 
  for (i = 1, num_diff = 1; i < num_timed; i++)
    if (timed_vect[i].position != timed_vect[i - 1].position)
      num_diff++;
  gnum_timed_facts = num_diff;
  gtimed_fct_vect = (Timed_fct **)calloc(num_diff, sizeof(Timed_fct *));
  memset(gtimed_fct_vect, 0, num_diff * sizeof(Timed_fct *));
  gnum_tmd_interval = (int *)calloc(num_diff, sizeof(int));
  memset(gnum_tmd_interval, 0, num_diff * sizeof(int));
  ginterval_idx = (int *)calloc(gnum_ft_conn, sizeof(int));
  memset(ginterval_idx, -1, gnum_ft_conn * sizeof(int));
  i = 0;
  k = 0;
  while (i < num_timed) {
    j = timed_vect[i].position;
    gtimed_fct_vect[k] = &timed_vect[i];
    ginterval_idx[timed_vect[i].position] = k;
    for (i = i + 1, l = 1; (i < num_timed) && (timed_vect[i].position == j); i++, l++);
    gnum_tmd_interval[k] = l;
    k++;
    if (i >= num_timed)
      break;
  }

  if (DEBUG3) {
    for (i = 0; i < gnum_timed_facts; i++) {
      j = gtimed_fct_vect[i][0].position;
      printf("\n\nTimed fact : %s\nTemporal intervals : ", print_ft_name_string(j, temp_name));
      for (k = 0; k < NUM_INTERVALS(j); k++)
	printf("[%d] : %.2f - %.2f", k, gtimed_fct_vect[i][k].start_time, gtimed_fct_vect[i][k].end_time);
    } 
  }
  
  // Alloco il vettore PC_int su cui effettuare temporaneamente 
  // tutte le modifiche sugli intervalli
  temp_PC_int = (int *)calloc(gnum_timed_facts, sizeof(int));

  // Inizializzo il bitarray delle azioni che hanno dei timed nelle precondizioni
  GpG.has_timed_preconds = (int *)calloc(gnum_ef_block, sizeof(int));
  assert(GpG.has_timed_preconds);
  memset(GpG.has_timed_preconds, 0, gnum_ef_block * sizeof(int));
  for (i = 0; i < gnum_timed_facts; i++) {
    // Prendo il l'i-esimo timed fact
    j = gtimed_fct_vect[i][0].position;
    
    if (DEBUG5)
      printf("\n\nTimed fact %s is precondition of actions", print_ft_name_string(j, temp_name));
    
    // Per tutte le azioni che hanno questo timed fact come precondizione
    // Setto a 1 il bit corrispondente in GpG.has_timed_preconds
    for (k = 0; k < gft_conn[j].num_PC; k++) {
      SET_BIT(GpG.has_timed_preconds, gft_conn[j].PC[k]);
      
      if (DEBUG5) {
	printf("\n        ");
	print_op_name(gft_conn[j].PC[k]);
      }
    }
  }

}


/**
 * Costruisce la rappresentazione finale dei predicati derivati, ovverlo l'array gdp_conn, e aggiorna
 * gft_conn marcando i fatti corrispondenti a predicati derivati con IS_DERIVED
 **/
void create_final_derived_predicates() {
  int i, j, num_base;
  Action *a;
  IntList **prec_ft;
  IntList **eff_ft, **neff_ft;
  IntList *tmp;

  printf("\nCreate finale derived predicates and operators...");
  fflush(stdout);

  prec_ft = (IntList **) calloc (gnum_ft_conn, sizeof(IntList *));
  memset(prec_ft, 0, gnum_ft_conn * sizeof(IntList *));

  eff_ft = (IntList **) calloc (gnum_ft_conn, sizeof(IntList *));
  memset(eff_ft, 0, gnum_ft_conn * sizeof(IntList *));

  neff_ft = (IntList **) calloc (gnum_ft_conn, sizeof(IntList *));
  memset(neff_ft, 0, gnum_ft_conn * sizeof(IntList *));

  gdp_conn = (DpConn *) calloc (gnum_dp_actions, sizeof(DpConn));
  memset(gdp_conn, 0, gnum_dp_actions * sizeof(DpConn));

  gnum_dp_conn = 0;

  num_base = gnum_ft_conn;

  for (a = gdpactions, i = 0; a; a = a -> next) {

    if (a -> effects -> num_adds == 0) 
      continue;

    gnum_dp_conn++;

    gdp_conn[i].op = i;
    gdp_conn[i].add = a -> effects -> adds[0];
    gft_conn[gdp_conn[i].add].fact_type = IS_DERIVED;
    
    if (gdp_conn[i].add < num_base)
      num_base = gdp_conn[i].add;

    if (gft_conn[gdp_conn[i].add].num_PC)
      {
	GpG.derived_pred_in_preconds = TRUE;
	GpG.save_action_cost_list = TRUE;
      }

    gft_conn[gdp_conn[i].add].num_dp_A++;
    tmp = (IntList *) malloc (sizeof(IntList));
    tmp -> item = i;
    tmp -> next = eff_ft[gdp_conn[i].add];
    eff_ft[gdp_conn[i].add] = tmp;

#ifdef __MY_OUTPUT__
    if (a -> effects -> num_adds != 1) 
      printf("Warning : derived predicates with%seffects found%s", (!a->effects->num_adds)?" no ":" more than one ",
	     (!a->effects->num_adds)?".":" : effects could be ignored.");
#endif

    if (a -> effects -> num_dels) {
      gdp_conn[i].del = a -> effects -> dels[0];
      gft_conn[gdp_conn[i].del].fact_type = IS_DERIVED;

      if (gft_conn[gdp_conn[i].del].num_PC)
	 GpG.derived_pred_in_preconds = TRUE;

      gft_conn[gdp_conn[i].del].num_dp_D++;
      tmp = (IntList *) malloc (sizeof(IntList));
      tmp -> item = i;
      tmp -> next = neff_ft[gdp_conn[i].del];
      neff_ft[gdp_conn[i].del] = tmp;
    }
    else
      gdp_conn[i].del = -1;

    gdp_conn[i].num_PC = a -> num_preconds;
    gdp_conn[i].PC = (int *)calloc(a -> num_preconds, sizeof(int));

    for (j = 0; j < a -> num_preconds; j++) {
      gdp_conn[i].PC[j] = a -> preconds[j];
      gft_conn[gdp_conn[i].PC[j]].num_dp_PC++;
      tmp = (IntList *) malloc (sizeof(IntList));
      tmp -> item = i;
      tmp -> next = prec_ft[gdp_conn[i].PC[j]];
      prec_ft[gdp_conn[i].PC[j]] = tmp;
    }

#ifdef __TEST_PD__
    printf("\n\nDerived operators %d", i);
    printf("\n* preconditions :");
    for (j = 0; j < gdp_conn[i].num_PC; j++)
      printf("\n%s [%d]", print_ft_name_string(gdp_conn[i].PC[j], temp_name), j);
    printf("\n* effects :");
    if (gdp_conn[i].add >= 0)
      printf("\nADD : %s [%d]", print_ft_name_string(gdp_conn[i].add, temp_name), gdp_conn[i].add);
    if (gdp_conn[i].del >= 0)
      printf("\nDEL : %s [%d]", print_ft_name_string(gdp_conn[i].del, temp_name), gdp_conn[i].del);
#endif    
    
    i++;

  }


  /* Update gft_conn structure */
  for (i = 0; i < gnum_ft_conn; i++) { 
    if (gft_conn[i].num_dp_PC)	
      gft_conn[i].dp_PC = (int *) calloc (gft_conn[i].num_dp_PC, sizeof(int));
    if (gft_conn[i].num_dp_A)
      gft_conn[i].dp_A = (int *) calloc (gft_conn[i].num_dp_A, sizeof(int));
    if (gft_conn[i].num_dp_D)
      gft_conn[i].dp_D = (int *) calloc (gft_conn[i].num_dp_D, sizeof(int));
    for (tmp = prec_ft[i], j = 0; tmp; tmp = tmp -> next, j++) 
      gft_conn[i].dp_PC[j] = tmp -> item;
    for (tmp = eff_ft[i], j = 0; tmp; tmp = tmp -> next, j++)
      gft_conn[i].dp_A[j] = tmp -> item;
    for (tmp = neff_ft[i], j = 0; tmp; tmp = tmp -> next, j++)
      gft_conn[i].dp_D[j] = tmp -> item;
  }

  /* Free allocated data */
  for (i = 0; i < gnum_ft_conn; i++) {
    free_intlist(prec_ft[i]);
    free_intlist(eff_ft[i]);
    free_intlist(neff_ft[i]);
  }
  free(prec_ft);
  free(eff_ft);
  free(neff_ft);

  gnum_dp_block = (gnum_dp_conn >> 5) + 1;

  gnum_base_ft_conn = num_base;
  gnum_base_ft_block = (num_base >> 5) + 1;

  if (GpG.derived_pred_in_preconds)
    GpG.save_action_cost_list = TRUE;

  printf("\n\nDerived predicates in actions preconditions: %s\n", GpG.derived_pred_in_preconds?"YES":"NO");

#ifdef __TEST_PD__ 
  printf("\n******* FACTS *******\n");
  for (i = 0; i < gnum_ft_conn; i++) {
    printf("\nFATTO %4d : ", i);
    printf("%15s :: %s", print_ft_name_string(i, temp_name), (gft_conn[i].fact_type == IS_BASE)?"BASE":"DERIVED");
  }
  printf("\n*********************\n");
#endif


}


/*
 * End of DEA
 */
