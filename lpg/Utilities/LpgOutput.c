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
 * File: LpgOutput.c
 * Description: printing and storing  output info.
 *
 *   PDDL 2.1 version without conditional and quantified effects 
 *
 * Authors: Alfonso Gerevini, Marco Lazzaroni, Alessandro Saetti, 
 *          Ivan Serina, Sergio Spinoni
 *
 *********************************************************************/




#include <math.h>
#include "lpg.h"
#include "output.h"
#include "LpgOutput.h"
#include "check.h"
#include "utilities.h"
#include "H_relaxed.h"


//#define  __TEST_PDDL__


/***************************************
        PRINT INSTANTIATION INFO
 ***************************************/


void print_NumVar (NumVar * f, int cv_index, int level)
{
  int j = 0;

  if (f==NULL)
    {
      printf("NULL");
      return;
    }

  if (f->function == -3)
    {
      printf ("GOAL-REACHED");
      return;
    }

  if (f->function == -1)
    {
      printf ("=(");
      for (j = 0; j < 2; j++)
	{
	  if (f->args[j] >= 0)
	    {
	      printf ("%s", gconstants[(f->args)[j]]);
	    }
	  else
	    {
	      printf ("x%d", DECODE_VAR (f->args[j]));
	    }
	  if (j < 1)
	    {
	      printf (" ");
	    }
	}
      printf (")");
      return;
    }

  if (f->function == -2)
    {
      printf ("!=(");
      for (j = 0; j < 2; j++)
	{
	  if (f->args[j] >= 0)
	    {
	      printf ("%s", gconstants[(f->args)[j]]);
	    }
	  else
	    {
	      printf ("x%d", DECODE_VAR (f->args[j]));
	    }
	  if (j < 1)
	    {
	      printf (" ");
	    }
	}
      printf (")");
      return;
    }

  printf ("%s(", gfunctions[f->function]);
  for (j = 0; j < gfunarity[f->function]; j++)
    {
      if (f->args[j] >= 0)
	{
	  printf ("%s", gconstants[(f->args)[j]]);
	}
      else
	{
	  printf ("x%d", DECODE_VAR (f->args[j]));
	}
      if (j < gfunarity[f->function] - 1)
	{
	  printf (" ");
	}
    }
  if (level < 0)
    printf (") = %f", f->value);
  else
    printf (") = %f", vectlevel[level]->numeric->values[cv_index]);

}












void print_parser_info_for_debug()
{
  int i,j, var; 
  IntList *el;


  if (gcmd_line.display_info == 141)
    {
      for (i = 0; i < gnum_fullnum_initial; i++)
	{
	  printf
	    ("\n------------------------------------------------------------\nNumVar %d:",
	     i);
	  print_NumVar (gfullnum_initial[i], i, -1);
	  printf
	    ("\n------------------------------------------------------------");
	}

      for (i = 0; i < gnum_comp_var; i++)
	{
	  IntList *il;
	  printf
	    ("\n------------------------------------------------------------\nCompVar %d:\n------------------------------------------------------------",
	     i);
	  if (GET_BIT (gis_inertial, i))
	    printf ("\n******INERTIAL******");
	  else
	    printf ("\n******DYNAMIC*******");
	  printf ("\nOPERATOR     :%s",
		  goperator_table[gcomp_var[i].operator]);
	  printf ("\nfirst_op     :%d\n", gcomp_var[i].first_op);

	  print_cvar_tree (gcomp_var[i].first_op, -1);
	  printf ("\nsecond_op    :%d\n", gcomp_var[i].second_op);
	  print_cvar_tree (gcomp_var[i].second_op, -1);
	  printf ("\nvalue        :%f\n", GCOMP_VAR_VALUE(i));
	  printf ("\nAffects vars :");
	  for (il = gcomp_var[i].affects; il; il = il->next)
	    printf ("%d%s", il->item, il->next ? ", " : " ");
	  printf ("\n");
	}
    }
  if (gcmd_line.display_info == 142)
    {
      printf ("\n\ncreated connectivity graph as follows:");

      printf ("\n\n------------------OP ARRAY:-----------------------");
      for (i = 0; i < gnum_op_conn; i++)
	{
	  printf ("\n\nOP: ");
	  print_op_name (i);
	  printf ("\n----------EFFS:");
	  for (j = 0; j < gop_conn[i].num_E; j++)
	    {
	      printf ("\neffect %d", gop_conn[i].E[j]);
	    }
	  printf ("\nSIZE = %d",
		  sizeof (gop_conn[i]) + sizeof (int) * (gop_conn[i].num_E -
							 1));
	}

      printf ("\n\n-------------------EFFECT ARRAY:----------------------");
      for (i = 0; i < gnum_ef_conn; i++)
	{
	  printf ("\n\neffect %d of op %d: ", i, gef_conn[i].op);
	  print_op_name (gef_conn[i].op);
	  printf ("\ncost     :%f", gef_conn[i].cost);
	  printf ("\nduration :%f - ", gef_conn[i].duration);
	  print_cvar_tree (gef_conn[i].dur_var_index, -1);
	  printf ("\n----------PCS START:");
	  for (j = 0; j < gef_conn[i].num_PC; j++)
	    {
	      printf ("\n Index %d ",gef_conn[i].PC[j] );
	      print_ft_name (gef_conn[i].PC[j]);
	    }
	  if (gef_conn[i].sf)
	    {
	      printf ("\n----------PCS OVERALL:");
	      for (j = 0; j < gef_conn[i].sf->num_PC_overall; j++)
		{
		  printf ("\n Index %d ",gef_conn[i].sf->PC_overall[j]);
		  print_ft_name (gef_conn[i].sf->PC_overall[j]);
		}
	      printf ("\n----------PCS END:");
	      for (j = 0; j < gef_conn[i].sf->num_PC_end; j++)
		{
		  printf ("\n Index %d ",gef_conn[i].sf->PC_end[j]);
		  print_ft_name (gef_conn[i].sf->PC_end[j]);
		}
	      printf ("\n----------ADDS START:");
	      for (j = 0; j < gef_conn[i].sf->num_A_start; j++)
		{
		  printf ("\n Index %d ",gef_conn[i].sf->A_start[j]);
		  print_ft_name (gef_conn[i].sf->A_start[j]);
		}
	    }
	  printf ("\n----------ADDS END:");
	  for (j = 0; j < gef_conn[i].num_A; j++)
	    {
	      printf ("\n Index %d ",gef_conn[i].A[j]);
	      print_ft_name (gef_conn[i].A[j]);
	    }
	  if (gef_conn[i].sf)
	    {
	      printf ("\n----------DELS START:");
	      for (j = 0; j < gef_conn[i].sf->num_D_start; j++)
		{
		  printf ("\n Index %d ",gef_conn[i].sf->D_start[j]);
		  print_ft_name (gef_conn[i].sf->D_start[j]);
		}
	    }
	  printf ("\n----------DELS END:");
	  for (j = 0; j < gef_conn[i].num_D; j++)
	    {
	      printf ("\n Index %d ",gef_conn[i].D[j]);
	      print_ft_name (gef_conn[i].D[j]);
	    }
	  printf ("\n----------IMPLIEDS:");
	  for (j = 0; j < gef_conn[i].num_I; j++)
	    {
	      printf ("\nimplied effect %d of op %d: ",
		      gef_conn[i].I[j], gef_conn[gef_conn[i].I[j]].op);
	      print_op_name (gef_conn[gef_conn[i].I[j]].op);
	    }
	}

      printf
	("\n\n----------------------FT ARRAY:-----------------------------");
      for (i = 0; i < gnum_ft_conn; i++)
	{

	  printf ("\n -------------------\n\n %d FT: ", i);
	  print_ft_name (i);
	  printf (" rand: %d", gft_conn[i].rand);
	  printf ("\n----------PRE COND OF:");
	  for (j = 0; j < gft_conn[i].num_PC; j++)
	    {
	      printf ("\neffect %d", gft_conn[i].PC[j]);
	    }
	  printf ("\n----------ADD BY:");
	  for (j = 0; j < gft_conn[i].num_A; j++)
	    {
	      printf ("\neffect %d", gft_conn[i].A[j]);
	    }
	  printf ("\n----------DEL BY:");
	  for (j = 0; j < gft_conn[i].num_D; j++)
	    {
	      printf ("\neffect %d", gft_conn[i].D[j]);
	    }

	}



      printf("\n\n----------------------NUM FT ARRAY:-----------------------------");
      for ( i = 0; i < gnum_comp_var; i++ ) 
	{
	  
	  var=-i;
	  printf("\n -------------------------------------------");
	  printf("\n Index %d - ",var);
	  print_ft_name(var);
	  printf("\n----------INCREASED BY:\n");
	  
	  for (el = gcomp_var[i].increased_by; el; el = el->next)
	  {
	    printf(" - "); 
	    print_op_name(el->item);
	  }
	  printf("\n----------DECREASED BY:\n"); 
  
	  for (el = gcomp_var[i].decreased_by; el; el = el->next)	
	  {
	    printf(" - "); 
	    print_op_name(el->item);
	  }

	  printf("\n----------AFFECTS VAR:\n"); 
  
	  for (el = gcomp_var[i].affects; el; el = el->next)	
	  {
	    printf(" - "); 
	    print_ft_name(el->item);
	  }

 
	}

    }

  /*calcolo delle mutex */

  /*fatti-fatti */
#ifdef __TEST__
  printf ("\n\ninitial state is:\n\n");
  for (i = 0; i < ginitial_state.num_F; i++)
    {
      print_ft_name (ginitial_state.F[i]);
      printf ("\n");
    }
  printf ("\n\ngoal state is:\n\n");
  for (i = 0; i < ggoal_state.num_F; i++)
    {
      print_ft_name (ggoal_state.F[i]);
      printf ("\n");
    }
#endif

}









/***************************************
           PRINT MUTEX INFO
 ***************************************/



// MUTEX

void
print_matrs ()
{
  int i, j;
  int total, total_mutex = 0;

  //#ifdef __TEST_PDDL__
  printf ("\n-----------------------------------------------------------\n ");
  printf ("ARRAY FT_EF");
  printf ("\n-----------------------------------------------------------\n ");
  //#endif
  total_mutex = 0;
  for (i = 0; i < gnum_ft_conn; i++)
    {
      //#ifdef __TEST_PDDL__
      printf ("\n\n");
      print_ft_name (i);
      printf (" MUTEX:\n ");
      //#endif
      total = 0;
      for (j = 0; j < gnum_ef_conn; j++)
	if (GET_BIT (FT_EF_mutex[i], j))
	  {
	    total++;
	    //#ifdef __TEST_PDDL__
	    print_op_name (gef_conn[j].op);
	    printf (" - ");
	    //#endif
	  }
      //#ifdef __TEST_PDDL__
      printf ("\n total mutex of fact: %d\n", total);
      //#endif
      total_mutex += total;
    }

  total_ft_ef_mutex = total_mutex;

  //#ifdef __TEST_PDDL__
  printf ("\n-----------------------------------------------------------\n ");
  printf ("ARRAY EF_EF");
  printf ("\n-----------------------------------------------------------\n ");
  //#endif
  total_mutex = 0;
  for (i = 0; i < gnum_ef_conn; i++)
    {
      //#ifdef __TEST_PDDL__
      printf ("\n\n");
      print_op_name (gef_conn[i].op);
      printf (" MUTEX:\n ");
      //#endif
      total = 0;
      for (j = 0; j < gnum_ef_conn; j++)
	if (GET_EF_EF_MX_BIT(i, j))
	  {
	    total++;
	    //#ifdef __TEST_PDDL__
	    print_op_name (gef_conn[j].op);
	    printf (" - ");
	    //#endif
	  }
      //#ifdef __TEST_PDDL__
      printf ("\n %d -- total mutex of action: %d\n", i, total);
      //#endif
      total_mutex += total;
    }
  total_ef_ef_mutex = total_mutex;

  //#ifdef __TEST_PDDL__
  printf ("\n-----------------------------------------------------------\n ");
  printf ("ARRAY EF_FT");
  printf ("\n-----------------------------------------------------------\n ");
  //#endif
  total_mutex = 0;
  for (i = 0; i < gnum_ef_conn; i++)
    {
      //#ifdef __TEST_PDDL__
      printf ("\n\n");
      print_op_name (gef_conn[i].op);
      printf (" MUTEX:\n ");
      //#endif
      total = 0;
      for (j = 0; j < gnum_ft_conn; j++)
	if (GET_BIT (EF_FT_mutex[i], j))
	  {
	    total++;
	    //#ifdef __TEST_PDDL__
	    print_ft_name (j);
	    printf (" - ");
	    //#endif
	  }
      //#ifdef __TEST_PDDL__
      printf ("\n total mutex of action: %d\n", total);
      //#endif
      total_mutex += total;
    }
  total_ef_ft_mutex = total_mutex;

  if (total_ft_ef_mutex != total_ef_ft_mutex)
    {
      printf ("\n\nWARNING num_ft_ef!=num_ef_ft\n\n");
      //        exit(1);
    }

  printf ("\n Total mutex pairs between facts: %d", total_ft_ft_mutex / 2);
  printf ("\n Total mutex pairs between facts and actions: %d",
	  total_ft_ef_mutex / 2);
  printf ("\n Total mutex pairs between actions: %d", total_ef_ef_mutex / 2);
  printf ("\n Total mutex pairs between actions and facts: %d",
	  total_ef_ft_mutex / 2);

  printf ("\n Number of facts  : %d", gnum_ft_conn);
  printf ("\n Number of actions: %d", gnum_ef_conn);
}



void
print_mutex_result (void)
{

  printf ("\n\n Total mutex pairs between facts: %d", total_ft_ft_mutex / 2);
  printf ("\n Total mutex pairs between facts and actions: %d",
	  total_ft_ef_mutex / 2);
  printf ("\n Total mutex pairs between actions: %d", total_ef_ef_mutex);
  printf ("\n Total mutex pairs between actions and facts: %d",
	  total_ef_ft_mutex / 2);

  printf ("\n Number of facts  : %d", gnum_ft_conn);
  printf ("\n Number of actions: %d", gnum_ef_conn);

}



void
print_mutex_table ()
{

  int i, j;
  printf ("\n");
  for (i = 0; i < gnum_ft_conn; i++)
    {
      printf ("\n\t\t%2d ", i);
      print_ft_name (i);
    }

  printf ("\n\nMutex table:\n   ");
  for (i = 0; i < gnum_ft_conn; i++)
    printf ("%d", i % 10);
  printf ("\n\n");
  for (i = 0; i < gnum_ft_conn; i++)
    {
      printf ("%2d ", i);
      for (j = 0; j < gnum_ft_conn; j++)
	if (GET_BIT (FT_FT_mutex[i], j))
	  printf ("1");
	else
	  printf ("0");
      printf ("\n");
    }

}



void
print_mutex_table_bet ()
{

  int i, j;
  printf ("\n");
  for (i = 0; i < gnum_ef_conn; i++)
    {
      printf ("\t\t%2d ", i);
      print_op_name (i);
    }

  printf ("\n\nMutex table:\n   ");
  for (i = 0; i < gnum_ef_conn; i++)
    printf ("%d", i % 10);
  printf ("\n\n");
  for (i = 0; i < gnum_ef_conn; i++)
    {
      printf ("%2d ", i);
      for (j = 0; j < gnum_ef_conn; j++)
	if (GET_EF_EF_MX_BIT(i, j))
	  printf ("1");
	else
	  printf ("0");
      printf ("\n");
    }

}




/***************************************
         PRINT NUMERIC INFO
 ***************************************/




void print_cvar_tree (int cv_index, int level)
{
  CompositeNumVar *cv;

  if (cv_index < 0)
    return;
  cv = &gcomp_var[cv_index];
  switch (cv->operator)
    {
    case INCREASE_OP:
    case DECREASE_OP:
    case SCALE_UP_OP:
    case SCALE_DOWN_OP:
    case ASSIGN_OP:
      MSG_ERROR("\n\nERROR NUMERIC PART\n\n");
      exit(0);
      break;
    case MUL_OP:
    case DIV_OP:
    case PLUS_OP:
    case MINUS_OP:
    case LESS_THAN_OP:
    case LESS_THAN_OR_EQUAL_OP:
    case EQUAL_OP:
    case GREATER_THAN_OP:
    case GREATER_OR_EQUAL_OP:

      printf ("( %s ",goperator_table[cv->operator]);
      print_cvar_tree (cv->first_op, level);
      printf (" ");
      print_cvar_tree (cv->second_op, level);
      printf (" )");
      if(GCOMP_VAR_VALUE( cv_index )>0.5)
	printf("   --> TRUE");
      else
	printf(" --> FALSE");
      break;
    case UMINUS_OP:
    case MINIMIZE_OP:
    case MAXIMIZE_OP:
      printf ("( %s ", goperator_table[cv->operator]);
      print_cvar_tree (cv->first_op, level);
      printf (" )");

      break;
      break;
    case FIX_NUMBER:
      printf (" %f ",GCOMP_VAR_VALUE( cv_index ) );
      break;
    case VARIABLE_OP:
      printf ("( ");
      print_NumVar (gfullnum_initial[gcomp_var[cv_index].first_op], cv_index, level);
      printf (" )");
      break;
    default:
      break;
    }
}



void
print_unsup_num_facts ()
{
  int i;

  printf ("\n<<< UNSUP NUM FACT: %d", GpG.num_false_num_fa);


  for (i = 0; i < GpG.num_false_num_fa; i++)
    {
      printf ("\nFalse num pos %d", i + 1);
      printf ("   Level %d", *unsup_num_fact[i]->level);
      printf ("   Fact %d\n", unsup_num_fact[i]->fact);



      if (unsup_num_fact[i]->fact != -1)
	print_cvar_tree (unsup_num_fact[i]->fact, *unsup_num_fact[i]->level);

      printf ("\n->action=%4d\t", unsup_num_fact[i]->action);
      if (unsup_num_fact[i]->action != -1)
	print_op_name (unsup_num_fact[i]->action);
      assert (i == vectlevel[*unsup_num_fact[i]->level]->numeric->false_position[unsup_num_fact[i]->fact]);
    }


}


/***************************************
         PRINT REACHABILITY INFO
 ***************************************/


void
print_cri_computed_costs (int level)
{
  int i;
  
  dg_inform ** loc_dg_facts_array;

 
 if(level<0)
    loc_dg_facts_array=Hvar.init_facts_array;
  else
    {
      printf("\n;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;\n\n\nLevel %d action ",level);
      print_op_name(GET_ACTION_POSITION_OF_LEVEL(level));
      loc_dg_facts_array=vectlevel[level]->dg_facts_array;

    }
 for ( i = 0; i < gnum_ft_conn; i++)
      {
        if (loc_dg_facts_array[i] == NULL)
          continue;

        printf("\nFact %d numact %d cost %.2f dur %.2f best_act %d tot %.2f name ",i,
               loc_dg_facts_array[i]->num_actions,
               loc_dg_facts_array[i]->cost,
               loc_dg_facts_array[i]->duration,
               loc_dg_facts_array[i]->best_act,
               loc_dg_facts_array[i]->totcost);
        print_ft_name(i);

      }
}




/***************************************
            PRINT NODE
 ***************************************/








char *
print_op_name_string (int pos, char *out_string)
{
  int i, j;
  Action *a;
  PlOperator *p;
  ActionEffect *ef;


 
  if(pos==INITIAL_ACTION)
    {
      strcat (out_string, "INITIAL_ACTION");  
      return out_string;
    }
 

 if (pos < 0 )
   {
     strcat (out_string, "(UNREACHABLE)");
     return out_string;
   }

  assert (pos >= 0);


  if (GpG.splitted_actions && pos >= gnum_op_conn)
    {
      pos = gef_conn[pos].op;
    }


  a = gop_conn[pos].action;
  p = gef_conn[pos].plop;

  assert (pos < gnum_op_conn);


#ifdef __TEST__
  if (pos >= 0)
    return gef_conn[pos].name;
#endif

  if (!a->norm_operator && !a->pseudo_action)
    strcat (out_string, "REACH-GOAL");

  else
    {
      strcpy (out_string, "(");
      strcat (out_string, a->name);
      if (!(p -> ops_type == TIMED_FACT_ACT))
	for (i = 0; i < a->num_name_vars; i++)
	  {
	    strcat (out_string, CONN_PLAN);
	    strcat (out_string, gconstants[a->name_inst_table[i]]);
	  }
      else
	{
	  ef = a -> effects;
	  if (ef -> num_adds) strcat(out_string, "\n                 ADD:");
	  for (i = 0; i < ef -> num_adds; i++) {
	    strcat(out_string, "\n                   ");
	    strcat(out_string,"(");
	    strcat(out_string, gpredicates[grelevant_facts[ef -> adds[i]].predicate]);
	    for (j = 0; j < garity[grelevant_facts[ef -> adds[i]].predicate]; j++) {
	      strcat(out_string, CONN_PLAN);
	      strcat(out_string, gconstants[grelevant_facts[ef -> adds[i]].args[j]]);
	    }
	    strcat(out_string, ")");
	  }
	  if (ef -> num_dels) strcat(out_string, "\n                 DEL:");
	  for (i = 0; i < ef -> num_dels; i++) {
	    strcat(out_string, "\n                   ");
	    strcat(out_string,"(");
	    strcat(out_string, gpredicates[grelevant_facts[ef -> dels[i]].predicate]);
	    for (j = 0; j < garity[grelevant_facts[ef -> dels[i]].predicate]; j++) {
	      strcat(out_string, CONN_PLAN);
	      strcat(out_string, gconstants[grelevant_facts[ef -> dels[i]].args[j]]);
	    }
	    strcat(out_string, ")");
	  }
	}
      strcat (out_string, ")");
    }

  return out_string;
}



char *
print_ft_name_string (int pos, char *out_string)
{
  int j;
  Fact *f;
  char *temp = NULL;

  if (pos < 0)
    return ("Derived NUM fact  ");

  assert (pos >= 0);
  assert (pos < gnum_ft_conn);

#ifdef __TEST__
  return gft_conn[pos].name;
#endif
  
  f = &grelevant_facts[pos];

  sprintf (out_string, "(%s ", gpredicates[f->predicate]);
  for (j = 0; j < garity[f->predicate]; j++)
    {
      if (f->args[j] >= 0)
	strcat (out_string, gconstants[(f->args)[j]]);
      else
	{
	  sprintf (temp, "x%d", DECODE_VAR (f->args[j]));
	  strcat (out_string, temp);
	}
      if (j < garity[f->predicate] - 1)
	strcat (out_string, " ");
    }
  strcat (out_string, ")");
  return out_string;
}




char *
print_noop_name_string (int pos, char *out_string)
{

  int j;
  Fact *f;
  char *temp = NULL;

#ifdef __TEST__
  
  strcpy (out_string, "NOOP_");
  strcat (out_string, gft_conn[pos].name);

  return out_string;
#endif
  
  assert (pos >= 0);

  sprintf (out_string, "NOOP_");

  f = &grelevant_facts[pos];
  strcat (out_string, gpredicates[f->predicate]);
  strcat (out_string, "(");
  for (j = 0; j < garity[f->predicate]; j++)
    {
      if (f->args[j] >= 0)
	strcat (out_string, gconstants[(f->args)[j]]);
      else
	{
	  sprintf (temp, "x%d", DECODE_VAR (f->args[j]));
	  strcat (out_string, temp);
	}
      if (j < garity[f->predicate] - 1)
	strcat (out_string, " ");
    }
  strcat (out_string, ")");


  return out_string;
}


void
print_cost_of_fact (int fact_pos, int level)
{
  dg_inform_list loc_dg_cost;


  get_dg_fact_cost (fact_pos, level, &loc_dg_cost);

  printf ("\n \tFact pos %d   level %d : ", fact_pos, level);
  print_ft_name (fact_pos);

  printf
    (" totcost %.2f    cost  %.2f duration %.2f num_actions %d, best_act %d  : ",
     loc_dg_cost->totcost, loc_dg_cost->cost, loc_dg_cost->duration,
     loc_dg_cost->num_actions, loc_dg_cost->best_act);
  if (loc_dg_cost->best_act >= 0)
    print_op_name (loc_dg_cost->best_act);

}

void
print_cost_of_unsupported_facts ()
{
  int i;
  if (GpG.accurate_cost < COMPUTE_DG_SUM_COST)
    return;


  printf ("\n COST OF UNSUPPORTED FACTS num %d ", GpG.num_false_fa);
  for (i = 0; i < GpG.num_false_fa; i++)
    print_cost_of_fact (unsup_fact[i]->fact, *unsup_fact[i]->level);

  printf ("\n\n");
}







/***************************************
            PRINT PLAN
 ***************************************/






/**
 * Nome:   print_pop
 * Scopo:  visualizza un piano parzialmente ordinato
 * Tipo:   void
 * Input:  nessuno
 * Output: piano parzialmente ordinato
 * Strutture Dati Principali: GpG
 *                            vectlevel
 *			      geff_conn
 *			      a_list
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: LocalSearch
 **
 * Name:  print_pop
 * Target:
 * Type:  void
 * Input:
 * Output: Partial-Order Planner
 * Main data structures used:  GpG
 *	                       vectlevel
 *	                       gef_conn
 *			       ActNode_list
 * Main functions:  none
 * Called by:  LocalSearch
 **/

void print_pop()

{
   int lev,lev_next,j;
   ActNode_list inf_act, inf_act_next;

   /**
      per ogni livello del piano imposto un ciclo
      **
      for every level of the plan I start a cycle
   **/
   for (lev=0; lev < GpG.curr_plan_length; lev++)
     {
       /**
	  inf_act contiene l'azione del livello corrente
	  **
	  inf_act contains the action of the current level
       **/
      inf_act = GET_ACTION_OF_LEVEL (lev);

      if (inf_act->w_is_used)
	   {
         /**
		      per ogni eff. add. at_end imposto un ciclo
		      **
		      for every additive effects at_end I start a cycle
	      **/
         for (j = 0; j < gef_conn[inf_act->position].num_A; j++)
	      {
            /**
	            per ogni azione del livello successivo controllo che le precodizioni
               dell'azione al livello successivo siano effetti dell' azione corrente
               setto in mat_ord il tipo di odinamento piu' restrittivo
		         **
	       	   for every action of the following level I control that the precoditions
		         of the action at the next level are effects of the correspondig action
		         I assign to  mat_ord the strongest ordering constraint
		      **/
            for (lev_next=lev+1; lev_next < GpG.curr_plan_length; lev_next++)
		      {
		         inf_act_next = GET_ACTION_OF_LEVEL (lev_next);
		         if (inf_act_next->w_is_used)
		         {
                  /**
			            controllo per precondizioni at start
			         **
			            I control  preconditions at start
			         **/
                  if (is_fact_in_preconditions (inf_act_next->position,gef_conn[inf_act->position].A[j]))
                     /**
			               setto mat_ord con il tipo di ordinamento, EA_SB è il più restrittivo
				            **
				            I assign to mat_ord  the type of ordering, EA_SB is the most restrictive one
			            **/
                     mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_SB;

                  /**
			            controllo per precondizioni at end
			            **
		              I control preconditions at end
			         **/
                  if (is_fact_in_preconditions_end (inf_act_next->position,gef_conn[inf_act->position].A[j]))
			         {
			            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]!=EA_SB)
			            {
			               if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==SA_SB)
                			   /**
				   		         caso particolare dove il vincolo è sia di tipo EA_EB sia di tipo SA_SB
						            **
						          a  particular case where the ordering constraint is both of the kind EA_EB and of the kind SA_SB
					            **/
                           mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_EB__SA_SB;
           			      else
				               mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_EB;
			            }
			         }

                  /**
			            controllo per precondizioni overall
			            **
		               I control for preconditions overall
			         **/
                  if (is_fact_in_preconditions_overall (inf_act_next->position,gef_conn[inf_act->position].A[j]))
                     mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_SB;
		         }
               /**
			         controllo che la catena di noop non sia spezzata
			      **
			         I control that the chain of noops is not broken
		         **/
               if (!vectlevel[lev_next]->noop_act[gef_conn[inf_act->position].A[j]].w_is_used == TRUE)
		            break;
		      }

	      }


	      if (gef_conn[inf_act->position].sf!=NULL)
         {
            /**
		         per ogni eff. add. at_start imposto un ciclo
		         **
               for every additive effect at_start I start a cycle
		      **/
            for (j = 0; j < gef_conn[inf_act->position].sf->num_A_start ; j++)
		      {
               /**
		            per ogni azione del livello successivo controllo che le precodizioni
                  dell'azione al livello successivo siano effetti dell' azione corrente
     		         setto in mat_ord il tipo di odinamento piu' restrittivo
			         **
                  for every action of the following level I control that the precoditions
		            of the action at the following level  are effects of the corresponding action
		            I assign to  mat_ord the strongest constraint
		         **/
               for (lev_next=lev+1; lev_next < GpG.curr_plan_length; lev_next++)
		         {
			         inf_act_next = GET_ACTION_OF_LEVEL (lev_next);
			         if (inf_act_next->w_is_used)
			         {
                     /**
			               controllo per precondizioni at start
				            **
			               I control for preconditions at start
			            **/

                     if  (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos] && is_fact_in_preconditions (inf_act_next->position,gef_conn[inf_act->position].sf->A_start[j]))
			            {
			               if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]!=EA_SB)
			               {
                           /**
					               caso particolare dove il vincolo è sia di tipo EA_EB sia di tipo SA_SB
					               **
                              a particular case where the ordering constraint is both of the type EA_EB and of the type SA_SB
                           **/
                           if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==EA_EB)
				                  mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_EB__SA_SB;
				               else
				                  mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=SA_SB;
			               }
			            }
			            /**
                        controllo per precondizioni at end
				            **
                        I control for preconditions at end
			            **/
                     if  (is_fact_in_preconditions_end (inf_act_next->position,gef_conn[inf_act->position].sf->A_start[j]) && mat_ord[inf_act->ord_pos][inf_act_next->ord_pos] == 0)
			               mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=SA_EB;
			            /**
                        controllo per precondizioni overall
				            **
                        I control for preconditions overall
			            **/
                     if  (is_fact_in_preconditions_overall (inf_act_next->position,gef_conn[inf_act->position].sf->A_start[j]))
			            {
				            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]!=EA_SB)
				            {
				               if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==EA_EB)
				                  mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_EB__SA_SB;
				               else
				                  mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=SA_SB;
				            }
			            }
			         }
			         /**
			            controllo che la catena di noop non sia spezzata
			    	      **
                     I control that the chain of noops is not broken
			         **/
			         if (!vectlevel[lev_next]->noop_act[gef_conn[inf_act->position].sf->A_start[j]].w_is_used == TRUE )
			            break;
		         }
		      }
         }
	   }
   }



   printf("\n");
   printf("\n");
   /**
   	imposto due cicli per verifivare il tipo di ordinamento all'interno di mat_ord
	**
      I start two cycles to check the type of ordering constraint in mat_ord
   **/	
   for (lev=0; lev < GpG.curr_plan_length; lev++)
   {
      inf_act = GET_ACTION_OF_LEVEL (lev);
      if (inf_act->w_is_used)
	   {
	      for (lev_next=lev+1; lev_next < GpG.curr_plan_length; lev_next++)
	      {
	         inf_act_next = GET_ACTION_OF_LEVEL (lev_next);
	         if (inf_act_next->w_is_used)
		      {

               if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]!=0)
		         {
			         /**
                     stampa a video il piano parzialmente ordinato nella forma
                     A-->B [tipo di vincolo]
			            **
                     print on video the Partial-Order Planner as follows
                     A-->B[ type of constraint]
			         **/
                  printf("%s",print_op_name_string(inf_act->position,temp_name));
		            printf("-->");
		            printf("%s",print_op_name_string(inf_act_next->position,temp_name));

		            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==EA_SB)
			            printf("[ES]\n");
                  if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==EA_EB)
			            printf("[EE]\n");
		            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==SA_SB)
			            printf("[SS]\n");
		            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==SA_EB)
			            printf("[SE]\n");
		            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==EA_EB__SA_SB)
			         {
			            /**
			               controlla e visualizza il vincolo piu' restrittivo
				            **
                        control and visualizes the strongest constraint
			            **/
                     if (get_action_time(inf_act->position, *inf_act->level) >  get_action_time(inf_act_next->position, *inf_act_next->level))
			               printf("[SS]\n");
			            else
			               printf("[EE]\n");
			         }
   		      }
   		   }
	      }
	   }
   }
}



void
print_actions_in_subgraph ()
{
  int i;

  printf ("\n\n>>> ACTIONS in subgraph");
  for (i = GpG.curr_plan_length - 1; i >= 0; i--)
    if (GET_ACTION_POSITION_OF_LEVEL (i) >= 0)
      {
	printf ("\nLevel %d: %s", i,
		print_op_name_string (GET_ACTION_POSITION_OF_LEVEL (i),
				      temp_name));
	if (GpG.temporal_plan)
	  printf (", start_time %.2f, end_time %.2f",
		  GET_ACTION_OF_LEVEL (i)->time_f -
		  get_action_time (GET_ACTION_POSITION_OF_LEVEL (i), i),
		  GET_ACTION_OF_LEVEL (i)->time_f);

	printf("  pos %d",GET_ACTION_POSITION_OF_LEVEL (i));
      }
  printf ("\n");

}







void
print_actions_in_temporal_plan ()
{
  int i;
  PlanAction *temp_act;

  printf ("\n\nPlan computed:");

  if (GpG.gplan_actions)
    {
      printf ("\n   Time: (ACTION) [action Duration; action Cost]");
      for (temp_act = GpG.plan_actions_for_quality_mode, i = 0; temp_act;
	   temp_act = temp_act->next, i++)
	{
	  printf ("\n %.4f: %s", temp_act->start_time,
		  print_op_name_string (temp_act->act_pos, temp_name));

	  printf (" [D:%.4f; C:%.4f]", temp_act->duration, temp_act->cost);
	  
	}
    }
  else
    printf ("\n No action in solution.");
		
  printf("\n\n");
  
}









void
print_actions_in_plan ()
{
  int i;
  PlanAction *temp_act;


  printf ("\n\nPlan computed:");

  if (GpG.gplan_actions)
    {
      printf ("\n   Time: (ACTION) [action Duration; action Cost]");
      for (temp_act = GpG.gplan_actions, i = 0; temp_act;
	   temp_act = temp_act->next, i++)
	{
	  printf ("\n %.4f: %s", temp_act->start_time,
		  print_op_name_string (temp_act->act_pos, temp_name));

	  printf (" [D:%.4f; C:%.4f]", temp_act->duration, temp_act->cost);
	  
	}
    }
  else
    printf ("\n No action in solution.");
		
  printf("\n\n");
  
}



/* Stampa a video il piano soluzione */

void
print_temporal_plan (int levels)
{

  int lev, i;
  FctNode_list inf_f;
  ActNode_list inf_a;


  printf ("\n\n -+- TEMPORAL PLAN -+-\n");

  /* Per ogni livello... */
  for (lev = 0; lev < levels; lev++)
    {

      /* Stampo i fatti veri del livello */
      printf ("\n %2d: Facts\n", lev);

      for (i = 0; i < gnum_ft_conn; i++)
	{
	  inf_f = &vectlevel[lev]->fact[i];


	  if (grelevant_facts[i].predicate == GpG.dummy_pos)
	    continue;

	  if (inf_f->w_is_true)
	    {

	      printf ("\t%s,", print_ft_name_string (i, temp_name));
	      printf (" true %d, goal %d, time %.2f \n", inf_f->w_is_true,
		      inf_f->w_is_goal, inf_f->time_f);
	    }
	}

      /* Stampo l'azione inserita nel livello */
      printf ("\n     Action");

      inf_a = GET_ACTION_OF_LEVEL (lev);

      if (inf_a->w_is_used)
	{
	  printf ("\t%s,",
		  print_op_name_string (GET_ACTION_POSITION_OF_LEVEL (lev),
					temp_name));
	  printf (" used %d, end_time %.2f \n", inf_a->w_is_used,
		  inf_a->time_f);
	}
    } /* end for nei livelli */

  printf ("\n %2d: Facts \t--- GOAL LEVEL ---\n", lev);

  for (i = 0; i < gnum_ft_conn; i++)
    {
      inf_f = &vectlevel[lev]->fact[i];

      if (grelevant_facts[i].predicate == GpG.dummy_pos)
	continue;

      if (inf_f->w_is_true)
	{
	  printf ("\t%s,", print_ft_name_string (i, temp_name));
	  printf (" true %d, goal %d, time %.2f \n", inf_f->w_is_true,
		  inf_f->w_is_goal, inf_f->time_f);
	}
    }
}



// Print some info about level
void
my_print_plan_level (int level)
{
  int i,j, k, temp, pos;
  
  printf ("\n LEVEL %d Fact:", level);
  for (j = 0; j < gnum_ft_block; j++)

    {
      temp = vectlevel[level]->fact_vect[j];
      k = 32;
      while (temp)

	{
	  k--;
	  if (temp & FIRST_1)
	    printf ("\n\t %s [%d] time_f: %.2f w_is_true %d",
		    print_ft_name_string (j * 32 + k, temp_name),
		    j * 32 + k,
		    vectlevel[level]->fact[j * 32 + k].time_f,
		    vectlevel[level]->fact[j * 32 + k].w_is_true);
	  temp <<= 1;
	}
    }
  printf ("\n LEVEL %d True-crit-vect:", level);
  for (j = 0; j < gnum_ft_block; j++)

    {
      temp = vectlevel[level]->true_crit_vect[j];
      k = 32;
      while (temp)

	{
	  k--;
	  if (temp & FIRST_1)
	    printf ("\n\t %s ", print_ft_name_string (j * 32 + k, temp_name));
	  temp <<= 1;
	}
    }
  printf ("\n LEVEL %d False-crit-vect:", level);
  for (j = 0; j < gnum_ft_block; j++)

    {
      temp = vectlevel[level]->false_crit_vect[j];
      k = 32;
      while (temp)

	{
	  k--;
	  if (temp & FIRST_1)
	    printf ("\n\t %s ", print_ft_name_string (j * 32 + k, temp_name));
	  temp <<= 1;
	}
    }
  printf ("\n LEVEL %d prec-vect:", level);
  for (j = 0; j < gnum_ft_block; j++)

    {
      temp = vectlevel[level]->prec_vect[j];
      k = 32;
      while (temp)

	{
	  k--;
	  if (temp & FIRST_1)
	    printf ("\n\t %s ", print_ft_name_string (j * 32 + k, temp_name));
	  temp <<= 1;
	}
    }
  printf ("\n LEVEL %d check w_is_used - w_is_goal - w_is_true:", level);
  for (pos = 0; pos < GpG.max_num_facts; pos++)

    {
      if (vectlevel[level]->fact[pos].w_is_goal >= 1
	  || vectlevel[level]->fact[pos].w_is_used >= 1
	  || vectlevel[level]->fact[pos].w_is_true >= 1)
	printf ("\n\t %s \tw_is_goal: %d \t w_is_used: %d \t w_is_true: %d",
		print_ft_name_string (pos, temp_name),
		vectlevel[level]->fact[pos].w_is_goal,
		vectlevel[level]->fact[pos].w_is_used,
		vectlevel[level]->fact[pos].w_is_true);
    }
  printf ("\n LEVEL %d NOOP:", level);
  for (j = 0; j < gnum_ft_conn; j++)

    {
      if (vectlevel[level]->noop_act[j].w_is_overall != 0)
	printf
	  ("\nnoop overall: %s w_is_used %d w_is_overall %d w_is_goal %d level %d",
	   print_noop_name_string (j, temp_name),
	   vectlevel[level]->noop_act[j].w_is_used,
	   vectlevel[level]->noop_act[j].w_is_overall,
	   vectlevel[level]->noop_act[j].w_is_goal, level);

      else
	if (vectlevel[level]->noop_act[j].w_is_used
	    || vectlevel[level]->noop_act[j].w_is_goal)
	    printf
	    ("\n\tnoop: %s w_is_used %d w_is_overall %d w_is_goal %d level %d",
	    print_noop_name_string (j, temp_name),
	    vectlevel[level]->noop_act[j].w_is_used,
	    vectlevel[level]->noop_act[j].w_is_overall,
	    vectlevel[level]->noop_act[j].w_is_goal, level);
	   }


  if (level >= GpG.curr_plan_length)

    {
      printf ("\n\n");
      return;
    }


  for(i=0;i<gnum_comp_var;i++)
    {
      print_cvar_tree (i,level);
      printf("\n");
    }

  printf ("\n LEVEL %d Action:", level);
  if (vectlevel[level]->action.position >= 0)
    printf (" %s [%d] time_f %.2f time_start %.2f",
	    print_op_name_string (vectlevel[level]->action.position,
				  temp_name),
	    vectlevel[level]->action.position,
	    vectlevel[level]->action.time_f,
	    vectlevel[level]->action.time_f -
	    get_action_time (vectlevel[level]->action.position, level));
	    printf ("\n\n");
	    

}



// Print info about all levels
void
my_print_plan_all (int max_time)
{
  int i;

  for (i = 0; i <= max_time; i++)
    my_print_plan_level (i);
}


// Print info about two consecutive levels
void
my_print_plan (int level)
{
  my_print_plan_level (level);
  if (level >= GpG.curr_plan_length)
    return;
  my_print_plan_level (level + 1);
}



/***************************************
             LIST
 ***************************************/


void
print_unsup_fact_vect ()
{
  int i;

  printf ("\n\n<<< UNSUP FACT: %d", GpG.num_false_fa);

  for (i = 0; i < GpG.num_false_fa; i++)
    printf ("\nFalse pos %d  Level %d  Unsup fact %s ",
	    CONVERT_FACT_TO_NODE (unsup_fact[i]->fact,
				    *unsup_fact[i]->level)->false_position,
	    *unsup_fact[i]->level, print_ft_name_string (unsup_fact[i]->fact,
							 temp_name));

  printf ("\n<<< TREATED FACT: %d", GpG.num_false_act);

  for (i = 0; i < GpG.num_false_act; i++)
    printf ("\nTreated pos %d  Level %d  Treated noop %s ",
	    CONVERT_NOOP_TO_NODE (treated_c_l[i]->fact,
				    *treated_c_l[i]->level)->false_position,
	    *treated_c_l[i]->level,
	    print_noop_name_string (treated_c_l[i]->fact, temp_name));
}


void print_unsup_timed_fact ()
{
  int i;

  if(!GpG.timed_facts_present)
    {
      printf("\n\nDomain without timed facts.\n\n");
      return;
    }

  printf ("\n\n<<< UNSUP TIMED FACT: %d", GpG.num_false_tmd_fa);

  for (i = 0; i < GpG.num_false_tmd_fa; i++)
    printf ("\nFalse pos %d  Level %d  Unsup fact %s ",
	    CONVERT_FACT_TO_NODE (unsup_tmd_facts[i]->fact,
				    *unsup_tmd_facts[i]->level)->false_position,
	    *unsup_tmd_facts[i]->level, 
	    print_ft_name_string (unsup_tmd_facts[i]->fact,temp_name));

}



/* Print the actions that make a fact TRUE with their costs */

void
print_list_resources (int index)
{
  dg_inform *tmp;
  int num;
  num = 0;
  tmp = Hvar.init_facts_array[index];

#ifndef __TEST__1
  return;
#endif

  printf ("\n +++++ FACT %d numA=%d  ", index, gft_conn[index].num_A);
  print_ft_name (index);

  while (tmp)
    {
      num = num + 1;
      printf ("\n Num. Risorsa %d \n", num);
      if (tmp->best_act == INFINITY)
	{
	  printf ("\n FATTO INIZIALE\n");
	}
      else
	{
	  print_op_name (tmp->best_act);
	  printf ("\n Costo %3f : Durata %3f \n", tmp->cost, tmp->duration);
	}
      tmp = tmp->next;
    }
}




void
print_num_levels_and_actions ()
{
  int j, k, cnt = 0;
  static int progress = 0;

#ifdef __TEST__
  printf
    ("\nGpG.num_false_fa %d GpG.num_false_act %d GpG.num_false_num_fa %d",
     GpG.num_false_fa, GpG.num_false_act, GpG.num_false_num_fa);
#endif

  printf ("\n\n -x- NUMERIC -x- %d", progress++);
  for (j = 0; j <= GpG.curr_plan_length; j++)
    {
      cnt = 0;
      printf ("\n----------------------------------------------------------");
      printf ("\n Num value in level %d:\n", j);
      if (vectlevel[j]->action.being_removed)
	{
	  printf ("\n Act in insert/remove => BREAK\n");
	  break;
	}
      for (k = 0; k < gnum_comp_var; k++)
	if (!GET_BIT (gis_inertial, k))
	  {

	    if ((j > 0) && ((fabsf (vectlevel[j]->numeric->values[k] - vectlevel[j - 1]->numeric->values[k])) > 0.10))
	      {
		printf ("%5d:", k);
		printf ("%9.2f->%9.2f", vectlevel[j]->numeric->values[k],
			vectlevel[j]->numeric->values_after_start[k]);
		if ((++cnt % 3) == 0)
		  printf ("\n");
	      }
	  }
      check_consistency (j);
      if (j != GpG.curr_plan_length)
	{
	  printf ("\n\n  Action %d: ",vectlevel[j]->action.position );
	  if (vectlevel[j]->action.position >= 0)
	    {
	      print_op_name (vectlevel[j]->action.position);
	    }
	  else
	    {

	      
	         for(k=0;k<gnum_comp_var;k++)
	         if(abs(vectlevel[j]->numeric->values[k] - vectlevel[j+1]->numeric->values[k])>0.1)
	         {
		   printf("\nERRRR2: livello %d-%d: cvar %d\n %f != %f\n\n",j,j+1,k,vectlevel[j]->numeric->values[k],vectlevel[j+1]->numeric->values[k]);
	         }
		 else
		   printf("cvar  %.2f \t", vectlevel[j]->numeric->values[k]);
	       
	    }
	}

      if(vectlevel[j]->action.position==452)
	{
	  printf("\n VARTEST lev %d :<>: ",j);
	  k=5;
	  printf("cvar %d= %.2f \t", k, vectlevel[j]->numeric->values[k]);
	  k=68;
	  printf("cvar %d= %.2f \t", k, vectlevel[j]->numeric->values[k]);
	  k=69;
	  printf("cvar %d= %.2f \t", k, vectlevel[j]->numeric->values[k]);
	  print_unsup_num_facts ();
	}
      
    }

  printf ("\n\n");
}




/***************************************
            STORE NODE
 ***************************************/



void
print_file_action_name (FILE * outfile, int index)
{

  int i;
  Action *a;


  if (GpG.splitted_actions && index > gnum_op_conn)
    {
      index = gef_conn[index].op;
    }

  a = gop_conn[index].action;

  if (a->norm_operator || a->pseudo_action)
    {
      fprintf (outfile, "(%s", a->name);

      for (i = 0; i < a->num_name_vars; i++)
	{
	  fprintf (outfile, " %s", gconstants[a->name_inst_table[i]]);
	}
    }

  fprintf (outfile, ")");
}


void
print_file_fact_name (FILE * outfile, int index)
{


  int j;
  Fact *f;

  f = &(grelevant_facts[index]);

  if (f->predicate == -3)
    {
      fprintf (outfile, "GOAL-REACHED");
      return;
    }

  if (f->predicate == -1)
    {
      fprintf (outfile, "=(");

      for (j = 0; j < 2; j++)
	{

	  if (f->args[j] >= 0)
	    {
	      fprintf (outfile, "%s", gconstants[(f->args)[j]]);
	    }
	  else
	    {
	      fprintf (outfile, "x%d", DECODE_VAR (f->args[j]));
	    }

	  if (j < 1)
	    {
	      fprintf (outfile, " ");
	    }
	}

      fprintf (outfile, ")");
      return;
    }

  if (f->predicate == -2)
    {
      fprintf (outfile, "!=(");

      for (j = 0; j < 2; j++)
	{

	  if (f->args[j] >= 0)
	    {
	      fprintf (outfile, "%s", gconstants[(f->args)[j]]);
	    }
	  else
	    {
	      fprintf (outfile, "x%d", DECODE_VAR (f->args[j]));

	    }

	  if (j < 1)
	    {
	      fprintf (outfile, " ");
	    }
	}

      fprintf (outfile, ")");
      return;
    }

  fprintf (outfile, "%s(", gpredicates[f->predicate]);

  for (j = 0; j < garity[f->predicate]; j++)
    {

      if (f->args[j] >= 0)
	{
	  fprintf (outfile, "%s", gconstants[(f->args)[j]]);
	}
      else
	{
	  fprintf (outfile, "x%d", DECODE_VAR (f->args[j]));
	}

      if (j < garity[f->predicate] - 1)
	{
	  fprintf (outfile, " ");
	}
    }

  fprintf (outfile, ")");

}










/***************************************
            STORE PLAN
 ***************************************/


/**
 * Nome:   store_pop
 * Scopo:  salva su file  piano parzialmente ordinato
 * Tipo:   void
 * Input:  nessuno
 * Output: file
 * Strutture Dati Principali: GpG
 *                            vectlevel
 *			      geff_conn
 *			      ActNode_list
 * Funzioni principali utilizzate: nessuna
 * Chiamata da: LocalSearch
 **
 *  Name:  store_pop
 *  Scope: saves on file Partial-Order Planner
 *  Type:  void
 *  Input: none
 *  Output: file with  Partial-Order Planner
 *  Main data structures used:  GpG
 *  			        vectlevel
 *  			        gef_conn
 *			        ActNode_list
 *  main functions:  none
 *  Called by:  LocalSearch
 *
 **/

void store_pop(char *fact_file_name)
{

   int lev,lev_next,j;
   ActNode_list inf_act, inf_act_next;
   static int num_plan=0;
   char cNameFile[256];
   FILE *fp;

   num_plan++;

   if (GpG.out_file_name)
      sprintf (cNameFile, "%s.soln", gcmd_line.out_file_name, num_plan);
   else
      sprintf (cNameFile, "plan_%s_%d.SOL", fact_file_name, num_plan);


   if ((fp = fopen (cNameFile, "w")) == NULL)
   {
      printf("\n\n\nError opening output file: %s",cNameFile);
      MSG_ERROR (WAR_OPEN_FILE);
      return;
   }

   /**
	   per ogni livello del piano imposto un ciclo
	   **
      for every level of the plan I start a cycle
   **/



   for (lev=0; lev < GpG.curr_plan_length; lev++)
   {
	   /**
         inf_act contiene l'azione del livello corrente
	      **
         inf_act contains the action of the current level
	   **/
      inf_act = GET_ACTION_OF_LEVEL (lev);

      if (inf_act->w_is_used)
	   {
         /**
		      per ogni eff. add. at_end imposto un ciclo
		      **
	         for every additive effect at_end I start a cycle
	      **/
         for (j = 0; j < gef_conn[inf_act->position].num_A; j++)
	      {
            /**
		         per ogni azione del livello successivo controllo che le precodizioni
               dell'azione al livello successivo siano effetti dell' azione corrente
               setto in mat_ord il tipo di odinamento piu' restrittivo
	            **
               for every action of the following level I control that the preconditions
		         of the action at the next level  are effects of the corresponding action
		         I assign to  mat_ord the strongest ordering constraint
		      **/
            for (lev_next=lev+1; lev_next < GpG.curr_plan_length; lev_next++)
		      {
		         inf_act_next = GET_ACTION_OF_LEVEL (lev_next);
		         if (inf_act_next->w_is_used)
		         {
                  /**
			            controllo per precondizioni at start
			          **
                     I control for preconditions at start
			         **/
                  if (is_fact_in_preconditions (inf_act_next->position,gef_conn[inf_act->position].A[j]))
                     /**
				            setto mat_ord con il tipo di ordinamento, EA_SB è il più restrittivo
				            **
                         I assign to mat_ord  the type of ordering, EA_SB is most restrictive
			            **/
                     mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_SB;

                  /**
			            controllo per precondizioni at end
			            **
                     I control for preconditions at end
			         **/
                  if (is_fact_in_preconditions_end (inf_act_next->position,gef_conn[inf_act->position].A[j]))
			         {
			            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]!=EA_SB)
			            {
			               if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==SA_SB)
                           /**
					               caso particolare dove il vincolo è sia di tipo EA_EB sia di tipo SA_SB
					               **
                              a particular case where the ordering constraint is both of the EA_EB and of the type SA_SB
				               **/
                           mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_EB__SA_SB;
           			      else
				               mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_EB;
			            }
			         }
			         /**
                     controllo per precondizioni overall
			            **
                     I control for preconditions overall
			         **/
                  if (is_fact_in_preconditions_overall (inf_act_next->position,gef_conn[inf_act->position].A[j]))
                     mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_SB;
		         }
               /**
			         controllo che la catena di noop non sia spezzata
			         **
                  I control that the chain of noops is not broken
		         **/
               if (!vectlevel[lev_next]->noop_act[gef_conn[inf_act->position].A[j]].w_is_used == TRUE)
		            break;
		      }

	      }


	      if (gef_conn[inf_act->position].sf!=NULL)
         {
            /**
		         per ogni eff. add. at_start imposto un ciclo
		         **
               for every additive effect at_start I start a cycle
		      **/
            for (j = 0; j < gef_conn[inf_act->position].sf->num_A_start ; j++)
		      {

		         /**
			         per ogni azione del livello successivo controllo che le precodizioni
                  dell'azione al livello successivo siano effetti dell' azione corrente
                  setto in mat_ord il tipo di odinamento piu' restrittivo
			         **
                  for every action of the following level control that the precoditions
		            of the action at the next level  are effects of the corresponding action
		            I assign to  mat_ord the strongest ordering constraint
		         **/

               for (lev_next=lev+1; lev_next < GpG.curr_plan_length; lev_next++)
		         {
			         inf_act_next = GET_ACTION_OF_LEVEL (lev_next);
			         if (inf_act_next->w_is_used)
			         {
                     /**
			               controllo per precondizioni at start
				            **
                        I control for preconditions at start
                     **/
                     if  (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos] && is_fact_in_preconditions (inf_act_next->position,gef_conn[inf_act->position].sf->A_start[j]))
			            {
			               if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]!=EA_SB)
			               {
                           /**
					               caso particolare dove il vincolo è sia di tipo EA_EB sia di tipo SA_SB
					               **
                              a particular case where the ordering constraint is both of the type EA_EB and of the type SA_SB
				               **/
                           if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==EA_EB)
				                  mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_EB__SA_SB;
				               else
				                  mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=SA_SB;
			               }
			            }

			            /**
                        controllo per precondizioni at end
				            **
                        I control for preconditions at end
			            **/
                     if  (is_fact_in_preconditions_end (inf_act_next->position,gef_conn[inf_act->position].sf->A_start[j]) && mat_ord[inf_act->ord_pos][inf_act_next->ord_pos] == 0)
			               mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=SA_EB;

                     /**
				            controllo per precondizioni overall
				            **
                        I control for preconditions overall
			            **/
                     if  (is_fact_in_preconditions_overall (inf_act_next->position,gef_conn[inf_act->position].sf->A_start[j]))
			            {
				            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]!=EA_SB)
				            {
				               if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==EA_EB)
				                  mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=EA_EB__SA_SB;
				               else
				                  mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]=SA_SB;
				            }
			            }
			         }
                  /**
				         controllo che la catena di noop non sia spezzata
				         **
                     I control that the chain of noops is not broken
			         **/
			         if (!vectlevel[lev_next]->noop_act[gef_conn[inf_act->position].sf->A_start[j]].w_is_used == TRUE )
			            break;
		         }
		      }
         }
	   }
   }

   /**
	   imposto due cicli per verifivare il tipo di ordinamento all'interno di mat_ord
	   **
      I start two cycles to check the type of ordering constraint in mat_ord
   **/
   for (lev=0; lev < GpG.curr_plan_length; lev++)
   {

      inf_act = GET_ACTION_OF_LEVEL (lev);
      if (inf_act->w_is_used)
	   {
	      for (lev_next=lev+1; lev_next < GpG.curr_plan_length; lev_next++)
	      {
	         inf_act_next = GET_ACTION_OF_LEVEL (lev_next);
	         if (inf_act_next->w_is_used)
		      {
               if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]!=0)
		         {
                  /**
			            salva nel file il piano parzialmente ordinato nella forma
                     A-->B [tipo di vincolo]
                     **
                     saves in the file the Partially-Ordered Plan as follows
                     A-->B [type of constraint]
                  **/
                  fprintf(fp, "%s",print_op_name_string(inf_act->position,temp_name));
		            fprintf(fp, "-->");
		            fprintf(fp,"%s",print_op_name_string(inf_act_next->position,temp_name));

		            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==EA_SB)
			            fprintf(fp,"[ES]\n");

		            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==EA_EB)
			            fprintf(fp,"[EE]\n");
		            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==SA_SB)
			            fprintf(fp,"[SS]\n");
		            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==SA_EB)
			            fprintf(fp,"[SE]\n");
		            if (mat_ord[inf_act->ord_pos][inf_act_next->ord_pos]==EA_EB__SA_SB)
			         {
                     /**
				            controllo e salvo il vincolo piu' restrittivo
				         **
                        I control and save  the strongest constraint
			            **/
			            if (get_action_time(inf_act->position, *inf_act->level) >  get_action_time(inf_act_next->position, *inf_act_next->level))
			               fprintf(fp,"[SS]\n");
			            else
			               fprintf(fp,"[EE]\n");
			         }
   		      }
   		   }
	      }
	   }
   }
   fclose(fp);
}









void
store_temporal_plan (int levels, char *fact_file_name, double time)
{
  int i, j, curr_plan_length = 0, out;
  char cNameFile[256];
  char validate_string[MAX_LENGTH];
  static int num_plan = 0;
  FILE *fp;
  ActNode_list infAction;
  float delta, start_act_time=0.0, prev_start_act_time=0.0 ;
  unsigned int ltime;


#ifdef __TEST__
  FtConn *factTemp;
  FctNode infTemp;
  int ind;
#endif



  curr_plan_length = 0;

#ifdef __ONLY_ONE_PLANNER__
  if (GpG.save_quality_plan_with_different_name != 1)
#endif
  num_plan++;


#ifdef __ONLY_ONE_PLANNER__
  if (GpG.save_quality_plan_with_different_name == 1)
    {
      if (GpG.out_file_name)
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "quality%s_%d.SOL", gcmd_line.out_file_name, num_plan);
#else
	  sprintf (cNameFile, "%squality%s_%d.SOL", gpath_sol_file_name, gcmd_line.out_file_name, num_plan);
#endif
	}
      else
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "qualityplan_%s_1.SOL", fact_file_name);
#else
	  sprintf (cNameFile, "%squalityplan_%s_1.SOL", gpath_sol_file_name, fact_file_name);
#endif
	}
    }
  else
#endif
  if (GpG.out_file_name)
    {
      if (GpG.mode != SPEED && GpG.mode != QUALITY)
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "%s.soln", gcmd_line.out_file_name);
#else
	  sprintf (cNameFile, "%s%s.soln", gpath_sol_file_name, gcmd_line.out_file_name);
#endif
	}
      else
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "%s.soln", gcmd_line.out_file_name);
#else
	  sprintf (cNameFile, "%s%s.soln", gpath_sol_file_name, gcmd_line.out_file_name);
#endif
	}
    }
  else
    {
      if (GpG.mode != SPEED && GpG.mode != QUALITY)
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "plan_%s_%d.SOL", fact_file_name, num_plan);
#else
	  sprintf (cNameFile, "%splan_%s_%d.SOL", gpath_sol_file_name, fact_file_name, num_plan);
#endif
	}
      else
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "plan_%s.SOL", fact_file_name);
#else
	  sprintf (cNameFile, "%splan_%s.SOL", gpath_sol_file_name, fact_file_name);
#endif
	}
    }



  if ((fp = fopen (cNameFile, "w")) == NULL)
    {
      printf("\n\n\nError opening output file: %s",cNameFile); 
      MSG_ERROR (WAR_OPEN_FILE);
      return;
    }


  fprintf (fp, "\n; Version %s", VERSION);
  fprintf (fp, "\n; Seed %d", seed);
  fprintf (fp, "\n; Command line: %s", gcomm_line);
  fprintf (fp, "\n; Problem %s", fact_file_name);

#ifdef __MY_OUTPUT__
  if ( GpG.search_type == LOCAL)
    fprintf (fp, "\n; Solution found using Local Search in the space of Action Graphs");
  else
    fprintf (fp, "\n; Solution found using Best First in the space of States");
#endif

   if (time < 0.0)
     {
       times (&glob_end_time);
       gtotal_time = DeltaTime(glob_end_time, glob_start_time);
     }
   
   fprintf (fp, "; Time %.2f\n", gtotal_time);
   
#ifndef __ONLY_ONE_PLANNER__
  if (GpG.mode == QUALITY)
#else
  if (GpG.save_quality_plan_with_different_name == 1)
#endif
    fprintf (fp, "\n; Plan generation time %.2f", GpG.time_lastsol);

  fprintf (fp, "\n; Search time %.2f",(time >= 0.0)?time:0.0);
  fprintf (fp, "\n; Parsing time %.2f", gtempl_time + greach_time + grelev_time + gconn_time + gnum_time);
  fprintf (fp, "\n; Mutex time %.2f", gmutex_total_time);

  //  if (GpG.mode == QUALITY)
    fprintf (fp, "; Time %.2f\n", GpG.time_lastsol);

  if(GpG.is_metric_present == 0 && GpG.durative_actions_in_domain == 0 && GpG.is_domain_numeric == 0)
    {
#ifndef __WINLPG__
     // fprintf (fp, "\n; NrActions %d\n\n", GpG.num_actions);
#else
      fprintf (fp, "\n; Quality %d\n\n", GpG.num_actions);
#endif
      //      fprintf (fp, "\n; MakeSpan %.2f\n\n", GpG.total_time);
    }
  else
    {
      if (GpG.is_metric_onlytemporal)
	{
#ifndef __WINLPG__
	  fprintf (fp, "\n; MakeSpan %.2f\n\n", GpG.total_time);
#else
	  fprintf (fp, "\n; Quality %.2f\n\n", GpG.total_time);
#endif
	}
      else
	{
	  if(GpG.maximize_plan && GpG.total_cost_from_metric < 0)
	    {
#ifndef __WINLPG__
	      fprintf (fp, "\n; MetricValue %.2f\n\n", GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time * (-1));
#else
	      fprintf (fp, "\n; Quality %.2f\n\n", GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time * (-1));
#endif
	    }
	  else
	    {
#ifndef __WINLPG__
	      fprintf (fp, "\n; MetricValue %.2f\n\n", GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time);
#else
	      fprintf (fp, "\n; Quality %.2f\n\n", GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time);
#endif
	    }
	}
    }


#ifdef __WINLPG__
  fprintf (fp, "; Time %.2f\n", gtotal_time);
  //  fprintf (fp, "Time %d\n\n", (int) (gtotal_time * 1000.0 + 0.5));
#endif    


  if (time >= 0.0)
    {
      // for all non empty operator levels  


      for (j = 0, i = 0; i < levels; i++)
	{
	  
	  if (GET_ACTION_POSITION_OF_LEVEL (i) >= 0)
	    {
	      curr_plan_length++;
	      
#ifdef __TEST__
	      if (DEBUG2)
		{
		  fprintf (fp, ";; \n;;Fatti lev %d: \n", i);
		  for (ind = 0; ind < gnum_ft_conn; ind++)
		    
		    if ((infTemp = &vectlevel[i]->fact[ind])->w_is_true)
		      {
			factTemp = CONVERT_FACT_TO_VERTEX (ind);
			
			fprintf (fp, ";;\t");
			print_file_fact_name (fp, ind);
			fprintf (fp, "   time %.4f \n", infTemp->time_f);
		      }
		}
#endif
	      
	      infAction = GET_ACTION_OF_LEVEL (i);
	      
	      
	      if ( gcomp_var != NULL && 
		   gcomp_var[gef_conn[infAction->position].dur_var_index].operator != FIX_NUMBER && 
		   get_action_time(infAction->position, *infAction->level) < MIN_ACTION_DURATION )
		continue;
	      
	      /* Warning there could be problems of integer overflow if time_f is big */
	      ltime=(unsigned int)((infAction->time_f - get_action_time (infAction->position, *infAction->level))*10000.0 + 0.5 );

	      start_act_time = (float)(((float) ltime) / 10000.0)  + MIN_DELTA_TIME * curr_plan_length;	

	      //  start_act_time =   ROUND_T0_1_1000(infAction->time_f - get_action_time (infAction->position, *infAction->level))  + MIN_DELTA_TIME * curr_plan_length;	
	      delta=start_act_time - prev_start_act_time;

	      if( fabsf(delta)<0.0001)
		start_act_time+= MIN_DELTA_TIME;

	      fprintf (fp, "%.4f:  ", start_act_time);
	      
	      
	      prev_start_act_time= start_act_time+ get_action_time (infAction->position, *infAction->level);

	      print_file_action_name (fp, infAction->position);
	      /**
		 if (GpG.maximize_plan && get_action_cost(infAction->position,NULL) < 0)
		 fprintf (fp, " [%.3f] ;; cost %.3f \n",
		 get_action_time (infAction->position, *infAction->level)
		 get_action_cost (infAction->position) * (-1));
		 else
		 fprintf (fp, " [%.3f], ;; cost %.3f \n",
		 get_action_time (infAction->position, *infAction->level)
		 get_action_cost (infAction->position) );
	      **/
	      fprintf (fp, " [%.4f]\n", get_action_time (infAction->position, *infAction->level));
	      
	    }
	}
    }
  else
    fprintf(fp, "\nno solution");
  
  fprintf (fp, "\n\n");

  
#ifdef __TEST__
  
  if (DEBUG2)
    {
      fprintf (fp, ";; \n;;Fatti lev GOAL: \n");

      for (ind = 0; ind < gnum_ft_conn; ind++)

	if ((infTemp = &vectlevel[i]->fact[ind])->w_is_true)
	  {
	    factTemp = CONVERT_FACT_TO_VERTEX (ind);

	    fprintf (fp, ";;\t");
	    print_file_fact_name (fp, ind);
	    fprintf (fp, "   time %.4f \n", infTemp->time_f);

	  }
    }
#endif


  fclose (fp);

  if (GpG.validate)
    {
      strcpy (validate_string, VALIDATOR_T);
      strcat (validate_string, gops_file_name);
      strcat (validate_string, " ");
      strcat (validate_string, gfct_file_name);
      strcat (validate_string, " ");
      strcat (validate_string, cNameFile);
      printf ("\n\n%s\n", validate_string);
      fflush (stdout);
      out = system (validate_string);
    }

}








void
store_temporal_plan_for_quality_mode (char *fact_file_name, double time)
{
  int i, curr_plan_length = 0, out;
  char cNameFile[256];
  char validate_string[MAX_LENGTH];
  static int num_plan = 0;
  FILE *fp;
  PlanAction *temp_act;

#ifdef __TEST__
  FtConn *factTemp;
  FctNode infTemp;
  int ind;
#endif



  curr_plan_length = 0;

#ifdef __ONLY_ONE_PLANNER__
  if (GpG.save_quality_plan_with_different_name != 1)
#endif
  num_plan++;

#ifdef __ONLY_ONE_PLANNER__
  if (GpG.save_quality_plan_with_different_name == 1)
    {
      if (GpG.out_file_name)
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "quality%s_%d.SOL", gcmd_line.out_file_name, num_plan);
#else
	  sprintf (cNameFile, "%squality%s_%d.SOL", gpath_sol_file_name, gcmd_line.out_file_name, num_plan);
#endif
	}
      else
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "qualityplan_%s_1.SOL", fact_file_name);
#else
	  sprintf (cNameFile, "%squalityplan_%s_1.SOL", gpath_sol_file_name, fact_file_name);
#endif
	}
    }
  else
#endif
  if (GpG.out_file_name)
    {
      if (GpG.mode != SPEED && GpG.mode != QUALITY)
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "%s.soln", gcmd_line.out_file_name, num_plan);
#else
	  sprintf (cNameFile, "%s%s.soln", gpath_sol_file_name, gcmd_line.out_file_name, num_plan);
#endif
	}
      else
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "%s.soln", gcmd_line.out_file_name);
#else
	  sprintf (cNameFile, "%s%s.soln", gpath_sol_file_name, gcmd_line.out_file_name);
#endif
	}
    }
  else
    {
      if (GpG.mode != SPEED && GpG.mode != QUALITY)
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "plan_%s_%d.SOL", fact_file_name, num_plan);
#else
	  sprintf (cNameFile, "%splan_%s_%d.SOL", gpath_sol_file_name, fact_file_name, num_plan);
#endif
	}
      else
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "plan_%s_1.SOL", fact_file_name); // TOGLIERE _1
#else
	  sprintf (cNameFile, "%splan_%s_1.SOL", gpath_sol_file_name, fact_file_name); // TOGLIERE _1
#endif
	}
    }


  if ((fp = fopen (cNameFile, "w")) == NULL)
    {
      printf("\n\n\nError opening output file: %s",cNameFile); 
      MSG_ERROR (WAR_OPEN_FILE);
      return;
    }


  //fprintf (fp, "\n; Version %s", VERSION);
  //fprintf (fp, "\n; Seed %d", seed);
  //fprintf (fp, "\n; Command line: %s", gcomm_line);
  //fprintf (fp, "\n; Problem %s", fact_file_name);

/*#ifdef __MY_OUTPUT__
  if ( GpG.search_type == LOCAL)
    fprintf (fp, "\n; Solution found using Local Search in the space of Action Graphs");
  else
    fprintf (fp, "\n; Solution found using Best First in the space of States");
#endif*/

  if (time < 0.0)
    {
      times (&glob_end_time);
      gtotal_time = DeltaTime(glob_end_time, glob_start_time);
      
     }
  
  fprintf (fp, "; Time %.2f\n", gtotal_time);
#ifndef __ONLY_ONE_PLANNER__
  if (GpG.mode == QUALITY)
#else
  if (GpG.save_quality_plan_with_different_name == 1)
#endif
    //fprintf (fp, "\n; Plan generation time %.2f", GpG.time_lastsol);

  //fprintf (fp, "\n; Search time %.2f",(time >= 0.0)?time:0.0);
  //fprintf (fp, "\n; Parsing time %.2f", gtempl_time + greach_time + grelev_time + gconn_time + gnum_time);
  //fprintf (fp, "\n; Mutex time %.2f", gmutex_total_time);

/*  if(GpG.is_metric_present == 0 && GpG.durative_actions_in_domain == 0 && GpG.is_domain_numeric == 0)
    {
#ifndef __WINLPG__
      fprintf (fp, "\n; NrActions %d\n\n", plan_info_for_quality_mode.num_actions);
#else
      fprintf (fp, "\n; Quality %d\n\n", plan_info_for_quality_mode.num_actions);
#endif
      //      fprintf (fp, "\n; MakeSpan %.2f\n\n", plan_info_for_quality_mode.total_time);
    }
  else
    {
      if (GpG.is_metric_onlytemporal)
	{
#ifndef __WINLPG__
	  fprintf (fp, "\n; MakeSpan %.2f\n\n", plan_info_for_quality_mode.total_time);
#else
	  fprintf (fp, "\n; Quality %.2f\n\n", plan_info_for_quality_mode.total_time);
#endif
	}
      else
	{
#ifndef __WINLPG__
	  fprintf (fp, "\n; MetricValue %.2f\n\n", plan_info_for_quality_mode.metricvalue);
#else
	  fprintf (fp, "\n; Quality %.2f\n\n", plan_info_for_quality_mode.metricvalue);
#endif
	}
    }
*/

#ifdef __WINLPG__
  fprintf (fp, "; Time %.2f\n", gtotal_time);
#endif 


  if (time >= 0.0)
    {

      for (temp_act = GpG.plan_actions_for_quality_mode, i = 0; temp_act;
	   temp_act = temp_act->next, i++)
	{
	  fprintf (fp, "%.4f:", temp_act->start_time);
	  print_file_action_name (fp, temp_act->act_pos);
	  fprintf (fp, " [%.4f]\n", temp_act->duration);
	}

    }
  else
    fprintf(fp, "\nno solution");
  
  fprintf (fp, "\n\n");

  fclose (fp);

  if (GpG.validate)
    {
      strcpy (validate_string, VALIDATOR_T);
      strcat (validate_string, gops_file_name);
      strcat (validate_string, " ");
      strcat (validate_string, gfct_file_name);
      strcat (validate_string, " ");
      strcat (validate_string, cNameFile);
      printf ("\n\n%s\n", validate_string);
      fflush (stdout);
      out = system (validate_string);
    }

}













/* Store adapted plan on file */
void
store_strips_plan (int levels, char *fact_file_name, double time)
{
  int i, out;
  //int level;
  char cNameFile[256];
  char validate_string[MAX_LENGTH];
  static int num_plan = 0;
  FILE *fp;
  PlanAction *temp_act;

#ifdef __TEST__
  FtConn *factTemp;
  FctNode infTemp;
  int ind;
#endif



#ifdef __ONLY_ONE_PLANNER__
  if (GpG.save_quality_plan_with_different_name != 1)
#endif
  num_plan++;


#ifdef __ONLY_ONE_PLANNER__
  if (GpG.save_quality_plan_with_different_name == 1)
    {
      if (GpG.out_file_name)
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "quality%s.SOL", gcmd_line.out_file_name);
#else
	  sprintf (cNameFile, "%squality%s.SOL", gpath_sol_file_name, gcmd_line.out_file_name);
#endif
	}
      else
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "qualityplan_%s_1.SOL", fact_file_name);
#else
	  sprintf (cNameFile, "%squalityplan_%s_1.SOL", gpath_sol_file_name, fact_file_name);
#endif
	}
    }
  else
    {
#endif
  if (GpG.out_file_name)
    {
      if (GpG.mode != SPEED && GpG.mode != QUALITY)
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "%s.soln", gcmd_line.out_file_name, num_plan);
#else
	  sprintf (cNameFile, "%s%s.soln", gpath_sol_file_name, gcmd_line.out_file_name, num_plan);
#endif
	}
      else
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "%s.soln", gcmd_line.out_file_name);
#else
	  sprintf (cNameFile, "%s%s.soln", gpath_sol_file_name, gcmd_line.out_file_name);
#endif
	}
    }
  else
    {
      if (GpG.mode != SPEED && GpG.mode != QUALITY)
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "plan_%s_%d.SOL", fact_file_name, num_plan);
#else
	  sprintf (cNameFile, "%splan_%s_%d.SOL", gpath_sol_file_name, fact_file_name, num_plan);
#endif
	}
      else
	{
#ifndef __WINLPG__
	  sprintf (cNameFile, "plan_%s_1.SOL", fact_file_name); // TOGLIERE _1
#else
	  sprintf (cNameFile, "%splan_%s_1.SOL", gpath_sol_file_name, fact_file_name); // TOGLIERE _1
#endif
	}
    }
#ifdef __ONLY_ONE_PLANNER__
    }
#endif

  if ((fp = fopen (cNameFile, "w")) == NULL)
    {
     printf("\n\n\nError opening output file: %s",cNameFile); 
     MSG_ERROR (WAR_OPEN_FILE);
      return;
    }


 /* fprintf (fp, "\n; Version %s", VERSION);
  fprintf (fp, "\n; Seed %d", seed);
  fprintf (fp, "\n; Command line: %s", gcomm_line);
  fprintf (fp, "\n; Problem %s", fact_file_name);
  fprintf (fp, "\n; Actions having STRIPS duration");*/
 
/*#ifdef __MY_OUTPUT__
  if ( GpG.search_type == LOCAL)
    fprintf (fp, "\n; Solution found using Local Search in the space of Action Graphs");
  else
    fprintf (fp, "\n; Solution found using Best First in the space of States");
#endif*/

  
  if (time < 0.0)
    {
      times (&glob_end_time);
      gtotal_time = DeltaTime(glob_end_time, glob_start_time);
      
    }
  
  fprintf (fp, "; Time %.2f\n", gtotal_time);

/*#ifndef __ONLY_ONE_PLANNER__
  if (GpG.mode == QUALITY)
#else
  if (GpG.save_quality_plan_with_different_name == 1)
#endif
    fprintf (fp, "\n; Plan generation time %.2f", GpG.time_lastsol);


  fprintf (fp, "\n; Search time %.2f",(time >= 0.0)?time:0.0);
  fprintf (fp, "\n; Parsing time %.2f", gtempl_time + greach_time + grelev_time + gconn_time + gnum_time);
  fprintf (fp, "\n; Mutex time %.2f", gmutex_total_time);*/

#ifndef __ONLY_ONE_PLANNER__
  if(GpG.mode == QUALITY)
#else
  if (GpG.save_quality_plan_with_different_name == 1)
#endif
    {
      if(GpG.is_metric_present == 0 && GpG.durative_actions_in_domain == 0 && GpG.is_domain_numeric == 0)
	{
#ifndef __WINLPG__
	  //fprintf (fp, "\n; NrActions %d\n\n", plan_info_for_quality_mode.num_actions);
#else
	  fprintf (fp, "\n; Quality %d\n\n", plan_info_for_quality_mode.num_actions);
#endif
	  //	  fprintf (fp, "\n; MakeSpan %.2f\n\n", plan_info_for_quality_mode.total_time);
	}
      else
	{
	  if (GpG.is_metric_onlytemporal)
	    {
#ifndef __WINLPG__
	      fprintf (fp, "\n; MakeSpan %.2f\n\n", plan_info_for_quality_mode.total_time);
#else
	      fprintf (fp, "\n; Quality %.2f\n\n", plan_info_for_quality_mode.total_time);
#endif
	    }
	  else
	    {
#ifndef __WINLPG__
	      fprintf (fp, "\n; MetricValue %.2f\n\n", plan_info_for_quality_mode.metricvalue);
#else
	      fprintf (fp, "\n; Quality %.2f\n\n", plan_info_for_quality_mode.metricvalue);
#endif
	    }
	}
      
    }
  else
    {
      if(GpG.is_metric_present == 0 && GpG.durative_actions_in_domain == 0 && GpG.is_domain_numeric == 0)
	{
#ifndef __WINLPG__
	 // fprintf (fp, "\n; NrActions %d\n\n", GpG.num_actions);
	  //	  fprintf (fp, "\n; MakeSpan %.2f\n\n", GpG.total_time);
#else
	  fprintf (fp, "\n; Quality %d\n\n", GpG.num_actions);
#endif
	}
      else
	{
	  if (GpG.is_metric_onlytemporal)
	    {
#ifndef __WINLPG__
	      fprintf (fp, "\n; MakeSpan %.2f\n\n", GpG.total_time);
#else
	      fprintf (fp, "\n; Quality %.2f\n\n", GpG.total_time);
#endif
	    }
	  else
	    {
	      if(GpG.maximize_plan && GpG.total_cost_from_metric < 0)
		{
#ifndef __WINLPG__
		  fprintf (fp, "\n; MetricValue %.2f\n\n", GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time * (-1));
#else
		  fprintf (fp, "\n; Quality %.2f\n\n", GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time * (-1));
#endif
		}
	      else
		{
#ifndef __WINLPG__
		  fprintf (fp, "\n; MetricValue %.2f\n\n", GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time);
#else
		  fprintf (fp, "\n; Quality %.2f\n\n", GpG.orig_weight_cost * GpG.total_cost_from_metric + GpG.orig_weight_time * GpG.total_time);
#endif
		}
	    }
	}
    }


   // for all actions in current solution plan

#ifdef __WINLPG__
  fprintf (fp, "; Time %.2f\n", gtotal_time);
#endif 

  if (time >= 0.0) 
    {
      for (temp_act = GpG.gplan_actions, i = 0; temp_act;
	   temp_act = temp_act->next, i++)
	{
	  
	  fprintf (fp, "%.0f: ", temp_act->start_time);
	  
	  print_file_action_name (fp, temp_act->act_pos);
	  
	  fprintf (fp, " [1]\n");
	}
    }
  else
    fprintf(fp, "\nno solution");

  /**
  for (level=0; level < GpG.curr_plan_length; level++)
    {
      if (GET_ACTION_POSITION_OF_LEVEL(level)>=0)
	{
	  fprintf (fp, "%.0f:  ", GET_ACTION_OF_LEVEL(level)->time_f);
	  
	  print_file_action_name (fp, GET_ACTION_POSITION_OF_LEVEL(level));
	  
	  fprintf (fp, "\n");
	}
    }
  **/

    //fprintf (fp, "; Time %d\n\n", (int) (gtotal_time * 1000.0 + 0.5));
  fclose (fp);

  if (GpG.validate)
    {
      strcpy (validate_string, VALIDATOR_T);
      strcat (validate_string, gops_file_name);
      strcat (validate_string, " ");
      strcat (validate_string, gfct_file_name);
      strcat (validate_string, " ");
      strcat (validate_string, cNameFile);
      printf ("\n\n%s\n", validate_string);
      fflush (stdout);
      out = system (validate_string);
    }

}









/* Store adapted plan on file*/
void
store_temporal_plan_for_debug (int levels, char *fact_file_name,
				       double time)
{
  int i, j, curr_plan_length = 0, ind, pos;
  char cNameFile[256];
  static int num_plan = 0;
  FILE *fp;
  ActNode_list infAction;
  FctNode_list infTemp;
  FtConn *factTemp;
  float start_time;

  curr_plan_length = 0;

  num_plan++;

  sprintf (cNameFile, "plan_%s_%d.SOL", fact_file_name, num_plan);

  if ((fp = fopen (cNameFile, "w")) == NULL)
    {
      MSG_ERROR (WAR_OPEN_FILE);
      exit (1);
    }

  fprintf (fp,
	   ";;Problem:\t%s\t time:\t%f\t actions:\t%d total cost \t %f \t total time %.2f\n",
	   fact_file_name, time, GpG.num_actions, GpG.total_cost_from_metric,
	   GpG.total_time);

  // for all non empty operator levels
  for (j = 0, i = 0; i < levels; i++)

    if (GET_ACTION_POSITION_OF_LEVEL (i) >= 0)
      {
	curr_plan_length++;
	{
	  fprintf (fp, ";; \n;;Fatti lev %d: \n", i);
	  for (ind = 0; ind < gnum_ft_conn; ind++)

	    if ((infTemp = &vectlevel[i]->fact[ind])->w_is_true)
	      {
		factTemp = CONVERT_FACT_TO_VERTEX (ind);

		fprintf (fp, ";;\t");
		print_file_fact_name (fp, ind);
		fprintf (fp, "   time %.2f \n", infTemp->time_f);
	      }
	}
	fprintf (fp, "\n;; check w_is_used - w_is_goal:\n");

	for (pos = 0; pos < GpG.max_num_facts; pos++)
	  {

	    if (vectlevel[i]->fact[pos].w_is_goal >= 1
		|| vectlevel[i]->fact[pos].w_is_used >= 1)
	      {

		fprintf (fp, ";;\t");
		print_file_fact_name (fp, pos);
		fprintf (fp, "\tw_is_goal: %d \t w_is_used: %d\n",
			 vectlevel[i]->fact[pos].w_is_goal,
			 vectlevel[i]->fact[pos].w_is_used);
	      }
	  }

	fprintf (fp, "\n;; check NOOP w_is_used - w_is_goal:\n");

	for (pos = 0; pos < GpG.max_num_facts; pos++)
	  {

	    if (vectlevel[i]->noop_act[pos].w_is_goal >= 1
		|| vectlevel[i]->noop_act[pos].w_is_used >= 1)
	      {
		fprintf (fp, ";;\t NOOP: ");
		print_file_fact_name (fp, pos);
		fprintf (fp, "\tw_is_goal: %d \t w_is_used: %d\n",
			 vectlevel[i]->noop_act[pos].w_is_goal,
			 vectlevel[i]->noop_act[pos].w_is_used);
	      }
	  }

	infAction = GET_ACTION_OF_LEVEL (i);

	if (GpG.temporal_plan)
	  {
	    start_time =
	      infAction->time_f - get_action_time (infAction->position,
						   *infAction->level) +
	      START_TIME + MIN_DELTA_TIME * i;
	    fprintf (fp, "\t %.4f:  ", start_time);
	  }
	else
	  fprintf (fp, "\t %d: ", curr_plan_length);

	print_file_action_name (fp, infAction->position);
	fprintf (fp, "[%.2f]\n",
		 get_action_time (infAction->position, *infAction->level));
      }

    fprintf (fp, ";; \n;;Fatti lev GOAL: \n");

    for (ind = 0; ind < gnum_ft_conn; ind++)

      if ((infTemp = &vectlevel[i]->fact[ind])->w_is_true)
	{
	  factTemp = CONVERT_FACT_TO_VERTEX (ind);
	  fprintf (fp, ";;\t");
	  print_file_fact_name (fp, ind);
	  fprintf (fp, "   time %.2f \n", infTemp->time_f);
	}

  fclose (fp);

}



/*
  store solution plan on file
 */
void store_plan(double time)
{
  if (GpG.noout || GpG.store_plan == FALSE)
    return;

  if(GpG.pop)
    {
#ifndef __WINLPG__
      store_pop(gcmd_line.fct_file_name);
#else
      store_pop(gfct_file_name);
#endif
    }
  else
    {
      if(GpG.durative_actions_in_domain)
	{
#ifndef __ONLY_ONE_PLANNER__
	  if (GpG.mode != QUALITY)
#else
	  if (GpG.save_quality_plan_with_different_name != 1)
#endif
	    {
#ifndef __WINLPG__
	      store_temporal_plan (GpG.curr_plan_length, gcmd_line.fct_file_name, time);
#else
	      store_temporal_plan (GpG.curr_plan_length, gfct_file_name, time);
#endif
	    }
	  else
	    {
#ifndef __WINLPG__
	      store_temporal_plan_for_quality_mode (gcmd_line.fct_file_name, time);
#else
	      store_temporal_plan_for_quality_mode (gfct_file_name, time);
#endif
	    }
	}
      else
	{
#ifndef __WINLPG__
	  store_strips_plan (GpG.curr_plan_length, gcmd_line.fct_file_name, time);
#else
	  store_strips_plan (GpG.curr_plan_length, gfct_file_name, time);
#endif
	}
    }
}




void
save_curr_temporal_plan (int levels, PlanAction ** plan_actions)
{
  int i, curr_plan_length = 0;
  ActNode_list infAction;
  float start_time;

  if (plan_actions != NULL)
    {
      free_gplan_actions (*plan_actions);
      *plan_actions = NULL;
    }
  else
    {
      printf ("\nplanact not initialized\n");
      return;
    }


  curr_plan_length = 0;

  
  for (i = 0; i < levels; i++)
	{
	  
	  if (GET_ACTION_POSITION_OF_LEVEL (i) >= 0)
	    {
	      curr_plan_length++;
	      
	      
	      infAction = GET_ACTION_OF_LEVEL (i);
	      
	      
	      if ( gcomp_var != NULL && 
		   gcomp_var[gef_conn[infAction->position].dur_var_index].operator != FIX_NUMBER && 
		   get_action_time(infAction->position, *infAction->level) < MIN_ACTION_DURATION )
		continue;
	      
	      
	      start_time = ROUND_TO_1_1000(infAction->time_f - get_action_time (infAction->position, *infAction->level))  + MIN_DELTA_TIME * curr_plan_length;	

	      store_temporal_action_vect (plan_actions, infAction->position, start_time, get_action_time (infAction->position, *infAction->level));

	    }
	}

      
}







int save_temp_plan (int max_time, PlanAction ** plan_actions)  
{
  int i, level;
  
  if (plan_actions != NULL)
    {
      free_gplan_actions (*plan_actions);
      *plan_actions = NULL;
    }
  else
    {
      printf ("\nplanact not initialized\n");
      return (0);
    }
  
  for (i=0, level = 0; level <= max_time; level++)
    if (vectlevel[level]->action.w_is_used)
      {
	store_action_vect (plan_actions, vectlevel[level]->action.position, vectlevel[level]->action.time_f - get_action_time (vectlevel[level]->action.position, level), get_action_time (vectlevel[level]->action.position, level));
	i++;
      }
  
  GpG.tempplan = *plan_actions;
  GpG.num_actions = i;
  return (level);
}







int restore_temp_plan (PlanAction *plan_actionsin, PlanAction ** plan_actionsout)
{
  int i;
  PlanAction *tmp;

  if (plan_actionsout != NULL)
    {
      free_gplan_actions (*plan_actionsout);
      *plan_actionsout = NULL;
    }
  else
    {
      printf ("\nplanact not initialized\n");
      return (0);
    }
  
  for (i =0, tmp = plan_actionsin; tmp !=NULL ; tmp = tmp->next, i++)
      {
	store_action_vect (plan_actionsout, tmp->act_pos, tmp->start_time, tmp->duration);
	i++;
      }
  
  plan_actionsout = &plan_actionsin;
  GpG.num_actions = i;
  return (i);
}




int save_curr_plan (int max_time, PlanAction ** plan_actions)  
{
  int i, level;
  
  if (plan_actions != NULL)
    {
      free_gplan_actions (*plan_actions);
      *plan_actions = NULL;
    }
  else
    {
      printf ("\nplanact not initialized\n");
      return (0);
    }
  
  for (i=0, level = 0; level <= max_time; level++)
    if (vectlevel[level]->action.w_is_used)
      {
	store_action_vect (plan_actions, vectlevel[level]->action.position, vectlevel[level]->action.time_f - get_action_time (vectlevel[level]->action.position, level), get_action_time (vectlevel[level]->action.position, level));
	i++;
      }
  
  GpG.gplan_actions = *plan_actions;
  GpG.num_actions = i;
  return (level);
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Stampa di fatti numerici e non
	PARAMETER	: index	indice del fatto
	RETURN		:
-----------------------------------------------------------------
*/
void print_numeric_ft(int index)
{
	CompositeNumVar *cv;

	if (index < 0)
		return;

	cv = &gcomp_var_effects[index];
	switch (cv->operator) {

	case INCREASE_OP:
	case DECREASE_OP:
	case SCALE_UP_OP:
	case SCALE_DOWN_OP:
	case ASSIGN_OP:
		printf ("( %s ",goperator_table[cv->operator]);
		print_cvar_tree (cv->first_op, -1);
		printf (" ");
		print_cvar_tree (cv->second_op, -1);
		printf (" )");
		break;

	case MUL_OP:
	case DIV_OP:
	case PLUS_OP:
	case MINUS_OP:
	case LESS_THAN_OP:
	case LESS_THAN_OR_EQUAL_OP:
	case EQUAL_OP:
	case GREATER_THAN_OP:
	case GREATER_OR_EQUAL_OP:
		printf ("( %s ",goperator_table[cv->operator]);
		print_cvar_tree (cv->first_op, -1);
		printf (" ");
		print_cvar_tree (cv->second_op, -1);
		printf (" )");
		if (GCOMP_VAR_VALUE(index)>0.5)
			printf("   --> TRUE");
		else
			printf(" --> FALSE");
		break;

	case UMINUS_OP:
	case MINIMIZE_OP:
	case MAXIMIZE_OP:
		printf ("( %s ", goperator_table[cv->operator]);
		print_cvar_tree (cv->first_op, -1);
		printf (" )");
		break;

	case FIX_NUMBER:
		printf (" %f ",GCOMP_VAR_VALUE(index));
		break;

	case VARIABLE_OP:
		printf ("( debug me ");
//		print_NumVar (gfullnum_initial[gcomp_var[index].first_op], index, level);
		printf (" )");
		break;

	default:
		break;
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Stampa dei fatti
	PARAMETER	: index	indice del fatto
	RETURN		:
-----------------------------------------------------------------
*/
void print_ft_name_effect(int index)
{
	if (index < 0)
		print_numeric_ft(-index);
	else
		print_Fact(&(grelevant_facts[index]));
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Stampa degli effetti
	PARAMETER	:
	RETURN		:
-----------------------------------------------------------------
*/
void print_efconn()
{
	EfConn	*ef;
	int		j;

	printf("\n\n-----------------------EFFECT ARRAY:------------------------");
	for (ef = gef_conn; ef < &gef_conn[gnum_ef_conn]; ef++) {
		printf ("\n\nAction: ");
		print_op_name (ef->op);
		printf ("\n----------PCS START:");
		for (j = 0; j < ef->num_PC; j++) {
			printf ("\n");
			print_ft_name (ef->PC[j]);
		}
		if (ef->sf) {
			printf ("\n----------PCS OVERALL:");
			for (j = 0; j < ef->sf->num_PC_overall; j++) {
				printf ("\n");
				print_ft_name (ef->sf->PC_overall[j]);
			}
			printf ("\n----------PCS END:");
			for (j = 0; j < ef->sf->num_PC_end; j++) {
				printf ("\n");
				print_ft_name (ef->sf->PC_end[j]);
			}
			printf ("\n----------ADDS START:");
			for (j = 0; j < ef->sf->num_A_start; j++) {
				printf ("\n");
				print_ft_name_effect (ef->sf->A_start[j]);
			}
		}
		printf ("\n----------ADDS END:");
		for (j = 0; j < ef->num_A; j++) {
			printf ("\n");
			print_ft_name_effect (ef->A[j]);
		}
		if (ef->sf) {
			printf ("\n----------DELS START:");
			for (j = 0; j < ef->sf->num_D_start; j++) {
				printf ("\n");
				print_ft_name_effect (ef->sf->D_start[j]);
			}
		}
		printf ("\n----------DELS END:");
		for (j = 0; j < ef->num_D; j++) {
			printf ("\n");
			print_ft_name_effect (ef->D[j]);
		}
		printf ("\n");
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Stampa degli effetti condizionali
	PARAMETER	:
	RETURN		:
-----------------------------------------------------------------
*/
void print_cond_efconn()
{
	CondEfConn	*cef;
	int		j;

	printf("\n\n----------------CONDITIONAL EFFECT ARRAY:-------------------");
	for (cef = gcondef_conn; cef < &gcondef_conn[gnum_condef_conn]; cef++) {
		printf("\n\nAction %d (base ef: %d) ", cef - gcondef_conn, cef->ef);
		print_op_name (cef->op);
		printf ("\n----------PCS START:");
		for (j = 0; j < cef->num_PC; j++) {
			printf ("\n");
			print_ft_name (cef->PC[j]);
		}
		if (cef->sf) {
			printf ("\n----------PCS OVERALL:");
			for (j = 0; j < cef->sf->num_PC_overall; j++) {
				printf ("\n");
				print_ft_name (cef->sf->PC_overall[j]);
			}
			printf ("\n----------PCS END:");
			for (j = 0; j < cef->sf->num_PC_end; j++) {
				printf ("\n");
				print_ft_name (cef->sf->PC_end[j]);
			}
			printf ("\n----------ADDS START:");
			for (j = 0; j < cef->sf->num_A_start; j++) {
				printf ("\n");
				print_ft_name_effect (cef->sf->A_start[j]);
			}
		}
		printf ("\n----------ADDS END:");
		for (j = 0; j < cef->num_A; j++) {
			printf ("\n");
			print_ft_name_effect (cef->A[j]);
		}
		if (cef->sf) {
			printf ("\n----------DELS START:");
			for (j = 0; j < cef->sf->num_D_start; j++) {
				printf ("\n");
				print_ft_name_effect (cef->sf->D_start[j]);
			}
		}
		printf ("\n----------DELS END:");
		for (j = 0; j < cef->num_D; j++) {
			printf ("\n");
			print_ft_name_effect (cef->D[j]);
		}
		printf ("\n");
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Stampa costo degli effetti condizionali
			  e riferimento di quali modificano i fatti
	PARAMETER	:
	RETURN		:
-----------------------------------------------------------------
*/
void print_numeric_cond_effect()
{
	CondEfConn	*cef;
	CompositeNumVar	*gv;
	IntList		*index;

	printf("\n\n----------------CONDITIONAL EFFECT COSTS:-------------------\n");
	printf("\n\nConditional action costs:\n");
	for (cef = gcondef_conn; cef < &gcondef_conn[gnum_condef_conn]; cef++) {
		printf ("Action %d :", cef - gcondef_conn);
		print_op_name(cef->op);
		printf(":     %.2f\n", get_cond_action_cost(cef - gcondef_conn,NULL));
	}
	printf("\n\n------------CONDITIONAL NUMERIC FCT MODIFIER:---------------\n");
	for (gv = gcomp_var; gv < &gcomp_var[gnum_comp_var]; gv++) {
		if ((gv->conditional_increased_by != NULL) || (gv->conditional_decreased_by != NULL)) {
			printf("\nNumeric fact: ");
			print_ft_name(-(gv - gcomp_var));

			printf ("\nIncreased by\n");
			for (index = gv->conditional_increased_by; index != NULL; index = index->next) {
				print_op_name(gcondef_conn[index->item].op);
				printf("\n");
			}

			printf ("\nDecreased by\n");
			for (index = gv->conditional_decreased_by; index != NULL; index = index->next) {
				print_op_name(gcondef_conn[index->item].op);
				printf("\n");
			}
		}
	}
}

/*
-----------------------------------------------------------------
	DESCRIPTION	: Stampa costo degli effetti di base
			  e riferimento di quali modificano i fatti
	PARAMETER	:
	RETURN		:
-----------------------------------------------------------------
*/
void print_numeric_effect()
{
	EfConn		*ef;
	CompositeNumVar	*gv;
	IntList		*index;

	printf("\n\n----------------------EFFECT COSTS:-------------------------\n");
	printf("\n\nConditional action costs:\n");
	for (ef = gef_conn; ef < &gef_conn[gnum_ef_conn]; ef++) {
		printf ("Action %d :", ef - gef_conn);
		print_op_name(ef->op);
		printf(":     %.2f\n", get_action_cost(ef - gef_conn, -1, NULL));
	}
	printf("\n\n------------------NUMERIC FCT MODIFIER:---------------------\n");
	for (gv = gcomp_var; gv < &gcomp_var[gnum_comp_var]; gv++) {
		if ((gv->increased_by != NULL) || (gv->decreased_by != NULL)) {
			printf("\nNumeric fact: ");
			print_ft_name(-(gv - gcomp_var));

			printf ("\nIncreased by\n");
			for (index = gv->increased_by; index != NULL; index = index->next) {
				print_op_name(gef_conn[index->item].op);
				printf("\n");
			}

			printf ("\nDecreased by\n");
			for (index = gv->decreased_by; index != NULL; index = index->next) {
				print_op_name(gef_conn[index->item].op);
				printf("\n");
			}
		}
	}
}


void print_solution_time_and_cost(void)
{
  
  if (GpG.maximize_plan && GpG.total_cost_from_metric < 0)
    printf("\n Found Solution: ExecCost %.2f TimeCost %.2f TotWeightCost %.2f",
	   GpG.total_cost_from_metric * (-1), GpG.total_time, GpG.total_cost_from_metric * GpG.orig_weight_cost * (-1) + GpG.total_time * GpG.orig_weight_time  );
  else
    printf("\n Found Solution: ExecCost %.2f TimeCost %.2f TotWeightCost %.2f",
	   GpG.total_cost_from_metric, GpG.total_time, GpG.total_cost_from_metric * GpG.orig_weight_cost + GpG.total_time * GpG.orig_weight_time);

}



#ifdef __STATISTIC_LM__
void print_statistic_info(void)
{
  printf("\nStampa statistiche riguardanti il moltiplicatori di Lagrange nella loro evoluzione:\n\n");
  printf("                      LM relativi alle prec    |    LM relativi alle me\n");
  printf(" Valore max:             %f                         %f\n",lm_prec_max_final,lm_me_max_final);
  printf(" Valore min:             %f                         %f\n",lm_prec_min_final,lm_me_min_final);
  printf(" Media:                  %f                         %f\n",average_prec_final,average_me_final);
  printf(" Varianza                %f                         %f\n",var_prec_final,var_me_final);                       
  printf(" Dev. Standard           %f                         %f\n\n",sqrt(var_prec_final),sqrt(var_me_final)); 
}
#endif



void print_solution_features(float plan_time, int num_restart)
{
  if (GpG.mode == INCREMENTAL)
    {
      if(GpG.maximize_plan && GpG.total_cost_from_metric < 0)
	printf ("\nSolution number: %d\nTotal time:      %.2f\nSearch time:     %.2f\nActions:         %d\nExecution cost:  %.2f\nDuration:        %.3f\nPlan quality:    %.3f", 
		GpG.num_solutions, gtotal_time, plan_time, GpG.num_actions, GpG.total_cost_from_metric * (-1), 
		GpG.total_time, GpG.total_cost_from_metric * GpG.orig_weight_cost * (-1) + GpG.total_time * GpG.orig_weight_time  );
      else
	printf ("\nSolution number: %d\nTotal time:      %.2f\nSearch time:     %.2f\nActions:         %d\nExecution cost:  %.2f\nDuration:        %.3f\nPlan quality:    %.3f", 
		GpG.num_solutions, gtotal_time, plan_time, GpG.num_actions, GpG.total_cost_from_metric, GpG.total_time, 
		GpG.total_cost_from_metric * GpG.orig_weight_cost + GpG.total_time * GpG.orig_weight_time );
    }
  else if (GpG.mode == SPEED)
    {
      if(GpG.maximize_plan && GpG.total_cost_from_metric < 0)
	printf ("\nSolution found:\nTotal time:      %.2f\nSearch time:     %.2f\nActions:         %d\nExecution cost:  %.2f\nDuration:        %.3f\nPlan quality:    %.3f", 
		gtotal_time, plan_time, GpG.num_actions, GpG.total_cost_from_metric * (-1), GpG.total_time, 
		GpG.total_cost_from_metric * GpG.orig_weight_cost * (-1) + GpG.total_time * GpG.orig_weight_time  );
      else
	printf ("\nSolution found:\nTotal time:      %.2f\nSearch time:     %.2f\nActions:         %d\nExecution cost:  %.2f\nDuration:        %.3f\nPlan quality:    %.3f", 
		gtotal_time, plan_time, GpG.num_actions, GpG.total_cost_from_metric, GpG.total_time, 
		GpG.total_cost_from_metric * GpG.orig_weight_cost + GpG.total_time * GpG.orig_weight_time ); 
    }

  if (!GpG.noout)
    {
      if (GpG.mode == INCREMENTAL)
	{
	  printf ("\n     Plan file:");
	  if (GpG.out_file_name)
	    {
#ifndef __WINLPG__
	      printf ("       %s_%d_1.SOL", gcmd_line.out_file_name,
		      GpG.num_solutions);
#else
	      printf ("       %s%s_%d.SOL", gpath_sol_file_name, 
		      gfct_file_name,
		      GpG.num_solutions);
#endif
	    }		      
	  else
	    {
#ifndef __WINLPG__
	      printf ("       plan_%s_%d.SOL", 
		      gcmd_line.fct_file_name,
		      GpG.num_solutions);
#else
	      printf ("       %splan_%s_%d.SOL", gpath_sol_file_name, 
		      gfct_file_name,
		      GpG.num_solutions);
#endif
	    }
	}
      else if (GpG.mode == SPEED)
	{
	  printf ("\n     Plan file:");
	  if (GpG.out_file_name)
	    {
#ifndef __WINLPG__
	      printf ("       %s_1.SOL", gcmd_line.out_file_name);
#else
	      printf ("       %s%s.SOL", gpath_sol_file_name, 
		      gfct_file_name);
#endif
	    }
	  else
	    {
	      printf ("       %splan_%s_1.SOL", gpath_sol_file_name, 
		      gfct_file_name);
	    }
	}
    }
  
#ifdef __MY_OUTPUT__
  if (GpG.mode == INCREMENTAL)
    {
      if(GpG.maximize_plan && GpG.total_cost_from_metric < 0)
	printf
	  ("\nAABBCC%d::%.2f::%d::%d::%.2f::%.3f::%.2f::%.2f::%.2f::%d::%d::%d::%.2f::%.2f",
	   GpG.num_solutions, plan_time, GpG.curr_plan_length,
	   GpG.num_actions, GpG.total_cost_from_metric * (-1), GpG.total_time,
	   plan_time, gmutex_total_time, gtotal_time, GpG.count_num_try,
	   num_restart, num_try,  ((plan_time*1000.0)/GpG.count_num_try),
	   GpG.total_cost_from_metric * GpG.orig_weight_cost * (-1) +
	   GpG.total_time * GpG.orig_weight_time);
      else 
	printf
	  ("\nAABBCC%d::%.2f::%d::%d::%.2f::%.3f::%.2f::%.2f::%.2f::%d::%d::%d::%.2f:%.2f",
	   GpG.num_solutions, plan_time, GpG.curr_plan_length,
	   GpG.num_actions, GpG.total_cost_from_metric, GpG.total_time,
	   plan_time, gmutex_total_time, gtotal_time, GpG.count_num_try,
	   num_restart, num_try,((plan_time*1000.0)/GpG.count_num_try),
	   GpG.total_cost_from_metric * GpG.orig_weight_cost +
	   GpG.total_time * GpG.orig_weight_time);
      
      //if(DEBUG5)
      printf("\n Tot num neigh %d",GpG.tot_num_neighb);
    }
#endif
  
}
