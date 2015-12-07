

/*********************************************************************
 * (C) Copyright 2010 INRIA, France
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA  02111-1307, USA.
 * 
 *********************************************************************/


/*
 * THIS SOURCE CODE IS SUPPLIED  ``AS IS'' WITHOUT WARRANTY OF ANY KIND, 
 * AND ITS AUTHOR AND THE JOURNAL OF ARTIFICIAL INTELLIGENCE RESEARCH 
 * (JAIR) AND JAIR'S PUBLISHERS AND DISTRIBUTORS, DISCLAIM ANY AND ALL 
 * WARRANTIES, INCLUDING BUT NOT LIMITED TO ANY IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE, AND
 * ANY WARRANTIES OR NON INFRINGEMENT.  THE USER ASSUMES ALL LIABILITY AND
 * RESPONSIBILITY FOR USE OF THIS SOURCE CODE, AND NEITHER THE AUTHOR NOR
 * JAIR, NOR JAIR'S PUBLISHERS AND DISTRIBUTORS, WILL BE LIABLE FOR 
 * DAMAGES OF ANY KIND RESULTING FROM ITS USE.  Without limiting the 
 * generality of the foregoing, neither the author, nor JAIR, nor JAIR's
 * publishers and distributors, warrant that the Source Code will be 
 * error-free, will operate without interruption, or will meet the needs 
 * of the user.
 */




/*********************************************************************
 * File: output.c
 * Description: printing info out
 *
 * Author: Joerg Hoffmann
 *
 *********************************************************************/ 





#include "torchlight.h"

#include "output.h"







/* parsing
 */







void print_FactList( FactList *list, char *sepf, char *sept )

{

  FactList *i_list;
  TokenList *i_tl;
    
  if ( list ) {
    i_tl = list->item;
    if (NULL == i_tl || NULL == i_tl->item) {
      printf("empty");
    } else {
      printf("%s", i_tl->item);
      i_tl = i_tl->next;
    }
    
    while (NULL != i_tl) {
      if (NULL != i_tl->item) {
	printf("%s%s", sept, i_tl->item);
      }
      i_tl = i_tl->next;
    }
    
    for ( i_list = list->next; i_list; i_list = i_list->next ) {
      printf("%s", sepf);
      i_tl = i_list->item;
      if (NULL == i_tl || NULL == i_tl->item) {
	printf("empty");
      } else {
	printf("%s", i_tl->item);
	i_tl = i_tl->next;
      }
      
      while (NULL != i_tl) {
	if (NULL != i_tl->item) {
	  printf("%s%s", sept, i_tl->item);
	}
	i_tl = i_tl->next;
      }
    }
  }

}



void print_hidden_TokenList( TokenList *list, char *sep )

{

  TokenList *i_tl;

  i_tl = list;
  if (NULL!=i_tl) {
    printf("%s", i_tl->item);
    i_tl = i_tl->next;
  } else {
    printf("empty");
  }
  
  while (NULL != i_tl) {
    printf("%s%s", sep, i_tl->item);
    i_tl = i_tl->next;
  }
  
}



void print_indent( int indent )

{

  int i;
  for (i=0;i<indent;i++) {
    printf(" ");
  }

}



void print_PlNode( PlNode *plnode, int indent )

{

  PlNode *i_son;

  if ( !plnode ) {
    printf("none\n");
    return;
  }
  
  switch (plnode->connective) {
  case ALL: 
    printf("ALL %s : %s\n", plnode->atom->item,
	    plnode->atom->next->item);
    print_indent(indent);
    printf("(   ");
    print_PlNode(plnode->sons,indent+4);
    print_indent(indent);
    printf(")\n");
    break;
  case EX:
    printf("EX  %s : %s\n", plnode->atom->item,
	    plnode->atom->next->item);
    print_indent(indent);
    printf("(   ");
    print_PlNode(plnode->sons,indent+4);
    print_indent(indent);
    printf(")\n");
    break;
  case AND: 
    printf("A(  ");
    print_PlNode(plnode->sons, indent+4);
    if ( plnode->sons ) {
      for ( i_son = plnode->sons->next; i_son!=NULL; i_son = i_son->next ) {
	print_indent(indent);
	printf("AND ");
	print_PlNode(i_son,indent+4);
      }
    }
    print_indent(indent);      
    printf(")\n");
    break;
  case OR:  
    printf("O(  ");
    print_PlNode(plnode->sons, indent+4);
    for ( i_son = plnode->sons->next; i_son!=NULL; i_son = i_son->next ) {
      print_indent(indent);
      printf("OR ");
      print_PlNode(i_son,indent+4);
    }
    print_indent(indent);      
    printf(")\n");
    break;
  case WHEN:
    printf("IF   ");
    print_PlNode(plnode->sons,indent+5);
    print_indent(indent);
    printf("THEN ");
    print_PlNode(plnode->sons->next,indent+5);
    print_indent(indent);
    printf("ENDIF\n");
    break;
  case NOT:
    if (ATOM==plnode->sons->connective) {
      printf("NOT ");
      print_PlNode(plnode->sons,indent+4);
    } else {
      printf("NOT(");
      print_PlNode(plnode->sons,indent+4);
      print_indent(indent+3);
      printf(")\n");
    }
    break;
  case ATOM:
    printf("(");
    print_hidden_TokenList(plnode->atom, " ");
    printf(")\n");
    break;
  case TRU:
     printf("(TRUE)\n");
     break;
  case FAL:
     printf("(FALSE)\n");
     break;   
  default:
    printf("\n***** ERROR ****");
    printf("\nprint_plnode: %d > Wrong Node specifier\n", plnode->connective);
    exit(1);
  }     

} 



void print_plops( PlOperator *plop )

{

  PlOperator *i_plop;
  int count = 0;

  if ( !plop ) {
    printf("none\n");
  }

  for ( i_plop = plop; i_plop!=NULL; i_plop = i_plop->next ) {
    printf("\nOPERATOR ");
    printf("%s", i_plop->name);
    printf("\nparameters: (%d real)\n", i_plop->number_of_real_params);
    print_FactList ( i_plop->params, "\n", " : ");
    printf("\n\npreconditions:\n");
    print_PlNode(i_plop->preconds, 0);
    printf("effects:\n");
    print_PlNode(i_plop->effects, 0);
    printf("\n-----\n");
    count++;
  }
  printf("\nAnzahl der Operatoren: %d\n", count);

}



void print_Wff( WffNode *n, int indent )

{

  WffNode *i;

  if ( !n ) {
    printf("none\n");
    return;
  }
  
  switch (n->connective) {
  case ALL: 
    printf("ALL x%d (%s): %s\n", n->var, n->var_name,
	    gtype_names[n->var_type]);
    print_indent(indent);
    printf("(   ");
    print_Wff(n->son,indent+4);
    print_indent(indent);
    printf(")\n");
    break;
  case EX:
    printf("EX  x%d (%s) : %s\n",  n->var, n->var_name,
	    gtype_names[n->var_type]);
    print_indent(indent);
    printf("(   ");
    print_Wff(n->son,indent+4);
    print_indent(indent);
    printf(")\n");
    break;
  case AND: 
    printf("A(  ");
    print_Wff(n->sons, indent+4);
    if ( n->sons ) {
      for ( i = n->sons->next; i!=NULL; i = i->next ) {
	if ( !i->prev ) {
	  printf("\nprev in AND not correctly set!\n\n");
	  exit( 1 );
	}
	print_indent(indent);
	printf("AND ");
	print_Wff(i,indent+4);
      }
    }
    print_indent(indent);      
    printf(")\n");
    break;
  case OR:  
    printf("O(  ");
    print_Wff(n->sons, indent+4);
    for ( i = n->sons->next; i!=NULL; i = i->next ) {
      print_indent(indent);
      printf("OR ");
      print_Wff(i,indent+4);
    }
    print_indent(indent);      
    printf(")\n");
    break;
  case NOT:
    if (ATOM==n->son->connective) {
      printf("NOT ");
      print_Wff(n->son,indent+4);
    } else {
      printf("NOT(");
      print_Wff(n->son,indent+4);
      print_indent(indent+3);
      printf(")\n");
    }
    break;
  case ATOM:
    print_Fact(n->fact);
    if ( n->NOT_p != -1 ) printf(" - translation NOT");
    printf("\n");
    break;
  case TRU:
     printf("(TRUE)\n");
     break;
  case FAL:
     printf("(FALSE)\n");
     break;   
  default:
    printf("\n***** ERROR ****");
    printf("\nprint_Wff: %d > Wrong Node specifier\n", n->connective);
    exit(1);
  }     

} 



void print_Operator( Operator *o )

{

  Effect *e;
  Literal *l;
  int i, m = 0;

  printf("\n\n----------------Operator %s, translated form, step 1--------------\n", o->name);

  for ( i = 0; i < o->num_vars; i++ ) {
    printf("\nx%d (%s) of type %s, removed ? %s",
	   i, o->var_names[i], gtype_names[o->var_types[i]],
	   o->removed[i] ? "YES" : "NO");
  }
  printf("\ntotal params %d, real params %d\n", 
	 o->num_vars, o->number_of_real_params);

  printf("\nPreconds:\n");
  print_Wff( o->preconds, 0 );

  printf("\n\nEffects:");
  for ( e = o->effects; e; e = e->next ) {
    printf("\n\neffect %d, parameters %d", m++, e->num_vars);

    for ( i = 0; i < e->num_vars; i++ ) {
      printf("\nx%d (%s) of type %s",
	     o->num_vars + i, e->var_names[i], gtype_names[e->var_types[i]]);
    }
    printf("\nConditions\n");
    print_Wff( e->conditions, 0 );
    printf("\nEffect Literals");
    for ( l = e->effects; l; l = l->next ) {
      if ( l->negated ) {
	printf("\nNOT ");
      } else {
	printf("\n");
      }
      print_Fact( &(l->fact) );
    }
  }

}



void print_NormOperator( NormOperator *o )

{

  NormEffect *e;
  int i, m;

  printf("\n\n----------------Operator %s, normalized form--------------\n", 
	 o->operator->name);

  for ( i = 0; i < o->num_vars; i++ ) {
    printf("\nx%d of type ", i);
    print_type( o->var_types[i] );
  }
  printf("\n\n%d vars removed from original operator:",
	 o->num_removed_vars);
  for ( i = 0; i < o->num_removed_vars; i++ ) {
    m = o->removed_vars[i];
    printf("\nx%d (%s) of type %s, type constraint ", m, o->operator->var_names[m], 
	   gtype_names[o->operator->var_types[m]]);
    print_type( o->type_removed_vars[i] );
  }

  printf("\nPreconds:\n");
  for ( i = 0; i < o->num_preconds; i++ ) {
    print_Fact( &(o->preconds[i]) );
    printf("\n");
  }

  m = 0;
  printf("\n\nEffects:");
  for ( e = o->effects; e; e = e->next ) {
    printf("\n\neffect %d, parameters %d", m++, e->num_vars);

    for ( i = 0; i < e->num_vars; i++ ) {
      printf("\nx%d of type ", o->num_vars + i);
      print_type( e->var_types[i] );
    }
    printf("\nConditions\n");
    for ( i = 0; i < e->num_conditions; i++ ) {
      print_Fact( &(e->conditions[i]) );
      printf("\n");
    }
    printf("\nAdds\n");
    for ( i = 0; i < e->num_adds; i++ ) {
      print_Fact( &(e->adds[i]) );
      printf("\n");
    }
    printf("\nDels\n");
    for ( i = 0; i < e->num_dels; i++ ) {
      print_Fact( &(e->dels[i]) );
      printf("\n");
    }
  }

}



void print_MixedOperator( MixedOperator *o )

{

  int i, m;
  Effect *e;
  Literal *l;

  printf("\n\n----------------Operator %s, mixed form--------------\n", 
	 o->operator->name);
 
  for ( i = 0; i < o->operator->num_vars; i++ ) {
    printf("\nx%d = %s of type ", i, gconstants[o->inst_table[i]]);
    print_type( o->operator->var_types[i] );
  }

  printf("\nPreconds:\n");
  for ( i = 0; i < o->num_preconds; i++ ) {
    print_Fact( &(o->preconds[i]) );
    printf("\n");
  }

  m = 0;
  printf("\n\nEffects:");
  for ( e = o->effects; e; e = e->next ) {
    printf("\n\neffect %d, parameters %d", m++, e->num_vars);

    for ( i = 0; i < e->num_vars; i++ ) {
      printf("\nx%d of type %s",
	     o->operator->num_vars + i, gtype_names[e->var_types[i]]);
    }
    printf("\nConditions\n");
    print_Wff( e->conditions, 0 );
    printf("\nEffect Literals");
    for ( l = e->effects; l; l = l->next ) {
      if ( l->negated ) {
	printf("\nNOT ");
      } else {
	printf("\n");
      }
      print_Fact( &(l->fact) );
    }
  }

}



void print_PseudoAction( PseudoAction *o )

{

  PseudoActionEffect *e;
  int i, m;

  printf("\n\n----------------Pseudo Action %s--------------\n", 
	 o->operator->name);

  for ( i = 0; i < o->operator->num_vars; i++ ) {
    printf("\nx%d = %s of type ", i, gconstants[o->inst_table[i]]);
    print_type( o->operator->var_types[i] );
  }

  printf("\nPreconds:\n");
  for ( i = 0; i < o->num_preconds; i++ ) {
    print_Fact( &(o->preconds[i]) );
    printf("\n");
  }

  m = 0;
  printf("\n\nEffects:");
  for ( e = o->effects; e; e = e->next ) {
    printf("\n\neffect %d", m++);
    printf("\n\nConditions\n");
    for ( i = 0; i < e->num_conditions; i++ ) {
      print_Fact( &(e->conditions[i]) );
      printf("\n");
    }
    printf("\nAdds\n");
    for ( i = 0; i < e->num_adds; i++ ) {
      print_Fact( &(e->adds[i]) );
      printf("\n");
    }
    printf("\nDels\n");
    for ( i = 0; i < e->num_dels; i++ ) {
      print_Fact( &(e->dels[i]) );
      printf("\n");
    }
  }

}



void print_Action( Action *a )

{

  ActionEffect *e;
  int i, j;

  if ( !a->norm_operator &&
       !a->pseudo_action ) {
    printf("\n\nAction REACH-GOAL");
  } else {
    printf("\n\nAction %s", a->name ); 
    for ( i = 0; i < a->num_name_vars; i++ ) {
      printf(" %s", gconstants[a->name_inst_table[i]]);
    }
  }

  printf("\n\nPreconds:\n");
  for ( i = 0; i < a->num_preconds; i++ ) {
    print_ft_name( a->preconds[i] );
    printf("\n");
  }

  printf("\n\nEffects:");
  for ( j = 0; j < a->num_effects; j++ ) {
    printf("\n\neffect %d", j);
    e = &(a->effects[j]);
    printf("\n\nConditions\n");
    for ( i = 0; i < e->num_conditions; i++ ) {
      print_ft_name( e->conditions[i] );
      printf("\n");
    }
    printf("\nAdds\n");
    for ( i = 0; i < e->num_adds; i++ ) {
      print_ft_name( e->adds[i] );
      printf("\n");
    }
    printf("\nDels\n");
    for ( i = 0; i < e->num_dels; i++ ) {
      print_ft_name( e->dels[i] );
      printf("\n");
    }
  }

}



void print_type( int t )

{

  int j;

  if ( gpredicate_to_type[t] == -1 ) {
    if ( gnum_intersected_types[t] == -1 ) {
      printf("%s", gtype_names[t]);
    } else {
      printf("INTERSECTED TYPE (");
      for ( j = 0; j < gnum_intersected_types[t]; j++ ) {
	if ( gpredicate_to_type[gintersected_types[t][j]] == -1 ) {
	  printf("%s", gtype_names[gintersected_types[t][j]]);
	} else {
	  printf("UNARY INERTIA TYPE (%s)", 
		 gpredicates[gpredicate_to_type[gintersected_types[t][j]]]);
	}
	if ( j < gnum_intersected_types[t] - 1 ) {
	  printf(" and ");
	}
      }
      printf(")");
    }
  } else {
    printf("UNARY INERTIA TYPE (%s)", gpredicates[gpredicate_to_type[t]]);
  }

}



void print_Fact( Fact *f )

{

  int j;

  if ( f->predicate == -3 ) {
    printf("GOAL-REACHED");
    return;
  }

  if ( f->predicate == -1 ) {
    printf("=(");
    for ( j=0; j<2; j++ ) {
      if ( f->args[j] >= 0 ) {
	printf("%s", gconstants[(f->args)[j]]);
      } else {
	printf("x%d", DECODE_VAR( f->args[j] ));
      }
      if ( j < 1) {
	printf(" ");
      }
    }
    printf(")");
    return;
  }

  if ( f->predicate == -2 ) {
    printf("!=(");
    for ( j=0; j<2; j++ ) {
      if ( f->args[j] >= 0 ) {
	printf("%s", gconstants[(f->args)[j]]);
      } else {
	printf("x%d", DECODE_VAR( f->args[j] ));
      }
      if ( j < 1) {
	printf(" ");
      }
    }
    printf(")");
    return;
  }
    
  printf("%s(", gpredicates[f->predicate]);
  for ( j=0; j<garity[f->predicate]; j++ ) {
    if ( f->args[j] >= 0 ) {
      printf("%s", gconstants[(f->args)[j]]);
    } else {
      printf("x%d", DECODE_VAR( f->args[j] ));
    }
    if ( j < garity[f->predicate] - 1 ) {
      printf(" ");
    }
  }
  printf(")");

}



void print_ft_name( int index )

{

  print_Fact( &(grelevant_facts[index]) );

}



void print_op_name( int index )

{

  int i;
  Action *a = gop_conn[index].action;

  if ( !a->norm_operator &&
       !a->pseudo_action ) {
    printf("REACH-GOAL");
  } else {
    printf("%s", a->name ); 
    for ( i = 0; i < a->num_name_vars; i++ ) {
      printf(" %s", gconstants[a->name_inst_table[i]]);
    }
  }

}



void print_Variable_Value( int var, int val, Bool verbose )

{

  if ( !verbose ) {
    if ( gvariables[var].vals[val] != -1 ) {
      print_ft_name(gvariables[var].vals[val]);
      /*     printf(" (REF: %d)\n", gvariables[var].vals[val]); */
    } else {
      printf("(--OTHER--)");
    }
    return;
  }

  if ( gvariables[var].vals[val] != -1 ) {
    print_ft_name(gvariables[var].vals[val]);
    /*     printf(" (REF: %d)\n", gvariables[var].vals[val]); */
  } else {
    print_Variable(var);
    printf(":");
    printf("(--OTHER--)");
  }
  
}



void print_Variable( int var )

{

  int i;

  if ( strcmp(gvariables[var].name, "-1") == SAME ) {
    for ( i = 0; i < gvariables[var].num_vals; i++ ) {
      print_Variable_Value(var, i, FALSE);
      if ( i < gvariables[var].num_vals - 1 ) {
	printf("-");
      }
    }
    return;
  } 

  printf("%s", gvariables[var].name);

}



void print_SG( void )

{

  int node, i;

  for ( node = 0; node < gSG.num_nodes; node++ ) {
    if ( !gSG.nodes[node].IN ) {
      continue;
    }

    for ( i = 0; i < gSG.nodes[node].num_succ; i++ ) {
      if ( !gSG.nodes[node].succ[i]->IN ) {
	continue;
      }
      if ( !gSG.nodes[node].succ[i]->end->IN ) {
	continue;
      }

      print_Variable(gSG.nodes[node].var);
      printf(" ===> ");
      print_Variable(gSG.nodes[node].succ[i]->end->var);
      printf("\n");
    }
  }

/*   if ( gSG.is_acyclic ) { */
/*     printf("==========PROP: SG is acyclic!\n"); */
/*   } else { */
/*     printf("==========PROP: SG contains cycle!\n"); */
/*   } */

}



void print_DTG( int var )

{

  int node, i;

/*   for ( i = 0; i < gDTGs[var].num_transitions; i++ ) { */
/*     print_DTGTransition(&(gDTGs[var].transitions[i])); */
/*   } */
  
  for ( node = 0; node < gDTGs[var].num_nodes; node++ ) {
    for ( i = 0; i < gDTGs[var].nodes[node].num_out; i++ ) {
      print_DTGTransition(gDTGs[var].nodes[node].out[i], TRUE);
    }
  }

  if ( gDTGs[var].all_invertible ) {
    printf("==========PROP: all transitions invertible!\n");
  }

  if ( gDTGs[var].all_no_side_effects ) {
    printf("==========PROP: all transitions have no side effects!\n");
  }

  if ( !(gDTGs[var].all_invertible && gDTGs[var].all_no_side_effects) &&
       gDTGs[var].NONLEAF_irrelevant_or_invertiblenoseff_or_irrelevantdeletes ) {
    printf("==========PROP: NON-LEAF --- all transitions are irrelevant, or\n");
    printf("                are invertible or potentially induced and have no side effects, or\n");
    printf("                have an irrelevant own-delete and irrelevant side effect deletes!\n"); 
  }

  if ( !gDTGs[var].all_no_side_effects &&
       !gDTGs[var].NONLEAF_irrelevant_or_invertiblenoseff_or_irrelevantdeletes &&
       gDTGs[var].LEAF_irrelevant_or_irrelevantseffdel_or_irrelevantseffrecoverableseffdel ) {
    printf("==========PROP: STRONGLEAF --- all transitions are irrelevant, or\n");
    printf("                have irrelevant side effect deletes, or\n");
    printf("                have irrelevant side effects and recoverable side effect deletes!\n");
  }

  if ( gDTGs[var].var_is_SG_leaf ) {
    printf("==========PROP: is SG leaf!\n");
  }

  if ( gDTGs[var].var_is_goal ) {
    printf("==========PROP: is goal!\n");
  }

  printf("==========DIAM:    %4d\n", gDTGs[var].diameter);
  printf("==========MAXDIAM: %4d\n", gDTGs[var].maxdiameter);
  

}



void print_DTGTransition( DTGTransition *t, Bool verbose )

{

  int j;

  if ( !t ) {
    printf("\nprinting NULL transition?\n\n");
    exit(1);
  }
  if ( !t->start ) {
    printf("\nprinting transition with NULL start?\n\n");
    exit(1);
  }
  if ( !t->end ) {
    printf("\nprinting transition with NULL end?\n\n");
    exit(1);
  }

  print_Variable_Value(t->start->var, t->start->val, TRUE);
  fflush(stdout);
  printf(" + [");
  for ( j = 0; j < t->num_conditions; j++ ) {
    if ( !t->conditions ) {
      printf("\nprinting transition with NULL conditions?\n\n");
      exit(1);
    }
    if ( !t->conditions[j] ) {
      printf("\nprinting transition with NULL condition %d?\n\n", j);
      exit(1);
    }
    print_Variable_Value(t->conditions[j]->var, t->conditions[j]->val, TRUE);
    if ( j < t->num_conditions - 1 ) {
      printf(",");
    }
  }
  printf("] ---> ");
/*   printf("] ==="); */
/*   print_op_name(t->rop); */
/*   printf("===> "); */
  print_Variable_Value(t->end->var, t->end->val, TRUE);
  printf(" + [");
  for ( j = 0; j < t->num_side_effects; j++ ) {
    if ( !t->side_effects ) {
      printf("\nprinting transition with NULL side effects?\n\n");
      exit(1);
    }
    if ( !t->side_effects[j] ) {
      printf("\nprinting transition with NULL side effect %d?\n\n", j);
      exit(1);
    }
    print_Variable_Value(t->side_effects[j]->var, t->side_effects[j]->val, TRUE);
    if ( j < t->num_side_effects - 1 ) {
      printf(",");
    }
  }
  printf("]");

  if ( verbose ) {
    printf(" === PROPs:");

    if ( t->irrelevant ) {
      printf(" irrelevant");
    }
    if ( t->invertible ) {
      printf(" invertible");
    }
    if ( t->no_side_effects ) {
      printf(" no-side-effects");
    }
    if ( t->irrelevant_own_delete ) {
      printf(" irrelevant-own-delete");
    }
    if ( !t->no_side_effects && t->irrelevant_side_effect_deletes ) {
      printf(" irrelevant-side-effect-deletes");
    }
    if ( !t->no_side_effects && 
	 !t->irrelevant_side_effect_deletes &&
	 t->self_irrelevant_side_effect_deletes ) {
      printf(" self-irrelevant-side-effect-deletes");
    }
    if ( !t->no_side_effects && 
	 !t->irrelevant_side_effect_deletes &&
	 t->replacable_side_effect_deletes ) {
      printf(" replacable-side-effect-deletes");
    }
    if ( !t->no_side_effects && t->irrelevant_side_effects ) {
      printf(" irrelevant-side-effects");
    }
    if ( !t->no_side_effects && 
	 !t->irrelevant_side_effect_deletes && 
	 t->recoverable_side_effect_deletes ) {
      printf(" recoverable-side-effect-deletes");
    }
    if ( !t->no_side_effects && 
	 !t->irrelevant_side_effect_deletes && 
	 !t->irrelevant_side_effects &&
	 t->recoverable_side_effect_deletes && 
	 t->recoverer_only_relevant_side_effects ) {
      printf(" recoverer-only-relevant-side-effects");
    }
  }

  printf("\n");

}











/*
 * program output routines
 */









void print_plan( void )

{  

  int i;
  /* , ef, j; */

  printf("\n\nff: found legal plan as follows");
  printf("\n\nstep ");
  for ( i = 0; i < gnum_plan_ops; i++ ) {
/*     printf("\n\nnstate:"); */
/*     print_state(gplan_states[i]); */

/*     printf("\n\nprec:"); */
/*     ef = gop_conn[gplan_ops[i]].E[0]; */
/*     for ( j =0; j < gef_conn[ef].num_PC; j++ ) { */
/*       print_ft_name(gef_conn[ef].PC[j]); */
/*     } */

    printf("%4d: ", i);
    print_op_name( gplan_ops[i] );
    printf("\n     ");
  }

}
