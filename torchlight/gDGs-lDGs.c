

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


/*********************************************************************
 * File: gDGs-lDGs.c
 *
 * Description: extraction and analysis of global dependency graphs
 * and local dependency graphs
 *
 * Author: Joerg Hoffmann
 *
 *********************************************************************/ 






#include "torchlight.h"
#include "output.h"
#include "gDGs-lDGs.h"

















/**********************
 * Global analysis with gDGs
 **********************/

























/* Let $(\vars,\ini,\goal,\ops)$ be a planning task. Say that, for all
 * global dependency graphs $\gdg = (V,A)$ for some $\var_0$ and
 * $\op_0$ where the transition $(c,c')$ taken by $\op_0$ on $\var_0$
 * is not irrelevant, we have: $\gdg$ is acyclic; the transition
 * $(c,c')$ either has irrelevant side effect deletes, or has
 * irrelevant side effects and recoverable side effect deletes; and
 * the $\dtg_\var$ transitions of every non-leaf $\var \in V$ either
 * are irrelevant, or are invertible or potentially induced and have
 * no side effects, or have an irrelevant own-delete and irrelevant
 * side effect deletes. 
 *
 * Then the state space of the task does not contain any local minima.
 * Then, for any state $s \in \statespace$ with $0 < \hplus(s) <
 * \infty$, $\ed(s) \leq \max_{\gdg} \Dcost(\gdg)$, and $\ed(s) \leq
 * \max_{\gdg} \Dcost(\gdg) - 1$ if every transition $(c,c')$ has
 * irrelevant side effect deletes.
 *
 */
void analyze_global( void )

{

  static Bool fc = TRUE;

  Bool nolm = TRUE;
  Bool max_ed_bound = TRUE;
  int ed_bound = 0;

  int var0, trans0;
  int new_ed_bound;

  int var;
  DTGTransition *t0;

  int i, j;
  Action *my_a;
  Operator *my_o;

  int bbb = 0, aaa = 0;



  if ( fc ) {
    ggDG_responsible_var0s = ( int * ) 
      calloc(gnum_variables * gnum_operators, sizeof( int ));
    ggDG_responsible_op0s = ( int * ) 
      calloc(gnum_variables * gnum_operators, sizeof( int ));
    ggDG_responsible_op0var0s_weights = ( int * ) 
      calloc(gnum_variables * gnum_operators, sizeof( int ));
    for ( i = 0; i < gnum_variables * gnum_operators; i++ ) {
      ggDG_responsible_op0var0s_weights[i] = 0;
    }
    ggDG_num_responsible_op0var0s = 0;

    fc = FALSE;
  }



/*   /\* preliminary version without gDGs, just testing the simple */
/*    * sufficient criteria */
/*    *\/ */

/*   if ( !gSG.is_acyclic ) { */
/*     nolm = FALSE; */
/*   } */
  
/*   for ( var = 0; var < gnum_variables; var++ ) { */
/*     if ( gDTGs[var].var_is_SG_leaf && */
/* 	 !gDTGs[var].LEAF_irrelevant_or_irrelevantseffdel_or_irrelevantseffrecoverableseffdel ) { */
/*       nolm = FALSE; */
/*     } */
/*     if ( !gDTGs[var].var_is_SG_leaf && */
/* 	 !gDTGs[var].NONLEAF_irrelevant_or_invertiblepinducednoseff_or_irrelevantdeletes ) { */
/*       nolm = FALSE; */
/*     } */
/*   } */

/*   if ( nolm ) { */
/*      printf("\n\n========================PLAIN GLOBAL ANALYSIS: no local minima under h+!"); */
/*   } */



  /* set defaults for return values
   */
  gsuccess = FALSE;
  ged_bound = -1;



  /* gDG - based!
   *
   * Look at all gDGs -- for each goal var and non-irrelevant
   * transition -- and test whether they are cycle-free and fulfill
   * the LEAF/NON-LEAF criteria.
   */

  ggDG_num_graphs = 0;
  ggDG_num_successes = 0;


/*   for ( var0 = 0; var0 < gnum_variables; var0++ ) { */
/*     printf("\nvar0 %d: isgoal? %d, has %d transitions",  */
/* 	   var0, gDTGs[var0].var_is_goal, */
/* 	   gDTGs[var0].num_transitions); */
/*     fflush(stdout); */
/*   } */


  for ( var0 = 0; var0 < gnum_variables; var0++ ) {
    if ( !gDTGs[var0].var_is_goal ) {
      continue;
    }
/*     printf("\nnew var0 %d is %d with %d transitions", aaa++, var0, gDTGs[var0].num_transitions); */
/*     fflush(stdout); */

/*     bbb = 0; */
    for ( trans0 = 0; trans0 < gDTGs[var0].num_transitions; trans0++ ) {
      t0 = &(gDTGs[var0].transitions[trans0]);

      if ( t0->irrelevant ) {
	continue;
      }

/*       printf("\nnew t0 %d of var0 %d with %d transitions",  */
/* 	     bbb++, var0, gDTGs[var0].num_transitions); */
/*       fflush(stdout); */

      /* count total number of attempts to build a successful gDG.
       */
      ggDG_num_graphs++;

      if ( !construct_gDG( var0, t0 ) ) {
	/* got a cycle!
	 */
/* 	printf("\ncycle!"); */
	nolm = FALSE;
	max_ed_bound = FALSE;
	if ( gcmd_line.do_diagnose_gDG_successrate ) {
	  /* for gDG percentage analysis, need to keep running this!
	   */
	  continue;
	} else {
	  break;
	}
      }

      if ( !gcmd_line.do_recoverer_only_relevant ) {
	if ( !t0->self_irrelevant_side_effect_deletes &&
	     !(t0->irrelevant_side_effects && t0->recoverable_side_effect_deletes) &&
	     !t0->replacable_side_effect_deletes ) {
	  /* t0 does not qualify
	   */
	  /* 	printf("\nt0 no qualify!"); */
	  nolm = FALSE;
	  max_ed_bound = FALSE;
	  if ( gcmd_line.do_diagnose_gDG_successrate ) {
	    /* for gDG percentage analysis, need to keep running this!
	     */
	    continue;
	  } else {
	    break;
	  }
	}
      } else {
	if ( !t0->self_irrelevant_side_effect_deletes &&
	     !(t0->recoverer_only_relevant_side_effects && t0->recoverable_side_effect_deletes) &&
	     !t0->replacable_side_effect_deletes ) {
	  /* t0 does not qualify
	   */
	  /* 	printf("\nt0 no qualify!"); */
	  nolm = FALSE;
	  max_ed_bound = FALSE;
	  if ( gcmd_line.do_diagnose_gDG_successrate ) {
	    /* for gDG percentage analysis, need to keep running this!
	     */
	    continue;
	  } else {
	    break;
	  }
	}
      }

      if ( !SG_fullDTGs_INsubgraph_nonleafs_qualifies( var0, t0 ) ) {
	/* one of the non-leaf vars does not satisfy the prerequisites
	 * of the theorem on each gDG
	 */
/* 	printf("\nno qualify!"); */
	nolm = FALSE;
	max_ed_bound = FALSE;
	if ( gcmd_line.do_diagnose_gDG_successrate ) {
	  /* for gDG percentage analysis, need to keep running this!
	   */
	  continue;
	} else {
	  break;
	}
      }

      ggDG_num_successes++;

      if ( gcmd_line.do_diagnose_gDG_successrate ) {
	/* record this success for diagnosis!
	 */
	my_a = gop_conn[t0->rop].action;
	if ( my_a->norm_operator ) {
	  my_o = my_a->norm_operator->operator;
	} else {
	  if ( my_a->pseudo_action ) {
	    my_o = my_a->pseudo_action->operator;
	  } else {
	    printf("\ngDG: my_a has neither norm op nor pseudo act??\n\n");
	    exit(1);
	  }
	}
	for ( i = 0; i < ggDG_num_responsible_op0var0s; i++ ) {
	  if ( ggDG_responsible_var0s[i] == var0 &&
	       goperators[ggDG_responsible_op0s[i]] == my_o ) {
	    break;
	  }
	}
	if ( i == ggDG_num_responsible_op0var0s ) {
	  ggDG_responsible_var0s[ggDG_num_responsible_op0var0s] = var0;
	  for ( j = 0; j < gnum_operators; j++ ) {
	    if ( goperators[j] == my_o ) {
	      break;
	    }
	  }
	  if ( j == gnum_operators ) {
	    printf("\ndidn't find my_o operator??\n\n");
	    exit(1);
	  }
	  ggDG_responsible_op0s[ggDG_num_responsible_op0var0s] = j;
	  ggDG_responsible_op0var0s_weights[ggDG_num_responsible_op0var0s] = 1;
	  ggDG_num_responsible_op0var0s++;
	} else {
	  ggDG_responsible_op0var0s_weights[i]++;
	}
      } /* endif want gDG success rate diagnosis */      

      new_ed_bound = SG_fullDTGs_INsubgraph_Dcost( var0 );
      if ( t0->self_irrelevant_side_effect_deletes ||
	   t0->replacable_side_effect_deletes ) {
	new_ed_bound--;
      }
      if ( ed_bound < new_ed_bound ) {
	ed_bound = new_ed_bound;
      }
    } /* endfor trans0 over t0s */

    if ( !gcmd_line.do_diagnose_gDG_successrate ) {
      /* for gDG percentage analysis, need to keep running this!
       */
      if ( trans0 < gDTGs[var0].num_transitions ) {
	/* found bad gDG! no need to continue.
	 */
	break;
      }
    }
  } /* endfor var0 over x0s */



  if ( nolm ) {
    gsuccess = TRUE;
/*     printf("\n========================gDG GLOBAL ANALYSIS: no local minima under h+!"); */
  }
  if ( max_ed_bound ) {
    ged_bound = ed_bound;
/*     printf("\n========================gDG GLOBAL ANALYSIS: h+ exit distance bound %d!\n", */
/* 	   ed_bound); */
  }

}



/* \item We have $\var \in V$ and $(\var,\var') \in A$ if either:
 * $\var' = \var_0$ and $\var_0 \neq \var \in \vars_{\pre_{op_0}}$; or
 * $\var' \in V \setminus \{\var_0\}$ and $(\var,\var')$ is an arc in
 * $\sg$.
 *
 */
Bool construct_gDG( int var0, DTGTransition *t0 )

{

  static Bool fc = TRUE;
  static SGNode_pointer *openlist;
/*   static int *openlist_father; */

  int i, j;
  int op0;
  SGNode *nextnode;
  int nextvar;
  int current_node, current_end;
  Bool result;

  /* a simple hack to recognize that this new guy will fail for the same reason 
   * as the previous one
   */
  static int previous_var0;
  static int *var0_predecessors;
  static int num_var0_predecessors;
  static int *previous_var0_predecessors;
  static int num_previous_var0_predecessors;



  if ( fc ) {
    openlist = ( SGNode_pointer * ) calloc(gSG.num_nodes, sizeof( SGNode_pointer ));
/*     openlist_father = ( int * ) calloc(gSG.num_nodes, sizeof( int )); */

    previous_var0_predecessors = ( int * ) calloc(gSG.num_nodes, sizeof( int ));
    var0_predecessors = ( int * ) calloc(gSG.num_nodes, sizeof( int ));
    num_previous_var0_predecessors = -1;
    previous_var0 = -1;
    fc = FALSE;
  }



  /* initialization: everything is out.
   */
  for ( i = 0; i < gSG.num_nodes; i++ ) {
    gSG.nodes[i].IN = FALSE;
/*     for ( j = 0; j < gSG.num_nodes; j++ ) { */
/*       gSG.IN_adj_matrix[i][j] = FALSE; */
/*     } */
  }
  for ( i = 0; i < gSG.num_edges; i++ ) {
    gSG.edges[i].IN = FALSE;
    gSG.IN_adj_matrix[gSG.edges[i].start->var][gSG.edges[i].end->var] = FALSE; 
  }



  /* the start is in for sure.
   */
  gSG.nodes[var0].IN = TRUE;
  openlist[0] = &(gSG.nodes[var0]);
/*   openlist_father[0] = -1; */

  current_node = 0;
  current_end = 1;
  


  /* now add the vars in the precondition of rop(t0)=op0 note: these
   * are necessarily SG arcs because they stem from the relevant
   * transition t0
   */
  num_var0_predecessors = 0;
  op0 = t0->rop;
  for ( i = 0; i < gop_conn[op0].num_pre; i++ ) {
    nextvar = gop_conn[op0].pre[i].var;
    if ( nextvar == var0 ) {
      /* no need to add var0 itself, since in the lDG setting this
       * prec will be satisfied in s anyway
       */
      continue;
    }
    nextnode = &(gSG.nodes[nextvar]);

    if ( nextnode->IN ) {
      printf("\nnextnode->IN??\n\n");
      exit(1);
    }

    /* insert the var
     */
    if ( current_end >= gSG.num_nodes ) {
      printf("\ngDG current_end %d >= %d gSG.num_nodes??\n\n",
	     current_end,
	     gSG.num_nodes);
      exit( 1 );
    }
    nextnode->IN = TRUE;
    openlist[current_end] = nextnode;
/*     openlist_father[current_end] = 0; */
    current_end++;
    
    /* and insert the respective SG arc.
     */
    for ( j = 0; j < nextnode->num_succ; j++ ) {
      if ( nextnode->succ[j]->end->var == var0 ) {
	break;
      }
    }
    if ( j == nextnode->num_succ ) {
      printf("\ngDG j == nextnode->num_succ??\n\n");
      exit(1);
    }
    nextnode->succ[j]->IN = TRUE;      
    gSG.IN_adj_matrix[nextvar][var0] = TRUE;

    /* and remember this.
     */
    var0_predecessors[num_var0_predecessors] = nextvar;
    num_var0_predecessors++;
  }
  current_node = 1;


  
  /* now check whether it's the same var0 as the previous one that
   * failed due to a cycle, and whether we have all predecessors that
   * we had for that var. if so, we'll get a cycle anyway so can stop.
   */
  if ( previous_var0 != -1 && previous_var0 == var0 ) {
    /* we'll get here iff previous try on same var0 got a cycle
     */
    for ( i = 0; i < num_previous_var0_predecessors; i++ ) {
      if ( !gSG.nodes[previous_var0_predecessors[i]].IN ) {
	break;
      }
    }
    if ( i == num_previous_var0_predecessors ) {
      /* yep, it's the same guys all over again.
       */
/*       if ( 1 ) { */
/* 	printf("\nstop! same problem as with previous try!"); */
/*       } */
      return FALSE;
    }
  }



  /* now simply keep adding all SG predecessors of the nodes we already got.
   */
  while ( current_node < current_end ) {

    for ( i = 0; i < openlist[current_node]->num_pred; i++ ) {
      nextnode = openlist[current_node]->pred[i]->start;
      
      /* NO! if we have reached the same var from two fathers, then
       * only one is kept and thus this acyclicity check is
       * incomplete!
       */
/*       /\* To check if there is a cycle, see if this same node appears */
/*        * already on the path to it! */
/*        *\/ */
/*       for ( checknode = current_node;  */
/* 	    checknode >= 0;  */
/* 	    checknode = openlist_father[checknode] ) { */
/* 	if ( openlist[checknode] == nextnode ) { */
/* 	  break; */
/* 	} */
/*       } */
/*       if ( checknode >= 0 ) { */
/* /\* 	printf("\ncycle node: "); *\/ */
/* /\* 	print_Variable(nextnode->var); *\/ */
/* /\* 	printf("\n"); *\/ */
/* /\* 	print_SG(); *\/ */
/* 	return FALSE; */
/*       } */
/*       if ( nextnode->IN && */
/* 	   nextnode->start_distance != openlist[current_node]->start_distance + 1 ) { */
/* 	/\* hit a cycle! */
/* 	 * */
/* 	 * NOTE that it is Ok to reach a node two times from the same */
/* 	 * layer. A cycle occurs iff we had already reached this node */
/* 	 * earlier on. */
/* 	 *\/ */
/* 	printf("\ncycle node: "); */
/* 	print_Variable(nextnode->var); */
/* 	printf("\n"); */
/* 	print_SG(); */
/* 	return FALSE; */
/*       } */
      
      if ( !nextnode->IN ) {
	/* var is new --> insert it!
	 */
	if ( current_end >= gSG.num_nodes ) {
	  printf("\ncurrent_end %d >= %d gSG.num_nodes??\n\n",
		 current_end,
		 gSG.num_nodes);
	  exit( 1 );
	}
	openlist[current_end] = nextnode;
/* 	openlist_father[current_end] = current_node; */
	nextnode->IN = TRUE;
	current_end++;
      }

      /* in any case, need to insert the new edge.
       */
      if ( openlist[current_node]->pred[i]->IN ) {
	printf("\nopenlist[current_node]->pred[i]->IN??\n\n");
	exit(1);
      }
      openlist[current_node]->pred[i]->IN = TRUE;	
      gSG.IN_adj_matrix[nextnode->var][openlist[current_node]->var] = TRUE;
    }

    current_node++;
  }

  gchecking_acyclic_for = 1;
  result = SG_INsubgraph_acyclic();

/*   print_SG(); */



  if ( !result ) {
    /* record the problem for the next guy...
     */
    previous_var0 = var0;
    for ( i = 0; i < num_var0_predecessors; i++ ) {
      previous_var0_predecessors[i] = var0_predecessors[i];
    }
    num_previous_var0_predecessors = num_var0_predecessors;
  } else {
    /* note down that there is no problem here!
     */
    previous_var0 = -1;
  }



  return result;

}























/**********************
 * Local analysis with lDGs
 **********************/























/* Let $(\vars,\ini,\goal,\ops)$ be a planning task, and let $s \in
 * \statespace$ be a state with $0 < \hplus(s) < \infty$. Say that
 * $\var_0 \in \vars$ so that, for every $\op_0 = \rop(s(\var_0),c)$
 * in $\dtg_{\var_0}$ where $(s(\var_0),c)$ is not irrelevant,
 * $\ldg_{\op_0} = (V,A)$ is a local dependency graph for $s$ where:
 * $(s(\var_0),c)$ either has irrelevant side effect deletes, or has
 * irrelevant side effects and recoverable side effect deletes; and
 * the $\dtg_\var$ transitions of every $\var \in V \setminus
 * \{\var_0\}$ either are irrelevant, or are invertible or potentially
 * induced and have no side effects, or have an irrelevant own-delete
 * and irrelevant side effect deletes. 
 *
 * Then $s$ is not a local minimum. Then $\ed(s) \leq \max_{\op_0}
 * \Dcost(\ldg_{\op_0})$, and $\ed(s) \leq \max_{\op_0}
 * \Dcost(\ldg_{\op_0}) - 1$ if every $(s(\var_0),c)$ has irrelevant
 * side effect deletes.
 *
 * This function minimizes the ed bound over all var0s for which the
 * claim could be applied.
 */

void analyze_local_lDG( State *s )

{

  static Bool fc = TRUE;
  static int *s_on_var;

  Bool nolm = FALSE;
  Bool max_ed_bound = FALSE;
  int ed_bound = -1;
  int responsible_var0;

  Bool this_var0_nolm;
  Bool this_var0_max_ed_bound;
  int this_var0_ed_bound;

  int var0, trans0;
  int new_ed_bound;

  int var;
  DTGTransition *t0;
  int i, j, var1, sval;
  DTGNode *svalnode;



  if ( fc ) {
    s_on_var = ( int * ) calloc(gnum_variables, sizeof( int ));

    glDG_num_successes = 0;

    glDG_responsible_var0s = ( int * ) calloc(gnum_variables, sizeof( int ));
    glDG_responsible_var0s_weights = ( int * ) calloc(gnum_variables, sizeof( int ));
    for ( i = 0; i < gnum_variables; i++ ) {
      glDG_responsible_var0s_weights[i] = 0;
    }
    glDG_num_responsible_var0s = 0;

    fc = FALSE;
  }



  /* set defaults for return values
   */
  gsuccess = FALSE;
  ged_bound = -1;
  gdead_end = FALSE;



  /* this whole thing gives a guarantee only if a relaxed plan
   * actually exists.
   */
  if ( get_1P( s, &ggoal_state ) == INFINITY ) {
    gdead_end = TRUE;
    return;
  }


  
  /* just a helper to be easily able to ask what the value of var x in s is.
   */
  for ( i = 0; i < gnum_variables; i++ ) {
    s_on_var[i] = -1;
  }
  for ( i = 0; i < s->num_F; i++ ) {
    if ( gft_conn[s->F[i]].notFD ) {
      continue;
    }
    if ( s_on_var[gft_conn[s->F[i]].var] != -1 ) {
      printf("\ns_on_var[gft_conn[s->F[i]].var] != -1??\n\n");
      exit(1);
    }
    s_on_var[gft_conn[s->F[i]].var] = gft_conn[s->F[i]].val;
  }
  for ( i = 0; i < gnum_variables; i++ ) {
    if ( s_on_var[i] == -1 ) {
      /* must be OTHER
       */
      for ( j = 0; j < gvariables[i].num_vals; j++ ) {
	if ( gvariables[i].vals[j] == -1 ) {
	  break;
	}
      }
      if ( j < gvariables[i].num_vals ) {
	s_on_var[i] = j;
      } else {
	printf("\ndidn't find OTHER value for variable not set by state?\n\n");
	exit(1);
      }
    }
  }

  

  /* $(V,A)$ contains the single leaf vertex $\var_0$, with $\var_0
   * \in \vars_{\goal}$ and $\goal(\var_0) \neq s(\var_0)$; there
   * exists no successor $\var'$ of $\var_0$ in $\sg$ so that $\var'
   * \in \vars_{\goal}$ and $\goal(\var') \neq s(\var')$.
   */
  for ( var0 = 0; var0 < gnum_variables; var0++ ) {

    /* $\var_0 \in \vars_{\goal}$ and $\goal(\var_0) \neq s(\var_0)$?
     */ 
    if ( !gDTGs[var0].var_is_goal ) {
      continue;
    }
    if ( ggoal_on_var[var0] == -1 ) {
      printf("\nggoal_on_var[var_0] == -1??\n\n");
      exit(1);
    }
    if ( ggoal_on_var[var0] == s_on_var[var0] ) {
      continue;
    }



  /* DISABLED! Was runtime critical in some benchmarks and, finally,
   * is used for NOTHING with the single exception of identifying
   * non-leaf goal vars for x0 in lDGs... which seems a rather useless
   * occupation anyhow...
   */
/*     /\* there exists no transitive successor $\var'$ of $\var_0$ in */
/*      * $\sg$ so that $\var' \in \vars_{\goal}$ and $\goal(\var') \neq */
/*      * s(\var')$? */
/*      *\/ */
/*     for ( i = 0; i < gnum_variables; i++ ) { */
/*       if ( !gSG.trans_adj_matrix[var0][i] ) { */
/* 	continue; */
/*       } */
/*       if ( !gDTGs[i].var_is_goal ) { */
/* 	continue; */
/*       } */
/*       if ( ggoal_on_var[i] == s_on_var[var1] ) { */
/* 	continue; */
/*       } */
/*       break; */
/*     } */
/*     if ( i < gnum_variables ) { */
/*       /\* found a bad successor, cannot use this as var0 for lDG! */
/*        *\/ */
/*       continue; */
/*     } */

    /* OLD faulty version, looking only at direct successors!
     */
/*     for ( i = 0; i < gSG.nodes[var0].num_succ; i++ ) { */
/*       var1 = gSG.nodes[var0].succ[i]->end->var; */
/*       if ( !gDTGs[var1].var_is_goal ) { */
/* 	continue; */
/*       } */
/*       if ( ggoal_on_var[var1] == s_on_var[var1] ) { */
/* 	continue; */
/*       } */
/*       break; */
/*     } */
/*     if ( i < gSG.nodes[var0].num_succ ) { */
/*       /\* found a bad successor, cannot use this as var0 for lDG! */
/*        *\/ */
/*       continue; */
/*     } */

    /* use a much simpler sufficient test...
     * ... namely, use only x0 that are SG leafs!!!!
     */
    if ( gSG.nodes[var0].num_succ > 0 ) {
      continue;
    }
    


    /* this is a var0 candidate. let's if all the necessary lDGs are
     * there and satisfy the prerequisites.
     */
    this_var0_nolm = TRUE;
    this_var0_max_ed_bound = TRUE;
    this_var0_ed_bound = 0;

    /* look at all non-irrelevant transitions leaving the value of
     * var0 in s.
     */
    sval = s_on_var[var0];
    svalnode = &(gDTGs[var0].nodes[sval]);
    
    for ( trans0 = 0; trans0 < svalnode->num_out; trans0++ ) {
      t0 = svalnode->out[trans0];

      if ( t0->irrelevant ) {
	continue;
      }

      if ( !construct_lDG( s_on_var, var0, t0 ) ) {
	/* got a cycle!
	 */
	this_var0_nolm = FALSE;
	this_var0_max_ed_bound = FALSE;
	break;
      }

      if ( !gcmd_line.do_recoverer_only_relevant ) {
	if ( !t0->self_irrelevant_side_effect_deletes &&
	     !(t0->irrelevant_side_effects && t0->recoverable_side_effect_deletes) &&
	     !t0->replacable_side_effect_deletes ) {
	  /* t0 does not qualify
	   */
	  this_var0_nolm = FALSE;
	  this_var0_max_ed_bound = FALSE;
	  break;
	}
      } else {
	if ( !t0->self_irrelevant_side_effect_deletes &&
	     !(t0->recoverer_only_relevant_side_effects && t0->recoverable_side_effect_deletes) &&
	     !t0->replacable_side_effect_deletes ) {
	  /* t0 does not qualify
	   */
	  this_var0_nolm = FALSE;
	  this_var0_max_ed_bound = FALSE;
	  break;
	}
      }

      if ( !SG_fullDTGs_INsubgraph_nonleafs_qualifies( var0, t0 ) ) {
	/* one of the non-leaf vars does not satisfy the prerequisites
	 * of the theorem on each lDG
	 */
	this_var0_nolm = FALSE;
	this_var0_max_ed_bound = FALSE;
	break;
      }

      new_ed_bound = SG_fullDTGs_INsubgraph_Dcost( var0 );
      if ( t0->self_irrelevant_side_effect_deletes || 
	   t0->replacable_side_effect_deletes) {
	new_ed_bound--;
      }
      if ( this_var0_ed_bound < new_ed_bound ) {
	this_var0_ed_bound = new_ed_bound;
      }

    } /* endfor trans0 over transitions out of s(var0) */



    /* did the analysis of this var0 lead to success?
     * if yes, remember best of successes obtained.
     */
    if ( this_var0_nolm ) {
      nolm = TRUE;
    }

    if ( this_var0_max_ed_bound ) {
      max_ed_bound = TRUE;
      if ( ed_bound == -1 || this_var0_ed_bound < ed_bound ) {
	ed_bound = this_var0_ed_bound;
	responsible_var0 = var0;
      }

    }

  } /* endfor var0 over variables */



  if ( nolm ) {
    gsuccess = TRUE;

    glDG_num_successes++;

    for ( i = 0; i < glDG_num_responsible_var0s; i++ ) {
      if ( glDG_responsible_var0s[i] == responsible_var0 ) {
	break;
      }
    }
    if ( i == glDG_num_responsible_var0s ) {
      glDG_responsible_var0s[glDG_num_responsible_var0s] = responsible_var0;
      glDG_responsible_var0s_weights[glDG_num_responsible_var0s] = 1;
      glDG_num_responsible_var0s++;
    } else {
      glDG_responsible_var0s_weights[i]++;
    }
  }
  if ( max_ed_bound ) {
    ged_bound = ed_bound;
  }

/*   if ( !nolm ) { */
/*     printf("\nunsuccessful State in lDG: "); */
/*     for ( i = 0; i < gnum_variables; i++ ) { */
/*       print_Variable(i); */
/*       printf(": "); */
/*       print_Variable_Value(i, s_on_var[i], FALSE); */
/*       printf("\n       "); */
/*     } */
/*     printf("\n... and now in FF version: "); */
/*     print_state(*s); */
/*     printf("\n"); */
/*     printf("\n"); */
/*   } */

/*   if ( nolm ) { */
/*     if ( !max_ed_bound ) { */
/*       printf("\n!max_ed_bound??\n\n"); */
/*       exit(1); */
/*     } */
/*     printf("\n\n========================lDG LOCAL ANALYSIS: no lm, ed bound %d.",  */
/* 	   ed_bound); */
/*     printf("\n                        Responsible variable: "); */
/*     print_Variable( responsible_var0 ); */
/*     printf("\nState: "); */
/*     for ( i = 0; i < gnum_variables; i++ ) { */
/*       print_Variable(i); */
/*       printf(": "); */
/*       print_Variable_Value(i, s_on_var[i], FALSE); */
/*       printf("\n       "); */
/*     } */
/*     printf("\n"); */
     
/*   } */

}



/* \item We have $\var \in V$ and $(\var,\var') \in A$ if either:
 * $\var' = \var_0$, $\var \in \vars_{\pre_{op_0}}$, and
 * $\pre_{\op_0}(\var) \neq s(\var)$; or $\var' \in V \setminus
 * \{\var_0\}$ and $(\var,\var')$ is an arc in $\sg$.
 */
Bool construct_lDG( int *s_on_var, int var0, DTGTransition *t0 )

{

  static Bool fc = TRUE;
  static SGNode_pointer *openlist;

  int i, j;
  int op0;
  SGNode *nextnode;
  int nextvar;
  int current_node, current_end;
  Bool result;



  if ( fc ) {
    openlist = ( SGNode_pointer * ) calloc(gSG.num_nodes, sizeof( SGNode_pointer ));
    fc = FALSE;
  }



  /* initialization: everything is out.
   */
  for ( i = 0; i < gSG.num_nodes; i++ ) {
    gSG.nodes[i].IN = FALSE;
/*     for ( j = 0; j < gSG.num_nodes; j++ ) { */
/*       gSG.IN_adj_matrix[i][j] = FALSE; */
/*     } */
  }
  for ( i = 0; i < gSG.num_edges; i++ ) {
    gSG.edges[i].IN = FALSE;
    gSG.IN_adj_matrix[gSG.edges[i].start->var][gSG.edges[i].end->var] = FALSE; 
  }



  /* the start is in for sure.
   */
  gSG.nodes[var0].IN = TRUE;
  openlist[0] = &(gSG.nodes[var0]);

  current_node = 0;
  current_end = 1;
  


  /* now add the vars in the precondition of rop(t0) = op0, other than
   * those that are satisfied in s. note: these are necessarily SG
   * arcs because they stem from the relevant transition t0
   */
  op0 = t0->rop;
  for ( i = 0; i < gop_conn[op0].num_pre; i++ ) {
    nextvar = gop_conn[op0].pre[i].var;

    if ( nextvar == var0 ) {
      /* this will be satisfied in s, so no need to include. just
       * double-check for debugging...
       */
      if ( s_on_var[var0] != gop_conn[op0].pre_on_var[var0] ) {
	printf("\ns_on_var[var0] != gop_conn[op0].pre_on_var[var0]??\n\n");
      }
      continue;
    }

    if ( s_on_var[nextvar] == gop_conn[op0].pre_on_var[nextvar] ) {
      /* this prec is satisfied in s, no need to worry about it!
       */
      continue;
    }

    nextnode = &(gSG.nodes[nextvar]);

    if ( nextnode->IN ) {
      printf("\nlDG nextnode->IN??\n\n");
      exit(1);
    }

    /* insert the var
     */
    if ( current_end >= gSG.num_nodes ) {
      printf("\nlDG current_end %d >= %d gSG.num_nodes??\n\n",
	     current_end,
	     gSG.num_nodes);
      exit( 1 );
    }
    nextnode->IN = TRUE;
    openlist[current_end] = nextnode;
    current_end++;
    
    /* and insert the respective SG arc.
     */
    for ( j = 0; j < nextnode->num_succ; j++ ) {
      if ( nextnode->succ[j]->end->var == var0 ) {
	break;
      }
    }
    if ( j == nextnode->num_succ ) {
      printf("\nlDG j == nextnode->num_succ??\n\n");
      exit(1);
    }
    nextnode->succ[j]->IN = TRUE;
    gSG.IN_adj_matrix[nextvar][var0] = TRUE;
  }
  current_node = 1;



  /* now simply keep adding all SG predecessors of the nodes we already got.
   */
  while ( current_node < current_end ) {

    for ( i = 0; i < openlist[current_node]->num_pred; i++ ) {
      nextnode = openlist[current_node]->pred[i]->start;
      
      if ( !nextnode->IN ) {
	/* var is new --> insert it!
	 */
	if ( current_end >= gSG.num_nodes ) {
	  printf("\ncurrent_end %d >= %d gSG.num_nodes??\n\n",
		 current_end,
		 gSG.num_nodes);
	  exit( 1 );
	}
	openlist[current_end] = nextnode;
	nextnode->IN = TRUE;
	current_end++;
      }

      /* in any case, need to insert the new edge.
       */
      if ( openlist[current_node]->pred[i]->IN ) {
	printf("\nopenlist[current_node]->pred[i]->IN??\n\n");
	exit(1);
      }
      openlist[current_node]->pred[i]->IN = TRUE;
      gSG.IN_adj_matrix[nextnode->var][openlist[current_node]->var] = TRUE;
    }

    current_node++;
  }



  /* December 2011 de-BUG: if, for op effect on x', pre(op)(x)=s(x)
   * but x is a non-var0 var we already collected, then the value of x
   * may change during exit path construction, and therefore we need
   * to record the dependency (x,x')! 
   *
   * Since lDG collects all SG predecessors except those for var0/op0,
   * this is the only case we need to look at. We need to include a
   * new dependency (var,var0) if var0 \neq var is in pre(op0), var is
   * in lDG, and s(var) = pre(op0)(var).
   */
  op0 = t0->rop;
  for ( i = 0; i < gop_conn[op0].num_pre; i++ ) {
    nextvar = gop_conn[op0].pre[i].var;

    if ( nextvar == var0 ) {
      continue;
    }

    if ( s_on_var[nextvar] != gop_conn[op0].pre_on_var[nextvar] ) {
      /* this guy was already accounted for above.
       */
      continue;
    }

    nextnode = &(gSG.nodes[nextvar]);

    if ( !(nextnode->IN) ) {
      /* this guy is not in lDG, so no danger
       */
      continue;
    }
    
    /* insert the new SG arc!
     */
    for ( j = 0; j < nextnode->num_succ; j++ ) {
      if ( nextnode->succ[j]->end->var == var0 ) {
	break;
      }
    }
    if ( j == nextnode->num_succ ) {
      printf("\nlDG j == nextnode->num_succ??\n\n");
      exit(1);
    }

    if ( !nextnode->succ[j]->IN ) {
      /* if ( 1 ) { */
      /* 	printf("\nlDG de-BUG true-in-s-dependencies added arc!"); */
      /* } */
      nextnode->succ[j]->IN = TRUE;
      gSG.IN_adj_matrix[nextvar][var0] = TRUE;
    }
  }



  gchecking_acyclic_for = 2;
  result = SG_INsubgraph_acyclic();

  return result;

}




















/**********************
 * Control for analysis of samples
 **********************/


















void analyze_samples_local_lDG( void )

{

  int i;
  int num_success = 0;
  int min_ed_bound = -1;
  float mean_ed_bound = 0;
  int max_ed_bound = -1;
  int num_dead_end = 0;

  for ( i = 0; i < gcmd_line.num_samples; i++ ) {

    if ( gcmd_line.negative_diagnose_all ) {
      gdo_negative_diagnosis = TRUE;
    } else {
      gdo_negative_diagnosis = FALSE;
    }
    analyze_local_lDG( &(gsample_states[i]) );

    if ( gsuccess ) {
      num_success++;

      if ( min_ed_bound == -1 || ged_bound < min_ed_bound ) {
	min_ed_bound = ged_bound;
      }

      if ( max_ed_bound == -1 || ged_bound > max_ed_bound ) {
	max_ed_bound = ged_bound;
      }

      mean_ed_bound += ged_bound;
      
    } else {
      if ( !gcmd_line.negative_diagnose_all ) {
	/* now diagnose this state!
	 */
	gdo_negative_diagnosis = TRUE;
	analyze_local_lDG( &(gsample_states[i]) );
      }
    }

    if ( gdead_end ) {
      num_dead_end++;
    }

  }

  gsuccess_percentage = ((float) num_success) / ((float) gcmd_line.num_samples) * 100.0;
  gmin_ed_bound = min_ed_bound;
  gmax_ed_bound = max_ed_bound;
  gmean_ed_bound = mean_ed_bound / ((float) gcmd_line.num_samples);
  gdead_end_percentage = ((float) num_dead_end) / ((float) gcmd_line.num_samples) * 100.0;

}
