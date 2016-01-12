

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
 * File: oDGplus.c
 *
 * Description: extraction and analysis of optimal rplan dependency
 * graphs -- using of course the usual non-optimal relaxed plans as
 * the basis
 *
 * Author: Joerg Hoffmann
 *
 *********************************************************************/ 






#include "torchlight.h"
#include "output.h"
#include "oDGplus.h"
























/**********************
 * main function
 **********************/














/* the relaxed plan for s -- make locally global since this will
 * probably be of interest to everybody.
 */
int *lPplus_of_s;
int lnum_Pplus_of_s;

/* here's in the re-ordered (relative to one op0) version
 */
int *lreordered_Pplus_of_s;
int lreordered_num_Pplus_of_s;

/* this well tell us where "op0" is located in the reordered rplan
 */
int lreordered_ind0;

/* here, also, is the state, in two forms for convenience
 */
State ls;
int *ls_on_var;

/* this is a simple flag telling us whether we do want to record this
 * var0 in diagnosis
 */
Bool ldo_record_var0;











void analyze_local_oDGplus( State *s )

{

  static Bool fc = TRUE;

  Bool nolm = FALSE;
  Bool max_ed_bound = FALSE;
  int ed_bound = -1;
  int responsible_op0, responsible_var0;
  DTGTransition *responsible_t0;
  int responsible_pred0;

  int ind0, op0, var0, trans0;
  DTGTransition *t0;

  int new_ed_bound;
  int i, j, k;
  int op0_qualification;

  Bool reordered;
  int operator_num;
  Action *my_a;
  Operator *my_o;

  int eff, ftt;

  /* Joerg2014: new flag, to remember that one of the 3 criteria
     failed, while continuing in order to keep stats on which of the
     others would fail as well.
  */
  Bool failed;
  
  if ( fc ) {
    lPplus_of_s = ( int * ) calloc( gnum_op_conn, sizeof( int ));
    lreordered_Pplus_of_s = ( int * ) calloc( gnum_op_conn, sizeof( int ));

    ls_on_var = ( int * ) calloc( gnum_variables, sizeof( int ));

    make_state( &ls, gnum_ft_conn );

    /* Joerg2014: new count, to measure stats at attempt-level as
       opposed to sample-state level 
    */    
    goDGplus_num_graphs = 0; 

    goDGplus_num_successes = 0;

    goDGplus_num_fail_cyclic = 0; /* Joerg2014: new feature */
    goDGplus_num_fail_t0notadequate = 0; /* Joerg2014: new feature */
    goDGplus_num_fail_nonleavesnotadequate = 0; /* Joerg2014: new feature */

    goDGplus_num_succ_t0 = 0; /* Joerg2014: new feature */
    goDGplus_num_succ_t0adequateRFCempty = 0; /* Joerg2014: new feature */
    goDGplus_num_succ_t0adequateRFCrecovered = 0; /* Joerg2014: new feature */

    goDGplus_num_succ_nonleavesDTGt = 0; /* Joerg2014: new feature */
    goDGplus_num_succ_nonleavesDTGtnoseff = 0; /* Joerg2014: new feature */
    goDGplus_num_succ_nonleavesDTGtirrdel = 0; /* Joerg2014: new feature */
    goDGplus_num_succ_nonleavesDTGtirrseffdel = 0; /* Joerg2014: new feature */

    goDGplus_nonrecovered_RFC_intersect_preds = ( int * ) 
      calloc(gnum_variables * gnum_operators, sizeof( int ));
    goDGplus_nonrecovered_RFC_intersect_op0s = ( int * ) 
      calloc(gnum_variables * gnum_operators, sizeof( int ));
    goDGplus_nonrecovered_RFC_intersects_weights = ( int * ) 
      calloc(gnum_variables * gnum_operators, sizeof( int ));
    for ( i = 0; i < gnum_variables * gnum_operators; i++ ) {
      goDGplus_nonrecovered_RFC_intersects_weights[i] = 0;
    }
    goDGplus_num_nonrecovered_RFC_intersects = 0;
    goDGplus_nonrecovered_RFC_intersects_totalweight = 0;

    fc = FALSE;
  }



  /* set defaults for return values
   */
  gsuccess = FALSE;
  ged_bound = -1;
  gdead_end = FALSE;


  /* First, of all, get a relaxed plan. If none exists, nothing to do
   * for us here.
   */
  if ( get_1P( s, &ggoal_state ) == INFINITY ) {
/*     printf("\ndead end:"); */
/*     print_state(*s); */
/*     printf("\n\n"); */
/*     exit(1); */
    
    gdead_end = TRUE;
    return;
  }


  
  /* the rplan is now in grplan/gnum_rplan, however still in inverse
   * order. reverse.
   */
  lnum_Pplus_of_s = 0;
  for ( i = gnum_rplan - 1; i >= 0; i-- ) {
    lPplus_of_s[lnum_Pplus_of_s] = grplan[i];
    lnum_Pplus_of_s++;
  }
  if ( gcmd_line.display_info == 2 ) {
    printf("\n=========oDGplus analysis -- relaxed plan:");
    for ( i = 0; i < lnum_Pplus_of_s; i++ ) {
      printf("\n%d: ", i);
      print_op_name(lPplus_of_s[i]);
    }
    printf("\n");
  }



  /* set the locally-global state info
   */
  for ( i = 0; i < s->num_F; i++ ) {
    ls.F[i] = s->F[i];
  }
  ls.num_F = s->num_F;

  for ( i = 0; i < gnum_variables; i++ ) {
    ls_on_var[i] = -1;
  }
  for ( i = 0; i < s->num_F; i++ ) {
    if ( gft_conn[s->F[i]].notFD ) {
      continue;
    }
    if ( ls_on_var[gft_conn[s->F[i]].var] != -1 ) {
      printf("\nls_on_var[gft_conn[s->F[i]].var] != -1??\n\n");
      exit(1);
    }
    ls_on_var[gft_conn[s->F[i]].var] = gft_conn[s->F[i]].val;
  }
  for ( i = 0; i < gnum_variables; i++ ) {
    if ( ls_on_var[i] == -1 ) {
      /* must be OTHER
       */
      for ( j = 0; j < gvariables[i].num_vals; j++ ) {
	if ( gvariables[i].vals[j] == -1 ) {
	  break;
	}
      }
      if ( j < gvariables[i].num_vals ) {
	ls_on_var[i] = j;
      } else {
	printf("\ndidn't find OTHER value for variable not set by state?\n\n");
	exit(1);
      }
    }
  }
  /* just for debugging...
   */
  if ( !is_relaxed_plan_for_s( lPplus_of_s, lnum_Pplus_of_s ) ) {
    printf("\n!is_relaxed_plan_for_s( lPplus_of_s, lnum_Pplus_of_s )??\n\n");
    printf("\nrplan as returned: ");
    for ( i = 0; i < lnum_Pplus_of_s; i++ ) {
      printf("\n%d: ", i);
      print_op_name(grplan[i]);
    }
    printf("\nrplan as taken: ");
    for ( i = 0; i < lnum_Pplus_of_s; i++ ) {
      printf("\n%d: ", i);
      print_op_name(lPplus_of_s[i]);
    }
    printf("\nstate: ");
    print_state(ls);
    printf("\ngoal: ");
    print_state(ggoal_state);
    printf("\n");
    exit(1);
  }



  /* the main thing: loop over all ops in the rplan, and see if they
   * result in an oDGplus fulfilling all the requirements!
   *
   * Is perhaps a bit naive for now, simply trying all ops and taking
   * the best result. If this takes time, think about trying less ops
   * (maybe some can be more easily filtered out, without first
   * re-ordering the relaxed plan).
   *
   * ACTUALLY, simply stop as soon as the first success has been
   * derived!
   */
  for ( ind0 = 0; ind0 < lnum_Pplus_of_s; ind0++ ) {
    op0 = lPplus_of_s[ind0];
    reordered = FALSE;
    if ( gcmd_line.display_info == 2 ) {
      printf("\n\n=========oDGplus analysis -- op0: ");
      print_op_name(op0);
    }



    /* naively, enumerate all possible var0 associated with this op.
     */
    if ( gop_conn[op0].num_E == 0 ) {
      printf("\nHALLO gop_conn[op0].num_E == 0??\n\n");
      exit(1);
    }
    for ( i = 0; i < gop_conn[op0].num_eff; i++ ) {
      var0 = gop_conn[op0].eff[i].var;
      if ( gcmd_line.display_info == 2 ) {
	printf("\nvar0: ");
	print_Variable(var0);
      }

      /* only consider effects that are actually different from the
       * value of var0 in s.
       */
      if ( ls_on_var[var0] == gop_conn[op0].eff[i].val ) {
	if ( gcmd_line.display_info == 2 ) {
	  printf(" --- no change from s!");
	}
	continue;
      }
      
      /* OUTDATED -- what we really want is that op0 is
       * var0-preconditioned (if at all) on s(var0)
       */
/*       /\* is this the first eff on this var? */
/*        *\/ */
/*       for ( j = 0; j < lreordered_ind0; j++ ) { */
/* 	if ( gop_conn[lreordered_Pplus_of_s[j]].eff_on_var[var0] != -1 ) { */
/* 	  break; */
/* 	} */
/*       } */
/*       if ( j < lreordered_ind0 ) { */
/* 	if ( gcmd_line.display_info == 2 ) { */
/* 	  printf(" --- not the first effect on var0!"); */
/* 	} */
/* 	continue; */
/*       } */
      /* is op0 var0-preconditioned (if at all) on s(var0)?
       */
      if ( gop_conn[op0].pre_on_var[var0] != -1 &&
	   gop_conn[op0].pre_on_var[var0] != ls_on_var[var0] ) {	
	if ( gcmd_line.display_info == 2 ) {
	  printf(" --- preconditioned on var0 != s(var0)!");
	}
	continue;
      }

      /* Joerg2014: The default was to NOT prune useless var0. I got
	 no idea why. I set it to TRUE now; this plays a role in the
	 stats below ie the diagnosis of failure, which should be done
	 only for non-useless var0. In case this test here is turned
	 off ie useless var0 are being processed, need to take care to
	 not use them in diagnosis below (original code does so via
	 "ldo_record_var0" flag).
       */
      /* if ( gcmd_line.prune_useless_var0 ) { */
	/* is this effect a goal in the rest of rplan?
	 */
      ftt = gvariables[gop_conn[op0].eff[i].var].vals[gop_conn[op0].eff[i].val];
      if ( ftt == -1 ) {
	continue;
      }
      if ( !gft_conn[ftt].is_global_goal ) {
	for ( j = ind0+1; j < lnum_Pplus_of_s; j++ ) {
	  if ( gop_conn[lPplus_of_s[j]].num_E == 0 ) {
	    printf("\ngop_conn[lPplus_of_s[j]].num_E == 0??\n\n");
	    exit(1);
	  }
	  eff = gop_conn[lPplus_of_s[j]].E[0];
	  for ( k = 0; k < gef_conn[eff].num_PC; k++ ) {
	    if ( gef_conn[eff].PC[k] == ftt ) {
	      break;
	    }
	  }
	  if ( k < gef_conn[eff].num_PC ) {
	    break;
	  }
	}
	if ( j == lnum_Pplus_of_s ) {
	  continue;
	}
      }
      /* } */
      

      /* yep. find the transition.
       */
      for ( j = 0; j < gDTGs[var0].nodes[ls_on_var[var0]].num_out; j++ ) {
	t0 = gDTGs[var0].nodes[ls_on_var[var0]].out[j];
	if ( t0->rop == op0 ) {
	  break;
	}
      }
      if ( j == gDTGs[var0].nodes[ls_on_var[var0]].num_out ) {
	/* if we get here, this means that this is one of the
	 * operators that are not explicitly preconditioned on this
	 * var, but that do not take a transition out of its value
	 * here anyhow because some other precondition is excluding
	 * that value. Example: Ferry debark is not preconditioned on
	 * var-at-car because "in-ferry" is encoded as OTHER of that
	 * var. However, there is the precond "carry-car" which
	 * excludes at-car-location. Such transitions are not put into
	 * the DTG, and hence they do not occur here.
	 */
	if ( gcmd_line.display_info == 2 ) {
	  printf(" --- not preconditioned on var0, however spurious transition removed!");
	}
	continue;
/* 	printf("\nj == gDTGs[var0].nodes[ls_on_var[var0]].num_out??\n\n"); */
/* 	exit(1); */
      }
      if ( gcmd_line.display_info == 2 ) {
	printf("\nt0: ");
	print_DTGTransition(t0, FALSE);
      }



      if ( t0->irrelevant ) {
	/* we consider only relevant transitions of op0
	 */
	continue;
      }

      /* Joerg2014: We get here for all t0 which we actually test for
	 oDGplus construction. Hence count here.
      */
      goDGplus_num_graphs++;

      /* this op0/var0/t0 needs to be checked! If not already done,
       * taylor the rplan to op0, by moving all ops behind it, as far as
       * possible.
       */
      if ( !reordered ) {
	reorder_Pplus_of_s( ind0 );
	if ( gcmd_line.display_info == 2 ) {
	  printf("\nreordered relaxed plan for %d: ", ind0);
	  print_op_name(op0);
	  printf(" now at %d", lreordered_ind0);
	  for ( j = 0; j < lreordered_num_Pplus_of_s; j++ ) {
	    printf("\n%d: ", j);
	    print_op_name(lreordered_Pplus_of_s[j]);
	  }
	  printf("\n");
	}
	reordered = TRUE;
      }

      
      /* Joerg2014: new flag, to remember that one of the 3 criteria
	 failed, while continuing in order to keep stats on which of the
	 others would fail as well.
      */
      failed = FALSE;

      /* now get the oDGplus for this rplan, op0, var0, t0
       */
      if ( !construct_oDGplus( op0, var0, t0 ) ) {
	/* got a cycle!
	 */
	goDGplus_num_fail_cyclic++; /* Joerg2014: new feature */
	/* Joerg2014: also execute the two tests below, to be able
	   to record whether or not they would fail as well
	*/
	/* continue; */
	failed = TRUE;
      }

      /* check the needed properties for non-leafs
       */
      if ( !SG_DTGs_oDGplus_INsubgraph_nonleafs_qualifies( var0 ) ) {
	/* one of the non-leaf vars does not satisfy the prerequisites
	 * of the theorem
	 */
	if ( gcmd_line.display_info == 2 ) {
	  printf("\nnon-leaf nodes do not qualify!");
	}
	goDGplus_num_fail_nonleavesnotadequate++; /* Joerg2014: new feature */
	/* Joerg2014: also execute the two tests below, to be able
	   to record whether or not they would fail as well
	*/
	/* continue; */
	failed = TRUE;
      }

      /* check whether op0, t0 satisfy point 2 of oDG+ def
       * 1 == (2a), 2 == (2b), 3 == (2c), -1 == none
       */
      op0_qualification = op0_var0_t0_qualification( op0, var0, t0 );
      if ( op0_qualification == -1 ) {
	/* we do not have (2a) or (2b) or (2c)
	 */
	if ( gcmd_line.display_info == 2 ) {
	  printf("\nop0, var0, t0 do not qualify!");
	}
	goDGplus_num_fail_t0notadequate++; /* Joerg2014: new feature */
	/* Joerg2014: do symmetrically to above 2 cases, for clarity.
	*/
	/* continue; */
	failed = TRUE;
      } else {
	/* Joerg2014: keep track of how often this criterion was Ok.
	*/
	goDGplus_num_succ_t0++;
      }

      if ( failed ) {
	continue;
      }

      /* this choice of op0, var0, t0 is successful!
       */
      goDGplus_num_successes++;

      nolm = TRUE;
      max_ed_bound = TRUE;
      new_ed_bound = SG_DTGs_oDGplus_INsubgraph_dcost( var0 );
      if ( op0_qualification == 1 || op0_qualification == 3 ) {
	new_ed_bound--;
      }
      if ( gcmd_line.display_info == 2 ) {
	printf("\nno lm, ed bound %d!", new_ed_bound);
      }

      if ( ed_bound == -1 || new_ed_bound < ed_bound ) {
	if ( gcmd_line.display_info == 2 ) {
	  printf(" -- improves old bound %d!", ed_bound);
	}
	ed_bound = new_ed_bound;
	responsible_op0 = op0;
	responsible_var0 = var0;
	responsible_t0 = t0;
      }
      if ( gcmd_line.display_info == 2 ) {
	printf("\n");
      }

      if ( !gcmd_line.optimize_over_op0var0 ) {     
	/* signal that we're good!
	 */
	break;
      }

    } /* i, var0 over selection of var0 for op0 */

    if ( !gcmd_line.optimize_over_op0var0 &&
	 i < gop_conn[op0].num_eff ) {
      /* had success already!
       */
      break;
    }

  } /* ind0, op0 over selection of op0 in rplan for s */

  if ( nolm ) {
    gsuccess = TRUE;
  }

  if ( max_ed_bound ) {
    ged_bound = ed_bound;
  }

/*   printf("\nsome State in oDG+: "); */
/*   for ( i = 0; i < gnum_variables; i++ ) { */
/*     print_Variable(i); */
/*     printf(": "); */
/*     print_Variable_Value(i, ls_on_var[i], FALSE); */
/*     printf("\n       "); */
/*   } */
/*   printf("\n... and now in copied FF version: "); */
/*   print_state(ls); */
/*   printf("\n... and now in original FF version: "); */
/*   print_state(*s); */
/*   printf("\n"); */

/*   if ( nolm ) { */
/*     if ( !max_ed_bound ) { */
/*       printf("\n!max_ed_bound??\n\n"); */
/*       exit(1); */
/*     } */
/*     printf("\n\n========================oDGplus LOCAL ANALYSIS: no lm, ed bound %d.",  */
/* 	   ed_bound); */
/*     printf("\n                        Responsible operator: "); */
/*     print_op_name( responsible_op0 ); */
/*     printf("\nState: "); */
/*     for ( i = 0; i < gnum_variables; i++ ) { */
/*       print_Variable(i); */
/*       printf(": "); */
/*       print_Variable_Value(i, ls_on_var[i], FALSE); */
/*       printf("\n       "); */
/*     } */
/*     printf("\n"); */
/*   } */

}
























/**********************
 * simple manipulations of relaxed plans
 **********************/



















void reorder_Pplus_of_s( int ind0 )

{

  static int *trial;
  static Bool fc = TRUE;

  int num_trial;
  int current_ind0;
  int current_candidate;
  int i;

  
  if ( fc ) {
    trial = ( int * ) calloc( gnum_op_conn, sizeof( int ));
    fc = FALSE;
  }



  /* initialize re-ordered rplan to original rplan
   */
  for ( i = 0; i < lnum_Pplus_of_s; i++ ) {
    lreordered_Pplus_of_s[i] = lPplus_of_s[i];
  }
  lreordered_num_Pplus_of_s = lnum_Pplus_of_s;



  /* now try, from ind0 backwards, to move ops after ind0.
   */
  current_ind0 = ind0;
  current_candidate = ind0 - 1;
  while ( current_candidate >= 0 ) {

    /* put current_candidate directly behind current_ind0
     */
    num_trial = 0;
    for ( i = 0; i < current_candidate; i++ ) {
      trial[num_trial] = lreordered_Pplus_of_s[i];
      num_trial++;
    }
    for ( i = current_candidate + 1; i <= current_ind0; i++ ) {
      trial[num_trial] = lreordered_Pplus_of_s[i];
      num_trial++;
    }
    trial[num_trial] = lreordered_Pplus_of_s[current_candidate];
    num_trial++;
    for ( i = current_ind0 + 1; i < lreordered_num_Pplus_of_s; i++ ) {
      trial[num_trial] = lreordered_Pplus_of_s[i];
      num_trial++;
    }
    if ( num_trial != lreordered_num_Pplus_of_s ) {
      printf("\nnum_trial != lreordered_num_Pplus_of_s??\n\n");
      exit( 1 );
    }
    
    /* is this still a relaxed plan?
     */
    if ( is_relaxed_plan_for_s( trial, num_trial ) ) {
      /* simply copy over...
       */
      for ( i = 0; i < num_trial; i++ ) {
	lreordered_Pplus_of_s[i] = trial[i];
      }
      lreordered_num_Pplus_of_s = num_trial;
      /* ... and say what are new candidate and ind0 are.
       */
      current_ind0--; /* op0 is now one position further below */
      current_candidate--; /* try the next op below */
    } else {
      /* discard trial, and just note that we now try the next op
       * below
       */
      current_candidate--;
    }
  }

  lreordered_ind0 = current_ind0;

}



Bool is_relaxed_plan_for_s( int *trial, int num_trial ) 

{

  static Bool *in_rstate;
  static int *rstate;
  static Bool fc = TRUE;

  int i, j, op, ef;
  int num_rstate = 0;

  if ( fc ) {
    in_rstate = ( Bool * ) calloc( gnum_ft_conn, sizeof( int ));
    rstate = ( int * ) calloc( gnum_ft_conn, sizeof( int ));
    for ( i = 0; i < gnum_ft_conn; i++ ) {
      in_rstate[i] = FALSE;
    }
    fc = FALSE;
  }

  /* initialize with s
   */
  for ( i = 0; i < ls.num_F; i++ ) {
    in_rstate[ls.F[i]] = TRUE;
    rstate[i] = ls.F[i];
  }
  num_rstate = ls.num_F;
     
  /* now loop through the ops
   */
  for ( i = 0; i < num_trial; i++ ) {
    op = trial[i];
    if ( gop_conn[op].num_E == 0 ) {
      printf("\nBALLO gop_conn[op].num_E == 0??\n\n");
      exit(1);
    }
    ef = gop_conn[op].E[0];

    /* check preconds
     */
    for ( j = 0; j < gef_conn[ef].num_PC; j++ ) {
      if ( !in_rstate[gef_conn[ef].PC[j]] ) {
	/* precond not satisfied!
	 */
	for ( i = 0; i < num_rstate; i++ ) {
	  in_rstate[rstate[i]] = FALSE;
	}
	return FALSE;
      }
    }
    
    /* Ok. Include new adds.
     */
    for ( j = 0; j < gef_conn[ef].num_A; j++ ) {
      if ( !in_rstate[gef_conn[ef].A[j]] ) {
	in_rstate[gef_conn[ef].A[j]] = TRUE;
	rstate[num_rstate++] = gef_conn[ef].A[j];
      }
    }
  }

  /* check if goal is true at end
   */
  for ( i = 0; i < ggoal_state.num_F; i++ ) {
    if ( !in_rstate[ggoal_state.F[i]] ) {
      /* goal not satisfied!
       */
      for ( i = 0; i < num_rstate; i++ ) {
	in_rstate[rstate[i]] = FALSE;
      }
      return FALSE;
    }
  }

  for ( i = 0; i < num_rstate; i++ ) {
    in_rstate[rstate[i]] = FALSE;
  }
  return TRUE;

}

























/**********************
 * oDG+ construction
 **********************/




















Bool construct_oDGplus( int op0, int var0, DTGTransition *t0 )

{

  static Bool fc = TRUE;
  static SGNode_pointer *IN_SGnodes;
  static int *IN_SGedge_pres;
  static int *IN_SGedge_effs;
  static DTGNode_pointer *IN_DTGnodes;
  static DTGTransition_pointer *IN_DTGtransitions;
  static int num_IN_SGnodes;
  static int num_IN_SGedges;
  static int num_IN_DTGnodes;
  static int num_IN_DTGtransitions;

  int count;

  int i, j, k;
  int current_ind, current_op;
  int effvar, prevar, preval;
  SGNode *prenode;
  int effvar_startval, effvar_endval;
  Bool result;
  DTGTransition *t;
  Bool found_relevant_t;



  if ( fc ) {
    IN_SGnodes = ( SGNode_pointer * ) calloc( gSG.num_nodes, sizeof( SGNode_pointer ) );
    IN_SGedge_pres = ( int * ) calloc( gSG.num_edges, sizeof( int ) );
    IN_SGedge_effs = ( int * ) calloc( gSG.num_edges, sizeof( int ) );
    num_IN_SGnodes = 0;
    num_IN_SGedges = 0;
    for ( i = 0; i < gSG.num_nodes; i++ ) {
      gSG.nodes[i].IN = FALSE;
    }
    for ( i = 0; i < gSG.num_edges; i++ ) {
      gSG.IN_adj_matrix[gSG.edges[i].start->var][gSG.edges[i].end->var] = FALSE; 
    }

    count = 0;
    for (  i = 0; i < gnum_variables; i++ ) {
      count += gDTGs[i].num_nodes;
    }
    IN_DTGnodes = ( DTGNode_pointer * ) calloc( count, sizeof( DTGNode_pointer ) );
    count = 0;
    for (  i = 0; i < gnum_variables; i++ ) {
      count += gDTGs[i].num_transitions;
    }
    IN_DTGtransitions = ( DTGTransition_pointer * ) calloc( count, sizeof( DTGTransition_pointer ) );
    num_IN_DTGnodes = 0;
    num_IN_DTGtransitions = 0;
    for ( i = 0; i < gnum_variables; i++ ) {
      for ( j = 0; j < gDTGs[i].num_nodes; j++ ) {
	gDTGs[i].nodes[j].IN = FALSE;
      }
      for ( j = 0; j < gDTGs[i].num_transitions; j++ ) {
	gDTGs[i].transitions[j].IN = FALSE;
	gDTGs[i].transitions[j].induced = FALSE;
      }
    }

    fc = FALSE;
  }



  if ( gcmd_line.display_info == 2 ) {
    printf("\noDG+: ");
  }


/*   if ( 1 ) { */
/*     printf("\n===================================start oDG+"); */
/*   } */


  /* before we do anything: undo information from previous time.
   *
   * NOTE: this is outdated in the one case of the first call for the
   * sampling states -- the "previous time" then was ini state
   * analysis, and IN BETWEEN the lDG sample analysis has changed all
   * this. To take care of this case, oDG sample state analysis (see
   * end of this file) first unsets all the IN data here. The
   * unsetting here will not do anything in this case so there is no
   * need to catch the case here.
   */
  for ( i = 0; i < num_IN_SGnodes; i++ ) {
    IN_SGnodes[i]->IN = FALSE;
/*     if ( 1 ) { */
/*       printf("\nunsetting %d", IN_SGnodes[i]->var); */
/*     } */
  }
  num_IN_SGnodes = 0;
  for ( i = 0; i < num_IN_SGedges; i++ ) {
    gSG.IN_adj_matrix[IN_SGedge_pres[i]][IN_SGedge_effs[i]] = FALSE; 
  }
  num_IN_SGedges = 0;

  for ( i = 0; i < num_IN_DTGnodes; i++ ) {
    IN_DTGnodes[i]->IN = FALSE;
  }  
  num_IN_DTGnodes = 0;
  for ( i = 0; i < num_IN_DTGtransitions; i++ ) {
    IN_DTGtransitions[i]->IN = FALSE;
    IN_DTGtransitions[i]->induced = FALSE;
  }  
  num_IN_DTGtransitions = 0;
/*   /\* initialization: everything is out in SG... */
/*    *\/ */
/*   for ( i = 0; i < gSG.num_nodes; i++ ) { */
/*     gSG.nodes[i].IN = FALSE; */
/* /\*     for ( j = 0; j < gSG.num_nodes; j++ ) { *\/ */
/* /\*       gSG.IN_adj_matrix[i][j] = FALSE; *\/ */
/* /\*     } *\/ */
/*   } */
/*   for ( i = 0; i < gSG.num_edges; i++ ) { */
/*     gSG.edges[i].IN = FALSE; */
/*     gSG.IN_adj_matrix[gSG.edges[i].start->var][gSG.edges[i].end->var] = FALSE;  */
/*   } */
/*   /\* ... end everything is out in every DTG! */
/*    *\/ */
/*   for ( i = 0; i < gnum_variables; i++ ) { */
/*     for ( j = 0; j < gDTGs[i].num_nodes; j++ ) { */
/*       gDTGs[i].nodes[j].IN = FALSE; */
/*     } */
/*     for ( j = 0; j < gDTGs[i].num_transitions; j++ ) { */
/*       gDTGs[i].transitions[j].IN = FALSE; */
/*       gDTGs[i].transitions[j].induced = FALSE; */
/*     } */
/*   } */

/*   for ( i = 0; i < gSG.num_nodes; i++ ) { */
/*     if ( gSG.nodes[i].IN ) { */
/*       printf("\n\nmamamama1: %d\n\n", i); */
/*       exit(1); */
/*     } */
/*   } */
/*   for ( i = 0; i < gSG.num_edges; i++ ) { */
/*     if ( gSG.IN_adj_matrix[gSG.edges[i].start->var][gSG.edges[i].end->var] ) { */
/*       printf("\n\nmamamama3\n\n"); */
/*       exit(1); */
/*     } */
/*   } */
/*   for ( i = 0; i < gnum_variables; i++ ) { */
/*     for ( j = 0; j < gDTGs[i].num_nodes; j++ ) { */
/*       if ( gDTGs[i].nodes[j].IN ) { */
/* 	printf("\n\nmamamama4\n\n"); */
/* 	exit(1); */
/*       } */
/*     } */
/*     for ( j = 0; j < gDTGs[i].num_transitions; j++ ) { */
/*       if ( gDTGs[i].transitions[j].IN ) { */
/* 	printf("\n\nmamamama5\n\n"); */
/* 	exit(1); */
/*       } */
/*       if ( gDTGs[i].transitions[j].induced ) { */
/* 	printf("\n\nmamamama6\n\n"); */
/* 	exit(1); */
/*       } */
/*     } */
/*   } */


  /* the start variable is in.
   */
  gSG.nodes[var0].IN = TRUE;
/*   if ( 1 ) { */
/*     printf("\nsetting %d", var0); */
/*   } */
  IN_SGnodes[num_IN_SGnodes++] = &(gSG.nodes[var0]);
  if ( gcmd_line.display_info == 2 ) {
    printf("\nvar0: ");
    print_Variable(var0);
  }
  


  /* now simply go backwards from (re-ordered) op0, and include v and
   * (v,v') whenever v' is already IN, and op has eff on v' and
   * non-s-sat precond on v. 
   *
   * Note: right now, var0 is the only var that's IN, so this
   * procedure does the right thing also for op0 itself so we start
   * the backchaining right there. BUT take care: while adding new
   * vars due to op0, we set new IN markers, and if op0 affects one of
   * these then we may mistakenly insert SG arcs for them. So, need to
   * exclude this special case.
   *
   * Note also: it's important we do this backwards -- to make sure
   * that v' is already in when we get to op.
   */
  for ( current_ind = lreordered_ind0; current_ind >= 0; current_ind-- ) {
    current_op = lreordered_Pplus_of_s[current_ind];

    /* loop through all v' that are already IN and that are in eff
     */
    for ( i = 0; i < gop_conn[current_op].num_eff; i++ ) {
      effvar = gop_conn[current_op].eff[i].var;
      effvar_endval = gop_conn[current_op].eff[i].val;

      if ( !gSG.nodes[effvar].IN ) {
	continue;
      }

      if ( current_op == op0 && effvar != var0 ) {
	continue;
      }

      /* for non-op0 ops, only record pDG+ arcs/DTG+ values&transitions for non-var0 vars...
       * 
       * (note: if this guy affects *only* var0 then it won't be here
       * anyhow)
       */
      if ( current_op != op0 && effvar == var0 ) {
	continue;
      }

      /* insert the relevant DTG_effvar transitions taken by
       * current_op != op0, plus, of each, the inverse if present.
       */
      if ( current_op != op0 ) {
	found_relevant_t = FALSE;
	for ( j = 0; j < gop_conn[current_op].num_eff_DTG_transitions[i]; j++ ) {
	  t = gop_conn[current_op].eff_DTG_transitions[i][j];
	  if ( t->rop != current_op ) {
	    printf("\nt->rop != current_op in loop over op transitions for oDG construct??\n\n");
	    exit(1);
	  }
	  if ( t->end->val != effvar_endval ) {
	    printf("\nt->end->val != effvar_endval in loop over op transitions for oDG construc??\n\n");
	    exit(1);
	  }
	  if ( t->irrelevant ) {
	    continue;
	  }
	  effvar_startval = t->start->val;
	  if ( gcmd_line.display_info == 2 ) {
	    printf("\noDTG+ of ");
	    print_Variable(effvar);
	    printf(": due to ");
	    print_op_name(current_op);
	    printf(" we have ");
	    print_Variable_Value(effvar, effvar_startval, FALSE);
	    printf(" ---> ");
	    print_Variable_Value(effvar, effvar_endval, FALSE);
	  }	
	  found_relevant_t = TRUE;
	  if ( !t->IN ) {
	    t->IN = TRUE;
	    IN_DTGtransitions[num_IN_DTGtransitions++] = t;
	  }
	  if ( !t->start->IN ) {
	    t->start->IN = TRUE;
	    IN_DTGnodes[num_IN_DTGnodes++] = t->start;
	  }
	  if ( !t->end->IN ) {
	    t->end->IN = TRUE;
	    IN_DTGnodes[num_IN_DTGnodes++] = t->end;
	  }

	  /* Joerg2014: Commented this test out as it will dilute our
	     statistics: we want stats why oDGplus failed, and this
	     function here is supposed to say "fail" iff there is a
	     cycle.
	  */
	  /* /\* will this t definitely break the non-leaf conditions? */
	  /*  * (simple sufficient test, do full test later since then */
	  /*  * we'll know exactly who is invertible and who is */
	  /*  * induced...) */
	  /*  *\/ */
	  /* if ( !(t->irrelevant_own_delete && t->self_irrelevant_side_effect_deletes) && */
	  /*      !t->irrelevant_side_effect_deletes ) { */
	  /*   /\* yep this is BAD. stop right here. */
	  /*    *\/ */
	  /*   if ( gcmd_line.display_info == 2 ) { */
	  /*     printf("\nbad nonleaf oDTG+ transition!"); */
	  /*   } */
	  /*   return FALSE; */
	  /* } */

	  if ( t->invertible &&
	       !t->inverted_by->irrelevant ) {
	    if ( gcmd_line.display_info == 2 ) {
	      printf("\noDTG+ of ");
	      print_Variable(effvar);
	      printf(": due to inverse for ");
	      print_op_name(current_op);
	      printf(" we have ");
	      print_Variable_Value(effvar, effvar_endval, FALSE);
	      printf(" ---> ");
	      print_Variable_Value(effvar, effvar_startval, FALSE);
	    }
	    if ( !t->inverted_by->IN ) {
	      t->inverted_by->IN = TRUE;
	      IN_DTGtransitions[num_IN_DTGtransitions++] = t->inverted_by;
	    }
	    if ( !t->inverted_by->induced ) {
	      t->inverted_by->induced = TRUE;
	    }

	    /* Joerg2014: Commented this test out as it will dilute our
	       statistics: we want stats why oDGplus failed, and this
	       function here is supposed to say "fail" iff there is a
	       cycle.
	    */
	    /* /\* does t->inverted_by definitely break the non-leaf conditions? */
	    /*  *\/ */
	    /* if ( !(t->inverted_by->irrelevant_own_delete && t->inverted_by->self_irrelevant_side_effect_deletes) && */
	    /* 	 !t->inverted_by->irrelevant_side_effect_deletes ) { */
	    /*   /\* yep this is BAD. stop right here. */
	    /*    *\/ */
	    /*   if ( gcmd_line.display_info == 2 ) { */
	    /* 	printf("\nbad nonleaf oDTG+ transition!"); */
	    /*   } */
	    /*   return FALSE; */
	    /* } */

	  } /* endif t has relevant inverse transition */
	} /* endfor j, t over transitions made by op due to this effect */
      } else {/* endif current_op != op0 thus oDTG+ transitions needed */
	found_relevant_t = TRUE; /* t0 itself is relevant */
      }

      /* now, if this guy actually takes a relevant transition,
       * include all non-s-sat outside precond vars
       */

      if ( !found_relevant_t ) {
	continue;
      }

      for ( j = 0; j < gop_conn[current_op].num_pre; j++ ) {
	prevar = gop_conn[current_op].pre[j].var;
	if ( prevar == effvar ) {
	  continue;
	}
	preval = gop_conn[current_op].pre[j].val;

	if ( ls_on_var[prevar] == preval ) {
	  /* this prec is satisfied in s, no need to worry about it!
	   */
	  continue;
	}

	/* mark the var and the SG arc as IN.
	 */
	if ( gcmd_line.display_info == 2 ) {
	  printf("\noDG+: due to ");
	  print_op_name(current_op);
	  printf(" we have ");
	  print_Variable(prevar);
	  printf(" ===> ");
	  print_Variable(effvar);
	}
	prenode = &(gSG.nodes[prevar]);
	if ( !prenode->IN ) {
	  prenode->IN = TRUE;
/* 	  if ( 1 ) { */
/* 	    printf("\nsetting %d", prenode->var); */
/* 	  } */
	  IN_SGnodes[num_IN_SGnodes++] = prenode;
	}
	if ( !gSG.IN_adj_matrix[prevar][effvar] ) {
	  gSG.IN_adj_matrix[prevar][effvar] = TRUE;
	  IN_SGedge_pres[num_IN_SGedges] = prevar;
	  IN_SGedge_effs[num_IN_SGedges++] = effvar;
	}
/* 	for ( k = 0; k < prenode->num_succ; k++ ) { */
/* 	  if ( prenode->succ[k]->end->var == effvar ) { */
/* 	    break; */
/* 	  } */
/* 	} */
/* 	if ( k == prenode->num_succ ) { */
/* 	  printf("\noDG+: k == prenode->num_succ??\n\n"); */
/* 	  exit(1); */
/* 	} */
/* 	if ( !prenode->succ[k]->IN ) { */
/* 	  prenode->succ[k]->IN = TRUE; */
/* 	  IN_SGnodes[num_IN_SGnodes++] = prenode->succ[k]; */
/* 	} */

      } /* endfor j, prevar, preval over preconds */

    } /* endfor i, effvar over IN effs */

  } /* endfor current_ind, current_op backwards from op0 */



  /* December 2011 de-BUG: if, for op effect on x', pre(op)(x)=s(x)
   * but x is a non-var0 var we already collected, then the value of x
   * may change during exit path construction, and therefore we need
   * to record the dependency (x,x')! Simply do so using a second
   * pass. 
   *
   * Note that this does neither increase the set of vars, nor is
   * there a need to include additional DTG transitions -- s(x) is of
   * course part of DTG+ already, along with the transitions leaving
   * it, and inverses thereof if present.
   */
  for ( current_ind = lreordered_ind0; current_ind >= 0; current_ind-- ) {
    current_op = lreordered_Pplus_of_s[current_ind];

    for ( i = 0; i < gop_conn[current_op].num_eff; i++ ) {
      effvar = gop_conn[current_op].eff[i].var;
      effvar_endval = gop_conn[current_op].eff[i].val;

      if ( !gSG.nodes[effvar].IN ) {
	continue;
      }

      if ( current_op == op0 && effvar != var0 ) {
	continue;
      }

      if ( current_op != op0 && effvar == var0 ) {
	continue;
      }

      if ( current_op != op0 ) {
	found_relevant_t = FALSE;
	for ( j = 0; j < gop_conn[current_op].num_eff_DTG_transitions[i]; j++ ) {
	  t = gop_conn[current_op].eff_DTG_transitions[i][j];
	  if ( t->irrelevant ) {
	    continue;
	  }
	  found_relevant_t = TRUE;
	  break;
	}
      } else {
	found_relevant_t = TRUE;
      }
      if ( !found_relevant_t ) {
	continue;
      }

      for ( j = 0; j < gop_conn[current_op].num_pre; j++ ) {
	prevar = gop_conn[current_op].pre[j].var;
	if ( prevar == effvar ) {
	  continue;
	}

	preval = gop_conn[current_op].pre[j].val;
	if ( ls_on_var[prevar] != preval ) {
	  /* if a dependency arises here, then it was recorded above already.
	   */
	  continue;
	}

	/* var0 will not be moved during exit path construction, so we
	 * can rely on its value in s with no issue
	 */
	if ( prevar == var0 ) {
	  continue;
	}

	/* if the prevar is not part of the graph at all, we also rely
	 * on its value in s
	 */
	if ( !gSG.nodes[prevar].IN ) {
	  continue;
	}

	/* prevar is not var0, and is true in s but may be moved
	 * during exit path! record dependency for effvar!
	 */
	if ( gcmd_line.display_info == 2 ) {
	  printf("\noDG+ de-BUG true-in-s-dependencies: due to ");
	  print_op_name(current_op);
	  printf(" we have ");
	  print_Variable(prevar);
	  printf(" ===> ");
	  print_Variable(effvar);
	}
	if ( !gSG.IN_adj_matrix[prevar][effvar] ) {
	  /* if ( 1 ) { */
	  /*   printf("\noDG+ de-BUG true-in-s-dependencies added arc!"); */
	  /* } */
	  gSG.IN_adj_matrix[prevar][effvar] = TRUE;
	  IN_SGedge_pres[num_IN_SGedges] = prevar;
	  IN_SGedge_effs[num_IN_SGedges++] = effvar;
	}

      } /* endfor j, prevar, preval over preconds */

    } /* endfor i, effvar over IN effs */

  } /* endfor current_ind, current_op backwards from op0 */

  result = SG_INsubgraph_acyclic();

  if ( gcmd_line.display_info == 2 ) {
    printf("\nAcyclic? %d", result);
  }

  return result;

}























/**********************
 * op0, var0, t0 qualification
 **********************/





















/* DEFs:
 *
\begin{enumerate}[(a)]
\item the $P^+(s)$-relevant deletes of $(s(\var_0),c)$ are
  $P^+(s)$-recoverable on $V \setminus \{\var_0\}$; or
\item $s(\var_0) \not \in R_{\neq 0}(P^+(s))$, and the transition
  $(s(\var_0),c)$ has irrelevant side effects and recoverable side
  effect deletes.
\item $s(\var_0) \not \in R_{\neq 0}(P^+(s))$, and the transition
  $(s(\var_0),c)$ has replacable side effect deletes.
\end{enumerate}
*
*
If $\op_0 \in P^+(s)$, then by $F_{<0}(P^+(s)) := s \cup \bigcup_{\op
\in P^+_{<0}(s)} \eff_\op$ we denote the set of facts true after the
relaxed execution of $P^+_{<0}(s)$ in $s$.
*
*
If $\op_0 \in P^+(s)$, then by $R_{\neq 0}(P^+(s))$ we denote the
union of $\goal$, the precondition of any $\op_0 \neq \op \in
P^+(s)$, and the precondition of any $\op$ which is the responsible
operator for the inverse of a transition taken by an operator $\op'
\in P^+_{<0}(s)$ -- these will be the facts needed by the relaxed
plan and adaptations thereof.
*
*
If $\op_0 \in P^+(s)$ and $V \subseteq \vars$, then by $S_{\geq
  0}(P^+(s),V)$ we denote the union of: $\prevail_{\op_0} \cup
  \eff_{\op_0}$; $\{(x,c) \mid (x,c) \in F_{<0}(P^+(s)), x \in (V
  \setminus \{var0\})\}$ if $\vars_{\eff_{\op_0}} \cap (V \setminus
  \{var0\}) = \emptyset$, else $\emptyset$; and the set of facts
  $(x,c) \in s$ where there exists no $\op$ such that $x \in
  \vars_{\eff_\op}$ and $\op$ is either $\op_0$ or in $P^+_{<0}(s)$ or
  is the responsible operator for the inverse of a transition taken by
  an operator $\op' \in P^+_{<0}(s)$.\footnote{Here, actually, we can
  look only at the $\orpdtg$ transitions on $V$, rather than all
  operators in $P^+_{<0}(s)$. I'll use this in the implementation. For
  presentation here it's a bit awkward. \todo{Maybe
  re-evaluate/re-write when writing up paper.}}
*
*
The {\em $P^+(s)$-relevant deletes of $(s(\var_0),c)$ are
  $P^+(s)$-recoverable on $V$} iff $P^+_{>0}(s)$ contains^1 a
  sub-sequence $\mypath{\op_0}$ so that $\pre^+_{\mypath{\op_0}}
  \subseteq S_{\geq 0}(P^+(s),V)$ and $\eff^+_{\mypath{\op_0}}
  \supseteq (\context(s(\var_0),c) \cup \{(\var_0,s(\var_0))\}) \cap
  F_{<0}(P^+(s)) \cap R_{\neq 0}(P^+(s))$.
  *
1: From a theoretical point of view, we can choose
  $P^+_{>0}(s)$ to be ``ideal'' in the sense that, if any such optimal
  rplan for $s$ exists, then $P^+(s)$ is it. From a practical point of
  view, we'd need rplan re-writing methods trying to find a ``good
  one''. Example is in Transport where $\mypath{\op_0}$ may not exist
  simply because the rplan chose to use non-matching capacity
  constraints (reduce from 2 to 1 when loading but increase from 2 to
  3 when unloading).
*
* return value 1 == (a), 2 == (b), 3 == (c), -1 == none
*/
int op0_var0_t0_qualification( int op0, int var0, DTGTransition *t0 )

{

  static Bool fc = TRUE;
  static DTGNode_pointer *F_less0_Pplus_of_s;
  static Bool **in_F_less0_Pplus_of_s;
  static DTGNode_pointer *R_neq0_Pplus_of_s;
  static Bool **in_R_neq0_Pplus_of_s;
  static DTGNode_pointer *context_t0_plus_own;
  static Bool **in_context_t0_plus_own;
  static DTGNode_pointer *RFC_intersect;/* intersection of the above 3, needed for (a) */
  static Bool **in_RFC_intersect;

  static DTGNode_pointer *S_geq0_Pplus_of_s;
  static Bool **in_S_geq0_Pplus_of_s;
  /* helpers for suitable P+ sub-path identification in (a)
   */
  static int *have_varval;
  static Bool *is_have_varval;
  static Bool *RFC_intersect_re_added;

  int num_F_less0_Pplus_of_s;
  int num_R_neq0_Pplus_of_s;
  int num_context_t0_plus_own;
  int num_RFC_intersect;

  int num_S_geq0_Pplus_of_s;

  int num_have_varval;

  int i, j, k, l;
  int count;
  DTGNode *newDTGnode;
  int op, effvar, effval, prevar, preval;
  DTGTransition *t;
  int ft, op_prime, RFCind;
  Action *my_a;
  Operator *my_o;
  Bool failure;
  int haveft;
  int ef;
  Bool rplan_preserve;
  DTGNode *op0effDTGnode;

  int op0_prime;
  DTGTransition *t0_prime;
  int t0_prime_index;

  Bool replaced_one;

  int result = -1;

  int fttt, oppp, preddd;



  if ( fc ) {
    count = 0;
    for ( i = 0; i < gnum_variables; i++ ) {
      count += gvariables[i].num_vals;
    }

    F_less0_Pplus_of_s = ( DTGNode_pointer * )
      calloc( count, sizeof( DTGNode_pointer ));
    in_F_less0_Pplus_of_s = ( Bool ** ) calloc(gnum_variables, sizeof( Bool * ));
    for ( i = 0; i < gnum_variables; i++ ) {
      in_F_less0_Pplus_of_s[i] = ( Bool * ) calloc(gvariables[i].num_vals, sizeof( Bool ));
      for ( j = 0; j < gvariables[i].num_vals; j++ ) {
	in_F_less0_Pplus_of_s[i][j] = FALSE;
      }
    }
    
    R_neq0_Pplus_of_s = ( DTGNode_pointer * )
      calloc( count, sizeof( DTGNode_pointer ));
    in_R_neq0_Pplus_of_s = ( Bool ** ) calloc(gnum_variables, sizeof( Bool * ));
    for ( i = 0; i < gnum_variables; i++ ) {
      in_R_neq0_Pplus_of_s[i] = ( Bool * ) calloc(gvariables[i].num_vals, sizeof( Bool ));
      for ( j = 0; j < gvariables[i].num_vals; j++ ) {
	in_R_neq0_Pplus_of_s[i][j] = FALSE;
      }
    }
    
    context_t0_plus_own = ( DTGNode_pointer * )
      calloc( count, sizeof( DTGNode_pointer ));
    in_context_t0_plus_own = ( Bool ** ) calloc(gnum_variables, sizeof( Bool * ));
    for ( i = 0; i < gnum_variables; i++ ) {
      in_context_t0_plus_own[i] = ( Bool * ) calloc(gvariables[i].num_vals, sizeof( Bool ));
      for ( j = 0; j < gvariables[i].num_vals; j++ ) {
	in_context_t0_plus_own[i][j] = FALSE;
      }
    }
    
    RFC_intersect = ( DTGNode_pointer * )
      calloc( count, sizeof( DTGNode_pointer ));
    in_RFC_intersect = ( Bool ** ) calloc(gnum_variables, sizeof( Bool * ));
    for ( i = 0; i < gnum_variables; i++ ) {
      in_RFC_intersect[i] = ( Bool * ) calloc(gvariables[i].num_vals, sizeof( Bool ));
      for ( j = 0; j < gvariables[i].num_vals; j++ ) {
	in_RFC_intersect[i][j] = FALSE;
      }
    }
    
    S_geq0_Pplus_of_s = ( DTGNode_pointer * )
      calloc( count, sizeof( DTGNode_pointer ));
    in_S_geq0_Pplus_of_s = ( Bool ** ) calloc(gnum_variables, sizeof( Bool * ));
    for ( i = 0; i < gnum_variables; i++ ) {
      in_S_geq0_Pplus_of_s[i] = ( Bool * ) calloc(gvariables[i].num_vals, sizeof( Bool ));
      for ( j = 0; j < gvariables[i].num_vals; j++ ) {
	in_S_geq0_Pplus_of_s[i][j] = FALSE;
      }
    }
    
    have_varval = ( int * ) calloc( gnum_ft_conn, sizeof( int ));
    is_have_varval = ( Bool * ) calloc( gnum_ft_conn, sizeof( Bool ));
    for ( i = 0; i < gnum_ft_conn; i++ ) {
      is_have_varval[i] = FALSE;
    }

    RFC_intersect_re_added = ( Bool * )
      calloc( count, sizeof( DTGNode_pointer ));

    fc = FALSE;
  }

  for ( i = 0; i < gnum_variables; i++ ) {
    for ( j = 0; j < gvariables[i].num_vals; j++ ) {
      if ( in_F_less0_Pplus_of_s[i][j] ||
	   in_R_neq0_Pplus_of_s[i][j] ||
	   in_context_t0_plus_own[i][j] ||
	   in_RFC_intersect[i][j] ||
	   in_S_geq0_Pplus_of_s[i][j] ) {
	printf("\n???\n\n");
	exit(1);
      }
    }
  }
  for ( i = 0; i < gnum_ft_conn; i++ ) {
    if ( is_have_varval[i] ) {
      printf("\n?????\n\n");
      exit(1);
    }
  }


  /* First establish the necessary data. This is certainly not the
   * most effective implementation: we repeat effort if the same op0
   * has several var0, t0; the representation in terms of simple
   * arrays could probably be improved. As usual, emphasize for now
   * code simplicity and see about efficiency later on.
   */



  /* First we do R_{\neq 0}(P^+(s)):
   *
   If $\op_0 \in P^+(s)$, then by $R_{\neq 0}(P^+(s))$ we denote the
   union of $\goal$, the precondition of any $\op_0 \neq \op \in
   P^+(s)$, and the precondition of any $\op$ which is the responsible
   operator for the inverse of a transition taken by an operator $\op'
   \in P^+_{<0}(s)$ -- these will be the facts needed by the relaxed
   plan and adaptations thereof.
   *
   *
   * start by simply collecting all P+(s) preconds except that of op0.
   */
  num_R_neq0_Pplus_of_s = 0;
  for ( i = 0; i < lreordered_num_Pplus_of_s; i++ ) {
    if ( i == lreordered_ind0 ) {
      continue;
    }
    op = lreordered_Pplus_of_s[i];
    
    for ( j = 0; j < gop_conn[op].num_pre; j++ ) {
      prevar = gop_conn[op].pre[j].var;
      preval = gop_conn[op].pre[j].val;
      newDTGnode = &(gDTGs[prevar].nodes[preval]);

      /* duplicate check... not strictly needed I guess...
       */
      if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
	R_neq0_Pplus_of_s[num_R_neq0_Pplus_of_s] = newDTGnode;
	in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
	num_R_neq0_Pplus_of_s++;
      }
    }
  }
  /* now add the goal into this.
   */
  for ( i = 0; i < gnum_variables; i++ ) {
    if ( ggoal_on_var[i] == -1 ) {
      continue;
    }
    newDTGnode = &(gDTGs[i].nodes[ggoal_on_var[i]]);

    if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
      R_neq0_Pplus_of_s[num_R_neq0_Pplus_of_s] = newDTGnode;
      in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
      num_R_neq0_Pplus_of_s++;
    }
  }
  /* finally, add any additional conditions needed for inverse
   * transitions. NOTE that such conditions pertain ONLY to the own
   * condition of a transition that is induced. So we can simply go
   * through the DTGs and collect the start point of all
   * IN-and-induced transitions.
   *
   * Note: here it doesn't matter if an invertible transition is also
   * marked as induced: the condition will then be in anyhow. It can,
   * however, matter if an irrdel transition has sparked an
   * unnecessarily induced transition -- the start cond of that
   * transition may be new. We do not currently catch this.
   */
  for ( i = 0; i < gSG.num_nodes; i++ ) {
    if ( !gSG.nodes[i].IN ) {
      continue;
    }
    if ( i == var0 ) {
      continue;
    }
    for ( j = 0; j < gDTGs[i].num_transitions; j++ ) {
      t = &(gDTGs[i].transitions[j]);
      if ( !t->IN ) {
	continue;
      }
      if ( !t->induced ) {
	continue;
      }
      newDTGnode = t->start;
      
      if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
	R_neq0_Pplus_of_s[num_R_neq0_Pplus_of_s] = newDTGnode;
	in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
	num_R_neq0_Pplus_of_s++;
      }
    }
  }
  if ( gcmd_line.display_info == 2 ) {
    printf("\nR_{neq 0}(P^+(s)): ");
    for ( i = 0; i < num_R_neq0_Pplus_of_s; i++ ) {
      print_Variable_Value(R_neq0_Pplus_of_s[i]->var, 
			   R_neq0_Pplus_of_s[i]->val,
			   TRUE);
      printf("; ");
    }
  }



  /* we can now already easily test a simple variant of (a): if
   * $s(\var_0) \not \in R_{\neq 0}(P^+(s))$ and the transition has
   * irrelevant side effect deletes (except perhaps for op0 itself),
   * then \context(s(\var_0),c) \cup \{(\var_0,s(\var_0))\} will have
   * an empty intersection with R_{\neq 0}(P^+(s)).
   */
  newDTGnode = &(gDTGs[var0].nodes[ls_on_var[var0]]);
  if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
    if ( t0->self_irrelevant_side_effect_deletes ) {
      if ( gcmd_line.display_info == 2 ) {
	printf("\ncriterion (2a) applies!");
      }
      result = 1;
      goDGplus_num_succ_t0adequateRFCempty++; /* Joerg2014: new feature */

      /* this will already give the best possible bound. undo booleans
       * made so far, and return.
       */
      for ( i = 0; i < num_R_neq0_Pplus_of_s; i++ ) {
	newDTGnode = R_neq0_Pplus_of_s[i];
	in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
      }

      return result;
    }
  }

  /* same goes for (c):
   *
\item $s(\var_0) \not \in R_{\neq 0}(P^+(s))$, and the transition
  $(s(\var_0),c)$ has replacable side effect deletes.
  *
  */
  newDTGnode = &(gDTGs[var0].nodes[ls_on_var[var0]]);
  if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
    if ( t0->replacable_side_effect_deletes ) {
      if ( gcmd_line.display_info == 2 ) {
	printf("\ncriterion (2c) applies!");
      }
      result = 3;

      /* this will already give the best possible bound. undo booleans
       * made so far, and return.
       */
      for ( i = 0; i < num_R_neq0_Pplus_of_s; i++ ) {
	newDTGnode = R_neq0_Pplus_of_s[i];
	in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
      }

      return result;
    }
  }
  


  /* same goes for (b): 
   *
\item $s(\var_0) \not \in R_{\neq 0}(P^+(s))$, and the transition
  $(s(\var_0),c)$ has irrelevant side effects and recoverable side
  effect deletes.
  *
  * respectively: has recoverer-only relevant side effects and
  recoverable side effect deletes.
  *
  */
  newDTGnode = &(gDTGs[var0].nodes[ls_on_var[var0]]);
  if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
    if ( !gcmd_line.do_recoverer_only_relevant ) {
      if ( t0->irrelevant_side_effects && t0->recoverable_side_effect_deletes ) {
	if ( gcmd_line.display_info == 2 ) {
	  printf("\ncriterion (2b) applies!");
	}
	result = 2;
	
	/* this will perhaps not give the best possible bound. anyway,
	 * +1 whatever, just go for it.
	 */
	for ( i = 0; i < num_R_neq0_Pplus_of_s; i++ ) {
	  newDTGnode = R_neq0_Pplus_of_s[i];
	  in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
	}
	
	return result;
      }
    } else {
      if ( t0->recoverer_only_relevant_side_effects && 
	   t0->recoverable_side_effect_deletes ) {
	if ( gcmd_line.display_info == 2 ) {
	  printf("\ncriterion (2b) applies!");
	}
	result = 2;
	for ( i = 0; i < num_R_neq0_Pplus_of_s; i++ ) {
	  newDTGnode = R_neq0_Pplus_of_s[i];
	  in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
	}
	
	return result;
      }
    }
  }



  /* Need to full test of (a). Need data. First do F_{<0}(P^+(s)):
   *
   If $\op_0 \in P^+(s)$, then by $F_{<0}(P^+(s)) := s \cup \bigcup_{\op
   \in P^+_{<0}(s)} \eff_\op$ we denote the set of facts true after the
   relaxed execution of $P^+_{<0}(s)$ in $s$.
   *
   */
  num_F_less0_Pplus_of_s = 0;
  for ( i = 0; i < gnum_variables; i++ ) {
    newDTGnode = &(gDTGs[i].nodes[ls_on_var[i]]);

    F_less0_Pplus_of_s[num_F_less0_Pplus_of_s] = newDTGnode;
    in_F_less0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
    num_F_less0_Pplus_of_s++;
  }
  for ( i = 0; i < lreordered_ind0; i++ ) {
    op = lreordered_Pplus_of_s[i];

    for ( j = 0; j < gop_conn[op].num_eff; j++ ) {
      effvar = gop_conn[op].eff[j].var;
      effval = gop_conn[op].eff[j].val;
      newDTGnode = &(gDTGs[effvar].nodes[effval]);

      /* duplicate check... not strictly needed I guess...
       */
      if ( !in_F_less0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
	F_less0_Pplus_of_s[num_F_less0_Pplus_of_s] = newDTGnode;
	in_F_less0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
	num_F_less0_Pplus_of_s++;
      }
    }
  }
  if ( gcmd_line.display_info == 2 ) {
    printf("\nF_{<0}(P^+(s)): ");
    for ( i = 0; i < num_F_less0_Pplus_of_s; i++ ) {
      print_Variable_Value(F_less0_Pplus_of_s[i]->var, 
			   F_less0_Pplus_of_s[i]->val,
			   TRUE);
      printf("; ");
    }
  }



  /* Now we do \context(s(\var_0),c) \cup \{(\var_0,s(\var_0))\}
   */
  num_context_t0_plus_own = 0;
  for ( i = 0; i < t0->num_contexts; i++ ) {
    for ( j = 0; j < t0->num_context[i]; j++ ) {
      newDTGnode = t0->context[i][j];
      if ( newDTGnode->var == var0 ) {
	printf("\nnewDTGnode->var == var0\n\n");
	exit(1);
      }
      /* no duplicates here -- diferent ctx vars, different ctx vals.
       */
      context_t0_plus_own[num_context_t0_plus_own] = newDTGnode;
      in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] = TRUE;
      num_context_t0_plus_own++;
    }
  }
  newDTGnode = &(gDTGs[var0].nodes[ls_on_var[var0]]);
  context_t0_plus_own[num_context_t0_plus_own] = newDTGnode;
  in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] = TRUE;
  num_context_t0_plus_own++;
  if ( gcmd_line.display_info == 2 ) {
    printf("\ncontext(s(var_0),c) cup {(var_0,s(var_0))}: ");
    for ( i = 0; i < num_context_t0_plus_own; i++ ) {
      print_Variable_Value(context_t0_plus_own[i]->var, 
			   context_t0_plus_own[i]->val,
			   TRUE);
      printf("; ");
    }
  }



  /* Next we compute the intersection of the three guys above.
   */
  num_RFC_intersect = 0;
  for ( i = 0; i < num_F_less0_Pplus_of_s; i++ ) {
    newDTGnode = F_less0_Pplus_of_s[i];

    if ( !in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] ) {
      continue;
    }

    if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
      continue;
    }

    RFC_intersect[num_RFC_intersect] = newDTGnode;
    in_RFC_intersect[newDTGnode->var][newDTGnode->val] = TRUE;
    num_RFC_intersect++;
  }
  if ( gcmd_line.display_info == 2 ) {
    printf("\nRFC_intersect: ");
    for ( i = 0; i < num_RFC_intersect; i++ ) {
      print_Variable_Value(RFC_intersect[i]->var, 
			   RFC_intersect[i]->val,
			   TRUE);
      printf("; ");
    }
  }



  /* now we go for test (a):
   *
   the $P^+(s)$-relevant deletes of $(s(\var_0),c)$ are
   $P^+(s)$-recoverable; or
   *
   The {\em $P^+(s)$-relevant deletes of $(s(\var_0),c)$ are
   $P^+(s)$-recoverable} iff $P^+_{>0}(s,\var)$ contains a sub-sequence
   $\mypath{\op_0}$ so that $\pre^+_{\mypath{\op_0}} \subseteq
   \prevail_{\op_0} \cup \eff_{\op_0}$ and $\eff^+_{\mypath{\op_0}}
   \supseteq (\context(s(\var_0),c) \cup \{(\var_0,s(\var_0))\}) \cap
   F_{<0}(P^+(s)) \cap R_{\neq 0}(P^+(s))$.
   *
   */

  /* a simple special case is that where RFC_intersect is actually
   * empty -- in which case the empty \mypath{\op_0} does the desired
   * job.
   */
  if ( num_RFC_intersect == 0 ) {
    if ( gcmd_line.display_info == 2 ) {
      printf("\ncriterion (2a) applies: empty RFC_intersect!");
    }
    result = 1;
    goDGplus_num_succ_t0adequateRFCempty++; /* Joerg2014: new feature */

    /* need to undo Booleans!
     */
    for ( i = 0; i < num_F_less0_Pplus_of_s; i++ ) {
      newDTGnode = F_less0_Pplus_of_s[i];
      in_F_less0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_R_neq0_Pplus_of_s; i++ ) {
      newDTGnode = R_neq0_Pplus_of_s[i];
      in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_context_t0_plus_own; i++ ) {
      newDTGnode = context_t0_plus_own[i];
      in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_RFC_intersect; i++ ) {
      newDTGnode = RFC_intersect[i];
      in_RFC_intersect[newDTGnode->var][newDTGnode->val] = FALSE;
    }

    return result;
  }



  /* RFC_intersect is non-empty. we need to test whether there is a
   * suitable \mypath{\op_0} recovering it.
   *
   * NOTE: we could actually post-process reordered rplan to increase
   * the likelihood that this works -- some ops might be repacable by
   * other ops that are "more applicable" and/or "more likely to
   * recover RFC_intersect". Example: Transport PICK-UP TRUCK-1
   * CITY-LOC-4 PACKAGE-1 CAPACITY-1 CAPACITY-2 is NOT recovered by
   * DROP TRUCK-1 CITY-LOC-5 PACKAGE-1 CAPACITY-2 CAPACITY-3 because
   * the capacities don't match. But we could just as well replace
   * DROP TRUCK-1 CITY-LOC-5 PACKAGE-1 CAPACITY-1
   * CAPACITY-2. 
   *
   * For now, we do the following HACK: if op is not applicable
   * but affects a var x that is in RFC_intersect and hasn't been
   * re-added yet, then we see whether there exists op' that
   * establishes the RFC_intersect value of x, that is applicable,
   * and where the rplan with op' instead of op is still an
   * rplan. If so, we consider op' to be in.
   */

  /* we use have_varval to record the facts we have at our disposal;
   * when going through P+(s) behind op0, we will then simply allow
   * any op whose pre is in here.
   *
   * we use RFC_intersect_re_added as a marker at each RFC_intersect
   * fact, recording whether it is in eff of any allowed op.
   *
   * To start, we need to compute S_geq0_Pplus_of_s now:
   *
If $\op_0 \in P^+(s)$ and $V \subseteq \vars$, then by $S_{\geq
  0}(P^+(s),V)$ we denote the union of: $\prevail_{\op_0} \cup
  \eff_{\op_0}$; $\{(x,c) \mid (x,c) \in F_{<0}(P^+(s)), x \in (V
  \setminus \{var0\})\}$ if $\vars_{\eff_{\op_0}} \cap (V \setminus
  \{var0\}) = \emptyset$, else $\emptyset$; and the set of facts
  $(x,c) \in s$ where there exists no $\op$ such that $x \in
  \vars_{\eff_\op}$ and $\op$ is either $\op_0$ or in $P^+_{<0}(s)$ or
  is the responsible operator for the inverse of a transition taken by
  an operator $\op' \in P^+_{<0}(s)$.\footnote{Here, actually, we can
  look only at the $\orpdtg$ transitions on $V$, rather than all
  operators in $P^+_{<0}(s)$. I'll use this in the implementation. For
  presentation here it's a bit awkward.
   *
   */

  /* first, $\prevail_{\op_0} \cup \eff_{\op_0}$
   */
  num_S_geq0_Pplus_of_s = 0;
  for ( i = 0; i < gnum_variables; i++ ) {
    if ( gop_conn[op0].pre_on_var[i] != -1 && 
	 gop_conn[op0].eff_on_var[i] == -1 ) {
      newDTGnode = &(gDTGs[i].nodes[gop_conn[op0].pre_on_var[i]]);
      S_geq0_Pplus_of_s[num_S_geq0_Pplus_of_s] = newDTGnode;
      in_S_geq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
      num_S_geq0_Pplus_of_s++;
    }
    if ( gop_conn[op0].eff_on_var[i] != -1 ) {
      newDTGnode = &(gDTGs[i].nodes[gop_conn[op0].eff_on_var[i]]);
      S_geq0_Pplus_of_s[num_S_geq0_Pplus_of_s] = newDTGnode;
      in_S_geq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
      num_S_geq0_Pplus_of_s++;
    }
  }
  
  /* second, the set of facts $(x,c) \in s$ where there exists no
   * oDTG+ transition t on a non-leaf var st x is affected by an (own
   * or side) effect of t, and where op0 does not affect x.
   *
   * VERY NAIVE implementation!
   */
  for ( i = 0; i < gnum_variables; i++ ) {
    if ( gSG.nodes[i].IN ) {
      /* this var is in oDG+ and therefore of course we don't count it
       * as preserved.
       */
      continue;
    }
    /* test whether op0 affects this guy.
     */
    if ( gop_conn[op0].eff_on_var[i] != -1 ) {
      continue;
    }
    /* test whether this var appears in any of the relevant
     * transitions.
     */
    for ( j = 0; j < gnum_variables; j++ ) {
      if ( j == var0 || !gSG.nodes[j].IN ) {
	continue;
      }
      for ( k = 0; k < gDTGs[j].num_transitions; k++ ) {
	t = &(gDTGs[j].transitions[k]);
	if ( !t->IN ) {
	  continue;
	}
	/* here we do a non-trivial pruning: we're only interested in
	 * invertible or induced transitions, since others won't be
	 * executed on our path.
	 */
	if ( !t->invertible && !t->induced ) {
	  continue;
	}
	/* j != i follows because i is not IN while j is. hence don't
	 * need to care about the own-effect.
	 */
	for ( l = 0; l < t->num_side_effects; l++ ) {
	  if ( t->side_effects[l]->var == i ) {
	    break;
	  }
	}
      }
      if ( k < gDTGs[j].num_transitions ) {
	/* found a bad transition!
	 */
	break;
      }
    }
    if ( j < gnum_variables ) {
      /* found a bad nonleaf var! try next variable in s.
       */
      continue;
    }
    /* do we already have this guy?
     */
    newDTGnode = &(gDTGs[i].nodes[ls_on_var[i]]);
    if ( !in_S_geq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
      S_geq0_Pplus_of_s[num_S_geq0_Pplus_of_s] = newDTGnode;
      in_S_geq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
      num_S_geq0_Pplus_of_s++;
    }
  } /* endif for i over all vars for fts true in s */

  /* third, is \vars_{\eff_{\op_0}} \cap (V \setminus \{var0\}) =
   * \emptyset?
   */
  for ( i = 0; i < gop_conn[op0].num_eff; i++ ) {
    if ( gop_conn[op0].eff[i].var != var0 &&
	 gSG.nodes[gop_conn[op0].eff[i].var].IN ) {
      break;
    }
  }
  if ( i == gop_conn[op0].num_eff ) {
    /* yes! add the set of facts $\{(x,c) \mid (x,c) \in
     * F_{<0}(P^+(s)), x \in (V \setminus \{var0\})\}$
     */
    for ( i = 0; i < num_F_less0_Pplus_of_s; i++ ) {
      newDTGnode = F_less0_Pplus_of_s[i];
      if ( newDTGnode->var != var0 && 
	   gSG.nodes[newDTGnode->var].IN ) {

	if ( !in_S_geq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
	  S_geq0_Pplus_of_s[num_S_geq0_Pplus_of_s] = newDTGnode;
	  in_S_geq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
	  num_S_geq0_Pplus_of_s++;
	}
      }
    }
  }
  if ( gcmd_line.display_info == 2 ) {
    printf("\nS_{>= 0}(P^+(s),V setminus {var0}): ");
    for ( i = 0; i < num_S_geq0_Pplus_of_s; i++ ) {
      print_Variable_Value(S_geq0_Pplus_of_s[i]->var, 
			   S_geq0_Pplus_of_s[i]->val,
			   TRUE);
      printf("; ");
    }
  }




  /* first go: no op replacement!
   */

  /* initialize RFC_intersect_re_added.
   */
  for ( i = 0; i < num_RFC_intersect; i++ ) {
    RFC_intersect_re_added[i] = FALSE;
  }

  /* initialize have_varval with S_geq0_Pplus_of_s
   */  
  num_have_varval = 0;
  for ( i = 0; i < num_S_geq0_Pplus_of_s; i++ ) {
    haveft = gvariables[S_geq0_Pplus_of_s[i]->var].vals[S_geq0_Pplus_of_s[i]->val];
    if ( haveft != -1 ) {
      have_varval[num_have_varval] = haveft;
      is_have_varval[haveft] = TRUE;
      num_have_varval++;
    }
  }

  /* now loop through the ops to the right hand side of op0!
   */
  for ( i = lreordered_ind0; i < lreordered_num_Pplus_of_s; i++ ) {
    op = lreordered_Pplus_of_s[i];

    /* is op allowed?
     */
    for ( j = 0; j < gop_conn[op].num_pre; j++ ) {
      haveft = gvariables[gop_conn[op].pre[j].var].vals[gop_conn[op].pre[j].val];
      if ( haveft == -1 ) {
	printf("\nft == -1??\n\n");
	exit(1);
      }
      if ( !is_have_varval[haveft] ) {
	break;
      }
    }
    if ( j < gop_conn[op].num_pre ) {
      continue;
    } /* endif op is not allowed */
  


    /* yep, we got this guy. add his eff to have_varval, and tick off
     * the re-added RFC_intersect.
     */
    for ( j = 0; j < gop_conn[op].num_eff; j++ ) {
      effvar = gop_conn[op].eff[j].var;
      effval = gop_conn[op].eff[j].val;
      newDTGnode = &(gDTGs[effvar].nodes[effval]);

      /* does this tick off a RFC_intersect?
       */
      for ( k = 0; k < num_RFC_intersect; k++ ) {
	if ( RFC_intersect[k] == newDTGnode ) {
	  RFC_intersect_re_added[k] = TRUE;
	  /* no duplicates so this ticks off only this guy and there's
	   * no need to continue
	   */
	  break;
	}
      }
      
      /* is this already in?
       */
      haveft = gvariables[effvar].vals[effval];
      if ( haveft != -1 && !is_have_varval[haveft] ) {
	have_varval[num_have_varval] = haveft;
	is_have_varval[haveft] = TRUE;
	num_have_varval++;
      }
    } /* endfor j, effvar/val over op effs */  

  } /* endfor i, op over ops to the right of op0 */



  /* now all we need to do, in order to check (a), is to see whether
   * all RFC_intersect facts have been ticked off.
   */
  failure = FALSE;
  for ( i = 0; i < num_RFC_intersect; i++ ) {
    if ( RFC_intersect_re_added[i] ) {
      continue;
    }

    failure = TRUE;
    
    if ( gcmd_line.replacement_level != 0 /* we're gonna analyze below */ ) {
      continue;
    }
    
    /* if this is var0, ie, the delete of t0, and if t0 is
     * invertible, then don't record it -- such a failure is just
     * because this is not what we should be doing, with this
     * var...
     */
    if ( RFC_intersect[i]->var == var0 && t0->invertible ) {
      continue;
    }
    
    fttt = gvariables[RFC_intersect[i]->var].vals[RFC_intersect[i]->val];
    /* if this guy is not a real fact then there's nothing we can record...
     */
    if ( fttt == -1 ) {
      continue;
    }
    
    /* if this is supposed to be a "side effect", but actually the
     * preds are "exchanged" -- every op having a positive effect on
     * one has a negative effect on the other -- then presume that
     * this is only FD not recognizing what is actually a multi-valued
     * variable, and don't record the bugger. Note here: FD sometimes
     * does not find obviously mutex facts, resulting in overly
     * fine-grained variables (eg separating "have" from "in-boot" in
     * tyreworld, and separating "power_avail" from "power_on" in
     * satellite), which results in diagnosis thinking that what is
     * actually simply a value change is a side-effect, thus
     * incorrectly diagnozing the side effect to be harmful (eg
     * "put-away, have" in tyreworld, "switch_on, power_avail" in
     * satellite). ... of course, the solution here is a HACK! (note
     * though that the real hack is PDDL, forcing us to express the
     * problem in an unnatural manner, resulting in imprecisions when
     * recovering its real structure automatically). what we would
     * really want is a stronger mutex detection technique, delivering
     * the correct variables at least in these simple cases.
     */
    if ( RFC_intersect[i]->var != var0 && gcmd_line.do_diagnose_ignore_exchangedvars ) {
      if ( gvariables[t0->end->var].vals[t0->end->val] != -1 &&
	   are_exchanged_predicates( grelevant_facts[fttt].predicate,
				     grelevant_facts[gvariables[t0->end->var].vals[t0->end->val]].predicate ) ) {
	continue;
      }
    }
    
    if ( RFC_intersect[i]->var == var0 && gcmd_line.do_diagnose_invertop0 ) {
      /* next test: if this is var0 and there exists op'
       *  recovering the delete, so that op' is definitely
       *  applicable in s1, then this own-delete is not the
       *  problem here...
       *
       * proceed by going over all adders of the deleted fact.
       */
      
      for ( j = 0; j < gft_conn[fttt].num_A; j++ ) {
	oppp =  gft_conn[fttt].A[j];
	if ( gop_conn[oppp].num_E == 0 ) {
	  /* this CAN happen! since we're going over ftconn here
	   * which does contain the empty-ops
	   */
	  continue;
	}
	for ( k = 0; k < gop_conn[oppp].num_pre; k++ ) {
	  if ( !in_S_geq0_Pplus_of_s[gop_conn[oppp].pre[k].var][gop_conn[oppp].pre[k].val] ) {
	    break;
	  }
	}
	if ( k == gop_conn[oppp].num_pre ) {
	  break;
	}
      }
      if ( j < gft_conn[fttt].num_A ) {
	/* yes! found such a guy!
	 */
	continue;
      }
    }
    
    /* Ok, record this bugger.
     */
    preddd = grelevant_facts[fttt].predicate;
    my_a = gop_conn[op0].action;
    if ( my_a->norm_operator ) {
      my_o = my_a->norm_operator->operator;
    } else {
      if ( my_a->pseudo_action ) {
	my_o = my_a->pseudo_action->operator;
      } else {
	printf("\nmy_a has neither norm op nor pseudo act??\n\n");
	exit(1);
      }
    }

    /* new version, with preds
     */
    for ( j = 0; j < goDGplus_num_nonrecovered_RFC_intersects; j++ ) {
      if ( goDGplus_nonrecovered_RFC_intersect_preds[j] == preddd &&
	   goperators[goDGplus_nonrecovered_RFC_intersect_op0s[j]] == my_o ) {
	break;
      }
    }
    if ( j == goDGplus_num_nonrecovered_RFC_intersects ) {
      goDGplus_nonrecovered_RFC_intersect_preds[goDGplus_num_nonrecovered_RFC_intersects] = 
	preddd;
      for ( k = 0; k < gnum_operators; k++ ) {
	if ( goperators[k] == my_o ) {
	  break;
	}
      }
      if ( k == gnum_operators ) {
	printf("\ndidn't find my_o operator??\n\n");
	exit(1);
      }
      goDGplus_nonrecovered_RFC_intersect_op0s[goDGplus_num_nonrecovered_RFC_intersects] = k;
      goDGplus_nonrecovered_RFC_intersects_weights[goDGplus_num_nonrecovered_RFC_intersects] = 1; 
      goDGplus_nonrecovered_RFC_intersects_totalweight += 1; 
      goDGplus_num_nonrecovered_RFC_intersects++;
    } else { /* did find record j! */
      goDGplus_nonrecovered_RFC_intersects_weights[j] += 1; 
      goDGplus_nonrecovered_RFC_intersects_totalweight += 1; 
    }

  } /* endfor i over RFC intersect */

  if ( !failure ) {
    if ( gcmd_line.display_info == 2 ) {
      printf("\ncriterion (2a) applies: RFC_intersect is recovered!");
    }
    result = 1;
    goDGplus_num_succ_t0adequateRFCrecovered++; /* Joerg2014: new feature */

    /* need to undo Booleans!
     */
    for ( i = 0; i < num_F_less0_Pplus_of_s; i++ ) {
      newDTGnode = F_less0_Pplus_of_s[i];
      in_F_less0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_R_neq0_Pplus_of_s; i++ ) {
      newDTGnode = R_neq0_Pplus_of_s[i];
      in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_context_t0_plus_own; i++ ) {
      newDTGnode = context_t0_plus_own[i];
      in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_RFC_intersect; i++ ) {
      newDTGnode = RFC_intersect[i];
      in_RFC_intersect[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_S_geq0_Pplus_of_s; i++ ) {
      newDTGnode = S_geq0_Pplus_of_s[i];
      in_S_geq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_have_varval; i++ ) {
      is_have_varval[have_varval[i]] = FALSE;
    }

    return result;
  }



  /* second go: WITH op replacement!
   *
   * ... if desired!
   */
  if ( gcmd_line.replacement_level == 0 ) {

    /* need to undo Booleans!
     */
    for ( i = 0; i < num_F_less0_Pplus_of_s; i++ ) {
      newDTGnode = F_less0_Pplus_of_s[i];
      in_F_less0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_R_neq0_Pplus_of_s; i++ ) {
      newDTGnode = R_neq0_Pplus_of_s[i];
      in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_context_t0_plus_own; i++ ) {
      newDTGnode = context_t0_plus_own[i];
      in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_RFC_intersect; i++ ) {
      newDTGnode = RFC_intersect[i];
      in_RFC_intersect[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_S_geq0_Pplus_of_s; i++ ) {
      newDTGnode = S_geq0_Pplus_of_s[i];
      in_S_geq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
    }
    for ( i = 0; i < num_have_varval; i++ ) {
      is_have_varval[have_varval[i]] = FALSE;
    }

    return result;
  }



  /* for op0 replacement, simply try all op0_prime that have same pre
   * as op0 and same eff on var0 and maintain rplan. find these by
   * looking at all outgoing transitions of s(var0)
   */
  for ( t0_prime_index = 0; 
	t0_prime_index < gDTGs[var0].nodes[ls_on_var[var0]].num_out;
	t0_prime_index++ ) {

    op0_prime = -1;
    if ( gcmd_line.replacement_level < 2 ) {
      /* op0 replacement NOT desired! simply do nothing here, and
       * break directly below.
       *
       * ... just need to signal that we haven't actually replaced op0.
       */
      op0_prime = op0;
      t0_prime = t0;
    } else {
      /* see if this guy is suitable, and if yes re-compute
       * \context(s(\var_0),c) \cup \{(\var_0,s(\var_0))\} as well as
       * RFC intersect
       */
      t0_prime = gDTGs[var0].nodes[ls_on_var[var0]].out[t0_prime_index];
      /* testing etc. here needed only for other transitions...
       */
      if ( t0_prime != t0 ) {
	if ( t0_prime->end != t0->end ) {
	  continue;
	}
	if ( t0_prime->num_conditions != t0->num_conditions ) {
	  continue;
	}
	for ( i = 0; i < t0_prime->num_conditions; i++ ) {
	  for ( j = 0; j < t0->num_conditions; j++ ) {
	    if ( t0->conditions[j] == t0_prime->conditions[i] ) {
	      break;
	    }
	  }
	  if ( j == t0->num_conditions ) {
	    break;
	  }
	}
	if ( i < t0_prime->num_conditions ) {
	  continue;
	}
	lreordered_Pplus_of_s[lreordered_ind0] = t0_prime->rop;
	rplan_preserve = is_relaxed_plan_for_s( lreordered_Pplus_of_s,
						lreordered_num_Pplus_of_s );
	if ( !rplan_preserve ) {
	  lreordered_Pplus_of_s[lreordered_ind0] = op0;
	  continue;
	}
      
	/* yep it's suitable!
	 */
	op0_prime = t0_prime->rop;
	if ( op0_prime == op0 ) {
	  printf("\n op0_prime == op0??\n\n");
	  exit(1);
	}
	if ( gcmd_line.display_info == 2 ) {
	  printf("\nR-reduction-by-op0: replacing ");
	  print_op_name(op0);
	  printf(" with ");
	  print_op_name(op0_prime);
	}
	
	/* Now we re-do \context(s(\var_0),c) \cup \{(\var_0,s(\var_0))\}
	 */
	for ( i = 0; i < num_context_t0_plus_own; i++ ) {
	  newDTGnode = context_t0_plus_own[i];
	  in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] = FALSE;
	}
	num_context_t0_plus_own = 0;
	for ( i = 0; i < t0_prime->num_contexts; i++ ) {
	  for ( j = 0; j < t0_prime->num_context[i]; j++ ) {
	    newDTGnode = t0_prime->context[i][j];
	    if ( newDTGnode->var == var0 ) {
	      printf("\nnewDTGnode->var == var0\n\n");
	      exit(1);
	    }
	    /* no duplicates here -- diferent ctx vars, different ctx vals.
	     */
	    context_t0_plus_own[num_context_t0_plus_own] = newDTGnode;
	    in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] = TRUE;
	    num_context_t0_plus_own++;
	  }
	}
	newDTGnode = &(gDTGs[var0].nodes[ls_on_var[var0]]);
	context_t0_plus_own[num_context_t0_plus_own] = newDTGnode;
	in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] = TRUE;
	num_context_t0_plus_own++;
	if ( gcmd_line.display_info == 2 ) {
	  printf("\ncontext(s(var_0),c) cup {(var_0,s(var_0))} after replacing op0: ");
	  for ( i = 0; i < num_context_t0_plus_own; i++ ) {
	    print_Variable_Value(context_t0_plus_own[i]->var,
				 context_t0_plus_own[i]->val,
				 TRUE);
	    printf("; ");
	  }
	}
	
	/* also need to re-do RFC...
	 */
	for ( i = 0; i < num_RFC_intersect; i++ ) {
	  newDTGnode = RFC_intersect[i];
	  in_RFC_intersect[newDTGnode->var][newDTGnode->val] = FALSE;
	}
	num_RFC_intersect = 0;
	for ( i = 0; i < num_F_less0_Pplus_of_s; i++ ) {
	  newDTGnode = F_less0_Pplus_of_s[i];    
	  if ( !in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] ) {
	    continue;
	  }
	  if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
	    continue;
	  }
	  RFC_intersect[num_RFC_intersect] = newDTGnode;
	  in_RFC_intersect[newDTGnode->var][newDTGnode->val] = TRUE;
	  num_RFC_intersect++;
	}
	if ( gcmd_line.display_info == 2 ) {
	  printf("\nRFC_intersect after replacing op0: ");
	  for ( i = 0; i < num_RFC_intersect; i++ ) {
	    print_Variable_Value(RFC_intersect[i]->var, 
				 RFC_intersect[i]->val,
				 TRUE);
	    printf("; ");
	  }
	}

      } else {/* endif t0_prime is actually different from t0 */
	op0_prime = op0;
	t0_prime = t0;
      }

    } /* endif wanna do op0 replacement */



    /* now, if desired, do P_{>0} op replacement for R reduction
     */
    if ( gcmd_line.replacement_level >= 1 ) {/* redundant "if"... well. */
      /* re-compute R and RFC based on trying to exchange P_{>0} ops!
       */
      for ( i = 0; i < num_R_neq0_Pplus_of_s; i++ ) {
	newDTGnode = R_neq0_Pplus_of_s[i];
	in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
      }
      num_R_neq0_Pplus_of_s = 0;
      /* first, all except P+ op precs remains the same!
       */
      for ( i = 0; i < lreordered_ind0; i++ ) {
	op = lreordered_Pplus_of_s[i];
	for ( j = 0; j < gop_conn[op].num_pre; j++ ) {
	  prevar = gop_conn[op].pre[j].var;
	  preval = gop_conn[op].pre[j].val;
	  newDTGnode = &(gDTGs[prevar].nodes[preval]);

	  if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
	    R_neq0_Pplus_of_s[num_R_neq0_Pplus_of_s] = newDTGnode;
	    in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
	    num_R_neq0_Pplus_of_s++;
	  }
	}
      }
      for ( i = 0; i < gnum_variables; i++ ) {
	if ( ggoal_on_var[i] == -1 ) {
	  continue;
	}
	newDTGnode = &(gDTGs[i].nodes[ggoal_on_var[i]]);
	if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
	  R_neq0_Pplus_of_s[num_R_neq0_Pplus_of_s] = newDTGnode;
	  in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
	  num_R_neq0_Pplus_of_s++;
	}
      }
      for ( i = 0; i < gSG.num_nodes; i++ ) {
	if ( !gSG.nodes[i].IN ) {
	  continue;
	}
	if ( i == var0 ) {
	  continue;
	}
	for ( j = 0; j < gDTGs[i].num_transitions; j++ ) {
	  t = &(gDTGs[i].transitions[j]);
	  if ( !t->IN ) {
	    continue;
	  }
	  if ( !t->induced ) {
	    continue;
	  }
	  newDTGnode = t->start;
	  if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
	    R_neq0_Pplus_of_s[num_R_neq0_Pplus_of_s] = newDTGnode;
	    in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
	    num_R_neq0_Pplus_of_s++;
	  }
	}
      }
      /* now, the meat here: go through all ops of P>0. If op has prec
       * (x,c) so that (x,c) is in C and (x,c) is not in R as computed
       * so far, then: try all op' where pre(op')(x) = (x,eff(t0)(x)) and
       * eff(op') cap eff(op) not empty. if replacing op with op' in
       * P+ remains rplan, then use op' instead.
       */
      replaced_one = FALSE;
      for ( i = lreordered_ind0 + 1; i < lreordered_num_Pplus_of_s; i++ ) {
	op = lreordered_Pplus_of_s[i];
	
	newDTGnode = NULL;
	for ( j = 0; j < num_context_t0_plus_own; j++ ) {
	  if ( gop_conn[op].pre_on_var[context_t0_plus_own[j]->var] ==
	       context_t0_plus_own[j]->val ) {
	    if ( !in_R_neq0_Pplus_of_s[context_t0_plus_own[j]->var][context_t0_plus_own[j]->val] ) {
	      newDTGnode = context_t0_plus_own[j];
	      break;
	    }
	  }
	}
	if ( newDTGnode ) {
/* 	  printf("\ncritical op: "); */
/* 	  print_op_name(op); */
	  /* yes -- this op uses the pre fact newDTGnode that's in C and
	   * not yet in R. Try to replace it!
	   */
	  if ( gop_conn[op].num_E == 0 ) {
	    printf("\nKALLO gop_conn[op].num_E == 0??\n\n");
	    exit(1);
	  }
	  /* first, find fact (x,eff(t0)(x)), into op0effDTGnode.
	   */
	  if ( newDTGnode->var == t0_prime->end->var ) {
	    op0effDTGnode = t0_prime->end;
	  } else {
	    for ( j = 0; j < t0_prime->num_side_effects; j++ ) {
	      if ( t0_prime->side_effects[j]->var == newDTGnode->var ) {
		break;
	      }
	    }
	    if ( j == t0_prime->num_side_effects ) {
	      printf("\nj == t0_prime->num_side_effects??\n\n");
	      exit(1);
	    }
	    op0effDTGnode = t0_prime->side_effects[j];
	  }
	  ft = gvariables[op0effDTGnode->var].vals[op0effDTGnode->val];
	  if ( ft != -1 ) {
/* 	    printf("\nop0 effect fact: "); */
/* 	    print_ft_name(ft); */
	    for ( k = 0; k < gft_conn[ft].num_PC; k++ ) {
	      op_prime = gef_conn[gft_conn[ft].PC[k]].op;
/* 	      printf("\nalternative: "); */
/* 	      print_op_name(op_prime); fflush(stdout); */
	      if ( op_prime == op ) {
		continue;
	      }
	      if ( gop_conn[op_prime].num_E == 0 ) {
		/* this CAN happen! since we're going over ftconn here
		 * which does contain the empty-ops
		 */
		continue;
	      }
	      /* check if effs have non-empty intersection
	       */
	      for ( l = 0; l < gnum_variables; l++ ) {
		if ( gop_conn[op].eff_on_var[l] != -1 &&
		     gop_conn[op].eff_on_var[l] == gop_conn[op_prime].eff_on_var[l] ) {
		  break;
		}
	      }
	      if ( l == gnum_variables ) {
/* 		printf("\nno common effect"); */
		continue;
	      }
	      /* check if we can replace and still have a relaxed plan
	       */
	      lreordered_Pplus_of_s[i] = op_prime;
/* 	      if ( op0_prime == -1 ) { */
/* 		printf("\noben: op0_prime == -1??\n\n"); */
/* 		exit(1); */
/* 	      } */
/* 	      lreordered_Pplus_of_s[lreordered_ind0] = op0_prime; */
	      rplan_preserve = is_relaxed_plan_for_s( lreordered_Pplus_of_s,
						       lreordered_num_Pplus_of_s );
/* 	      lreordered_Pplus_of_s[lreordered_ind0] = op0; */
	      if ( rplan_preserve ) {
		if ( gcmd_line.display_info == 2 ) {
		  printf("\nR-reduction-by-P>0: replacing ");
		  print_op_name(op);
		  printf(" with ");
		  print_op_name(op_prime);
		}
		/* success! simply replace, in what follows, op with op_prime.
		 */
		op = op_prime;
		replaced_one = TRUE;
		break;
	      } else {
		lreordered_Pplus_of_s[i] = op;
/* 		printf("\nno rplan"); */
	      }
	    } /* endfor k, op_prime over alternatives */	    
	  } /* endif (x,eff(t0)(x)) is not OTHER */



	  /* OLD version based on trying all add-intersects.
	   */
/* 	  ef = gop_conn[op].E[0]; */
/* 	  for ( j = 0; j < gef_conn[ef].num_A; j++ ) { */
/* 	    ft = gef_conn[ef].A[j]; */
/* 	    for ( k = 0; k < gft_conn[ft].num_A; k++ ) { */
/* 	      op_prime = gef_conn[gft_conn[ft].A[k]].op; */
/* 	      if ( op_prime == op ) { */
/* 		continue; */
/* 	      } */
/* 	      /\* if op_prime has the same precond, no point in using it! */
/* 	       * (actually could test whole condition rather than "just" */
/* 	       * this precond.) */
/* 	       *\/ */
/* 	      if ( gop_conn[op_prime].pre_on_var[newDTGnode->var] == */
/* 		   newDTGnode->val ) { */
/* 		continue; */
/* 	      } */
/* 	      /\* check if we can replace and still have a relaxed plan */
/* 	       *\/ */
/* 	      lreordered_Pplus_of_s[i] = op_prime; */
/* 	      if ( op0_prime == -1 ) { */
/* 		printf("\noben: op0_prime == -1??\n\n"); */
/* 		exit(1); */
/* 	      } */
/* 	      lreordered_Pplus_of_s[lreordered_ind0] = op0_prime; */
/* 	      rplan_preserve = is_relaxed_plan_for_s( lreordered_Pplus_of_s, */
/* 						       lreordered_num_Pplus_of_s ); */
/* 	      lreordered_Pplus_of_s[lreordered_ind0] = op0; */
/* 	      lreordered_Pplus_of_s[i] = op; */
/* 	      if ( rplan_preserve ) { */
/* 		if ( gcmd_line.display_info == 2 ) { */
/* 		  printf("\nR-reduction-by-P>0: replacing "); */
/* 		  print_op_name(op); */
/* 		  printf(" with "); */
/* 		  print_op_name(op_prime); */
/* 		} */
/* 		op = op_prime; */
/* 		replaced_one = TRUE; */
/* 		break; */
/* 	      } */
/* 	    } /\* endfor k, op_prime over all adders of ft *\/ */
/* 	    if ( k < gft_conn[ft].num_A ) { */
/* 	      break; */
/* 	    } */
/* 	  } /\* endfor j, ft over all adds of op *\/ */


	} /* endif yep have newDTGnode, try to replace op */

	/* now include op's preconds, just as before.
	 */
	for ( j = 0; j < gop_conn[op].num_pre; j++ ) {
	  prevar = gop_conn[op].pre[j].var;
	  preval = gop_conn[op].pre[j].val;
	  newDTGnode = &(gDTGs[prevar].nodes[preval]);
	  if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
	    R_neq0_Pplus_of_s[num_R_neq0_Pplus_of_s] = newDTGnode;
	    in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = TRUE;
	    num_R_neq0_Pplus_of_s++;
	  }
	}
      } /* endfor i, op over P>0 ops */

      if ( replaced_one ) {
	if ( gcmd_line.display_info == 2 ) {
	  printf("\nR_{neq 0}(P^+(s)) after replacing P_>0 ops: ");
	  for ( i = 0; i < num_R_neq0_Pplus_of_s; i++ ) {
	    print_Variable_Value(R_neq0_Pplus_of_s[i]->var, 
				 R_neq0_Pplus_of_s[i]->val,
				 TRUE);
	    printf("; ");
	  }
	}
	/* also need to re-do RFC...
	 */
	for ( i = 0; i < num_RFC_intersect; i++ ) {
	  newDTGnode = RFC_intersect[i];
	  in_RFC_intersect[newDTGnode->var][newDTGnode->val] = FALSE;
	}
	num_RFC_intersect = 0;
	for ( i = 0; i < num_F_less0_Pplus_of_s; i++ ) {
	  newDTGnode = F_less0_Pplus_of_s[i];    
	  if ( !in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] ) {
	    continue;
	  }
	  if ( !in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] ) {
	    continue;
	  }
	  RFC_intersect[num_RFC_intersect] = newDTGnode;
	  in_RFC_intersect[newDTGnode->var][newDTGnode->val] = TRUE;
	  num_RFC_intersect++;
	}
	if ( gcmd_line.display_info == 2 ) {
	  printf("\nRFC_intersect after replacing P_>0 ops: ");
	  for ( i = 0; i < num_RFC_intersect; i++ ) {
	    print_Variable_Value(RFC_intersect[i]->var, 
				 RFC_intersect[i]->val,
				 TRUE);
	    printf("; ");
	  }
	}
      }
    } /* endif re-compute R based on trying to exchange P_{>0} ops */
    


    /* initialize RFC_intersect_re_added.
     */
    for ( i = 0; i < num_RFC_intersect; i++ ) {
      RFC_intersect_re_added[i] = FALSE;
    }
    
    /* re-do have_varval with S_geq0_Pplus_of_s
     */
    for ( i = 0; i < num_have_varval; i++ ) {
      is_have_varval[have_varval[i]] = FALSE;
    }
    num_have_varval = 0;
    for ( i = 0; i < num_S_geq0_Pplus_of_s; i++ ) {
      haveft = gvariables[S_geq0_Pplus_of_s[i]->var].vals[S_geq0_Pplus_of_s[i]->val];
      if ( haveft != -1 ) {
	have_varval[num_have_varval] = haveft;
	is_have_varval[haveft] = TRUE;
	num_have_varval++;
      }
    }
    
    /* now loop through the ops to the right hand side of op0!
     */
    for ( i = lreordered_ind0 + 1; i < lreordered_num_Pplus_of_s; i++ ) {
      op = lreordered_Pplus_of_s[i];
      
      /* is op allowed?
       */
      for ( j = 0; j < gop_conn[op].num_pre; j++ ) {
	haveft = gvariables[gop_conn[op].pre[j].var].vals[gop_conn[op].pre[j].val];
	if ( haveft == -1 ) {
	  printf("\nft == -1??\n\n");
	  exit(1);
	}
	if ( !is_have_varval[haveft] ) {
	  break;
	}
      }
      if ( j < gop_conn[op].num_pre ) {
	if ( gcmd_line.replacement_level < 3 ) {
	  continue;
	}
	
	/* For now, we do the following HACK: if op is not applicable
	 * but affects a var x that is in RFC_intersect and hasn't been
	 * re-added yet, then we see whether there exists op' that
	 * establishes the RFC_intersect value of x, that is applicable,
	 * and where the rplan with op' instead of op is still an
	 * rplan. If so, we consider op' to be in.
	 */
	RFCind = -1;
	for ( j = 0; j < num_RFC_intersect; j++ ) {
	  if ( gop_conn[op].eff_on_var[RFC_intersect[j]->var] != -1 &&
	       !RFC_intersect_re_added[j] ) {
	    RFCind = j;
	    break;
	  }
	}
	if ( RFCind != -1 ) {
	  /* yes this guy looks "potentially important". Try to
	   * exchange.
	   */
	  ft = gvariables[RFC_intersect[RFCind]->var].vals[RFC_intersect[RFCind]->val];
	  if ( ft != -1 ) {
	    for ( j = 0; j < gft_conn[ft].num_A; j++ ) {
	      op_prime = gef_conn[gft_conn[ft].A[j]].op;
	      if ( op_prime == op ) {
		continue;
	      }
	      if ( gop_conn[op_prime].num_E == 0 ) {
		/* this CAN happen! since we're going over ftconn here
		 * which does contain the empty-ops
		 */
		continue;
	      }
	      /* is this guy allowed?
	       */
	      for ( k = 0; k < gop_conn[op_prime].num_pre; k++ ) {
		haveft = gvariables[gop_conn[op_prime].pre[k].var].vals[gop_conn[op_prime].pre[k].val];
		if ( haveft == -1 ) {
		  printf("\nhaveft == -1??\n\n");
		  exit(1);
		}
		if ( !is_have_varval[haveft] ) {
		  break;
		}
	      }
	      if ( k < gop_conn[op_prime].num_pre ) {
		/* not allowed, try next replacer
		 */
		continue; 
	      }
	      /* allowed, check if we can replace and still have a relaxed plan
	       */
	      lreordered_Pplus_of_s[i] = op_prime;
/* 	      if ( op0_prime == -1 ) { */
/* 		printf("\noben: op0_prime == -1??\n\n"); */
/* 		exit(1); */
/* 	      } */
/* 	      lreordered_Pplus_of_s[lreordered_ind0] = op0_prime; */
	      rplan_preserve = is_relaxed_plan_for_s( lreordered_Pplus_of_s,
						      lreordered_num_Pplus_of_s );
/* 	      lreordered_Pplus_of_s[lreordered_ind0] = op0; */
	      if ( rplan_preserve ) {
		if ( gcmd_line.display_info == 2 ) {
		  printf("\nRFC recovery: replacing ");
		  print_op_name(op);
		  printf(" with ");
		  print_op_name(op_prime);
		}
		/* yes! include the effs of this guy!
		 */
		for ( k = 0; k < gop_conn[op_prime].num_eff; k++ ) {
		  effvar = gop_conn[op_prime].eff[k].var;
		  effval = gop_conn[op_prime].eff[k].val;
		  newDTGnode = &(gDTGs[effvar].nodes[effval]);
		  /* does this tick off a RFC_intersect?
		   */
		  for ( l = 0; l < num_RFC_intersect; l++ ) {
		    if ( RFC_intersect[l] == newDTGnode ) {
		      RFC_intersect_re_added[l] = TRUE;
		      /* no duplicates so this ticks off only this guy and there's
		       * no need to continue
		       */
		      break;
		    }
		  }
		  /* is this already in?
		   */
		  haveft = gvariables[effvar].vals[effval];
		  if ( haveft != -1 && !is_have_varval[haveft] ) {
		    have_varval[num_have_varval] = haveft;
		    is_have_varval[haveft] = TRUE;
		    num_have_varval++;
		  }
		} /* endfor k, effvar/val over op_prime effs */ 
		
		/*found a replacer. STOP the j, op_prime loop!
		 */
		break;
	      } else {/* endif op_prime still results in relaxed plan */
		lreordered_Pplus_of_s[i] = op;
	      }
	    } /* j, op_prime over adders of RFC_intersect fact on var affected by op */
	  } /* endif RFC_intersect fact on var affected by op is not OTHER */
	} /* endif RFC_intersect fact on var affected by op does exist */
	
	/* this lets us go on to next op in reordered rplan
	 */
	continue;
      } /* endif op is not allowed */
      
      
      
      /* yep, we got this guy. add his eff to have_varval, and tick off
       * the re-added RFC_intersect.
       */
      for ( j = 0; j < gop_conn[op].num_eff; j++ ) {
	effvar = gop_conn[op].eff[j].var;
	effval = gop_conn[op].eff[j].val;
	newDTGnode = &(gDTGs[effvar].nodes[effval]);
	
	/* does this tick off a RFC_intersect?
	 */
	for ( k = 0; k < num_RFC_intersect; k++ ) {
	  if ( RFC_intersect[k] == newDTGnode ) {
	    RFC_intersect_re_added[k] = TRUE;
	    /* no duplicates so this ticks off only this guy and there's
	     * no need to continue
	     */
	    break;
	  }
	}
	
	/* is this already in?
	 */
	haveft = gvariables[effvar].vals[effval];
	if ( haveft != -1 && !is_have_varval[haveft] ) {
	  have_varval[num_have_varval] = haveft;
	  is_have_varval[haveft] = TRUE;
	  num_have_varval++;
	}
      } /* endfor j, effvar/val over op effs */  
      
    } /* endfor i, op over ops to the right of op0 */

    if ( gcmd_line.replacement_level < 3 ) {
      /* we're doing no op0/t0 alternatives, simply stop right now.
       */
      break;
    }

  } /* endfor t0_prime_index over possible op0/t0 alternatives */



  /* now all we need to do, in order to check (a), is to see whether
   * all RFC_intersect facts have been ticked off.
   */
  failure = FALSE;
  for ( i = 0; i < num_RFC_intersect; i++ ) {
    if ( RFC_intersect_re_added[i] ) {
      continue;
    }

    failure = TRUE;
    
    /* if this is var0, ie, the delete of t0, and if t0 is
     * invertible, then don't record it -- such a failure is just
     * because this is not what we should be doing, with this
     * var...
     */
    if ( RFC_intersect[i]->var == var0 && t0->invertible ) {
      continue;
    }
    
    fttt = gvariables[RFC_intersect[i]->var].vals[RFC_intersect[i]->val];
    /* if this guy is not a real fact then there's nothing we can record...
     */
    if ( fttt == -1 ) {
      continue;
    }
    
    /* if this is supposed to be a "side effect", but actually the
     * preds are "exchanged" -- every op having a positive effect on
     * one has a negative effect on the other -- then presume that
     * this is only FD not recognizing what is actually a multi-valued
     * variable, and don't record the bugger. Note here: FD sometimes
     * does not find obviously mutex facts, resulting in overly
     * fine-grained variables (eg separating "have" from "in-boot" in
     * tyreworld, and separating "power_avail" from "power_on" in
     * satellite), which results in diagnosis thinking that what is
     * actually simply a value change is a side-effect, thus
     * incorrectly diagnozing the side effect to be harmful (eg
     * "put-away, have" in tyreworld, "switch_on, power_avail" in
     * satellite). ... of course, the solution here is a HACK! (note
     * though that the real hack is PDDL, forcing us to express the
     * problem in an unnatural manner, resulting in imprecisions when
     * recovering its real structure automatically). what we would
     * really want is a stronger mutex detection technique, delivering
     * the correct variables at least in these simple cases.
     */
    if ( RFC_intersect[i]->var != var0 && gcmd_line.do_diagnose_ignore_exchangedvars ) {
      if ( gvariables[t0->end->var].vals[t0->end->val] != -1 &&
	   are_exchanged_predicates( grelevant_facts[fttt].predicate,
				     grelevant_facts[gvariables[t0->end->var].vals[t0->end->val]].predicate ) ) {
	continue;
      }
    }

    if ( RFC_intersect[i]->var == var0 && gcmd_line.do_diagnose_invertop0 ) {
      /* next test: if this is var0 and there exists op'
       *  recovering the delete, so that op' is definitely
       *  applicable in s1, then this own-delete is not the
       *  problem here...
       *
       * proceed by going over all adders of the deleted fact.
       */
      
      for ( j = 0; j < gft_conn[fttt].num_A; j++ ) {
	oppp =  gft_conn[fttt].A[j];
	if ( gop_conn[oppp].num_E == 0 ) {
	  /* this CAN happen! since we're going over ftconn here
	   * which does contain the empty-ops
	   */
	  continue;
	}
	for ( k = 0; k < gop_conn[oppp].num_pre; k++ ) {
	  if ( !in_S_geq0_Pplus_of_s[gop_conn[oppp].pre[k].var][gop_conn[oppp].pre[k].val] ) {
	    break;
	  }
	}
	if ( k == gop_conn[oppp].num_pre ) {
	  break;
	}
      }
      if ( j < gft_conn[fttt].num_A ) {
	/* yes! found such a guy!
	 */
	continue;
      }
    }

    /* Ok, record this bugger.
     */
    preddd = grelevant_facts[fttt].predicate;
    my_a = gop_conn[op0].action;
    if ( my_a->norm_operator ) {
      my_o = my_a->norm_operator->operator;
    } else {
      if ( my_a->pseudo_action ) {
	my_o = my_a->pseudo_action->operator;
      } else {
	printf("\nmy_a has neither norm op nor pseudo act??\n\n");
	exit(1);
      }
    }

    /* new version, with preds
     */
    for ( j = 0; j < goDGplus_num_nonrecovered_RFC_intersects; j++ ) {
      if ( goDGplus_nonrecovered_RFC_intersect_preds[j] == preddd &&
	   goperators[goDGplus_nonrecovered_RFC_intersect_op0s[j]] == my_o ) {
	break;
      }
    }
    if ( j == goDGplus_num_nonrecovered_RFC_intersects ) {
      goDGplus_nonrecovered_RFC_intersect_preds[goDGplus_num_nonrecovered_RFC_intersects] = 
	preddd;
      for ( k = 0; k < gnum_operators; k++ ) {
	if ( goperators[k] == my_o ) {
	  break;
	}
      }
      if ( k == gnum_operators ) {
	printf("\ndidn't find my_o operator??\n\n");
	exit(1);
      }
      goDGplus_nonrecovered_RFC_intersect_op0s[goDGplus_num_nonrecovered_RFC_intersects] = k;
      goDGplus_nonrecovered_RFC_intersects_weights[goDGplus_num_nonrecovered_RFC_intersects] = 1; 
      goDGplus_nonrecovered_RFC_intersects_totalweight += 1; 
      goDGplus_num_nonrecovered_RFC_intersects++;
    } else { /* did find record j! */
      goDGplus_nonrecovered_RFC_intersects_weights[j] += 1; 
      goDGplus_nonrecovered_RFC_intersects_totalweight += 1; 
    }

  } /* endfor i over RFC intersect */
  
  if ( !failure ) {
    if ( gcmd_line.display_info == 2 ) {
      printf("\ncriterion (2a) applies: RFC_intersect is recovered!");
    }
    result = 1;   
    goDGplus_num_succ_t0adequateRFCrecovered++; /* Joerg2014: new feature */
  }

  /* need to undo Booleans!
   */
  for ( i = 0; i < num_F_less0_Pplus_of_s; i++ ) {
    newDTGnode = F_less0_Pplus_of_s[i];
    in_F_less0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
  }
  for ( i = 0; i < num_R_neq0_Pplus_of_s; i++ ) {
    newDTGnode = R_neq0_Pplus_of_s[i];
    in_R_neq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
  }
  for ( i = 0; i < num_context_t0_plus_own; i++ ) {
    newDTGnode = context_t0_plus_own[i];
    in_context_t0_plus_own[newDTGnode->var][newDTGnode->val] = FALSE;
  }
  for ( i = 0; i < num_RFC_intersect; i++ ) {
    newDTGnode = RFC_intersect[i];
    in_RFC_intersect[newDTGnode->var][newDTGnode->val] = FALSE;
  }
  for ( i = 0; i < num_S_geq0_Pplus_of_s; i++ ) {
    newDTGnode = S_geq0_Pplus_of_s[i];
    in_S_geq0_Pplus_of_s[newDTGnode->var][newDTGnode->val] = FALSE;
  }
  for ( i = 0; i < num_have_varval; i++ ) {
    is_have_varval[have_varval[i]] = FALSE;
  }

  return result;

}
























/**********************
 * Control for analysis of samples
 **********************/





















void analyze_samples_local_oDGplus( void )

{

  int i;
  int num_success = 0;
  int min_ed_bound = -1;
  float mean_ed_bound = 0;
  int max_ed_bound = -1;
  int num_dead_end = 0;

  /* undo any crap left behind for us from our predecessors...
   */
  for ( i = 0; i < gSG.num_nodes; i++ ) {
    gSG.nodes[i].IN = FALSE;
  }
  for ( i = 0; i < gSG.num_edges; i++ ) {
    gSG.IN_adj_matrix[gSG.edges[i].start->var][gSG.edges[i].end->var] = FALSE; 
  }

  for ( i = 0; i < gcmd_line.num_samples; i++ ) {

    analyze_local_oDGplus( &(gsample_states[i]) );

    if ( gsuccess ) {
      num_success++;

      if ( min_ed_bound == -1 || ged_bound < min_ed_bound ) {
	min_ed_bound = ged_bound;
      }

      if ( max_ed_bound == -1 || ged_bound > max_ed_bound ) {
	max_ed_bound = ged_bound;
      }

      mean_ed_bound += ged_bound;
      
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



