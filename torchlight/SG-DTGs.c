

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
 * File: SG-DTG.c
 * Description: creation of variables, support graph, DTGs
 *
 * Author: Joerg Hoffmann
 *
 *********************************************************************/ 






#include "torchlight.h"
#include "output.h"
#include "SG-DTGs.h"





Bool ldebug = FALSE;














/**********************
 * generate and parse the multi-valued vars
 **********************/














void create_and_parse_variables( void )

{

  FILE *f;
  char *tmp;
  int length;
  char command[MAX_LENGTH];

  int parsed_var;
  int var;
  int val;
  int arg;

  char ***predicate;
  char ****args;
  int **num_args;
  int *num_vals;
  int num_vars;

  int i, j, k, l, ll;
  int me, he;

  Bool *common_pred;
  Bool *common_arg;

  Fact *fact;

  int digit1, digit2;

  length = MAX_LENGTH;
  tmp = (char *) malloc (length + 1);

  /* run FD translator
   */
  if ( gcmd_line.use_FD ) {
    sprintf(command, "./GENERATE-VARS/generate-vars %s %s > BLA", gops_file, gfct_file);
    system( command );
  }

  if ( (f = fopen(gcmd_line.fdr_path, "r")) == NULL ) {
    printf("\nCan't open finite-domain variables file!\n\n");
    exit(1);
  }
  /* get the number of vars
   */
  getline(&tmp, &length, f);
  while ( strcmp(tmp, "end_metric\n") != 0 ) getline(&tmp, &length, f);
  getline(&tmp, &length, f);
  sscanf(tmp, "%d", &num_vars); 
  /* printf("Number of vars: %d\n\n", num_vars); */
  /* exit (1); */

  num_vals = ( int * ) calloc(num_vars, sizeof(int));
  predicate = ( char *** ) calloc(num_vars, sizeof(char **));
  args = ( char **** ) calloc(num_vars, sizeof(char ***));
  num_args = ( int ** ) calloc(num_vars, sizeof(int*));

  /* now process the vars one-by-one
   */
  for ( i = 0; i < num_vars; i++ ) {
    getline(&tmp, &length, f);

    while ( strcmp(tmp, "begin_variable\n") != 0 ) getline(&tmp, &length, f);
    getline(&tmp, &length, f); /* var name, skip */
    getline(&tmp, &length, f); /* var axiom layer, skip */

    /* get number of values
     */
    getline(&tmp, &length, f);
    sscanf(tmp, "%d", &(num_vals[i])); 
    
    predicate[i] = ( char ** ) calloc(num_vals[i], sizeof(char *));
    args[i] = ( char *** ) calloc(num_vals[i], sizeof(char **));
    num_args[i] = ( int * ) calloc(num_vals[i], sizeof(int));
    for ( j = 0; j < num_vals[i]; j++) {
      predicate[i][j] = (char *) malloc(MAX_LENGTH);
    }

    /* get the values
     */
    for ( j = 0; j < num_vals[i]; j++) {
      getline(&tmp, &length, f); /* tmp now is a line a la "Atom at(ball1, rooma)" */

      /* count the args
       */
      num_args[i][j] = 0;
      l = 0;
      if ( tmp[l] == 'N' ) {
	/* This is a "NegatedAtom". These did not exist when I
	   implemented my first parser. Simply ignore and pretend they
	   were still "<none of those>".
	*/
      } else {
	while ( tmp[l] != '('  && tmp[l] != '<' ) l++;
	if ( tmp[l] == '<' ) {
	  /* this is a "<none of those>"
	   */
	} else {
	  /* regular fact, count arguments
	   */
	  if ( tmp[l+1] != ')' ) {
	    while ( TRUE ) {
	      while ( tmp[l] != ',' && tmp[l] != ')' ) l++;
	      num_args[i][j]++;
	      if ( tmp[l] == ')' ) break;
	      l++;
	    }
	  }
	}
      } /* endelse processing something other than a "NegatedAtom" */

      args[i][j] = ( char ** ) calloc(num_args[i][j], sizeof(char *));
      for ( k = 0; k < num_args[i][j]; k++ ) {
	args[i][j][k] = (char *) malloc(MAX_LENGTH);
      }
      
      l = 0;

      if ( tmp[l] == 'N' ) {
	/* This is a "NegatedAtom". These did not exist when I
	   implemented my first parser. Simply ignore and pretend they
	   were still "<none of those>".
	*/
	sprintf(predicate[i][j], "NONE");
	continue;
      }
    
      while ( tmp[l] != 'm' && tmp[l] != '<' ) l++;
      
      if ( tmp[l] == '<' ) {
	/* this is a "<none of those>"
	 */
	sprintf(predicate[i][j], "NONE");
	continue;
      }

      /* regular fact, get arguments
       */
      l++;
      l++;
      /* now we're at start of predicate name 
       */
      get_name(tmp, l, predicate[i][j]);
      
      while ( tmp[l] != '(' ) l++;
      l++;
      for ( k = 0; k < num_args[i][j]; k++ ) {
	/* invariant: we're at start of k-th argument
	 */
	get_name(tmp, l, args[i][j][k]);
	if ( k < num_args[i][j] - 1 ) {
	  while ( tmp[l] != ',' && tmp[l] != ')' ) l++;
	  if ( tmp[l] == ')' ) {
	    printf("\n\nERROR: tmp[l] == ')'\n\n");
	    exit(1);
	  } 
	  l++;
	  while ( tmp[l] == ' ' ) l++;
	}

      } /* endfor k over values of var i val j */

    } /* endfor j over values of var i */

    getline(&tmp, &length, f);
    while ( strcmp(tmp, "end_variable\n") != 0 ) getline(&tmp, &length, f);

  } /* endfor i over vars */



  /* printf("\n\nParsed Variables:\n"); */
  /* for ( i = 0; i < num_vars; i++ ) { */
  /*   printf("Variable %d:\n", i); */
  /*   for ( j = 0; j < num_vals[i]; j++) { */
  /*     printf("Value %d: %s(", j, predicate[i][j]); */
  /*     for ( k = 0; k < num_args[i][j]; k++ ) { */
  /* 	printf("%s", args[i][j][k]); */
  /* 	if ( k < num_args[i][j]-1 ) printf(", "); */
  /*     } */
  /*     printf(")\n"); */
  /*   } */
  /* } */
  /* fflush(stdout); */
  /* exit(1); */


  /* Now create the global Variables!
   */
  gvariables = ( Variable * ) calloc(num_vars, sizeof(Variable));
  gnum_variables = num_vars;
  for ( i = 0; i < num_vars; i++ ) {
    gvariables[i].vals = ( int * ) calloc(num_vals[i], sizeof(int));
    gvariables[i].num_vals = num_vals[i];
    for ( j = 0; j < num_vals[i]; j++) {
      gvariables[i].vals[j] = 
	find_ft_from_parsedvarval(predicate[i][j], num_args[i][j], args[i][j]);
    }
  }

  /* Need to post-process for "NONE"...  ... resolve for Booleans
   * where FF compiles an explicit fact for this; just keep as "OTHER"
   * for non-Booleans (this will never appear in an op
   * precondition... it's just an artificial "non of real vals
   * currently true" introduced by FD).
   */
  for ( i = 0; i < num_vars; i++ ) {
    if ( num_vals[i] < 2 ) {
      printf("\n\nFD var with less than 2 values??\n\n");
      exit(1);
    }

    me = -1;
    for ( j = 0; j < num_vals[i]; j++) {
      if ( gvariables[i].vals[j] != -1 ) {
	continue;
      }
      /* Either way we'll be done with this var.
       */
      me = j;
      break;
    }
    if ( me == -1 ) {
      /* no probl here
       */
      continue;
    }

    for ( k = 0; k < num_vals[i]; k++) {
      if ( k == me ) continue;
      if ( gvariables[i].vals[k] == -1 ) {
	printf("\n\nSorry -- FD \"none of those\" 2 times in single var?\n\n");
	exit(1);
      }
    }

    if ( num_vals[i] > 2 ) {
      if ( gcmd_line.display_info == 2 ) {
	printf("\nWarning -- FD \"none of those\" in non-binary var. Inserting OTHER.");
      }
      continue;
    }
    
    /* Try to negate the other guy, and find this fact instead!
     */
    if ( me == 0 ) {
      he = 1;
    } else {
      he = 0;
    }
    sprintf(predicate[i][me], "NOT-%s", predicate[i][he]);
    gvariables[i].vals[me] = 
      find_ft_from_parsedvarval(predicate[i][me], num_args[i][he], args[i][he]);
    if ( gvariables[i].vals[me] == -1 ) {
      /* Didn't find the negated fact -- means it hasn't been produced.
       * Then, this var is OTHER
       */
      if ( gcmd_line.display_info == 2 ) {
	printf("\nWarning -- FD \"none of those\" in binary var with no FF negated fact. Inserting OTHER.");
      }
    }
  }



  /* Joerg2014: disabling the recording of runtime taken by FD. not
     relevant in our context, and I don't wanna bother adpting this
     parser as well.
  */
  gFDvariables_time = 0;
  if ( gcmd_line.use_FD ) {
    sprintf(command, "rm ./BLA");
    system( command );
  }
  /* if ( gcmd_line.use_FD ) { */
  /*   /\* read the time taken by FD! */
  /*    *\/ */
  /*   if ( (f = fopen( "./BLA", "r")) == NULL ) { */
  /*     printf("\nCan't open FD BLA file!\n\n"); */
  /*     exit(1); */
  /*   } */
  /*   while ( !feof(f) ) { */
  /*     length = MAX_LENGTH; */
  /*     tmp = (char *) malloc (length + 1); */
  /*     getline(&tmp, &length, f); */
  /*     if ( tmp[0] == 'D' && */
  /* 	   tmp[1] == 'o' && */
  /* 	   tmp[2] == 'n' && */
  /* 	   tmp[3] == 'e' && */
  /* 	   tmp[4] == '!' ) { */
  /* 	break; */
  /*     } */
  /*   } */
  /*   sscanf(tmp, "Done! [%f", &gFDvariables_time); */
  /*   fclose(f); */
    
  /*   sprintf(command, "rm ./BLA"); */
  /*   system( command ); */
  /* } else { */
  /*   gFDvariables_time = 0; */
  /* } */


  /* as a final step here, find some (hopefully) useful name for each
   * var, for printing.
   */
  common_pred = ( Bool * ) calloc(gnum_predicates, sizeof(Bool));
  common_arg = ( Bool * ) calloc(gnum_constants, sizeof(Bool));

  for ( i = 0; i < gnum_variables; i++ ) {
    for ( j = 0; j < gnum_predicates; j++ ) {
      common_pred[j] = TRUE;
    }
    for ( j = 0; j < gnum_constants; j++ ) {
      common_arg[j] = TRUE;
    }
    for ( j = 0; j < gvariables[i].num_vals; j++ ) {
      if ( gvariables[i].vals[j] == -1 ) {
	continue;
      }
      fact = &(grelevant_facts[gvariables[i].vals[j]]);

      for ( k = 0; k < gnum_predicates; k++ ) {
	if ( k == fact->predicate ) {
	  continue;
	}
	common_pred[k] = FALSE;
      }

      for ( k = 0; k < gnum_constants; k++ ) {
	for ( l = 0; l < garity[fact->predicate]; l++ ) {
	  if ( fact->args[l] == k ) {
	    break;
	  }
	}
	if ( l == garity[fact->predicate] ) {
	  common_arg[k] = FALSE;
	}
      }
    } /* endfor j over var vals */

    /* Now we know which preds/args, if any, are common to all
     * var-vals (except OTHER, if present).  Assemble the var name
     * accordingly.
     */
    length = 0;
    for ( j = 0; j < gnum_predicates; j++ ) {
      if ( common_pred[j] ) length += (strlen(gpredicates[j])+1);
    }
    for ( j = 0; j < gnum_constants; j++ ) {
      if ( common_arg[j] ) length += (strlen(gconstants[j])+1);
    }
    if ( length > 0 ) {
      /* yes, found something
       */
      length += 6;
      gvariables[i].name = (char *) malloc(length);
      sprintf(gvariables[i].name, "-VAR-");
      for ( j = 0; j < gnum_predicates; j++ ) {
	if ( common_pred[j] ) {
	  strcat(gvariables[i].name, gpredicates[j]);
	  strcat(gvariables[i].name, "-");
	}
      }
      for ( j = 0; j < gnum_constants; j++ ) {
	if ( common_arg[j] ) {
	  strcat(gvariables[i].name, gconstants[j]);
	  strcat(gvariables[i].name, "-");
	}
      }
    } else {
      /* nope, simply make name "-1" to mark this
       */
      gvariables[i].name = (char *) malloc(3);
      sprintf(gvariables[i].name, "-1");
    }
  } /* endfor i over vars */

}



void get_name( char *tmp, int pos, char *name )

{

  int i;

  i = pos;
  while ( TRUE ) {
    if ( 'a' <= tmp[i] && tmp[i] <= 'z' ) {
      name[i-pos] =  (char) toupper((int) tmp[i]);
      i++;
      continue;
    }
    if ( 'A' <= tmp[i] && tmp[i] <= 'Z' ) {
      name[i-pos] =  (char) toupper((int) tmp[i]);
      i++;
      continue;
    }
    if ( '0' <= tmp[i] && tmp[i] <= '9' ) {
      name[i-pos] =  (char) toupper((int) tmp[i]);
      i++;
      continue;
    }
    if ( '-' == tmp[i] || '_' == tmp[i] ) {
      name[i-pos] = tmp[i];
      i++;
      continue;
    }
    break;
  }

  name[i-pos] = '\0';

}



int find_ft_from_parsedvarval( char *predicate, int num_args, char **args )

{

  int i, j;
  Fact *f;

  if ( strcmp("NONE", predicate) == SAME ) {
    return -1;
  }

  for ( i = 0; i < gnum_ft_conn; i++ ) {
    f = &(grelevant_facts[i]);

    if ( strcmp(gpredicates[f->predicate], predicate) != SAME ) {
      continue;
    }

    for ( j = 0; j < garity[f->predicate]; j++ ) {
      if ( strcmp(gconstants[(f->args)[j]], args[j]) != SAME ) {
	break;
      }
    }
    if ( j < garity[f->predicate] ) {
      continue;
    }

    return i;

  }

/*   printf("\n\nDidn't find this parsed fact: %s(", predicate); */
/*   for ( i = 0; i < num_args; i++ ) { */
/*     printf("%s", args[i]); */
/*     if ( i < num_args-1 ) printf(", "); */
/*   } */
/*   printf(")\n"); */
/*   printf("\n"); */
/*   exit(1); */

  return -1;

}


















/**********************
 * Put the VarVal info into the ft/op structures!
 **********************/


















void create_ft_op_indices( void )

{

  int i, j, k, var, val;
  int op, ef;
  int delft, delvar, delval, addvar, addval;

  Bool *hadvar;
  
  for ( i = 0; i < gnum_ft_conn; i++ ) {
    var = -1;
    val = -1;
    for ( j = 0; j < gnum_variables; j++ ) {
      for ( k = 0; k < gvariables[j].num_vals; k++ ) {
	if ( gvariables[j].vals[k] == i ) {
	  val = k;
	  break;
	}
      }
      if (  k < gvariables[j].num_vals ) {
	var = j;
	break;
      }
    }
    if ( var == -1 || val == -1 ) {
/*       /\* this can of course happen, if negations are compiled. */
/*        * BUT that should never be the case in STRIPS! */
/*        *\/ */
/*       printf("\n\nSorry -- didn't find VarVal for FF ft? "); */
/*       print_ft_name(i); */
/*       printf("\n\n"); */
/*       exit(1); */
      /* maybe FD has some sort of reachability
       * analysis... dunno. just mark this guy, and exclude it at
       * those places where we try to go from ftconn into varvals.
       */
      if ( gcmd_line.display_info == 2 ) {
	printf("\nWarning: didn't find variable value for FF ft ");
	print_ft_name(i);
	printf(". Skipping the fact from variables structures.");
      }
      gft_conn[i].notFD = TRUE;
    }
    gft_conn[i].var = var;
    gft_conn[i].val = val;
/*     if ( ldebug ) { */
/*       printf("\nVarVal for FF ft %d ", i); */
/*       print_ft_name(i); */
/*       printf(": var %d val %d", var, val); */
/*     } */
  }



  /* now create this simple helper structure.
   */
  ggoal_on_var = ( int * ) calloc(gnum_variables, sizeof( int ));
  for ( i = 0; i < gnum_variables; i++ ) {
    ggoal_on_var[i] = -1;
  }
  for ( i = 0; i < ggoal_state.num_F; i++ ) {
    if ( ggoal_on_var[gft_conn[ggoal_state.F[i]].var] != -1 ) {
      printf("\nggoal_on_var[gft_conn[ggoal_state.F[i]].var] != -1??\n\n");
      exit(1);
    }
    ggoal_on_var[gft_conn[ggoal_state.F[i]].var] = gft_conn[ggoal_state.F[i]].val;
  }



  hadvar = ( Bool * ) calloc(gnum_variables, sizeof(Bool));

  for ( op = 0; op < gnum_op_conn; op++ ) {
    if ( gop_conn[op].num_E == 0 ) {
      /* irrelevant op rendered obvious by pre-process
       */
      continue;
    }
    /* we have previously verified that each op has at most 1 effect
     */
/*     printf("\nop: %d, numE: %d", op, gop_conn[op].num_E); fflush(stdout); */
    ef = gop_conn[op].E[0];
/*     printf("\nef: %d", ef); fflush(stdout); */

    if ( gef_conn[ef].num_PC > 0 ) {
      gop_conn[op].pre = ( VarVal * ) 
	calloc(gef_conn[ef].num_PC, sizeof(VarVal));
    }
    if ( gef_conn[ef].num_A + gef_conn[ef].num_D > 0 ) {
      gop_conn[op].eff = ( VarVal * ) 
	calloc(gef_conn[ef].num_A + gef_conn[ef].num_D, sizeof(VarVal));
    }
	     
    /* the single effect-cond then contains op prec, and its add/del
     * is that of op.
     *
     * VarVal pre is easy: simply get the VarVal for each ft prec
     */
    /* now that we got the vars, of which we know they are
     * all pairwise mutex, we can prune ops whose prec contains two vals
     * of the same var!
     */
    for ( i = 0; i < gnum_variables; i++ ) {
      hadvar[i] = FALSE;
    }
    j = 0;
    for ( i = 0; i < gef_conn[ef].num_PC; i++ ) {
      if ( gft_conn[gef_conn[ef].PC[i]].notFD ) {
	continue;
      }
      if ( hadvar[gft_conn[gef_conn[ef].PC[i]].var] ) {
	break;
      }
      hadvar[gft_conn[gef_conn[ef].PC[i]].var] = TRUE;
      gop_conn[op].pre[j].var = gft_conn[gef_conn[ef].PC[i]].var;
      gop_conn[op].pre[j].val = gft_conn[gef_conn[ef].PC[i]].val;
      j++;
    }
    if ( i < gef_conn[ef].num_PC ) {
      /* same var constrained twice!
       * prune op by setting its eff number to 0!
       */
      gop_conn[op].num_E = 0;
      continue;/* and skip to next op... */
    }
    gop_conn[op].num_pre = gef_conn[ef].num_PC;

    /* VarVal eff slightly more complicated.
     *
     * First of all, all adds are VarVals.
     */
    for ( i = 0; i < gnum_variables; i++ ) {
      hadvar[i] = FALSE;
    }
    j = 0;
    for ( i = 0; i < gef_conn[ef].num_A; i++ ) {
      if ( gft_conn[gef_conn[ef].A[i]].notFD ) {
	continue;
      }
      if ( hadvar[gft_conn[gef_conn[ef].A[i]].var] ) {
	break;
      }
      hadvar[gft_conn[gef_conn[ef].A[i]].var] = TRUE;
      gop_conn[op].eff[j].var = gft_conn[gef_conn[ef].A[i]].var;
      gop_conn[op].eff[j].val = gft_conn[gef_conn[ef].A[i]].val;
      j++;
    }
    if ( i < gef_conn[ef].num_A ) {
      printf("\n\nVarVal sanity: same var added twice?\n\n");
      exit(1);
    }
    gop_conn[op].num_eff = gef_conn[ef].num_A;
    
    /* Dels are complicated -- basically, if var x val is
     * in del but no other x val is in add, then the eff val must be
     * OTHER. Details see below...
     */
    for ( i = 0; i < gef_conn[ef].num_D; i++ ) {
      if ( gft_conn[gef_conn[ef].D[i]].notFD ) {
	continue;
      }
      delft = gef_conn[ef].D[i];
      delvar = gft_conn[gef_conn[ef].D[i]].var;
      delval = gft_conn[gef_conn[ef].D[i]].val;
      
      for ( j = 0; j < gop_conn[op].num_pre; j++ ) {
	if ( gop_conn[op].pre[j].var == delvar ) {
	  /* Joerg2014: This case occured, with the new FD translator,
	     in philosophers. No idea what the reason is. I suppose an
	     action might explicitly delete more than one value of a
	     FD variable?
	  */
	  if ( gop_conn[op].pre[j].val != delval ) {
	    if ( gcmd_line.display_info == 2 ) {
	      printf("\n\nWarning: VarVal sanity: deleted val of var != pre val of var? op: ");
	      print_op_name(op);
	      printf("; fact: ");
	      print_ft_name(delft);
	      printf("\n\n");
	    }
	    continue;
	  }
	  break;
	}
      }

      if ( j < gop_conn[op].num_pre ) {
	/* we have a del on delvar, same value as in pre
	 *
	 * --> if add on delvar, that's it. else, add needs to be OTHER.
	 */
	for ( j = 0; j < gef_conn[ef].num_A; j++ ) {
	  if ( gft_conn[gef_conn[ef].A[j]].var == delvar ) {
	    break;
	  }
	}
	if ( j < gef_conn[ef].num_A ) {
	  continue;
	}

	for ( k = 0; k < gvariables[delvar].num_vals; k++ ) {
	  if ( gvariables[delvar].vals[k] == -1 ) {
	    break;
	  }
	}
	if ( k == gvariables[delvar].num_vals ) {
/* 	  printf("\n\nVarVal sanity: delvar val==pre, no add, no OTHER val?"); */
/* 	  printf("\nVariable: "); print_Variable(delvar); */
/* 	  printf("\nValue: "); print_Variable_Value(delvar, delval, FALSE); */
/* 	  printf("\nop: "); print_op_name(op); */
/* 	  printf("\n\n"); */
/* 	  exit(1); */
	  /* This can happen if FD removed some fts that FF keeps.
	   *
	   * Example: 
	   *
	   * Warning: didn't find variable value for FF ft
	   * READY-TO-LOAD-GOODS1-MARKET1-LEVEL2(). Skipping the fact
	   * from variables structures.
	   *
	   * VarVal sanity: delvar val==pre, no add, no OTHER val?
	   * Variable: READY-TO-LOAD-GOODS1-MARKET1-LEVEL0()-READY-TO-LOAD-GOODS1-MARKET1-LEVEL1()
	   * Value: READY-TO-LOAD-GOODS1-MARKET1-LEVEL1()
	   * op: BUY-TRUCK1-GOODS1-MARKET1-LEVEL0-LEVEL1-LEVEL1-LEVEL2
	   *
	   * I assume for now that FD has a good reason for removing
	   * the value, and thus the op should be removed. I note that
	   * this occurs ONLY in TPP, in all other domains "didn't
	   * find variable value for FF ft" never happens!
	   */
	  gop_conn[op].num_E = 0;
	  /* breaks loop i over deletes, then op loop will directly proceed to next op.
	   */ 
	  break; 
	}
       

	gop_conn[op].eff[gop_conn[op].num_eff].var = delvar;
	gop_conn[op].eff[gop_conn[op].num_eff].val = k;
	gop_conn[op].num_eff++;
	continue;
      }

      /* we have a del on delvar and no pre.
       * 
       * --> if add on delvar, that's it. else, if var has 2 values
       *      then add needs to be OTHER because in FF dels, we have
       *      only real facts so the deleted value is the non-OTHER
       *      one of delvar.
       *
       * Airport example: TAKEOFF has delete with no prec on OCCUPIED,
       * which groups together a whole set of segments (apparently at
       * most one of these can be occupied, at any time). OTHER is the
       * correct choice here. Let's just assume it always is -- FD
       * should make sure that the action is not applicable when a
       * different fact is true in the state.
       */
      for ( j = 0; j < gef_conn[ef].num_A; j++ ) {
	if ( gft_conn[gef_conn[ef].A[j]].var == delvar ) {
	  break;
	}
      }
      if ( j < gef_conn[ef].num_A ) {
	continue;
      }

/*       if ( gvariables[delvar].num_vals > 2 ) { */
/* 	printf("\n\nVarVal sanity: deleted var no pre no add, >2 vals of var? "); */
/* 	printf("\noperator: "); */
/* 	print_op_name(op); */
/* 	printf("\ndeleted: "); */
/* 	print_ft_name(delft); */
/* 	printf("\nvariable: "); */
/* 	print_Variable(delvar); */
/* 	printf("\nvamues: %d", gvariables[delvar].num_vals); */
/* 	for ( j = 0; j < gvariables[delvar].num_vals; j++ ) { */
/* 	  printf("\n"); */
/* 	  print_Variable_Value(delvar, j, TRUE); */
/* 	} */
/* 	printf("\n\n"); */
/* 	exit(1); */
/*       } */

      for ( k = 0; k < gvariables[delvar].num_vals; k++ ) {
	if ( gvariables[delvar].vals[k] == -1 ) {
	  break;
	}
      }
      if ( k == gvariables[delvar].num_vals ) {
	printf("\n\nVarVal sanity: delvar val no pre, no add, no OTHER val?\n\n");
	exit(1);
      }
     
      gop_conn[op].eff[gop_conn[op].num_eff].var = delvar;
      gop_conn[op].eff[gop_conn[op].num_eff].val = k;
      gop_conn[op].num_eff++;
    } /* endfor i over deletes */

  } /* endfor op over ops */

/*   if ( ldebug ) { */
/*     printf("\n\n========================OPs using Variables:\n"); */
/*     for ( op = 0; op < gnum_op_conn; op++ ) { */
/*       if ( gop_conn[op].num_E == 0 ) { */
/* 	continue; */
/*       } */
/*       print_op_name(op); */
/*       printf(": "); */
/*       for ( i = 0; i < gop_conn[op].num_pre; i++ ) { */
/* 	print_Variable_Value(gop_conn[op].pre[i].var, gop_conn[op].pre[i].val, TRUE); */
/* 	if ( i < gop_conn[op].num_pre - 1 ) { */
/* 	  printf(", "); */
/* 	} */
/*       } */
/*       printf(" --> "); */
/*       for ( i = 0; i < gop_conn[op].num_eff; i++ ) { */
/* 	print_Variable_Value(gop_conn[op].eff[i].var, gop_conn[op].eff[i].val, TRUE); */
/* 	if ( i < gop_conn[op].num_eff - 1 ) { */
/* 	  printf(", "); */
/* 	} */
/*       } */
/*       printf("\n"); */
/*     } */
/*   }  */

  for ( op = 0; op < gnum_op_conn; op++ ) {
    gop_conn[op].pre_on_var = ( int * ) calloc( gnum_variables, sizeof(int));
    gop_conn[op].eff_on_var = ( int * ) calloc( gnum_variables, sizeof(int));

    /* assign memory also to the useless ops... just to avoid any seg
     * faults in case I forgot somewhere to catch this special case...
     */
    if ( gop_conn[op].num_E == 0 ) {
      continue;
    }

    for ( i = 0; i < gnum_variables; i++ ) {
      gop_conn[op].pre_on_var[i] = -1;
      gop_conn[op].eff_on_var[i] = -1;

      for ( j = 0; j < gop_conn[op].num_pre; j++ ) {
	gop_conn[op].pre_on_var[gop_conn[op].pre[j].var] = gop_conn[op].pre[j].val;
      }

      for ( j = 0; j < gop_conn[op].num_eff; j++ ) {
	gop_conn[op].eff_on_var[gop_conn[op].eff[j].var] = gop_conn[op].eff[j].val;
      }
    }
  }

/*   if ( ldebug ) { */
/*     printf("\n\n========================OPs using Variables, Cross-check:\n"); */
/*     for ( op = 0; op < gnum_op_conn; op++ ) { */
/*       if ( gop_conn[op].num_E == 0 ) { */
/* 	continue; */
/*       } */
/*       print_op_name(op); */
/*       printf(" PRE:\n"); */
/*       for ( i = 0; i < gnum_variables; i++ ) { */
/* 	print_Variable(i); */
/* 	printf(": "); */
/* 	if ( gop_conn[op].pre_on_var[i] == -1 ) { */
/* 	  printf(" NO-PRE"); */
/* 	} else { */
/* 	  print_Variable_Value(i, gop_conn[op].pre_on_var[i], FALSE); */
/* 	} */
/* 	printf("\n"); */
/*       } */
/*       print_op_name(op); */
/*       printf(" EFF:\n"); */
/*       for ( i = 0; i < gnum_variables; i++ ) { */
/* 	print_Variable(i); */
/* 	printf(": "); */
/* 	if ( gop_conn[op].eff_on_var[i] == -1 ) { */
/* 	  printf(" NO-EFF"); */
/* 	} else { */
/* 	  print_Variable_Value(i, gop_conn[op].eff_on_var[i], FALSE); */
/* 	} */
/* 	printf("\n"); */
/*       } */
/*     } */
/*   } */

}






















/**********************
 * Now read off the SG and the DTGs, from all this
 **********************/
























/* ATTENTION!  This guy relies on that the order of SG nodes in gSG is
 * same as that of gvariables! same for order of DTG nodes in each
 * DTG, and the values of the respective variable.
 */
void create_SG_DTG( void )

{

  int var, op, node, val;
  int pre, eff, prevar, effvar, effval, preval;
  int i, j;
  int ef;
  DTGTransition *t;



  /* First create the DTGs ...
   */
  gDTGs = ( DTG * ) calloc(gnum_variables, sizeof( DTG ));

  for ( var = 0; var < gnum_variables; var++ ) {
    gDTGs[var].var = var;

    gDTGs[var].nodes = 
      ( DTGNode * ) calloc(gvariables[var].num_vals, sizeof(DTGNode));
    gDTGs[var].num_nodes = gvariables[var].num_vals;
    gDTGs[var].num_transitions = 0;
    
    for ( val = 0; val < gvariables[var].num_vals; val++ ) {
      gDTGs[var].nodes[val].var = var;
      gDTGs[var].nodes[val].val = val;

      gDTGs[var].nodes[val].num_in = 0;
      gDTGs[var].nodes[val].num_out = 0;
    }
  }
  
  /* first pass over ops: just count the number of in/out transitions,
   * overall and in each DTGNode
   *
   * also care about the eff_DTG_transitions structure here!
   */
  for ( op = 0; op < gnum_op_conn; op++ ) {
    if ( gop_conn[op].num_E == 0 ) {
      continue;
    }

    gop_conn[op].num_eff_DTG_transitions = 
      ( int * ) calloc( gop_conn[op].num_eff, sizeof( int ) );

    for ( eff = 0; eff < gop_conn[op].num_eff; eff++ ) {

      gop_conn[op].num_eff_DTG_transitions[eff] = 0;

      effvar = gop_conn[op].eff[eff].var;
      effval = gop_conn[op].eff[eff].val;
      preval = gop_conn[op].pre_on_var[effvar];
      if ( preval != -1 ) {
	gDTGs[effvar].nodes[preval].num_out++;
	gDTGs[effvar].nodes[effval].num_in++;
	gDTGs[effvar].num_transitions++;
	gop_conn[op].num_eff_DTG_transitions[eff] = 1;
      } else {
	/* see explanation of this below.
	 */
	if ( gvariables[effvar].vals[effval] != -1 ) {
	  for ( j = 0; j < gvariables[effvar].num_vals; j++ ) {
	    if ( gvariables[effvar].vals[j] == -1 ) {
	      gDTGs[effvar].nodes[j].num_out++;
	      gDTGs[effvar].nodes[effval].num_in++;
	      gDTGs[effvar].num_transitions++;
	      gop_conn[op].num_eff_DTG_transitions[eff]++;
	      break;
	    }
	  }
	}
	ef = gop_conn[op].E[0];
	for ( j = 0; j < gef_conn[ef].num_D; j++ ) {
	  if ( effvar == gft_conn[gef_conn[ef].D[j]].var ) {/* doesn't happen for notFD */
	    if ( effval == gft_conn[gef_conn[ef].D[j]].val ) {/* doesn't happen for notFD */
	      printf("\nsame var both added and deleted??\n\n");
	      exit(1);
	    }
	    if ( gft_conn[gef_conn[ef].D[j]].val == -1 ) {
	      printf("\ngft_conn[gef_conn[ef].D[j]].val == -1??\n\n");
	      exit(1);
	    }
	    gDTGs[effvar].nodes[gft_conn[gef_conn[ef].D[j]].val].num_out++;
	    gDTGs[effvar].nodes[effval].num_in++;
	    gDTGs[effvar].num_transitions++;
	    gop_conn[op].num_eff_DTG_transitions[eff]++;
	  }
	}

/* 	for ( val = 0; val < gDTGs[effvar].num_nodes; val++ ) { */
/* 	  if ( val == effval ) { */
/* 	    continue; */
/* 	  } */
/* 	  gDTGs[effvar].nodes[val].num_out++; */
/* 	  gDTGs[effvar].nodes[effval].num_in++; */
/* 	  gDTGs[effvar].num_transitions++; */
/* 	} */
      }
    }
  }

  /* now allocate the necessary memory based on these counts
   */
  for ( var = 0; var < gnum_variables; var++ ) {
    if ( gDTGs[var].num_transitions > 0 ) {
      gDTGs[var].transitions = ( DTGTransition * ) 
	calloc(gDTGs[var].num_transitions, sizeof(DTGTransition));
    }
    gDTGs[var].num_transitions = 0;

    for ( val = 0; val < gvariables[var].num_vals; val++ ) {
      if ( gDTGs[var].nodes[val].num_in > 0 ) {
	gDTGs[var].nodes[val].in = 
	  ( DTGTransition_pointer * ) 
	  calloc(gDTGs[var].nodes[val].num_in,sizeof(DTGTransition_pointer));
      }
      if ( gDTGs[var].nodes[val].num_out > 0 ) {
	gDTGs[var].nodes[val].out = 
	  ( DTGTransition_pointer * ) 
	  calloc(gDTGs[var].nodes[val].num_out,sizeof(DTGTransition_pointer)); 
      }

      /* re-initialize counters, for upcoming pass
       */
      gDTGs[var].nodes[val].num_in = 0;
      gDTGs[var].nodes[val].num_out = 0;
    }
  }
  
  /* second pass over ops: insert the transitions!
   */
  for ( op = 0; op < gnum_op_conn; op++ ) {
    if ( gop_conn[op].num_E == 0 ) {
      continue;
    }

    gop_conn[op].eff_DTG_transitions = 
      ( DTGTransition_pointer ** ) calloc( gop_conn[op].num_eff, 
					   sizeof( DTGTransition_pointer * ) );

    for ( eff = 0; eff < gop_conn[op].num_eff; eff++ ) {

      gop_conn[op].eff_DTG_transitions[eff] = 
      ( DTGTransition_pointer * ) calloc( gop_conn[op].num_eff_DTG_transitions[eff], 
					  sizeof( DTGTransition_pointer ) );
      gop_conn[op].num_eff_DTG_transitions[eff] = 0;

      effvar = gop_conn[op].eff[eff].var;
      effval = gop_conn[op].eff[eff].val;
      preval = gop_conn[op].pre_on_var[effvar];
      if ( preval != -1 ) {
	/* insert transition effvar/preval to effvar/effval
	 */
	insert_DTG_transition(effvar, preval, effval, op, eff);
      } else {
	/* if an added var does not have a precondition then we need
	 * DTG transitions ONLY from those values that are in the
	 * delete list! if a value is not deleted, then in exec state
	 * this value of the var could be true, and then the op would
	 * result in the var having two values, in contradiction to
	 * what FD proved about the var.
	 *
	 * For OTHER -- if it exists -- there is the special case
	 * handling that, unless the add effect itself is OTHER, this
	 * is considered to be a "delete" of the added real value.
	 *
	 * ATTENTION!! This changes the def of "DTG". An undesired
	 * side effect it has is that it is no longer true that an
	 * irrelevant fact cannot lie on a shortest path in the
	 * DTG. example ferry: if the "car in ferry" value of the car
	 * var is OTHER, then this occurs in no pre and the transition
	 * of board is irrelevant -- which is a priori correct because
	 * the car var will have transitions applying board even in
	 * states where OTHER is not true, thus side-stepping the
	 * transition to OTHER. However, these spurious transitions
	 * are removed in here. Therefore, need to re-define "relevant
	 * transition (c,c')" to expliccitly check whether or not, for
	 * all c'' where we have (c',c''), there exists also (c,c'').
	 */
	if ( gvariables[effvar].vals[effval] != -1 ) {
	  for ( j = 0; j < gvariables[effvar].num_vals; j++ ) {
	    if ( gvariables[effvar].vals[j] == -1 ) {
	      insert_DTG_transition(effvar, j, effval, op, eff);
	      break;
	    }
	  }
	}
	ef = gop_conn[op].E[0];
	for ( j = 0; j < gef_conn[ef].num_D; j++ ) {
	  if ( effvar == gft_conn[gef_conn[ef].D[j]].var ) {
	    insert_DTG_transition(effvar,
				  gft_conn[gef_conn[ef].D[j]].val,
				  effval,
				  op,
				  eff);
	  }
	}

/* 	for ( val = 0; val < gDTGs[effvar].num_nodes; val++ ) { */
/* 	  if ( val == effval ) { */
/* 	    continue; */
/* 	  } */
/* 	  insert_DTG_transition(effvar, val, effval, op); */
/* 	} */
      }
    }
  }

/*   if ( ldebug ) { */
/*     printf("\n\n========================DOMAIN TRANSITION GRAPHS:\n"); */
/*     for ( var = 0; var < gnum_variables; var++ ) { */
/*       printf("\nVariable %d: ", var); */
/*       print_Variable(var); */
/*       printf("\n"); */
/*       print_DTG(var); */
/*     } */
/*   } */




  /* ... then determine which of their transitions are irrelevant
   *
   * NOTE: this was previously in determine_SG_DTG_static_properties(
   * void ), had to move it here because for revise def of SG we
   * already need to know which transitions are actually relevant.
   */
  determine_DTGt_irrelevant();



  /* ... now create the SG!
   *
   * MUST do this last because we first need to know which transitions
   * are irrelevant!
   */
  gSG.nodes = ( SGNode * ) calloc(gnum_variables, sizeof( SGNode ));
  /*simply assume that vars*vars won't be too big for our memory...
   */
  gSG.edges = ( SGEdge * ) 
    calloc(gnum_variables * gnum_variables, sizeof( SGEdge ));

  for ( var = 0; var < gnum_variables; var++ ) {
    gSG.nodes[var].var = var;
    gSG.nodes[var].IN = TRUE;

    gSG.nodes[var].pred = 
      ( SGEdge_pointer * ) calloc(gnum_variables, sizeof( SGEdge_pointer ));
    gSG.nodes[var].num_pred = 0;
    gSG.nodes[var].succ = 
      ( SGEdge_pointer * ) calloc(gnum_variables, sizeof( SGEdge_pointer ));
    gSG.nodes[var].num_succ = 0;
  }
  gSG.num_nodes = gnum_variables;
  gSG.num_edges = 0;

  /* fill in the adjacency matrix while we're doing this...
   * serves also for quick duplicate check.
   */
  gSG.adj_matrix = ( Bool ** ) calloc(gSG.num_nodes, sizeof( Bool * ));
  for ( i = 0; i < gSG.num_nodes; i++ ) {
    gSG.adj_matrix[i] = ( Bool * ) calloc(gSG.num_nodes, sizeof( Bool ));
    for ( j = 0; j < gSG.num_nodes; j++ ) {
      gSG.adj_matrix[i][j] = FALSE;
    }
  }

  for ( var = 0; var < gnum_variables; var++ ) {
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);
      
      if ( t->irrelevant ) {
	continue;
      }

      effvar = t->end->var;

      for ( j = 0; j < t->num_conditions; j++ ) {
	prevar = t->conditions[j]->var;

	if ( prevar == effvar ) {
	  printf("\nSG building: prevar == effvar??\n\n");
	  exit(1);
	}

	/* have a dependency from prevar to effvar
	 * First see whether that dependency was already recorded
	 */
	if ( gSG.adj_matrix[prevar][effvar] ) {
	  continue;
	}
	
	/* this successor hasn't yet been recorded, thus dependency is
	 * new. add it.
	 */
	gSG.adj_matrix[prevar][effvar] = TRUE;
	
	gSG.edges[gSG.num_edges].start = &(gSG.nodes[prevar]);
	gSG.edges[gSG.num_edges].end = &(gSG.nodes[effvar]);
	gSG.edges[gSG.num_edges].IN = TRUE;
	
	gSG.nodes[prevar].succ[gSG.nodes[prevar].num_succ] = &(gSG.edges[gSG.num_edges]);
	gSG.nodes[prevar].num_succ++;
	gSG.nodes[effvar].pred[gSG.nodes[effvar].num_pred] = &(gSG.edges[gSG.num_edges]);
	gSG.nodes[effvar].num_pred++;
	
	gSG.num_edges++;
      }
    }
  }


  /* OLD version based on ops rather than DTG transitions
   */
/*   for ( op = 0; op < gnum_op_conn; op++ ) { */
/*     if ( gop_conn[op].num_E == 0 ) { */
/*       continue; */
/*     } */

/*     for ( pre = 0; pre < gop_conn[op].num_pre; pre++ ) { */
/*       for ( eff = 0; eff < gop_conn[op].num_eff; eff++ ) { */
/* 	if ( gop_conn[op].pre[pre].var == gop_conn[op].eff[eff].var ) { */
/* 	  /\* no edge from var to itself... */
/* 	   *\/ */
/* 	  continue; */
/* 	} */

/* 	prevar = gop_conn[op].pre[pre].var; */
/* 	effvar = gop_conn[op].eff[eff].var; */

/* 	/\* have a dependency from prevar to effvar */
/* 	 * First see whether that dependency was already recorded */
/* 	 *\/ */
/* 	for ( i = 0; i < gSG.nodes[prevar].num_succ; i++ ) { */
/* 	  if ( gSG.nodes[prevar].succ[i]->end->var == effvar ) { */
/* 	    break; */
/* 	  } */
/* 	} */
/* 	if ( i < gSG.nodes[prevar].num_succ ) { */
/* 	  continue;/\* look at next effect *\/ */
/* 	} */

/* 	/\* this successor hasn't yet been recorded, thus dependency is */
/* 	 * new. add it. */
/* 	 *\/ */
/* 	gSG.edges[gSG.num_edges].start = &(gSG.nodes[prevar]); */
/* 	gSG.edges[gSG.num_edges].end = &(gSG.nodes[effvar]); */
/* 	gSG.edges[gSG.num_edges].IN = TRUE; */

/* 	gSG.nodes[prevar].succ[gSG.nodes[prevar].num_succ] = &(gSG.edges[gSG.num_edges]); */
/* 	gSG.nodes[prevar].num_succ++; */
/* 	gSG.nodes[effvar].pred[gSG.nodes[effvar].num_pred] = &(gSG.edges[gSG.num_edges]); */
/* 	gSG.nodes[effvar].num_pred++; */

/* 	gSG.num_edges++; */
/*       } */
/*     } */
/*   } */

/*   if ( ldebug ) { */
/*     printf("\n\n========================SUPPORT GRAPH:\n"); */
/*     print_SG(); */
/*   } */



}



void insert_DTG_transition( int var, int start, int end, int op, int eff )

{

  DTGTransition *t;
  int i;


  t = &(gDTGs[var].transitions[gDTGs[var].num_transitions]);
  gDTGs[var].num_transitions++;


  t->start = &(gDTGs[var].nodes[start]);
  t->end = &(gDTGs[var].nodes[end]);
/*   printf("\nTransition for op: "); */
/*   print_op_name(op); */
/*   printf("\nstart: "); */
/*   print_Variable_Value(t->start->var, t->start->val, TRUE); */
/*   printf("\nend: "); */
/*   print_Variable_Value(t->end->var, t->end->val, TRUE); */
/*   fflush(stdout); */

  t->rop = op;

  t->num_conditions = 0;
  if ( gop_conn[op].num_pre > 0 ) {
    t->conditions = ( DTGNode_pointer * ) 
      calloc( gop_conn[op].num_pre, sizeof(DTGNode_pointer));
  }
  for ( i = 0; i < gop_conn[op].num_pre; i++ ) {
    if ( gop_conn[op].pre[i].var == var ) {
      /* transition condition stores only *outside* conds!
       */
      continue;
    }
/*     printf("\ncond: "); */
/*     print_Variable_Value(gDTGs[gop_conn[op].pre[i].var].nodes[gop_conn[op].pre[i].val].var,  */
/* 			 gDTGs[gop_conn[op].pre[i].var].nodes[gop_conn[op].pre[i].val].val,  */
/* 			 TRUE); */
/*     fflush(stdout); */
    t->conditions[t->num_conditions] = 
      &(gDTGs[gop_conn[op].pre[i].var].nodes[gop_conn[op].pre[i].val]);
    t->num_conditions++;
  }

  t->num_side_effects = 0;
  if ( gop_conn[op].num_eff > 0 ) {
    t->side_effects = ( DTGNode_pointer * ) 
      calloc( gop_conn[op].num_eff, sizeof(DTGNode_pointer));
  }
  for ( i = 0; i < gop_conn[op].num_eff; i++ ) {
    if ( gop_conn[op].eff[i].var == var ) {
      /* transition side effects store only *outside* effs!
       */
      continue;
    }
/*     printf("\nseff: "); */
/*     print_Variable_Value(gDTGs[gop_conn[op].eff[i].var].nodes[gop_conn[op].eff[i].val].var,  */
/* 			 gDTGs[gop_conn[op].eff[i].var].nodes[gop_conn[op].eff[i].val].val,  */
/* 			 TRUE); */
/*     fflush(stdout); */
    t->side_effects[t->num_side_effects] = 
      &(gDTGs[gop_conn[op].eff[i].var].nodes[gop_conn[op].eff[i].val]);
    t->num_side_effects++;
  }
  
  gDTGs[var].nodes[start].out[gDTGs[var].nodes[start].num_out] = t;
  gDTGs[var].nodes[start].num_out++;
  gDTGs[var].nodes[end].in[gDTGs[var].nodes[end].num_in] = t;
  gDTGs[var].nodes[end].num_in++;



  /* finally insert this bugger into the eff_DTG_transitions structure!
   */
  gop_conn[op].eff_DTG_transitions[eff][gop_conn[op].num_eff_DTG_transitions[eff]] = t;
  gop_conn[op].num_eff_DTG_transitions[eff]++;
  
}



























/**********************
 * set all the static properties of SG and DTGs
 **********************/

























void determine_SG_DTG_static_properties( void )

{

  determine_SG_acyclic();

  determine_DTGt_invertible();
  determine_DTGt_no_side_effects();
  /* moved up ahead after DTG building, in front of SG building
   */
/*   determine_DTGt_irrelevant(); */
  determine_DTGt_irrelevant_own_delete();
  determine_DTGt_irrelevant_side_effect_deletes();
  determine_DTGt_replacable_side_effect_deletes();
  determine_DTGt_irrelevant_side_effects();
  determine_DTGt_recoverable_side_effect_deletes();

  determine_DTG_overall();

  determine_DTG_diameters();
  determine_DTG_maxdiameters();

}



void determine_SG_acyclic( void )

{

  int i, j;

	  

  /* moved above into building of SG (served as duplicate check there)
   */
/*   /\* first, fill in the adjacency matrix */
/*    *\/ */
/*   gSG.adj_matrix = ( Bool ** ) calloc(gSG.num_nodes, sizeof( Bool * )); */
/*   for ( i = 0; i < gSG.num_nodes; i++ ) { */
/*     gSG.adj_matrix[i] = ( Bool * ) calloc(gSG.num_nodes, sizeof( Bool )); */
/*     for ( j = 0; j < gSG.num_nodes; j++ ) { */
/*       gSG.adj_matrix[i][j] = FALSE; */
/*     } */
/*   } */
/*   for ( i = 0; i < gSG.num_edges; i++ ) { */
/*     gSG.adj_matrix[gSG.edges[i].start->var][gSG.edges[i].end->var] = TRUE; */
/*   } */

  /* DISABLED! Was runtime critical in some benchmarks and, finally,
   * is used for NOTHING with the single exception of identifying
   * non-leaf goal vars for x0 in lDGs... which seems a rather useless
   * occupation anyhow...
   */

/*   /\* now compute the transitive hull. */
/*    *\/ */
/*   gSG.trans_adj_matrix = ( Bool ** ) calloc(gSG.num_nodes, sizeof( Bool * )); */
/*   for ( i = 0; i < gSG.num_nodes; i++ ) { */
/*     gSG.trans_adj_matrix[i] = ( Bool * ) calloc(gSG.num_nodes, sizeof( Bool )); */
/*     for ( j = 0; j < gSG.num_nodes; j++ ) { */
/*       gSG.trans_adj_matrix[i][j] = gSG.adj_matrix[i][j]; */
/*     } */
/*   } */

/*   for ( j = 0; j < gSG.num_nodes; j++ ) { */
/*     for ( i = 0; i < gSG.num_nodes; i++ ) { */
/*       if ( !gSG.trans_adj_matrix[i][j] ) { */
/* 	continue; */
/*       } */
/*       for ( k = 0; k < gSG.num_nodes; k++ ) { */
/* 	if ( !gSG.trans_adj_matrix[j][k] ) { */
/* 	  continue; */
/* 	} */
/* 	gSG.trans_adj_matrix[i][k] = TRUE; */
/* 	/\* 	  if ( ldebug ) { *\/ */
/* 	/\* 	    printf("\nSG new transitive edge: "); *\/ */
/* 	/\* 	    print_Variable(i); *\/ */
/* 	/\* 	    printf(" ===> "); *\/ */
/* 	/\* 	    print_Variable(k); *\/ */
/* 	/\* 	  } *\/ */
/*       } */
/*     } */
/*   } */


/*   /\* now determine based on non-reflexive transitive hull whether or */
/*    * not this guy contains a cycle. */
/*    *\/ */
/*   gSG.is_acyclic = TRUE; */
/*   for ( i = 0; i < gSG.num_nodes; i++ ) { */
/*     if ( gSG.trans_adj_matrix[i][i] ) { */
/*       gSG.is_acyclic = FALSE; */
/*       if ( gcmd_line.display_info == 2 ) { */
/* 	printf("\nSG node "); */
/* 	print_Variable(i); */
/* 	printf(" lies on a cycle."); */
/*       } */
/*     } */
/*   } */


  /* finally, make space for INsubgraph adjacency matrix.
   */
  gSG.IN_adj_matrix = ( Bool ** ) calloc(gSG.num_nodes, sizeof( Bool * ));
  for ( i = 0; i < gSG.num_nodes; i++ ) {
    gSG.IN_adj_matrix[i] = ( Bool * ) calloc(gSG.num_nodes, sizeof( Bool ));
    for ( j = 0; j < gSG.num_nodes; j++ ) {
      gSG.IN_adj_matrix[i][j] = FALSE;
    }
  }
 
}



void determine_DTGt_invertible( void )

{

  int var, i, j, k, l;
  DTGTransition *t, *tt;

  for ( var = 0; var < gnum_variables; var++ ) {
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);

      t->invertible = FALSE;
      t->inverted_by = NULL;

      /* is there an inverting transition? if so, it must be an
       * outgoing trans of t's end node
       */
      for ( j = 0; j < t->end->num_out; j++ ) {
	tt = t->end->out[j];
	/* does it go back to t's start?
	 */
	if ( tt->end->val != t->start->val ) {
	  continue;
	}

	/* is its outside condition contained in that of t?
	 */
	for ( k = 0; k < tt->num_conditions; k++ ) {
	  for ( l = 0; l < t->num_conditions; l++ ) {
	    if (t->conditions[l]->var == tt->conditions[k]->var &&
		t->conditions[l]->val == tt->conditions[k]->val ) {
	      break;
	    }
	  }
	  if ( l == t->num_conditions ) {
	    /* no, this one isn't present!
	     */
	    break;
	  }
	}
	if ( k < tt->num_conditions ) {
	  /* found bad condition! try next transition.
	   */
	  continue;
	}

	/* yes this is an inverse transition.
	 */
	t->invertible = TRUE;
	if ( t->inverted_by == NULL || 
	     tt->num_side_effects == 0 ) {
	  t->inverted_by = tt;
	}
      } /* endfor j, tt over potential inverses */

    } /* endfor i, t over transitions */

  } /* endfor var over vars */

}



void determine_DTGt_no_side_effects( void )

{

  int var, i;
  DTGTransition *t;

  for ( var = 0; var < gnum_variables; var++ ) {
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);

      if ( t->num_side_effects == 0 ) {
      	t->no_side_effects = TRUE;
      } else {
      	t->no_side_effects = FALSE;
      }
    }
  }

}



void determine_DTGt_irrelevant( void )

{

  int i, j, k;
  int var, ef, numops, relop, ft, op;
  Bool goal;
  DTGTransition *t, *tt, *ttt;

  /* first, set these meta-values for all ft in gft_conn
   *
   * NOTE: we can deal with this via gft_conn, ie "real" varvals only,
   * since OTHER does by def not occur in any op precs (as for those
   * where we inserted it in the above, cf discussion there).
   */
  for ( i = 0; i < gnum_ft_conn; i++ ) {
    numops = 0;
    relop = -1;
    for ( j = 0; j < gft_conn[i].num_PC; j++ ) {
      ef = gft_conn[i].PC[j];
      op = gef_conn[ef].op;
      if ( gop_conn[op].num_E == 0 ) {
	continue;
      }
      if ( numops == 0 ) {
	relop = op;
      }
      numops++;
    }
    goal = FALSE;
    if ( gft_conn[i].is_global_goal ) {
      goal = TRUE;
    }

    if ( goal ) {
      gft_conn[i].is_relevant = TRUE;
    }
    if ( numops > 0 ) {
      gft_conn[i].is_relevant = TRUE;
    }
    if ( numops == 1 && !goal ) {
      gft_conn[i].is_relevant_only_for = relop;
    } else {
      gft_conn[i].is_relevant_only_for = -1;
    }

/*     printf("\n"); print_ft_name(i); */
/*     printf(" --- rel: %d relfor: %d",  */
/* 	   gft_conn[i].is_relevant,  */
/* 	   gft_conn[i].is_relevant_only_for); */
  } /* endfor i over gft_conn */




  /* NOT valid with sharper def of DTGs!! See footnotes in draft, with
   * def of DTG and with def of irrelevant trans in new_DG.
   */
/*   /\* now, make a pass over the transition and simply check whether or */
/*    * not their end varval is relevant. */
/*    *\/ */
/*   for ( var = 0; var < gnum_variables; var++ ) { */
/*     for ( i = 0; i < gDTGs[var].num_transitions; i++ ) { */
/*       t = &(gDTGs[var].transitions[i]); */
/*       ft = gvariables[t->end->var].vals[t->end->val]; */
/*       if ( ft == -1 ) { */
/* 	t->irrelevant = TRUE; */
/* 	continue; */
/*       } */
/*       if ( gft_conn[ft].is_relevant ) { */
/* 	t->irrelevant = FALSE; */
/*       } else { */
/* 	t->irrelevant = TRUE; */
/*       } */
/*     } */
/*   }   */

  /* Instead, simply test whether the transition can always be
   * by-passed directly, with the same responsible op.
   */
  for ( var = 0; var < gnum_variables; var++ ) {
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);

/*       if ( ggoal_on_var[var] == t->end->val ) { */
/* 	/\* transitions into goal values are of course relevant. */
/* 	 *\/ */
/* 	t->irrelevant = FALSE; */
/* 	continue; */
/*       } */
      /* actually, need to test for relevance, not only for goal!! ts
       * ts.
       */
      ft = gvariables[t->end->var].vals[t->end->val];
      if ( ft != -1 && gft_conn[ft].is_relevant ) {
	/* transitions into goal values are of course relevant.
	 */
	t->irrelevant = FALSE;
	continue;
      }


      /* Fact itself not marked as relevant; need to look at all
       * outgoing transitions tt of t->end that lead to a third value,
       * to make sure this really works.
       */
      for ( j = 0; j < t->end->num_out; j++ ) {
	tt = t->end->out[j];

	if ( tt->end == t->start ) {
	  /* this guy just goes back to where we are. no need to by-pass it!
	   */
	  continue;
	}

	/* Can we by-pass tt from t->start?
	 */
	for ( k = 0; k < t->start->num_out; k++ ) {
	  ttt = t->start->out[k];

	  if ( ttt->end != tt->end ) {
	    /* No. Does not have same end point.
	     */
	    continue;
	  }
	  
	  if ( ttt->rop != tt->rop ) {
	    /* No. Uses a different operator.
	     */
	    continue;
	  }
	  
	  /* Yes, got it.
	   */
	  break;
	} /* endfor k, ttt over possible bypassing transitions */
	
	if ( k == t->start->num_out ) {
	  /* No! This tt cannot be bypassed.
	   */
	  break;
	}
      } /* j, tt over to-be-bypassed transitions */

      if ( j < t->end->num_out ) {
	/* found "bad" tt
	 */
	t->irrelevant = FALSE;
      } else {
	t->irrelevant = TRUE;
      }
    } /* i, t over all transitions of var */
  } /* var over all variables */
  

}



void determine_DTGt_irrelevant_own_delete( void )

{

  int var, i, ft;
  DTGTransition *t;

  for ( var = 0; var < gnum_variables; var++ ) {
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);
      ft = gvariables[t->start->var].vals[t->start->val];

      if ( ft == -1 ) {
	t->irrelevant_own_delete = TRUE;
	continue;
      }

      if ( !gft_conn[ft].is_relevant ) {
	t->irrelevant_own_delete = TRUE;
	continue;
      }    

      if ( gft_conn[ft].is_relevant_only_for != -1 &&
	   gft_conn[ft].is_relevant_only_for == t->rop ) {
	t->irrelevant_own_delete = TRUE;
	continue;
      } 
      
      t->irrelevant_own_delete = FALSE;
    }
  }

}



void determine_DTGt_irrelevant_side_effect_deletes( void )

{

  int var, i, j, k;
  DTGTransition *t;
  DTGNode *seff;
  int ctxvar, ctxval, ctxft;


  /* first collect the contexts for all transitions.
   */
  for ( var = 0; var < gnum_variables; var++ ) {
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);

      /* no need if there are no side effects anyway!
       */
      if ( t->no_side_effects ) {
	t->num_contexts = 0;
	continue;
      }

      if ( t->num_side_effects == 0 ) {
	printf("\nbuilding context w/o side effects?\n\n");
	exit(1);
      }
      t->context = ( DTGNode_pointer ** ) 
	calloc(t->num_side_effects, sizeof( DTGNode_pointer * ));
      t->num_context = ( int * ) 
	calloc(t->num_side_effects, sizeof( int ));
      t->num_contexts = 0;

      for ( j = 0; j < t->num_side_effects; j++ ) {
	seff = t->side_effects[j];

	/* is there a pre on this side eff?
	 */
	for ( k = 0; k < t->num_conditions; k++ ) {
	  if ( t->conditions[k]->var == seff->var ) {
	    break;
	  }
	}
	if ( k < t->num_conditions ) {
	  /* yes: insert this as the only context for this var!
	   */
	  t->context[t->num_contexts] = ( DTGNode_pointer * ) 
	    calloc(1, sizeof( DTGNode_pointer ));
	  t->context[t->num_contexts][0] = t->conditions[k];
	  t->num_context[t->num_contexts] = 1;
	  t->num_contexts++;
	  continue;
	}
	
	/* no: insert all other var vals as context facts!
	 */
	t->context[t->num_contexts] = ( DTGNode_pointer * ) 
	  calloc(gDTGs[seff->var].num_nodes, sizeof( DTGNode_pointer ));
	t->num_context[t->num_contexts] = 0;
	for ( k = 0; k < gDTGs[seff->var].num_nodes; k++ ) {
	  if ( gDTGs[seff->var].nodes[k].val == seff->val ) {
	    continue;
	  }
	  t->context[t->num_contexts][t->num_context[t->num_contexts]] = 
	    &(gDTGs[seff->var].nodes[k]);
	  t->num_context[t->num_contexts]++;
	}
	t->num_contexts++;
      } /* endfor j over side effects */
    } /* endfor i over transitions */
  } /* endfor var over variables */




  /* now verify whether all context facts are irrelevant or rop-only
     relevant.
   */
  for ( var = 0; var < gnum_variables; var++ ) {
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);

      /* no side effs implies irrelevant_side_effect_deletes!
       */
      if ( t->no_side_effects ) {
	t->self_irrelevant_side_effect_deletes = TRUE;
	t->irrelevant_side_effect_deletes = TRUE;
	continue;
      }

      /* as yet we have not found a problem...
       */
      t->self_irrelevant_side_effect_deletes = TRUE;
      t->irrelevant_side_effect_deletes = TRUE;

      /* ... do we find one?
       */
      for ( j = 0; j < t->num_contexts; j++ ) {
	if ( t->num_context[j] == 0 ) {
	  printf("\nempty context??\n\n");
	  exit(1);
	}
	ctxvar = t->context[j][0]->var;

	for ( k = 0; k < t->num_context[j]; k++ ) {
	  ctxval = t->context[j][k]->val;
	  ctxft = gvariables[ctxvar].vals[ctxval];

	  if ( ctxft == -1 ) {
	    continue;
	  }
	  if ( !gft_conn[ctxft].is_relevant ) {
	    continue;
	  }  

	  /* this fact is needed somewhere! strong condition not given!
	   */
	  t->irrelevant_side_effect_deletes = FALSE;

	  if ( gft_conn[ctxft].is_relevant_only_for != -1 &&
	       gft_conn[ctxft].is_relevant_only_for == t->rop ) {
	    continue;
	  } 
	  t->self_irrelevant_side_effect_deletes = FALSE;
      
	  /* found a relevant ctxft! 
	   */
	  break;
	}
	if ( k < t->num_context[j] ) {
	  /* found a relevant ctxft! 
	   */
	  break;
	}
      } /* endfor j over ctx vars */

    } /* endfor i over transitions */
  } /* endfor var over vars */

}



/*
 * DEF: 
 *
\item has {\em replacable side effect deletes} iff $\context(c,c')
  \cap \goal = \emptyset$ and, for every $\rop(c,c') \neq \op \in
  \ops$ where $\pre_{\op} \cap \context(c,c') \neq \emptyset$ there
  exists $\op' \in \ops$ so that $\eff_{\op'} = \eff_{\op}$ and
  $\pre_{\op'} \subseteq \prevail_{\rop(c,c')} \cup
  \eff_{\rop(c,c')}$.
 *
 */
void determine_DTGt_replacable_side_effect_deletes( void )

{

  int var, i, j, k;
  DTGTransition *t;
  int ctxvar, ctxval, ctxft;

  for ( var = 0; var < gnum_variables; var++ ) {
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);

      /* no side effs and self_irrelevant_side_effects imply
       * replacable_side_effects!
       */
      if ( t->no_side_effects ||
	   t->self_irrelevant_side_effect_deletes ) {
	t->replacable_side_effect_deletes = TRUE;
	continue;
      }

      /* to save time: run the full test ONLY if there is only one
       * side effect... else, this can be very costly... and it
       * applies only rarely anyhow.
       */
      if ( t->num_contexts > 1 || t->num_context[0] > 1 ) {
	t->replacable_side_effect_deletes = FALSE;
	continue;	
      }

      for ( j = 0; j < t->num_contexts; j++ ) {
	if ( t->num_context[j] == 0 ) {
	  printf("\nempty context??\n\n");
	  exit(1);
	}
	ctxvar = t->context[j][0]->var;

	for ( k = 0; k < t->num_context[j]; k++ ) {
	  ctxval = t->context[j][k]->val;
	  ctxft = gvariables[ctxvar].vals[ctxval];

	  if ( ctxft == -1 ) {
	    /* nobody relies on this guy, don't care!
	     */
	    continue;
	  }

	  if ( !gft_conn[ctxft].is_relevant ||
	       (gft_conn[i].is_relevant_only_for != -1 && 
		gft_conn[i].is_relevant_only_for == t->rop) ) {
	    /* nobody relies on this, except perhaps t->rop itself.
	     */
	    continue;
	  }

	  /* is this a goal? ... can't happen with what we just tested. anyway...
	   */
	  if ( gft_conn[ctxft].is_global_goal ) {
	    break;
	  }

	  /* are there any non-replacable ops != rop relying on it?
	   */
	  if ( !is_replacable_precond( ctxft, t->rop ) ) {
	    break;
	  }

	} /* endfor k, ctxval, ctxft over context facts in var j */

	if ( k < t->num_context[j] ) {
	  break;
	}

      } /* endfor j, ctxvar over ctx vars */

      if ( j < t->num_contexts ) {
	/* found a bad seff fact.
	 */
	t->replacable_side_effect_deletes = FALSE;
      } else {
	/* all seff facts dealt with successfully.
	 */
	t->replacable_side_effect_deletes = TRUE;
      }

    } /* endfor i, t over transitions in DTG(var) */

  } /* endfor var over all vars */

}



Bool is_replacable_precond( int ft, int rop ) 

{

  int i, j, k;
  int op, ef, efft, minA, minefft;
  int op_prime;

/*   if ( 1 ) { */
/*     printf("\nis_replacable_precond for "); */
/*     print_ft_name(ft); */
/*     printf(" and "); */
/*     print_op_name(rop); */
/*   } */
  
  for ( i = 0; i < gft_conn[ft].num_PC; i++ ) {
    op = gef_conn[gft_conn[ft].PC[i]].op;
    if ( gop_conn[op].num_E == 0 ) {
      continue;
    }
    ef = gop_conn[op].E[0];

    if ( op == rop ) {
      continue;
    }
/*     if ( 1 ) { */
/*       printf("\nendangered op "); */
/*       print_op_name(op); */
/*     } */
    
    /* now try to find a replacer!
     *
     * To not have to walk through all other ops, walk only through
     * those that add some effect of op -- the one with the min number
     * of adders.
     */
    minA = -1;
    efft = -1;
    for ( j = 0; j < gef_conn[ef].num_A; j++ ) {
      if ( minA == -1 || gft_conn[gef_conn[ef].A[j]].num_A < minA ) {
	minA = gft_conn[gef_conn[ef].A[j]].num_A;
	efft = gef_conn[ef].A[j];
      }
    }
/*     if ( efft == -1 ) { */
/*       printf("\nefft == -1??\n\n"); */
/*       exit(1); */
/*     } */
/*     if ( 1 ) { */
/*       printf("\nselected eff "); */
/*       print_ft_name(efft); */
/*     } */
/*     efft = gef_conn[ef].A[0]; */

    for ( j = 0; j < gft_conn[efft].num_A; j++ ) {
      op_prime = gef_conn[gft_conn[efft].A[j]].op;
      if ( gop_conn[op_prime].num_E == 0 ) {
	continue;
      }
/*       if ( 1 ) { */
/* 	printf("\ntesting op' "); */
/* 	print_op_name(op_prime); */
/*       } */
 
      if ( gop_conn[op_prime].num_eff != gop_conn[op].num_eff ) {
	continue;
      }

      if ( gop_conn[op_prime].num_pre >
	   gop_conn[op].num_pre + gop_conn[op].num_eff ) {
	continue;
      }
      
	   
      /* is eff of op_prime identical with eff of op?
       */
      for ( k = 0; k < gnum_variables; k++ ) {
	if ( gop_conn[op_prime].eff_on_var[k] != gop_conn[op].eff_on_var[k] ) {
	  break;
	}	
      }
      if ( k < gnum_variables ) {
	/* thus op_prime doesn't work, try next one.
	 */
/* 	if ( 1 ) { */
/* 	  printf("\neff(op') != eff(op)"); */
/* 	} */
	continue;
      }

      /* is pre of op_prime contained in prev(rop) \cup eff(rop)?
       */
      for ( k = 0; k < gnum_variables; k++ ) {
	if ( gop_conn[op_prime].pre_on_var[k] == -1 ) {
	  continue;
	}	
	if ( gop_conn[op_prime].pre_on_var[k] == gop_conn[rop].pre_on_var[k] &&
	     gop_conn[rop].eff_on_var[k] == -1 ) {
	  continue;
	}	
	if ( gop_conn[op_prime].pre_on_var[k] == gop_conn[rop].eff_on_var[k] ) {
	  continue;
	}	
	break;
      }
      if ( k < gnum_variables ) {
	/* thus op_prime doesn't work, try next one.
	 */
/* 	if ( 1 ) { */
/* 	  printf("\nprec(op') not in prev(rop) cup eff(rop)"); */
/* 	} */
	continue;
      }

      /* this is our man, for this op!
       */
/*       if ( 1 ) { */
/* 	printf("\nworks!"); */
/*       } */
      break;
    } /* endfor j, op_prime over adders of efft -- possible replacers */

    if ( j == gft_conn[efft].num_A ) {
      /* didn't find a replacer for this op!
       */
/*       if ( 1 ) { */
/* 	printf("\nsorry no replacer!"); */
/*       } */
      return FALSE;
    }

  } /* endfor i, op, ef over ops that have ft in their precondition */

  return TRUE;

}



void determine_DTGt_irrelevant_side_effects( void )

{

  int var, i, j;
  DTGTransition *t;
  DTGNode *seff;
  int seffft;

  for ( var = 0; var < gnum_variables; var++ ) {
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);

      /* no side effs implies irrelevant_side_effects!
       */
      if ( t->no_side_effects ) {
	t->irrelevant_side_effects = TRUE;
	continue;
      }

      for ( j = 0; j < t->num_side_effects; j++ ) {
	seff = t->side_effects[j];
	seffft = gvariables[seff->var].vals[seff->val];

	if ( seffft == -1 ) {
	  continue;
	}
	if ( !gft_conn[seffft].is_relevant ) {
	  continue;
	}    

	/* no need to test rop-only relevant here since ops with add
	 * in pre is not being generated. well, double-check.
	 */
	if ( gft_conn[seffft].is_relevant_only_for != -1 &&
	     gft_conn[seffft].is_relevant_only_for == t->rop ) {
	  printf("\nside effect is rop-only relevant?\n\n");
	  exit(1);
	}

	/* found a relevant seff-ft! break loop to indicate this.
	 */
	break;
      }

      if ( j < t->num_side_effects ) {
	/* found a relevant seff-ft!
	 */
	t->irrelevant_side_effects = FALSE;
      } else {
	/* all seff-fts are irrelevant!
	 */
	t->irrelevant_side_effects = TRUE;
      }

    } /* endfor i over transitions */
  } /* endfor var over vars */

}



/* need to recursively build all PSI, i.e., the possible combinations of
 * context facts.
 *
 * this here will be an array over all vars, storing which val this
 * var has in the current PSI, -1 if none.
 */
int *lPSIval_on_var;
/* for more effective processing, for the current transition this will
 * always store \prevail_{\rop(c,c')} \cup \eff_{\rop(c,c')}, in the
 * same format.
 *
 */
int *lprevail_eff_on_var;
/* collect recovery-ops...
 */
int *lrecoverers;
int lnum_recoverers;

void determine_DTGt_recoverable_side_effect_deletes( void )

{

  int var, i, j, k;
  DTGTransition *t;
  Bool success;
  int ft;

  lPSIval_on_var = ( int * ) calloc(gnum_variables, sizeof( int ));
  lprevail_eff_on_var = ( int * ) calloc(gnum_variables, sizeof( int ));
  lrecoverers = ( int * ) calloc(gnum_op_conn, sizeof( int ));

  for ( var = 0; var < gnum_variables; var++ ) {
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);

      /* no side effs implies recoverable_side_effect_deletes!
       */
      if ( t->no_side_effects ) {
	t->recoverable_side_effect_deletes = TRUE;
	continue;
      }

      /* same for irrelevant_side_effect_deletes!
       */
      if ( t->self_irrelevant_side_effect_deletes ) {
	t->recoverable_side_effect_deletes = TRUE;
	continue;
      }

      /* In case we ask for "irrelevant seff" not for "recoverer-only
       * relevant seff": If this guy doesn't have irrelevant side
       * effects anyway, then we will never use the "recoverable?"
       * information so there is no point in computing it!
       */
      if ( !gcmd_line.do_recoverer_only_relevant ) {
	if ( !t->irrelevant_side_effects ) {
	  t->recoverable_side_effect_deletes = FALSE; 
	  t->recoverer_only_relevant_side_effects = FALSE;
	  continue;
	}
      }



      /* setup prevail+eff
       */
      for ( j = 0; j < gnum_variables; j++ ) {
	lPSIval_on_var[j] = -1;

	lprevail_eff_on_var[j] = -1;
	/* is it a prevail?
	 */
	if ( gop_conn[t->rop].pre_on_var[j] != -1 && 
	     gop_conn[t->rop].eff_on_var[j] == -1 ) {
	  lprevail_eff_on_var[j] = gop_conn[t->rop].pre_on_var[j];
	}
	/* is it an effect?
	 */
	if ( gop_conn[t->rop].eff_on_var[j] != -1 ) {
	  lprevail_eff_on_var[j] = gop_conn[t->rop].eff_on_var[j];
	}
      }



      if ( gcmd_line.do_recoverer_only_relevant ) {
	/* run a quick test now, determining whether we can already
	 *  conclude that the seff will NOT be recoverer-only relevant
	 */
	for ( j = 0; j < t->num_side_effects; j++ ) {
	  ft = gvariables[t->side_effects[j]->var].vals[t->side_effects[j]->val];
	  if ( ft == -1 ) {
	    continue;
	  }
	  if ( gft_conn[ft].is_global_goal ) {
	    break;
	  }
	  for ( k = 0; k < gft_conn[ft].num_PC; k++ ) {
	    if ( gop_conn[gef_conn[gft_conn[ft].PC[k]].op].num_E == 0 ) {
	      /* this CAN happen! since we're going over ftconn here
	       * which does contain the empty-ops
	       */
	      continue;
	    }
	    if ( !is_potential_recoverer( t, gef_conn[gft_conn[ft].PC[k]].op ) ) {
	      break;
	    }
	  }
	  if ( k < gft_conn[ft].num_PC ) {
	    break;
	  }
	}
	if ( j < t->num_side_effects ) {
	  t->recoverer_only_relevant_side_effects = FALSE;
	  t->recoverable_side_effect_deletes = FALSE; 
	  continue;
	} 
      }
      


      lnum_recoverers = 0;
      success = recoverable_side_effect_deletes_testPSI( t, 0 );

      t->recoverable_side_effect_deletes = success;

      if ( success && gcmd_line.do_recoverer_only_relevant ) {
	if ( t->irrelevant_side_effects ) {
	  t->recoverer_only_relevant_side_effects = TRUE;
	  continue;
	}
	for ( j = 0; j < t->num_side_effects; j++ ) {
	  ft = gvariables[t->side_effects[j]->var].vals[t->side_effects[j]->val];
	  if ( ft == -1 ) {
	    continue;
	  }
	  if ( gft_conn[ft].is_global_goal ) {
	    break;
	  }
	  for ( k = 0; k < gft_conn[ft].num_PC; k++ ) {
	    if ( !gop_conn[gef_conn[gft_conn[ft].PC[k]].op].is_recoverer ) {
	      break;
	    }
	  }
	  if ( k < gft_conn[ft].num_PC ) {
	    break;
	  }
	}
	if ( j < t->num_side_effects ) {
	  t->recoverer_only_relevant_side_effects = FALSE;
	} else {
	  t->recoverer_only_relevant_side_effects = TRUE;
	}

	for ( j = 0; j < lnum_recoverers; j++ ) {
	  gop_conn[lrecoverers[j]].is_recoverer = FALSE;
	}
      } else {/* endif do rel-for-recoverers analysis */
	t->recoverer_only_relevant_side_effects = FALSE;
      }
      
    } /* endfor i over transitions */
  } /* endfor var over vars */

}



Bool recoverable_side_effect_deletes_testPSI( DTGTransition *t, 
					      int current_ctxvar_index )

{

  int i, j, ft, op;
  int current_var, current_val;
  static State tmpstate;
  static Bool fc = TRUE;
  Bool result;

  if ( fc ) {
    make_state( &tmpstate, gnum_ft_conn );

    fc = FALSE;
  }

  if ( current_ctxvar_index >= gnum_variables ) {
    printf("\ncurrent_ctxvar_index >= gnum_variables??\n\n");
    exit(1);
  }

  if ( current_ctxvar_index == t->num_contexts ) {
    /* do the actual testing:
     * 
     * there exists an operator $\op$ so that $\pre_\op \subseteq
     * \prevail_{\rop(c,c')} \cup \eff_{\rop(c,c')}$ and $\eff_\op
     * \subseteq \psi$, $\eff_\op \supseteq \{(y,d) \mid (y,d) \in
     * \psi, (y,d) \in \goal \cup \bigcup_{\rop(c,c') \neq \op' \in
     * \ops} \pre_{\op'}\}$.
     *
     */
    result = FALSE;

    /* to not have to actually iterate over all ops -- this would be
     *  square in transtions and ops, we look at only those ops where
     * \pre_\op \subseteq \prevail_{\rop(c,c')} \cup \eff_{\rop(c,c')}.
     * we collect them using the find-applicable-actions mechanism.
     */
    tmpstate.num_F = 0;
    for ( i = 0; i < gnum_variables; i++ ) {
      if ( lprevail_eff_on_var[i] != -1 ) {
	ft = gvariables[i].vals[lprevail_eff_on_var[i]];
	if ( ft != -1 ) {
	  /* dont use OTHER here, of course (no need to since no op
	   * pre contains this anyhow)
	   */
	  tmpstate.F[tmpstate.num_F] = ft;
	  tmpstate.num_F++;
	}
      }
    }
    get_A( &tmpstate );

    /* now we got what we want in gA!
     */
    for ( i = 0; i < gnum_A; i++ ) {
      op = gA[i];

      /* \eff_\op \subseteq \psi?
       */
      for ( j = 0; j < gnum_variables; j++ ) {
	if ( gop_conn[op].eff_on_var[j] != -1 &&
	     gop_conn[op].eff_on_var[j] != lPSIval_on_var[j] ) {
	  break;
	}
      }
      if ( j < gnum_variables ) {
	/* no! found a bad effect. try next op.
	 */
	continue;
      }

      /* \eff_\op \supseteq \{(y,d) \mid (y,d) \in \psi, (y,d) \in
       * \goal \cup \bigcup_{\rop(c,c') \neq \op' \in \ops}
       * \pre_{\op'}\}?
       */
      for ( j = 0; j < gnum_variables; j++ ) {
	if ( lPSIval_on_var[j] == -1 ) {
	  continue;
	}

	/* which fact are we talking about?
	 */
	ft = gvariables[j].vals[lPSIval_on_var[j]];

	/* if OTHER, it's not in goal or any op pre so we can skip.
	 */
	if ( ft == -1 ) {
	  continue;
	}
	/* if it's not relevant, we're fine too
	 */
	if ( !gft_conn[ft].is_relevant ) {
	  continue;
	}    
	/* if it's relevant, it may still be relevant only for rop
	 */
	if ( gft_conn[ft].is_relevant_only_for != -1 &&
	     gft_conn[ft].is_relevant_only_for == t->rop ) {
	  continue;
	} 

	/* now we have a context ft that is relevant outside rop. to
	 * qualify, op must recover this guy.
	 */
	if ( gop_conn[op].eff_on_var[j] != -1 &&
	     gop_conn[op].eff_on_var[j] == lPSIval_on_var[j] ) {
	  continue;
	}

	/* no! found a bad PSI fact! signal by breaking loop over vars.
	 */
	break;
      } /* endfor j over vars for testing recoverage of PSI */

      if ( j < gnum_variables ) {
	/* nope, found a bad PSI fact. try next op.
	 */
	continue;
      }     

      /* this is the man!
       */
/*       printf("\nfound recoverer! "); */
/*       print_op_name(op); */
/*       printf(" for "); */
/*       print_op_name(t->rop); */
/*       printf("\ncontext is: "); */
/*       for ( j = 0; j < gnum_variables; j++ ) { */
/* 	if ( lPSIval_on_var[j] == -1 ) { */
/* 	  continue; */
/* 	} */
/* 	print_Variable_Value(j, lPSIval_on_var[j], TRUE); */
/* 	printf(" "); */
/*       }       */
      result = TRUE;

      if ( gcmd_line.do_recoverer_only_relevant ) {
	/* record this recoverer and continue collecting them...
	 */
	if ( !gop_conn[op].is_recoverer ) {
	  lrecoverers[lnum_recoverers] = op;
	  lnum_recoverers++;
	}
	gop_conn[op].is_recoverer = TRUE;
      } else {
	return TRUE;
      }

    } /* endfor i,op over ops whose pre is in prev\cupeff(rop) */

    /* tried all ops...
     */
    return result;
  }



  /* not yet at final var. loop through the possible values here, and
   * recurse to next ctxvar index
   */
  if (  t->num_context[current_ctxvar_index] <= 0 ) {
    printf("\nt->num_context[current_ctxvar_index] <= 0??\n\n");
    exit(1);
  }
  current_var = t->context[current_ctxvar_index][0]->var;
  for ( i = 0; i < t->num_context[current_ctxvar_index]; i++ ) {
    current_val = t->context[current_ctxvar_index][i]->val;
    lPSIval_on_var[current_var] = current_val;
    if ( !recoverable_side_effect_deletes_testPSI( t, current_ctxvar_index + 1 ) ) {
      return FALSE;
    }
  }

  return TRUE;

}



Bool is_potential_recoverer( DTGTransition *t, int op ) 

{

  int i;

  /* is precond contained in prevail-eff? 
   */
  for ( i = 0; i < gnum_variables; i++ ) {
    if ( gop_conn[op].pre_on_var[i] == -1 ) {
      continue;
    }
    if ( lprevail_eff_on_var[i] == -1 ) {
      return FALSE;
    }
    if ( lprevail_eff_on_var[i] != gop_conn[op].pre_on_var[i] ) {
      return FALSE;
    }
  }

  return TRUE;

}



void determine_DTG_overall( void )

{

  int var, i, j;
  DTGTransition *t;

  for ( var = 0; var < gnum_variables; var++ ) {
    
    /* properties depending on transitions
     */
    gDTGs[var].all_invertible = TRUE;
    gDTGs[var].all_no_side_effects = TRUE;
    gDTGs[var].all_irrelevant_side_effect_deletes = TRUE;
    gDTGs[var].NONLEAF_irrelevant_or_invertiblenoseff_or_irrelevantdeletes = TRUE;
    gDTGs[var].LEAF_irrelevant_or_irrelevantseffdel_or_irrelevantseffrecoverableseffdel = TRUE;

    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);

      if ( !t->invertible ) {
	gDTGs[var].all_invertible = FALSE;
      }

      if ( !t->no_side_effects ) {
	gDTGs[var].all_no_side_effects = FALSE;
      }

      if ( !t->irrelevant_side_effect_deletes ) {
	gDTGs[var].all_irrelevant_side_effect_deletes = FALSE;
      }

      if ( !t->irrelevant &&
	   !(t->invertible && t->no_side_effects) &&
	   !(t->irrelevant_own_delete && t->self_irrelevant_side_effect_deletes) ) {
	gDTGs[var].NONLEAF_irrelevant_or_invertiblenoseff_or_irrelevantdeletes = FALSE;
      }

      if ( !t->irrelevant &&
	   !t->self_irrelevant_side_effect_deletes &&
	   !(t->irrelevant_side_effects && t->recoverable_side_effect_deletes) ) {
	gDTGs[var].LEAF_irrelevant_or_irrelevantseffdel_or_irrelevantseffrecoverableseffdel = FALSE;
      }

      /* additional properties convenient to have here
       */
      if ( gSG.nodes[gDTGs[var].var].num_succ == 0 ) {
	gDTGs[var].var_is_SG_leaf = TRUE;
      } else {
	gDTGs[var].var_is_SG_leaf = FALSE;
      }

      gDTGs[var].var_is_goal = FALSE;
      for ( j = 0; j < ggoal_state.num_F; j++ ) {
	if ( gft_conn[ggoal_state.F[j]].var == gDTGs[var].var ) {/* doesn't happen for notFD */
	  gDTGs[var].var_is_goal = TRUE;
	  break;
	}
      }

    } /* endfor i,t over transitions */

  } /* endfor var over vars */

}



void determine_DTG_diameters( void )

{

  int var, i;
  int pathlength, diameter;

  for ( var = 0; var < gnum_variables; var++ ) {

    /* initialization for looking at the WHOLE DTG
     */
    for ( i = 0; i < gDTGs[var].num_nodes; i++ ) {
      gDTGs[var].nodes[i].IN = TRUE;
    }
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      gDTGs[var].transitions[i].IN = TRUE;
    }

    /* now do this, via simple breadth-first searches
     */
    diameter = -1;
    for ( i = 0; i < gDTGs[var].num_nodes; i++ ) {
      pathlength = DTG_bfs_diameter( &(gDTGs[var]), &(gDTGs[var].nodes[i]) );
      if ( diameter == -1 || pathlength > diameter ) {
	diameter = pathlength;
      } 
    }

    gDTGs[var].diameter = diameter;
  }

}



void determine_DTG_maxdiameters( void )

{

  int var, i;
  int pathlength, maxdiameter;

  for ( var = 0; var < gnum_variables; var++ ) {

    /* initialization for looking at the WHOLE DTG
     */
    for ( i = 0; i < gDTGs[var].num_nodes; i++ ) {
      gDTGs[var].nodes[i].IN = TRUE;
    }
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      gDTGs[var].transitions[i].IN = TRUE;
    }

    /* now do this, via simple breadth-first searches
     */
    maxdiameter = -1;
    for ( i = 0; i < gDTGs[var].num_nodes; i++ ) {
      pathlength = DTG_bfs_maxdiameter( &(gDTGs[var]), &(gDTGs[var].nodes[i]) );
      if ( maxdiameter == -1 || pathlength > maxdiameter ) {
	maxdiameter = pathlength;
      } 
    }

    gDTGs[var].maxdiameter = maxdiameter;
  }

}



/* this is a HACK! 1. would be better to do nthis via DFS, rather than
 * explicitly and quite unnecessarily keeping all paths. 2. Is this
 * actually hard or can it be computed effectively? Oh, what the
 * heck...
 */
int DTG_bfs_maxdiameter( DTG *dtg, DTGNode *node )

{

  static Bool fc = TRUE;
  static DTGNode_pointer *openlist;
  static int *openlist_father;
  static int *start_distance;

  int i, m;
  int current_node, current_end, checknode;
  DTGNode *nextnode;
  int max_distance;
  int max_nodes = 100000;
  int current_distance;



  /* JUST APPROXIMATE THIS TRIVIALLY! Seems to have little to no
   * effect on quality of information returened...
   */
  return dtg->num_nodes - 1;



  /* just once, make space for search space structures
   */
  if ( fc ) {
    openlist = ( DTGNode_pointer * ) calloc(max_nodes, sizeof( DTGNode_pointer ));
    openlist_father = ( int * ) calloc(max_nodes, sizeof( int ));
    start_distance = ( int * ) calloc(max_nodes, sizeof( int ));

    fc = FALSE;
  }


  
  /* sanity test: called on someone not actually in this sub-graph?
   */
  if ( !node->IN ) {
    return 0;
  }



  /* if this guy seems too large, just resort to default value right
   * away.
   */
  if ( dtg->num_nodes > 10 ) {
    return dtg->num_nodes - 1;
  }



  /* initialize search space...
   */
/*   printf("\nMAXDIAM LAYERS for "); */
/*   print_Variable(dtg->var); */
  openlist[0] = node;
  openlist_father[0] = -1;
  start_distance[0] = 0;
/*   printf("\nLayer 0: "); */
/*   print_Variable_Value(dtg->var, node->val, FALSE); */

  /* ... and search.
   */
  current_node = 0;
  current_end = 1;
  current_distance = 0;
  while ( TRUE ) {
/*     printf("\nLayer %d:", current_distance + 1); */

     /* expand all nodes with current_distance; stop at next higher
      *	(ie at successors of these guyes here), or if no such
      *	successors exist in which case we're done.
      */
    while ( current_node < current_end &&
	    start_distance[current_node] <= current_distance ) {

      for ( i = 0; i < openlist[current_node]->num_out; i++ ) {
	if ( !openlist[current_node]->out[i]->IN ) {
	  /* this transition is not in the sub-graph!
	   */
	  continue;
	}
	nextnode = openlist[current_node]->out[i]->end;
	
	if ( !nextnode->IN ) {
	  /* this node is not in the sub-graph!
	   */
	  continue;
	}
	
	/* instead of a global node-closed criterion, we test only
	 * whether the same node has already been included in the path
	 * up to here!
	 */
	for ( checknode = current_node; 
	      checknode >= 0; 
	      checknode = openlist_father[checknode] ) {
	  if ( openlist[checknode] == nextnode ) {
	    break;
	  }
	}
	if ( checknode >= 0 ) {
	  continue;
	}
	
	if ( current_end >= max_nodes ) {
	  if ( gcmd_line.display_info ) {
	    printf("\nWarning: not enough memory to compute maxdiameter of ");
	    print_Variable(dtg->var);
	    printf(". Resorting to default value.");
	  }
	  return dtg->num_nodes - 1;
/* 	  printf("\n Please increase max_nodes (now %d) in DTG_bfs_maxdiameter\n\n", */
/* 		max_nodes); */
/* 	  exit( 1 ); */
	}
	openlist[current_end] = nextnode;
	openlist_father[current_end] = current_node;
	start_distance[current_end] = start_distance[current_node] + 1;
/* 	printf(" "); */
/* 	print_Variable_Value(dtg->var, nextnode->val, FALSE); */
  
	current_end++;
      }

      current_node++;
    }

    if ( current_node == current_end ) {
      break;
    }

    current_distance++;
  }

  return current_distance;

}


























/**********************
 * functions for dynamic properties of SG and DTGs
 **********************/























/* this should probably be done more effectively...
 */
Bool SG_INsubgraph_acyclic( void )

{

  static Bool fc = TRUE;
  static int *IN_SGedge_pres;
  static int *IN_SGedge_effs;

  int num_IN_SGedges;

  int i, j, k;

  if ( fc ) {
    IN_SGedge_pres = ( int * ) calloc( gSG.num_edges, sizeof( int ) );
    IN_SGedge_effs = ( int * ) calloc( gSG.num_edges, sizeof( int ) );
    num_IN_SGedges = 0;
    fc = FALSE;
  }

  for ( j = 0; j < gSG.num_nodes; j++ ) {
    if ( !gSG.nodes[j].IN ) {
      continue;
    }
    
    for ( i = 0; i < gSG.num_nodes; i++ ) {
      if ( !gSG.nodes[i].IN ) {
	continue;
      }
      
      if ( !gSG.IN_adj_matrix[i][j] ) {
	continue;
      }
      for ( k = 0; k < gSG.num_nodes; k++ ) {
	if ( !gSG.nodes[k].IN ) {
	  continue;
	}
	
	if ( !gSG.IN_adj_matrix[j][k] ) {
	  continue;
	}
	if ( gSG.IN_adj_matrix[i][k] ) {
	  continue;
	}
	if ( i == k ) {
	  for ( i = 0; i < num_IN_SGedges; i++ ) {
	    gSG.IN_adj_matrix[IN_SGedge_pres[i]][IN_SGedge_effs[i]] = FALSE; 
	  }
	  num_IN_SGedges = 0;
	  return FALSE;
	}
	gSG.IN_adj_matrix[i][k] = TRUE;
	IN_SGedge_pres[num_IN_SGedges] = i;
	IN_SGedge_effs[num_IN_SGedges++] = k;
      }
    }
  }

  for ( i = 0; i < num_IN_SGedges; i++ ) {
    gSG.IN_adj_matrix[IN_SGedge_pres[i]][IN_SGedge_effs[i]] = FALSE; 
  }
  num_IN_SGedges = 0;
  return TRUE;

}



/* For computing the diameter, this is of course NOT the most
 * effective method in existence. Use it, for now, since it's easy to
 * implement and probably this is not gonna be time-critical -- we do
 * it for oDG+s, where we do it only for the (hopefully small) subset
 * traversed by a relaxed plan
 */
int DTG_bfs_diameter( DTG *dtg, DTGNode *node )

{

  static Bool fc = TRUE;
  static DTGNode_pointer *openlist;
  static Bool *node_closed;
  static int *start_distance;

  int i, m;
  int current_node, current_end;
  DTGNode *nextnode;
  int current_distance;



  /* just once, make space for search space structures
   */
  if ( fc ) {
    m = 1;
    for ( i = 0; i < gnum_variables; i++ ) {
      if ( gDTGs[i].num_nodes > m ) {
	m = gDTGs[i].num_nodes;
      }
    }
    openlist = ( DTGNode_pointer * ) calloc(m, sizeof( DTGNode_pointer ));
    node_closed = ( Bool * ) calloc(m, sizeof( Bool ));
    start_distance = ( int * ) calloc(m, sizeof( int ));

    fc = FALSE;
  }


  
  /* sanity test: called on someone not actually in this sub-graph?
   */
  if ( !node->IN ) {
    return 0;
  }

  /* initialize search space...
   */
  for ( i = 0; i < dtg->num_nodes; i++ ) {
    node_closed[dtg->nodes[i].val] = FALSE;
  }
  openlist[0] = node;
  node_closed[node->val] = TRUE;
  start_distance[0] = 0;

  /* ... and search.
   */
  current_node = 0;
  current_end = 1;
  current_distance = 0;
  while ( TRUE ) {

     /* expand all nodes with current_distance; stop at next higher
      *	(ie at successors of these guyes here), or if no such
      *	successors exist in which case we're done.
      */
    while ( current_node < current_end &&
	    start_distance[current_node] <= current_distance ) {

      for ( i = 0; i < openlist[current_node]->num_out; i++ ) {
	if ( !openlist[current_node]->out[i]->IN ) {
	  /* this transition is not in the sub-graph!
	   */
	  continue;
	}
	nextnode = openlist[current_node]->out[i]->end;
	
	if ( !nextnode->IN ) {
	  /* this node is not in the sub-graph!
	   */
	  continue;
	}
	
	if ( node_closed[nextnode->val] ) {
	  continue;
	}
	
	if ( current_end >= dtg->num_nodes ) {
	  printf("\ncurrent_end %d >= %d dtg->num_nodes??\n\n",
		 current_end,
		 dtg->num_nodes);
	  exit( 1 );
	}
	openlist[current_end] = nextnode;
	node_closed[nextnode->val] = TRUE;
	start_distance[current_end] = start_distance[current_node] + 1;
	current_end++;
      }

      current_node++;
    }

    if ( current_node == current_end ) {
      break;
    }

    current_distance++;
  }

  return current_distance;

}



/* test whether the gDG for var0, t0, sub-graph of SG marked by IN,
 * with the full DTGs, qualifies on all non-leaf vars.
 */
Bool SG_fullDTGs_INsubgraph_nonleafs_qualifies( int var0, DTGTransition *t0 )

{

  int var, i, j;
  DTGTransition *t;
  DTGNode *seff;

  for ( var = 0; var < gSG.num_nodes; var++ ) {
    if ( !gSG.nodes[var].IN ) {
      continue;
    }

    if ( var == var0 ) {
      continue;
    }

    if ( gDTGs[var].NONLEAF_irrelevant_or_invertiblenoseff_or_irrelevantdeletes ) {
      continue;
    }

    /* now we got a nonleaf var that does not have the strong NONLEAF
     * condition. the only remaining chance is that all transitions
     * are either irrelevant, or invertible/induced and have
     * irrelevant seff dels and no seff on nonleaf vars, or have
     * self-irrelevant own and seff dels.
     */
    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);
      
      if ( t->irrelevant ) {
	continue;
      }

      if ( t->irrelevant_own_delete && 
	   t->self_irrelevant_side_effect_deletes ) {
	continue;
      }

      if ( t->invertible &&
	   t->irrelevant_side_effect_deletes ) {
	/* still need to test whether there is a side effect on a
	 * nonleaf var
	 */
	for ( j = 0; j < t->num_side_effects; j++ ) {
	  seff = t->side_effects[j];
	  if ( seff->var == var0 ) {
	    continue;
	  }
	  if ( gSG.nodes[seff->var].IN ) {
	    break;
	  }
	}
	if ( j == t->num_side_effects ) {
	  /* all is fine. continue with next transition.
	   */
	  continue;
	}
      }

      /* found a bad guy!
       */
      return FALSE;
    }

  }

  return TRUE;

}



/* compute Dcost() of the gDG for var0, sub-graph of SG marked by
 * IN, with the full DTGs.
 *
 * Not sure if this is the most effective method... maybe re-think if
 * it turns out to take a lot of time.
 */
int SG_fullDTGs_INsubgraph_Dcost( int var0 )

{

  int i, result;

  /* initialize the guys to be explicitly undefined.
   */
  for ( i = 0; i < gSG.num_nodes; i++ ) {
    gSG.nodes[i].ownDcost = -1;
  }

  gSG.nodes[var0].ownDcost = 1;

  SG_fullDTGs_INsubgraph_Dcost_recursive( &(gSG.nodes[var0]), &(gSG.nodes[var0]) );

  result = 0;
  for ( i = 0; i < gSG.num_nodes; i++ ) {
    if ( !gSG.nodes[i].IN ) {
      continue;
    }

    if ( gSG.nodes[i].ownDcost == -1 ) {
      printf("\ngSG.nodes[i].ownDcost == -1??\n\n");
      exit(1);
    }

    result += gSG.nodes[i].ownDcost;
  }
  
  return result;

}



void SG_fullDTGs_INsubgraph_Dcost_recursive( SGNode *node0, SGNode *current_node )

{

  int i;
  SGNode *succ, *pred;
  int ownDcost;



  /* unless in node0, look above myself to compute my own value.
   */
  if ( node0 != current_node ) {
    ownDcost = 0;

    for ( i = 0; i < current_node->num_succ; i++ ) {
      if ( !current_node->succ[i]->IN ) {
	/* this edge is not in our sub-graph.
	 */
	continue;
      }

      if ( !current_node->succ[i]->end->IN ) {
	printf("\n!current_node->succ[i]->end->IN??\n\n");
	exit(1);
      }

      if ( current_node->succ[i]->end->ownDcost == -1 ) {
	/* one of the predecessors still hasn't computed itself. wait
	 * a little longer...
	 */
	return;
      }

      ownDcost += current_node->succ[i]->end->ownDcost;
    }
    
    if ( !gcmd_line.do_SG_root ||
	 current_node->num_pred > 0 ||
	 !gDTGs[current_node->var].all_irrelevant_side_effect_deletes ) {
      /* now I got the number of times I need to move. multiply with
       * my maxdiameter in case I'm not a root or some of my
       * transitions have relevant side effect deletes, or this
       * special case handling is disabled...
       */
      ownDcost *= gDTGs[current_node->var].maxdiameter;
    } else {
      /* if I'm a root AND all my transitions have no seff (plus I
       * qualify according to the usual non-leaf criteria) then, in
       * exit path construction, rather than following rplan subgraph
       * of my DTG we can take a direct shortest path to where we
       * wanna go! Hence diameter is sufficient here!  (see extra
       * theorems reg "all other transitions have no seff and no
       * outside conds" in draft...)
       */
      ownDcost *= gDTGs[current_node->var].diameter;
    }
    
    current_node->ownDcost = ownDcost;
  }



  /* now, look below myself to make the others also compute their value.
   */
  for ( i = 0; i < current_node->num_pred; i++ ) {
    if ( !current_node->pred[i]->IN ) {
      /* this edge is not in our sub-graph.
       */
      continue;
    }

    if ( !current_node->pred[i]->start->IN ) {
      printf("\n!current_node->pred[i]->start->IN??\n\n");
      exit(1);
    }

    SG_fullDTGs_INsubgraph_Dcost_recursive( node0, current_node->pred[i]->start );

  }

}



/* We could just as well test this right away when we select the DTG
 * transitions. Keep it separate now for nicety of code, and mix it in
 * in case it takes runtime.
 */
Bool SG_DTGs_oDGplus_INsubgraph_nonleafs_qualifies( int var0 )

{

  int var, i, j, k, l;
  DTGTransition *t;
  Action *my_a;
  Operator *my_o;
  DTGNode *seff;

  for ( var = 0; var < gSG.num_nodes; var++ ) {

    if ( !gSG.nodes[var].IN ) {
      continue;
    }

    if ( var == var0 ) {
      continue;
    }

    for ( i = 0; i < gDTGs[var].num_transitions; i++ ) {
      t = &(gDTGs[var].transitions[i]);

      if ( !t->IN ) {
	continue;
      }

      if ( !t->start->IN || !t->end->IN ) {
	printf("\n!t->start->IN || !t->end->IN\n\n");
	exit(1);
      }

      /* Joerg2014: Stats here the positive reason why it worked?
	 (negative reason ie for failure not interesting stats as then
	 all alternate conditions must have failed).
      */
      if ( (t->invertible || t->induced) && t->no_side_effects ) {
	goDGplus_num_succ_nonleavesDTGtnoseff++;
      }
      if ( t->irrelevant_own_delete && t->self_irrelevant_side_effect_deletes ) {
	goDGplus_num_succ_nonleavesDTGtirrdel++;
      }

      if ( !t->irrelevant &&
	   !((t->invertible || t->induced) && t->no_side_effects) &&
	   !(t->irrelevant_own_delete && t->self_irrelevant_side_effect_deletes) ) {

	if ( (t->invertible || t->induced) && t->irrelevant_side_effect_deletes ) {
	  /* we might still be good, provided the guy has no seff on V \ x0. test this!
	   */
	  for ( j = 0; j < t->num_side_effects; j++ ) {
	    seff = t->side_effects[j];
	    if ( seff->var == var0 ) {
	      continue;
	    }
	    if ( gSG.nodes[seff->var].IN ) {
	      break;
	    }
	  }
	  if ( j == t->num_side_effects ) {
	    /* Ok! continue with the next transition!
	     */
	    goDGplus_num_succ_nonleavesDTGtirrseffdel++;
	    goDGplus_num_succ_nonleavesDTGt++;
	    continue;
	  }
	}

	if ( gcmd_line.display_info == 2 ) {
	  printf("\nbad oDTG+ transition on var ");
	  print_Variable(var);
	  printf(": ");
	  print_DTGTransition(t, FALSE);
	}

	return FALSE;
      } /* endif transition is bad */ else {
	goDGplus_num_succ_nonleavesDTGt++;
      }

    } /* endfor i, t over transitions */

  } /* endfor var over vars */

  return TRUE;

}



/* compute dcost() of the gDG for var0, sub-graph of SG marked by
 * IN, with the INsubgraphs of the DTGs.
 *
 * Not sure if this is the most effective method... maybe re-think if
 * it turns out to take a lot of time.
 */
int SG_DTGs_oDGplus_INsubgraph_dcost( int var0 )

{

  int i, result;

  /* initialize the guys to be explicitly undefined.
   */
  for ( i = 0; i < gSG.num_nodes; i++ ) {
    gSG.nodes[i].owndcost = -1;
  }

  gSG.nodes[var0].owndcost = 1;

  SG_DTGs_oDGplus_INsubgraph_dcost_recursive( &(gSG.nodes[var0]), &(gSG.nodes[var0]) );

  result = 0;
  for ( i = 0; i < gSG.num_nodes; i++ ) {
    if ( !gSG.nodes[i].IN ) {
      continue;
    }

    if ( gSG.nodes[i].owndcost == -1 ) {
      printf("\ngSG.nodes[i].owndcost == -1??\n\n");
      exit(1);
    }

    result += gSG.nodes[i].owndcost;
  }
  
  return result;

}



void SG_DTGs_oDGplus_INsubgraph_dcost_recursive( SGNode *node0, SGNode *current_node )

{

  int i;
  SGNode *succ, *pred;
  int owndcost;
  int ownINsubgraph_diameter;
  DTGNode *currentDTGnode;
  int pathlength;



  /* unless in node0, look above myself to compute my own value.
   */
  if ( node0 != current_node ) {
    owndcost = 0;

    for ( i = 0; i < current_node->num_succ; i++ ) {
      /* ATTENTION! in oDG, we do not set IN in SGEdges directly
       * anymore. use IN_adj_matrix instead!
       */
      if ( !gSG.IN_adj_matrix[current_node->var][current_node->succ[i]->end->var] ) { 
/*       if ( !current_node->succ[i]->IN ) { */
	/* this edge is not in our sub-graph.
	 */
	continue;
      }

      if ( !current_node->succ[i]->end->IN ) {
	printf("\n!current_node->succ[i]->end->IN??\n\n");
	exit(1);
      }

      if ( current_node->succ[i]->end->owndcost == -1 ) {
	/* one of the predecessors still hasn't computed itself. wait
	 * a little longer...
	 */
	return;
      }

      owndcost += current_node->succ[i]->end->owndcost;
    }
    
    /* now I got the number of times I need to move. multiply with the
     * diameter of my oDTG+ (which I first need to compute)
     */
    ownINsubgraph_diameter = -1;
    for ( i = 0; i < gDTGs[current_node->var].num_nodes; i++ ) {
      currentDTGnode = &(gDTGs[current_node->var].nodes[i]);

      if ( !currentDTGnode->IN ) {
	continue;
      }

      pathlength = DTG_bfs_diameter( &(gDTGs[current_node->var]), 
				     currentDTGnode );

      if ( ownINsubgraph_diameter == -1 || pathlength > ownINsubgraph_diameter ) {
	ownINsubgraph_diameter = pathlength;
      } 
    }

    owndcost *= ownINsubgraph_diameter;
    
    current_node->owndcost = owndcost;
  }



  /* now, look below myself to make the others also compute their value.
   */
  for ( i = 0; i < current_node->num_pred; i++ ) {
    /* ATTENTION! in oDG, we do not set IN in SGEdges directly
     * anymore. use IN_adj_matrix instead!
     */
    if ( !gSG.IN_adj_matrix[current_node->pred[i]->start->var][current_node->var] ) { 
/*     if ( !current_node->pred[i]->IN ) { */
      /* this edge is not in our sub-graph.
       */
      continue;
    }

    if ( !current_node->pred[i]->start->IN ) {
      printf("\nin oDG: !current_node->pred[i]->start->IN??\n\n");
      exit(1);
    }

    SG_DTGs_oDGplus_INsubgraph_dcost_recursive( node0, current_node->pred[i]->start );

  }

}



























/**********************
 * a simple helper
 **********************/






















Bool are_exchanged_predicates( int p1, int p2 )

{

  static Bool fc = TRUE;
  static int **yes_are_exchanged_predicates;

  int i, j;
  Effect *e, *ee;
  Literal *l, *ll;

  if ( fc ) {
    yes_are_exchanged_predicates = ( int ** ) calloc( gnum_predicates, sizeof( int * ) );
    for ( i = 0; i < gnum_predicates; i++ ) {
      yes_are_exchanged_predicates[i] = ( int * ) calloc( gnum_predicates, sizeof( int * ) );
      for ( j = 0; j < gnum_predicates; j++ ) {
	yes_are_exchanged_predicates[i][j] = -1;
      }
    }
    fc = FALSE;
  }

  if ( yes_are_exchanged_predicates[p1][p2] == 1 ) {
    return TRUE;
  }
  if ( yes_are_exchanged_predicates[p1][p2] == 0 ) {
    return FALSE;
  }

  for ( i = 0; i < gnum_operators; i++ ) {
    for ( e = goperators[i]->effects; e; e = e->next ) {
      for ( l = e->effects; l; l = l->next ) {
	if ( !l->negated && l->fact.predicate == p1 ) {
	  /* do we have the other guy negated?
	   */
	  for ( ee = goperators[i]->effects; ee; ee = ee->next ) {
	    for ( ll = ee->effects; ll; ll = ll->next ) {
	      if ( ll->negated && ll->fact.predicate == p2 ) {
		break;
	      }
	    }
	    if ( ll ) {
	      break;
	    }
	  }
	  if ( ee ) {
	    /* yes! continue with next guy.
	     */
	    continue;
	  }
	  /* no, the other guy is not here. not exchanged preds!
	   */
/* 	  if ( 1 ) { */
/* 	    printf("\n%s and %s not exchanged: %s adds former notdel latter", */
/* 		   gpredicates[p1], gpredicates[p2], goperators[i]->name); */
/* 	  } */
	  yes_are_exchanged_predicates[p1][p2] = 0;
	  return FALSE;
	}
	
	/* now vice versa
	 */
	if ( !l->negated && l->fact.predicate == p2 ) {
	  /* do we have the other guy negated?
	   */
	  for ( ee = goperators[i]->effects; ee; ee = ee->next ) {
	    for ( ll = ee->effects; ll; ll = ll->next ) {
	      if ( ll->negated && ll->fact.predicate == p1 ) {
		break;
	      }
	    }
	    if ( ll ) {
	      break;
	    }
	  }
	  if ( ee ) {
	    /* yes! continue with next guy.
	     */
	    continue;
	  }
	  /* no, the other guy is not here. not exchanged preds!
	   */
/* 	  if ( 1 ) { */
/* 	    printf("\n%s and %s not exchanged: %s adds latter notdel former", */
/* 		   gpredicates[p1], gpredicates[p2], goperators[i]->name); */
/* 	  } */
	  yes_are_exchanged_predicates[p1][p2] = 0;
	  return FALSE;
	  
	}

      } /* endfor l over e lits */

    } /* endfor e over efs */
      
  } /* endfor i over ops */

/*   if ( 1 ) { */
/*     printf("\n%s and %s exchanged", gpredicates[p1], gpredicates[p2]); */
/*   } */
  yes_are_exchanged_predicates[p1][p2] = 1;
  return TRUE;
  
}



