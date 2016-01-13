
/*  2012 (C) Jussi Rintanen  */

#define noDECDEBUG
#define noHEURDEBUG
#define noDEBUGDISJ

typedef struct {
  int l;	/* Will satisfy subgoal l */
  int var;	/* with variable var (action, conditional effect) */
  short t;	/* at time point t */
  int flaws;	/* How many later actions this action disables/affects */
} planstep;

#define MAXPLANSTEPS 1000000
planstep plansteps[MAXPLANSTEPS];
int Nsteps;

#define STACKSIZE 50000
typedef struct _stackel {
  int lit;
  short t;
  short val;
} stackel;

int stackptr;
stackel stack[STACKSIZE];

/* Order the subgoals according to a measure.
   0. No measure is used (everything is 0).
   1. How early does it have to be true.
   TODO: 2. How early, + how constrained.
     If two are equally early, choose the one that is more constrained
     in the sense that can be TRUE in a smaller number of consecutive
     time points. Choosing a highly constrained subgoal leads to failures
     sooner.
*/

inline int anyactionapplicable(satinstance sati,int l,int t) {
  compactCEstruct *ptr;  
  for(ptr=cCEs[l];ptr->var != -1;ptr++) { /* All ways of making l true. */
    if(!tvarfalsep(sati,ptr->var,t)) {  /* Is it applicable? */
      return 1;
    }
  }
  return 0;
}

inline int goallitvalue(satinstance sati,int l,int t0) {
  int t,t2;
  t = t0;
  switch(HEURordmode) {
  case 1:
    /* How long the goal lit has been true before t. */
    while(t >= 0 && tlittruep(sati,l,t)) t = t - 1;
    return t+1;
  case 2:
    /* How long the goal lit has been true before t. */
    while(t >= 0 && tlittruep(sati,l,t)) t = t - 1;
    t2 = t;
    /* How much earlier it was last false. */
    while(t2 >= 0 && !tlitfalsep(sati,l,t2)) t2 = t2-1;
    return (t+1)*200+(t-t2);
  case 3:
    /* How long the goal lit must have been true before t (check applicability
       of actions making it true!) */
    t = t-1;
    while(t >= 0 && anyactionapplicable(sati,l,t) == 0) t = t - 1;
    return t+1;
  case 4:
    /* How wide is the gap in which it must be made true? */
    /* WARNING: This stops depth-first! */
    t = t-1;
    while(t >= 0 && anyactionapplicable(sati,l,t) == 0) t = t - 1;
    t2 = t;
    while(t2 >= 0 && !tlitfalsep(sati,l,t2)) t2 = t2 - 1;
    return t-t2;
  case 5:
    /* Case 1 with Case 4 as a tie-breaker. */
    /* How wide is the gap in which it must be made true? */
    t = t-1;
    while(t >= 0 && tlittruep(sati,l,t)) t = t - 1;
    t2 = t;
    while(t2 >= 0 && !tlitfalsep(sati,l,t2)) t2 = t2 - 1;
    return t*1000+t-t2;
  case 6:
    /* Case 3 with Case 4 as a tie-breaker. */
    /* How wide is the gap in which it must be made true? */
    t = t-1;
    while(t >= 0 && anyactionapplicable(sati,l,t) == 0) t = t - 1;
    t2 = t;
    while(t2 >= 0 && !tlitfalsep(sati,l,t2)) t2 = t2 - 1;
    return t*1000+t-t2;
  default:
    return 0;
  }
}

void push2goalstack(satinstance sati,int l,int t) {
  int v,i;

  i = stackptr++;

  ASSERT(stackptr < STACKSIZE);

  v = goallitvalue(sati,l,t);

  /* Insert the literal in the stack. Lowest .val is on top (last). */
  /* This means that we have a depth-first traversal: support for
     one precondition (or top-level goal) is found first, before
     proceeding with another precondition (or top-level goal). */

  while(i > 0 && stack[i-1].val < v) {
    stack[i].lit = stack[i-1].lit;
    stack[i].t = stack[i-1].t;
    stack[i].val = stack[i-1].val;
    i = i-1;
  }

  stack[i].lit = l;
  stack[i].t = t;
  stack[i].val = v;
}

/* Push the constituent literals of a conjunctive goal formula in the stack. */

void push2goalstackCfma(satinstance sati,fma *f,int t) {
  fmalist *fs;
  switch(f->t) {
  case patom: push2goalstack(sati,PLIT(f->a),t); break;
  case natom: push2goalstack(sati,NLIT(f->a),t); break;
  case conj:
    fs = f->juncts;
    while(fs != NULL) {
      push2goalstackCfma(sati,fs->hd,t);
      fs = fs->tl;
    }
    break;
  case TRUE: break;
  default:
    assert(1==2);
  }
}

/* Push a subset of the literals in a general NNF formula which are
   sufficient for making the formula true, in the stack.
   This is as in the ICAPS'11 submission.
   For conjunctions all conjuncts have to be taken.
   For disjunctions one of the disjuncts is taken. If at least one of
   the disjuncts is true or unknown, then the chosen disjunct cannot
   be a false one.
*/

/* The implementation is in with a stack of sets of literals.
   The operations are
   - adding a set into the set (empty or singleton)
   - taking the union of two top stacks
   - removing the top or the second set from the stack
   - comparing the two top sets (cardinality?) for choosing a disjunct

tset_stack: element is the index of the first element of the set in tset_store
*/

typedef struct {
  int l;
  short t;
} storepair;

int stacktop;
int storetop;
int tset_stack[1000];
int tset_card[1000];
storepair tset_store[100000];

#define CARDTOP (storetop-tset_stack[stacktop]+1)
#define CARD2ND (tset_stack[stacktop]-tset_stack[stacktop-1])

void tset_emptyset() {
#ifdef DEBUGDISJ
  printf("tset_emptyset\n");
#endif
  stacktop += 1;
  tset_card[stacktop] = 0;
  tset_stack[stacktop] = storetop+1;
}

void tset_show() {
#ifdef DEBUGDISJ
  int i,j;
  printf("=========================================================\n");
  for(i=0;i<=storetop+1;i++) {
    for(j=0;j<=stacktop;j++) {
      if(tset_stack[j] == i) printf("START %i (card %i)\n",j,tset_card[j]);
    }
    if(i<=storetop) {
      printf("%i: ",i); printlit(tset_store[i].l); printf("@%i\n",tset_store[i].t);
    }
  }
  printf("     =========================================================\n");
#endif
}

/* Add the empty set in the stack. */

void tset_makeempty() {
#ifdef DEBUGDISJ
  printf("tset_makeempty\n");
#endif
  stacktop=-1;
  storetop=-1;
  tset_emptyset(); /* Always have an empty set in the stack. */
}

/* Add a singleton set into the stack. */

void tset_singleton(int l,int t) {
#ifdef DEBUGDISJ
  printf("tset_singleton "); printlit(l); printf("@%i\n",t);
#endif
  storetop = storetop+1;
  tset_store[storetop].l = l;
  tset_store[storetop].t = t;
  stacktop = stacktop+1;
  tset_stack[stacktop] = storetop;
  tset_card[stacktop] = 1;
}

/* Take the union of the two top sets. */

void tset_union() {
#ifdef DEBUGDISJ
  printf("tset_union\n");
#endif
  tset_card[stacktop-1] = tset_card[stacktop-1]+tset_card[stacktop];
  stacktop = stacktop - 1;
}

/* Return TRUE if top element has a smaller cardinality than the second. */

int tset_top_better() {
  if(tset_card[stacktop] < tset_card[stacktop-1]) return 1; else return 0;
}

/* Remove the top set from the stack. */

void tset_top_delete() {
#ifdef DEBUGDISJ
  printf("tset_top_delete\n");
#endif
  storetop = storetop-tset_card[stacktop];
  stacktop = stacktop-1;
}

/* Remove the second set from the stack. */

void tset_second_delete() {
  int i,n;
#ifdef DEBUGDISJ
  printf("tset_second_delete\n");
#endif
  n = tset_card[stacktop];
  /* Move the top set where the second one was. */
  for(i=0;i<n;i++) {
    tset_store[tset_stack[stacktop-1]+i] = tset_store[tset_stack[stacktop]+i];
  }
  storetop = tset_stack[stacktop-1]+n-1;
  stacktop = stacktop-1;
  tset_card[stacktop]=n;
}

int traverseDfma(satinstance sati,fma *f,int t) {
  fmalist *fs;
  int have;

#ifdef DEBUGDISJ
  tset_show();
#endif

  switch(f->t) {
    /* Here we have to restrict to literals that are not FALSE ? */
  case patom:
    if(tvarfalsep(sati,f->a,t)) return 0;
    tset_singleton(PLIT(f->a),t);
    return 1;
  case natom:
    if(tvartruep(sati,f->a,t)) return 0;
    tset_singleton(NLIT(f->a),t);
    return 1;
  case conj: /* The literal sets for all conjuncts are combined. */
    tset_emptyset();
    fs = f->juncts;
    while(fs != NULL) {
      if(traverseDfma(sati,fs->hd,t) == 0) {
	tset_top_delete();
	return 0;
      }
      tset_union();
      fs = fs->tl;
    }
    return 1;
  case disj: /* The set for one of the disjuncts is chosen, others ignored. */
    //    tset_emptyset(); ???????????????????
    have = 0;
    fs = f->juncts;
    while(fs != NULL) {
      if(traverseDfma(sati,fs->hd,t)) {
	if(have) {
#ifdef DEBUGDISJ
	  tset_show();
#endif
	  if(tset_top_better()) tset_second_delete(); else tset_top_delete();
	}
	have = 1;
      }
      fs = fs->tl;
    }
    return have;
  case TRUE: tset_emptyset(); return 1;
  case FALSE: return 0;
  }
  return 0;
}

void push2goalstackDfma(satinstance sati,fma *f,int t) {
  int i,l,t2;
  tset_makeempty();
  if(traverseDfma(sati,f,t) == 0) return;
#ifdef DEBUGDISJ
  tset_show();
#endif
  //  if(tset_stack[stacktop]+1>storetop) printf("Not pushing anything\n");
  /* Push the literals from the traverseDfma stack into the heuristic stack. */
  for(i=tset_stack[stacktop];i<=storetop;i++) {
    l = tset_store[i].l;
    t2 = tset_store[i].t;
#ifdef DEBUGDISJ
    printf("Pushing %i:",l); printlit(l); printf("@%i\n",t2);
#endif
    push2goalstack(sati,l,t2);
  }
}

#ifdef HARDDEBUG
void showheustack(satinstance sati) {
  int i;
  printf("STACK CONTENTS:\n");
  for(i=0;i<stackptr;i++) {
    printlit(stack[i].lit);
    printf("@%i (score %i)\n",stack[i].t,stack[i].val);
  }
}
#endif

#define TMPARRAYSIZE 1000

void do_cpath(satinstance);

int weightedscore(satinstance sati,int i) {
  return sati->lits[PLIT(TVAR(plansteps[i].var,plansteps[i].t))].score + 10000-100*plansteps[i].flaws;
}

/* Identify actions that are useful in reaching the goals. */

int do_cpath_heuristic(satinstance sati) {
  int i,j,best,besttime;
#ifdef WEIGHTS
  int tmparray[TMPARRAYSIZE];
#endif

  nextround(sati);

  Nsteps = 0;
  stackptr = 0;

  switch(sati->heuristic_mode) {

  case 0:	/* Choose an action. */

    if(goalisdisjunctive) {
      push2goalstackDfma(sati,goal,sati->nOfTPoints-1);
    } else {
      push2goalstackCfma(sati,goal,sati->nOfTPoints-1);
    }

#ifdef HARDDEBUG
    showheustack(sati);
#endif

    /* Find paths */
    do_cpath(sati);

    /* Pick action. */

    /* Only one action to choose from: return it directly. */
    if(Nsteps == 1) return PLIT(TVAR(plansteps[0].var,plansteps[0].t));

    if(Nsteps > 0) {

      switch(HEURactionchoice) {
      case 0: /* Choose action randomly. */
	i = random() % Nsteps;
	break;
      case 1: /* Choose the earliest possible action. */
	best = -1;
	besttime = 100000;
	for(i=0;i<Nsteps;i++) {
	  if(plansteps[i].t < besttime) {
	    best = i;
	    besttime = plansteps[i].t;
	  }
	}
	i = best;
	break;
      case 2: /* Choose action randomly, with bias to earlier. */
	j = random() % Nsteps;
	i = random() % (j+1);
	break;
      case 3: /* Choose action randomly, with bias to later. */
	j = random() % Nsteps;
	i = Nsteps-(random() % (j+1))-1;
	break;
      case 4: /* Choose action based on its weight, with ties broken
		 randomly. */
#ifdef WEIGHTS
	best = -1;
	for(i=0;i< Nsteps;i++) { /* Determine the best score. */
	  int score = weightedscore(sati,i);
	  if(score > best) best = score;
	}
	j = 0;
	for(i=0;i<Nsteps;i++) { /* Collect the literals with the best score. */
	  if(weightedscore(sati,i) == best) {
	    tmparray[j++] = i;
	    ASSERT(j < 1000);
	  }
	  
	}
	i = tmparray[random() % j];
	break;
#else
	fprintf(stderr,"Heuristic needs WEIGHTS compiled.\n");
	exit(1);
#endif
      }

      return PLIT(TVAR(plansteps[i].var,plansteps[i].t));
      //      return TLIT(plansteps[i].l,plansteps[i].t);

    }

    sati->heuristic_mode = 1;
    sati->heuristic_time = 1;
    sati->heuristic_index = 0;

  case 1:	/* No actions needed. Do inertia. */

#ifdef HEURDEBUG
    printf("Doing INERTIA\n");
#endif

    while(sati->heuristic_time < sati->nOfTPoints) {

	i = sati->heuristic_index;
	j = sati->heuristic_time;

	if(i+1 == sati->nOfSVars) {
	  sati->heuristic_index = 0;
	  sati->heuristic_time += 1;
	} else {
	  sati->heuristic_index += 1;
	}

	if(tvarunsetp(sati,i,j)) {
	  if(tvartruep(sati,i,j-1)) return PLIT(TVAR(i,j));
	  else return NLIT(TVAR(i,j));
	}

    }

    sati->heuristic_mode = 2;
    sati->heuristic_time = 0;
    sati->heuristic_index = 0;

  case 2:	/* All state variables have a value. Set actions to FALSE. */

    while(sati->heuristic_time < sati->nOfTPoints-1) {

	i = sati->heuristic_index;
	j = sati->heuristic_time;

	if(i+1 == sati->nOfActions) {
	  sati->heuristic_index = 0;
	  sati->heuristic_time += 1;
	} else {
	  sati->heuristic_index += 1;
	}

	if(tvarunsetp(sati,ACTVAR(i),j)) return NLIT(TVAR(ACTVAR(i),j));
    }

  }

  return -1;

}

int fmavalue(satinstance sati,fma *f,int t) {
  fmalist *juncts;
  switch(f->t) {
  case patom: if(!tvarfalsep(sati,f->a,t)) return 1; else return 0;
  case natom: if(!tvartruep(sati,f->a,t)) return 1; else return 0;
  case disj:
    juncts = f->juncts;
    while(juncts != NULL) {
      if(fmavalue(sati,juncts->hd,t) != 0) return 1;
      juncts = juncts->tl;
    }
    return 0;
  case conj:
    juncts = f->juncts;
    while(juncts != NULL) {
      if(fmavalue(sati,juncts->hd,t) == 0) return 0;
      juncts = juncts->tl;
    }
    return 1;
  case TRUE: return 1;
  case FALSE: return 0;
  }
  return 0;
}

/* Estimate the value for an action */

int actionvalue(satinstance sati,int var,int t,fma *precondition,int disjunctive) {
  int i;
  int val;
  switch(HEURops) {
  case 1: /* Evaluate 'constrainedness' of action */
    /* How many steps later can this action be taken? */
    val = 0;
    while(t+1 < sati->nOfTPoints-1 && !tvarfalsep(sati,var,t+1)) {
      t = t+1;
      val = val + 1;
    }
    return val;
  case 2: /* Evaluate 'constrainedness' of action */
    /* How many steps later can this action be taken? */
    val = 0;
    while(t+1 < sati->nOfTPoints-1 && !tvarfalsep(sati,var,t+1)) {
      t = t+1;
      val = val + 1;
    }
    return 1000-val;
  case 3: /* Evaluate 'constrainedness' of precondition */
    /* How many steps later can the precondition be true? */
    val = 0;
    while(t+1 < sati->nOfTPoints && fmavalue(sati,precondition,t+1) != 0) {
      t = t+1;
      val = val + 1;
    }
    return val;
  case 4: /* Evaluate 'constrainedness' of precondition */
    /* How many steps later can the precondition be true? */
    val = 0;
    while(t+1 < sati->nOfTPoints && fmavalue(sati,precondition,t+1) != 0) {
      t = t+1;
      val = val + 1;
    }
    return 1000-val;
  case 5:
    /* How many steps earlier can the precondition be true? */
    val = 0;
    while(t-1 >= 0 && fmavalue(sati,precondition,t-1) != 0) {
      t = t-1;
      val = val + 1;
    }
    return val;
  case 6:
    /* How many steps earlier can the precondition be true? */
    val = 0;
    while(t-1 >= 0 && fmavalue(sati,precondition,t-1) != 0) {
      t = t-1;
      val = val + 1;
    }
    return 1000-val;
  case 7:
    /* How many later suggested actions the action disables/affects. */
    val = 0;
    for(i=0;i<Nsteps;i++) {
      if((plansteps[i].t > t) && (actaffects(var,plansteps[i].var))) {
	val = val + 1;
      }
    }
    //    printf("{%i}",val);
    return 1000-val;
  default: assert(2==7);
  }
}

/* Go through actions at time point t-1 to find one that could
   make literal l true at t. "Could" means: l occurs as a conditional
   or unconditional effect, and we don't care about the condition.

   This is based on the following parameters (given on command line):
     HEURtime: which time to consider, 0 = earliest, 1 = latest, 2 = all
     HEURops: which operator to consider 0 = first (arbitrary), 1 = all
     HEURchoice: which action@time to choose, 0 = random, 1 = weight
*/

/* Choose an action at t1-1 that can make l@t TRUE. The action is returned
   in var,t.  */

void supports(satinstance sati,int t0,int t1,int l,int *var,int *t,fma **precondition,int *disjunctive) {
  compactCEstruct *ptr;
  int bestvalue,value;
  int bestvar,bestt,bestdisjunctive;
  fma *bestprecondition;

  if(HEURops == 0) { /* Return the "first" (arbitrary) action. */

    for(ptr=cCEs[l];ptr->var != -1;ptr++) { /* All ways of making l true. */
      if(!tvarfalsep(sati,ptr->var,t1-1)) {  /* Is it applicable? */
#ifdef HARDDEBUG
	printf("Add ACTION %i:",ptr->var); printUvar(ptr->var); printf("@%i\n",t1-1);
#endif
	*var = ptr->var;
	*t = t1-1;
	*precondition = ptr->condition;
	*disjunctive = ptr->disjunctive;
	return;
      }
    }

    assert(1==2);
  }

  bestvar = -1;

  for(ptr=cCEs[l];ptr->var != -1;ptr++) { /* All ways of making l true. */
    if(!tvarfalsep(sati,ptr->var,t1-1)) {  /* Is it applicable? */
#ifdef HARDDEBUG
      printf("Consider ACTION %i:",ptr->var); printUvar(ptr->var); printf("@%i\n",t1-1);
#endif
      if(bestvar == -1) {
	bestvar = ptr->var;
	bestt = t1-1;
	bestprecondition = ptr->condition;
	bestdisjunctive = ptr->disjunctive;
	bestvalue = actionvalue(sati,ptr->var,t1-1,ptr->condition,ptr->disjunctive);
      } else {
	value = actionvalue(sati,ptr->var,t1-1,ptr->condition,ptr->disjunctive);
	if(value > bestvalue) {
	  bestvar = ptr->var;
	  bestt = t1-1;
	  bestprecondition = ptr->condition;
	  bestdisjunctive = ptr->disjunctive;
	  bestvalue = value;
	}
      }
    }
  }

  assert(bestvar != -1);

#ifdef DECDEBUG
  printf("Best action: ");
  printUvar(bestvar);
  printf("@%i for ",bestt);
  printlit(l);
  printf(" has value %i.\n",bestvalue);
#endif

  *var = bestvar;
  *t = bestt;
  *precondition = bestprecondition;
  *disjunctive = bestdisjunctive;
}


/* Is some action op actually making l true at t-1? (= op assigned TRUE?) */

int litmadetrue(satinstance sati,int l,int t,fma **precondition,int *disjunctive) {
  int i;

  if(!littruep(sati,litwithtime(sati,l,t))) return -1; /* l@t is not even true: no action! */

  for(i=0;cCEs[l][i].var != -1;i++) { /* All ways of making l@t-1 true. */
    if(tvartruep(sati,cCEs[l][i].var,t-1)) {
      *precondition = cCEs[l][i].condition;
      *disjunctive = cCEs[l][i].disjunctive;
      return cCEs[l][i].var;
    }
  }
  
  return -1; /* l@t-1 not made true. */
}

/***********************************************************************/
/*** Heuristic:                                                      ***/
/***   Find an unfulfilled (sub)goal and fulfill it at the earliest  ***/
/***   possible time point.                                          ***/
/***                                                                 ***/
/***********************************************************************/

#define noPRUNEfromGOAL
#define noPRUNEtoGOAL

void do_cpath(satinstance sati) {
  int l,t,t1;
  int j,var,isthere;
  int suggestedactionsfound;
  int depthlimitHIGH;
  fma *precondition;
  int disjunctive;

  depthlimitHIGH = -1;
  suggestedactionsfound = 0;

  while(stackptr > 0) {

    /* Pop literal-time pair from the stack. */
    l = stack[stackptr-1].lit;
    t = stack[--stackptr].t;

#ifdef PRUNEtoGOAL
    if(HEURactiondepthlimit && suggestedactionsfound && t >= depthlimitHIGH)
      return;
#endif

#ifdef HEURDEBUG
    printf("Find action for goal "); printlit(l); printf("@%i.\n",t);
#endif

    /* Starting from last time point, find last time t such that either
       1) an action op@t-1 makes l@t TRUE, or
       2) l@t-1 is FALSE and l@t is TRUE or UNASSIGNED.
    */
    isthere = 0;
    var = -1;

    for(j=t;j>0;j--) {
      var = litmadetrue(sati,l,j,&precondition,&disjunctive);
      if(var != -1) {
	isthere = 1;
	t1 = j-1;
	break;
      }

      if(litfalsep(sati,litwithtime(sati,l,j-1))) break;
    }

    if(j == 0) { /* Literal is true at time 0. */
#ifdef HEURDEBUG
      printf("(true in the initial state.)\n");
#endif
      continue; 
    }

    /* Literal is last false at time point j-1. */

    if(var == -1) { /* Choose an action that turns l true between j-1 and j. */
      supports(sati,t,j,l,&var,&t1,&precondition,&disjunctive);
    /* The following assertions cannot be false because
       there must be an action that could make l true at t1 (i.e. is not FALSE).
       If there were not, the frame action (-l & l) -> ... would
       contradict Ass1 and Ass2.
    */
      ASSERT(var != 0);
      ASSERT(precondition->t != -1);
      ASSERT(tlitfalsep(sati,l,j-1));
      ASSERT(!tlitfalsep(sati,l,j));
    }

    if(seenp(sati,TVAR(var,t1))) continue;	/* Operator already processed once. */

    /* Don't go back to top-level goals. */

#ifndef PRUNEtoGOAL
    if(HEURactiondepthlimit && suggestedactionsfound && t1 >= depthlimitHIGH)
      return;
#endif

    if(!isthere) { /* Add the variable to the list of candidate decisions. */
      suggestedactionsfound += 1;
      plansteps[Nsteps].var = var;
      plansteps[Nsteps].t = t1;
      plansteps[Nsteps].flaws = 0;
      if(HEURops == 7) {
	for(j=0;j<Nsteps;j++) {
	  if(actaffects(var,plansteps[j].var)) plansteps[Nsteps].flaws += 1;
	}
      }
      plansteps[Nsteps++].l = l;

#ifdef HEURDEBUG
      printf("Chose action ");
      printUvar(var);
      printf(" to make literal true @%i.\n",j);
#endif

#ifdef PRUNEfromGOAL
      if(suggestedactionsfound == 1) depthlimitHIGH = t;
#else
      if(suggestedactionsfound == 1) depthlimitHIGH = t1;
#endif
    }

    ASSERT(Nsteps < MAXPLANSTEPS);

    if(suggestedactionsfound >= HEURactions) return;
    
#ifdef HARDDEBUG
    printf(" Push preconditions of %i:",var); printUvar(var); printf("@%i into the stack (%i).\n",t1,isthere);
#endif
    
    if(t1 > 0) {      /* Push preconditions in the stack. */
      if(disjunctive == 0) {
	push2goalstackCfma(sati,precondition,t1);
      } else {
	push2goalstackDfma(sati,precondition,t1);
      }
#ifdef HARDDEBUG
      showheustack(sati);
#endif

    }
  }
}
