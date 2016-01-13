

/* This is the learning function that moves all non-decision literals
directly to the clause array, without unnecessarily routing them through
the stack first. */


void learn(satinstance sati,int dlevel,int *CCdliteral,PTRINT *CCreason,int *maxnondecisionlevel) {

  int ptr;	/* Index to the last literal in the conflict clause */

  int top;	/* Index to the top of the stack */

  int CCwatch1;
  int CCwatch2;

  int *newClause;

  int len,l,rl,i,j;
  PTRINT r;
  int *c;
  int *stck,*cc;

#ifdef MULTICORE
  stck = threads[sati->thread].stck;
  cc = threads[sati->thread].cc;
#else
  stck = sati->stck;
  cc = sati->cc;
#endif

#ifdef LBD
  int lbd;
#endif

  /* This counter is used for eliminating multiple occurrences of
     a literal from the derivation of the conflict clause.
     If the literal is associated with the current round, it has
     been seen already and will be ignored. */

  nextround(sati);

  ptr = -1;	/* The clause we will learn is still empty. */
  top = -1;	/* All literals in the clause are in the stack. */

  *maxnondecisionlevel = -1; /* Highest non-decision level. */

  if(sati->conflicttype2lit) { /* A 2-literal clause was falsified. */
    stck[0] = sati->conflictl1; /* Push both literals into the stack. */
    stck[1] = sati->conflictl2;

    top = 1;

#ifdef MULTICORE
    threads[sati->thread].wasseen[sati->conflictl1] = threads[sati->thread].cround;
    threads[sati->thread].wasseen[sati->conflictl2] = threads[sati->thread].cround;
#else
    wasseen[sati->conflictl1] = cround;
    wasseen[sati->conflictl2] = cround;
#endif

#ifdef HARDDEBUG
    printf("Violated binary clause ");
    printTlit(sati,sati->conflictl1);
    printf(" ");
    printTlit(sati,sati->conflictl2);
    printf("\n");
#endif

#ifdef ASSERTS
    assert(isliteral(sati,sati->conflictl1));
    assert(isliteral(sati,sati->conflictl2));
#endif

  } else { /* A clause of >= 3 literals was falsified. */

    len = sati->conflictclause[PREFIX_CLAUSELEN];

#ifdef DEBUG
    printf("Violated clause %i (len %i):\n",(int)(sati->conflictclause),len);
    for(i=0;i<len;i++) { printTlit(sati,sati->conflictclause[i]); }
    //    for(i=0;i<len;i++) { printf(" %i",sati->conflictclause[i]); }
    printf("\n");
#endif

#ifdef ASSERTS
    for(i=0;i<len;i++) assert(isliteral(sati,NEG(sati->conflictclause[i])));
#endif

    /* Push all literals in the clause into the stack or in the cc array. */
    for(i=0;i<len;i++) {
#ifdef MULTICORE
      threads[sati->thread].wasseen[NEG(sati->conflictclause[i])] =
	threads[sati->thread].cround;
#else
      wasseen[NEG(sati->conflictclause[i])] = cround;
#endif
      if(LITDLEVEL(sati->conflictclause[i]) == dlevel) {
	stck[++top] = NEG(sati->conflictclause[i]);
      } else {
	int l = sati->conflictclause[i];
	if(LITREASON(l) != REASON_INPUT) {
	  *maxnondecisionlevel = max(LITDLEVEL(l),*maxnondecisionlevel);
	  cc[++ptr] = l;
	}
      }
    }
  }

  //  printf("FALSIFIED A %i-LITERAL CLAUSE.\n",len);

  //  for(i=0;i<=top;i++) printf("{%i}",sati->variabledlevel[VAR(stck[i])]);
  //  for(i=0;i<=top;i++) printTlit(sati,stck[i]);
  //  printf("\n");

  CCwatch1 = -1;
  CCwatch2 = -1;

#ifdef ASSERTS
  assert(ptr<MAXCCLENGTH);
  assert(top<MAXCCLENGTH);
  assert(ptr>=-1);
  assert(top>=0); /* Necessarily at least one literal at the decision level. */
#endif

  while(top >= 0) {

    l = stck[top--];	/* Pop literal from the stack. */

#ifdef ASSERTS
    assert(ptr<MAXCCLENGTH);
    assert(top<MAXCCLENGTH);
    assert(isliteral(sati,l));
    assert(!litunsetp(sati,l));
    assert(top>=-1);
#endif

    r = LITREASON(l); 

    /* Infer (learn) a new clause from the falsified clause, one literal
       at a time. */
    
    if(r == REASON_DECISION) { /* It is the decision literal. */
      cc[++ptr] = NEG(l);
      CCwatch1 = NEG(l);
      *CCdliteral = NEG(l);
    } else if(r&1) {	/* Reason is a literal (2 lit clause) */
#ifdef WEIGHTS
      increase_score(sati,l);	/* Increase score */
#endif

      if(!seenp(sati,r >> 1)) {
	  stck[++top] = (r >> 1);
#ifdef ASSERTS
	assert(isliteral(sati,r >> 1));
#endif
      }
    } else {	/* Reason is a clause */
#ifdef WEIGHTS
      increase_score(sati,l);	/* Increase score */
#endif

      c = (int *)r;
      while(*c != -1) {	/* Literals except l into the stack or into the CC. */
	if(VAR(*c) != VAR(l) && !seenp(sati,NEG(*c))) {
	  if(LITDLEVEL(*c) == dlevel) {
	    stck[++top] = NEG(*c);
	  } else {
	    *maxnondecisionlevel = max(LITDLEVEL(*c),*maxnondecisionlevel);
	    cc[++ptr] = *c;
	  }
	}
	c += 1;
      }
    }
  }

#ifdef ASSERTS
    assert(ptr<MAXCCLENGTH);
    assert(top<MAXCCLENGTH);
    assert(top>=-1);
#endif

#ifdef DEBUG
  printf("Learned clause %i (%i lits):",clausecount,ptr+1);
  for(i=0;i<=ptr;i++) { printf(" %i:",VAR(cc[i])); printTlit(sati,cc[i]); }
  printf("\n");
#endif

#ifdef ASSERTS
  /* See that the learned clause is false in the current valuation. */
  for(i=0;i<=ptr;i++) {
    assert(!littruep(sati,cc[i]));
    assert(!litunsetp(sati,cc[i]));
  }
#endif

  /* Minimize the size of the learned clause:
     1. Mark all literals in the clause.
     2. Remove literals whose parent is marked.
  */

#define noMINIMIZE

#ifdef MINIMIZE
{
  PTRINT rr;
  cround += 1;
  for(i=0;i<=ptr;i++) wasseen[NEG(cc[i])] = cround;
  i = 0;
  while(i<=ptr) {
    rr = LITREASON(cc[i]);
    if(rr != REASON_DECISION && (((int)rr)&1) && (wasseen[((int)rr) >> 1] == cround)) { /* Remove. */
      //      printf("*");
      cc[i] = cc[ptr--];
    } else {
      if(LITDLEVEL(cc[i]) == *maxnondecisionlevel) CCwatch2 = cc[i];
      i = i + 1;
    }
  }
}
#else
  for(i=0;i<=ptr;i++) {
    if(LITDLEVEL(cc[i]) == *maxnondecisionlevel) {
      CCwatch2 = cc[i];
      break;
    }
  }
#endif

#ifdef LBD
  /* Calculate the Literal Block Distance LBD of Laurent & Simon IJCAI'09. */

  lbd = 0;
  sati->LBDcounter += 1;
  for(i=0;i<=ptr;i++) {
    if(sati->LBDflag[LITDLEVEL(cc[i])] != sati->LBDcounter) {
      lbd += 1;
      sati->LBDflag[LITDLEVEL(cc[i])] = sati->LBDcounter;
    }
  }
#endif

//printf("LEARNED A %i-LITERAL CLAUSE.\n",ptr+1);
//if(ptr+1 > 20000) printf("QZ(%i,%i)",ptr+1,dlevel);

//  printf("ADDING NEW CLAUSE, ptr == %i\n",ptr);

  /* Add the new clause to the clause set. */

  if(ptr+1 > stats_longest_learned) stats_longest_learned = ptr+1;

  if(ptr >= 2) { /* Clause with at least 3 literals */

#ifdef ASSERTS
    assert(isliteral(sati,CCwatch1));
    assert(isliteral(sati,CCwatch2));
    assert(CCwatch1 != CCwatch2);
#endif

    newClause = allocclause(sati->id,ptr+1);

    //    updateactivity(newClause,sati->conflicts);
    newClause[PREFIX_ACTIVITY] = sati->conflicts;

#ifdef LBD
    //    printf("/%i/",lbd);
  setLBD(newClause,lbd);
#endif

    /* The watched literals are the ones with the highest levels,
       that is, the one at the decision level and one on the
       next highest level. */

    newClause[0] = CCwatch1;
    newClause[1] = CCwatch2;

#ifdef WEIGHTS
    increase_score(sati,newClause[0]);
    increase_score(sati,newClause[1]);
#endif

    // Sort the learned clause. Impact on total runtime???????
    qsort(cc,ptr+1,sizeof(int),litCmp);

    j = 2;
    for(i=0;i<=ptr;i++) {
#ifdef ASSERTS
      assert(isliteral(sati,cc[i]));
      //      assert(cc[i] != cc[i+1]);
#endif
      if(cc[i] != CCwatch1 && cc[i] != CCwatch2) {
	newClause[j++] = cc[i];
#ifdef WEIGHTS
	increase_score(sati,newClause[j-1]);
#endif
      }
    }

#ifdef ASSERTS
    assert(j == ptr+1);
    assert(newClause[ptr+1] == -1);
#endif

    *CCreason = (PTRINT)newClause;

    setwatch(sati,CCwatch1,(int *)(*CCreason),0);
    setwatch(sati,CCwatch2,(int *)(*CCreason),1);

  } else if(ptr == 1) { /* Clause with 2 literals */

#ifdef DEBUG
    printf("LEARNED A 2-LITERAL CLAUSE (horizon %i)\n",sati->nOfTPoints);
#endif

    add2clause(sati,cc[0],cc[1],InitC);

    if(cc[0] == *CCdliteral) rl = cc[1];
    else rl = cc[0];
    *CCreason = ((NEG(rl))<< 1)|1;

  } else { /* Unit clause */

#ifdef DEBUG
    printf("LEARNED A 1-LITERAL CLAUSE! (horizon %i)\n",sati->nOfTPoints);
#endif
#ifdef UCC
    addUCC(sati,cc[0]);
#endif
    *CCreason = REASON_INPUT;
    *maxnondecisionlevel = 0;

  }

}
