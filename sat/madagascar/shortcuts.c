
/* 2012 (C) Jussi Rintanen, jrintanen.jr@gmail.com */

/* For every literal l1, identify unit-propagation consequences l2 for which
   the derivation involve non-binary clauses. These consequences l1 !-UP l2
   are useful for two reasons.
   1. It is not necessarily the case that -l2 !-UP -l1, and hence with
      the new clause -l1 V l2 we get l2 !-UP l1 as a new consequence.
   2. The clause learning algorithm avoids the use of a potentially long
      non-binary clauses, sometimes leading to much shorter learned clauses
      and much faster learning and unit propagation.
*/

#define noHARDDEBUG
#define noSHOWIT

void shortcutprobe(satinstance sati,int l) {
  int i,l2;
  PTRINT reason;

#ifdef HARDDEBUG
  printf("--------------------------------------------------------------\n");
#endif

  for(i=0;i<sati->nOfVars;i++) {
    int flag;
    flag=0;
    if(!varunsetp(sati,i)) {
      printf("INCORRECTLY ALREADY SET: %i",i); printTlit(sati,PLIT(i));
      flag = 1;
    }
    assert(flag==0);
  }

  setUPstacktop(sati,-1); /* Drop the input unit clauses from the stack. */
  sati->dlevel = 0;

  sati->declevels[0] = 0;

#ifdef HARDDEBUG
  printf("Trying ");
  printTlit(sati,l);
  printf("\n");
#endif

  simpleaddtoqueue(sati,l,REASON_DECISION,0);

  if(propagate(sati)) {
    // Literal cannot be true.
#ifdef SHOWIT
    printf("CONTRADICTION WITH ");
    printTlit(sati,l);
    printf("\n");
#endif
    undo_assignments_until_level_NOHEAP(sati,0);
    return;
  }

  //  printf("PROPAGATED\n");

  for(i=1;i<sati->endunitstack;i++) {   // Go through inferred literals.

    l2 = sati->unitstack[i];

    reason = LITREASON(l2);

#ifdef HARDDEBUG
    printf("Checking %i:",i); printTlit(sati,l2);
    printf("   REASON: ");
    if(reason == REASON_INPUT) printf("INPUT");
    else if(reason == REASON_DECISION) printf("DECISION");
    else if((reason&1)==0) printf(" LONG CLAUSE");
    else printTlit(sati,reason >> 1);
			      
    printf("\n");
#endif

    if((reason & 3) == 0 && clauselen((int *)reason) > 3) { // Reason is a long clause?
      // Store the new binary literal for later use.
      if(nofshortcutclauses+1 >= maxshortcutclauses) {
	maxshortcutclauses = maxshortcutclauses * 2;
	shortcutclauses = (shortcutclause *)realloc(shortcutclauses,
						    maxshortcutclauses * sizeof(shortcutclause));
      }

      shortcutclauses[nofshortcutclauses].l1 = NEG(l) % (2 * sati->nOfVarsPerTime);
      shortcutclauses[nofshortcutclauses].l2 = l2 % (2 * sati->nOfVarsPerTime);
      shortcutclauses[nofshortcutclauses++].tdiff = tvartime(sati,VAR(l2))-tvartime(sati,VAR(l));

#ifdef SHOWIT
      printf("INFER CLAUSE: ");
      printTlit(sati,shortcutclauses[nofshortcutclauses-1].l1);
      printf(" V ");
      printlit(shortcutclauses[nofshortcutclauses-1].l2);
      printf("@%i (through length %i)\n",shortcutclauses[nofshortcutclauses-1].tdiff,clauselen((int *)reason));
#endif
    }

  }
  undo_assignments_until_level_NOHEAP(sati,0);

  for(i=0;i<sati->nOfVars;i++)
    if(!varunsetp(sati,i)) {
      printf("INCORRECTLY REMAINS SET: %i",i); printTlit(sati,PLIT(i));
      assert(1==0);
    }
}

void shortcuts(satinstance sati) {
  int p;

  maxshortcutclauses = 100000;
  nofshortcutclauses = 0;
  shortcutclauses = (shortcutclause *)malloc(maxshortcutclauses * sizeof(shortcutclause));

  for(p=0;p<sati->nOfSVars;p++) {
    shortcutprobe(sati,PLIT(varwithtime(sati,p,flagShortCutHorizon)));
    shortcutprobe(sati,NLIT(varwithtime(sati,p,flagShortCutHorizon)));
  }
#ifdef SHOWIT
  printf("INFERRED %i SHORTCUT CLAUSES.\n",nofshortcutclauses);
#endif
}
