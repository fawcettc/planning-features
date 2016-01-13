
cfma Cgroundfma(Sfma *,int *);

void Cgroundfmalist(Sfmalist *fs,int *ptr,int *b) {
  while(fs != NULL) {
    *(ptr++) = Cgroundfma(fs->hd,b);
    fs = fs->tl;
  }
}

cfma Cgroundfma(Sfma *sf,int *b) {
  int *vals;
  int i,cnt;
  Sfmalist *fs;
  cfma f;

  switch(Sfmatypeof(sf)) {

  case STRUE: return cTRUE;
  case SFALSE: return cFALSE;

  case Sconj:
    f = (cfma)malloc(sizeof(int *) * (sf->cnt + 1));
    Cgroundfmalist(sf->juncts,f+1,b);
    f[0] = 1+(sf->cnt << 1);
    return f;

  case Sdisj:
    f = (cfma)malloc(sizeof(int *) * (sf->cnt + 1));
    Cgroundfmalist(sf->juncts,f+1,b);
    f[0] = (sf->cnt << 1);
    return f;

  case Seq:
    if(bvalue(sf->p1,b) == bvalue(sf->p2,b)) {
      return cTRUE;
    } else {
      return cFALSE;
    }

  case Sneq:
    if(bvalue(sf->p1,b) == bvalue(sf->p2,b)) {
      return cFALSE;
    } else {
      return cTRUE;
    }

  case Spatom: return cPATOM(atomindex(sf->a,b));

  case Snatom: return cNATOM(atomindex(sf->a,b));

  case Sforall:  /* Iterate over all values of the variable. */

    cnt = getdomainsize(sf->ss->t);

    f = (cfma)malloc(sizeof(int *) * (cnt + 1));

    f[0] = (cnt << 1) + 1;

    vals = getdomain(sf->ss->t);

    for(i=0;i<cnt;i++) {
      b[-1-sf->ss->v] = vals[i];
      f[i+1] = Cgroundfma(sf->f,b);
    }

    return f;

  case Sforsome: /* Iterate over all values of the variable. */

    cnt = getdomainsize(sf->ss->t);

    f = (cfma)malloc(sizeof(int *) * (cnt + 1));

    f[0] = (cnt << 1);

    vals = getdomain(sf->ss->t);

    for(i=0;i<cnt;i++) {
      b[-1-sf->ss->v] = vals[i];
      f[i+1] = Cgroundfma(sf->f,b);
    }

    return f;

  }
}

void printcfma(cfma f) {
  int i;
  if(((int)f)&1) { /* Atom */
    switch(((int)f)&7) {
    case cTRUEtag: printf("TRUE"); break;
    case cFALSEtag: printf("FALSE"); break;
    case cPATOMtag: printatomi((((int)f) >> 3)); break;
    case cNATOMtag: printf("NOT "); printatomi((((int)f) >> 3)); break;
    }
  } else {
    int cnt;
    if(((int)(*f))&1) printf("(AND"); else printf("(OR");
    cnt = ((int)(*f)) >> 1;
    for(i=0;i<cnt;i++) {
      printf(" ");
      printcfma(f[i+1]);
    }
    printf(")");
  }
  printf("\n");
}
