
  /*   2010 (C) Jussi Rintanen   */

#include <stdio.h>
#include <stdlib.h>
#include "interface.h"
#include "clausedb.h"
#include "main.h"

#define noDEBUG

int lineno;

void nextline(FILE *f) {
  char c;
  do {
    c = getc(f);
  } while(c != '\n');
  lineno += 1;
}

int numeric(char c) { return '0' <= c && c <= '9'; }
int numvalue(char c) { return c-'0'; }

int readnat(FILE *f) {
  char c;
  int i;
  do {
    c = getc(f);
    if(c == '%') nextline(f);
    if(c == '\n') lineno += 1;
  } while (c == ' ' || c == '\n' || c == '\t' || c == '%');
  i = 0;
  if(! numeric(c)) {
    fprintf(stderr,"Found illegal character %c on line %i ... exiting.\n",c,lineno);
    exit(0);
  }
  i = numvalue(c);
  do {
    c = getc(f);
    if(numeric(c)) i = i*10+numvalue(c);
  } while(numeric(c));
  ungetc(c,f);
  return i;
}

int readint(FILE *f) {
  char c;
  int i;
  int neg;
  neg = 0;
  do {
    c = getc(f);
    if(c == '%') nextline(f);
    if(c == '\n') lineno += 1;
  } while (c == ' ' || c == '\n' || c == '\t' || c == '%');
  i = 0;
  if((! numeric(c)) && (c != '-')) {
    fprintf(stderr,"Found illegal character %c on line %i ... exiting.\n",c,lineno);
    exit(0);
  }
  if(c == '-') {
    neg = 1; i = 0;
  } else i = numvalue(c);
  do {
    c = getc(f);
    if(numeric(c)) i = i*10+numvalue(c);
  } while(numeric(c));
  ungetc(c,f);
  return neg ? 0-i : i;
}

int dsatlit(int l) {
  if(l < 0) return ((-l-1) << 1)|1;
  return ((l-1) << 1);
}

int inputclause[100000];

satinstance DIMACSinput() {
  FILE *f;
  satinstance sati;
  int i,len,j,n;
  char c;
  int numberOfProps;
  int numberOfClauses;

  if(nOfInputFiles != 1) {
    fprintf(stderr,"ERROR: DIMACS input has to be exactly one file!\n");
    exit(1);
  }

  f = fopen(inputfiles[0],"r");
  if(f == NULL) {
    fprintf(stderr,"ERROR: could not open file '%s'\n",inputfiles[0]);
    exit(1);
  }

  lineno = 1;

  initclausedb();

  numberOfProps = -1;
  numberOfClauses = -1;

  while(1 == 1) {
    c = getc(f);
    switch(c) {
    case 'c': nextline(f); break;
    case 'p':
      printf("Reading DIMACS header\n");
      do { c = getc(f); } while(c != 'c');
      do { c = getc(f); } while(c != 'n');
      do { c = getc(f); } while(c != 'f');
      numberOfProps = readnat(f);
      numberOfClauses = readnat(f);
      printf("%i variables %i clauses\n",numberOfProps,numberOfClauses);
      nextline(f);
      break;
    default:
      ungetc(c,f);
      goto preambleended;
    }
  }
 preambleended:    

  sati = newinstance(1,1,numberOfProps,0,0);

  for(i=0;i<numberOfClauses;i++) {

    len = 0;
    do {
      n = readint(f);
      inputclause[len] = n;
      len += 1;
    } while(n != 0);

    len = len-1;

    switch(len) {
    case 1: add1clause(sati,dsatlit(inputclause[0]),InitC); break;
    case 2:
      add2clause(sati,dsatlit(inputclause[0]),dsatlit(inputclause[1]),InitC);
      break;
    default:
#ifdef DEBUG
      printf("adding clause of length %i\n",len);
#endif
      addnewclause(sati,len,InitC);
      for(j=0;j<len;j++) addliteral(sati,j,dsatlit(inputclause[j]));
      finishclause(sati);
    }
  }
  fclose(f);
  printf("Finished reading file.\n");
  return sati;
}
