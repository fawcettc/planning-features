
  /*   2012 (C) Jussi Rintanen  */

/* Definitions */

%{

#include <stdio.h>
#include <stdlib.h>
#include "asyntax.h"
#include "parser.tab.h"
#include "main.h"

#include "tables.h"

  int lexeropen(char *fn) {
    yyin = fopen(fn,"r");
    if(yyin == NULL) {
      fprintf(stderr,"ERROR: opening file %s\n",fn);
      exit(1);
    }
    return 0;
  }

  int lexeropenstdin() {
    yyin = stdin;
    nOfInputFiles = 0;
    currentInputFile=-1;
    return 0;
  }

int yywrap() { 
  linenumber = 1;
  if(currentInputFile == nOfInputFiles-1) return 1;
  fclose(yyin);
  currentInputFile += 1;
  yyin = fopen(inputfiles[currentInputFile],"r");
  if(yyin == NULL) {
    fprintf(stderr,"ERROR: opening input file #%i: %s",currentInputFile,inputfiles[currentInputFile]);
    exit(1);
  }
  return 0;
}

void lowercase(char *tmp) {
  while(*tmp != 0) {
    if(*tmp >= 'A' && *tmp <= 'Z') *tmp += ('a'-'A');
    tmp += 1;
  }
}

%}

ALPHA	[a-zA-Z]
ALPNUM	[0-9a-zA-Z\-_,/]
NUM	[0-9]

%%

":"{ALPHA}{ALPNUM}*	{
			lowercase(yytext);
#ifdef DEBUG
			printf(":ID %s\n",yytext);
#endif
			if(strcmp(yytext,":action") == 0) return rwACTION;
			if(strcmp(yytext,":parameters") == 0) return rwPARAMS;
			if(strcmp(yytext,":effect") == 0) return rwEFFECT;
			if(strcmp(yytext,":precondition") == 0) return rwPRECOND;
			if(strcmp(yytext,":predicates") == 0) return rwPREDICATES;
			if(strcmp(yytext,":requirements") == 0) return rwREQUIREMENTS;
			if(strcmp(yytext,":functions") == 0) return rwFUNCTIONS;
			if(strcmp(yytext,":types") == 0) return rwTYPES;
			if(strcmp(yytext,":constants") == 0) return rwCONSTANTS;
			if(strcmp(yytext,":objects") == 0) return rwOBJECTS;
			if(strcmp(yytext,":init") == 0) return rwINIT;
			if(strcmp(yytext,":goal") == 0) return rwGOAL;
			if(strcmp(yytext,":domain") == 0) return rwDOMAIN;
			if(strcmp(yytext,":metric") == 0) return rwMETRIC;
			
			yylval.i = symbolindex(yytext);
			return ID;
			}

{ALPHA}{ALPNUM}*	{
			lowercase(yytext);
#ifdef DEBUG
			printf("ID %s\n",yytext);
#endif

			if(strcmp(yytext,"define") == 0) return rwDEFINE;
			if(strcmp(yytext,"and") == 0) return rwAND;
			if(strcmp(yytext,"or") == 0) return rwOR;
			if(strcmp(yytext,"imply") == 0) return rwIMPLY;
			if(strcmp(yytext,"when") == 0) return rwWHEN;
			if(strcmp(yytext,"not") == 0) return rwNOT;
			if(strcmp(yytext,"exists") == 0) return rwEXISTS;
			if(strcmp(yytext,"forall") == 0) return rwFORALL;
			if(strcmp(yytext,"problem") == 0) return rwPROBLEM;
			if(strcmp(yytext,"domain") == 0) return rwDOMAIN;
			if(strcmp(yytext,"either") == 0) return rwEITHER;
			if(strcmp(yytext,"increase") == 0) return rwINCREASE;
			if(strcmp(yytext,"minimize") == 0) return rwMINIMIZE;
			
			yylval.i = symbolindex(yytext);
			return ID;
			}

"?"{ALPHA}{ALPNUM}*	{
			lowercase(yytext);
#ifdef DEBUG
			printf("VAR %s\n",yytext);
#endif
			yylval.i = symbolindex(yytext);
			return VAR;
			}

{NUM}{NUM}*		{
			sscanf(yytext,"%d",&yylval.i);
			return INT;
			}

"("			{
#ifdef DEBUG
			printf("Left (\n");
#endif
			return LPAREN;
			}


")"			{
#ifdef DEBUG
			printf("Right )\n");
#endif
			return RPAREN;
			}

"-"			{
#ifdef DEBUG
			printf("DASH\n");
#endif
			return DASH;
			}

"="			{
#ifdef DEBUG
			printf("EQUA\n");
#endif
			return EQUA;
			}

[ \015\t]+			{  }

\n			{ linenumber += 1; }

";".*\n			{ linenumber += 1; }

.			printf("Unrecognized character %i '%s'\n",yytext[0],yytext);

%%

/* User subroutines */
