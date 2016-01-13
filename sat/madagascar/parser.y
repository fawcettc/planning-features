
  /*   2010 (C) Jussi Rintanen  */

%{

#include "stdio.h"
#include "main.h"
#include "asyntax.h"

#define YYERROR_VERBOSE

void rparen(char *);

int COST;

%}

/*%define parse.error verbose */

%union {
  int i;
  intlist *intlistp;
  atomlist *atomlistp;
  atom *atomp;
  Sfma *Sfmap;
  Sfmalist *Sfmalistp;
  Seff *Seffp;
  Sefflist *Sefflistp;
  typedvarlist *typedvarlistp;
}

/* all of the terminal grammar symbols (tokens recognized
   by the lexical analyzer) */

%left RPAREN LPAREN DASH rwDEFINE rwACTION rwPARAMS rwEFFECT rwPRECOND rwPREDICATES rwREQUIREMENTS rwTYPES rwOBJECTS rwINIT rwGOAL rwDOMAIN rwTYPING rwAND rwOR rwWHEN rwNOT rwIMPLY rwFORALL rwPROBLEM EQUA rwEXISTS rwLENGTH rwCONSTANTS rwEITHER rwINCREASE rwMETRIC rwMINIMIZE

%left <i> ID VAR INT

%term LPAREN RPAREN DASH EQUA rwAND rwOR rwNOT rwIMPLY rwPRECOND rwDEFINE rwDOMAIN rwPROBLEM rwPREDICATES rwFUNCTIONS rwREQUIREMENTS rwACTION rwPARAMS rwEFFECT rwOBJECTS rwTYPES rwWHEN rwFORALL rwEXISTS rwLENGTH rwGOAL rwINIT rwCONSTANTS


/* What nonterminals return? */

%type <void> begin domain domaindefs domaindef actdef actdefs problem defs def typedvarlist typedatoms costexpr
%type <atomp> atom
%type <Sfmap> fma
%type <Sfmalistp> fmas
%type <Seffp> effect
%type <Sefflistp> effects
%type <intlistp> idlist varlist varidlist
%type <atomlistp> atomlist
%type <i> varid
%type <i> numexpr
%type <typedvarlistp> opvars opvar opvarlist objectlist

%start begin
%%

begin	: domain problem
	;

idlist	: ID idlist { $$ = intcons($1,$2); }
	| { $$ = EMPTYLIST; }
	;

costexpr	: LPAREN EQUA numexpr numexpr RPAREN { }
	;

atom	: LPAREN ID varidlist { rparen("term"); } RPAREN { $$ = newatom($2,$3); }
	;

atomlist	: atomlist atom { $$ = atomcons($2,$1); }
	| atomlist costexpr { $$ = $1; }
	| { $$ = EMPTYLIST; }
	;

varid	: VAR { $$ = $1; }
	| ID { $$ = $1; }
	;

varidlist	: varid varidlist { $$ = intcons($1,$2); }
		| { $$ = EMPTYLIST; }
	;

	/* PDDL definitions start here. */

domain	: LPAREN rwDEFINE LPAREN rwDOMAIN ID { rparen("domain"); } RPAREN domaindefs { rparen("domain body"); } RPAREN { storedomain($5); }
	;

domaindefs	: domaindefs domaindef
		| { }
	;

domaindef	: LPAREN rwPREDICATES typedatoms { rparen(":predicates"); } RPAREN { storepredicates(); }
	| LPAREN rwREQUIREMENTS idlist { rparen(":requirements"); } RPAREN { checkrequirements($3); }
	| LPAREN rwCONSTANTS objectlist { rparen(":constants"); } RPAREN { storeconstants($3); }
	| LPAREN rwFUNCTIONS functiondecls { rparen(":functions"); } RPAREN { }
	| LPAREN rwTYPES objectlist { rparen(":types"); } RPAREN { storetypes($3); }
	| LPAREN rwACTION { COST = 0; } ID actdefs { rparen(":action"); } RPAREN { addactioncost(COST); addnewaction($4); }
	;

actdefs	: actdef actdefs
	| actdef
	;

actdef	: rwPARAMS LPAREN opvars { rparen(":action definitions"); } RPAREN { addactionparameters($3); }
	| rwPRECOND fma { addactionprecond($2); }
	| rwEFFECT effect { addactioneffect($2); }
	;

opvars	: varlist { $$ = withtype(UNIVTYPE,$1); }
	| opvarlist { $$ = $1; }
	| { $$ = EMPTYLIST; }
	;

varlist	: VAR varlist { $$ = intcons($1,$2); }
	| VAR { $$ = intcons($1, EMPTYLIST); }
	;

opvarlist	: opvar opvarlist { $$ = TVappend($1,$2); }
	| opvar { $$ = $1; }
	;

opvar	: varlist DASH ID { $$ = withtype($3,$1); }
	;


problem		: LPAREN rwDEFINE LPAREN rwPROBLEM ID { rparen(":problem"); } RPAREN defs { rparen("problem definition"); } RPAREN { addproblem($5); }
	;

defs	: defs LPAREN def { rparen("problem definitions"); } RPAREN { }
	| LPAREN def { rparen("problem definitions"); } RPAREN { }
	;

def	: rwDOMAIN ID { checkdomain($2); }
	| rwOBJECTS objectlist  { storeobjects($2); }
	| rwINIT atomlist { storeinit($2); }
	| rwGOAL fma { storegoal($2); }
	| rwMETRIC rwMINIMIZE atomlist { }
	;


objectlist	: idlist DASH ID objectlist { $$ = TVappend(withtype($3,$1),$4); }
	| idlist { $$ = withtype(UNIVTYPE,$1); }
	;

typedvarlist	: VAR DASH ID typedvarlist { }
		| VAR DASH LPAREN rwEITHER ID idlist { rparen("typed variable list"); } RPAREN typedvarlist { }
		| VAR typedvarlist { }
		| { }
	;

typedatoms	:  typedatoms LPAREN ID typedvarlist { rparen("typed atom list"); } RPAREN { }
		|  { }
	;

functiondecls	: functiondecl functiondecls { }
		| { }
		;

functiondecl	: tdecl DASH ID { }
	| tdecl { }
	;

tdecl	: LPAREN ID typedvarlist { rparen("function list"); } RPAREN
	;



fma	: LPAREN rwAND { rparen("empty conjunction"); } RPAREN { $$ = Strue(); }
	| LPAREN rwAND fmas { rparen("conjunction"); } RPAREN { $$ = Sconjunction($3); }
	| LPAREN rwWHEN fma fma { rparen("when"); } RPAREN { $$ = Sconjunction(Sfmacons(Sneg($3),Sfmacons($4,EMPTYLIST))); }
	| LPAREN rwOR fmas { rparen("disjunction"); } RPAREN { $$ = Sdisjunction($3); }
	| LPAREN rwIMPLY fma fma { rparen("imply"); } RPAREN { $$ = Sdisjunction(Sfmacons(Sneg($3),Sfmacons($4,EMPTYLIST))); }
	| LPAREN rwNOT fma { rparen("not"); } RPAREN { $$ = Sneg($3); }
	| atom { $$ = Satom($1); }
	| LPAREN EQUA varid varid { rparen("equality"); } RPAREN { $$ = SfmaEQ($3,$4); }
	| LPAREN rwFORALL LPAREN opvars RPAREN fma { rparen("forall"); } RPAREN { $$ = Sfmaforall($4,$6); }
	| LPAREN rwEXISTS LPAREN opvars RPAREN fma { rparen("exists"); } RPAREN { $$ = Sfmaforsome($4,$6); }
	;

fmas	: fmas fma { $$ = Sfmacons($2,$1); }
	| fma { $$ = Sfmacons($1,EMPTYLIST); }
	;

effects	: effects effect { $$ = Seffcons($2,$1); }
	| effect { $$ = Seffcons($1,EMPTYLIST); }
	;

numexpr	: atom { $$ = 0; }
	| INT { $$ = $1; }
	;

effect:	LPAREN rwAND { rparen("empty conjunction"); } RPAREN { $$ = Seffconjunction(EMPTYLIST); }
	| LPAREN rwAND effects { rparen("compound effect"); } RPAREN { $$ = Seffconjunction($3); }
	| LPAREN rwWHEN fma effect { rparen("when"); } RPAREN { $$ = Seffwhen($3,$4); }
	| LPAREN rwFORALL LPAREN opvars RPAREN effect { rparen("forall"); } RPAREN { $$ = Seffforall($4,$6); }
	| atom { $$ = SPeffatom($1); }
	| LPAREN rwNOT atom { rparen("not"); } RPAREN { $$ = SNeffatom($3); }
	| LPAREN rwINCREASE atom numexpr { rparen("increase"); } RPAREN { $$ = Seffconjunction(NULL); COST = $4; }
	;

%%

void parseerror(char *s) {
  errorstring = s;
}

void rparen(char *s) {
  errorstring = s;
}
