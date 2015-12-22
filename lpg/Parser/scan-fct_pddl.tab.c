
/* A Bison parser, made by GNU Bison 2.4.1.  */

/* Skeleton implementation for Bison's Yacc-like parsers in C
   
      Copyright (C) 1984, 1989, 1990, 2000, 2001, 2002, 2003, 2004, 2005, 2006
   Free Software Foundation, Inc.
   
   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.
   
   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.
   
   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <http://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.
   
   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output.  */
#define YYBISON 1

/* Bison version.  */
#define YYBISON_VERSION "2.4.1"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1

/* Using locations.  */
#define YYLSP_NEEDED 0

/* Substitute the variable and function names.  */
#define yyparse         fct_pddlparse
#define yylex           fct_pddllex
#define yyerror         fct_pddlerror
#define yylval          fct_pddllval
#define yychar          fct_pddlchar
#define yydebug         fct_pddldebug
#define yynerrs         fct_pddlnerrs


/* Copy the first part of user declarations.  */

/* Line 189 of yacc.c  */
#line 19 "scan-fct_pddl.y"

#ifdef YYDEBUG
   int yydebug = 1;
#define YYPRINT(file, type, value)   yyprint (file, type, value)  
#endif

#define YYMAXDEPTH 100000 
#define YY_NO_UNPUT

#define YYSTACK_USE_ALLOCA FALSE

#include <stdio.h>
#include <string.h> 
#include "ff.h"
#include "lpg.h"
#include "memory.h"
#include "parse.h"

#define yyin fct_pddlin
#define yytext fct_pddltext

#ifndef SCAN_ERR
#define SCAN_ERR
#define DEFINE_EXPECTED            0
#define PROBLEM_EXPECTED           1
#define PROBNAME_EXPECTED          2
#define LBRACKET_EXPECTED          3
#define RBRACKET_EXPECTED          4
#define DOMDEFS_EXPECTED           5
#define REQUIREM_EXPECTED          6
#define TYPEDLIST_EXPECTED         7
#define DOMEXT_EXPECTED            8
#define DOMEXTNAME_EXPECTED        9
#define TYPEDEF_EXPECTED          10
#define CONSTLIST_EXPECTED        11
#define PREDDEF_EXPECTED          12 
#define NAME_EXPECTED             13
#define VARIABLE_EXPECTED         14
#define ACTIONFUNCTOR_EXPECTED    15
#define ATOM_FORMULA_EXPECTED     16
#define EFFECT_DEF_EXPECTED       17
#define NEG_FORMULA_EXPECTED      18
#define NOT_SUPPORTED             19
#define SITUATION_EXPECTED        20
#define SITNAME_EXPECTED          21
#define BDOMAIN_EXPECTED          22
#define BADDOMAIN                 23
#define INIFACTS                  24
#define GOALDEF                   25
#define ADLGOAL                   26
#endif


static char * serrmsg[] = {
  "'define' expected",
  "'problem' expected",
  "problem name expected",
  "'(' expected",
  "')' expected",
  "additional domain definitions expected",
  "requirements (e.g. ':strips') expected",
  "typed list of <%s> expected",
  "domain extension expected",
  "domain to be extented expected",
  "type definition expected",
  "list of constants expected",
  "predicate definition expected",
  "<name> expected",
  "<variable> expected",
  "action functor expected",
  "atomic formula expected",
  "effect definition expected",
  "negated atomic formula expected",
  "requirement %s not supported by this IPP version",  
  "'situation' expected",
  "situation name expected",
  "':domain' expected",
  "this problem needs another domain file",
  "initial facts definition expected",
  "goal definition expected",
  "first order logic expression expected",
  NULL
};


static int sact_err;
static char *sact_err_par = NULL;
static Bool sis_negated = FALSE;

 int yylex(void);
 int yyerror(char *msg); 

/* 
 * call	bison -pfct -bscan-fct scan-fct.y
 */
void fcterr( int errno, char *par ) {

  sact_err = errno;

  if ( sact_err_par ) {
    free( sact_err_par );
  }
  if ( par ) {
    sact_err_par = new_Token( strlen(par)+1 );
    strcpy( sact_err_par, par);
  } else {
    sact_err_par = NULL;
  }

}

 extern void opserr( int errno, char *par );
 extern int supported( char *str );



/* Line 189 of yacc.c  */
#line 198 "scan-fct_pddl.tab.c"

/* Enabling traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif

/* Enabling verbose error messages.  */
#ifdef YYERROR_VERBOSE
# undef YYERROR_VERBOSE
# define YYERROR_VERBOSE 1
#else
# define YYERROR_VERBOSE 0
#endif

/* Enabling the token table.  */
#ifndef YYTOKEN_TABLE
# define YYTOKEN_TABLE 0
#endif


/* Tokens.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
   /* Put the tokens into the symbol table, so that GDB and other debuggers
      know about them.  */
   enum yytokentype {
     DEFINE_TOK = 258,
     PROBLEM_TOK = 259,
     SITUATION_TOK = 260,
     BSITUATION_TOK = 261,
     OBJECTS_TOK = 262,
     BDOMAIN_TOK = 263,
     INIT_TOK = 264,
     GOAL_TOK = 265,
     AND_TOK = 266,
     NOT_TOK = 267,
     NAME = 268,
     VARIABLE = 269,
     EQUAL_TOK = 270,
     FORALL_TOK = 271,
     IMPLY_TOK = 272,
     OR_TOK = 273,
     EXISTS_TOK = 274,
     EITHER_TOK = 275,
     OPEN_PAREN = 276,
     CLOSE_PAREN = 277,
     REQUIREMENTS_TOK = 278,
     GREATER_OR_EQUAL_TOK = 279,
     LESS_THAN_OR_EQUAL_TOK = 280,
     INTVAL = 281,
     FLOATVAL = 282,
     PLUS_TOK = 283,
     MINUS_TOK = 284,
     MUL_TOK = 285,
     DIV_TOK = 286,
     GREATER_TOK = 287,
     LESS_THAN_TOK = 288,
     METRIC_TOK = 289,
     MINIMIZE_TOK = 290,
     MAXIMIZE_TOK = 291,
     LENGTH_TOK = 292,
     SERIAL_TOK = 293,
     PARALLEL_TOK = 294,
     TOTAL_TIME_TOK = 295,
     TIMED_EL_TOK = 296,
     UMINUS = 297
   };
#endif



#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
{

/* Line 214 of yacc.c  */
#line 139 "scan-fct_pddl.y"


  char string[MAX_LENGTH];
  char* pstring;
  PlNode* pPlNode;
  FactList* pFactList;
  TokenList* pTokenList;
  TypedList* pTypedList;

    int ival;
    float fval;



/* Line 214 of yacc.c  */
#line 291 "scan-fct_pddl.tab.c"
} YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif


/* Copy the second part of user declarations.  */


/* Line 264 of yacc.c  */
#line 303 "scan-fct_pddl.tab.c"

#ifdef short
# undef short
#endif

#ifdef YYTYPE_UINT8
typedef YYTYPE_UINT8 yytype_uint8;
#else
typedef unsigned char yytype_uint8;
#endif

#ifdef YYTYPE_INT8
typedef YYTYPE_INT8 yytype_int8;
#elif (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
typedef signed char yytype_int8;
#else
typedef short int yytype_int8;
#endif

#ifdef YYTYPE_UINT16
typedef YYTYPE_UINT16 yytype_uint16;
#else
typedef unsigned short int yytype_uint16;
#endif

#ifdef YYTYPE_INT16
typedef YYTYPE_INT16 yytype_int16;
#else
typedef short int yytype_int16;
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif ! defined YYSIZE_T && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned int
# endif
#endif

#define YYSIZE_MAXIMUM ((YYSIZE_T) -1)

#ifndef YY_
# if YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(msgid) dgettext ("bison-runtime", msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(msgid) msgid
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YYUSE(e) ((void) (e))
#else
# define YYUSE(e) /* empty */
#endif

/* Identity function, used to suppress warnings about constant conditions.  */
#ifndef lint
# define YYID(n) (n)
#else
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static int
YYID (int yyi)
#else
static int
YYID (yyi)
    int yyi;
#endif
{
  return yyi;
}
#endif

#if ! defined yyoverflow || YYERROR_VERBOSE

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#     ifndef _STDLIB_H
#      define _STDLIB_H 1
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's `empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (YYID (0))
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined _STDLIB_H \
       && ! ((defined YYMALLOC || defined malloc) \
	     && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef _STDLIB_H
#    define _STDLIB_H 1
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined _STDLIB_H && (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* ! defined yyoverflow || YYERROR_VERBOSE */


#if (! defined yyoverflow \
     && (! defined __cplusplus \
	 || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yytype_int16 yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (sizeof (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (sizeof (yytype_int16) + sizeof (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

/* Copy COUNT objects from FROM to TO.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(To, From, Count) \
      __builtin_memcpy (To, From, (Count) * sizeof (*(From)))
#  else
#   define YYCOPY(To, From, Count)		\
      do					\
	{					\
	  YYSIZE_T yyi;				\
	  for (yyi = 0; yyi < (Count); yyi++)	\
	    (To)[yyi] = (From)[yyi];		\
	}					\
      while (YYID (0))
#  endif
# endif

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)				\
    do									\
      {									\
	YYSIZE_T yynewbytes;						\
	YYCOPY (&yyptr->Stack_alloc, Stack, yysize);			\
	Stack = &yyptr->Stack_alloc;					\
	yynewbytes = yystacksize * sizeof (*Stack) + YYSTACK_GAP_MAXIMUM; \
	yyptr += yynewbytes / sizeof (*yyptr);				\
      }									\
    while (YYID (0))

#endif

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  5
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   272

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  43
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  46
/* YYNRULES -- Number of rules.  */
#define YYNRULES  115
/* YYNRULES -- Number of states.  */
#define YYNSTATES  261

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   297

#define YYTRANSLATE(YYX)						\
  ((unsigned int) (YYX) <= YYMAXUTOK ? yytranslate[YYX] : YYUNDEFTOK)

/* YYTRANSLATE[YYLEX] -- Bison symbol number corresponding to YYLEX.  */
static const yytype_uint8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     4,     7,     8,    15,    20,    25,    26,
      29,    32,    35,    38,    40,    42,    44,    49,    50,    56,
      58,    61,    63,    69,    75,    76,    82,    84,    89,    94,
      99,   105,   113,   121,   123,   129,   131,   136,   142,   148,
     154,   160,   162,   167,   169,   171,   173,   175,   177,   179,
     184,   190,   196,   202,   208,   210,   212,   214,   216,   217,
     220,   225,   227,   232,   233,   236,   238,   240,   242,   245,
     246,   252,   256,   259,   260,   266,   270,   273,   275,   277,
     282,   284,   289,   290,   293,   299,   301,   303,   308,   314,
     320,   326,   332,   334,   336,   338,   342,   348,   354,   360,
     366,   372,   378,   384,   390,   395,   396,   401,   406,   409,
     413,   414,   415,   423,   424,   425
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int8 yyrhs[] =
{
      44,     0,    -1,    -1,    45,    44,    -1,    -1,    21,     3,
      46,    47,    49,    22,    -1,    21,     4,    13,    22,    -1,
      21,     8,    13,    22,    -1,    -1,    50,    49,    -1,    51,
      49,    -1,    55,    49,    -1,    48,    49,    -1,    84,    -1,
      77,    -1,    80,    -1,    21,     7,    71,    22,    -1,    -1,
      21,     9,    52,    53,    22,    -1,    54,    -1,    54,    53,
      -1,    74,    -1,    21,    41,    63,    74,    22,    -1,    21,
      15,    60,    62,    22,    -1,    -1,    21,    10,    56,    57,
      22,    -1,    66,    -1,    21,    11,    65,    22,    -1,    21,
      18,    65,    22,    -1,    21,    12,    57,    22,    -1,    21,
      17,    57,    57,    22,    -1,    21,    19,    21,    72,    22,
      57,    22,    -1,    21,    16,    21,    72,    22,    57,    22,
      -1,    58,    -1,    21,    61,    59,    59,    22,    -1,    62,
      -1,    21,    29,    59,    22,    -1,    21,    29,    59,    59,
      22,    -1,    21,    28,    59,    59,    22,    -1,    21,    30,
      59,    59,    22,    -1,    21,    31,    59,    59,    22,    -1,
      60,    -1,    21,    64,    68,    22,    -1,    64,    -1,    32,
      -1,    33,    -1,    15,    -1,    24,    -1,    25,    -1,    21,
      29,    62,    22,    -1,    21,    29,    62,    62,    22,    -1,
      21,    28,    62,    62,    22,    -1,    21,    30,    62,    62,
      22,    -1,    21,    31,    62,    62,    22,    -1,    63,    -1,
      26,    -1,    27,    -1,    13,    -1,    -1,    57,    65,    -1,
      21,    12,    67,    22,    -1,    67,    -1,    21,    73,    68,
      22,    -1,    -1,    69,    68,    -1,    13,    -1,    14,    -1,
      13,    -1,    13,    70,    -1,    -1,    13,    83,    70,    22,
      71,    -1,    13,    82,    71,    -1,    13,    71,    -1,    -1,
      14,    83,    70,    22,    72,    -1,    14,    82,    72,    -1,
      14,    72,    -1,    13,    -1,    15,    -1,    21,    12,    75,
      22,    -1,    75,    -1,    21,    73,    76,    22,    -1,    -1,
      13,    76,    -1,    21,    34,    78,    79,    22,    -1,    35,
      -1,    36,    -1,    21,    29,    79,    22,    -1,    21,    29,
      79,    79,    22,    -1,    21,    28,    79,    79,    22,    -1,
      21,    30,    79,    79,    22,    -1,    21,    31,    79,    79,
      22,    -1,    62,    -1,    60,    -1,    40,    -1,    21,    79,
      22,    -1,    21,    29,    62,    79,    22,    -1,    21,    29,
      79,    62,    22,    -1,    21,    28,    62,    79,    22,    -1,
      21,    28,    79,    62,    22,    -1,    21,    31,    62,    79,
      22,    -1,    21,    31,    79,    62,    22,    -1,    21,    30,
      62,    79,    22,    -1,    21,    30,    79,    62,    22,    -1,
      21,    37,    81,    22,    -1,    -1,    21,    38,    26,    22,
      -1,    21,    39,    26,    22,    -1,    29,    13,    -1,    29,
      21,    20,    -1,    -1,    -1,    21,    23,    85,    13,    86,
      87,    22,    -1,    -1,    -1,    13,    88,    87,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint16 yyrline[] =
{
       0,   258,   258,   261,   268,   267,   283,   293,   303,   306,
     308,   310,   312,   315,   317,   319,   326,   352,   351,   363,
     370,   380,   382,   394,   409,   408,   426,   439,   445,   451,
     457,   467,   482,   498,   510,   525,   531,   541,   553,   566,
     578,   590,   598,   605,   627,   632,   637,   642,   647,   655,
     662,   669,   676,   683,   690,   698,   708,   720,   765,   769,
     782,   788,   797,   809,   813,   824,   830,   840,   847,   859,
     861,   870,   881,   901,   903,   912,   923,   944,   950,   960,
     970,   980,   992,   994,  1006,  1015,  1020,  1027,  1037,  1049,
    1062,  1074,  1086,  1092,  1098,  1103,  1109,  1120,  1131,  1142,
    1153,  1164,  1175,  1186,  1200,  1203,  1205,  1207,  1211,  1219,
    1225,  1229,  1224,  1240,  1244,  1243
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "DEFINE_TOK", "PROBLEM_TOK",
  "SITUATION_TOK", "BSITUATION_TOK", "OBJECTS_TOK", "BDOMAIN_TOK",
  "INIT_TOK", "GOAL_TOK", "AND_TOK", "NOT_TOK", "NAME", "VARIABLE",
  "EQUAL_TOK", "FORALL_TOK", "IMPLY_TOK", "OR_TOK", "EXISTS_TOK",
  "EITHER_TOK", "OPEN_PAREN", "CLOSE_PAREN", "REQUIREMENTS_TOK",
  "GREATER_OR_EQUAL_TOK", "LESS_THAN_OR_EQUAL_TOK", "INTVAL", "FLOATVAL",
  "PLUS_TOK", "MINUS_TOK", "MUL_TOK", "DIV_TOK", "GREATER_TOK",
  "LESS_THAN_TOK", "METRIC_TOK", "MINIMIZE_TOK", "MAXIMIZE_TOK",
  "LENGTH_TOK", "SERIAL_TOK", "PARALLEL_TOK", "TOTAL_TIME_TOK",
  "TIMED_EL_TOK", "UMINUS", "$accept", "file", "problem_definition", "$@1",
  "problem_name", "base_domain_name", "problem_defs", "objects_def",
  "init_def", "$@2", "init_el_plus", "init_el", "goal_def", "$@3",
  "adl_goal_description", "f_comp", "f_exp", "f_head", "binary_comp",
  "num_exp", "number", "function_symbol", "adl_goal_description_star",
  "literal_term", "atomic_formula_term", "term_star", "term", "name_plus",
  "typed_list_name", "typed_list_variable", "predicate", "literal_name",
  "atomic_formula_name", "name_star", "metric_spec", "optimization",
  "ground_f_exp", "length_spec", "ser_par", "type", "either",
  "require_def", "$@4", "$@5", "require_key_star", "$@6", 0
};
#endif

# ifdef YYPRINT
/* YYTOKNUM[YYLEX-NUM] -- Internal token number corresponding to
   token YYLEX-NUM.  */
static const yytype_uint16 yytoknum[] =
{
       0,   256,   257,   258,   259,   260,   261,   262,   263,   264,
     265,   266,   267,   268,   269,   270,   271,   272,   273,   274,
     275,   276,   277,   278,   279,   280,   281,   282,   283,   284,
     285,   286,   287,   288,   289,   290,   291,   292,   293,   294,
     295,   296,   297
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    43,    44,    44,    46,    45,    47,    48,    49,    49,
      49,    49,    49,    49,    49,    49,    50,    52,    51,    53,
      53,    54,    54,    54,    56,    55,    57,    57,    57,    57,
      57,    57,    57,    57,    58,    59,    59,    59,    59,    59,
      59,    59,    60,    60,    61,    61,    61,    61,    61,    62,
      62,    62,    62,    62,    62,    63,    63,    64,    65,    65,
      66,    66,    67,    68,    68,    69,    69,    70,    70,    71,
      71,    71,    71,    72,    72,    72,    72,    73,    73,    74,
      74,    75,    76,    76,    77,    78,    78,    79,    79,    79,
      79,    79,    79,    79,    79,    79,    79,    79,    79,    79,
      79,    79,    79,    79,    80,    81,    81,    81,    82,    83,
      85,    86,    84,    87,    88,    87
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     0,     2,     0,     6,     4,     4,     0,     2,
       2,     2,     2,     1,     1,     1,     4,     0,     5,     1,
       2,     1,     5,     5,     0,     5,     1,     4,     4,     4,
       5,     7,     7,     1,     5,     1,     4,     5,     5,     5,
       5,     1,     4,     1,     1,     1,     1,     1,     1,     4,
       5,     5,     5,     5,     1,     1,     1,     1,     0,     2,
       4,     1,     4,     0,     2,     1,     1,     1,     2,     0,
       5,     3,     2,     0,     5,     3,     2,     1,     1,     4,
       1,     4,     0,     2,     5,     1,     1,     4,     5,     5,
       5,     5,     1,     1,     1,     3,     5,     5,     5,     5,
       5,     5,     5,     5,     4,     0,     4,     4,     2,     3,
       0,     0,     7,     0,     0,     3
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       2,     0,     0,     2,     4,     1,     3,     0,     0,     8,
       0,     0,     8,     0,     8,     8,     8,    14,    15,    13,
       0,    69,     0,    17,    24,   110,     0,   105,    12,     5,
       9,    10,    11,     6,    69,     0,     0,     0,     0,     0,
      85,    86,     0,     0,     0,     0,    72,    69,     0,    16,
       7,     0,     0,    19,    21,    80,     0,     0,    33,    26,
      61,   111,    57,     0,    55,    56,    94,    93,    92,    54,
      43,     0,     0,     0,   104,   108,     0,    71,    67,     0,
       0,    77,    78,     0,    82,    18,    20,    58,     0,    46,
       0,     0,    58,     0,    47,    48,    44,    45,     0,    63,
      25,   113,     0,     0,     0,     0,    43,     0,    84,     0,
       0,   109,    68,    69,     0,     0,     0,     0,     0,    82,
       0,    58,     0,     0,     0,    73,     0,     0,    73,     0,
       0,    41,    35,    65,    66,     0,    63,   114,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,    95,   106,
     107,    70,    78,    79,    63,     0,     0,     0,     0,    83,
      81,    59,    27,    29,    60,    73,     0,     0,    28,     0,
       0,     0,     0,     0,     0,    62,    64,   113,   112,     0,
       0,     0,     0,    49,     0,     0,    87,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,    42,     0,     0,
       0,     0,    23,    22,    76,    73,     0,     0,    30,     0,
       0,    35,     0,    35,     0,    35,     0,    35,    34,   115,
      51,    98,    99,    89,    50,    96,    97,    88,    52,   102,
     103,    90,    53,   100,   101,    91,     0,     0,     0,     0,
      75,     0,     0,     0,     0,     0,    36,     0,     0,     0,
       0,     0,     0,    73,    32,    31,    38,    37,    39,    40,
      74
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,     3,     7,     9,    12,    13,    14,    15,    37,
      52,    53,    16,    38,   121,    58,   130,    67,    98,   132,
      69,    70,   122,    59,    60,   147,   136,    79,    35,   166,
      84,    54,    55,   120,    17,    42,    71,    18,    44,    47,
      48,    19,    39,   101,   138,   177
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -127
static const yytype_int16 yypact[] =
{
      -5,    23,    33,    -5,  -127,  -127,  -127,    15,    70,    69,
      93,     1,    69,    88,    69,    69,    69,  -127,  -127,  -127,
      90,   112,   113,  -127,  -127,  -127,    22,   118,  -127,  -127,
    -127,  -127,  -127,  -127,     5,   131,   132,   119,   134,   150,
    -127,  -127,   124,    32,   145,    10,  -127,   112,   155,  -127,
    -127,     2,   152,   119,  -127,  -127,   166,   154,  -127,  -127,
    -127,  -127,  -127,    19,  -127,  -127,  -127,  -127,  -127,  -127,
    -127,   171,   177,   182,  -127,  -127,   160,  -127,   155,   190,
     192,  -127,    63,    60,   201,  -127,  -127,   134,   134,    74,
     194,   134,   134,   196,  -127,  -127,  -127,  -127,   179,   102,
    -127,   203,   124,   124,   124,   124,   102,   197,  -127,   198,
     199,  -127,  -127,   112,    40,   200,   205,    87,   202,   201,
     204,   134,   206,   207,   208,   210,   134,   209,   210,    -1,
     179,  -127,  -127,  -127,  -127,   211,   102,  -127,   212,   124,
     124,    51,   122,   124,   124,   124,   124,   213,  -127,  -127,
    -127,  -127,  -127,  -127,   102,   158,   214,   189,   215,  -127,
    -127,  -127,  -127,  -127,  -127,     8,   216,   217,  -127,   218,
     179,   179,   179,   179,   219,  -127,  -127,   203,  -127,   220,
     221,   222,   223,  -127,   224,   225,  -127,   226,   227,   228,
     229,   230,   231,   232,   233,   234,   235,  -127,    87,    87,
      87,    87,  -127,  -127,  -127,   210,   155,   134,  -127,   134,
     179,    87,   139,   120,   179,    87,   179,    87,  -127,  -127,
    -127,  -127,  -127,  -127,  -127,  -127,  -127,  -127,  -127,  -127,
    -127,  -127,  -127,  -127,  -127,  -127,    87,   120,    87,    87,
    -127,   236,   237,   238,   239,   220,  -127,   240,   224,   241,
     228,   242,   232,   210,  -127,  -127,  -127,  -127,  -127,  -127,
    -127
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -127,   262,  -127,  -127,  -127,  -127,   195,  -127,  -127,  -127,
     172,  -127,  -127,  -127,   -37,  -127,  -105,   -78,  -127,   -42,
     144,   -60,   -79,  -127,   178,   -92,  -127,   -73,   -28,  -126,
     176,   149,   188,   151,  -127,  -127,   -22,  -127,  -127,   104,
     106,  -127,  -127,  -127,    95,  -127
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -79
static const yytype_int16 yytable[] =
{
      68,    57,   169,   106,   117,   112,    46,   135,    21,    22,
      23,    24,    62,   127,    80,    81,     1,    82,    34,    77,
     131,    68,   165,    75,    25,   174,     4,   170,   171,   172,
     173,    76,    62,     5,    45,    26,     8,    45,    27,   204,
      63,   107,   161,    83,   176,    64,    65,   102,   103,   104,
     105,   123,   131,    81,   126,   152,   154,    40,    41,    66,
     139,   141,   143,   145,    62,   210,   212,   214,   216,   154,
      72,    73,    63,   183,    10,   156,    62,    64,    65,   240,
     140,   142,   144,   146,   116,   151,    64,    65,   -78,   167,
      11,    66,   131,   131,   131,   131,   -78,   179,   181,   184,
     187,   189,   191,   193,   195,   244,    20,   247,   155,   249,
      29,   251,    33,    64,    65,   133,   134,   180,   182,   185,
     188,   190,   192,   194,   196,    34,    36,   260,   211,   213,
     215,   217,   131,   241,   131,    62,   131,    62,   131,    43,
      51,   155,   183,    63,   186,    63,    64,    65,    64,    65,
      64,    65,    62,    49,    50,    56,   236,   237,   238,   239,
     129,   246,    66,    61,    66,    64,    65,    74,    78,   245,
     242,   248,   243,   250,    85,   252,   100,    87,    88,    81,
     111,    89,    90,    91,    92,    93,   198,   199,   200,   201,
      94,    95,    62,   108,   245,   248,   250,   252,    96,    97,
     129,    80,    81,   109,   152,    64,    65,    28,   110,    30,
      31,    32,   113,   114,   119,   125,   137,   128,    62,   148,
     149,   150,   153,   157,   165,    86,   160,   118,   162,   163,
     164,   168,    99,   175,   178,   197,   202,   203,   207,   208,
     209,   218,   220,   221,   222,   223,   224,   225,   226,   227,
     228,   229,   230,   231,   232,   233,   234,   235,   253,   254,
     255,   256,   257,   258,   259,     6,   124,   158,   115,   205,
     159,   206,   219
};

static const yytype_uint8 yycheck[] =
{
      42,    38,   128,    63,    82,    78,    34,    99,     7,     8,
       9,    10,    13,    92,    12,    13,    21,    15,    13,    47,
      98,    63,    14,    13,    23,   130,     3,    28,    29,    30,
      31,    21,    13,     0,    29,    34,    21,    29,    37,   165,
      21,    63,   121,    41,   136,    26,    27,    28,    29,    30,
      31,    88,   130,    13,    91,    15,   116,    35,    36,    40,
     102,   103,   104,   105,    13,   170,   171,   172,   173,   129,
      38,    39,    21,    22,     4,   117,    13,    26,    27,   205,
     102,   103,   104,   105,    21,   113,    26,    27,    14,   126,
      21,    40,   170,   171,   172,   173,    22,   139,   140,   141,
     142,   143,   144,   145,   146,   210,    13,   212,    21,   214,
      22,   216,    22,    26,    27,    13,    14,   139,   140,   141,
     142,   143,   144,   145,   146,    13,    13,   253,   170,   171,
     172,   173,   210,   206,   212,    13,   214,    13,   216,    21,
      21,    21,    22,    21,    22,    21,    26,    27,    26,    27,
      26,    27,    13,    22,    22,    21,   198,   199,   200,   201,
      21,    22,    40,    13,    40,    26,    27,    22,    13,   211,
     207,   213,   209,   215,    22,   217,    22,    11,    12,    13,
      20,    15,    16,    17,    18,    19,    28,    29,    30,    31,
      24,    25,    13,    22,   236,   237,   238,   239,    32,    33,
      21,    12,    13,    26,    15,    26,    27,    12,    26,    14,
      15,    16,    22,    21,    13,    21,    13,    21,    13,    22,
      22,    22,    22,    21,    14,    53,    22,    83,    22,    22,
      22,    22,    56,    22,    22,    22,    22,    22,    22,    22,
      22,    22,    22,    22,    22,    22,    22,    22,    22,    22,
      22,    22,    22,    22,    22,    22,    22,    22,    22,    22,
      22,    22,    22,    22,    22,     3,    88,   118,    80,   165,
     119,   165,   177
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    21,    44,    45,     3,     0,    44,    46,    21,    47,
       4,    21,    48,    49,    50,    51,    55,    77,    80,    84,
      13,     7,     8,     9,    10,    23,    34,    37,    49,    22,
      49,    49,    49,    22,    13,    71,    13,    52,    56,    85,
      35,    36,    78,    21,    81,    29,    71,    82,    83,    22,
      22,    21,    53,    54,    74,    75,    21,    57,    58,    66,
      67,    13,    13,    21,    26,    27,    40,    60,    62,    63,
      64,    79,    38,    39,    22,    13,    21,    71,    13,    70,
      12,    13,    15,    41,    73,    22,    53,    11,    12,    15,
      16,    17,    18,    19,    24,    25,    32,    33,    61,    73,
      22,    86,    28,    29,    30,    31,    64,    79,    22,    26,
      26,    20,    70,    22,    21,    75,    21,    60,    63,    13,
      76,    57,    65,    57,    67,    21,    57,    65,    21,    21,
      59,    60,    62,    13,    14,    68,    69,    13,    87,    62,
      79,    62,    79,    62,    79,    62,    79,    68,    22,    22,
      22,    71,    15,    22,    64,    21,    62,    21,    74,    76,
      22,    65,    22,    22,    22,    14,    72,    57,    22,    72,
      28,    29,    30,    31,    59,    22,    68,    88,    22,    62,
      79,    62,    79,    22,    62,    79,    22,    62,    79,    62,
      79,    62,    79,    62,    79,    62,    79,    22,    28,    29,
      30,    31,    22,    22,    72,    82,    83,    22,    22,    22,
      59,    62,    59,    62,    59,    62,    59,    62,    22,    87,
      22,    22,    22,    22,    22,    22,    22,    22,    22,    22,
      22,    22,    22,    22,    22,    22,    62,    62,    62,    62,
      72,    70,    57,    57,    59,    62,    22,    59,    62,    59,
      62,    59,    62,    22,    22,    22,    22,    22,    22,    22,
      72
};

#define yyerrok		(yyerrstatus = 0)
#define yyclearin	(yychar = YYEMPTY)
#define YYEMPTY		(-2)
#define YYEOF		0

#define YYACCEPT	goto yyacceptlab
#define YYABORT		goto yyabortlab
#define YYERROR		goto yyerrorlab


/* Like YYERROR except do call yyerror.  This remains here temporarily
   to ease the transition to the new meaning of YYERROR, for GCC.
   Once GCC version 2 has supplanted version 1, this can go.  */

#define YYFAIL		goto yyerrlab

#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)					\
do								\
  if (yychar == YYEMPTY && yylen == 1)				\
    {								\
      yychar = (Token);						\
      yylval = (Value);						\
      yytoken = YYTRANSLATE (yychar);				\
      YYPOPSTACK (1);						\
      goto yybackup;						\
    }								\
  else								\
    {								\
      yyerror (YY_("syntax error: cannot back up")); \
      YYERROR;							\
    }								\
while (YYID (0))


#define YYTERROR	1
#define YYERRCODE	256


/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#define YYRHSLOC(Rhs, K) ((Rhs)[K])
#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)				\
    do									\
      if (YYID (N))                                                    \
	{								\
	  (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;	\
	  (Current).first_column = YYRHSLOC (Rhs, 1).first_column;	\
	  (Current).last_line    = YYRHSLOC (Rhs, N).last_line;		\
	  (Current).last_column  = YYRHSLOC (Rhs, N).last_column;	\
	}								\
      else								\
	{								\
	  (Current).first_line   = (Current).last_line   =		\
	    YYRHSLOC (Rhs, 0).last_line;				\
	  (Current).first_column = (Current).last_column =		\
	    YYRHSLOC (Rhs, 0).last_column;				\
	}								\
    while (YYID (0))
#endif


/* YY_LOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

#ifndef YY_LOCATION_PRINT
# if YYLTYPE_IS_TRIVIAL
#  define YY_LOCATION_PRINT(File, Loc)			\
     fprintf (File, "%d.%d-%d.%d",			\
	      (Loc).first_line, (Loc).first_column,	\
	      (Loc).last_line,  (Loc).last_column)
# else
#  define YY_LOCATION_PRINT(File, Loc) ((void) 0)
# endif
#endif


/* YYLEX -- calling `yylex' with the right arguments.  */

#ifdef YYLEX_PARAM
# define YYLEX yylex (YYLEX_PARAM)
#else
# define YYLEX yylex ()
#endif

/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)			\
do {						\
  if (yydebug)					\
    YYFPRINTF Args;				\
} while (YYID (0))

# define YY_SYMBOL_PRINT(Title, Type, Value, Location)			  \
do {									  \
  if (yydebug)								  \
    {									  \
      YYFPRINTF (stderr, "%s ", Title);					  \
      yy_symbol_print (stderr,						  \
		  Type, Value); \
      YYFPRINTF (stderr, "\n");						  \
    }									  \
} while (YYID (0))


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_value_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_value_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (!yyvaluep)
    return;
# ifdef YYPRINT
  if (yytype < YYNTOKENS)
    YYPRINT (yyoutput, yytoknum[yytype], *yyvaluep);
# else
  YYUSE (yyoutput);
# endif
  switch (yytype)
    {
      default:
	break;
    }
}


/*--------------------------------.
| Print this symbol on YYOUTPUT.  |
`--------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_symbol_print (FILE *yyoutput, int yytype, YYSTYPE const * const yyvaluep)
#else
static void
yy_symbol_print (yyoutput, yytype, yyvaluep)
    FILE *yyoutput;
    int yytype;
    YYSTYPE const * const yyvaluep;
#endif
{
  if (yytype < YYNTOKENS)
    YYFPRINTF (yyoutput, "token %s (", yytname[yytype]);
  else
    YYFPRINTF (yyoutput, "nterm %s (", yytname[yytype]);

  yy_symbol_value_print (yyoutput, yytype, yyvaluep);
  YYFPRINTF (yyoutput, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_stack_print (yytype_int16 *yybottom, yytype_int16 *yytop)
#else
static void
yy_stack_print (yybottom, yytop)
    yytype_int16 *yybottom;
    yytype_int16 *yytop;
#endif
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)				\
do {								\
  if (yydebug)							\
    yy_stack_print ((Bottom), (Top));				\
} while (YYID (0))


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yy_reduce_print (YYSTYPE *yyvsp, int yyrule)
#else
static void
yy_reduce_print (yyvsp, yyrule)
    YYSTYPE *yyvsp;
    int yyrule;
#endif
{
  int yynrhs = yyr2[yyrule];
  int yyi;
  unsigned long int yylno = yyrline[yyrule];
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %lu):\n",
	     yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr, yyrhs[yyprhs[yyrule] + yyi],
		       &(yyvsp[(yyi + 1) - (yynrhs)])
		       		       );
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)		\
do {					\
  if (yydebug)				\
    yy_reduce_print (yyvsp, Rule); \
} while (YYID (0))

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args)
# define YY_SYMBOL_PRINT(Title, Type, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef	YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif



#if YYERROR_VERBOSE

# ifndef yystrlen
#  if defined __GLIBC__ && defined _STRING_H
#   define yystrlen strlen
#  else
/* Return the length of YYSTR.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static YYSIZE_T
yystrlen (const char *yystr)
#else
static YYSIZE_T
yystrlen (yystr)
    const char *yystr;
#endif
{
  YYSIZE_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
#  endif
# endif

# ifndef yystpcpy
#  if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#   define yystpcpy stpcpy
#  else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static char *
yystpcpy (char *yydest, const char *yysrc)
#else
static char *
yystpcpy (yydest, yysrc)
    char *yydest;
    const char *yysrc;
#endif
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
#  endif
# endif

# ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYSIZE_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYSIZE_T yyn = 0;
      char const *yyp = yystr;

      for (;;)
	switch (*++yyp)
	  {
	  case '\'':
	  case ',':
	    goto do_not_strip_quotes;

	  case '\\':
	    if (*++yyp != '\\')
	      goto do_not_strip_quotes;
	    /* Fall through.  */
	  default:
	    if (yyres)
	      yyres[yyn] = *yyp;
	    yyn++;
	    break;

	  case '"':
	    if (yyres)
	      yyres[yyn] = '\0';
	    return yyn;
	  }
    do_not_strip_quotes: ;
    }

  if (! yyres)
    return yystrlen (yystr);

  return yystpcpy (yyres, yystr) - yyres;
}
# endif

/* Copy into YYRESULT an error message about the unexpected token
   YYCHAR while in state YYSTATE.  Return the number of bytes copied,
   including the terminating null byte.  If YYRESULT is null, do not
   copy anything; just return the number of bytes that would be
   copied.  As a special case, return 0 if an ordinary "syntax error"
   message will do.  Return YYSIZE_MAXIMUM if overflow occurs during
   size calculation.  */
static YYSIZE_T
yysyntax_error (char *yyresult, int yystate, int yychar)
{
  int yyn = yypact[yystate];

  if (! (YYPACT_NINF < yyn && yyn <= YYLAST))
    return 0;
  else
    {
      int yytype = YYTRANSLATE (yychar);
      YYSIZE_T yysize0 = yytnamerr (0, yytname[yytype]);
      YYSIZE_T yysize = yysize0;
      YYSIZE_T yysize1;
      int yysize_overflow = 0;
      enum { YYERROR_VERBOSE_ARGS_MAXIMUM = 5 };
      char const *yyarg[YYERROR_VERBOSE_ARGS_MAXIMUM];
      int yyx;

# if 0
      /* This is so xgettext sees the translatable formats that are
	 constructed on the fly.  */
      YY_("syntax error, unexpected %s");
      YY_("syntax error, unexpected %s, expecting %s");
      YY_("syntax error, unexpected %s, expecting %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s");
      YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s");
# endif
      char *yyfmt;
      char const *yyf;
      static char const yyunexpected[] = "syntax error, unexpected %s";
      static char const yyexpecting[] = ", expecting %s";
      static char const yyor[] = " or %s";
      char yyformat[sizeof yyunexpected
		    + sizeof yyexpecting - 1
		    + ((YYERROR_VERBOSE_ARGS_MAXIMUM - 2)
		       * (sizeof yyor - 1))];
      char const *yyprefix = yyexpecting;

      /* Start YYX at -YYN if negative to avoid negative indexes in
	 YYCHECK.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;

      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yycount = 1;

      yyarg[0] = yytname[yytype];
      yyfmt = yystpcpy (yyformat, yyunexpected);

      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
	if (yycheck[yyx + yyn] == yyx && yyx != YYTERROR)
	  {
	    if (yycount == YYERROR_VERBOSE_ARGS_MAXIMUM)
	      {
		yycount = 1;
		yysize = yysize0;
		yyformat[sizeof yyunexpected - 1] = '\0';
		break;
	      }
	    yyarg[yycount++] = yytname[yyx];
	    yysize1 = yysize + yytnamerr (0, yytname[yyx]);
	    yysize_overflow |= (yysize1 < yysize);
	    yysize = yysize1;
	    yyfmt = yystpcpy (yyfmt, yyprefix);
	    yyprefix = yyor;
	  }

      yyf = YY_(yyformat);
      yysize1 = yysize + yystrlen (yyf);
      yysize_overflow |= (yysize1 < yysize);
      yysize = yysize1;

      if (yysize_overflow)
	return YYSIZE_MAXIMUM;

      if (yyresult)
	{
	  /* Avoid sprintf, as that infringes on the user's name space.
	     Don't have undefined behavior even if the translation
	     produced a string with the wrong number of "%s"s.  */
	  char *yyp = yyresult;
	  int yyi = 0;
	  while ((*yyp = *yyf) != '\0')
	    {
	      if (*yyp == '%' && yyf[1] == 's' && yyi < yycount)
		{
		  yyp += yytnamerr (yyp, yyarg[yyi++]);
		  yyf += 2;
		}
	      else
		{
		  yyp++;
		  yyf++;
		}
	    }
	}
      return yysize;
    }
}
#endif /* YYERROR_VERBOSE */


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

/*ARGSUSED*/
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
static void
yydestruct (const char *yymsg, int yytype, YYSTYPE *yyvaluep)
#else
static void
yydestruct (yymsg, yytype, yyvaluep)
    const char *yymsg;
    int yytype;
    YYSTYPE *yyvaluep;
#endif
{
  YYUSE (yyvaluep);

  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yytype, yyvaluep, yylocationp);

  switch (yytype)
    {

      default:
	break;
    }
}

/* Prevent warnings from -Wmissing-prototypes.  */
#ifdef YYPARSE_PARAM
#if defined __STDC__ || defined __cplusplus
int yyparse (void *YYPARSE_PARAM);
#else
int yyparse ();
#endif
#else /* ! YYPARSE_PARAM */
#if defined __STDC__ || defined __cplusplus
int yyparse (void);
#else
int yyparse ();
#endif
#endif /* ! YYPARSE_PARAM */


/* The lookahead symbol.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;

/* Number of syntax errors so far.  */
int yynerrs;



/*-------------------------.
| yyparse or yypush_parse.  |
`-------------------------*/

#ifdef YYPARSE_PARAM
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void *YYPARSE_PARAM)
#else
int
yyparse (YYPARSE_PARAM)
    void *YYPARSE_PARAM;
#endif
#else /* ! YYPARSE_PARAM */
#if (defined __STDC__ || defined __C99__FUNC__ \
     || defined __cplusplus || defined _MSC_VER)
int
yyparse (void)
#else
int
yyparse ()

#endif
#endif
{


    int yystate;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus;

    /* The stacks and their tools:
       `yyss': related to states.
       `yyvs': related to semantic values.

       Refer to the stacks thru separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* The state stack.  */
    yytype_int16 yyssa[YYINITDEPTH];
    yytype_int16 *yyss;
    yytype_int16 *yyssp;

    /* The semantic value stack.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs;
    YYSTYPE *yyvsp;

    YYSIZE_T yystacksize;

  int yyn;
  int yyresult;
  /* Lookahead token as an internal (translated) token number.  */
  int yytoken;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;

#if YYERROR_VERBOSE
  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYSIZE_T yymsg_alloc = sizeof yymsgbuf;
#endif

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  yytoken = 0;
  yyss = yyssa;
  yyvs = yyvsa;
  yystacksize = YYINITDEPTH;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yystate = 0;
  yyerrstatus = 0;
  yynerrs = 0;
  yychar = YYEMPTY; /* Cause a token to be read.  */

  /* Initialize stack pointers.
     Waste one element of value and location stack
     so that they stay on the same level as the state stack.
     The wasted elements are never initialized.  */
  yyssp = yyss;
  yyvsp = yyvs;

  goto yysetstate;

/*------------------------------------------------------------.
| yynewstate -- Push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
 yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;

 yysetstate:
  *yyssp = yystate;

  if (yyss + yystacksize - 1 <= yyssp)
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYSIZE_T yysize = yyssp - yyss + 1;

#ifdef yyoverflow
      {
	/* Give user a chance to reallocate the stack.  Use copies of
	   these so that the &'s don't force the real ones into
	   memory.  */
	YYSTYPE *yyvs1 = yyvs;
	yytype_int16 *yyss1 = yyss;

	/* Each stack pointer address is followed by the size of the
	   data in use in that stack, in bytes.  This used to be a
	   conditional around just the two extra args, but that might
	   be undefined if yyoverflow is a macro.  */
	yyoverflow (YY_("memory exhausted"),
		    &yyss1, yysize * sizeof (*yyssp),
		    &yyvs1, yysize * sizeof (*yyvsp),
		    &yystacksize);

	yyss = yyss1;
	yyvs = yyvs1;
      }
#else /* no yyoverflow */
# ifndef YYSTACK_RELOCATE
      goto yyexhaustedlab;
# else
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
	goto yyexhaustedlab;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
	yystacksize = YYMAXDEPTH;

      {
	yytype_int16 *yyss1 = yyss;
	union yyalloc *yyptr =
	  (union yyalloc *) YYSTACK_ALLOC (YYSTACK_BYTES (yystacksize));
	if (! yyptr)
	  goto yyexhaustedlab;
	YYSTACK_RELOCATE (yyss_alloc, yyss);
	YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
	if (yyss1 != yyssa)
	  YYSTACK_FREE (yyss1);
      }
# endif
#endif /* no yyoverflow */

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YYDPRINTF ((stderr, "Stack size increased to %lu\n",
		  (unsigned long int) yystacksize));

      if (yyss + yystacksize - 1 <= yyssp)
	YYABORT;
    }

  YYDPRINTF ((stderr, "Entering state %d\n", yystate));

  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;

/*-----------.
| yybackup.  |
`-----------*/
yybackup:

  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yyn == YYPACT_NINF)
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either YYEMPTY or YYEOF or a valid lookahead symbol.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token: "));
      yychar = YYLEX;
    }

  if (yychar <= YYEOF)
    {
      yychar = yytoken = YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yyn == 0 || yyn == YYTABLE_NINF)
	goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);

  /* Discard the shifted token.  */
  yychar = YYEMPTY;

  yystate = yyn;
  *++yyvsp = yylval;

  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- Do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     `$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
        case 4:

/* Line 1455 of yacc.c  */
#line 268 "scan-fct_pddl.y"
    { 
  fcterr( PROBNAME_EXPECTED, NULL ); 
;}
    break;

  case 5:

/* Line 1455 of yacc.c  */
#line 272 "scan-fct_pddl.y"
    {  
  gproblem_name = (yyvsp[(4) - (6)].pstring);
  if ( gcmd_line.display_info >= 1 ) {
    printf(" problem '%s' defined", gproblem_name);
  }
;}
    break;

  case 6:

/* Line 1455 of yacc.c  */
#line 284 "scan-fct_pddl.y"
    { 
  (yyval.pstring) = new_Token( strlen((yyvsp[(3) - (4)].string))+1 );
  strcpy((yyval.pstring), (yyvsp[(3) - (4)].string));
;}
    break;

  case 7:

/* Line 1455 of yacc.c  */
#line 294 "scan-fct_pddl.y"
    { 
  if ( SAME != strcmp((yyvsp[(3) - (4)].string), gdomain_name) ) {
    fcterr( BADDOMAIN, NULL );
    yyerror(NULL);
  }
;}
    break;

  case 16:

/* Line 1455 of yacc.c  */
#line 327 "scan-fct_pddl.y"
    { 
  gparse_objects = (yyvsp[(3) - (4)].pTypedList);
;}
    break;

  case 17:

/* Line 1455 of yacc.c  */
#line 352 "scan-fct_pddl.y"
    {
  fcterr( INIFACTS, NULL ); 
;}
    break;

  case 18:

/* Line 1455 of yacc.c  */
#line 356 "scan-fct_pddl.y"
    {
  gorig_initial_facts = new_PlNode(AND);
  gorig_initial_facts->sons = (yyvsp[(4) - (5)].pPlNode); /*4 perche' una mid rule action conta 1*/
;}
    break;

  case 19:

/* Line 1455 of yacc.c  */
#line 365 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=(yyvsp[(1) - (1)].pPlNode);
;}
    break;

  case 20:

/* Line 1455 of yacc.c  */
#line 372 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=(yyvsp[(1) - (2)].pPlNode);
  (yyval.pPlNode)->next = (yyvsp[(2) - (2)].pPlNode);
;}
    break;

  case 22:

/* Line 1455 of yacc.c  */
#line 383 "scan-fct_pddl.y"
    {
  /* gestisce i timed initial facts */
  PlNode *pln;
  (yyval.pPlNode)=new_PlNode(TIMED_FACT);
  (yyval.pPlNode)->sons=(yyvsp[(4) - (5)].pPlNode);
  pln = new_PlNode(ATOM);
  pln->atom=(yyvsp[(3) - (5)].pTokenList);
  (yyval.pPlNode)->sons->next=pln; 
  gnum_tmd_init_fcts++;
;}
    break;

  case 23:

/* Line 1455 of yacc.c  */
#line 395 "scan-fct_pddl.y"
    {
  PlNode* pln;
  (yyval.pPlNode)=new_PlNode(EQUAL_CONN);
  pln = new_PlNode(FN_HEAD);
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->atom = (yyvsp[(3) - (5)].pTokenList);
  (yyval.pPlNode)->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 24:

/* Line 1455 of yacc.c  */
#line 409 "scan-fct_pddl.y"
    { 
  fcterr( GOALDEF, NULL ); 
;}
    break;

  case 25:

/* Line 1455 of yacc.c  */
#line 413 "scan-fct_pddl.y"
    {
  (yyvsp[(4) - (5)].pPlNode)->next = gorig_goal_facts;
  gorig_goal_facts = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 26:

/* Line 1455 of yacc.c  */
#line 427 "scan-fct_pddl.y"
    { 
  if ( sis_negated ) {
    (yyval.pPlNode) = new_PlNode(NOT);
    (yyval.pPlNode)->sons = new_PlNode(ATOM);
    (yyval.pPlNode)->sons->atom = (yyvsp[(1) - (1)].pTokenList);
    sis_negated = FALSE;
  } else {
    (yyval.pPlNode) = new_PlNode(ATOM);
    (yyval.pPlNode)->atom = (yyvsp[(1) - (1)].pTokenList);
  }
;}
    break;

  case 27:

/* Line 1455 of yacc.c  */
#line 440 "scan-fct_pddl.y"
    { 
  (yyval.pPlNode) = new_PlNode(AND);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (4)].pPlNode);
;}
    break;

  case 28:

/* Line 1455 of yacc.c  */
#line 446 "scan-fct_pddl.y"
    { 
  (yyval.pPlNode) = new_PlNode(OR);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (4)].pPlNode);
;}
    break;

  case 29:

/* Line 1455 of yacc.c  */
#line 452 "scan-fct_pddl.y"
    { 
  (yyval.pPlNode) = new_PlNode(NOT);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (4)].pPlNode);
;}
    break;

  case 30:

/* Line 1455 of yacc.c  */
#line 458 "scan-fct_pddl.y"
    { 
  PlNode *np = new_PlNode(NOT);
  np->sons = (yyvsp[(3) - (5)].pPlNode);
  np->next = (yyvsp[(4) - (5)].pPlNode);

  (yyval.pPlNode) = new_PlNode(OR);
  (yyval.pPlNode)->sons = np;
;}
    break;

  case 31:

/* Line 1455 of yacc.c  */
#line 470 "scan-fct_pddl.y"
    { 

  PlNode *pln;

  pln = new_PlNode(EX);
  pln->parse_vars = (yyvsp[(4) - (7)].pTypedList);

  (yyval.pPlNode) = pln;
  pln->sons = (yyvsp[(6) - (7)].pPlNode);

;}
    break;

  case 32:

/* Line 1455 of yacc.c  */
#line 485 "scan-fct_pddl.y"
    { 

  PlNode *pln;

  pln = new_PlNode(ALL);
  pln->parse_vars = (yyvsp[(4) - (7)].pTypedList);

  (yyval.pPlNode) = pln;
  pln->sons = (yyvsp[(6) - (7)].pPlNode);

;}
    break;

  case 34:

/* Line 1455 of yacc.c  */
#line 511 "scan-fct_pddl.y"
    { 
//AGGIUNTALAZZA
  //    printf("\n\nNumeric goal still not allowed in the goal definition\n\n");
    // exit(1);
//FINEAGGIUNTALAZZA
  (yyval.pPlNode) = new_PlNode(BIN_COMP);
  (yyval.pPlNode)->sons = (yyvsp[(2) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons= (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next= (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 35:

/* Line 1455 of yacc.c  */
#line 526 "scan-fct_pddl.y"
    {
       (yyval.pPlNode)=new_PlNode(NUM_EXP);
       (yyval.pPlNode)->sons = (yyvsp[(1) - (1)].pPlNode);
;}
    break;

  case 36:

/* Line 1455 of yacc.c  */
#line 532 "scan-fct_pddl.y"
    { 
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(UMINUS_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (4)].pPlNode);
;}
    break;

  case 37:

/* Line 1455 of yacc.c  */
#line 542 "scan-fct_pddl.y"
    { 
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(MINUS_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);

;}
    break;

  case 38:

/* Line 1455 of yacc.c  */
#line 554 "scan-fct_pddl.y"
    { 
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(PLUS_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);


;}
    break;

  case 39:

/* Line 1455 of yacc.c  */
#line 567 "scan-fct_pddl.y"
    { 
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(MUL_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);

;}
    break;

  case 40:

/* Line 1455 of yacc.c  */
#line 579 "scan-fct_pddl.y"
    { 
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(DIV_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);

;}
    break;

  case 41:

/* Line 1455 of yacc.c  */
#line 591 "scan-fct_pddl.y"
    {
  (yyval.pPlNode) = new_PlNode(FN_HEAD);
  (yyval.pPlNode)->atom = (yyvsp[(1) - (1)].pTokenList);
;}
    break;

  case 42:

/* Line 1455 of yacc.c  */
#line 599 "scan-fct_pddl.y"
    { 
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = (yyvsp[(2) - (4)].pstring);
  (yyval.pTokenList)->next = (yyvsp[(3) - (4)].pTokenList);
;}
    break;

  case 43:

/* Line 1455 of yacc.c  */
#line 606 "scan-fct_pddl.y"
    { 
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = (yyvsp[(1) - (1)].pstring);
;}
    break;

  case 44:

/* Line 1455 of yacc.c  */
#line 628 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=new_PlNode(GREATER_THAN_CONN);
;}
    break;

  case 45:

/* Line 1455 of yacc.c  */
#line 633 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=new_PlNode(LESS_THAN_CONN);
;}
    break;

  case 46:

/* Line 1455 of yacc.c  */
#line 638 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=new_PlNode(EQUAL_CONN);
;}
    break;

  case 47:

/* Line 1455 of yacc.c  */
#line 643 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=new_PlNode(GREATER_OR_EQUAL_CONN);
;}
    break;

  case 48:

/* Line 1455 of yacc.c  */
#line 648 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=new_PlNode(LESS_THAN_OR_EQUAL_CONN);
;}
    break;

  case 49:

/* Line 1455 of yacc.c  */
#line 656 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=new_PlNode(UMINUS_CONN);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (4)].pPlNode);
   
;}
    break;

  case 50:

/* Line 1455 of yacc.c  */
#line 663 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=new_PlNode(MINUS_CONN);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 51:

/* Line 1455 of yacc.c  */
#line 670 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=new_PlNode(PLUS_CONN);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 52:

/* Line 1455 of yacc.c  */
#line 677 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=new_PlNode(MUL_CONN);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 53:

/* Line 1455 of yacc.c  */
#line 684 "scan-fct_pddl.y"
    {
  (yyval.pPlNode)=new_PlNode(DIV_CONN);
  (yyval.pPlNode)->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 54:

/* Line 1455 of yacc.c  */
#line 691 "scan-fct_pddl.y"
    {
    (yyval.pPlNode)=new_PlNode(ATOM);
    (yyval.pPlNode)->atom = (yyvsp[(1) - (1)].pTokenList);
;}
    break;

  case 55:

/* Line 1455 of yacc.c  */
#line 699 "scan-fct_pddl.y"
    {
  Token t;
  t = new_Token( strlen((yyvsp[(1) - (1)].string))+1 );
  strcpy (t, (yyvsp[(1) - (1)].string));
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = t;

;}
    break;

  case 56:

/* Line 1455 of yacc.c  */
#line 709 "scan-fct_pddl.y"
    {
  Token t;
  t = new_Token( strlen((yyvsp[(1) - (1)].string))+1 );
  strcpy (t, (yyvsp[(1) - (1)].string));
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = t;

;}
    break;

  case 57:

/* Line 1455 of yacc.c  */
#line 721 "scan-fct_pddl.y"
    { 
  (yyval.pstring) = new_Token( strlen((yyvsp[(1) - (1)].string))+1 );
  strcpy( (yyval.pstring), (yyvsp[(1) - (1)].string) );
;}
    break;

  case 58:

/* Line 1455 of yacc.c  */
#line 765 "scan-fct_pddl.y"
    {
  (yyval.pPlNode) = NULL;
;}
    break;

  case 59:

/* Line 1455 of yacc.c  */
#line 770 "scan-fct_pddl.y"
    {
  (yyvsp[(1) - (2)].pPlNode)->next = (yyvsp[(2) - (2)].pPlNode);
  (yyval.pPlNode) = (yyvsp[(1) - (2)].pPlNode);
;}
    break;

  case 60:

/* Line 1455 of yacc.c  */
#line 783 "scan-fct_pddl.y"
    { 
  (yyval.pTokenList) = (yyvsp[(3) - (4)].pTokenList);
  sis_negated = TRUE;
;}
    break;

  case 61:

/* Line 1455 of yacc.c  */
#line 789 "scan-fct_pddl.y"
    {
  (yyval.pTokenList) = (yyvsp[(1) - (1)].pTokenList);
;}
    break;

  case 62:

/* Line 1455 of yacc.c  */
#line 798 "scan-fct_pddl.y"
    { 
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = (yyvsp[(2) - (4)].pstring);
  (yyval.pTokenList)->next = (yyvsp[(3) - (4)].pTokenList);
;}
    break;

  case 63:

/* Line 1455 of yacc.c  */
#line 809 "scan-fct_pddl.y"
    {
  (yyval.pTokenList) = NULL;
;}
    break;

  case 64:

/* Line 1455 of yacc.c  */
#line 814 "scan-fct_pddl.y"
    {
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = (yyvsp[(1) - (2)].pstring);
  (yyval.pTokenList)->next = (yyvsp[(2) - (2)].pTokenList);
;}
    break;

  case 65:

/* Line 1455 of yacc.c  */
#line 825 "scan-fct_pddl.y"
    { 
  (yyval.pstring) = new_Token(strlen((yyvsp[(1) - (1)].string)) + 1);
  strcpy((yyval.pstring), (yyvsp[(1) - (1)].string));
;}
    break;

  case 66:

/* Line 1455 of yacc.c  */
#line 831 "scan-fct_pddl.y"
    { 
  (yyval.pstring) = new_Token(strlen((yyvsp[(1) - (1)].string)) + 1);
  strcpy((yyval.pstring), (yyvsp[(1) - (1)].string));
;}
    break;

  case 67:

/* Line 1455 of yacc.c  */
#line 841 "scan-fct_pddl.y"
    {
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = new_Token(strlen((yyvsp[(1) - (1)].string)) + 1);
  strcpy((yyval.pTokenList)->item, (yyvsp[(1) - (1)].string));
;}
    break;

  case 68:

/* Line 1455 of yacc.c  */
#line 848 "scan-fct_pddl.y"
    {
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = new_Token(strlen((yyvsp[(1) - (2)].string)) + 1);
  strcpy((yyval.pTokenList)->item, (yyvsp[(1) - (2)].string));
  (yyval.pTokenList)->next = (yyvsp[(2) - (2)].pTokenList);
;}
    break;

  case 69:

/* Line 1455 of yacc.c  */
#line 859 "scan-fct_pddl.y"
    { (yyval.pTypedList) = NULL; ;}
    break;

  case 70:

/* Line 1455 of yacc.c  */
#line 862 "scan-fct_pddl.y"
    { 
  (yyval.pTypedList) = new_TypedList();
  (yyval.pTypedList)->name = new_Token( strlen((yyvsp[(1) - (5)].string))+1 );
  strcpy( (yyval.pTypedList)->name, (yyvsp[(1) - (5)].string) );
  (yyval.pTypedList)->type = (yyvsp[(3) - (5)].pTokenList);
  (yyval.pTypedList)->next = (yyvsp[(5) - (5)].pTypedList);
;}
    break;

  case 71:

/* Line 1455 of yacc.c  */
#line 871 "scan-fct_pddl.y"
    {
  (yyval.pTypedList) = new_TypedList();
  (yyval.pTypedList)->name = new_Token( strlen((yyvsp[(1) - (3)].string))+1 );
  strcpy( (yyval.pTypedList)->name, (yyvsp[(1) - (3)].string) );
  (yyval.pTypedList)->type = new_TokenList();
  (yyval.pTypedList)->type->item = new_Token( strlen((yyvsp[(2) - (3)].pstring))+1 );
  strcpy( (yyval.pTypedList)->type->item, (yyvsp[(2) - (3)].pstring) );
  (yyval.pTypedList)->next = (yyvsp[(3) - (3)].pTypedList);
;}
    break;

  case 72:

/* Line 1455 of yacc.c  */
#line 882 "scan-fct_pddl.y"
    {
  (yyval.pTypedList) = new_TypedList();
  (yyval.pTypedList)->name = new_Token( strlen((yyvsp[(1) - (2)].string))+1 );
  strcpy( (yyval.pTypedList)->name, (yyvsp[(1) - (2)].string) );
  if ( (yyvsp[(2) - (2)].pTypedList) ) {/* another element (already typed) is following */
    (yyval.pTypedList)->type = copy_TokenList( (yyvsp[(2) - (2)].pTypedList)->type );
  } else {/* no further element - it must be an untyped list */
    (yyval.pTypedList)->type = new_TokenList();
    (yyval.pTypedList)->type->item = new_Token( strlen(STANDARD_TYPE)+1 );
    strcpy( (yyval.pTypedList)->type->item, STANDARD_TYPE );
  }
  (yyval.pTypedList)->next = (yyvsp[(2) - (2)].pTypedList);
;}
    break;

  case 73:

/* Line 1455 of yacc.c  */
#line 901 "scan-fct_pddl.y"
    { (yyval.pTypedList) = NULL; ;}
    break;

  case 74:

/* Line 1455 of yacc.c  */
#line 904 "scan-fct_pddl.y"
    { 
  (yyval.pTypedList) = new_TypedList();
  (yyval.pTypedList)->name = new_Token( strlen((yyvsp[(1) - (5)].string))+1 );
  strcpy( (yyval.pTypedList)->name, (yyvsp[(1) - (5)].string) );
  (yyval.pTypedList)->type = (yyvsp[(3) - (5)].pTokenList);
  (yyval.pTypedList)->next = (yyvsp[(5) - (5)].pTypedList);
;}
    break;

  case 75:

/* Line 1455 of yacc.c  */
#line 913 "scan-fct_pddl.y"
    {
  (yyval.pTypedList) = new_TypedList();
  (yyval.pTypedList)->name = new_Token( strlen((yyvsp[(1) - (3)].string))+1 );
  strcpy( (yyval.pTypedList)->name, (yyvsp[(1) - (3)].string) );
  (yyval.pTypedList)->type = new_TokenList();
  (yyval.pTypedList)->type->item = new_Token( strlen((yyvsp[(2) - (3)].pstring))+1 );
  strcpy( (yyval.pTypedList)->type->item, (yyvsp[(2) - (3)].pstring) );
  (yyval.pTypedList)->next = (yyvsp[(3) - (3)].pTypedList);
;}
    break;

  case 76:

/* Line 1455 of yacc.c  */
#line 924 "scan-fct_pddl.y"
    {
  (yyval.pTypedList) = new_TypedList();
  (yyval.pTypedList)->name = new_Token( strlen((yyvsp[(1) - (2)].string))+1 );
  strcpy( (yyval.pTypedList)->name, (yyvsp[(1) - (2)].string) );
  if ( (yyvsp[(2) - (2)].pTypedList) ) {/* another element (already typed) is following */
    (yyval.pTypedList)->type = copy_TokenList( (yyvsp[(2) - (2)].pTypedList)->type );
  } else {/* no further element - it must be an untyped list */
    (yyval.pTypedList)->type = new_TokenList();
    (yyval.pTypedList)->type->item = new_Token( strlen(STANDARD_TYPE)+1 );
    strcpy( (yyval.pTypedList)->type->item, STANDARD_TYPE );
  }
  (yyval.pTypedList)->next = (yyvsp[(2) - (2)].pTypedList);
;}
    break;

  case 77:

/* Line 1455 of yacc.c  */
#line 945 "scan-fct_pddl.y"
    { 
  (yyval.pstring) = new_Token(strlen((yyvsp[(1) - (1)].string)) + 1);
  strcpy((yyval.pstring), (yyvsp[(1) - (1)].string));
;}
    break;

  case 78:

/* Line 1455 of yacc.c  */
#line 951 "scan-fct_pddl.y"
    { 
  (yyval.pstring) = new_Token( strlen(EQ_STR)+1 );
  strcpy( (yyval.pstring), EQ_STR );
;}
    break;

  case 79:

/* Line 1455 of yacc.c  */
#line 961 "scan-fct_pddl.y"
    { 
  PlNode *tmp;

  tmp = new_PlNode(ATOM);
  tmp->atom = (yyvsp[(3) - (4)].pTokenList);
  (yyval.pPlNode) = new_PlNode(NOT);
  (yyval.pPlNode)->sons = tmp;
;}
    break;

  case 80:

/* Line 1455 of yacc.c  */
#line 971 "scan-fct_pddl.y"
    {
  (yyval.pPlNode) = new_PlNode(ATOM);
  (yyval.pPlNode)->atom = (yyvsp[(1) - (1)].pTokenList);
;}
    break;

  case 81:

/* Line 1455 of yacc.c  */
#line 981 "scan-fct_pddl.y"
    { 
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = (yyvsp[(2) - (4)].pstring);
  (yyval.pTokenList)->next = (yyvsp[(3) - (4)].pTokenList);
;}
    break;

  case 82:

/* Line 1455 of yacc.c  */
#line 992 "scan-fct_pddl.y"
    { (yyval.pTokenList) = NULL; ;}
    break;

  case 83:

/* Line 1455 of yacc.c  */
#line 995 "scan-fct_pddl.y"
    {
  (yyval.pTokenList) = new_TokenList();
  (yyval.pTokenList)->item = new_Token(strlen((yyvsp[(1) - (2)].string)) + 1);
  strcpy((yyval.pTokenList)->item, (yyvsp[(1) - (2)].string));
  (yyval.pTokenList)->next = (yyvsp[(2) - (2)].pTokenList);
;}
    break;

  case 84:

/* Line 1455 of yacc.c  */
#line 1007 "scan-fct_pddl.y"
    {
  gmetric_exp = new_PlNode (METRIC_CONN);
  gmetric_exp->sons = (yyvsp[(3) - (5)].pPlNode);
  gmetric_exp->sons->sons = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 85:

/* Line 1455 of yacc.c  */
#line 1016 "scan-fct_pddl.y"
    {
  (yyval.pPlNode) = new_PlNode ( MINIMIZE_CONN);
;}
    break;

  case 86:

/* Line 1455 of yacc.c  */
#line 1021 "scan-fct_pddl.y"
    {
  (yyval.pPlNode) = new_PlNode ( MAXIMIZE_CONN);
;}
    break;

  case 87:

/* Line 1455 of yacc.c  */
#line 1028 "scan-fct_pddl.y"
    { 
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(UMINUS_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (4)].pPlNode);
;}
    break;

  case 88:

/* Line 1455 of yacc.c  */
#line 1038 "scan-fct_pddl.y"
    { 
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(MINUS_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);

;}
    break;

  case 89:

/* Line 1455 of yacc.c  */
#line 1050 "scan-fct_pddl.y"
    { 
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(PLUS_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);


;}
    break;

  case 90:

/* Line 1455 of yacc.c  */
#line 1063 "scan-fct_pddl.y"
    { 
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(MUL_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);

;}
    break;

  case 91:

/* Line 1455 of yacc.c  */
#line 1075 "scan-fct_pddl.y"
    { 
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(DIV_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);

;}
    break;

  case 92:

/* Line 1455 of yacc.c  */
#line 1087 "scan-fct_pddl.y"
    {
       (yyval.pPlNode)=new_PlNode(NUM_EXP);
       (yyval.pPlNode)->sons = (yyvsp[(1) - (1)].pPlNode);
;}
    break;

  case 93:

/* Line 1455 of yacc.c  */
#line 1093 "scan-fct_pddl.y"
    {
  (yyval.pPlNode) = new_PlNode(FN_HEAD);
  (yyval.pPlNode)->atom = (yyvsp[(1) - (1)].pTokenList);
;}
    break;

  case 94:

/* Line 1455 of yacc.c  */
#line 1099 "scan-fct_pddl.y"
    {
  (yyval.pPlNode) = new_PlNode(TOTAL_TIME_CONN);
;}
    break;

  case 95:

/* Line 1455 of yacc.c  */
#line 1104 "scan-fct_pddl.y"
    {
  (yyval.pPlNode) = (yyvsp[(2) - (3)].pPlNode);
;}
    break;

  case 96:

/* Line 1455 of yacc.c  */
#line 1110 "scan-fct_pddl.y"
    {
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(MINUS_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 97:

/* Line 1455 of yacc.c  */
#line 1121 "scan-fct_pddl.y"
    {
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(MINUS_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 98:

/* Line 1455 of yacc.c  */
#line 1132 "scan-fct_pddl.y"
    {
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(PLUS_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 99:

/* Line 1455 of yacc.c  */
#line 1143 "scan-fct_pddl.y"
    {
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(PLUS_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 100:

/* Line 1455 of yacc.c  */
#line 1154 "scan-fct_pddl.y"
    {
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(DIV_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 101:

/* Line 1455 of yacc.c  */
#line 1165 "scan-fct_pddl.y"
    {
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(DIV_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 102:

/* Line 1455 of yacc.c  */
#line 1176 "scan-fct_pddl.y"
    {
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(MUL_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 103:

/* Line 1455 of yacc.c  */
#line 1187 "scan-fct_pddl.y"
    {
  PlNode *pln;

  (yyval.pPlNode)=new_PlNode(F_EXP);
  pln=new_PlNode(MUL_CONN); 
  (yyval.pPlNode)->sons = pln;
  (yyval.pPlNode)->sons->sons = (yyvsp[(3) - (5)].pPlNode);
  (yyval.pPlNode)->sons->sons->next = (yyvsp[(4) - (5)].pPlNode);
;}
    break;

  case 108:

/* Line 1455 of yacc.c  */
#line 1212 "scan-fct_pddl.y"
    {
  (yyval.pstring) = new_Token(strlen((yyvsp[(2) - (2)].string)) + 1);
  strcpy((yyval.pstring), (yyvsp[(2) - (2)].string));
;}
    break;

  case 110:

/* Line 1455 of yacc.c  */
#line 1225 "scan-fct_pddl.y"
    { 
  opserr( REQUIREM_EXPECTED, NULL ); 
;}
    break;

  case 111:

/* Line 1455 of yacc.c  */
#line 1229 "scan-fct_pddl.y"
    { 
  if ( !supported( (yyvsp[(4) - (4)].string) ) ) {
    opserr( NOT_SUPPORTED, (yyvsp[(4) - (4)].string) );
    yyerror(NULL);
  }
;}
    break;

  case 114:

/* Line 1455 of yacc.c  */
#line 1244 "scan-fct_pddl.y"
    { 
  if ( !supported( (yyvsp[(1) - (1)].string) ) ) {
    opserr( NOT_SUPPORTED, (yyvsp[(1) - (1)].string) );
    yyerror(NULL);
  }
;}
    break;



/* Line 1455 of yacc.c  */
#line 2852 "scan-fct_pddl.tab.c"
      default: break;
    }
  YY_SYMBOL_PRINT ("-> $$ =", yyr1[yyn], &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);

  *++yyvsp = yyval;

  /* Now `shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */

  yyn = yyr1[yyn];

  yystate = yypgoto[yyn - YYNTOKENS] + *yyssp;
  if (0 <= yystate && yystate <= YYLAST && yycheck[yystate] == *yyssp)
    yystate = yytable[yystate];
  else
    yystate = yydefgoto[yyn - YYNTOKENS];

  goto yynewstate;


/*------------------------------------.
| yyerrlab -- here on detecting error |
`------------------------------------*/
yyerrlab:
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
#if ! YYERROR_VERBOSE
      yyerror (YY_("syntax error"));
#else
      {
	YYSIZE_T yysize = yysyntax_error (0, yystate, yychar);
	if (yymsg_alloc < yysize && yymsg_alloc < YYSTACK_ALLOC_MAXIMUM)
	  {
	    YYSIZE_T yyalloc = 2 * yysize;
	    if (! (yysize <= yyalloc && yyalloc <= YYSTACK_ALLOC_MAXIMUM))
	      yyalloc = YYSTACK_ALLOC_MAXIMUM;
	    if (yymsg != yymsgbuf)
	      YYSTACK_FREE (yymsg);
	    yymsg = (char *) YYSTACK_ALLOC (yyalloc);
	    if (yymsg)
	      yymsg_alloc = yyalloc;
	    else
	      {
		yymsg = yymsgbuf;
		yymsg_alloc = sizeof yymsgbuf;
	      }
	  }

	if (0 < yysize && yysize <= yymsg_alloc)
	  {
	    (void) yysyntax_error (yymsg, yystate, yychar);
	    yyerror (yymsg);
	  }
	else
	  {
	    yyerror (YY_("syntax error"));
	    if (yysize != 0)
	      goto yyexhaustedlab;
	  }
      }
#endif
    }



  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
	 error, discard it.  */

      if (yychar <= YYEOF)
	{
	  /* Return failure if at end of input.  */
	  if (yychar == YYEOF)
	    YYABORT;
	}
      else
	{
	  yydestruct ("Error: discarding",
		      yytoken, &yylval);
	  yychar = YYEMPTY;
	}
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:

  /* Pacify compilers like GCC when the user code never invokes
     YYERROR and the label yyerrorlab therefore never appears in user
     code.  */
  if (/*CONSTCOND*/ 0)
     goto yyerrorlab;

  /* Do not reclaim the symbols of the rule which action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;	/* Each real token shifted decrements this.  */

  for (;;)
    {
      yyn = yypact[yystate];
      if (yyn != YYPACT_NINF)
	{
	  yyn += YYTERROR;
	  if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYTERROR)
	    {
	      yyn = yytable[yyn];
	      if (0 < yyn)
		break;
	    }
	}

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
	YYABORT;


      yydestruct ("Error: popping",
		  yystos[yystate], yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  *++yyvsp = yylval;


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", yystos[yyn], yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturn;

/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturn;

#if !defined(yyoverflow) || YYERROR_VERBOSE
/*-------------------------------------------------.
| yyexhaustedlab -- memory exhaustion comes here.  |
`-------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  /* Fall through.  */
#endif

yyreturn:
  if (yychar != YYEMPTY)
     yydestruct ("Cleanup: discarding lookahead",
		 yytoken, &yylval);
  /* Do not reclaim the symbols of the rule which action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
		  yystos[*yyssp], yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
#if YYERROR_VERBOSE
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
#endif
  /* Make sure YYID is used.  */
  return YYID (yyresult);
}



/* Line 1675 of yacc.c  */
#line 1255 "scan-fct_pddl.y"



#include "lex.fct_pddl.c"


/**********************************************************************
 * Functions
 **********************************************************************/



int fct_pddlerror(char *msg)

{

  if (msg)
    printf("\n%s", msg);

  fprintf(stderr,"\n%s: syntax error in line %d, '%s':\n", 
	  gact_filename, lineno, yytext );
  
  if ( sact_err_par ) {
    fprintf(stderr, "%s%s\n", serrmsg[sact_err], sact_err_par );
  } else {
    fprintf(stderr,"%s\n", serrmsg[sact_err] );
  }
  fflush( stdout );
  
  exit( 1 );

}



void load_fct_file( char *filename ) 

{

  FILE *fp;/* pointer to input files */
  char tmp[MAX_LENGTH] = "";

  /* open fact file 
   */
  if( ( fp = fopen( filename, "r" ) ) == NULL ) {
    sprintf(tmp, "\n Can't find fact file: %s\n\n", filename );
    perror(tmp);
    exit ( 1 );
  }

  gact_filename = filename;
  lineno = 1; 
  yyin = fp;

  yyparse();

  fclose( fp );/* and close file again */

}

#ifdef YYDEBUG
void yyprint (thisfile, mytype, value)
     FILE *thisfile;
     int mytype;
     YYSTYPE value;
{
  fprintf (thisfile, " %s", value.string);
  /*
    if (type == VAR)
    fprintf (file, " %s", value.tptr->name);
    else if (type == NUM)
    fprintf (file, " %d", value.val);
  */
}
#endif

