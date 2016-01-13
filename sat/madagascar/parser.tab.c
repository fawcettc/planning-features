
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



/* Copy the first part of user declarations.  */

/* Line 189 of yacc.c  */
#line 4 "parser.y"


#include "stdio.h"
#include "main.h"
#include "asyntax.h"

#define YYERROR_VERBOSE

void rparen(char *);

int COST;



/* Line 189 of yacc.c  */
#line 88 "parser.tab.c"

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
     rwMINIMIZE = 258,
     rwMETRIC = 259,
     rwINCREASE = 260,
     rwEITHER = 261,
     rwCONSTANTS = 262,
     rwLENGTH = 263,
     rwEXISTS = 264,
     EQUA = 265,
     rwPROBLEM = 266,
     rwFORALL = 267,
     rwIMPLY = 268,
     rwNOT = 269,
     rwWHEN = 270,
     rwOR = 271,
     rwAND = 272,
     rwTYPING = 273,
     rwDOMAIN = 274,
     rwGOAL = 275,
     rwINIT = 276,
     rwOBJECTS = 277,
     rwTYPES = 278,
     rwREQUIREMENTS = 279,
     rwPREDICATES = 280,
     rwPRECOND = 281,
     rwEFFECT = 282,
     rwPARAMS = 283,
     rwACTION = 284,
     rwDEFINE = 285,
     DASH = 286,
     LPAREN = 287,
     RPAREN = 288,
     INT = 289,
     VAR = 290,
     ID = 291,
     rwFUNCTIONS = 292
   };
#endif



#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef union YYSTYPE
{

/* Line 214 of yacc.c  */
#line 20 "parser.y"

  int i;
  intlist *intlistp;
  atomlist *atomlistp;
  atom *atomp;
  Sfma *Sfmap;
  Sfmalist *Sfmalistp;
  Seff *Seffp;
  Sefflist *Sefflistp;
  typedvarlist *typedvarlistp;



/* Line 214 of yacc.c  */
#line 175 "parser.tab.c"
} YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define yystype YYSTYPE /* obsolescent; will be withdrawn */
# define YYSTYPE_IS_DECLARED 1
#endif


/* Copy the second part of user declarations.  */


/* Line 264 of yacc.c  */
#line 187 "parser.tab.c"

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
#define YYLAST   175

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  38
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  64
/* YYNRULES -- Number of rules.  */
#define YYNRULES  112
/* YYNRULES -- Number of states.  */
#define YYNSTATES  221

/* YYTRANSLATE(YYLEX) -- Bison symbol number corresponding to YYLEX.  */
#define YYUNDEFTOK  2
#define YYMAXUTOK   292

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
      35,    36,    37
};

#if YYDEBUG
/* YYPRHS[YYN] -- Index of the first RHS symbol of rule number YYN in
   YYRHS.  */
static const yytype_uint16 yyprhs[] =
{
       0,     0,     3,     6,     9,    10,    16,    17,    23,    26,
      29,    30,    32,    34,    37,    38,    39,    40,    51,    54,
      55,    56,    62,    63,    69,    70,    76,    77,    83,    84,
      90,    91,    92,   100,   103,   105,   106,   112,   115,   118,
     120,   122,   123,   126,   128,   131,   133,   137,   138,   139,
     150,   151,   157,   158,   163,   166,   169,   172,   175,   179,
     184,   186,   191,   192,   202,   205,   206,   207,   214,   215,
     218,   219,   223,   225,   226,   232,   233,   238,   239,   245,
     246,   253,   254,   260,   261,   268,   269,   275,   277,   278,
     285,   286,   295,   296,   305,   308,   310,   313,   315,   317,
     319,   320,   325,   326,   332,   333,   340,   341,   350,   352,
     353,   359,   360
};

/* YYRHS -- A `-1'-separated list of the rules' RHS.  */
static const yytype_int8 yyrhs[] =
{
      39,     0,    -1,    47,    66,    -1,    36,    40,    -1,    -1,
      32,    10,    94,    94,    33,    -1,    -1,    32,    36,    46,
      43,    33,    -1,    44,    42,    -1,    44,    41,    -1,    -1,
      35,    -1,    36,    -1,    45,    46,    -1,    -1,    -1,    -1,
      32,    30,    32,    19,    36,    48,    33,    50,    49,    33,
      -1,    50,    51,    -1,    -1,    -1,    32,    25,    76,    52,
      33,    -1,    -1,    32,    24,    40,    53,    33,    -1,    -1,
      32,     7,    73,    54,    33,    -1,    -1,    32,    37,    78,
      55,    33,    -1,    -1,    32,    23,    73,    56,    33,    -1,
      -1,    -1,    32,    29,    57,    36,    59,    58,    33,    -1,
      60,    59,    -1,    60,    -1,    -1,    28,    32,    62,    61,
      33,    -1,    26,    82,    -1,    27,    95,    -1,    63,    -1,
      64,    -1,    -1,    35,    63,    -1,    35,    -1,    65,    64,
      -1,    65,    -1,    63,    31,    36,    -1,    -1,    -1,    32,
      30,    32,    11,    36,    67,    33,    69,    68,    33,    -1,
      -1,    69,    32,    72,    70,    33,    -1,    -1,    32,    72,
      71,    33,    -1,    19,    36,    -1,    22,    73,    -1,    21,
      44,    -1,    20,    82,    -1,     4,     3,    44,    -1,    40,
      31,    36,    73,    -1,    40,    -1,    35,    31,    36,    74,
      -1,    -1,    35,    31,    32,     6,    36,    40,    75,    33,
      74,    -1,    35,    74,    -1,    -1,    -1,    76,    32,    36,
      74,    77,    33,    -1,    -1,    79,    78,    -1,    -1,    80,
      31,    36,    -1,    80,    -1,    -1,    32,    36,    74,    81,
      33,    -1,    -1,    32,    17,    83,    33,    -1,    -1,    32,
      17,    92,    84,    33,    -1,    -1,    32,    15,    82,    82,
      85,    33,    -1,    -1,    32,    16,    92,    86,    33,    -1,
      -1,    32,    13,    82,    82,    87,    33,    -1,    -1,    32,
      14,    82,    88,    33,    -1,    42,    -1,    -1,    32,    10,
      45,    45,    89,    33,    -1,    -1,    32,    12,    32,    62,
      33,    82,    90,    33,    -1,    -1,    32,     9,    32,    62,
      33,    82,    91,    33,    -1,    92,    82,    -1,    82,    -1,
      93,    95,    -1,    95,    -1,    42,    -1,    34,    -1,    -1,
      32,    17,    96,    33,    -1,    -1,    32,    17,    93,    97,
      33,    -1,    -1,    32,    15,    82,    95,    98,    33,    -1,
      -1,    32,    12,    32,    62,    33,    95,    99,    33,    -1,
      42,    -1,    -1,    32,    14,    42,   100,    33,    -1,    -1,
      32,     5,    42,    94,   101,    33,    -1
};

/* YYRLINE[YYN] -- source line where rule number YYN was defined.  */
static const yytype_uint8 yyrline[] =
{
       0,    59,    59,    62,    63,    66,    69,    69,    72,    73,
      74,    77,    78,    81,    82,    87,    87,    87,    90,    91,
      94,    94,    95,    95,    96,    96,    97,    97,    98,    98,
      99,    99,    99,   102,   103,   106,   106,   107,   108,   111,
     112,   113,   116,   117,   120,   121,   124,   128,   128,   128,
     131,   131,   132,   132,   135,   136,   137,   138,   139,   143,
     144,   147,   148,   148,   149,   150,   153,   153,   154,   157,
     158,   161,   162,   165,   165,   170,   170,   171,   171,   172,
     172,   173,   173,   174,   174,   175,   175,   176,   177,   177,
     178,   178,   179,   179,   182,   183,   186,   187,   190,   191,
     194,   194,   195,   195,   196,   196,   197,   197,   198,   199,
     199,   200,   200
};
#endif

#if YYDEBUG || YYERROR_VERBOSE || YYTOKEN_TABLE
/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "$end", "error", "$undefined", "rwMINIMIZE", "rwMETRIC", "rwINCREASE",
  "rwEITHER", "rwCONSTANTS", "rwLENGTH", "rwEXISTS", "EQUA", "rwPROBLEM",
  "rwFORALL", "rwIMPLY", "rwNOT", "rwWHEN", "rwOR", "rwAND", "rwTYPING",
  "rwDOMAIN", "rwGOAL", "rwINIT", "rwOBJECTS", "rwTYPES", "rwREQUIREMENTS",
  "rwPREDICATES", "rwPRECOND", "rwEFFECT", "rwPARAMS", "rwACTION",
  "rwDEFINE", "DASH", "LPAREN", "RPAREN", "INT", "VAR", "ID",
  "rwFUNCTIONS", "$accept", "begin", "idlist", "costexpr", "atom", "$@1",
  "atomlist", "varid", "varidlist", "domain", "$@2", "$@3", "domaindefs",
  "domaindef", "$@4", "$@5", "$@6", "$@7", "$@8", "$@9", "$@10", "actdefs",
  "actdef", "$@11", "opvars", "varlist", "opvarlist", "opvar", "problem",
  "$@12", "$@13", "defs", "$@14", "$@15", "def", "objectlist",
  "typedvarlist", "$@16", "typedatoms", "$@17", "functiondecls",
  "functiondecl", "tdecl", "$@18", "fma", "$@19", "$@20", "$@21", "$@22",
  "$@23", "$@24", "$@25", "$@26", "$@27", "fmas", "effects", "numexpr",
  "effect", "$@28", "$@29", "$@30", "$@31", "$@32", "$@33", 0
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
     285,   286,   287,   288,   289,   290,   291,   292
};
# endif

/* YYR1[YYN] -- Symbol number of symbol that rule YYN derives.  */
static const yytype_uint8 yyr1[] =
{
       0,    38,    39,    40,    40,    41,    43,    42,    44,    44,
      44,    45,    45,    46,    46,    48,    49,    47,    50,    50,
      52,    51,    53,    51,    54,    51,    55,    51,    56,    51,
      57,    58,    51,    59,    59,    61,    60,    60,    60,    62,
      62,    62,    63,    63,    64,    64,    65,    67,    68,    66,
      70,    69,    71,    69,    72,    72,    72,    72,    72,    73,
      73,    74,    75,    74,    74,    74,    77,    76,    76,    78,
      78,    79,    79,    81,    80,    83,    82,    84,    82,    85,
      82,    86,    82,    87,    82,    88,    82,    82,    89,    82,
      90,    82,    91,    82,    92,    92,    93,    93,    94,    94,
      96,    95,    97,    95,    98,    95,    99,    95,    95,   100,
      95,   101,    95
};

/* YYR2[YYN] -- Number of symbols composing right hand side of rule YYN.  */
static const yytype_uint8 yyr2[] =
{
       0,     2,     2,     2,     0,     5,     0,     5,     2,     2,
       0,     1,     1,     2,     0,     0,     0,    10,     2,     0,
       0,     5,     0,     5,     0,     5,     0,     5,     0,     5,
       0,     0,     7,     2,     1,     0,     5,     2,     2,     1,
       1,     0,     2,     1,     2,     1,     3,     0,     0,    10,
       0,     5,     0,     4,     2,     2,     2,     2,     3,     4,
       1,     4,     0,     9,     2,     0,     0,     6,     0,     2,
       0,     3,     1,     0,     5,     0,     4,     0,     5,     0,
       6,     0,     5,     0,     6,     0,     5,     1,     0,     6,
       0,     8,     0,     8,     2,     1,     2,     1,     1,     1,
       0,     4,     0,     5,     0,     6,     0,     8,     1,     0,
       5,     0,     6
};

/* YYDEFACT[STATE-NAME] -- Default rule to reduce with in state
   STATE-NUM when YYTABLE doesn't specify something else to do.  Zero
   means the default is an error.  */
static const yytype_uint8 yydefact[] =
{
       0,     0,     0,     0,     0,     1,     0,     2,     0,     0,
       0,     0,    15,     0,     0,    47,    19,     0,    16,     0,
       0,     0,    18,     0,    48,     4,     4,     4,    68,    30,
      70,    17,     0,     0,     0,    10,     4,    52,     0,     0,
       4,    60,    24,    28,    22,    20,     0,     0,    26,    70,
      72,    10,    54,     0,    87,    57,    56,    55,     0,    50,
      49,     3,     0,     0,     0,     0,     0,     0,     0,    65,
       0,    69,     0,    58,     0,     0,     0,     0,     0,     0,
       0,    75,    14,     0,     9,     8,    53,     0,     4,    25,
      29,    23,    65,    21,     0,     0,     0,    31,    34,    65,
      73,    27,    71,    41,    11,    12,     0,    41,     0,    85,
       0,    95,    81,     0,    77,    14,     6,     0,    51,    59,
      66,    37,     0,   108,    38,    41,     0,    33,     0,    64,
       0,    43,     0,    39,    40,    45,    88,     0,    83,     0,
      79,    94,     0,    76,     0,    13,     0,     0,    99,    98,
       0,     0,     0,     0,     0,     0,   100,    35,    32,     0,
      65,    74,    42,     0,     0,     0,    44,     0,     0,     0,
      86,     0,    82,    78,     7,     0,    67,     0,    41,   109,
       0,   102,    97,     0,     0,     0,    61,    92,    46,    89,
      90,    84,    80,     5,   111,     0,     0,   104,    96,     0,
     101,    36,     4,     0,     0,     0,     0,   110,     0,   103,
      62,    93,    91,   112,   106,   105,     0,     0,    65,   107,
      63
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int16 yydefgoto[] =
{
      -1,     2,    41,    84,    54,   146,    56,   115,   116,     3,
      14,    21,    18,    22,    67,    65,    63,    70,    64,    46,
     126,    97,    98,   184,   132,   133,   134,   135,     7,    17,
      39,    24,    87,    58,    37,    42,   100,   216,    45,   151,
      48,    49,    50,   130,   111,   113,   144,   171,   142,   169,
     139,   167,   204,   203,   112,   181,   150,   124,   183,   199,
     208,   217,   196,   205
};

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
#define YYPACT_NINF -151
static const yytype_int16 yypact[] =
{
     -20,    -4,    34,    22,    26,  -151,    15,  -151,    42,    32,
      29,    55,  -151,    33,    35,  -151,  -151,    38,    40,    41,
       4,    43,  -151,    31,    46,    44,    44,    44,  -151,  -151,
      50,  -151,    71,    57,    54,  -151,    44,  -151,    31,    61,
      44,    65,  -151,  -151,  -151,    66,    64,    67,  -151,    50,
      73,  -151,  -151,    75,  -151,  -151,    70,  -151,    72,  -151,
    -151,  -151,    74,    76,    79,    80,    78,    82,    16,    81,
      84,  -151,    83,    70,    86,    24,    88,    54,    54,    54,
      54,    54,    24,    13,  -151,  -151,  -151,    90,    44,  -151,
    -151,  -151,    81,  -151,    54,    89,    95,  -151,    16,   -11,
    -151,  -151,  -151,    94,  -151,  -151,    24,    94,    54,  -151,
      54,  -151,    54,    97,    54,    24,  -151,    23,  -151,  -151,
    -151,  -151,     2,  -151,  -151,    94,    98,  -151,     0,  -151,
     100,    94,   101,    77,  -151,    94,  -151,   102,  -151,   103,
    -151,  -151,   105,  -151,   106,  -151,   107,   108,  -151,  -151,
      23,   109,   111,   113,   111,    54,    89,  -151,  -151,   135,
      81,  -151,  -151,    54,   110,    77,  -151,   114,    54,   115,
    -151,   116,  -151,  -151,  -151,   117,  -151,    23,    94,  -151,
      89,    89,  -151,   119,   120,   118,  -151,  -151,  -151,  -151,
    -151,  -151,  -151,  -151,  -151,   122,   123,  -151,  -151,   124,
    -151,  -151,    44,   125,   126,   127,    89,  -151,   128,  -151,
    -151,  -151,  -151,  -151,  -151,  -151,   129,   130,    81,  -151,
    -151
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
    -151,  -151,   -27,  -151,   -55,  -151,    56,   -67,    -9,  -151,
    -151,  -151,  -151,  -151,  -151,  -151,  -151,  -151,  -151,  -151,
    -151,    68,  -151,  -151,  -103,  -110,    30,  -151,  -151,  -151,
    -151,  -151,  -151,  -151,   131,   -21,   -90,  -151,  -151,  -151,
     121,  -151,  -151,  -151,   -31,  -151,  -151,  -151,  -151,  -151,
    -151,  -151,  -151,  -151,    87,  -151,  -140,  -150,  -151,  -151,
    -151,  -151,  -151,  -151
};

/* YYTABLE[YYPACT[STATE-NUM]].  What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule which
   number is the opposite.  If zero, do what YYDEFACT says.
   If YYTABLE_NINF, syntax error.  */
#define YYTABLE_NINF -1
static const yytype_uint8 yytable[] =
{
      44,    85,   120,    55,   137,    43,   182,   152,   106,   129,
     175,    25,     1,    61,   153,    57,   154,   155,    85,   156,
     128,   162,   157,   117,    99,   165,     4,    26,    27,    28,
     197,   198,   159,    29,     5,    32,   160,   194,    82,   136,
     123,    30,    94,    95,    96,     9,   108,   109,   110,    82,
      33,    34,    35,    36,     6,   147,   214,   148,     8,   104,
     105,    10,   149,   121,    11,    12,    13,   119,    16,    15,
     186,    19,    20,    23,    51,   195,    31,   138,    38,   140,
      40,   141,    47,   141,    74,    75,    53,    76,    77,    78,
      79,    80,    81,    52,    60,   149,    62,   177,    66,   179,
      68,   123,    83,    69,    72,    86,   145,    73,   164,    89,
      88,    82,    90,    91,    92,    93,    99,   101,   103,   102,
     107,   122,   149,   118,   180,   123,   123,   125,   220,   131,
     143,   158,   187,   161,   163,   168,   170,   190,   172,   173,
     174,   185,   176,   147,    82,   178,   188,   189,   191,   192,
     193,   123,   200,   201,   202,   206,   207,   209,   211,   212,
     213,   215,   218,   219,     0,   166,   127,     0,   114,    59,
      71,     0,     0,     0,     0,   210
};

static const yytype_int16 yycheck[] =
{
      27,    56,    92,    34,   107,    26,   156,     5,    75,    99,
     150,     7,    32,    40,    12,    36,    14,    15,    73,    17,
      31,   131,   125,    10,    35,   135,    30,    23,    24,    25,
     180,   181,    32,    29,     0,     4,    36,   177,    36,   106,
      95,    37,    26,    27,    28,    30,    77,    78,    79,    36,
      19,    20,    21,    22,    32,    32,   206,    34,    32,    35,
      36,    19,   117,    94,    32,    36,    11,    88,    33,    36,
     160,    33,    32,    32,     3,   178,    33,   108,    32,   110,
      36,   112,    32,   114,     9,    10,    32,    12,    13,    14,
      15,    16,    17,    36,    33,   150,    31,   152,    32,   154,
      36,   156,    32,    36,    31,    33,   115,    51,    31,    33,
      36,    36,    33,    33,    36,    33,    35,    33,    32,    36,
      32,    32,   177,    33,   155,   180,   181,    32,   218,    35,
      33,    33,   163,    33,    33,    33,    33,   168,    33,    33,
      33,     6,    33,    32,    36,    32,    36,    33,    33,    33,
      33,   206,    33,    33,    36,    33,    33,    33,    33,    33,
      33,    33,    33,    33,    -1,   135,    98,    -1,    81,    38,
      49,    -1,    -1,    -1,    -1,   202
};

/* YYSTOS[STATE-NUM] -- The (internal number of the) accessing
   symbol of state STATE-NUM.  */
static const yytype_uint8 yystos[] =
{
       0,    32,    39,    47,    30,     0,    32,    66,    32,    30,
      19,    32,    36,    11,    48,    36,    33,    67,    50,    33,
      32,    49,    51,    32,    69,     7,    23,    24,    25,    29,
      37,    33,     4,    19,    20,    21,    22,    72,    32,    68,
      36,    40,    73,    73,    40,    76,    57,    32,    78,    79,
      80,     3,    36,    32,    42,    82,    44,    73,    71,    72,
      33,    40,    31,    54,    56,    53,    32,    52,    36,    36,
      55,    78,    31,    44,     9,    10,    12,    13,    14,    15,
      16,    17,    36,    32,    41,    42,    33,    70,    36,    33,
      33,    33,    36,    33,    26,    27,    28,    59,    60,    35,
      74,    33,    36,    32,    35,    36,    45,    32,    82,    82,
      82,    82,    92,    83,    92,    45,    46,    10,    33,    73,
      74,    82,    32,    42,    95,    32,    58,    59,    31,    74,
      81,    35,    62,    63,    64,    65,    45,    62,    82,    88,
      82,    82,    86,    33,    84,    46,    43,    32,    34,    42,
      94,    77,     5,    12,    14,    15,    17,    62,    33,    32,
      36,    33,    63,    33,    31,    63,    64,    89,    33,    87,
      33,    85,    33,    33,    33,    94,    33,    42,    32,    42,
      82,    93,    95,    96,    61,     6,    74,    82,    36,    33,
      82,    33,    33,    33,    94,    62,   100,    95,    95,    97,
      33,    33,    36,    91,    90,   101,    33,    33,    98,    33,
      40,    33,    33,    33,    95,    33,    75,    99,    33,    33,
      74
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
        case 3:

/* Line 1455 of yacc.c  */
#line 62 "parser.y"
    { (yyval.intlistp) = intcons((yyvsp[(1) - (2)].i),(yyvsp[(2) - (2)].intlistp)); ;}
    break;

  case 4:

/* Line 1455 of yacc.c  */
#line 63 "parser.y"
    { (yyval.intlistp) = EMPTYLIST; ;}
    break;

  case 5:

/* Line 1455 of yacc.c  */
#line 66 "parser.y"
    { ;}
    break;

  case 6:

/* Line 1455 of yacc.c  */
#line 69 "parser.y"
    { rparen("term"); ;}
    break;

  case 7:

/* Line 1455 of yacc.c  */
#line 69 "parser.y"
    { (yyval.atomp) = newatom((yyvsp[(2) - (5)].i),(yyvsp[(3) - (5)].intlistp)); ;}
    break;

  case 8:

/* Line 1455 of yacc.c  */
#line 72 "parser.y"
    { (yyval.atomlistp) = atomcons((yyvsp[(2) - (2)].atomp),(yyvsp[(1) - (2)].atomlistp)); ;}
    break;

  case 9:

/* Line 1455 of yacc.c  */
#line 73 "parser.y"
    { (yyval.atomlistp) = (yyvsp[(1) - (2)].atomlistp); ;}
    break;

  case 10:

/* Line 1455 of yacc.c  */
#line 74 "parser.y"
    { (yyval.atomlistp) = EMPTYLIST; ;}
    break;

  case 11:

/* Line 1455 of yacc.c  */
#line 77 "parser.y"
    { (yyval.i) = (yyvsp[(1) - (1)].i); ;}
    break;

  case 12:

/* Line 1455 of yacc.c  */
#line 78 "parser.y"
    { (yyval.i) = (yyvsp[(1) - (1)].i); ;}
    break;

  case 13:

/* Line 1455 of yacc.c  */
#line 81 "parser.y"
    { (yyval.intlistp) = intcons((yyvsp[(1) - (2)].i),(yyvsp[(2) - (2)].intlistp)); ;}
    break;

  case 14:

/* Line 1455 of yacc.c  */
#line 82 "parser.y"
    { (yyval.intlistp) = EMPTYLIST; ;}
    break;

  case 15:

/* Line 1455 of yacc.c  */
#line 87 "parser.y"
    { rparen("domain"); ;}
    break;

  case 16:

/* Line 1455 of yacc.c  */
#line 87 "parser.y"
    { rparen("domain body"); ;}
    break;

  case 17:

/* Line 1455 of yacc.c  */
#line 87 "parser.y"
    { storedomain((yyvsp[(5) - (10)].i)); ;}
    break;

  case 19:

/* Line 1455 of yacc.c  */
#line 91 "parser.y"
    { ;}
    break;

  case 20:

/* Line 1455 of yacc.c  */
#line 94 "parser.y"
    { rparen(":predicates"); ;}
    break;

  case 21:

/* Line 1455 of yacc.c  */
#line 94 "parser.y"
    { storepredicates(); ;}
    break;

  case 22:

/* Line 1455 of yacc.c  */
#line 95 "parser.y"
    { rparen(":requirements"); ;}
    break;

  case 23:

/* Line 1455 of yacc.c  */
#line 95 "parser.y"
    { checkrequirements((yyvsp[(3) - (5)].intlistp)); ;}
    break;

  case 24:

/* Line 1455 of yacc.c  */
#line 96 "parser.y"
    { rparen(":constants"); ;}
    break;

  case 25:

/* Line 1455 of yacc.c  */
#line 96 "parser.y"
    { storeconstants((yyvsp[(3) - (5)].typedvarlistp)); ;}
    break;

  case 26:

/* Line 1455 of yacc.c  */
#line 97 "parser.y"
    { rparen(":functions"); ;}
    break;

  case 27:

/* Line 1455 of yacc.c  */
#line 97 "parser.y"
    { ;}
    break;

  case 28:

/* Line 1455 of yacc.c  */
#line 98 "parser.y"
    { rparen(":types"); ;}
    break;

  case 29:

/* Line 1455 of yacc.c  */
#line 98 "parser.y"
    { storetypes((yyvsp[(3) - (5)].typedvarlistp)); ;}
    break;

  case 30:

/* Line 1455 of yacc.c  */
#line 99 "parser.y"
    { COST = 0; ;}
    break;

  case 31:

/* Line 1455 of yacc.c  */
#line 99 "parser.y"
    { rparen(":action"); ;}
    break;

  case 32:

/* Line 1455 of yacc.c  */
#line 99 "parser.y"
    { addactioncost(COST); addnewaction((yyvsp[(4) - (7)].i)); ;}
    break;

  case 35:

/* Line 1455 of yacc.c  */
#line 106 "parser.y"
    { rparen(":action definitions"); ;}
    break;

  case 36:

/* Line 1455 of yacc.c  */
#line 106 "parser.y"
    { addactionparameters((yyvsp[(3) - (5)].typedvarlistp)); ;}
    break;

  case 37:

/* Line 1455 of yacc.c  */
#line 107 "parser.y"
    { addactionprecond((yyvsp[(2) - (2)].Sfmap)); ;}
    break;

  case 38:

/* Line 1455 of yacc.c  */
#line 108 "parser.y"
    { addactioneffect((yyvsp[(2) - (2)].Seffp)); ;}
    break;

  case 39:

/* Line 1455 of yacc.c  */
#line 111 "parser.y"
    { (yyval.typedvarlistp) = withtype(UNIVTYPE,(yyvsp[(1) - (1)].intlistp)); ;}
    break;

  case 40:

/* Line 1455 of yacc.c  */
#line 112 "parser.y"
    { (yyval.typedvarlistp) = (yyvsp[(1) - (1)].typedvarlistp); ;}
    break;

  case 41:

/* Line 1455 of yacc.c  */
#line 113 "parser.y"
    { (yyval.typedvarlistp) = EMPTYLIST; ;}
    break;

  case 42:

/* Line 1455 of yacc.c  */
#line 116 "parser.y"
    { (yyval.intlistp) = intcons((yyvsp[(1) - (2)].i),(yyvsp[(2) - (2)].intlistp)); ;}
    break;

  case 43:

/* Line 1455 of yacc.c  */
#line 117 "parser.y"
    { (yyval.intlistp) = intcons((yyvsp[(1) - (1)].i), EMPTYLIST); ;}
    break;

  case 44:

/* Line 1455 of yacc.c  */
#line 120 "parser.y"
    { (yyval.typedvarlistp) = TVappend((yyvsp[(1) - (2)].typedvarlistp),(yyvsp[(2) - (2)].typedvarlistp)); ;}
    break;

  case 45:

/* Line 1455 of yacc.c  */
#line 121 "parser.y"
    { (yyval.typedvarlistp) = (yyvsp[(1) - (1)].typedvarlistp); ;}
    break;

  case 46:

/* Line 1455 of yacc.c  */
#line 124 "parser.y"
    { (yyval.typedvarlistp) = withtype((yyvsp[(3) - (3)].i),(yyvsp[(1) - (3)].intlistp)); ;}
    break;

  case 47:

/* Line 1455 of yacc.c  */
#line 128 "parser.y"
    { rparen(":problem"); ;}
    break;

  case 48:

/* Line 1455 of yacc.c  */
#line 128 "parser.y"
    { rparen("problem definition"); ;}
    break;

  case 49:

/* Line 1455 of yacc.c  */
#line 128 "parser.y"
    { addproblem((yyvsp[(5) - (10)].i)); ;}
    break;

  case 50:

/* Line 1455 of yacc.c  */
#line 131 "parser.y"
    { rparen("problem definitions"); ;}
    break;

  case 51:

/* Line 1455 of yacc.c  */
#line 131 "parser.y"
    { ;}
    break;

  case 52:

/* Line 1455 of yacc.c  */
#line 132 "parser.y"
    { rparen("problem definitions"); ;}
    break;

  case 53:

/* Line 1455 of yacc.c  */
#line 132 "parser.y"
    { ;}
    break;

  case 54:

/* Line 1455 of yacc.c  */
#line 135 "parser.y"
    { checkdomain((yyvsp[(2) - (2)].i)); ;}
    break;

  case 55:

/* Line 1455 of yacc.c  */
#line 136 "parser.y"
    { storeobjects((yyvsp[(2) - (2)].typedvarlistp)); ;}
    break;

  case 56:

/* Line 1455 of yacc.c  */
#line 137 "parser.y"
    { storeinit((yyvsp[(2) - (2)].atomlistp)); ;}
    break;

  case 57:

/* Line 1455 of yacc.c  */
#line 138 "parser.y"
    { storegoal((yyvsp[(2) - (2)].Sfmap)); ;}
    break;

  case 58:

/* Line 1455 of yacc.c  */
#line 139 "parser.y"
    { ;}
    break;

  case 59:

/* Line 1455 of yacc.c  */
#line 143 "parser.y"
    { (yyval.typedvarlistp) = TVappend(withtype((yyvsp[(3) - (4)].i),(yyvsp[(1) - (4)].intlistp)),(yyvsp[(4) - (4)].typedvarlistp)); ;}
    break;

  case 60:

/* Line 1455 of yacc.c  */
#line 144 "parser.y"
    { (yyval.typedvarlistp) = withtype(UNIVTYPE,(yyvsp[(1) - (1)].intlistp)); ;}
    break;

  case 61:

/* Line 1455 of yacc.c  */
#line 147 "parser.y"
    { ;}
    break;

  case 62:

/* Line 1455 of yacc.c  */
#line 148 "parser.y"
    { rparen("typed variable list"); ;}
    break;

  case 63:

/* Line 1455 of yacc.c  */
#line 148 "parser.y"
    { ;}
    break;

  case 64:

/* Line 1455 of yacc.c  */
#line 149 "parser.y"
    { ;}
    break;

  case 65:

/* Line 1455 of yacc.c  */
#line 150 "parser.y"
    { ;}
    break;

  case 66:

/* Line 1455 of yacc.c  */
#line 153 "parser.y"
    { rparen("typed atom list"); ;}
    break;

  case 67:

/* Line 1455 of yacc.c  */
#line 153 "parser.y"
    { ;}
    break;

  case 68:

/* Line 1455 of yacc.c  */
#line 154 "parser.y"
    { ;}
    break;

  case 69:

/* Line 1455 of yacc.c  */
#line 157 "parser.y"
    { ;}
    break;

  case 70:

/* Line 1455 of yacc.c  */
#line 158 "parser.y"
    { ;}
    break;

  case 71:

/* Line 1455 of yacc.c  */
#line 161 "parser.y"
    { ;}
    break;

  case 72:

/* Line 1455 of yacc.c  */
#line 162 "parser.y"
    { ;}
    break;

  case 73:

/* Line 1455 of yacc.c  */
#line 165 "parser.y"
    { rparen("function list"); ;}
    break;

  case 75:

/* Line 1455 of yacc.c  */
#line 170 "parser.y"
    { rparen("empty conjunction"); ;}
    break;

  case 76:

/* Line 1455 of yacc.c  */
#line 170 "parser.y"
    { (yyval.Sfmap) = Strue(); ;}
    break;

  case 77:

/* Line 1455 of yacc.c  */
#line 171 "parser.y"
    { rparen("conjunction"); ;}
    break;

  case 78:

/* Line 1455 of yacc.c  */
#line 171 "parser.y"
    { (yyval.Sfmap) = Sconjunction((yyvsp[(3) - (5)].Sfmalistp)); ;}
    break;

  case 79:

/* Line 1455 of yacc.c  */
#line 172 "parser.y"
    { rparen("when"); ;}
    break;

  case 80:

/* Line 1455 of yacc.c  */
#line 172 "parser.y"
    { (yyval.Sfmap) = Sconjunction(Sfmacons(Sneg((yyvsp[(3) - (6)].Sfmap)),Sfmacons((yyvsp[(4) - (6)].Sfmap),EMPTYLIST))); ;}
    break;

  case 81:

/* Line 1455 of yacc.c  */
#line 173 "parser.y"
    { rparen("disjunction"); ;}
    break;

  case 82:

/* Line 1455 of yacc.c  */
#line 173 "parser.y"
    { (yyval.Sfmap) = Sdisjunction((yyvsp[(3) - (5)].Sfmalistp)); ;}
    break;

  case 83:

/* Line 1455 of yacc.c  */
#line 174 "parser.y"
    { rparen("imply"); ;}
    break;

  case 84:

/* Line 1455 of yacc.c  */
#line 174 "parser.y"
    { (yyval.Sfmap) = Sdisjunction(Sfmacons(Sneg((yyvsp[(3) - (6)].Sfmap)),Sfmacons((yyvsp[(4) - (6)].Sfmap),EMPTYLIST))); ;}
    break;

  case 85:

/* Line 1455 of yacc.c  */
#line 175 "parser.y"
    { rparen("not"); ;}
    break;

  case 86:

/* Line 1455 of yacc.c  */
#line 175 "parser.y"
    { (yyval.Sfmap) = Sneg((yyvsp[(3) - (5)].Sfmap)); ;}
    break;

  case 87:

/* Line 1455 of yacc.c  */
#line 176 "parser.y"
    { (yyval.Sfmap) = Satom((yyvsp[(1) - (1)].atomp)); ;}
    break;

  case 88:

/* Line 1455 of yacc.c  */
#line 177 "parser.y"
    { rparen("equality"); ;}
    break;

  case 89:

/* Line 1455 of yacc.c  */
#line 177 "parser.y"
    { (yyval.Sfmap) = SfmaEQ((yyvsp[(3) - (6)].i),(yyvsp[(4) - (6)].i)); ;}
    break;

  case 90:

/* Line 1455 of yacc.c  */
#line 178 "parser.y"
    { rparen("forall"); ;}
    break;

  case 91:

/* Line 1455 of yacc.c  */
#line 178 "parser.y"
    { (yyval.Sfmap) = Sfmaforall((yyvsp[(4) - (8)].typedvarlistp),(yyvsp[(6) - (8)].Sfmap)); ;}
    break;

  case 92:

/* Line 1455 of yacc.c  */
#line 179 "parser.y"
    { rparen("exists"); ;}
    break;

  case 93:

/* Line 1455 of yacc.c  */
#line 179 "parser.y"
    { (yyval.Sfmap) = Sfmaforsome((yyvsp[(4) - (8)].typedvarlistp),(yyvsp[(6) - (8)].Sfmap)); ;}
    break;

  case 94:

/* Line 1455 of yacc.c  */
#line 182 "parser.y"
    { (yyval.Sfmalistp) = Sfmacons((yyvsp[(2) - (2)].Sfmap),(yyvsp[(1) - (2)].Sfmalistp)); ;}
    break;

  case 95:

/* Line 1455 of yacc.c  */
#line 183 "parser.y"
    { (yyval.Sfmalistp) = Sfmacons((yyvsp[(1) - (1)].Sfmap),EMPTYLIST); ;}
    break;

  case 96:

/* Line 1455 of yacc.c  */
#line 186 "parser.y"
    { (yyval.Sefflistp) = Seffcons((yyvsp[(2) - (2)].Seffp),(yyvsp[(1) - (2)].Sefflistp)); ;}
    break;

  case 97:

/* Line 1455 of yacc.c  */
#line 187 "parser.y"
    { (yyval.Sefflistp) = Seffcons((yyvsp[(1) - (1)].Seffp),EMPTYLIST); ;}
    break;

  case 98:

/* Line 1455 of yacc.c  */
#line 190 "parser.y"
    { (yyval.i) = 0; ;}
    break;

  case 99:

/* Line 1455 of yacc.c  */
#line 191 "parser.y"
    { (yyval.i) = (yyvsp[(1) - (1)].i); ;}
    break;

  case 100:

/* Line 1455 of yacc.c  */
#line 194 "parser.y"
    { rparen("empty conjunction"); ;}
    break;

  case 101:

/* Line 1455 of yacc.c  */
#line 194 "parser.y"
    { (yyval.Seffp) = Seffconjunction(EMPTYLIST); ;}
    break;

  case 102:

/* Line 1455 of yacc.c  */
#line 195 "parser.y"
    { rparen("compound effect"); ;}
    break;

  case 103:

/* Line 1455 of yacc.c  */
#line 195 "parser.y"
    { (yyval.Seffp) = Seffconjunction((yyvsp[(3) - (5)].Sefflistp)); ;}
    break;

  case 104:

/* Line 1455 of yacc.c  */
#line 196 "parser.y"
    { rparen("when"); ;}
    break;

  case 105:

/* Line 1455 of yacc.c  */
#line 196 "parser.y"
    { (yyval.Seffp) = Seffwhen((yyvsp[(3) - (6)].Sfmap),(yyvsp[(4) - (6)].Seffp)); ;}
    break;

  case 106:

/* Line 1455 of yacc.c  */
#line 197 "parser.y"
    { rparen("forall"); ;}
    break;

  case 107:

/* Line 1455 of yacc.c  */
#line 197 "parser.y"
    { (yyval.Seffp) = Seffforall((yyvsp[(4) - (8)].typedvarlistp),(yyvsp[(6) - (8)].Seffp)); ;}
    break;

  case 108:

/* Line 1455 of yacc.c  */
#line 198 "parser.y"
    { (yyval.Seffp) = SPeffatom((yyvsp[(1) - (1)].atomp)); ;}
    break;

  case 109:

/* Line 1455 of yacc.c  */
#line 199 "parser.y"
    { rparen("not"); ;}
    break;

  case 110:

/* Line 1455 of yacc.c  */
#line 199 "parser.y"
    { (yyval.Seffp) = SNeffatom((yyvsp[(3) - (5)].atomp)); ;}
    break;

  case 111:

/* Line 1455 of yacc.c  */
#line 200 "parser.y"
    { rparen("increase"); ;}
    break;

  case 112:

/* Line 1455 of yacc.c  */
#line 200 "parser.y"
    { (yyval.Seffp) = Seffconjunction(NULL); COST = (yyvsp[(4) - (6)].i); ;}
    break;



/* Line 1455 of yacc.c  */
#line 2318 "parser.tab.c"
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
#line 203 "parser.y"


void parseerror(char *s) {
  errorstring = s;
}

void rparen(char *s) {
  errorstring = s;
}

