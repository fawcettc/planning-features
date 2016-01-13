# 2012 (C) Jussi Rintanen, jrintanen.jr@gmail.com

#EXECUTABLE=nplan
# Uncomment for Madagascar with the planning heuristic as default (Mp)
VERSION = -DMPDOWNLOAD
EXECUTABLE=Mp
# Uncomment for Madagascar C with the planning heuristic as default (MpC)
#VERSION = -DCMPDOWNLOAD
#EXECUTABLE=MpC
# Uncomment for Madagascar with VSIDS as default (M)
#VERSION = -DVSIDS
#EXECUTABLE=M
ARCH=-m64

INSTRUMENT = #-g -ggdb -pg

CONFIGURATION= -DLBD -DREPRTHREE -DWEIGHTS #-DFUIP #-DMULTICORE #-DSPREAD -DCOSTS -DCFMA  -DCP3

#FEATURES= -fopenmp
#LINKFEATURES= -fopenmp

# The following options are specific to GCC. Disable when necessary (e.g. in OS X).
GCCOPTIMIZE= $(ARCH) -O3 -fprefetch-loop-arrays -funroll-loops -ftree-loop-im -ftracer -maccumulate-outgoing-args -momit-leaf-frame-pointer #-falign-functions=64

CFLAGS = $(VERSION) $(FEATURES) $(CONFIGURATION) $(INSTRUMENT) $(GCCOPTIMIZE) -Wall

PARSERGENERATOR=bison
PARSERC = parser.tab.c
PARSERH = parser.tab.h
PARSER=parser
#PARSERGENERATOR=yacc
#PARSERC = y.tab.c
#PARSERH = y.tab.h
#PARSER=y

CC = gcc

#LINKFLAGS = -L . -lcp3 -lpthread -lz -lrt #-static
#LINKFLAGS = -s
LINKFLAGS = $(ARCH) -static

OBJ = $(PARSER).tab.o main.o asyntax.o lex.yy.o tables.o operators.o invariants.o intsets.o cleanup.o translate2sat.o scc.o clausesets.o printplan.o clausedb.o dimacsinput.o ground.o
HDR = main.h asyntax.h tables.h operators.h invariants.h intsets.h cleanup.h scc.h intsets.h translate2sat.h ordintsets.h clausedb.h interface.h printplan.h dimacsinput.h

all: nplan

nplan: date lex.yy.c Makefile $(PARSERC) $(OBJ) $(HDR)
	$(CC) $(LINKFLAGS) $(LINKFEATURES) $(INSTRUMENT) $(OBJ) -lm -o $(EXECUTABLE)

clausesets.o: heuristics2.c varvals.c learn2.c

ground.o: Cground.c

%.o: %.c Makefile $(HDR)
	$(CC) $(CFLAGS) $(AMD64FLAGS) -c $<

date:
	./makedate

main.o: zPRINTDATE

$(PARSERC): parser.y
	$(PARSERGENERATOR) -d parser.y

$(PARSERH): parser.y
	$(PARSERGENERATOR) -d parser.y

lex.yy.c: lexer.lex $(PARSERH) $(PARSERH)
	flex lexer.lex

clean:
	rm -f $(OBJ) $(PARSERC) $(PARSERH)

tar:
	tar cvf MADAGASCAR.TAR README plan build asyntax.c asyntax.h clausedb.c clausedb.h clausesets.c clausesets.h cleanup.c cleanup.h dimacs.h dimacsinput.c dimacsinput.h ground.c Cground.c heuristics2.c interface.h intsets.c intsets.h invariants.c invariants.h lexer.lex main.c main.h makedate Makefile operators.c operators.h ordintsets.c ordintsets.h parser.y printplan.c printplan.h scc.c scc.h tables.c tables.h translate2sat.c translate2sat.h varvals.c learn2.c shortcuts.c zPOSTF zPREF
