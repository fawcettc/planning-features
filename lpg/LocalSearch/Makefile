#####################
# Makefile for LPG  #
#####################


####### FLAGS

CFLAGS = -g -DNDEBUG


####### INCLUDE CONFIGURATION FILE

include ../configure.make


####### COMPILE

CC = gcc 

PATH_HEADERS = -I$(SRC_HEADER)

SRC_HEADER =../include

SOURCES = H_relaxed.c \
	H_max.c \
	numeric.c \
	LocalSearch.c \
	ActionSubgraph.c \
	time.c\
	ComputeReachInf.c

OBJECTS = $(SOURCES:.c=.o)

find_header = $(wildcard $(dir)/*.h)

HEADERS := $(foreach dir,../include,$(find_header))


####### Implicit rules

.SUFFIXES:

.SUFFIXES: .c .o

.c.o:; $(CC) $(PATH_HEADERS) -c $(CFLAGS) $<


####### Build rules

LocalSearch.a: 	$(OBJECTS) 
		$(AR) rc $@ $(OBJECTS)

$(OBJECTS): $(HEADERS)

clean:
	rm -f *.o *.a *~ .#*

#######
