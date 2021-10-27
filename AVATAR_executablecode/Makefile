CC     = /usr/bin/gcc
#CC     = test2.sh
#CC = /packages/gcc_3.2.2/bin/g++32
OPT    = -O1 -pthread
# Solaris
#LOPT   = -O1 -pthread -ldl -lnsl -lsocket
#Linux
LOPT_UNIX   = -O1 -pthread -ldl -lm
LOPT_MAC = -O1 -pthread -ldl

DEBUG  = -g
OTHER  = -Wall
TRY    = 
CFLAGS = $(OPT) $(OTHER) $(TRY)
LFLAGS_MAC = $(LOPT_MAC) $(OTHER) $(TRY)
LFLAGS_UNIX = $(LOPT_UNIX) $(OTHER) $(TRY)
# CFLAGS = $(DEBUG) $(OTHER)
OBJDIR = lib

MODULE = run
SRCS_generated_DIR = generated_src
SRCS_fstar_DIR = fstar/out
SRCS_misrac_DIR = misrac
include Makefile.src
SRCS_base_DIRSRC = src
SRCS_base = $(foreach dir, $(SRCS_base_DIRSRC), $(wildcard $(dir)/*.c))
SRCS_fstar = $(foreach dir, $(SRCS_fstar_DIR), $(wildcard $(dir)/*.c))
SRCS_misrac = $(foreach dir, $(SRCS_misrac_DIR), $(wildcard $(dir)/*.c))
SRCS_base_DIR = .
Kremlin = $(KREMLIN_HOME)/include
OBJS_executor = $(SRCS_base:%.c=lib/%.o)
OBJS = $(SRCS:%.c=lib/%.o)
OBJS_fstar = $(SRCS_fstar:%.c=lib/%.o)
OBJS_misrac = $(SRCS_misrac:%.c=lib/%.o)

include Makefile.defs


