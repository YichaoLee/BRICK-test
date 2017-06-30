##===- lib/Transforms/MyInstrumentation/Makefile -----------------------*- Makefile -*-===##
#
#                     The LLVM Compiler Infrastructure
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
##===----------------------------------------------------------------------===##

LEVEL = ../../..
LIBRARYNAME = buildCFG
LOADABLE_MODULE = 1
USEDLIBS = ClpSolver.a Clp.a CoinUtils.a capd.a prim.a ibex.a nlopt.a
# -ldreal -libex -lClpSolver -lClp -lCoinUtils -lcapd -lnlopt -lprim -lz3 -lminisat

# If we don't need RTTI or EH, there's no reason to export anything
# from the MyInstrumentation plugin.
ifneq ($(REQUIRES_RTTI), 1)
ifneq ($(REQUIRES_EH), 1)
EXPORTED_SYMBOL_FILE = $(PROJ_SRC_DIR)/buildCFG.exports
endif
endif
CCOPT = -fPIC -fno-strict-aliasing -fexceptions -DIL_STD 
CPPFLAGS += -g -O3 $(CCOPT) -Iinclude -I.  -D __STDC_LIMIT_MACROS -D __STD_FORMAT_MACROS -I/usr/include/python2.7 -Wall -Wno-parentheses -Wextra -std=c++11 -mfpmath=sse -msse -msse2 -ffloat-store -frounding-math -lm -lpthread 
#CXXFLAGS += -g -O3 $(CCOPT) -Iinclude -I.  -D __STDC_LIMIT_MACROS -D __STD_FORMAT_MACROS -I/usr/include/python2.7 -Wall -Wno-parentheses -Wextra -std=c++11 -mfpmath=sse -msse -msse2 -ffloat-store -frounding-math -ldreal -libex -lClpSolver -lClp -lCoinUtils -lm -lcapd -lnlopt -lprim -lpthread
#CXXFLAGS += -fexceptions
include $(LEVEL)/Makefile.common

