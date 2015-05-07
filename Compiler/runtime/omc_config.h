/*
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-2013, Linköpings University,
 * Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF THIS OSMC PUBLIC
 * LICENSE (OSMC-PL). ANY USE, REPRODUCTION OR DISTRIBUTION OF
 * THIS PROGRAM CONSTITUTES RECIPIENT'S ACCEPTANCE OF THE OSMC
 * PUBLIC LICENSE.
 *
 * The OpenModelica software and the Open Source Modelica
 * Consortium (OSMC) Public License (OSMC-PL) are obtained
 * from Linköpings University, either from the above address,
 * from the URL: http://www.ida.liu.se/projects/OpenModelica
 * and in the OpenModelica distribution.
 *
 * This program is distributed  WITHOUT ANY WARRANTY; without
 * even the implied warranty of  MERCHANTABILITY or FITNESS
 * FOR A PARTICULAR PURPOSE, EXCEPT AS EXPRESSLY SET FORTH
 * IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE CONDITIONS
 * OF OSMC-PL.
 *
 * See the full OSMC Public License conditions for more details.
 *
 */

#ifndef OPENMODELICA_CONFIG_H
#define OPENMODELICA_CONFIG_H

#if defined(__MINGW32__) || defined(_MSC_VER) /* Windows */

#define DEFAULT_CC "gcc"
#define DEFAULT_CXX "g++"
#define DEFAULT_OMPCC "gcc -fopenmp"
#define DEFAULT_MAKE "make"

/* adrpo: add -loleaut32 as is used by ExternalMedia */
#define DEFAULT_LDFLAGS "-lregex -lexpat -lomcgc -lpthread -fopenmp -loleaut32"

#define CONFIG_PLATFORM "WIN32"
#define CONFIG_MODELICA_SPEC_PLATFORM "win32"
#define CONFIG_OPENMODELICA_SPEC_PLATFORM "mingw32"
#define CONFIG_USER_IS_ROOT 0
#define CONFIG_WITH_OPENMP 1

#define CONFIG_DEFAULT_OPENMODELICAHOME NULL
#if defined(__MINGW32__)
  #define CONFIGURE_COMMANDLINE "Manually created Makefiles for OMDev"
#elif defined(_MSC_VER)
  #define CONFIGURE_COMMANDLINE "Manually created Makefiles for Visual Studio"
#endif

/* adrpo: add -loleaut32 as is used by ExternalMedia */
#define BASIC_LDFLAGS_RT " -lomcgc -lexpat -lregex -static-libgcc -luuid -loleaut32 -lole32 -lws2_32 -llis -lumfpack -lamd -lsundials_kinsol -lsundials_nvecserial -lipopt -lcoinmumps -lpthread -lm -lgfortranbegin -lgfortran -lmingw32 -lgcc_eh -lmoldname -lmingwex -lmsvcrt -luser32 -lkernel32 -ladvapi32 -lshell32 -llapack-mingw -lcminpack -ltmglib-mingw -lblas-mingw -lf2c"
#define LDFLAGS_RT " -lOpenModelicaRuntimeC" BASIC_LDFLAGS_RT
#define LDFLAGS_RT_SIM " -lSimulationRuntimeC" BASIC_LDFLAGS_RT " -lwsock32 -lstdc++"
#define CONFIG_EXE_EXT ".exe"
#define CONFIG_DLL_EXT ".dll"
#define CONFIG_OS "Windows_NT"
#define CONFIG_CORBALIBS "-L$(OPENMODELICAHOME)/lib/omc -lmico2313"
#define CONFIG_LPSOLVEINC "lpsolve/lp_lib.h"
/* Windows is always "special" */
#define CONFIG_SYSTEMLIBS mmc_mk_nil()


#if defined(__i386__) || defined(__x86_64__) || defined(_MSC_VER)
  /*
   * if we are on i386 or x86_64 or compiling with
   * Visual Studio then use the SSE instructions,
   * not the normal i387 FPU
   */
  #define DEFAULT_CFLAGS "${SIM_OR_DYNLOAD_OPT_LEVEL} -falign-functions -msse2 -mfpmath=sse ${MODELICAUSERCFLAGS}"
#else
  #define DEFAULT_CFLAGS "${SIM_OR_DYNLOAD_OPT_LEVEL} -falign-functions ${MODELICAUSERCFLAGS}"
#endif
#if defined(__x86_64__)
  /* -fPIC needed on x86_64! */
  #define DEFAULT_LINKER "g++ -shared -Xlinker --export-all-symbols -fPIC"
#else
  #define DEFAULT_LINKER "g++ -shared -Xlinker --export-all-symbols"
#endif
#define DEFAULT_TRIPLE ""

#define CONFIG_PATH_DELIMITER "/"
#define CONFIG_GROUP_DELIMITER ";"

#define CONFIG_IPOPT_INC /* Without IPOPT */
#define CONFIG_IPOPT_LIB /* Without IPOPT */

#define WITH_SUNDIALS

#if defined(__MINGW32__)
#define WITH_IPOPT
#else
/* Without IPOPT for MSVC */
#endif

#include "revision.h"

#define WITH_UMFPACK

#else /* Unix */

#define DEFAULT_LDFLAGS ""

#include "config.unix.h"

#endif

#ifdef CONFIG_REVISION
#define CONFIG_VERSION CONFIG_REVISION
#else
#define CONFIG_VERSION "1.9.3-dev"
#endif


#endif
