/** @addtogroup fmu2
 *
 *  @{
 */
#pragma once
/*
 * Wrap a Modelica System of the Cpp runtime for FMI 2.0.
 *
 * This file is part of OpenModelica.
 *
 * Copyright (c) 1998-CurrentYear, Open Source Modelica Consortium (OSMC),
 * c/o Linköpings universitet, Department of Computer and Information Science,
 * SE-58183 Linköping, Sweden.
 *
 * All rights reserved.
 *
 * THIS PROGRAM IS PROVIDED UNDER THE TERMS OF THE BSD NEW LICENSE OR THE
 * GPL VERSION 3 LICENSE OR THE OSMC PUBLIC LICENSE (OSMC-PL) VERSION 1.2.
 * ANY USE, REPRODUCTION OR DISTRIBUTION OF THIS PROGRAM CONSTITUTES
 * RECIPIENT'S ACCEPTANCE OF THE OSMC PUBLIC LICENSE OR THE GPL VERSION 3,
 * ACCORDING TO RECIPIENTS CHOICE.
 *
 * The OpenModelica software and the OSMC (Open Source Modelica Consortium)
 * Public License (OSMC-PL) are obtained from OSMC, either from the above
 * address, from the URLs: http://www.openmodelica.org or
 * http://www.ida.liu.se/projects/OpenModelica, and in the OpenModelica
 * distribution. GNU version 3 is obtained from:
 * http://www.gnu.org/copyleft/gpl.html. The New BSD License is obtained from:
 * http://www.opensource.org/licenses/BSD-3-Clause.
 *
 * This program is distributed WITHOUT ANY WARRANTY; without even the implied
 * warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE, EXCEPT AS
 * EXPRESSLY SET FORTH IN THE BY RECIPIENT SELECTED SUBSIDIARY LICENSE
 * CONDITIONS OF OSMC-PL.
 *
 */

#include <iostream>
#include <string>
#include <vector>
#include <assert.h>

#include "fmi2Functions.h"
#include "FMU2GlobalSettings.h"

// define logger as macro that passes through variadic args
#define FMU2_LOG(w, status, category, ...) \
  if ((w)->logCategories & (1 << (category))) \
    (w)->logger((w)->componentEnvironment, (w)->instanceName, \
                status, (w)->LogCategoryFMUName(category), __VA_ARGS__)

enum LogCategoryFMU {
  logEvents = 0,
  logSingularLinearSystems,
  logNonlinearSystems,
  logDynamicStateSelection,
  logStatusWarning,
  logStatusDiscard,
  logStatusError,
  logStatusFatal,
  logStatusPending,
  logFmi2Call
};

class FMU2Wrapper
{
 public:
  // Creation and destruction of FMU instances and setting logging status
  FMU2Wrapper(fmi2String instanceName, fmi2String GUID,
              const fmi2CallbackFunctions *functions, fmi2Boolean loggingOn);
  virtual ~FMU2Wrapper();

  // Debug logging
  virtual fmi2Status setDebugLogging(fmi2Boolean loggingOn,
                                     size_t nCategories,
                                     const fmi2String categories[]);
  const unsigned int &logCategories;
  const fmi2CallbackLogger &logger;
  const fmi2ComponentEnvironment &componentEnvironment;
  const fmi2String &instanceName;
  static fmi2String LogCategoryFMUName(LogCategoryFMU);

  // Enter and exit initialization mode, terminate and reset
  virtual fmi2Status setupExperiment(fmi2Boolean toleranceDefined,
                                     fmi2Real tolerance,
                                     fmi2Real startTime,
                                     fmi2Boolean stopTimeDefined,
                                     fmi2Real stopTime);
  virtual fmi2Status enterInitializationMode();
  virtual fmi2Status exitInitializationMode();
  virtual fmi2Status terminate      ();
  virtual fmi2Status reset          ();

  // Getting and setting variable values
  virtual fmi2Status getReal   (const fmi2ValueReference vr[], size_t nvr,
                                fmi2Real    value[]);
  virtual fmi2Status getInteger(const fmi2ValueReference vr[], size_t nvr,
                                fmi2Integer value[]);
  virtual fmi2Status getBoolean(const fmi2ValueReference vr[], size_t nvr,
                                fmi2Boolean value[]);
  virtual fmi2Status getString (const fmi2ValueReference vr[], size_t nvr,
                                fmi2String  value[]);
  virtual fmi2Status getClock  (const fmi2Integer clockIndex[],
                                size_t nClockIndex, fmi2Boolean active[]);
  virtual fmi2Status getInterval(const fmi2Integer clockIndex[],
                                 size_t nClockIndex, fmi2Real interval[]);

  virtual fmi2Status setReal   (const fmi2ValueReference vr[], size_t nvr,
                                const fmi2Real    value[]);
  virtual fmi2Status setInteger(const fmi2ValueReference vr[], size_t nvr,
                                const fmi2Integer value[]);
  virtual fmi2Status setBoolean(const fmi2ValueReference vr[], size_t nvr,
                                const fmi2Boolean value[]);
  virtual fmi2Status setString (const fmi2ValueReference vr[], size_t nvr,
                                const fmi2String  value[]);
  virtual fmi2Status setClock  (const fmi2Integer clockIndex[],
                                size_t nClockIndex, const fmi2Boolean active[]);
  virtual fmi2Status setInterval(const fmi2Integer clockIndex[],
                                 size_t nClockIndex, const fmi2Real interval[]);

  // Enter and exit the different modes for Model Exchange
  virtual fmi2Status newDiscreteStates      (fmi2EventInfo *eventInfo);
  virtual fmi2Status completedIntegratorStep(fmi2Boolean noSetFMUStatePriorToCurrentPoint,
                                             fmi2Boolean *enterEventMode,
                                             fmi2Boolean *terminateSimulation);

  // Providing independent variables and re-initialization of caching
  virtual fmi2Status setTime                (fmi2Real time);
  virtual fmi2Status setContinuousStates    (const fmi2Real x[], size_t nx);

  // Evaluation of the model equations
  virtual fmi2Status getDerivatives     (fmi2Real derivatives[], size_t nx);
  virtual fmi2Status getEventIndicators (fmi2Real eventIndicators[], size_t ni);
  virtual fmi2Status getContinuousStates(fmi2Real states[], size_t nx);
  virtual fmi2Status getNominalsOfContinuousStates(fmi2Real x_nominal[], size_t nx);

 private:
  FMU2GlobalSettings _global_settings;
  MODEL_CLASS *_model;
  std::vector<string> _string_buffer;
  bool *_clock_buffer;
  int _nclock_active;
  double _need_update;
  void updateModel();

  typedef enum {
    Instantiated       = 1 << 0,
    InitializationMode = 1 << 1,
    EventMode          = 1 << 2,
    ContinuousTimeMode = 1 << 3,
    Terminated         = 1 << 4,
    Error              = 1 << 5,
    Fatal              = 1 << 6
  } ModelState;

  unsigned int _logCategories;
  fmi2String _instanceName;
  fmi2String _GUID;
  fmi2CallbackFunctions _functions;
  ModelState _state;
};
/** @} */ // end of fmu2
