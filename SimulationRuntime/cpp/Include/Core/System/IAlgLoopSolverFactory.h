#pragma once
/** @addtogroup coreSystem
 *
 *  @{
 */

/*****************************************************************************/
/**

Abstract interface class for numerical methods for the (possibly iterative)
solution of algebraic loops in open modelica.

\date     October, 1st, 2008
\author

*/
/*****************************************************************************
Copyright (c) 2008, OSMC
*****************************************************************************/

class IAlgLoopSolverFactory
{
public:
  IAlgLoopSolverFactory() {};
  virtual ~IAlgLoopSolverFactory() {};
  virtual  shared_ptr<ILinearAlgLoopSolver> createLinearAlgLoopSolver() = 0;
  virtual  shared_ptr<INonLinearAlgLoopSolver> createNonLinearAlgLoopSolver() = 0;
};
/** @} */ // end of coreSystem
