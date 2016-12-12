#pragma once
/** @addtogroup solverLinearSolver
 *
 *  @{
 */

// #if defined(klu)
#include <klu.h>
// #endif

class LinearSolver : public IAlgLoopSolver
{
public:
  LinearSolver(ILinearAlgLoop* algLoop, ILinSolverSettings* settings);
  virtual ~LinearSolver();

  /// (Re-) initialize the solver
  virtual void initialize();

  /// Solution of a (non-)linear system of equations
  virtual void solve();

  /// Returns the status of iteration
  virtual ITERATIONSTATUS getIterationStatus();
  virtual void stepCompleted(double time);
  virtual void restoreOldValues();
  virtual void restoreNewValues();



private:
  // Member variables
  //---------------------------------------------------------------

  ILinearAlgLoop
    *_algLoop;            ///< Algebraic loop to be solved

  ITERATIONSTATUS
    _iterationStatus;     ///< Output   - Denotes the status of iteration

  long int
    _dimSys;              ///< Temp   - Number of unknowns (=dimension of system of equations)

  bool
    _firstCall;           ///< Temp   - Denotes the first call to the solver, init() is called

  long int *_ihelpArray,	//pivot indices for lapackroutine
	  *_jhelpArray;			//pivot indices for lapackroutine

  double
	  *_y,                  ///< Temp   - Unknowns
	  *_y0,                 ///< Temp   - Auxillary variables
      *_y_old,				//stores old solution
      *_y_new,				//stores new solution
	  *_b,                  ///< right hand side
	  *_A,				///coefficients of linear system
	  *_zeroVec,			///zero vector
	  *_scale;				//scaling parameter to prevent overflow in singular systems
  bool _sparse;
//#if defined(klu)
  int _dim;
  klu_symbolic* _kluSymbolic ;
  klu_numeric* _kluNumeric ;
  klu_common* _kluCommon ;
  int* _Ai;
  int* _Ap;
  double* _Ax;
  int _nonzeros;
//#endif

};
/** @} */ // end of solverLinearSolver
