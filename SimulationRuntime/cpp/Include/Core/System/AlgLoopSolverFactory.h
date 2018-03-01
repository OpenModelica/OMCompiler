#pragma once
/** @addtogroup coreSystem
 *
 *  @{
 */
/*****************************************************************************/
/**
Factory used by the system to create a solver for the solution of a (possibly
non-linear) system of the Form F(x)=0.
*/

#include <SimCoreFactory/Policies/FactoryPolicy.h>
class AlgLoopSolverFactory : public IAlgLoopSolverFactory, public NonLinSolverPolicy, public LinSolverPolicy
{
public:
  AlgLoopSolverFactory(IGlobalSettings* gloabl_settings, PATH library_path, PATH modelicasystem_path);
  virtual ~AlgLoopSolverFactory();

  /// Creates a solver according to given system of equations of type algebraic loop
  virtual shared_ptr<ILinearAlgLoopSolver> createLinearAlgLoopSolver();
  virtual shared_ptr<INonLinearAlgLoopSolver> createNonLinearAlgLoopSolver();
private:
  //std::vector<shared_ptr<IKinsolSettings> > _algsolversettings;
  std::vector<shared_ptr<INonLinSolverSettings> > _algsolversettings;
  std::vector<shared_ptr<ILinSolverSettings> > _linalgsolversettings;
  std::vector<shared_ptr<ILinearAlgLoopSolver> > _linear_algsolvers;
  std::vector<shared_ptr<INonLinearAlgLoopSolver> > _non_linear_algsolvers;
  IGlobalSettings* _global_settings;
};
/** @} */ // end of coreSystem
