#pragma once
/** @addtogroup simcorefactoriesPolicies
 *
 *  @{
 */
#include <SimCoreFactory/ObjectFactory.h>
shared_ptr<ILinSolverSettings> createUmfpackSettings();
shared_ptr<IAlgLoopSolver> createUmfpackSolver(ILinearAlgLoop* algLoop, shared_ptr<ILinSolverSettings> solver_settings);
template<class CreationPolicy>
struct StaticLinSolverOMCFactory : virtual public ObjectFactory<CreationPolicy>{

public:
  StaticLinSolverOMCFactory(PATH library_path, PATH modelicasystem_path,PATH config_path)
   :ObjectFactory<CreationPolicy>(library_path,modelicasystem_path,config_path)
    ,_last_selected_solver("empty")
   {
   }

  virtual ~StaticLinSolverOMCFactory() {};

  virtual shared_ptr<ILinSolverSettings> createLinSolverSettings(string lin_solver)
  {
     #ifdef USE_UMFPACK
      if(lin_solver.compare("umfpack")==0)
      {
           shared_ptr<ILinSolverSettings> settings = createUmfpackSettings();
           return settings;
      }
      else
     #endif
        throw ModelicaSimulationError(MODEL_FACTORY,"Selected lin solver is not available");
  }
  virtual shared_ptr<IAlgLoopSolver> createLinSolver(ILinearAlgLoop* algLoop, string solver_name, shared_ptr<ILinSolverSettings> solver_settings)
  {
      #ifdef USE_UMFPACK
       if(solver_name.compare("umfpack")==0)
       {
           shared_ptr<IAlgLoopSolver> solver =createUmfpackSolver(algLoop,solver_settings);
           return solver;
       }
       else
      #endif
          throw ModelicaSimulationError(MODEL_FACTORY,"Selected lin solver is not available");
   }

protected:
     string _last_selected_solver;
private:
    type_map _linsolver_type_map;
};
/** @} */ // end of simcorefactoriesPolicies
