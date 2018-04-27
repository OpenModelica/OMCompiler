#pragma once

#include <Core/System/ILinearAlgLoop.h>              // Interface to AlgLoo
#include <Core/System/INonLinearAlgLoop.h>              // Interface to AlgLoo
#include <Core/Solver/ILinearAlgLoopSolver.h>        // Export function from dll
#include <Core/Solver/ILinSolverSettings.h>
#include <Solver/UmfPack/UmfPackSettings.h>


class UmfPack : public ILinearAlgLoopSolver
{
public:
  UmfPack(ILinSolverSettings* settings);
  virtual ~UmfPack();

    virtual void initialize();

    /// Solution of a (non-)linear system of equations
    virtual void solve(shared_ptr<ILinearAlgLoop> algLoop,bool restart = false);

    /// Returns the status of iteration
    virtual ITERATIONSTATUS getIterationStatus();
    virtual void stepCompleted(double time);
    virtual void restoreOldValues();
    virtual void restoreNewValues();
private:
    ITERATIONSTATUS _iterationStatus;
    ILinSolverSettings *_umfpackSettings;
    ILinearAlgLoop *_algLoop;

    double * _jacd;
    double * _rhs;
    double * _x,
           *_x_old,
           *_x_new;
    bool _firstuse;
};
