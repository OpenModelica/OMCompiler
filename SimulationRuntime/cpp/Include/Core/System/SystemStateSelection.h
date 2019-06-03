#pragma once
/** @addtogroup coreSystem
 *
 *  @{
 */


#include <Core/System/IStateSelection.h>
#include <boost/shared_array.hpp>
class SystemDefaultImplementation;
class  SystemStateSelection
{
public:
  SystemStateSelection(SystemDefaultImplementation* system);
  ~SystemStateSelection();

  bool stateSelectionSet(int switchStates, int i);
  bool stateSelection(int switchStates);
  void initialize();

private:
  void setAMatrix(int* newEnable, unsigned int index);
  int comparePivot(int* oldPivot, int* newPivot, int switchStates, unsigned int index);

  SystemDefaultImplementation* _system;
  IStateSelection* _state_selection;
  IMixedSystem* _mixed_selection;
  vector<boost::shared_array<int> > _rowPivot;
  vector<boost::shared_array<int> > _colPivot;
  unsigned int _dimStateSets;
  vector<unsigned int> _dimStates;
  vector<unsigned int> _dimDummyStates;
  vector<unsigned int> _dimStateCanditates;
  bool _initialized;

};
 /** @} */ // end of coreSolver
