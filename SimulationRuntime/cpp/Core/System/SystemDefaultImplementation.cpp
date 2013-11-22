
#include "stdafx.h"
#include "FactoryExport.h"
#include <System/SystemDefaultImplementation.h>
#include <System/AlgLoopSolverFactory.h>

bool greaterTime( pair<unsigned int,double> t1, double t2)
{
   return t1.second > t2;
}

SystemDefaultImplementation::SystemDefaultImplementation(IGlobalSettings& globalSettings)
: _simTime        (0.0)
, __z        (NULL)
, __zDot       (NULL)
,_conditions(NULL)
,_time_conditions(NULL)
,_time_event_counter(NULL)
{

 

}

SystemDefaultImplementation::~SystemDefaultImplementation()
{
  if(__z) delete [] __z;
  if(__zDot) delete [] __zDot;
}
void SystemDefaultImplementation::Assert(bool cond,string msg)
{
    if(!cond)
        throw std::runtime_error(msg);
}

void SystemDefaultImplementation::Terminate(string msg)
{
    throw std::runtime_error(msg);
}

int SystemDefaultImplementation::getDimBoolean() const
{
    return _dimBoolean;
}

int SystemDefaultImplementation::getDimContinuousStates() const
{
    return _dimContinuousStates;
}

int SystemDefaultImplementation::getDimInteger() const
{
    return _dimInteger;
}

int SystemDefaultImplementation::getDimReal() const
{
    return _dimReal;
}

int SystemDefaultImplementation::getDimString() const
{
    return _dimString;
}

/// Provide number (dimension) of right hand sides (equations and/or residuals) according to the index
int SystemDefaultImplementation::getDimRHS() const
{

    return _dimRHS;
};


/// (Re-) initialize the system of equations
void SystemDefaultImplementation::initialize()
{
    _callType = IContinuous::CONTINUOUS;
    if((_dimContinuousStates) > 0)
    {
        // Initialize "extended state vector"
    if(__z) delete [] __z ; 
    if(__zDot) delete [] __zDot;

    __z = new double[_dimContinuousStates];
    __zDot = new double[_dimContinuousStates];

    memset(__z,0,(_dimContinuousStates)*sizeof(double));
    memset(__zDot,0,(_dimContinuousStates)*sizeof(double));
  }
  if(_dimZeroFunc > 0)
  {
    if(_conditions) delete [] _conditions ; 
   
    _conditions = new bool[_dimZeroFunc];
  
    memset(_conditions,false,(_dimZeroFunc)*sizeof(bool));
  
  }
  if(_dimTimeEvent > 0)
  {
    if(_time_conditions) delete [] _time_conditions ; 
    if(_time_event_counter) delete [] _time_event_counter;
    _time_conditions = new bool[_dimTimeEvent];
   
   
   _time_event_counter = new int[_dimTimeEvent];
   
   memset(_time_conditions,false,(_dimTimeEvent)*sizeof(bool));
    memset(_time_event_counter,0,(_dimTimeEvent)*sizeof(int));
  }
  
  
};


/// Set current integration time
void SystemDefaultImplementation::setTime(const double& t)
{
    _simTime = t;
};


/// getter for variables of different types
void SystemDefaultImplementation::getBoolean(bool* z)
{ 
    for(int i=0; i< _dimBoolean; ++i)
    {
      //z[i] = __z[i];
    // TODO: insert Code here
    }

};

void SystemDefaultImplementation::getReal(double* z)
{ 
    for(int i=0; i< _dimReal; ++i)
    {
      //z[i] = __z[i];
    // TODO: insert Code here
    }

};

void SystemDefaultImplementation::getInteger(int* z)
{ 
    for(int i=0; i< _dimInteger; ++i)
    {
      //z[i] = __z[i];
    // TODO: insert Code here
    }

};

void SystemDefaultImplementation::getString(string* z)
{ 
    for(int i=0; i< _dimString; ++i)
    {
      //z[i] = __z[i];
    // TODO: insert Code here
    }

};

void SystemDefaultImplementation::getContinuousStates(double* z)
{ 
    for(int i=0; i< _dimContinuousStates; ++i)
    {
        z[i] = __z[i];
    }

};





/// setter for variables of different types

void SystemDefaultImplementation::setBoolean(const bool* z)
{ 
    for(int i=0; i< _dimBoolean; ++i)
    {
      //z[i] = __z[i];
    // TODO: insert Code here
    }

};

void SystemDefaultImplementation::setInteger(const int* z)
{ 
    for(int i=0; i< _dimInteger; ++i)
    {
      //z[i] = __z[i];
    // TODO: insert Code here
    }

};

void SystemDefaultImplementation::setString(const string* z)
{ 
    for(int i=0; i< _dimString; ++i)
    {
      //z[i] = __z[i];
    // TODO: insert Code here
    }

};

void SystemDefaultImplementation::setReal(const double* z)
{ 
    for(int i=0; i< _dimReal; ++i)
    {
      //z[i] = __z[i];
    // TODO: insert Code here
    }

};

void SystemDefaultImplementation::setContinuousStates(const double* z)
{
    for(int i=0; i<_dimContinuousStates; ++i)
    {
      __z[i] = z[i];
    }

};

void SystemDefaultImplementation::setRHS(const double* f)
{
    for(int i=0; i<_dimRHS; ++i)
    {
      __zDot[i] = f[i];
    }

};


/// Provide the right hand side (according to the index)
void SystemDefaultImplementation::getRHS(double* f)
{
 
     for(int i=0; i<_dimRHS; ++i)
      f[i] = __zDot[i];

};
void  SystemDefaultImplementation::intDelay(vector<unsigned int> expr)
{
   _time_buffer.set_capacity(1024);
   unsigned int expr_id;
   BOOST_FOREACH(expr_id,expr)
   {
      buffer_type delay_buffer(1024);
     _delay_buffer[expr_id]=delay_buffer;
   }
}
void SystemDefaultImplementation::storeDelay(unsigned int expr_id,double expr_value)
{
    map<unsigned int,buffer_type>::iterator iter;
    if((iter = _delay_buffer.find(expr_id))!=_delay_buffer.end())
    {
    
        iter->second.push_back(expr_value);
    }
}
 void SystemDefaultImplementation::storeTime(double time)
 {
 
    _time_buffer.push_back(time);
  
 }
 
double SystemDefaultImplementation::delay(unsigned int expr_id,double expr_value,double delayTime, double delayMax)
{
  
  map<unsigned int,buffer_type>::iterator iter;
  //find buffer for delay expression
  if((iter = _delay_buffer.find(expr_id))!=_delay_buffer.end())
  {
      if(delayTime < 0.0)
      {
        throw std::invalid_argument("Negative delay requested");
      }
      if(_time_buffer.size()==0)
      {
        /*  This occurs in the initialization phase */
        return expr_value;
      }
      
      double ts; //difference of current time and delay time
      double tl; //last buffer entry
      double res0, res1, t0, t1;
     
      if(_simTime <=  delayTime)
      {
         res0 = iter->second[0];
         return res0;  
      }
      else //time > delay time
      {
        ts = _simTime -delayTime;
        
        tl = _time_buffer.back();
        if(ts > tl)
        {
            t0 = tl;
            res0=iter->second.back();
            t1=_simTime;
            res1=expr_value;
        }
        else
        {
         //find posion in value buffer for queried time
           buffer_type::iterator pos = find_if(_time_buffer.begin(),_time_buffer.end(),bind2nd(std::greater<double>(),ts));
          
           if(pos!=_time_buffer.end()) 
           {
                buffer_type::iterator first = _time_buffer.begin(); // first time entry
                unsigned int index = std::distance(first,pos); //found time 
                t0 = *pos;
                res0 = iter->second[index];
                if(index+ 1  == _time_buffer.size())
                    return res0;
                t1 = _time_buffer[index+1];
                res1 = iter->second[index+1];
           }
           else
                throw std::invalid_argument("time im delay buffer not found");
        }
        if(t0==ts)
         return res0;
        else if(t1==ts)
         return res1;
        else
        {
          /* linear interpolation */
          double timedif = t1 - t0;
          double dt0 = t1 - ts;
          double dt1 = ts - t0;
          double res2 = (res0 * dt0 + res1 * dt1) / timedif;
          return res2;
        }
      }
  }
  else
    throw  std::invalid_argument("invalid expression id"); 
  
  
}
 
