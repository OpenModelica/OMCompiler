#include <Core/ModelicaDefine.h>
#include <Core/Modelica.h>
#include <Core/DataExchange/FactoryExport.h>
#include <Core/Utils/extension/logger.hpp>
#include <Core/DataExchange/XmlPropertyReader.h>
#include <boost/property_tree/xml_parser.hpp>
#include <boost/property_tree/ptree.hpp>
#include <boost/lexical_cast.hpp>
#include <fstream>
#include <iostream>

XmlPropertyReader::XmlPropertyReader(IGlobalSettings *globalSettings, std::string propertyFile)
  : IPropertyReader()
  ,_globalSettings(globalSettings)
  ,_propertyFile(propertyFile)
  ,_isInitialized(false)
{
}

XmlPropertyReader::~XmlPropertyReader()
{
}

void XmlPropertyReader::readInitialValues(IContinuous& system, shared_ptr<ISimVars> sim_vars)
{
  using boost::property_tree::ptree;
  std::ifstream file;
  file.open (_propertyFile.c_str(), std::ifstream::in);
  if (file.good())
  {
    double *realVars = sim_vars->getRealVarsVector();
    int *intVars = sim_vars->getIntVarsVector();
    bool *boolVars = sim_vars->getBoolVarsVector();
    string *stringVars = sim_vars->getStringVarsVector();
    int refIdx = -1;
    boost::optional<int> refIdxOpt;
    try
    {
      ptree tree;
      read_xml(file, tree);

      ptree modelDescription = tree.get_child("ModelDescription");

      FOREACH(ptree::value_type const& vars, modelDescription.get_child("ModelVariables"))
      {
        if (vars.first == "ScalarVariable")
        {
          refIdxOpt = vars.second.get_optional<int>("<xmlattr>.valueReference");

          if (!refIdxOpt)
          {
            //boost::property_tree::xml_parser::write_xml(std::cout, vars.second);
            continue;
          }

          string name = vars.second.get<string>("<xmlattr>.name");
          boost::optional<string> descriptonOpt = vars.second.get_optional<string>("<xmlattr>.description");
          string descripton;
          if (descriptonOpt)
            descripton  = *descriptonOpt;

          if (_globalSettings->getEmitResults() != EMIT_ALL)
          {
            if (name.substr(0, 3) == "_D_")
              continue;
            std::string hideResultInfo = vars.second.get<std::string>("<xmlattr>.hideResult");
            if (hideResultInfo.compare("true") == 0)
              // Note: we don't need values of hidden variables because the code calculates them
              continue;
          }

          refIdx = *refIdxOpt;
          std::string aliasInfo = vars.second.get<std::string>("<xmlattr>.alias");
          std::string variabilityInfo = vars.second.get<std::string>("<xmlattr>.variability");
          bool isParameter = (variabilityInfo.compare("parameter") == 0);
          //If a start value is given for the alias and the referred variable, skip the alias declaration
          bool isAlias = aliasInfo.compare("alias") == 0;
          bool isNegatedAlias = aliasInfo.compare("negatedAlias") == 0;

          FOREACH(ptree::value_type const& var, vars.second.get_child(""))
          {
            if (var.first == "Real")
            {
               //If a start value is given for the alias and the referred variable, skip the alias declaration
              if (!(isAlias || isNegatedAlias))
              {
                boost::optional<double> v = var.second.get_optional<double>("<xmlattr>.start");
                double value = (v? (*v):0.0);
                LOGGER_WRITE("XMLPropertyReader: Setting real variable for " + boost::lexical_cast<std::string>(vars.second.get<std::string>("<xmlattr>.name")) + " with reference " + boost::lexical_cast<std::string>(refIdx) + " to " + boost::lexical_cast<std::string>(value) ,LC_INIT,LL_DEBUG);
                system.setRealStartValue(realVars[refIdx],value);
              }
              const double& realVar = sim_vars->getRealVar(refIdx);
              const double* realVarPtr = &realVar;
              if (isParameter)
                _realVars.addParameter(name,descripton,realVarPtr);
              else
                _realVars.addOutputVar(name,descripton,realVarPtr,isNegatedAlias);
            }
            else if (var.first == "Integer")
            {
               //If a start value is given for the alias and the referred variable, skip the alias declaration
              if (!(isAlias || isNegatedAlias))
              {
                boost::optional<int> v = var.second.get_optional<int>("<xmlattr>.start");
                int value = (v? (*v):0);
                LOGGER_WRITE("XMLPropertyReader: Setting int variable for " + boost::lexical_cast<std::string>(vars.second.get<std::string>("<xmlattr>.name")) + " with reference " + boost::lexical_cast<std::string>(refIdx) + " to " + boost::lexical_cast<std::string>(value) ,LC_INIT,LL_DEBUG);
                system.setIntStartValue(intVars[refIdx],value);
              }
              const int& intVar = sim_vars->getIntVar(refIdx);
              const int* intVarPtr = &intVar;
              if (isParameter)
                _intVars.addParameter(name,descripton,intVarPtr);
              else
                _intVars.addOutputVar(name,descripton,intVarPtr,isNegatedAlias);
            }
            else if (var.first == "Boolean")
            {
               //If a start value is given for the alias and the referred variable, skip the alias declaration
              if (!(isAlias || isNegatedAlias))
              {
                boost::optional<bool> v = var.second.get_optional<bool>("<xmlattr>.start");
                bool value = (v? (*v):false);
                LOGGER_WRITE("XMLPropertyReader: Setting bool variable for " + boost::lexical_cast<std::string>(vars.second.get<std::string>("<xmlattr>.name")) + " with reference " + boost::lexical_cast<std::string>(refIdx) + " to " + boost::lexical_cast<std::string>(value) ,LC_INIT,LL_DEBUG);
                system.setBoolStartValue(boolVars[refIdx],value);
              }
              const bool& boolVar = sim_vars->getBoolVar(refIdx);
              const bool* boolVarPtr = &boolVar;
              if (isParameter)
                _boolVars.addParameter(name,descripton,boolVarPtr);
              else
                _boolVars.addOutputVar(name,descripton,boolVarPtr,isNegatedAlias);
            }
            else if (var.first == "String")
            {
               //If a start value is given for the alias and the referred variable, skip the alias declaration
              if (!(isAlias || isNegatedAlias))
              {
                boost::optional<string> v = var.second.get_optional<string>("<xmlattr>.start");
                string value = (v? (*v):"");
                LOGGER_WRITE("XMLPropertyReader: Setting string variable for " + boost::lexical_cast<std::string>(vars.second.get<std::string>("<xmlattr>.name")) + " with reference " + boost::lexical_cast<std::string>(refIdx) + " to " + boost::lexical_cast<std::string>(value) ,LC_INIT,LL_DEBUG);
                system.setStringStartValue(stringVars[refIdx],value);
              }
            }
          }
        }
      }
    }
    catch(exception &ex)
    {
      std::stringstream sstream;
      sstream << "Could not read start values. Current variable reference is " << refIdx;
      throw ModelicaSimulationError(UTILITY,sstream.str());
    }
    _isInitialized = true;
    file.close();

  }
}

const output_int_vars_t&  XmlPropertyReader::getIntOutVars()
{
  static output_int_vars_t int_none;
  if (_isInitialized)
  {
    if (_globalSettings->getEmitResults() == EMIT_NONE)
      return int_none;
    else
      return _intVars;
  }
  else
    throw ModelicaSimulationError(UTILITY, "init xml file has not been read");
}

const output_real_vars_t& XmlPropertyReader::getRealOutVars()
{
  static output_real_vars_t real_none;
  if (_isInitialized)
  {
    if (_globalSettings->getEmitResults() == EMIT_NONE)
      return real_none;
    else
      return _realVars;
  }
  else
    throw ModelicaSimulationError(UTILITY, "init xml file has not been read");
}

const output_bool_vars_t& XmlPropertyReader::getBoolOutVars()
{
  static output_bool_vars_t bool_none;
  if (_isInitialized)
  {
    if (_globalSettings->getEmitResults() == EMIT_NONE)
      return bool_none;
    else
      return _boolVars;
  }
  else
    throw ModelicaSimulationError(UTILITY, "init xml file has not been read");
}

std::string XmlPropertyReader::getPropertyFile()
{
  return _propertyFile;
}

void XmlPropertyReader::setPropertyFile(std::string file)
{
  _propertyFile = file;
}
