cmake_minimum_required(VERSION 2.8.9)

project(${DgesvSolverName})

add_library(${DgesvSolverName} DgesvSolver.cpp DgesvSolverSettings.cpp FactoryExport.cpp)

if(NOT BUILD_SHARED_LIBS)
  set_target_properties(${DgesvSolverName} PROPERTIES COMPILE_DEFINITIONS "RUNTIME_STATIC_LINKING;ENABLE_SUNDIALS_STATIC")
endif(NOT BUILD_SHARED_LIBS)

add_precompiled_header(${DgesvSolverName} Include/Core/Modelica.h)
target_link_libraries(${DgesvSolverName})    #C:/OpenModelica/OMCompiler/SimulationRuntime/cpp/Solver/KLU/OMCppklu_static.lib
#target_link_libraries(${DgesvSolverName} ${ExtensionUtilitiesName} ${Boost_LIBRARIES} ${SUNDIALS_LIBRARIES} ${LAPACK_LIBRARIES} ${kluName})

install(TARGETS ${DgesvSolverName} DESTINATION ${LIBINSTALLEXT})
install(FILES
  ${CMAKE_SOURCE_DIR}/Include/Solver/DgesvSolver/DgesvSolver.h
  ${CMAKE_SOURCE_DIR}/Include/Solver/DgesvSolver/FactoryExport.h
  DESTINATION include/omc/cpp/Solver/DgesvSolver)
