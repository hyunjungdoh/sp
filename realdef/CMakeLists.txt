cmake_minimum_required(VERSION 3.20)
project(realdef LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(LLVM REQUIRED CONFIG)
message(STATUS "LLVM ${LLVM_PACKAGE_VERSION} at ${LLVM_DIR}")

add_library(realdef STATIC RealDef.cpp)
target_include_directories(realdef PUBLIC ${CMAKE_CURRENT_SOURCE_DIR} ${LLVM_INCLUDE_DIRS})
target_compile_definitions(realdef PUBLIC ${LLVM_DEFINITIONS})
llvm_map_components_to_libnames(REALDEF_LLVM support core irreader passes analysis transformutils)
target_link_libraries(realdef PUBLIC ${REALDEF_LLVM})
if(NOT LLVM_ENABLE_RTTI)
  target_compile_options(realdef PRIVATE -fno-rtti)
endif()

add_executable(realdef-bin main.cpp)
target_link_libraries(realdef-bin PRIVATE realdef)
if(NOT LLVM_ENABLE_RTTI)
  target_compile_options(realdef-bin PRIVATE -fno-rtti)
endif()
set_target_properties(realdef-bin PROPERTIES OUTPUT_NAME realdef)
