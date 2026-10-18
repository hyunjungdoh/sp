cmake_minimum_required(VERSION 3.20)
project(gen LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(LLVM REQUIRED CONFIG)
llvm_map_components_to_libnames(GEN_LLVM support core irreader bitwriter linker transformutils demangle)

add_executable(gen
  tools/main.cpp
  src/Loader.cpp
  src/Driver.cpp
  src/Place.cpp
  src/Emit.cpp
  src/Generator.cpp)
target_include_directories(gen PRIVATE include ${LLVM_INCLUDE_DIRS})
target_compile_definitions(gen PRIVATE ${LLVM_DEFINITIONS})
target_link_libraries(gen PRIVATE ${GEN_LLVM})
if(NOT LLVM_ENABLE_RTTI)
  target_compile_options(gen PRIVATE -fno-rtti)
endif()
