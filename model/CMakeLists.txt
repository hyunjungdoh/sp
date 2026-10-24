cmake_minimum_required(VERSION 3.20)
project(model LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(LLVM REQUIRED CONFIG)
llvm_map_components_to_libnames(MODEL_LLVM support core irreader bitwriter linker demangle)

add_executable(model
  src/Model.cpp
  src/Index.cpp
  src/Locate.cpp
  src/Solve.cpp
  src/Emit.cpp
  src/Origin.cpp
  src/Client.cpp
  src/Source.cpp
)
target_include_directories(model PRIVATE ${LLVM_INCLUDE_DIRS})
target_compile_definitions(model PRIVATE ${LLVM_DEFINITIONS})
target_link_libraries(model PRIVATE ${MODEL_LLVM})
if(NOT LLVM_ENABLE_RTTI)
  target_compile_options(model PRIVATE -fno-rtti)
endif()
