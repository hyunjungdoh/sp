cmake_minimum_required(VERSION 3.20)
project(chain LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(LLVM REQUIRED CONFIG)
llvm_map_components_to_libnames(CHOP_LLVM support core irreader demangle passes analysis transformutils)

add_executable(chop main.cpp Chop.cpp)
add_executable(entry entry_main.cpp Entry.cpp Chop.cpp Points.cpp)
foreach(tgt chop entry)
  target_include_directories(${tgt} PRIVATE ${LLVM_INCLUDE_DIRS})
  target_compile_definitions(${tgt} PRIVATE ${LLVM_DEFINITIONS})
  target_link_libraries(${tgt} PRIVATE ${CHOP_LLVM})
  if(NOT LLVM_ENABLE_RTTI)
    target_compile_options(${tgt} PRIVATE -fno-rtti)
  endif()
endforeach()
