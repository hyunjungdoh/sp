cmake_minimum_required(VERSION 3.20)
project(harness LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

add_library(harness Harness.cpp)
target_include_directories(harness PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
                           ${CMAKE_CURRENT_SOURCE_DIR}/../chain
                           ${CMAKE_CURRENT_SOURCE_DIR}/../realdef)

add_executable(harness_spec_test spec_test.cpp)
target_link_libraries(harness_spec_test PRIVATE harness)

add_executable(harness_spec spec_main.cpp)
target_link_libraries(harness_spec PRIVATE harness)
