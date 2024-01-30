cmake_minimum_required(VERSION 3.25)
project(tam41_cs31920_assignment C)

set(CMAKE_C_STANDARD 23)

add_executable(tam41_cs31920_assignment rounding.c)
target_link_libraries(tam41_cs31920_assignment glpk)

