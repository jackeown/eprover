cmake_minimum_required(VERSION 3.0 FATAL_ERROR)
project(idk_man)

find_package(Torch REQUIRED)

add_library(NNetInterface STATIC NNetInterface.cpp)
target_link_libraries(NNetInterface "${TORCH_LIBRARIES}")
set_property(TARGET NNetInterface PROPERTY POSITION_INDEPENDENT_CODE ON)
