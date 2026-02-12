cmake_minimum_required(VERSION 3.16)
project(Measure LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

option(MEASURE_EXTENSIONS "Enable Measure kernel extensions" ON)

add_subdirectory(measure/src/kernel)
