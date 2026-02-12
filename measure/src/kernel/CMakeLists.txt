add_library(measure_kernel STATIC
    approx_eq.cpp
    rigor_propagation.cpp
    measure_metadata.cpp
    theory_module.cpp
    epsilon_tracker.cpp
    is_approx_eq.cpp
    theory_graph.cpp
    conservation.cpp
)

target_include_directories(measure_kernel PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/..
)

if(MEASURE_EXTENSIONS)
    target_compile_definitions(measure_kernel PUBLIC MEASURE_EXTENSIONS)
endif()
