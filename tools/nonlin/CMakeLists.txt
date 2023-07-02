add_executable (maxpranq NonlinSolver.cpp)
target_link_libraries (maxpranq ${Z3_LIBRARY} ${Boost_SYSTEM_LIBRARY} ${GMPXX_LIB} ${GMP_LIB} Threads::Threads)
install(TARGETS maxpranq RUNTIME DESTINATION bin)
