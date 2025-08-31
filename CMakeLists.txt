###############################################################
# Cmake file for testing frama-c WP plugin
###############################################################
cmake_minimum_required(VERSION 3.15)
project(frama_c_test VERSION 0.1
                  DESCRIPTION "Testing Frama-c WP plugin"
                  LANGUAGES C)


## Set ENV Variables
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)

## Project Variables
set(SRC_FILES 
    ${CMAKE_SOURCE_DIR}/src/main.c 
    ${CMAKE_SOURCE_DIR}/src/pid.c
    ${CMAKE_SOURCE_DIR}/src/filter.c
    )
set(
    INCLUDE_DIR 
    ${CMAKE_SOURCE_DIR}/include
    )
set(
    COMPILE_COMMANDS_JSON_PATH
    ${CMAKE_SOURCE_DIR}/build/compile_commands.json
)

## Main Compilation
add_executable(main ${SRC_FILES})
target_include_directories(main PUBLIC ${INCLUDE_DIR})

## Verification Command
# If it fails you may need to init OPAM again: 
# opam init && eval $(opam env)
add_custom_target(
    verify
    COMMAND frama-c-gui -json-compilation-database ${COMPILE_COMMANDS_JSON_PATH} ${SRC_FILES} -wp -wp-prover z3,alt-ergo
    COMMENT "Running Frama-C wp and rte plugins on all files built"
    )

add_custom_target(
    verify_cli
    COMMAND frama-c -json-compilation-database ${COMPILE_COMMANDS_JSON_PATH} ${SRC_FILES} -wp -wp-timeout 30 -wp-model real -wp-prover alt-ergo,z3,cvc5 
    COMMENT "Running Frama-C wp and rte plugins on all files built"
    )