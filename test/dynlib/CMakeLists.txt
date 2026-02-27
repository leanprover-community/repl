cmake_minimum_required(VERSION 3.15)
project(mylib C)

# Default elan base directory (adjust if your elan is elsewhere)
set(ELAN_BASE_DIR "$ENV{HOME}/.elan/toolchains")

# Try to read lean-toolchain file (simple read first line)
file(READ "${CMAKE_SOURCE_DIR}/lean-toolchain" LEAN_TOOLCHAIN_CONTENT)
string(STRIP "${LEAN_TOOLCHAIN_CONTENT}" LEAN_TOOLCHAIN_CONTENT)

# Extract version after colon, e.g. leanprover/lean4:v4.21.0  --> v4.21.0
string(REGEX MATCH "v[0-9]+\\.[0-9]+\\.[0-9]+" LEAN_VERSION "${LEAN_TOOLCHAIN_CONTENT}")

message("${LEAN_VERSION}")


set(LEAN_TOOLCHAIN_DIR "${ELAN_BASE_DIR}/leanprover--lean4---${LEAN_VERSION}")
message(STATUS "Using Lean toolchain: ${LEAN_TOOLCHAIN_DIR}")

set(LEAN_INCLUDE_DIR "${LEAN_TOOLCHAIN_DIR}/include")
set(LEAN_LIBRARY_DIR "${LEAN_TOOLCHAIN_DIR}/lib")

include_directories(${LEAN_INCLUDE_DIR})
link_directories(${LEAN_LIBRARY_DIR})

add_library(mylib SHARED mylib.c)

set_target_properties(mylib PROPERTIES
    LIBRARY_OUTPUT_DIRECTORY "${CMAKE_SOURCE_DIR}/.lake/build/lib"
)