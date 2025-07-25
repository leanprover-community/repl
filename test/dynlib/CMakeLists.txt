cmake_minimum_required(VERSION 3.15)
project(mylib C)

# Put your actual path here from step 1
set(LEAN_INCLUDE_DIR "/home/codespace/.elan/toolchains/leanprover--lean4---v4.22.0-rc4/include")

include_directories(${LEAN_INCLUDE_DIR})

add_library(mylib SHARED mylib.c)
