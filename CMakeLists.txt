cmake_minimum_required(VERSION 3.16)
project(selfie_bare_metal)
add_executable(selfie selfie.c)
target_compile_options(selfie PUBLIC -Wall -Wextra -O3 -m64)