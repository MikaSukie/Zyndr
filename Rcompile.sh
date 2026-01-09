#!/bin/bash
clear
  ./Zyndr test.zy -o out.ll &&
  opt -O2 out.ll -o out.opt.ll &&
  clang -O2 -Wno-override-module out.opt.ll -o main &&
time bash -c '  ./main
  echo "Exit code: $?"
'