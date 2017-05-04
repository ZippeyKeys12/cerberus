#!/bin/bash

source tests.sh

mkdir -p tmp
cd tmp

pass=0
fail=0

function test {
  rm -rf ${1%.c}.native
  cbuild $1 > /dev/null 2> /dev/null
  if [ "$?" -ne "0" ]; then
    echo -e "Test $1: Cerberus failed..."
    return
  fi

  if [ -e ../$2/expected/$1.expected ]; then
    CERB_BATCH=1 ./${1%.c}.native > result
    cmp --silent result ../$2/expected/$1.expected
    if [[ "$?" -eq "0" ]]; then
      res="\033[1m\033[32mPASSED!\033[0m"
      pass=$((pass+1))
    else
      res="\033[1m\033[31mFAILED!\033[0m"
      fail=$((fail+1))
    fi
    echo -e "Test $1: $res"
  else
    echo -e "Test $1: Expected file does not exist..."
  fi

}

function run_ci {
  # Running ci tests
  for file in "${citests[@]}"
  do
    test $file ci
  done

  echo "PASSED: $pass"
  echo "FAILED: $fail"
}

if [ $# -eq 0 ]; then
  cp ../ci/*.c .
  run_ci
else
  if [ "$1" == "csmith" ]; then
    cp ../csmith/small_int_arith/*.c .
    for f in csmith_*.c
    do
      echo "File: $f"
      cbuild --csmith $f > /dev/null 2> /dev/null
      if [ $? -eq 0 ]; then
        ./${f%.c}.native
      else
        echo "FAIL"
      fi
    done
  else
    cp ../suite/$1/*.c .
    for f in *.c
    do
      echo "File: $f"
      cbuild $f > /dev/null 2> /dev/null
      if [ $? -eq 0 ]; then
        ./${f%.c}.native
      else
        echo "FAIL"
      fi
    done
  fi
fi
