#!/bin/bash
for input in $(ls *.cnfp); do
    echo -n "Running ${input} ... "
    minicard_result=$(./minicard_static -verb=0 ${input} 2> /dev/null | grep '^s' | awk '{ print $2 }')
    crocodile_result=$(./crocodile_static ${input} | grep 'SAT')
    if [[ ${minicard_result} != ${crocodile_result} ]]; then
      echo "non-match! crocodile: ${crocodile_result}, minicard: ${minicard_result}"
      exit
    else
      echo "match! ${crocodile_result}"
    fi
done