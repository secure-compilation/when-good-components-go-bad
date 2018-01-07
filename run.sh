#!/bin/bash

mkdir -p test_out

TESTS=(store jump stack correct)
FRECV=(undef def spec)

for t in ${TESTS[*]};
do
    for f in ${FRECV[*]};
    do    
	echo "Run $t $f"
	./run_test $t $f > test_out/${t}_${f}_`date +"%b%d_%H_%M_%S"`
    done
done 
