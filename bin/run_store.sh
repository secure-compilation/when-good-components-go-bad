#!/bin/bash

mkdir -p ../test_out

TESTS=(undef def spec)
FLAGS=(store store1 store2 alloff)

for t in ${TESTS[*]};
do
    for f in ${FLAGS[*]};
    do    
	echo "Run $t $f"
	./run_store_test $t $f > ../test_out/${t}_${f}_`date +"%b%d_%H_%M_%S"`
    done
done 
