#!/bin/bash

mkdir -p ../test_out

TESTS=(store jump stack correct)
FLAGS=(store store1 jump jump1 jump2 push pop call targets alloff)

for t in ${TESTS[*]};
do
    for f in ${FLAGS[*]};
    do    
	echo "Run $t $f"
	./run_injection_test $t $f > ../test_out/${t}_${f}_`date +"%b%d_%H_%M_%S"`
    done
done 
