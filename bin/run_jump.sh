#!/bin/bash

#!/bin/bash

mkdir -p ../test_out

TESTS=(jump)
FRECV=(undef def spec)
FLAGS=(jump jump1 jump2)

for t in ${TESTS[*]};
do
    for f in ${FRECV[*]};
    do    
	for fl in ${FLAGS[*]};
	do
		echo "Run $t $f ${fl}"
		./run_test $t $f ${fl} > ../test_out/${t}_${f}_${fl}`date +"%b%d_%H_%M_%S"`
	done
    done
done 
