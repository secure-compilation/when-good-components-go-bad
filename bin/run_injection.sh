#!/bin/bash

#!/bin/bash

mkdir -p ../test_out

export RAND_SEED=$RANDOM

TESTS=(jump stack store)
FRECV=(spec undef def)
FLAGS=(store store1 store2 jump jump1 jump2 push pop call targets)

for i in `seq 1 600`;
do
    export RAND_SEED=$RANDOM
    echo "Seed=$RAND_SEED"

    for f in ${FRECV[*]};
    do
        for fl in ${FLAGS[*]};
        do
		for t in ${TESTS[*]};
		do
		    echo "Run $t $f ${fl}"
		    ./run_test $t $f ${fl} > ../test_out/${t}_${f}_${fl}`date +"%b%d_%H_%M_%S"`
		done
	done
    done
done
