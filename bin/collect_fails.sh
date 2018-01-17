#/bin/bash


TESTS=(store jump stack)
FRECV=(undef def spec)
#TESTS=(undef def spec)
FAULT=(store store1 store2 jump jump1 jump2 call pop push targets)
#FAULT=(store store1 store2)

echo "Generator: tests specific ()"

for t in ${TESTS[*]};
do
	for fr in ${FRECV[*]};
	do
		for f in ${FAULT[*]};
    		do 
		for fn in `ls ${t}_${fr}_${f}* 2> /dev/null`;
		do
			echo -n "$t $fr $f "
			grep "*** Failed" ${fn} 2> /dev/null | cut -d' ' -f4
			grep Passed ${fn} > /dev/null
			if [[ $? -eq 0 ]] 
			then
				echo "No failure found!" 
			fi
		done
    	done
done
done 

