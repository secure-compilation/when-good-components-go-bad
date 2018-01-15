#/bin/bash


TESTS=(store jump stack)
#FRECV=(undef def spec)
FAULT=(store store1 store2 jump jump1 jump2 call pop push targets)

echo "Generator: tests specific (jump to RA)"

for t in ${TESTS[*]};
do
    for f in ${FAULT[*]};
    do 
	for fn in `ls ${t}_${f}_* 2> /dev/null`;
	do
		echo -n "$t $f "
		grep "*** Failed" ${fn} 2> /dev/null | cut -d' ' -f4
		grep Passed ${fn} > /dev/null
		if [[ $? -eq 0 ]] 
		then
			echo "No failure found!" 
		fi
	done
    done
done 

