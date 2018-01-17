#/bin/bash


#TESTS=(store jump stack)
#FRECV=(undef def spec)
TESTS=(undef def spec)
FRECV=(alloff)

echo "Generator: tests specific (jump to RA)"

for t in ${TESTS[*]};
do
    for f in ${FRECV[*]};
    do 
	for fn in `ls ${t}_${f}_*`;
	do 
		cat "${fn}" | grep -v Passed |  sed 's/:/ /g' | sed 's/,/ /g' | tr -s ' ' | cut -d' ' -f1,2,3,4,5 | sed '/^$/d' 
	done | awk -v x=$t -v y=$f 'BEGIN{print x, y} { tests+= $1; dyn+= $1*$2; static+= $1*$3; internal += $1*$4; sfi += $1*$5 } END {print tests, dyn/tests, static/tests, internal/tests, sfi/tests}'
    done
done 

STATE=(Halted OutOfFuel JumpNotAddressInReg NoInfo MissingComponentId NegativePointerOffset LoadOutsideComponent LoadNotAddressInReg StoreOutsideComponent StoreNotAddressInReg JumpOutsideComponent MissingJalLabel MissingLabel MissingBlock OffsetTooBig MemoryError StoreMemoryError NotIntInReg AllocNegativeBlockSize InvalidEnv)

for s in ${STATE[*]};
do
	for t in ${TESTS[*]};
	do
    		for f in ${FRECV[*]};
    		do 
        		for fn in `ls ${t}_${f}_*`;
        		do 
                		cat "${fn}" | grep "$s"  | grep -v Passed |  sed 's/:/ /g' | sed 's/,/ /g' | tr -s ' ' | cut -d' ' -f1,2,3,4,5 | sed '/^$/d'
		        done | awk -v x=$t -v y=$f -v z=$s 'BEGIN{print x, y, z} { tests+= $1; dyn+= $1*$2; static+= $1*$3; internal += $1*$4; sfi += $1*$5 } END {if (tests > 0 ) print tests, dyn/tests, static/tests, internal/tests, sfi/tests}'
    		done
	done
done

