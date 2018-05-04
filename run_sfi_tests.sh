#!/bin/bash

mkdir -p ../test_out

if [ -e "sfi_safety_properties.exe" ]
then
	for i in `seq 1 600`;
	do
		echo "Run $i "
		./sfi_safety_properties.exe > ../test_out/all_${i}_`date +"%b%d_%H_%M_%S"`
	done
else
	make -f Makefile.Test
	if [ "$?" -eq "0" ]
	then
		echo "========================"
		echo "Running Tests"
		./sfi_safety_properties.exe
	fi
fi
