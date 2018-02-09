#!/bin/bash

if [ -e "sfi_safety_properties.exe" ]
then
	./sfi_safety_properties.exe
else
	make -f Makefile.Test
	if [ "$?" -eq "0" ]
	then
		echo "========================"
		echo "Running Tests"
		./sfi_safety_properties.exe
	fi
fi
