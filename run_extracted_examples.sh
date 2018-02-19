#!/bin/bash

EXAMPLES_DIR=Source/Examples
EXTRACTION_DIR=/tmp

SOURCE_PREFIX="run_source_"
INTERMEDIATE_PREFIX="run_intermediate_compiled_"
TARGET_PREFIX="run_target_compiled_"

if (( $# == 1 )); then
    if [[ $1 = "--force-extraction" ]]; then
        echo "*** Forcing extraction ***"
        touch $EXAMPLES_DIR/*.v
        make
    fi
fi

# run source examples
echo "*** Running examples at the source level ***"
for example in $EXTRACTION_DIR/$SOURCE_PREFIX*.ml; do
    # prepend big int import to each example
    echo -e "#load \"nums.cma\";;open Big_int;;\n$(cat $example)" > $example
    # run the example
    echo "Output of $example:"
    ocaml $example
done

# run compiled examples at the intermediate level
echo "*** Examples compiled at the intermediate level ***"
for example in $EXTRACTION_DIR/$INTERMEDIATE_PREFIX*.ml; do
    # prepend big int import to each example
    echo -e "#load \"nums.cma\";;open Big_int;;\n$(cat $example)" > $example
    echo "Output of $example:"
    ocaml $example
done

# run sources compiled to target
echo "*** Examples compiled at the target level ***"
for example in $EXTRACTION_DIR/$TARGET_PREFIX*.ml; do
    # prepend big int import to each example
    echo -e "#load \"nums.cma\";;open Big_int;;\n$(cat $example)" > $example
    echo "Output of $example:"
    ocaml $example
done
