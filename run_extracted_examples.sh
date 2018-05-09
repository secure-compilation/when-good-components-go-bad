#!/bin/bash

EXAMPLES_DIR=Source/Examples
EXTRACTION_DIR=/tmp

SOURCE_PREFIX="run_source_"
INTERMEDIATE_PREFIX="run_intermediate_compiled_"
TARGET_PREFIX="run_target_compiled_"
MP_PREFIX="run_compiled_"

if (( $# == 1 )); then
    if [[ $1 = "--force-extraction" ]]; then
        echo "*** Forcing extraction ***"
        touch $EXAMPLES_DIR/*.v
        make
    fi
fi


cp Lib/big.ml $EXTRACTION_DIR/big.ml

pushd $EXTRACTION_DIR
ocamlc -a nums.cma big.ml -o big.cma
# ocamlc -c nums.cma Extraction/big.ml -o $EXTRACTION_DIR/big.cmo


# run source examples
echo "*** Running examples at the source level ***"
for example in $SOURCE_PREFIX*.ml; do
    # prepend big int import to each example
    echo -e "open Big_int\n$(cat $example)" > $example
    # run the example
    echo "Output of $example:"
    ocaml nums.cma big.cma $example
done

# run compiled examples at the intermediate level
echo "*** Examples compiled at the intermediate level ***"
for example in $INTERMEDIATE_PREFIX*.ml; do
    # prepend big int import to each example
    echo -e "open Big_int\n$(cat $example)" > $example
    echo "Output of $example:"
    ocaml nums.cma big.cma $example
done

# run sources compiled to target
echo "*** Examples compiled at the SFI level ***"
for example in $TARGET_PREFIX*.ml; do
    # prepend big int import to each example
    echo -e "open Big_int;;\n$(cat $example)" > $example
    echo "Output of $example:"
    ocaml nums.cma big.cma $example
done

# # run compiled examples at the micro-policy level
# echo "*** Examples compiled at the micro-policy level ***"
# for example in $MP_PREFIX*.ml; do
#     # prepend big int import to each example
#     echo -e "open Big_int\n$(cat $example)" > $example
#     echo "Output of $example:"
#     ocaml nums.cma big.cma $example
# done



popd
