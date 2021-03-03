#!/bin/bash

EXAMPLES_DIR=Source/Examples
EXTRACTION_DIR=/tmp

SOURCE_PREFIX="run_source_"
INTERMEDIATE_PREFIX="run_intermediate_compiled_"
MP_PREFIX="run_compiled_"
TARGET_PREFIX="run_target_compiled_"

if (( $# == 1 )); then
    if [[ $1 = "--force-extraction" ]]; then
        echo "*** Forcing extraction ***"
        touch $EXAMPLES_DIR/*.v
        make
    fi
fi

pushd $EXTRACTION_DIR/

echo "*** Examples at the source level ***"
for example in $SOURCE_PREFIX*.ml; do
    # prepend big int import to each example
    echo -e "open Big_int\n$(cat $example)" > $example
    filename=$(basename "$example")
    filename="${filename%.*}"
    echo "Compilation of $example:"
    ocamlbuild -libs nums -use-ocamlfind $filename.native
done

echo "*** Examples compiled at the intermediate level ***"
for example in $INTERMEDIATE_PREFIX*.ml; do
    # prepend big int import to each example
    echo -e "open Big_int\n$(cat $example)" > $example
    filename=$(basename "$example")
    filename="${filename%.*}"
    echo "Compilation of $example:"
    ocamlbuild -libs nums -use-ocamlfind $filename.native
done

echo "*** Examples compiled at the micro-policy level ***"
for example in $MP_PREFIX*.ml; do
    # prepend big int import to each example
    echo -e "open Big_int\n$(cat $example)" > $example
    filename=$(basename "$example")
    filename="${filename%.*}"
    echo "Compilation of $example:"
    ocamlbuild -libs nums -use-ocamlfind $filename.native
done

echo "*** Examples compiled at the SFI level ***"
for example in $TARGET_PREFIX*.ml; do
    # prepend big int import to each example
    echo -e "open Big_int\n$(cat $example)" > $example
    filename=$(basename "$example")
    filename="${filename%.*}"
    echo "Compilation of $example:"
    ocamlbuild -libs nums -use-ocamlfind $filename.native
done

popd
