#!/bin/bash

if [ ! -f /usr/bin/time ]; then
    echo "Please install the GNU time utility." >&2
    exit 1
fi

if [ ! -d benchmark-output ]; then
    mkdir benchmark-output
fi

pushd ../../../

for i in `seq 1 3`; do
    make clean
    echo -e "\n\ncurrent time is $( date -Iseconds )\n\n"
    # cpu model extraction from https://askubuntu.com/questions/988440/how-do-i-get-the-model-name-of-my-processor/988449#988449
    /usr/bin/time -v -o "notes/selfie-pt/scripts/benchmark-output/tree_$( lscpu | sed -nr "/Model name/ s/.*:\s*(.*) @ .*/\1/p" | sed "s/ /_/g" )_$( uname -r)_$( date -Iseconds ).txt" make all
    sed -i "s/PAGE_TABLE_TREE \+= 1/PAGE_TABLE_TREE = 0/g" selfie.c

    echo -e "\n\ncurrent time is $( date -Iseconds )\n\n"
    make clean
    # cpu model extraction from https://askubuntu.com/questions/988440/how-do-i-get-the-model-name-of-my-processor/988449#988449
    /usr/bin/time -v -o "notes/selfie-pt/scripts/benchmark-output/linear_$( lscpu | sed -nr "/Model name/ s/.*:\s*(.*) @ .*/\1/p" | sed "s/ /_/g" )_$( uname -r)_$( date -Iseconds ).txt" make all
    sed -i "s/PAGE_TABLE_TREE \+= 0/PAGE_TABLE_TREE = 1/g" selfie.c
done

popd
