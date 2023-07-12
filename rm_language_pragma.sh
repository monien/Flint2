#!/bin/sh

remove_pragma()
{
    temp_file=$(mktemp)
    awk '
    /{-# language/{p=1}
    !p
    /#-}/{p=0}
    ' $1 > "$temp_file"
    cp "$temp_file" $1
}

export -f remove_pragma

find src -type f -exec bash -c 'remove_pragma $0' {} \;

# remove_pragma src/Data/Number/Flint/Fmpz/Poly/FFI.hsc
