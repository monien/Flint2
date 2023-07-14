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

remove_blank_lines()
{
    temp_file=$(mktemp)
    awk 'NF {p=1} p' $1  > "$temp_file"
    cp "$temp_file" $1
}

fix_module_comment()
{
    sed 's/^{- |/{-|/g' $1
}

change_license()
{
    sed '/BSD\-style/GNU GPL\,\ version\ 2\ or\ above/' $1
}

export -f remove_pragma
export -f remove_blank_lines
export -f fix_module_comment
export -f change_license

# find src -type f -exec bash -c 'fix_module_comment $0' {} \;
# fix_module_comment src/Data/Number/Flint/Fmpz/Poly.hs

find src -type f -exec bash -c 'change_license $0' {} \;
