#!/bin/sh

echo "argument: $1"

remove_pragma()
{
    echo "remove_pragma: argument = $1"
    # awk '/{-# language/, /#-}/' $1
    awk 'f;/{-# language/, /#-}/{f=1}' $1
}

export -f remove_pragma

find src -type f -exec bash -c 'remove_pragma $0' {} \;
