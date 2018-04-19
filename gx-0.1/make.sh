#!/bin/sh

cd $(dirname $0)

PKGNAME=$(basename "$(pwd)")

echo "Packagename $PKGNAME"

rm -R src/build

cd ..

sage -pkg "$PKGNAME"
