#!/bin/sh

cd $(dirname $0)/src
sage -python setup.py build
