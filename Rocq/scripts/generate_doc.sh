#!/bin/bash
mkdir -p doc
coqdoc --html -d doc -R _build/default/src Verilog _build/default/src/*.v
