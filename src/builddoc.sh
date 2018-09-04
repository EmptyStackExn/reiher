#!/bin/sh
ISABELLE=/Applications/Isabelle2018.app/Contents/Resources/Isabelle2018
ISABIN=$ISABELLE/bin/isabelle
env ISABELLE_HOME=$ISABELLE $ISABIN build -v -D .
