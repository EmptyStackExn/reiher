#!/bin/sh
YEAR=2018
ISABELLE=/Applications/Isabelle${YEAR}.app/Contents/Resources/Isabelle${YEAR}
ISABIN=${ISABELLE}/bin/isabelle
env ISABELLE_HOME=$ISABELLE $ISABIN build -v -D .
