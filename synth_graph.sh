#! /bin/bash

echo "Combing COMP AND CON files"
echo "$1 is the COMPONENT and $2 is the connections" 

cat $1 $2 > $3IN

echo " $1 & $2 in $3IN"

./synth_graph.pl "$3IN" "$4OUT"