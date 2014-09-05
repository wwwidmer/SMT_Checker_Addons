#! /bin/bash

# 1 add to iter line 81 - done
add_to_iter () {
iter=$2
iterline=$(awk "/define\(\`ITER/ { print NR;}" $1)
distline=$(awk "/define\(\`DIST/ { print NR;}" $1)
sed -i "$iterline s/[[:digit:]]\+/$iter/" $1
sed -i "$distline s/;;define/define/" $1
sed -i "$distline s/define/;;define/" $1
}

# 2 remove - done
clean () {
rm foo.smt2
rm components
rm connections
rm bar
}

# 3 create connections - done
create_connections () {
iter=$2
m4 -I /usr/share/m4/examples $1 > foo.smt2
cvc4 foo.smt2 > connections
cat components connections > bar

# graph and assert scripts 
./synth.out bar graph_out$iter
./synth_graph.pl bar graph_imgout$iter
./synth_assert.pl connections assert_out$iter 119
}

# 7 edit foo.m4 to add wff from 5s out
oracle_assertions () {
iter=$2
addwff=$(awk "/ADDWFF/ { print NR;}" $1)
sysnum=1
while [ $sysnum -lt 9 ]
do
read -p "Enter sysout for sysin= "$sysnum": " temp
sysout="(sysinxh-"$sysnum" (_ bv"$temp" 5))"
echo $sysout >> oracle$iter
((sysnum++))
done
# format 
./synth_assert.pl oracle$iter assert_oracle$iter 120
line=$(head -1 assert_oracle$iter)
sed -i "$addwff i $line" $1
}





main () {

iter=1
check_for_satisfied=""true
# always keep a backup
if [ -e $1 ]
then
cp $1 $1_b
fi

while [ $check_for_satisfied == true ]
do

# 1 add to iter line 81 - done
add_to_iter $1 $iter

# 2 remove - done
clean

# 3 create connections - done
create_connections $1 $iter 

# 4 uncomment DIST macro repeat - done
sed -i "$distline s/;;define/define/" $1

# 5 - timing - done
{ time cvc4 foo.smt2 ; } 2>time.log$iter
cvc4 foo.smt2 > connections
./synth_assert.pl connections assert_out$iter 32

# 6 check for unsat - done??
if grep -q "unsat" connections; then
echo "UNSAT detected"
check_for_satisfied=""false
fi

# 7 edit foo.m4 to add wff from 5s out
oracle_assertions $1 $iter

# 8 goto 1 - done
((iter++))

done

}


#call main
main $1