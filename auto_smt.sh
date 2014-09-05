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

read -p "Enter sysout for sysinxh="$iter": " temp
sysout="(sysinxh-"$iter" (_ bv"$temp" 4))"
echo $sysout >> oracle$iter
read -p "Enter sysout for sysinxl="$iter": " temp
sysout="(sysinxl-"$iter" (_ bv"$temp" 4))"
echo $sysout >> oracle$iter
read -p "Enter sysout for sysinyh="$iter": " temp
sysout="(sysinyh-"$iter" (_ bv"$temp" 4))"
echo $sysout >> oracle$iter
read -p "Enter sysout for sysinyl="$iter": " temp
sysout="(sysinyl-"$iter" (_ bv"$temp" 4))"
echo $sysout >> oracle$iter

# format 
./synth_assert.pl oracle$iter assert_oracle$iter 15
line=$(head -1 assert_oracle$iter)
sed -i "$addwff i $line" $1
}





main () {

iter=1
check_for_satisfied=""true

while [ $check_for_satisfied == true ]
do
# keep a backup of the backup (for testing each iteration)
cp $1 $1_b


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
./synth_assert.pl connections assert_out$iter 15

# 6 check for unsat - done??
if grep -q "unsat" connections; then
echo "UNSAT detected"
check_for_satisfied=""false
break
fi

# 7 edit foo.m4 to add wff from 5s out
oracle_assertions $1 $iter

# 8 goto 1 - done
((iter++))

done

}


#call main

if [ -e $1 ]
then
backup=$1"_"$(date +%T)
cp $1 $backup
fi
#backup
main $backup
