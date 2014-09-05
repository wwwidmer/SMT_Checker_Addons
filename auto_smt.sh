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
# not very good looking at the moment, just getting the idea down to make it work
oracle_assertions () {
iter=$2
((iter++))
addwff=$(awk "/ADDWFF/ { print NR;}" $1)

read -p "Enter sysout for sysinxh="$iter": " xh
sysoutxh="(sysinxh-"$iter" (_ bv"$xh" 4))"
echo $sysoutxh >> oracle$iter
read -p "Enter sysout for sysinxl="$iter": " xl
sysoutxl="(sysinxl-"$iter" (_ bv"$xl" 4))"
echo $sysoutxl >> oracle$iter
read -p "Enter sysout for sysinyh="$iter": " yh
sysoutyh="(sysinyh-"$iter" (_ bv"$yh" 4))"
echo $sysoutyh >> oracle$iter
read -p "Enter sysout for sysinyl="$iter": " yl
sysoutyl="(sysinyl-"$iter" (_ bv"$yl" 4))"
echo $sysoutyl >> oracle$iter

xh=$(echo "obase=2;$xh" | bc)
xl=$(echo "obase=2;$xl" | bc)
yh=$(echo "obase=2;$yh" | bc)
yl=$(echo "obase=2;$yl" | bc)

xh=$(printf "%04s\n" $xh | tr ' ' '0')
xl=$(printf "%04s\n" $xl | tr ' ' '0')
yh=$(printf "%04s\n" $yh | tr ' ' '0')
yl=$(printf "%04s\n" $yl | tr ' ' '0')

xhxl=2#$(echo $xh$xl)
yhyl=2#$(echo $yh$yl)

echo "(sysout-"$iter" (_ bv"$(($xhxl+$yhyl))" 8))" 
read -p "Assume these are correct and press ENTER (error checking next version!)"


# format 
concat=$(($xhxl+$yhyl))
concat=$(echo "obase=2;$concat" | bc)
concat=$(printf "%08s\n" $concat | tr ' ' '0')

./synth_assert.pl oracle$iter assert_oracle$iter 15
sed -i 's/)))/)/g' assert_oracle$iter
echo "(= sysout-"$iter" #b"$concat")))" >> assert_oracle$iter
read -p "Assume these are correct and press ENTER (error checking next version!)"
line=$(head -1 assert_oracle$iter)
sed -i "$addwff i $line" $1

}


 ############ ############ ############
#  main to call all functions #
 ############ ############ ############

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
backup=$1"_b"$(date +%T)
cp $1 $backup
fi
#backup
main $backup
