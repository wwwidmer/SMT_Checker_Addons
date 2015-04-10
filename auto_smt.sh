#! /bin/bash
# TODO
# srcdir
# specify oracle values
# iteration check


srcdir=$HOME/src/synthesis

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
rm -f foo*
rm -f components*
rm -f connections*
rm -f bar*
}

# 3 create connections - done
create_connections () {
iter=$2

m4 -I /usr/share/m4/examples $1 > foo_s$iter.smt2
echo "cvc working..."
(time cvc4 foo.smt2 > connections_s$iter) 2>time.logs$iter

cat components connections_s$iter > bar_s$iter

# graph and assert scripts 
./synth.out bar_s$iter graph_out-s$iter
#./synth_graph.pl bar_s graph_imgout-s$iter
./synth_assert.pl connections_s$iter assert_out-s$iter 119
}
# 7 edit foo.m4 to add wff from 5s out
# not very good looking at the moment, just getting the idea down to make it work
oracle_assertions () {
iter=$2
next=$2

((next++))

addwff=$(awk "/ADDWFF/ { print NR;}" $1)
lines=$(awk "/sysin*/ { print NR;}" connections_d$iter)
sed -n $lines'p' connections_d$iter >> oracle$iter

echo "sysout-"$next" for inputs "
more oracle$iter
read -p "Enter sysout-"$next": " so

./synth_assert.pl oracle$iter assert_oracle$iter 15
sed -i 's/)))/)/g' assert_oracle$iter
echo "(= sysout-"$next" #b"$so")))" >> assert_oracle$iter
line=$(head -1 assert_oracle$iter)
sed -i "$addwff i $line" $1


}


 ############ ############ ############
#  main to call all functions #
 ############ ############ ############

main () {

iter=1
check_for_satisfied=""true

make clean

while [ $check_for_satisfied == true ]
do

echo "----------------------ITERATION $iter---------------------------------"
# 1 add to iter line 81 - done
add_to_iter $1 $iter

# 2 remove old - done
clean
# 3 create connections - done
create_connections $1 $iter 
cp foo.smt2 foo_s$iter.smt2
# 4 uncomment DIST macro repeat - done
sed -i "$distline s/;;define/define/" $1
# 5 - timing - done
clean
m4 -I /usr/share/m4/examples $1 > foo.smt2
{ time cvc4 foo.smt2 > connections_d$iter ; } 2>time.logd$iter
cp foo.smt2 foo_d$iter.smt2
cat components connections_d$iter > bar_d$iter
./synth.out bar_d$iter graph_out-a$iter
#./synth_graph.pl bar_d graph_imgout-d$iter
./synth_assert.pl connections_d$iter assert_out-d$iter 255

# 6 check for unsat - done??
if grep -q "unsat" connections_d$iter; then
echo "UNSAT detected"
check_for_satisfied=""false
break
fi


# 7 edit foo.m4 to add wff from 5s out
oracle_assertions $1 $iter
echo "Is this correct? ITER:$iter \n"
more assert_oracle$iter

'
read -p "Redo iteration?(y or n)\n" cor
if cor = y
then
# Redo without changing iter, remove all $iter items
rm -f *$iter
else
# 8 goto 1 - done
((iter++))
fi
'
((iter++))
done
}

#call main

if [ -e $1 ]
then
backup=$1"_b"
cp $1 $backup
fi
#backup our M4 file -> to ensure we have an original copy
main $backup
