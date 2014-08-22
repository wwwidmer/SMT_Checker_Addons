#! /bin/bash
iter=1
satisfied=""false
cp $1 $1_b
while [ $satisfied == false ]
do

# 1 add to iter line 81 - done
iterline=$(awk "/define\(\`ITER/ { print NR;}" $1)
distline=$(awk "/define\(\`DIST/ { print NR;}" $1)
sed -i "$iterline s/[[:digit:]]\+/$iter/" $1
sed -i "$distline s/;;define/define/" $1
sed -i "$distline s/define/;;define/" $1

# 2 remove - done
rm foo.smt2
rm components
rm connections
rm bar

# 3 create connections - done
m4 -I /usr/share/m4/examples $1 > foo.smt2
cvc4 foo.smt2 > connections
cat components connections > bar
# graph and assert scripts - done
./synth.out bar graph_out$iter
./synth_assert.pl connections assert_out$iter 30
# 4 uncomment DIST macro repeat - done
sed -i "$distline s/;;define/define/" $1

# 5 - done
{ time cvc4 foo.smt2 ; } 2>time.log$iter
cvc4 foo.smt2 > connections
# 6 check for unsat - wip
if [`echo "unsat" || grep 'connections'`] then;
$satisfied = true
fi

# 7 edit foo.m4 to add wff from 5s out
addwff=$(awk "/ADDWFF/ { print NR;}" $1)
line=$(head -1 assert_out$iter)
sed -i "$addwff i $line" $1

# 8 goto 1 - done
((iter++))


done
