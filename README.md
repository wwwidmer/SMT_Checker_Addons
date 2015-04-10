==================
SMT_Checker_Addons
==================

A collection of scripts to take output from an SMT checker and make analysis friendly.
(http://en.wikipedia.org/wiki/Satisfiability_Modulo_Theories)

Auto SMT
	Generates the connections and components for the bottom scripts, calls them iteratively until the circuit is 'satisfied' or deemed 'unsatisfiable'. Takes an m4 file as input and outputs many Graphs and Assertion text files.
	

Graphing
	Generates a graph in the DOT format using the GraphViz2 perl module. (Regex based)

Assertion
	Generates a series of assertions from connections and components. (Regex based) 

==================
Running
==================

PREREQS:
--------
The following must be done for the bash script to work. Exclusive of these cause all sorts of error. (if there is no ; ADDWFF your file will turn into a 20k line mess)

Add these lines to your .m4 file - somewhere near the top.
     define(`ITER', 1)     
     define(`DIST',`')
  

Add this line to your .m4 file where you want the oracle components to be.
    ; ADDWFF


Determine the number of bits which will need to be padded in the oracle and Edit L54 in the .sh script. (Number mod 2 = padding, as in 4 = 2 bits of padding, 6 = 3 bits of padding, 8 = 3 bits of padding, etc...)
L54 looks like:
<< ./synth_assert.pl oracle$iter assert_oracle$iter 15 >>
and will turn:
<< sysninxh-2 (_ bv1 4)) >>
into
<< (assert(and(= sysinxh-2 #b0001) ... ))>>

Oracle lines will begin with "sysin" at the moment. IE the script looks for "sysin" and determines those lines are holding oracle components. 

--------
./auto_smt.sh m4file
all changes to the file happen at m4file_b.

==================
Outputs
==================



==================
MAKEFILE
==================
- Limited functionality for now

make clean
	Removes all temporary files (components, foo, bar, sed files)
	Removes all output files from previous run (.png, .dot, assert_out, time log)

make sort
     moves all S and A files into folders. (Synthesis and Alt-inputs)

- Todo -
rebuild synth.out with a clean

==================
FILES
==================
auto_smt.sh input [m4_file]
	See below (RUN)

synth_graph.pl input output
	Source for executable below. (Edit this and run "pp -o synth_graph.pl synth_graph.out")

synth_graph.out
	Above perl script in executable form (Binaries for most linux)

synth_assert.pl input output numvars
	Perl script for assertion production. 


=================
TODO
=================
Check for Oracle nodes better. 


=================
ISSUES
=================

-- That out-1 in-1 bug.
-- Graph takes synthesis values and alternate distinguishing input values so the graphs are incorrect for DIST enabled part of the iteration.