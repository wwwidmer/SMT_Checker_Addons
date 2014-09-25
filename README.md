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
MAKEFILE
==================
- Limited functionality for now

make clean
	Removes all temporary files (components, foo, bar, sed files)
	Removes all output files from previous run (.png, .dot, assert_out, time log)

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

==================
RUN
==================
./auto_smt.sh m4_file

This script also cleans the folder of old Output files to avoid ambiguity. Please save your work after each successful run. 

Interactive inputs:
At end of iteration you will be prompted for a new set of connections assuming the circuit is not satisfied. This will be in the form:


=================
Outputs
=================
connections - ()
components - ()
output_graph$num - dot file, where $num is the iteration number
output_assert$num - text file, where $num is the iteration number
foo - placeholder
bar - placeholder




=================
TODO
=================
Check for Oracle nodes better. Right now we just assume they're called sysin and grab that whole line. It works for examples but may not for future files depending on names. The cvc command automatically puts these files on a seperate line but I think we should plan for the worst. (Just slighty more complicated regex checking really)