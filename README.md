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
Add this line to your .m4 file
; ADDWFF


./auto_smt m4file



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
SRCDIR script relocation



=================
ISSUES
=================

-- That out-1 in-1 bug.