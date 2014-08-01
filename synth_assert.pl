#!/usr/bin/perl

use strict;
use warnings;
use File::Spec;

# ---------------

# ./synth_assert input output NUM*
#  Where input must exist and is a text file
#  And output may exist but is overwritten
#  And NUM* is the number of netids
#  example: ./synth_assert SMT_Connections.txt SMT_Asserts.txt 20

sub main{

# Command line validation

    if($#ARGV < 2){
	print "Please specify input and output files\n";
	terminate();
    } else{
	if(defined $ARGV[2] && defined $ARGV[1] && defined $ARGV[0]){
	    print "Input file: $ARGV[0]\nto \nOutput file: $ARGV[1] with $ARGV[2] variables\n";
	}     
    }
    read_input();
    exit;
}


sub read_input{
    my($in) = "$ARGV[0]";
    open(DATA, $in) or die "Couldn't open file ' $in '";
    my(@connections);
    while(<DATA>){
	push(@connections, $_);
    }
    print "Scanning this input for nodes and connections...\n";
    print "@connections\n";
    close DATA or die "Cannot close $in";
    create_assert(@connections);   
}


sub create_assert{
    my(@connections_info) = @_;
    my($binary_pad) = length(sprintf("%b",$ARGV[2]));
    open(my($out), '>',$ARGV[1]);
    print $out "(assert(and";
    foreach (@connections_info){	
	my(@connection) = split(('\n'), $_);	
	foreach (@connection){
	 #   print $_;
	    while($_ =~ /(\w+)-(\d+)\s+\(_\s+bv(\d+)/g){
		my($in) = $1;
		my($from) = $2;
		my($to) = sprintf("%0${binary_pad}b", $3);
		my($assert) = "(= $in-$from #b$to)";
		print $out $assert;
	    }    
	}	
    } 
    print $out "))";
    close $out;
    print "done\n"; 
    terminate();
}


sub terminate{
    die "Program terminates";
}


# Call main to limit scope
main();
