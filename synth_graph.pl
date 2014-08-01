#!/usr/bin/perl

use strict;
use warnings;
use Data::Dumper;
use File::Spec;
use GraphViz2;

# ---------------

sub main{
# Command line validation
    if($#ARGV != 1){
	print "Please specify input and output files\n";
	terminate();
    } else{
	if(defined $ARGV[1] && defined $ARGV[0]){
	    print "Input file: $ARGV[0]\nto \nOutput file: $ARGV[1].dot\n";
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
    create_graph(@connections);   
}

sub create_graph{
# For GraphhViz
    my(@connections_info) = @_;
    my(@nodes);
    my(@edges);
    my(%components);
    my($graph) = GraphViz2 -> new
	(
	 edge   => {color => 'black'},
	 global => {directed => 1},
	 graph  => {label => 'Connections'},
	 node   => {shape => 'component'},
	);    
      foreach (@connections_info){
	my(@connection) = split(('\n'), $_);
       	foreach (@connection){	
	    my($line) = $_;
	    #components
	    while($line =~ /^\((\w+(-\d+)*)\s+/g){
		my($comp) = $1;
		my(%com) = create_component($line);
		$components{$comp} = {%com};
		if(!(@{$com{'ins'}})){$graph -> add_node(name=>"$comp",shape=>"invtriangle");}
		elsif(!(@{$com{'outs'}})){$graph -> add_node(name=>"$comp",shape=>"triangle");}
		else{ # default node used
		    $graph -> add_node(name=>"$comp");
		}
	    }
	    #connections
	    while($line =~ /\w+-(\d+)\s+\(_\s+bv(\d+) \d+/g){
		my($out) = $2;
		my($in) = $1;
		if($out == 0){
		    next;
		}
		my($inc, $outc) = split(/ /,make_connections($in, $out, \%components));	
		$graph -> add_edge(from=>"$outc",to=>"$inc",label=>"out-$out to in-$in");
	    }     
	}
      }
    output_dot($graph);
}

sub make_connections{
    my($in) = $_[0];
    my($out) = $_[1];        
    my(%components) = %{$_[2]};    
    my($inc) = 0;
    my($outc) = 0;
    my($key);
    foreach $key(keys %components){
	my(@ins) = @{$components{$key}{'ins'}};
	my(@outs) = @{$components{$key}{'outs'}};
	foreach my $x (@ins){
	    if($x == $in){
		$inc = $key;
	    }	    
	}
	foreach my $x (@outs){
	    if($x == $out){
		$outc = $key;
	    }
	}
    }
    return "$inc $outc";  
}

sub create_component{
    my($line) = @_;
    my(@ins);
    my(@outs);
    #get the input nets
    my(@matches) = ($line =~ /in-(\d+)/g);
    foreach my $x (@matches){
	push(@ins,$x);
    }
    #get the output nets
    @matches = ($line =~ /out-(\d+)/g);
    foreach my $x (@matches){
	push(@outs,$x);
    }
    my(%comp) = (
	'ins' => [@ins],
	'outs' => [@outs],
	);
    return %comp;
}

sub output_dot{
    my($graph) = @_;    
    my($out) = "$ARGV[1]";
    my($format)      = "png";
    my($output_file) =  File::Spec -> catfile("$out.$format");
    $graph -> run(format=>$format, output_file => $output_file);
    terminate();
}


sub terminate{
    die "Program terminates";
}


# Call main to limit scope
main();
