#!/usr/bin/perl

# Author: Arnold Wikey
# Creation Date: November 1, 2012
# Description: Front end script to detex.

use lib ('./detexify');

use strict;
use warnings;
use Getopt::Long qw(GetOptions);
Getopt::Long::Configure qw(gnu_getopt);
use Detex qw(detex);

my $debug = 0;
my $match = 'f';

GetOptions(
	'debug|d' => \$debug,
	'match|m=s' => \$match
) or die "Usage: $0 [--debug | -d] [--match=<f | t> | -m <f | t>]\n";

my $latexExpr = <STDIN>;
chomp($latexExpr);

#my @entries = split(/@#@/, $latexExpr);

#$latexExpr = $entries[0];

#if ($entries[1]) {
#	$match = substr $entries[1], 0, 1;
#}

my $coord = 0;
my $detexExpr = '';

if ($latexExpr =~ /^\([^\(\)\,]+?(\,[^\(\)\,]+?)+\)$/) {
	$coord = 1;
}

$detexExpr = &detex($latexExpr, $match, $debug);

if ($coord and ($detexExpr !~ /^\(.*?\)$/)) { $detexExpr = "($detexExpr)"; }

# split latex expression on commas
# (this assumes input is a list of items)
#my @latexExprParts = split(/,/, $latexExpr);

#foreach my $i (0 .. (scalar @latexExprParts)-1) {
#	$latexExprParts[$i] = &detex($latexExprParts[$i], $match, $debug);
#}

# join comma separated list again
#$detexExpr = join(',', @latexExprParts);

print $detexExpr;
exit();
