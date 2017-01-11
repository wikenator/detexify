#!/usr/bin/perl

use strict;
use warnings;
use Data::Dumper;

my ($expr, $expandExpr);

$expr = <STDIN>;
chomp($expr);

$expandExpr = &expand_expr ($expr);

print $expandExpr;
exit();

sub expand_expr {
	my $expandExpr = shift; 

	$expandExpr =~ s/([abc])([uvxyz])/$1*$2/g;	# ax -> a*x
	$expandExpr =~ s/([abc])([abc[^o]])/$1*$2/g;	# ab -> a*b
	$expandExpr =~ s/(\d+)([abcuvxyz])/$1*$2/g;	# #x -> #*x
	#expandExpr = re.sub(r"\^([\w\d]+)", r"^(\1)", expandExpr)	# x^a -> x^(a)
	$expandExpr =~ s/([\w\d]+)\)([abcuvxyz])/$1)*$2/g;	# (a)x -> (a)*x
	$expandExpr =~ s/\)\s*\(/)*(/g;			# )( -> )*(
	#Df(x) = re.sub(r"\^([^ ]+)", r"^(\1)", str(Df(x)))	# x^a*b -> x^(a*b)

	return $expandExpr;
}
