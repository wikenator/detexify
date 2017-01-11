package PerlAPI;

use strict;
use warnings;
use Exporter;
use IPC::Open2;
use Data::Dumper;
use vars qw(@ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);

@ISA = qw(Exporter);
@EXPORT = ();
@EXPORT_OK = qw(preClean detex expand_expr num_compare verify injectAsterixes removeOuterParens cleanParens unbalancedCharacter condense latexplosion movePi condenseArrayExponents removeArrayBlanks);
%EXPORT_TAGS = (
        DEFAULT => [qw(&detex &expand_expr)],
        All     => [qw(&detex &expand_expr &num_compare &verify &removeArrayBlanks &condenseArrayExponents &injectAsterixes &removeOuterParens &cleanParens &unbalancedCharacter &condense &latexplosion &movePi)]
);

our @latexFunc;
{
	no warnings 'qw';
	@latexFunc = qw(sqrt sinh cosh tanh csch coth sech log ln abs sin cos tan csc sec cot #sin #cos #tan #csc #sec #cot #ln #log);
}

### Standard Data Cleaning for All Procedures #################################
sub preClean {
	my $expr = shift;

	$expr =~ s/\\[\,\!\s]/ /g;	# remove tex space (escaped , ! whitespace)
	$expr =~ s/\\\[/\$\$/g;		# remove escaped [
	$expr =~ s/\\\]/\$\$/g;		# remove escaped ]
	$expr =~ s/\\\{/\(/g;		# remove escaped {
	$expr =~ s/\\\}/\)/g;		# remove escaped }
	$expr =~ s/\\\$//g;		# remove escaped dollar signs
	$expr =~ s/[\?\$]//g;		# remove punctuation and latex delimiters
	$expr =~ s/\\%/%/g;		# remove backslashes before percent signs
	$expr =~ s/\*\*/\^/g;		# replace python ** with sage ^
	$expr =~ s/\\displaystyle//g;	# remove displaystyle tags
	$expr =~ s/[dt]frac/frac/g;	# replace \dfrac and \tfrac with \frac
	$expr =~ s/\^(-.)/\^\($1\)/g;	# replace a^-b with a^(-b)
	$expr =~ s/\\left//g;		# remove \left tags
	$expr =~ s/\\right//g;		# remove \right tags
	$expr =~ s/\\break//g;		# remove break tags
	$expr =~ s/\\q?quad//g;		# remove qquad, quad tags
	$expr =~ s/\\lbrack/\(/g;	# replace lbrack with (
	$expr =~ s/\\rbrack/\)/g;	# replace rbrack with )
	$expr =~ s/\\[lc]?dots/.../g;	# replace \dots, \ldots, \cdots with ...
	$expr =~ s/\s+/ /g;		# replace multiple spaces with 1 space
	$expr =~ s/^\s*(.*?)\s*$/$1/;	# remove leading and trailing spaces

	# remove these tags to prevent XSS attacks
	$expr =~ s/\\immediate//g;
	$expr =~ s/\\write18//g;
	$expr =~ s/\\write//g;
	
	return $expr;
}
###############################################################################

### Detexify ##################################################################
sub detex {
        my $prob = shift;
	my $match = shift;
	my $debug = shift;
	$match = 'f' if not defined $match;
	$debug = 0 if not defined $debug;
        my $detexPath = './detexify/detexify/detex.pl';
	my $cmd = "$detexPath" . ($match eq 't' ? " -m t " : "") . ($debug ? " -d " : "");

	my $detexID = open2(\*pipeRead, \*pipeWrite, "$cmd");

        print pipeWrite "$prob\n";
        close (pipeWrite);

        my $detexResult = <pipeRead>;
        close (pipeRead);

        waitpid ($detexID, 0);

        return $detexResult;
}
###############################################################################

### Clean String of Parentheses ###############################################
sub cleanParens {
	my $expr = shift;
	my $debug = shift;
	$debug = 0 if not defined $debug;
	my $cleanPath = './detexify/detexify/clean_parens.pl';
	my $cmd = "$cleanPath" . ($debug ? " -d" : "");

	my $cleanID = open2(\*pipeRead, \*pipeWrite, "$cmd");

	print pipeWrite "$expr\n";
	close(pipeWrite);
	
	my $cleanExpr = <pipeRead>;
	close(pipeRead);

	waitpid($cleanID, 0);

	return $cleanExpr;
}
###############################################################################

### Remove Blank Entries from Array ###########################################
sub removeArrayBlanks {
	my $arr = shift;
	my $debug = shift;

	# remove blank entries from subExpr array
	my $arraySize = (scalar @$arr);

	for (my $i = 0; $i < $arraySize; $i++) {
		if ($debug) { print "slice $i: " . $arr->[$i] . "\n"; }

		if ($arr->[$i] ne '0') {
			if (not($arr->[$i]) or ($arr->[$i] eq '')) {
				splice @$arr, $i, 1;
				$arraySize--;

				if ($debug) { print "----------\n"; }
			}
		}
	}

	return $arr;
}
###############################################################################

### Condense Exponents in Array ###########################################
sub condenseArrayExponents {
	my $arr = shift;
	my $debug = shift;

	# remove blank entries from subExpr array
	my $arraySize = (scalar @$arr);

	for (my $i = 0; $i < $arraySize; $i++) {
		if ($debug) { print "slice $i: " . $arr->[$i] . "\n"; }

		if ($arr->[$i] eq '/') {
			if (($arr->[$i-3] =~ /\^$/) and
			($arr->[$i-2] eq '(') and
			($arr->[$i-1] =~ /\w+/) and
			($arr->[$i+1] =~ /\w+/) and
			($arr->[$i+2] eq ')')) {
				splice @$arr, $i-3, 6, $arr->[$i-3] . $arr->[$i-2] . $arr->[$i-1] . $arr->[$i] . $arr->[$i+1] . $arr->[$i+2];
				$arraySize -= 5;
				$i -= 2;

				if ($debug) { print "----------\n"; }
			}
		}
	}

	return $arr;
}
###############################################################################

### Insert Asterixes into String to Make it Evaluateable ######################
sub injectAsterixes {
	my $expr = shift;
	my $debug = shift;

	# put hash tag before trig functions to avoid losing the function
	if ($expr =~ /[^#]a?[sct][aieos][cnst]h?[^A-Za-z]/) {
		$expr =~ s/([^#])(a?)([sct])([aieos])([cnst])(h?)/$1#$2$3$4$5$6/g;
	}

	$expr =~ s/([\w]+)\s?\((.*?)\)/$1*($2)/g;  # a(x) -> a*(x)
	# run second time for deeper nested expressions
	$expr =~ s/([\w]+)\s?\((.*?)\)/$1*($2)/g;  # a(x) -> a*(x)
	# fix for subscript
	$expr =~ s/_\*/_/g;
	$expr =~ s/([\(\{])(.*?)([\)\}])\s?(#?[\w]+)/$1$2$3*$4/g;  # (x)a -> (x)*a OR {x}a -> {x}*a
	$expr =~ s/([\)\}])([\(\{])/$1*$2/g;                       # )( -> )*(

	if ($debug) { print "before ab->a*b: $expr\n"; }

	# split expr again to avoid splitting up functions

	# \da -> \d*a
	$expr =~ s/(\d)([a-zA-Z])/$1*$2/g;
	# a\d => a*\d
	$expr =~ s/([a-zA-Z])(\d)/$1*$2/g;
	# i\d -> i*\d
	$expr =~ s/i(\d)/i*$1/g;
	# ab -> a*b
	$expr =~ s/([a-zA-Z])([a-zA-Z])/$1*$2/g;
	# n!m! -> n!*m!
	$expr =~ s/!(\d+!)/!*$1/g;
	# run second time for string of variables greater than length 3
	$expr =~ s/([a-zA-Z])([a-zA-Z])/$1*$2/g;
	# run second time for more than 2 factorials together
	$expr =~ s/!(\d+!)/!*$1/g;
	# run third time for variables in front of functions
	$expr =~ s/([a-zA-Z])(#)/$1*$2/g;
	# fix previous line's conversion of arc trig functions
	$expr =~ s/(#a\*)#([cst]\*[aeios]\*[cnst]h?)/$1$2/g;
	# fix previous conversion of pi constants
	$expr =~ s/([^#])(p\*i)/$1#$2/g;

	if ($debug) { print "during ab->a*b 1: $expr\n"; }

	# fix split for pi
	$expr =~ s/#p\*i([\+\-\*\/]?)/pi$1/g;
	$expr =~ s/pi\*$/pi/;
	# fix split for log/ln
	$expr =~ s/#(l)\*([on])\*?(g?)\*?(_\{?.+?\}?)?\*?((\^[\(\{]?\d+[\)\}]?)?)\*?\(/$1$2$3$4$5(/g;
	# fix split for ln
#       $detexExpr =~ s/#l\*n\*?(\()/ln$1/g; 
	# fix split for (arc/hyperbolic) trig 
	$expr =~ s/#(((a?)\*?))([sct])\*([aieos])\*([cnst])\*?(h?)\*?((\^[\(\{]?-?\d+[\)\}]?)?)\*?\(/$3$4$5$6$7$8(/g;
	# fix split for trig 
#       $detexExpr =~ s/#([sct])\*([aieo])\*([cnst])\*?(\^\(?\d+\)?)?\*?(\()/$1$2$3$4$5/g;
	# fix split for sqrt
	$expr =~ s/s\*q\*r\*t\*?\(/sqrt\(/g;
	# fix split for abs
	$expr =~ s/a\*b\*s\*?\(/abs\(/g;
	# fix split for emptyset
	$expr =~ s/#e\*m\*p\*t\*y\*s\*e\*t/emptyset/g;
	# fix split for infinity
	$expr =~ s/i\*n\*f/inf/g;

	if ($debug) { print "during ab->a*b 2: $expr\n"; }

	$expr = &movePi($expr, $debug);

	# replace * before log and ln
	$expr =~ s/([\w\)])(log|ln)/$1*$2/g;

	### complete trig expression handling here
#       $detexExpr =~ s/([^(sin|cos|tan|csc|cot|sec|du|dv|-|\+|\*|\/)])([^(sin|cos|tan|csc|cot|sec|du|dv|^)])/$1*$2/g;  # ab -> a*b

	if ($debug) { print "after ab->a*b: $expr\n"; }

	# remove ending periods
	$expr =~ s/\.$/""/g;

	# clean unnecessary parentheses from expression
	$expr = &cleanParens($expr, $debug);

	if ($debug) { print "after paren cleaning 1: $expr\n"; }

	if ($expr =~ /[\{\}]/g) {
		$expr =~ s/{/(/g;  # replace curly braces with parentheses
		$expr =~ s/}/)/g;  # replace curly braces with parentheses

		# clean unnecessary parentheses from expression after bracket to parenthesis conversion
		$expr = &cleanParens($expr, $debug);

		if ($debug) { print "after paren cleaning 2: $expr\n"; }
	}

	# move trig/ln exponents after the argument: sin^2(x) -> sin(x)^2
	my $m = 0;
	my $trigSize = length($expr);
	my $startChar = '';
	my $endChar = '';
	
	for (my $i = 0; $i < $trigSize-2; $i++) {
		my $subTrigExpr = substr $expr, $i, 3;

		if (grep(/\Q$subTrigExpr\E/, @latexFunc)) {
			my $powArg = '';
			$i += 3;
			my $s = $i;

			if ((substr($expr, $i, 1) eq '^') and
			((substr($expr, $i+1, 1) eq '(') or
			(substr($expr, $i+1, 1) eq '{'))) {
				if (substr($expr, $i+1, 1) eq '(') {
					$startChar = '(';
					$endChar = ')';

				} else {
					$startChar = '{';
					$endChar = '}';
				}

				$powArg .= substr($expr, $i, 2);
				$i += 2;

				while (substr($expr, $i, 1) ne $endChar) {
					$powArg .= substr($expr, $i, 1);
					$i++;
				}

				my $trigArg = '';
				$powArg .= $endChar;
				$i++;
				
				if (substr($expr, $i, 1) eq '(') {
					my $innerDelim = 1;
					$i++;

					while ($innerDelim > 0) {
						if (substr($expr, $i, 1) eq '(') { $innerDelim++; }
						elsif (substr($expr, $i, 1) eq ')') { $innerDelim--; }

						$trigArg .= substr($expr, $i, 1);
						$i++;
					}

					$trigArg = substr($trigArg, 0, length($trigArg)-1);
					$trigArg = &cleanParens($trigArg, $debug);

					$expr = substr($expr, 0, $s) . "($trigArg)" . $powArg . substr($expr, $i);
				}
			}
		}
	}
				
	$expr =~ s/(a?)(ln|log|cosh|sinh|tanh|csch|sech|coth|cos|sin|tan|csc|sec|cot)(\^\(?-?\d+\)?)(\(.*?\))/$1$2$4$3/g;
	$expr =~ s/(a?)(ln|log|cosh|sinh|tanh|csch|sech|coth|cos|sin|tan|csc|sec|cot)(\^\(?-?\d+\)?)(.)/$1$2($4)$3/g;
	$expr =~ s/(a?)(ln|log|cosh|sinh|tanh|csch|sech|coth|cos|sin|tan|csc|sec|cot)(\(.*?\))\^\((\d)\)/$1$2$3^$4/g;

	if ($debug) { print "after trig exponent move: $expr\n"; }

	# final a(x) -> a*(x)
	$expr =~ s/(\^[\w])\s?\((.*?)\)/$1*($2)/g;
	# \da -> \d*a
	$expr =~ s/(\d)([a-zA-Z])/$1*$2/g;

	return $expr;
}
###############################################################################

### Explode LaTeX String into Array ###########################################
sub latexplosion {
	my $expr = shift;
	my $debug = shift;
	my @fragment;

	my $subExpr = [split(/([{}\(\)\[\]\^\*\/_])/, $expr)];

        # splice backslashes together with corresponding latex tag
	for my $i (0 .. (scalar @$subExpr)-1) {
		if (grep(/\\/, $subExpr->[$i])) {
			@fragment = split(/(?=[\\])/, $subExpr->[$i]);
			splice (@$subExpr, $i, 1, @fragment);
		}
	}

	if ($debug) {
		print "before blank removal: ";
		print Dumper($subExpr);
	}

	$subExpr = &removeArrayBlanks($subExpr, $debug);

	if ($debug) {
		print "after blank removal: ";
		print Dumper($subExpr);
	}

	return $subExpr;
}
###############################################################################

### Move Constant Pi to Appropriate Location in Expression ####################
sub movePi {
	my $expr = shift;
	my $debug = shift;

	# replace * around pi
	$expr =~ s/([\w]\)?)pi/$1*pi/g;
	$expr =~ s/pi(\(?[\w])/pi*$1/g;
	
	if ($expr =~ /pi\*[^\^\)\+\-\/]/) {
		while ($expr =~ /pi\*[^\^\)\+\-\/]/) {
			# pi*(a)^(b) -> (a)^(b)*pi
			if ($expr =~ /pi\*(\(.*?\)\^\(.*?\)\*?)/) {
				if ($debug) { print "move pi 1: $1\n"; }
	
				$expr =~ s/(pi)\*(\(.*?\)\^\(.*?\)\*?)/$2*$1/g;
	
			# pi*(a)^{b} -> (a)^{b}*pi
			} elsif ($expr =~ /pi\*(\([^\+\-\(\)]\)\^\{.*?\})/) {
				if ($debug) { print "move pi 2: $1\n"; }
	
				$expr =~ s/(pi)\*(\(.*?\)\^\{.*?\})/$2*$1/g;
	
			# pi*a^b -> a^b*pi
			} elsif ($expr =~ /pi\*([^\+\-\(\)]+\^\{.*?\})/) {
				if ($debug) { print "move pi 3: $1\n"; }
	
				$expr =~ s/(pi)\*([^\+\-\(\)]+\^\{.*?\})/$2*$1/g;

			# pi*(a) -> (a)*pi
			} elsif ($expr =~ /pi\*(\([^\+\-\(\)]\)\*?)/) {
				if ($debug) { print "move pi 4: $1\n"; }

				$expr =~ s/(pi)\*(\(.*?\)\*?)/$2*$1/g;
	
			# pi*a -> a*pi
			} elsif ($expr =~ /pi\*([^\+\-\(\)]+\*?)/) {
				my $temp_results = $1;

				if ($debug) { print "move pi 5: $1\n"; }

				if ($temp_results =~ /\^$/) {
					$expr =~ s/(pi)\*([^\+\-\(\)]+\^\(.*?\)\*?)/$2*$1/g;

				} elsif ($temp_results =~ /(sin|cos|tan|csc|sec|cot|ln|sqrt|log)/) {
					$expr =~ s/(pi)\*(.*?\(.*?\)\*?)/$2*$1/g;

				} else {
					$expr =~ s/(pi)\*([^\+\-\(\)]+\*?)/$2*$1/g;
				}
	
			# pi can not be moved
			} else {
				last;
			}
		}

	} elsif ($expr =~ /pi\*\)/) {
		$expr =~ s/pi\*/pi/g;
	}
	
	# fix final pi if pushed to the end of a string
	$expr =~ s/pi\*$/*pi/g;
	# remove double * as a result of pi moves
	$expr =~ s/(pi)\*\*/$1\*/g;
	$expr =~ s/\*\*(pi)/\*$1/g;

	return $expr;
}
###############################################################################

### Remove Outer Parentheses ##################################################
sub removeOuterParens {
	my $outerExpr = shift;
	my $debug = shift;

	$outerExpr =~ s/^\s*(.*?)\s*$/$1/g;

	my $innerExpr = $outerExpr;

	if ($debug) { print "outer: $outerExpr\n"; }

	$innerExpr =~ s/^\((.*?)\)$/$1/;

	if ($debug) { print "inner: $innerExpr\n"; }

	if (&unbalancedCharacter($innerExpr, '(', ')', $debug) == 0) {
		return $innerExpr;

	} else {
		return $outerExpr;
	}
}
###############################################################################

### Unbalanced Character Checker ##############################################
sub unbalancedCharacter {
	my $str = shift;
	my $chrLeft = shift;
	my $chrRight = shift;
	my $debug = shift;
	my $count = 0;

	for (my $i = 0; $i < length($str); $i++) {
		if (substr($str, $i, 1) eq $chrLeft) {
			$count++;

		} elsif (substr($str, $i, 1) eq $chrRight) {
			$count--;

			# unbalanced if more right characters found
			if ($count < 0) {
				return -1;
			}
		}
	}

	# unbalanced if counts are not equal
	if ($count > 0) { return 1; }
	else { return 0; }
}
###############################################################################

### Format number by removing extraneous components ###########################
sub condense {
        my $num = shift;
	my $debug = shift;

        if ($debug) { print "before condense: $num\n"; }

        # remove all spaces and commas
        $num =~ s/[\s\,]//g;
        # 0.123 => .123
        $num =~ s/^0(\..*)$/$1/;
        # .1230 => .123
        $num =~ s/^(\-?(\d+)?\.[^0]*)0+$/$1/;
        # 1. => 1
        $num =~ s/^(\d+)\.$/$1/;

        return $num;
}
###############################################################################

1;
