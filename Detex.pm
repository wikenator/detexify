package Detex;

# Author: Arnold Wikey
# Creation Date: December 18, 2013
# Description: Module containing all detex procedures for removing latex tags from a given string.

### tags for tracking detex changes
###
### tag: KEEP{}
###	3.3.15: method for avoiding over-saturation of parentheses in expressions

use strict;
use warnings;
use PerlAPI qw(preClean unbalancedCharacter injectAsterixes latexplosion);
use Exporter;
use Data::Dumper;
use vars qw(@ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);

@ISA = qw(Exporter);
@EXPORT = ();
@EXPORT_OK = qw(detex);
%EXPORT_TAGS = (
	DEFAULT => [qw(&detex)],
	All     => [qw(&detex &detexify &collapse)]
);

our ($debug, $match);
our $firstPass = 1;
my $infinite = 0;
my $maxIter = 40;
my @latexSplit = qw(\{ \} \[ \] \^);

my @latexTag;
{
	no warnings 'qw';
	@latexTag = qw(\\frac \\sqrt \\sinh \\cosh \\tanh \\csch \\coth \\sech \\sin \\cos \\tan \\csc \\cot \\sec \\pi \\log \\ln sqrt pi log ln abs #sin #cos #tan #sec #csc #cot #ln #log);
}

my $search_items = join("|", @latexSplit);
my $search_terms = join("|", @latexTag);
$search_terms =~ s/\\/\\\\/g;

### Detex: remove latex tags from expressions #################################
sub detex {
	my $latexExpr = shift;
	our $match = shift;
	our $debug = shift;
	my $fragment = '';

	$latexExpr = &preClean($latexExpr);

	if ($latexExpr !~ /\d+\s\d+\/\d+/) {
		$latexExpr =~ s/\s+//g; 		# remove all spaces

	} else {
		$latexExpr =~ s/(\d+)\s(\d+\/\d+)/$1+$2/g;
	}

	$latexExpr =~ s/\$\\\\\$//g;		# remove newline between latex tags
	$latexExpr =~ s/^(.*?):(.*?)$/($1)\/($2)/g;	# replace : (ratio) with / (division)
	$latexExpr =~ s/^(.*?):(.*?)$/$1)\/($2/g;	# replace : (ratio) with / (division)

	if ($debug) { print STDERR "even tags start: $latexExpr\n"; }

	# make sure tags are even
	if (&unbalancedCharacter($latexExpr, '(', ')', $debug) != 0) {
		return 0;

	} elsif (&unbalancedCharacter($latexExpr, '{', '}', $debug) != 0) {
		return 0;

	} elsif (&unbalancedCharacter($latexExpr, '[', ']', $debug) != 0) {
		return 0;
	}

	if ($debug) { print STDERR "even tags end: $latexExpr\n"; }

	$latexExpr =~ s/(\-)?\\infty/$1inf/g;	# replace \infty with inf
	$latexExpr =~ s/([^\d])(\.\d+)/${1}0$2/g;# replace .# with 0.#
	$latexExpr =~ s/^\.(.*?)$/0.$1/g;	# replace leading .# with 0.#
	$latexExpr =~ s/\^\(([\d\w\*]+)\)/^{$1}/g;	# a^b -> a^(b)
	$latexExpr =~ s/\^([\d\w])/^{$1}/g;	# a^b -> a^(b)
	$latexExpr =~ s/\\cdot/*/g;		# replace \cdot tags with *
	$latexExpr =~ s/\\times/*/g;		# replace \times tags with *
	
	my $dbl_check = 2;

	# handle \div tags to make sure 'denominators' are parenthesized correctly
	while ($dbl_check) {
		if ($latexExpr =~ /\\div\(/) {
			$latexExpr =~ s/\\div\(/\/\(/g;

		} elsif ($latexExpr =~ /\\div\\frac/) {
			my $subString = '';
			my $brack_count = 1;
			my $i = (index $latexExpr, "\\div\\frac") + 4;
			my $j = $i + 6;
			my $numer = 1;

			while ($brack_count > 0) {
				if (substr($latexExpr, $j, 1) eq "{") { $brack_count++; }
				elsif (substr($latexExpr, $j, 1) eq "}") { $brack_count--; }

				if ($brack_count > 0) {
					$j++;

				} elsif ($numer == 1) {
					$numer = 0;
					$j += 2;
					$brack_count++;

				} else {	
					last;
				}
			}

			$subString = quotemeta(substr $latexExpr, $i, $j-$i+1);
			$latexExpr =~ s/\\div($subString)/\/($1)/g;

		} elsif ($latexExpr =~ /\\div([\w\(\)\{\}\^]+)\*/) {
			$latexExpr =~ s#\\div([\w\(\)\{\}\^]+)\*#/($1)*#g;

		} elsif ($latexExpr =~ /\)\\div/) {
			$latexExpr =~ s/\)\\div/\)\//g;
		}

		$latexExpr =~ s#([^\+\-]+)\\div([^\+\-]+)#$1/($2)#g; # a \div b -> (a)/(b)

		$dbl_check--;
	}

	$latexExpr =~ s/\^\{\\circ\}//g;	# remove degree symbols
#	$latexExpr =~ s/\(/{/g;			# replace ( with {
#	$latexExpr =~ s/\)/}/g;			# replace ) with }
	$latexExpr =~ s/\|(.*?)\|/abs($1)/g;	# replace | with abs tag
	$latexExpr =~ s/\\?pi/#pi/g;		# escape pi tag

	if ($latexExpr =~ /log[^A-Za-z]/) {
		$latexExpr =~ s/\\?log/#log/g;	# escape log tag
	}

	$latexExpr =~ s/\\?ln/#ln/g;		# escape ln tag
	$latexExpr =~ s/\\emptyset/#emptyset/g;	# escape emptyset tag
	$latexExpr =~ s/\\operatorname\{(.*?)\}/$1/g;	# remove operatorname

	if ($latexExpr =~ /\\?((a)(rc)?)?(cos|sin|tan|csc|sec|cot)(h)?[^A-Za-z]/) {
		$latexExpr =~ s/\\?(((a)(rc)?)?)(cos|sin|tan|csc|sec|cot)/#$1$5$6/g;# escape atrig tag
	}

	$latexExpr =~ s/#arc(cos|sin|tan|csc|sec|cot)/#a$1$2/g;
	$latexExpr =~ s/\\?sqrt/\\sqrt/g;	# escape sqrt tag
	$latexExpr =~ s/exp/e\^/g;		# replace exp function with e

	if ($debug) { print STDERR "ready: $latexExpr\n"; }

	my $strPos = 0;
	my @fragment;
	my ($detexExpr, $latexChar);

	if (length($latexExpr) >= 4) {
		my $subExpr = &latexplosion($latexExpr, $debug);

		# detexify and collapse subExpr array
		while ((scalar @$subExpr) > 3) {
			&detexify($subExpr);
			&collapse($subExpr);

			# quit if detex does not finish before 50 iterations
			if (++$infinite > $maxIter) { return $subExpr->[0]; }
		
			if ($debug) { print STDERR Dumper($subExpr); }
		}

		# collapse remaining 2 or 3 subexpression entries
		if ((scalar @$subExpr) == 3) {
			$fragment = $subExpr->[0] . $subExpr->[1] . $subExpr->[2];
			splice @$subExpr, 0, 3, $fragment;

		} elsif ((scalar @$subExpr) == 2) {
			$fragment = $subExpr->[0] . $subExpr->[1];
			splice @$subExpr, 0, 2, $fragment;
		}

		if ($debug) { print STDERR "\nFinal Detex\n"; }
	
		# final detexify
		$detexExpr = &detexify($subExpr);
		&collapse([$detexExpr]);

		$detexExpr =~ s/\\//g;	# remove backslashes
	
		### avoid removing {} for now
		### tag: KEEP{}
		#$detexExpr =~ s/{/(/g;	# replace curly braces with parentheses
		#$detexExpr =~ s/}/)/g;	# replace curly braces with parentheses
		if ($detexExpr =~ /[^_\^]\{.*?\}/) {
			$detexExpr =~ s/([^_\^])\{(.*?)\}/$1($2)/g;
		}

		# replace -1 exponent with arc equivalent
		$detexExpr =~ s/(cosh|sinh|tanh|csch|sech|coth|cos|sin|tan|csc|sec|cot)\^[\(\{]{1,2}-1[\)\}]{1,2}/a$1/g;

		# remove *1 and 1*
		$detexExpr =~ s/[^\w\(]1\*//g;
		$detexExpr =~ s/\*1[^\w\)]//g;

	} else {
		$detexExpr = $latexExpr;
	}

	$detexExpr = &injectAsterixes($detexExpr, $debug);

	# final paren removal for negative numbers
	$detexExpr =~ s/((?<!\^)(?<!sqrt))\((-\w+)\)([^\^])/$1$2$3/g;
	$detexExpr =~ s/^\((-\w+)\)([^\^])/$1$2/;

	if ($debug) { print STDERR "iterations used: $infinite\n"; }

	return $detexExpr;
}
###############################################################################

### Detexify: remove latex tags and expand expressions ########################
sub detexify {
	my $latexExpr = shift;
	our $firstPass;
	my ($latexChar, $innerExpr, $innerDetex, $numer, $denom);
	my $i = 0;
	my $j = 0;
	my $brack_count = 0;
	my $delim_count = 0;
	my $subExpr;
	my $subString;
	my $initialString = $latexExpr;

	if ($debug) {
		print STDERR "Entering detexify: ";
		print STDERR Dumper($latexExpr);
	}

	if ($firstPass) {
		$firstPass = 0;

		if (((scalar @$latexExpr) == 1) and ($latexExpr->[$i] =~ /($search_terms)/)) {
			$initialString = $latexExpr->[0];
			$latexExpr = &latexplosion(@$latexExpr, $debug);
		}

	} else {
		return join('', @$latexExpr);
	}

	while ($i < (scalar @$latexExpr)) {
		$latexChar = $latexExpr->[$i];

		if ($debug) { print STDERR "latexChar detex: $latexChar\n"; }

		if ($latexChar eq '\frac') {
			if ($debug) { print STDERR "frac section\n"; }

			my ($numer, $denom, $n1, $n2, $d1, $d2);
			$subString = '';
			$brack_count = 1;
			$j = $i+2;
			$n1 = $j;

			while ($brack_count > 0) {
				if ($latexExpr->[$j] eq "{") { $brack_count++; }
				elsif ($latexExpr->[$j] eq "}") { $brack_count--; }

				if ($brack_count > 0) { $subString .= $latexExpr->[$j]; }
				else { last; }
				
				$j++;
			}

			$firstPass = 1;
			$numer = &detexify([$subString]);
			
			if ($debug) { print STDERR "\nnumer: $numer\n"; }

			$n2 = $j;
			$j += 2;
			$d1 = $j;
			$brack_count = 1;
			$subString = '';

			while ($brack_count > 0) {
				if ($latexExpr->[$j] eq "{") { $brack_count++; }
				elsif ($latexExpr->[$j] eq "}") { $brack_count--; }

				if ($brack_count > 0) { $subString .= $latexExpr->[$j]; }
				else { last; }
			
				$j++;
			}

			$firstPass = 1;
			$denom = &detexify([$subString]);

			if ($debug) { print STDERR "\ndenom: $denom\n"; }

			$d2 = $j;
			splice @$latexExpr, $d1, $d2-$d1, $denom;
			splice @$latexExpr, $n1, $n2-$n1, $numer;

			if ($debug) { print STDERR Dumper($latexExpr); }

			&collapse($latexExpr);

		} elsif ($latexChar =~ /^($search_terms)$/) {
			if ($debug) { print STDERR "other latex tag\n"; }

			my ($tag_arg, $left_delim, $right_delim);
			my $offset = 0;
			my $sqrt_section = 0;
			$subString = '';
			$delim_count = 0;
			$j = $i+2;

			if ($latexChar eq '\sqrt') {
				if ($debug) { print STDERR "sqrt section\n"; }

				$sqrt_section = 1;

				if ($latexExpr->[$i+1] eq '[') {
					while ($latexExpr->[$i+1] ne ']') { $i++; }

					$left_delim = '{';
					$right_delim = '}';
					$i++;
					$j = $i+2;
					$i -= 2;
					$offset = 4;
				
				} else {
					if ($latexExpr->[$i+1] eq '_') {
						$i++;
						
						if ($latexExpr->[$i+1] eq '{') {
							while (1) {
								if ($latexExpr->[$i+1] eq '}') { last; }
								else { $i++; }
							}

						} else {
							$i++;
						}
					}

					$left_delim = $latexExpr->[$i+1];

					if ($left_delim eq '(') { $right_delim = ')'; }
					else { $right_delim = '}'; }

					$i++;
					$j = $i+1;
					$offset = 1;

					if ($latexExpr->[$i+1] eq $left_delim) { $delim_count++; }
				}

				$delim_count++;

			} elsif ($latexExpr->[$i+1] and
			($latexExpr->[$i+1] eq '^') and 
			($latexExpr->[$i+2] eq '{')) {
				$left_delim = '{';
				$right_delim = '}';
				
				$i += 2;
				$j = $i + 1;
				
				$offset = 1;
				$delim_count = 1;

			} else {
				if ($debug) { print STDERR "paren delimiters\n"; }

				$left_delim = '(';
				$right_delim = ')';

				# make sure substring is not denominator
				if ((($latexExpr->[$i+2] and 
				($latexExpr->[$i+2] eq '(') and
				($latexExpr->[$i+1] ne '/'))) or
				($latexExpr->[$i+1] eq '(')) {
					$delim_count = 1;
					$i += 2;

				} else {
					$subString = $latexExpr->[$i];
				}
			}

			my $k = $j;
			
			if ($delim_count > 0) {
				while ($delim_count > 0) {
					if (($latexExpr->[$k] eq $left_delim) and ($j != $k)) { $delim_count++; }
					elsif ($latexExpr->[$k] eq $right_delim) { $delim_count--; }

					if ($delim_count > 0) {
						$subString .= $latexExpr->[$k];

					} elsif (($delim_count == 0) and
#					($latexExpr->[$k-1] ne $right_delim) and
#					($latexExpr->[$k] eq $right_delim) and
#					($subString =~ /^\Q$left_delim\E/) and
					(($subString =~ tr/\(//)+1 == ($subString =~ tr/\)//))) {
						$subString .= $latexExpr->[$k];
						$k++;
						last;
					
					} else { last; }

					$k++;

					# quit if detexify does not finish before 50 iterations
					if (++$infinite > $maxIter) {
						if ($debug) { print STDERR "stuck in delim hell\n"; }

						return $latexExpr->[0];
					}
				}

				if ($debug) { print STDERR "substring: $subString\n"; }

				$firstPass = 1;
				$tag_arg = &detexify([$subString]);

				$tag_arg =~ s/\{/\(/g;
				$tag_arg =~ s/\}/\)/g;

				if ($debug) { print STDERR "\ntag arg: $tag_arg\n"; }

			} else {
				$tag_arg = $subString;
				$k = --$j;
			}

			if ($sqrt_section and 
			($left_delim eq '(')) {
				$latexExpr->[$k] = '}';

				if ($k-$j > 1) {
					if ($debug) { print STDERR "IDX -- i: $i $latexExpr->[$i], j: $j $latexExpr->[$j], k: $k $latexExpr->[$k]\n"; }

					$latexExpr->[$i] = '{';
					$j++;

					if ($debug) { print STDERR "IDX -- size: " . ($j-$i-$offset) . ", i: $i $latexExpr->[$i], j: $j $latexExpr->[$j], k: $k $latexExpr->[$k]\n"; }

					splice @$latexExpr, $i+$offset, $k-$i-$offset, $tag_arg;

				} else {
					$latexExpr->[$i+$offset-1] = '{';
					$j++;
	
					if ($debug) { print STDERR "IDX 2 -- size: " . ($j-$i-$offset) . ", i: $i $latexExpr->[$i], j: $j $latexExpr->[$j], k: $k $latexExpr->[$k]\n"; }

					splice @$latexExpr, $i+$offset, $j-$i-$offset, $tag_arg;
				}

			} else {
				splice @$latexExpr, $i+$offset, $k-$i-$offset, $tag_arg;
			}

			&collapse($latexExpr);

			if ($debug) { print STDERR "after match check: $latexExpr->[$i]\n"; }
		}
			
		$i++;

#		if (not(grep(/\Q$latexChar\E/, @latexTag))) {
#			# \ln{a} -> \ln(a)
#			$latexExpr->[$i] =~ s#\\*ln\\*{(.*?)\\*}#ln($1)#g;
#		}

		# quit if detexify does not finish before 50 iterations
		if (++$infinite > $maxIter) { return $latexExpr->[0]; }
	}

	# collapse remaining 2 or 3 subexpression entries
	if ((scalar @$latexExpr) == 3) {
		splice @$latexExpr, 0, 3, ($latexExpr->[0] . $latexExpr->[1] . $latexExpr->[2]);

	} elsif ((scalar @$latexExpr) == 2) {
		splice @$latexExpr, 0, 2, ($latexExpr->[0] . $latexExpr->[1]);
	}

	if ($latexExpr->[0] eq $initialString) {
		return $latexExpr->[0];

	} elsif ((scalar @$latexExpr) == 1) {
		return $latexExpr->[0];

	} else {
		&detexify($latexExpr);
	}
}
###############################################################################

### Collapse: collapse latex expression array #################################
sub collapse {
	my $latexExpr = shift;
	my (@collapseExpr, @latexChar);
	my ($latexChar1, $latexChar2, $latexChar3, $latexChar4);
	my $i = 0;
	my $j;
	my $fragment = '';

	if ($debug) {
		print STDERR "Collapsing\n";
		print STDERR Dumper($latexExpr);
	}

	while ($i < (scalar @$latexExpr)-1) {
		$latexChar1 = $latexExpr->[$i];
		$latexChar2 = $latexExpr->[$i+1];
		$latexChar3 = $latexExpr->[$i+2];
		$latexChar4 = $latexExpr->[$i+3];

		if ($debug) {
			print STDERR Dumper($latexExpr);
			print STDERR "char1: $latexChar1\tchar2: $latexChar2\n";
			
			if ($latexChar2 !~ /^($search_terms)$/) { print STDERR "not a tag\n"; }
			else { print STDERR "it's a tag\n"; }
		}
				
		if (($latexChar2 eq '\sqrt') and
		($latexChar3 eq '(') and
		(($latexExpr->[$i+4] eq ')') or
		($latexExpr->[$i+5] eq ')'))) {
			$latexExpr->[$i+2] = '{';

			if ($latexExpr->[$i+4] eq ')') {
				$latexExpr->[$i+4] = '}';

			} elsif ($latexExpr->[$i+5] eq ')') {
				$latexExpr->[$i+5] = '}';
				$fragment = $latexChar4 . $latexExpr->[$i+4];
				splice @$latexExpr, $i+3, 2, $fragment;

				$i = -1;
			}
		}

		# add addition sign into mixed fractions
		if (($latexChar2 eq '\frac') and
		($latexChar1 =~ /\d*\.?\d+$/)) {
			if (($latexChar2 =~ /\\frac\{\d*\.?\d+\}\{\d*\.?\d+\}/) or
			($latexChar2 =~ /^\\frac/)) {
				$latexExpr->[$i] = $latexChar1 . '+';

			# otherwise add multiplication sign to scalar multiple
			} else {
				$latexExpr->[$i] = $latexChar1 . '*';
			}

			if ($debug) { print STDERR "mixed fractions: $latexExpr->[$i]\n"; }

			$latexChar1 = $latexExpr->[$i];
		}

		if (($latexChar1 =~ /($search_terms)(\^\(?[\w\d]+\)?)?/) and
		($latexChar2 eq '(') and
		($latexChar4 eq ')')) {
			if ($debug) { print STDERR "function with simple arg\n"; }

			$fragment = $latexChar1 . '(' . $latexChar3 . ')';
			splice @$latexExpr, $i, 4, $fragment;

			$i = -1;

		} elsif (($latexChar1 =~ /^($search_terms)$/) and
		($latexChar2 =~ /^\^/) and
		($latexChar3 eq '(') and
		$latexExpr->[$i+4] and
		($latexExpr->[$i+4] eq ')')) {
			if ($debug) { print STDERR "power of a function\n"; }

			$fragment = $latexChar1 . $latexChar2 . "($latexChar4)";
			splice @$latexExpr, $i, 5, $fragment;

			$i = -1;

		} elsif (($latexChar1 =~ /^($search_terms)$/) and
		($latexChar2 =~ /^\^\d$/)) {
			if ($debug) { print STDERR "function power\n"; }

			$fragment = $latexChar1 . $latexChar2;
			splice @$latexExpr, $i, 2, $fragment;
			
			$i = -1;

		} elsif (($latexChar1 !~ /^($search_terms)$/) and
		($latexChar1 !~ /^($search_items)$/) and
		(($latexChar2 eq '+') or 
		($latexChar2 eq '-')) and
		($latexChar3 !~ /^($search_terms)$/)) {
			$fragment = $latexChar1 . $latexChar2 . $latexChar3;

			if ($debug) { print STDERR "combining additive items: $fragment\n"; }

			splice @$latexExpr, $i, 3, $fragment;
			
			$i = -1;

		} elsif (($latexChar2 eq '{') and
		($latexChar4 eq '}')) {
			if ($debug) { print STDERR "part two\n"; }

			if ($latexChar1 eq '\sqrt') {
				# create '\sqrt{a}' fragment
				if ($match eq 'f') {
					$latexChar3 = &injectAsterixes($latexChar3, $debug);

					$latexChar3 = "($latexChar3)";

					if ($latexChar3 =~ /^\(([\w\^]+)\)$/) { $latexChar3 = $1; }

					# \sqrt{a} -> (a)^(1/2)
					$fragment = $latexChar3 . '^(1/2)';

				} else {
					$fragment = $latexChar1 . $latexChar2 . $latexChar3 . $latexChar4;
				}

				if ($debug) { print STDERR "sqrt frag: $fragment\n"; }

				splice @$latexExpr, $i, 4, $fragment;
				$i = -1;

			} elsif ($latexChar1 eq '^') {
				# create '^{a}', '[]', or '()' fragment
				if (length($latexChar3) == 1) {
					$fragment = $latexChar1 . $latexChar3;

				} else {
					$fragment = $latexChar1 . $latexChar2 . $latexChar3 . $latexChar4;
				}

				$fragment =~ s/^\\+(.*)$/$1/;
				
				if ($debug) { print STDERR "bracket frag: $fragment\n"; }

				$fragment = &detexify([$fragment]);

				splice @$latexExpr, $i, 4, $fragment;
				$i = -1;

			} elsif (($latexChar1 eq '\frac') and 
			($latexExpr->[$i+4] eq "{") and
			($latexExpr->[$i+6] eq "}")) {
				# create '\frac{a}{b}' fragment
				#$fragment = &detexify([$latexChar1 . $latexChar2 . $latexChar3 . $latexChar4 . $latexExpr->[$i+4] . $latexExpr->[$i+5] . $latexExpr->[$i+6]]);

				$fragment = '(' . $latexChar3 . ')/(' . $latexExpr->[$i+5] . ')';

				if ($debug) { print STDERR "frac frag: $fragment\n"; }

				splice @$latexExpr, $i, 7, $fragment;
				$i = -1;

			} elsif (($latexChar1 !~ /^($search_terms)$/) and
			($latexChar1 !~ /^($search_items)$/)) {
				# create '#()' fragment
				$fragment = &detexify([$latexChar1 . "{" . $latexChar3 . "}"]);
	
				if ($debug) { print STDERR "#() frag: $fragment\n"; }

				splice @$latexExpr, $i, 4, $fragment;
				$i = -1;

			} elsif (($latexChar2 eq '{') and
			($latexChar4 eq '}') and
			($latexChar1 ne '\frac')) {
				# create '()' fragment
				$fragment = &detexify(["(" . $latexChar3 . ")"]);

				if ($debug) { print STDERR "() frag: $fragment\n"; }

				splice @$latexExpr, $i+1, 3, $fragment;
				$i = -1; 
			}

		} elsif (($latexChar1 eq '\sqrt') and
		($latexChar2 eq "[") and
		($latexChar4 eq "]") and
		($latexExpr->[$i+4] eq "{")) {
			if ($debug) { print STDERR "part three\n"; }

			my $inner_arg = $latexExpr->[$i+5];
			my $delims = 1;
			my $k = $i+6;

			while ($delims > 0) {
				if ($latexExpr->[$k] eq '{') { $delims++; }
				elsif ($latexExpr->[$k] eq '}') { $delims--; }

				if ($delims > 0) {
					$inner_arg .= $latexExpr->[$k];
					$k++;
				}
			}

			$inner_arg = &detexify([$inner_arg], $debug);

			if ($debug) { print STDERR "inner arg: $inner_arg\n"; }

			splice @$latexExpr, $i+5, $k-$i-5, $inner_arg;

			if ($debug) { print STDERR Dumper($latexExpr); }

			# simplify square root function to exponent
#			if ($match eq 'f') {
			$latexExpr->[$i+5] = &injectAsterixes($latexExpr->[$i+5], $debug);

			$latexExpr->[$i+5] = "($latexExpr->[$i+5])";

			if ($latexExpr->[$i+5] =~ /^\(([\w\^]+)\)$/) { $latexExpr->[$i+5] = $1; }

			# \sqrt[a]{b} -> (b)^(1/a)
			$fragment = $latexExpr->[$i+5] . '^(1/' . $latexChar3 . ')';

#			} else {
				# create '\sqrt[a]{b}' fragment
#				$fragment = &detexify([$latexChar1 . $latexChar2 . $latexChar3 . $latexChar4 . $latexExpr->[$i+4] . $latexExpr->[$i+5] . $latexExpr->[$i+6]]);
#			}

			if ($debug) {
				print STDERR "sqrt[] frag: $fragment\n";
				print STDERR "after match check: $latexExpr->[$i]\n";
			}

			splice @$latexExpr, $i, 7, $fragment;
			$i = -1;

		} elsif (($latexChar1 eq '{') and
		($latexChar3 eq '}') and
		$latexChar4 and
		$latexExpr->[$i+5]) {
			if (($latexChar4 ne '{') and 
			($latexExpr->[$i+5] ne '}')) { 
				# create '()' fragment
				$fragment = &detexify(["($latexChar2)"]);
				
				if ($debug) { print STDERR "() frag: $fragment\n"; }

				splice (@$latexExpr, $i, 3, $fragment);
				$i = -1;
			}

		} elsif (($latexChar1 eq '^') and
		($latexChar2 !~ /^($search_terms)$/) and
		($latexChar2 !~ /^($search_items)$/) and
		($latexExpr->[$i-1] !~ /^($search_terms)$/)) {
			# create '^a' fragment
			if ($latexChar2 ne '(') {
				$fragment = &detexify([$latexChar1 . "(" . $latexChar2 . ")"]);
			
				if ($debug) { print STDERR "^a fragment: $fragment\n"; }

				splice (@$latexExpr, $i, 2, $fragment);

			} elsif (($latexChar2 eq '(') and
			$latexChar4 and
			($latexChar4 eq ')')) {
				$fragment = &detexify([$latexChar1 . $latexChar2 . $latexChar3 . $latexChar4]);

				if ($debug) { print STDERR "^(a) fragment: $fragment\n"; }

				splice (@$latexExpr, $i, 4, $fragment);
			}

		} elsif ($latexChar2 =~ /^\^[\{\(].*[\)\}]/) {
			$latexChar2 =~ s/\{/(/;
			$latexChar2 =~ s/\}/)/;

			#create 'a^b' fragment
			$fragment = &detexify([$latexChar1 . $latexChar2]);

			if ($debug) { print STDERR "a^b frag: $fragment\n"; }

			splice @$latexExpr, $i, 2, $fragment;
			$i = -1;

		} elsif (($latexChar1 eq '^') and
		($latexChar2 =~ /\(.*\)/)) {
			# create ^a fragment
			$fragment = &detexify([$latexChar1 . $latexChar2]);

			if ($debug) { print STDERR "split a^b frag: $fragment\n"; }
			
			splice @$latexExpr, $i, 2, $fragment;
			$i = -1;

		} elsif (($latexChar1 eq '{') and
		($latexChar3 eq '}') and
		$latexChar4 and
		($latexChar4 ne '}')) {
			# create a^b fragment
			$fragment = &detexify([$latexChar1 . $latexChar2 . $latexChar3 . $latexChar4]);
			
			if ($debug) { print STDERR "{a}^b frag: $fragment\n"; }

			splice @$latexExpr, $i, 4, $fragment;
			$i = -1;
		
		} elsif (($latexChar1 eq '{') and
		$latexChar4 and
		($latexChar4 eq '}')) {
			if ($debug) { print STDERR "a, b => ab: $fragment\n"; }

			# "{, a, b, }" => "{a*b}"
			if (($latexChar2 =~ /\d$/) and
			($latexChar3 =~ /^\d/)) {
				$fragment = &detexify([$latexChar2 . '*' . $latexChar3]);

			# "{, a, b, }" => "{ab}"
			} else {
				$fragment = &detexify([$latexChar2 . $latexChar3]);
			}

			splice @$latexExpr, $i+1, 2, $fragment;
			$i = -1;

		} elsif (($latexChar1 eq '[') and
		($latexChar3 eq ']')) {
			$fragment = "($latexChar2)";

			if ($debug) { print STDERR "[] => (): $fragment\n"; }

			splice @$latexExpr, $i, 3, $fragment;
			$i = -1;

		} elsif (not(($latexChar1 =~ /^($search_items)$/) or
		($latexChar2 =~ /^($search_terms)$/) or
		($latexChar1 =~ /^($search_terms)$/) or
		($latexChar2 =~ /^($search_items)$/)) and
		not($latexChar1 eq '(') and
		not($latexChar2 eq ')')) {
			if (($latexChar1 =~ /\w$/) and
			($latexChar2 =~ /^\w/)) {
				$latexChar2 = "*$latexChar2";

			} elsif ($latexChar1 eq '*') {
				$i--;
				splice @$latexExpr, $i, 2, $latexExpr->[$i] . $latexChar1;
				$latexChar1 = $latexExpr->[$i];

			# keep left paren for numerator together if division found
			} elsif (($latexChar1 eq ')') and
			($latexChar2 eq '/') and
			($latexExpr->[$i-2] eq '(')) {
				$i--;
				splice @$latexExpr, $i-1, 2, $latexExpr->[$i-1] . $latexExpr->[$i];
			}

			$fragment = $latexChar1 . $latexChar2;

			if ($debug) { print STDERR "combine: $fragment\n"; }

			splice @$latexExpr, $i, 2, $fragment;
			$i = -1;

		} elsif (($latexChar1 eq '(') and
		($latexChar3 eq ')')) {
			$fragment = "($latexChar2)";

			if ($debug) { print STDERR "sandwiching: $fragment\n"; }

			splice @$latexExpr, $i, 3, $fragment;
			$i = -1;

		} elsif (($latexChar1 eq '(') and
		$latexChar4 and
		($latexChar4 eq ')')) {
			if (($latexChar2 =~ /\d$/) and
			($latexChar3 =~ /^\d/)) {
				$latexChar2 .= '*';
			}

			$fragment = "(" . $latexChar2 . $latexChar3 . ")";

			if ($debug) { print STDERR "double-decker sandwich: $fragment\n"; }

			splice @$latexExpr, $i, 4, $fragment;
			$i = -1;

		} elsif (($latexChar1 =~ /[\*\)]$/) and
		($latexChar2 =~ /^[\w\d]+$/)) {
			$fragment = $latexChar1 . $latexChar2;

			if ($debug) { print STDERR "combining single variable: $fragment\n"; }

			splice @$latexExpr, $i, 2, $fragment;
			$i = -1;
		}
	
		$i += 1;
	}
}
###############################################################################

1;
