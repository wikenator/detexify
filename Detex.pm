package Detex;

# Author: Arnold Wikey
# Creation Date: December 18, 2013
# Description: Module containing all detex procedures for removing latex tags from a given string.

### tags for tracking detex changes
###
### tag: KEEP{}
###	3.3.15: method for avoiding over-saturation of parentheses in expressions

use lib('/home/arnold/git_repos/math-abstraction');
use lib('/home/arnold/git_repos/detexify');

use strict;
use warnings;
use PerlAPI qw(:Constants preClean unbalancedCharacter injectAsterixes latexplosion isLiteral isExpression);
use Abstraction qw(:All);
use Exporter;
use Data::Dumper;
use vars qw(@ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);

@ISA = qw(Exporter);
@EXPORT = ();
@EXPORT_OK = qw(&abstract &detex);
%EXPORT_TAGS = (
	DEFAULT => [qw(&detex)],
	All     => [qw(&abstract &detex &detexify &collapse)]
);

our ($debug, $match);
our $firstPass = 1;
my $infinite = 0;
my $maxIter = 100;
our @latexSplit = &getLatexSplit();
our $search_items = &getSearchItems();
our @latexTag = &getLatexTag();
our $search_terms = &getSearchTermsTag();
our @latexConstants = &getLatexConstants();
our $constant_terms = &getConstantTerms();
our $trig_terms = &getTrigTerms();

my $is_number = '-?(\d{1,3}\,?)+(\\.\\d+)?';
#my $is_number = '-?[\\d,]+(\\.\\d+)?';

### Abstract: math object abstraction and categorization ######################
sub abstract {
	my $latexExpr = shift;
	our $debug = shift;
	my $coord = 0;
	my $detexExpr;
	my $abstraction;

	if ($latexExpr =~ /^\([^\(\)\,]+?(\,[^\(\)\,]+?)+\)$/) { $coord = 1; }

	($detexExpr, $abstraction) = &detex($latexExpr, 'f', $debug, 1);

	if ($coord and ($detexExpr !~ /^\(.*?\)$/)) { $detexExpr = "($detexExpr)"; }

	return $detexExpr, $abstraction;
}
###############################################################################

### Detex: remove latex tags from expressions #################################
sub detex {
	my $latexExpr = shift;
	our $match = shift;
	our $debug = shift;
	my $abstraction = shift;
	my $fragment = '';
	my $abstractExpr = 'MATH';
	my $innerAbstract = '';
	my $outerAbstract = '';
	my ($temp_ia, $temp_oa, $temp_collapse_ia, $temp_collapse_oa);

	if ((not $latexExpr) and
	$latexExpr != 0) {
		if ($abstraction == 1) { return $latexExpr, 'NOPARSE'; }
		else { return $latexExpr; }
	}

	$latexExpr = &preClean($latexExpr);

	if ($latexExpr !~ /\d+\s\d+\/\d+/) {
		$latexExpr =~ s/\s+//g; 	# remove all spaces

	} else {
		if ($latexExpr !~ /^\d+\s\d+\/\d+$/) {
			$innerAbstract = 'LITERAL';
			$outerAbstract = 'FRACTION';
		}

		$latexExpr =~ s/(\d+)\s(\d+\/\d+)/$1+$2/g;
	}

	$latexExpr =~ s/\$\\\\\$//g;		# remove newline between latex tags

	if (&isLiteral($latexExpr, $debug)) {
		$innerAbstract = 'LITERAL';
	}

	if ($latexExpr =~ /^(.*?):(.*?)$/) {
		$outerAbstract = 'RATIO';
	}

	$latexExpr =~ s/^(.*?):(.*?)$/($1)\/($2)/g;	# replace : (ratio) with / (division)
	$latexExpr =~ s/^(.*?):(.*?)$/$1)\/($2/g;	# replace : (ratio) with / (division)

	if ($debug) { print STDERR "DETEX even tags start: $latexExpr\n"; }

	# make sure tags are even
	if (&unbalancedCharacter($latexExpr, '(', ')', $debug) != 0 or
	&unbalancedCharacter($latexExpr, '{', '}', $debug) != 0 or
#	&unbalancedCharacter($latexExpr, '(', ']', $debug) != 0 or
#	&unbalancedCharacter($latexExpr, '[', ')', $debug) != 0 or
	&unbalancedCharacter($latexExpr, '[', ']', $debug) != 0) {
		if ($abstraction == 1) { return 0, 'NOPARSE'; }
		else { return 0; }
	}

	if ($debug) { print STDERR "DETEX even tags end: $latexExpr\n"; }

	if ($latexExpr =~ /^(\-)?\\infty$/) {
		$outerAbstract = 'INFINITY';
	}

	$latexExpr =~ s/(\-)?\\infty/$1inf/g;	# replace \infty with inf

	if ($latexExpr =~ /^([^\^]+)^([^\^]+)$/) {
		my $tmp1 = $1;
		my $tmp2 = $2;

		if ($tmp1 =~ /^\d+$/ and $tmp2 =~ /^\d+$/) {
			$innerAbstract = 'LITERAL';

		} else {
			$innerAbstract = 'SYMBOLIC';
		}

		$outerAbstract .= 'EXPRESSION:EXPONENTIAL';
	}

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

	if ($latexExpr =~ /^(\.|[^\d])\.\d+(\\?%)?/) {
		$innerAbstract = 'LITERAL';
		$outerAbstract = 'DECIMAL';

	} elsif ($latexExpr =~ /^\.[a-zA-Z]+/) {
		$innerAbstract = 'SYMBOLIC';
		$outerAbstract = 'DECIMAL';

	} elsif ($latexExpr =~ /^-?([^\.\(\)\{\}\+\-\*\/]*?)\.([^\.\(\)\{\}\+\-\*\/]+?)(\\?%)?$/) {
		my $temp1 = $1;
		my $temp2 = $2;

		if (($temp1 =~ /^[\d,]*$/) and ($temp2 =~ /^\d+$/)) {
			$innerAbstract = 'LITERAL';
			$outerAbstract = 'DECIMAL';

		} else {
			$innerAbstract = 'SYMBOLIC';
			$outerAbstract = 'DECIMAL';
		}
	}

	$latexExpr =~ s/([^\d])(\.\d+)/${1}0$2/g; # replace .# with 0.#
	$latexExpr =~ s/^\.([^\.][^\.])/0.$1/g; # replace leading .# with 0.#

	if ($latexExpr =~ /%$/) {
		if ($debug) { print STDERR "DETEX percentage found\n"; }

		if ($innerAbstract ne 'LITERAL' and
		&isLiteral($latexExpr, $debug)) {
			if (not defined $outerAbstract or
			($outerAbstract eq '')) {
				$outerAbstract = 'PERCENT';

			} else {
				$outerAbstract .= ':PERCENT';
			}

		} else {
			if (not defined $outerAbstract or
			($outerAbstract eq '')) {
				$outerAbstract = 'PERCENT';

			} else {
				$outerAbstract .= ':PERCENT';
			}
		}
	}

	if ($latexExpr =~ /^(.+?)\^\{\\circ\}$/) {
		if ($innerAbstract ne 'LITERAL' and
		&isLiteral($1, $debug)) {
			$innerAbstract = 'LITERAL';
			$outerAbstract = 'DEGREE';

		} else {
			$innerAbstract = 'SYMBOLIC';
			$outerAbstract = 'DEGREE';

			# continue finding DEGREE or ANGLE abstractions here
		}
	}

	if ($latexExpr =~ /angle/) {
		$innerAbstract = 'SYMBOLIC';
		$outerAbstract = 'ANGLE';
	}

	if ($latexExpr =~ /\^\{\\circ\}/) {
		$latexExpr =~ s/\^\{\\circ\}//g;	# remove degree symbols

		if ($latexExpr !~ /,/ and
		$latexExpr !~ /($trig_terms)/) {
			$innerAbstract = &isLiteral($latexExpr, $debug) ? 'LITERAL' : 'SYMBOLIC';
		}
	}

#	$latexExpr =~ s/\(/{/g;			# replace ( with {
#	$latexExpr =~ s/\)/}/g;			# replace ) with }

	if ($latexExpr =~ /^\|(.*?)\|$/) {
		$outerAbstract = 'EXPRESSION:ABSOLUTEVALUE';
	}

	$latexExpr =~ s/\|(.*?)\|/abs($1)/g;	# replace | with abs tag

	if ($latexExpr =~ /^-?($constant_terms|[a-zA-Z])(_\{?.\}?)?$/) {
		$innerAbstract = 'SYMBOLIC';
		$outerAbstract = 'CONSTANT';
	}

	$latexExpr =~ s/\\?pi/#pi/g;		# escape pi tag
	$latexExpr =~ s/\\?theta/#theta/g;
	$latexExpr =~ s/\\?phi/#phi/g;
	$latexExpr =~ s/\\?var#phi/#varphi/g;
	$latexExpr =~ s/\\?rho/#rho/g;
	$latexExpr =~ s/\\?sigma/#sigma/g;
	$latexExpr =~ s/\\?([Gg])amma/#$1amma/g;
	$latexExpr =~ s/\\?beta/#beta/g;
	$latexExpr =~ s/\\?beth/#beth/g;
	$latexExpr =~ s/\\?alpha/#alpha/g;
	$latexExpr =~ s/\\?aleph/#aleph/g;
	$latexExpr =~ s/\\?omega/#omega/g;
	$latexExpr =~ s/\\?delta/#delta/g;
	$latexExpr =~ s/\\?chi/#chi/g;
	$latexExpr =~ s/\\?epsilon/#epsilon/g;

	if ($latexExpr =~ /^-?\\?(log|ln)([^a-zA-Z])?\(?.+?\)?$/) {
		$outerAbstract = 'EXPRESSION:LOGARITHM';
	}

	# old regex compare			
#	if ($latexExpr =~ /log[^A-Za-z]/) {
#		$latexExpr =~ s/\\?log/#log/g;	# escape log tag
#	}

	$latexExpr =~ s/\\?(log|ln)([^\(\)\+\-\*\/_]+?)/$1($2)/g; # escape log or ln tag
	$latexExpr =~ s/\\?(log|ln)/#$1/g;	# escape log tag

	# old ln regex
#	$latexExpr =~ s/\\?ln/#ln/g;		# escape ln tag
	$latexExpr =~ s/\\emptyset/#emptyset/g;	# escape emptyset tag
#	$latexExpr =~ s/\\operatorname\{(.*?)\}/$1/g;	# remove operatorname
	$latexExpr =~ s/\\mbox\{(.*?)\}/$1/g;		# remove mbox
#	$latexExpr =~ s/\\overline\{(.*?)\}/$1/g;	# remove overline
	$latexExpr =~ s/\\mathrm\{(.*?)\}/$1/g;		# remove mathrm
	## mathbb, textbf, text, textit, texttt, mathcal, mathfrak
	## doteq

	if ($latexExpr =~ /\\?((a)(rc)?)?(cos|sin|tan|csc|sec|cot)(h)?[^A-Za-z]/) {
		$latexExpr =~ s/\\?(((a)(rc)?)?)(cos|sin|tan|csc|sec|cot)/#$1$5$6/g;# escape atrig tag
		$outerAbstract = 'EXPRESSION:TRIGONOMETRY';
	}

	if ($latexExpr =~ /($trig_terms)/) {
		$outerAbstract = 'EXPRESSION:TRIGONOMETRY';
	}

	$latexExpr =~ s/#arc(cos|sin|tan|csc|sec|cot)/#a$1$2/g;
	$latexExpr =~ s/\\?sqrt/\\sqrt/g;	# escape sqrt tag
	$latexExpr =~ s/exp/e\^/g;		# replace exp function with e

	if ($debug) { print STDERR "DETEX ready: $latexExpr\n"; }

	my $strPos = 0;
	my @fragment;
	my ($detexExpr, $latexChar);

	if (length($latexExpr) >= 4) {
		my $subExpr = &latexplosion($latexExpr, $debug);

		if ($debug) { print STDERR "DETEX length greater than 4\n"; }

		# detexify and collapse subExpr array
		while ((scalar @$subExpr) > 3) {
			if ($debug) { print STDERR "DETEX length greater than 3\n"; }

			(undef, $temp_ia, $temp_oa) = &detexify($subExpr, $innerAbstract, $outerAbstract);
			($temp_collapse_ia, $temp_collapse_oa) = &collapse($subExpr, $temp_ia, $temp_oa);
			$outerAbstract = &Abstraction::compare_outer_abstraction($temp_collapse_oa, $temp_oa, $debug);
			$temp_ia = &Abstraction::compare_inner_abstraction($temp_ia, $temp_collapse_ia, $debug);
			($innerAbstract, $outerAbstract) = &Abstraction::compare_inner_outer_abstraction($temp_ia, $innerAbstract, $temp_oa, $outerAbstract, $debug);

			# quit if detex does not finish before 50 iterations
			if (++$infinite > $maxIter) {
				if ($abstraction == 1) {
					return $subExpr->[0], 'NOPARSE';

				} else {
					return $subExpr->[0];
				}
			}
		
			if ($debug) {
				print STDERR "DETEX end of 3-item section\n";
				print STDERR Dumper($subExpr);
			}
		}

		# collapse remaining 2 or 3 subexpression entries
		if ((scalar @$subExpr) == 3) {
			if ($debug) { print STDERR "DETEX remaining collapse entries: IA: $innerAbstract OA: $outerAbstract\n"; }

			if ($innerAbstract eq '' and
			$outerAbstract eq '') {
				if ($latexExpr =~ /^[\d\.\+\-\*\/]+$/) {
					$innerAbstract = 'LITERAL';
					$outerAbstract = 'EXPRESSION';

				} elsif ($latexExpr =~ /^[a-zA-Z\+\-\*\/]$/) {
					$innerAbstract = 'SYMBOLIC';
					$outerAbstract = 'EXPRESSION';
				}
			}

			if ($subExpr->[1] =~ /,/) {
				my @coords = split(',', $subExpr->[1]);

				if ($subExpr->[0] eq '[' or
				$subExpr->[2] eq ']') {
					$outerAbstract = 'INTERVAL';

				} elsif ($subExpr->[0] eq '(' or
				$subExpr->[2] eq ')') {
					$outerAbstract = 'ORDEREDSET';

				} else {
					$outerAbstract = 'SET';
				}

				foreach my $coord (@coords) {
					if ($debug) { print STDERR "DETEX coord: $coord\n"; }

					$firstPass = 1;

					if ($innerAbstract ne 'SYMBOLIC') {
						$innerAbstract = &Abstraction::compare_inner_abstraction((&detexify([$coord], &isLiteral($coord, $debug) ? 'LITERAL' : 'SYMBOLIC', $outerAbstract))[1], $innerAbstract, $debug);
					} else { last; }

#					if ($innerAbstract eq 'SYMBOLIC') { last; }
				}
			}

			$fragment = $subExpr->[0] . $subExpr->[1] . $subExpr->[2];
			splice @$subExpr, 0, 3, $fragment;

		} elsif ((scalar @$subExpr) == 2) {
			if ($debug) { print STDERR "DETEX remaining 2 entries\n"; }

			$fragment = $subExpr->[0] . $subExpr->[1];

			# TEMP not sure if separate detexifies, or run like doing coordinates
#			$innerAbstract = &Abstraction::compare_inner_abstraction((&detexify([$fragment], &isLiteral($fragment) ? 'LITERAL' : 'SYMBOLIC', $outerAbstract))[1], $innerAbstract, $debug);

			splice @$subExpr, 0, 2, $fragment;

		} elsif ($subExpr->[0] =~ /,/ and
		$subExpr->[0] =~ /^[\{\[\(].*?[\}\]\)]$/) {
			my @coords = split(',', $subExpr->[0]);

			if ($coords[0] =~ /^\[/ or
			$coords[1] =~ /\]$/) {
				$outerAbstract = 'INTERVAL';

			} elsif ($coords[0] =~ /^\(/ or
			$coords[1] =~ /\)$/) {
				$outerAbstract = 'ORDEREDSET';

			} else {
				$outerAbstract = 'SET';
			}

			my $i = 0;

			foreach my $coord (@coords) {
				if ($i == 0) {
					$coord = substr $coord, 1;
					$i += 1;

				} elsif ($i != $#coords-1) {
					$coord = substr $coord, 0, -1;

				} else {
					$i += 1;
				}

				if ($debug) { print STDERR "DETEX coord: $coord\n"; }

				$firstPass = 1;

				if ($innerAbstract ne 'SYMBOLIC') {
					$innerAbstract = &Abstraction::compare_inner_abstraction((&detexify([$coord], &isLiteral($coord, $debug) ? 'LITERAL' : 'SYMBOLIC', $outerAbstract))[1], $innerAbstract, $debug);
				} else { last; }

#				if ($innerAbstract eq 'SYMBOLIC') { last; }
			}
		}

		if ($innerAbstract eq '' and
		$outerAbstract eq '' and
		(scalar @$subExpr) == 1) {
			if ($debug) { print STDERR "DETEX nothing classified yet\n"; }

			if ($subExpr->[0] =~ /^[\d\.\+\-\*\/\(\)i]+$/) {
				$innerAbstract = 'LITERAL';
				$outerAbstract = 'EXPRESSION';

			} elsif ($subExpr->[0] =~ /^[\da-zA-Z\+\-\*\/\(\)]+$/) {
				$innerAbstract = 'SYMBOLIC';
				$outerAbstract = 'EXPRESSION';
			}

			if ($subExpr->[0] =~ /^[^islcp]*i[^inmr]*$/) {
				$outerAbstract .= ':COMPLEX';
			}
		}

		if ($debug) { print STDERR "DETEX \nFinal Detex\n"; }
	
		# final detexify
		($detexExpr, $temp_ia, $temp_oa) = &detexify($subExpr, $innerAbstract, $outerAbstract);
		($temp_collapse_ia, $temp_collapse_oa) = &collapse([$detexExpr], $temp_ia, $temp_oa);
		$outerAbstract = &Abstraction::compare_outer_abstraction($temp_collapse_oa, $temp_oa, $debug);
		$temp_ia = &Abstraction::compare_inner_abstraction($temp_ia, $temp_collapse_ia, $debug);
		($innerAbstract, $outerAbstract) = &Abstraction::compare_inner_outer_abstraction($temp_ia, $innerAbstract, $temp_oa, $outerAbstract, $debug);

		$detexExpr =~ s/\\//g;	# remove backslashes
	
		### avoid removing {} for now
		### tag: KEEP{}
		#$detexExpr =~ s/{/(/g;	# replace curly braces with parentheses
		#$detexExpr =~ s/}/)/g;	# replace curly braces with parentheses
		if ($detexExpr =~ /[^_\^]\{.*?\}/) {
			$detexExpr =~ s/([^_\^])\{(.*?)\}/$1($2)/g;
		}

		# replace -1 exponent with arc equivalent
		if ($detexExpr =~ /(cosh|sinh|tanh|csch|sech|coth|cos|sin|tan|csc|sec|cot)\^[\(\{]{1,2}-1[\)\}]{1,2}/) {
			$detexExpr =~ s/(cosh|sinh|tanh|csch|sech|coth|cos|sin|tan|csc|sec|cot)\^[\(\{]{1,2}-1[\)\}]{1,2}/a$1/g;
		}

		# remove *1 and 1*
		$detexExpr =~ s/[^\w\(]1\*//g;
		$detexExpr =~ s/\*1[^\w\)]//g;

	} else {
		if ($debug) { print STDERR "DETEX length less than 4\n"; }

		if (length($latexExpr) == 3) {
			if ($debug) { print STDERR "DETEX short-length abstract 3\n"; }
			
			if ($latexExpr =~ /^(.+?)[\+\-\*\/](.+?)$/) {
				my $temp1 = $1;
				my $temp2 = $2;
				$outerAbstract = 'EXPRESSION';

				if ($latexExpr =~ /^[^islcp]*i[^inmr]*$/) {
					$outerAbstract .= ':COMPLEX';
				}

				if (($temp1 =~ /^[a-zA-Z]+$/ or
				$temp2 =~ /^[a-zA-Z]+$/) and
				not($temp1 =~ /^[^islcp]*i[^inmr]*$/ or
				$temp2 =~ /^[^islcp]*i[^inmr]*$/)) {
					$innerAbstract = 'SYMBOLIC';

				} else {
					$innerAbstract = 'LITERAL';

					# override EXPRESSION abstraction
					if ($latexExpr =~ /^.+\/.+$/) {
						$outerAbstract = 'FRACTION';
					}
				}

			} elsif ($latexExpr =~ /^[\+\-\*\/]([\da-zA-Z]{2})$/ or
			$latexExpr =~ /^([\da-zA-Z]{2})([\+\-\*\/!])$/) {
				my $temp1 = $1;
				my $temp2 = $2;

				if ($temp1 =~ /^[a-zA-Z]{2}$/ or
				$temp1 =~ /^\d[a-zA-Z]$/) {
					$innerAbstract = 'SYMBOLIC';

				} else {
					$innerAbstract = 'LITERAL';
				}

				if ($temp2 =~ /^!$/) { $outerAbstract .= 'FACTORIAL'; }
				else { $outerAbstract = 'EXPRESSION'; }

			} elsif ($latexExpr =~ /^([\da-zA-Z])([\da-zA-Z])([\da-zA-Z])$/) {
				my $temp1 = $1;
				my $temp2 = $2;
				my $temp3 = $3;

				if ($temp1 =~ /[a-zA-Z]/ or
				$temp2 =~ /[a-zA-Z]/ or
				$temp3 =~ /[a-zA-Z]/) {
					$innerAbstract = 'SYMBOLIC';

				} else {
					$innerAbstract = 'LITERAL';
				}
			}

		} elsif (length($latexExpr) == 2) {
			if ($debug) { print STDERR "DETEX short-length abstract 2\n"; }

			if ($latexExpr =~ /^[\+\-\*\/]([\da-zA-Z])$/) {
				my $temp1 = $1;

				if ($temp1 =~ /^[a-zA-Z]$/) { $innerAbstract = 'SYMBOLIC'; }
				else { $innerAbstract = 'LITERAL'; }

			} elsif ($latexExpr =~ /^([\da-zA-Z])([\+\-\*\/!])$/) {
				my $temp1 = $1;
				my $temp2 = $2;

				if ($temp1 =~ /^[a-zA-Z]$/) { $innerAbstract = 'SYMBOLIC'; }
				else { $innerAbstract = 'LITERAL'; }

				if ($temp2 =~ /^!$/) { $outerAbstract = 'FACTORIAL'; }
				else { $outerAbstract = 'EXPRESSION'; }

			} elsif ($latexExpr =~ /^\d[a-zA-Z]$/ or
			$latexExpr =~ /^[a-zA-Z]{2}$/) {
				$outerAbstract = 'EXPRESSION';
				$innerAbstract = 'SYMBOLIC';
			}
		}

		$detexExpr = $latexExpr;

		if ($debug) { print STDERR "DETEX short-length, IA: $innerAbstract, OA: $outerAbstract\n"; }
	}

	$detexExpr = &injectAsterixes($detexExpr, $debug);

	if (&isExpression($detexExpr, $outerAbstract, $debug)) {
		$outerAbstract = &Abstraction::compare_outer_abstraction('EXPRESSION', $outerAbstract, $debug);

		if ($innerAbstract eq '') {
			if ($detexExpr =~ /^[\d\.\+\-\*\/\(\)i]+$/) {
				$innerAbstract = 'LITERAL';

			} elsif ($detexExpr =~ /^[\da-zA-Z\+\-\*\/\(\)]+$/) {
				$innerAbstract = 'SYMBOLIC';
			}
		}

		if ($outerAbstract eq 'EXPRESSION' and
		$detexExpr =~ /^[^islcp]*i[^inmr]*$/) {
			$outerAbstract .= ':COMPLEX';
		}
	}

	if ($detexExpr =~ /^($constant_terms|gcd|lcm|[a-zA-Z])\([^,]+?(,[^,]+?)?\)$/) {
		$outerAbstract = 'EXPRESSION:FUNCTION';
		$innerAbstract = 'SYMBOLIC';
	}

	if ($detexExpr =~ /vector\([abcijkABCIJK]\)/) {
		$outerAbstract = 'LINEARALG:VECTOR';
		$innerAbstract = 'SYMBOLIC';

	} elsif ($detexExpr =~ /vector\((F|sigma\(t\))\)/) {
		if ($1 eq 'F') {
			$outerAbstract = 'CALCULUS:MULTIVAR:VECTOR';

		} else {
			$outerAbstract = 'CALCULUS:SINGLEVAR:VECTOR';
		}

		$innerAbstract = 'SYMBOLIC';
	}

	if ($detexExpr =~ /(curl|div)vector/) {
		$outerAbstract = 'CALCULUS:MULTIVAR';
	}

	# final paren removal for negative numbers
	$detexExpr =~ s/((?<!\^)(?<!sqrt))\((-\w+)\)([^\^])/$1$2$3/g;
	$detexExpr =~ s/^\((-\w+)\)([^\^])/$1$2/;

	if ($debug) { print STDERR "DETEX iterations used: $infinite\n"; }

	if ($abstraction == 1) {
		my @a = split(':', $innerAbstract);
		push @a, split(':', $outerAbstract);

		if ($debug) { print "DETEX final abstraction: " . Dumper(@a); }

		$abstractExpr = &Abstraction::update_abstraction("MATH", [@a], $debug);

		return $detexExpr, $abstractExpr;

	} else {
		return $detexExpr;
	}
}
###############################################################################

### Detexify: remove latex tags and expand expressions ########################
sub detexify {
	my $latexExpr = shift;
#	my $abstractExpr = shift;
	my $innerAbstract = shift;
	my $outerAbstract = shift;
	$innerAbstract = '' if not defined $innerAbstract;
	$outerAbstract = '' if not defined $outerAbstract;
	our $firstPass;
	my ($latexChar, $innerExpr, $innerDetex, $numer, $denom);
	my ($temp_ia, $temp_oa);
	my $i = 0;
	my $j = 0;
	my $brack_count = 0;
	my $delim_count = 0;
	my $subExpr;
	my $subString;
	my $initialString = $latexExpr;

	if ($debug) {
		print STDERR "DETEXIFY Entering detexify (pass $firstPass):\n";
		print STDERR "DETEXIFY IA: $innerAbstract, OA: $outerAbstract\n";
		print STDERR Dumper($latexExpr);
	}

	if ($firstPass) {
		$firstPass = 0;

		if (((scalar @$latexExpr) == 1) and ($latexExpr->[$i] =~ /($search_terms)/)) {
			if ($debug) { print STDERR "DETEXIFY last pass, one item: $latexExpr->[0]\n"; }

			$initialString = $latexExpr->[0];
			$latexExpr = &latexplosion(@$latexExpr, $debug);
		}

	} else {
		return join('', @$latexExpr), $innerAbstract, $outerAbstract;
	}

	while ($i < (scalar @$latexExpr)) {
		$latexChar = $latexExpr->[$i];

		if ($debug) { print STDERR "DETEXIFY latexChar detex: $latexChar\n"; }

		if ($latexChar eq '\frac') {
			$outerAbstract = &Abstraction::compare_outer_abstraction('FRACTION', $outerAbstract, $debug);

			if ($debug) { print STDERR "DETEXIFY frac section\n"; }

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
			($numer, $innerAbstract, $outerAbstract) = &detexify(&latexplosion($subString), $innerAbstract, $outerAbstract);
			
#			$innerAbstract = ($numer =~ /^$is_number$/) ? 'LITERAL' : 'SYMBOLIC';

			if ($debug) { print STDERR "DETEXIFY \nnumer: $numer, $innerAbstract, $outerAbstract\n"; }

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
			($denom, $innerAbstract, $outerAbstract) = &detexify(&latexplosion($subString), $innerAbstract, $outerAbstract);

#			$innerAbstract = ($denom =~ /^$is_number$/) ? 'LITERAL' : 'SYMBOLIC';

			if ($debug) { print STDERR "DETEXIFY \ndenom: $denom, $innerAbstract, $outerAbstract\n"; }

			$d2 = $j;
			splice @$latexExpr, $d1, $d2-$d1, $denom;
			splice @$latexExpr, $n1, $n2-$n1, $numer;

			if ($debug) { print STDERR Dumper($latexExpr); }

			($temp_ia, $temp_oa) = &collapse($latexExpr, $innerAbstract, $outerAbstract);
			$innerAbstract = &Abstraction::compare_inner_abstraction($temp_ia, $innerAbstract, $debug);
			$outerAbstract = &Abstraction::compare_outer_abstraction($outerAbstract, $temp_oa, $debug);

		} elsif ($latexChar =~ /^($search_terms)$/) {
			if ($debug) { print STDERR "DETEXIFY other latex tag\n"; }

			my ($tag_arg, $left_delim, $right_delim);
			my $offset = 0;
			my $sqrt_section = 0;
			$subString = '';
			$delim_count = 0;
			$j = $i+2;

			if ($latexChar eq '\sqrt') {
				$outerAbstract = &Abstraction::compare_outer_abstraction('EXPRESSION:ROOT', $outerAbstract, $debug);

				if ($debug) { print STDERR "DETEXIFY sqrt section\n"; }

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
				if ($debug) { print STDERR "DETEXIFY exponential part\n"; }

				if ($latexExpr->[$i] =~ /($trig_terms)/) {
					$outerAbstract = 'EXPRESSION:TRIGONOMETRY';

				} else {
					$outerAbstract = 'EXPRESSION:EXPONENTIAL';
				}

				$left_delim = '{';
				$right_delim = '}';
				
				$i += 2;
				$j = $i + 1;
				
				$offset = 1;
				$delim_count = 1;

			} else {
				if ($debug) { print STDERR "DETEXIFY paren delimiters\n"; }

				$left_delim = '(';
				$right_delim = ')';

				# make sure substring is not denominator
				if ((($latexExpr->[$i+2] and 
				($latexExpr->[$i+2] eq '(') and
				($latexExpr->[$i+1] ne '/'))) or
				($latexExpr->[$i+1] and 
				$latexExpr->[$i+1] eq '(')) {
					$delim_count = 1;
					$i += 2;

				} else {
					$subString = $latexExpr->[$i];
				}
			}

			my $k = $j;
			
			if ($delim_count > 0) {
				if ($debug) { print STDERR "DETEXIFY gathering arg\n"; }

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
						if ($debug) { print STDERR "DETEXIFY stuck in delim hell\n"; }

						return $latexExpr->[0], $innerAbstract, $outerAbstract;
					}
				}

				if ($debug) { print STDERR "DETEXIFY substring: $subString\n"; }

				$firstPass = 1;
				($tag_arg, $innerAbstract, $outerAbstract) = &detexify(&latexplosion($subString, $debug), $innerAbstract, $outerAbstract);
#				($tag_arg, $innerAbstract, $outerAbstract) = &detexify([$subString], $innerAbstract, $outerAbstract);

				$tag_arg =~ s/\{/\(/g;
				$tag_arg =~ s/\}/\)/g;

				if ($debug) { print STDERR "DETEXIFY \ntag arg: $tag_arg, IA: $innerAbstract OA: $outerAbstract\n"; }

				$innerAbstract = &isLiteral($tag_arg, $debug) ? 'LITERAL' : 'SYMBOLIC';

			} else {
				$tag_arg = $subString;
				$k = --$j;
			}

			if ($sqrt_section and 
			($left_delim eq '(')) {
				$latexExpr->[$k] = '}';

				if ($k-$j > 1) {
					if ($debug) { print STDERR "DETEXIFY IDX -- i: $i $latexExpr->[$i], j: $j $latexExpr->[$j], k: $k $latexExpr->[$k]\n"; }

					$latexExpr->[$i] = '{';
					$j++;

					if ($debug) { print STDERR "DETEXIFY IDX -- size: " . ($j-$i-$offset) . ", i: $i $latexExpr->[$i], j: $j $latexExpr->[$j], k: $k $latexExpr->[$k]\n"; }

					splice @$latexExpr, $i+$offset, $k-$i-$offset, $tag_arg;

				} else {
					$latexExpr->[$i+$offset-1] = '{';
					$j++;
	
					if ($debug) { print STDERR "DETEXIFY IDX 2 -- size: " . ($j-$i-$offset) . ", i: $i $latexExpr->[$i], j: $j $latexExpr->[$j], k: $k $latexExpr->[$k]\n"; }

					splice @$latexExpr, $i+$offset, $j-$i-$offset, $tag_arg;
				}

			} else {
				splice @$latexExpr, $i+$offset, $k-$i-$offset, $tag_arg;
			}

			($temp_ia, $temp_oa) = &collapse($latexExpr, $innerAbstract, $outerAbstract);
			$innerAbstract = &Abstraction::compare_inner_abstraction($temp_ia, $innerAbstract, $debug);
			$outerAbstract = &Abstraction::compare_outer_abstraction($temp_oa, $outerAbstract, $debug);

			if ($debug) { print STDERR "DETEXIFY after match check: " . ($latexExpr->[$i] ? $latexExpr->[$i] : 'nothing') . "\n"; }

		} elsif ($latexExpr->[$i+1] and 
		$latexExpr->[$i+1] eq '^') {
			($temp_ia, $temp_oa) = &collapse($latexExpr, $innerAbstract, $outerAbstract);
			$outerAbstract = &Abstraction::compare_outer_abstraction($outerAbstract, $temp_oa, $debug);
			$innerAbstract = &Abstraction::compare_inner_abstraction($temp_ia, $innerAbstract, $debug);
#		($innerAbstract, $outerAbstract) = &Abstraction::compare_inner_outer_abstraction($temp_ia, $innerAbstract, $temp_oa, $outerAbstract, $debug);
		}
			
		$i++;

#		if (not(grep(/\Q$latexChar\E/, @latexTag))) {
#			# \ln{a} -> \ln(a)
#			$latexExpr->[$i] =~ s#\\*ln\\*{(.*?)\\*}#ln($1)#g;
#		}

		# quit if detexify does not finish before 50 iterations
		if (++$infinite > $maxIter) {
#			($innerAbstract, $outerAbstract) = &Abstraction::compare_inner_outer_abstraction($temp_ia, $innerAbstract, $temp_oa, $outerAbstract);

			return $latexExpr->[0], $innerAbstract, $outerAbstract;
		}
	}

#	($innerAbstract, $outerAbstract) = &Abstraction::compare_inner_outer_abstraction($temp_ia, $innerAbstract, $temp_oa, $outerAbstract);

	# collapse remaining 2 or 3 subexpression entries
	if ((scalar @$latexExpr) == 3) {
		if ($debug) { print STDERR "DETEXIFY last three\n"; }

		splice @$latexExpr, 0, 3, ($latexExpr->[0] . $latexExpr->[1] . $latexExpr->[2]);

	} elsif ((scalar @$latexExpr) == 2) {
		if ($debug) { print STDERR "DETEXIFY last two\n"; }

		if ($innerAbstract eq '' and
		$outerAbstract eq '') {
			if ($latexExpr->[0] =~ /^-?\d+$/ and
			$latexExpr->[1] =~ /^($constant_terms)$/) {
				$innerAbstract = 'SYMBOLIC';
				$outerAbstract = 'EXPRESSION';
			}
		}

		splice @$latexExpr, 0, 2, ($latexExpr->[0] . $latexExpr->[1]);
	}

	if ($latexExpr->[0] eq $initialString) {
		if ($debug) { print STDERR "DETEXIFY nothing to handle: $latexExpr->[0]\n"; }

		if ($latexExpr->[0] =~ /^-?($constant_terms)$/) {
			$innerAbstract = 'SYMBOLIC';
		}

#		$innerAbstract = ($latexExpr->[0] =~ /^$is_number$/) ? 'LITERAL' : 'SYMBOLIC';

		return $latexExpr->[0], $innerAbstract, $outerAbstract;

	} elsif ((scalar @$latexExpr) == 1) {
		if ($debug) { print STDERR "DETEXIFY only one item, $latexExpr->[0] IA: $innerAbstract OA: $outerAbstract\n"; }

		if ((not defined $innerAbstract) or
		($innerAbstract eq '')) {
#			if ($latexExpr->[0] =~ /^$is_number$/) {
			if ($innerAbstract ne 'LITERAL' and
			&isLiteral($latexExpr->[0], $debug)) {
				$innerAbstract = 'LITERAL';

			} elsif ($latexExpr->[0] =~ /^-?($constant_terms|[a-zA-Z])(_\{?.\}?)?$/) {
				$innerAbstract = 'SYMBOLIC';
				$outerAbstract = &Abstraction::compare_outer_abstraction('CONSTANT', $outerAbstract, $debug);

			} else {
				$innerAbstract = 'SYMBOLIC';
			}
		}

		return $latexExpr->[0], $innerAbstract, $outerAbstract;

	} else {
		(undef, $innerAbstract, $outerAbstract) = &detexify($latexExpr, $innerAbstract, $outerAbstract);
	}
}
###############################################################################

### Collapse: collapse latex expression array #################################
sub collapse {
	my $latexExpr = shift;
#	my $abstractExpr = shift;
	my (@collapseExpr, @latexChar);
	my ($latexChar1, $latexChar2, $latexChar3, $latexChar4);
	my $innerAbstract = shift;
	my $outerAbstract = shift;
	my $i = 0;
	my $j;
	my $fragment = '';
	my ($temp_ia, $temp_oa);

	if ($debug) {
		print STDERR "COLLAPSE Collapsing, IA: $innerAbstract, OA: $outerAbstract\n";
		print STDERR Dumper($latexExpr);
	}

#	if ((scalar @$latexExpr) == 1) {
#		print "returning here\n";
#		$innerAbstract = ($latexExpr->[0] =~ /^$is_number$/) ? 'LITERAL' : 'SYMBOLIC';
#	}

	while ($i < (scalar @$latexExpr)-1) {
		$latexChar1 = $latexExpr->[$i];
		$latexChar2 = $latexExpr->[$i+1];
		$latexChar3 = $latexExpr->[$i+2];
		$latexChar4 = $latexExpr->[$i+3];

		if ($debug) {
			print STDERR Dumper($latexExpr);
			print STDERR "COLLAPSE char1: $latexChar1\tchar2: $latexChar2\n";
			
			if ($latexChar2 !~ /^($search_terms)$/) { print STDERR "COLLAPSE not a tag\n"; }
			else { print STDERR "COLLAPSE it's a tag\n"; }
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
		(($latexChar1 =~ /\d*\.?\d+\+?$/) or
		($latexChar1 =~ /\w\+?/))) {
			if ($latexChar1 =~ /-?[\w\d]\+?$/) {
				if ((($latexChar2 =~ /\\frac\{\d*\.?\d+\}\{\d*\.?\d+\}/) or
				($latexChar2 =~ /\\frac\{\w\}\{\w\}/) or
				($latexChar2 =~ /^\\frac/)) and
				($latexChar1 !~ /\+$/)) {
					$latexExpr->[$i] = $latexChar1 . '+';

				# otherwise add multiplication sign to scalar multiple
				} elsif ($latexChar1 !~ /\+$/) {
					$latexExpr->[$i] = $latexChar1 . '*';
				}

				$outerAbstract = 'FRACTION:MIXED';
			}

			if ($debug) { print STDERR "COLLAPSE mixed fractions: $latexExpr->[$i], OA: $outerAbstract\n"; }

			$latexChar1 = $latexExpr->[$i];
		}

		if (($latexChar1 =~ /($search_terms)(\^\(?[\w\d]+\)?)?/) and
		($latexChar2 eq '(') and
		($latexChar4 eq ')')) {
			if ($debug) { print STDERR "COLLAPSE function with simple arg\n"; }

			$outerAbstract = &determineOuterAbstract($latexChar1, $debug);
#			$innerAbstract = ($latexChar3 =~ /$is_number/) ? 'LITERAL' : 'SYMBOLIC';
			$innerAbstract = &isLiteral($latexChar3, $debug) ? 'LITERAL' : 'SYMBOLIC';

			$fragment = $latexChar1 . '(' . $latexChar3 . ')';
			splice @$latexExpr, $i, 4, $fragment;

			$i = -1;

		} elsif (($latexChar1 =~ /^($search_terms)$/) and
		($latexChar2 =~ /^\^/) and
		($latexChar3 eq '(') and
		$latexExpr->[$i+4] and
		($latexExpr->[$i+4] eq ')')) {
			if ($debug) { print STDERR "COLLAPSE power of a function\n"; }

			$innerAbstract = &isLiteral($latexChar4, $debug) ? 'LITERAL' : 'SYMBOLIC';
			$latexChar2 =~ s/^\^\{(\(.*?\))\}$/^$1/;
			$fragment = $latexChar1 . $latexChar2 . "($latexChar4)";
			splice @$latexExpr, $i, 5, $fragment;

			$i = -1;

		} elsif (($latexChar1 =~ /^($search_terms)$/) and
		($latexChar2 =~ /^\^\d$/)) {
			if ($debug) { print STDERR "COLLAPSE function power\n"; }

			$innerAbstract = 'LITERAL';
			$fragment = $latexChar1 . $latexChar2;
			splice @$latexExpr, $i, 2, $fragment;
			
			$i = -1;

		} elsif (($latexChar1 !~ /^($search_terms)$/) and
		($latexChar1 !~ /^($search_items)$/) and
		(($latexChar2 eq '+') or 
		($latexChar2 eq '-')) and
		($latexChar3 !~ /^($search_terms)$/)) {
			if ($latexChar1 ne '(') {
				$innerAbstract = 'SYMBOLIC';
				$outerAbstract = 'EXPRESSION';
			}

			$fragment = $latexChar1 . $latexChar2 . $latexChar3;

			if ($debug) { print STDERR "COLLAPSE combining additive items: $fragment\n"; }

			splice @$latexExpr, $i, 3, $fragment;
			
			$i = -1;

		} elsif (($latexChar2 eq '{') and
		($latexChar4 eq '}')) {
			if ($debug) { print STDERR "COLLAPSE part two\n"; }

			if ($latexChar1 eq '\sqrt') {
				$outerAbstract = 'EXPRESSION:ROOT';

				if ($innerAbstract eq '') {
#					$innerAbstract = ($latexChar3 =~ /^$is_number$/) ? 'LITERAL' : 'SYMBOLIC';
					$firstPass = 1;
					$innerAbstract = (&detexify([$latexChar3], $innerAbstract, $outerAbstract))[1];
				}

				# create '\sqrt{a}' fragment
				if ($match eq 'f') {
					$latexChar3 = &injectAsterixes($latexChar3, $debug);

					if (&isExpression($latexChar3, $outerAbstract, $debug)) {
						if ($debug) { print STDERR "COLLAPSE is expression\n"; }

						$outerAbstract = &Abstraction::compare_outer_abstraction('EXPRESSION', $outerAbstract, $debug);
					}

					$latexChar3 = "($latexChar3)";

					if ($latexChar3 =~ /^\((\w)\)$/) { $latexChar3 = $1; }

					# \sqrt{a} -> (a)^(1/2)
					$fragment = $latexChar3 . '^(1/2)';

				} else {
					$fragment = $latexChar1 . $latexChar2 . $latexChar3 . $latexChar4;
				}

				if ($debug) { print STDERR "COLLAPSE sqrt frag: $fragment, IA: $innerAbstract OA: $outerAbstract\n"; }

				splice @$latexExpr, $i, 4, $fragment;
				$i = -1;

			} elsif ($latexChar1 eq '^') {
#				if ($innerAbstract eq '') {
				$innerAbstract = &Abstraction::compare_inner_abstraction((&isLiteral($latexChar3, $debug) and &isLiteral((split(/[\/\*\+\-\^\_]/, $latexExpr->[$i-1]))[-1], $debug)) ? 'LITERAL' : 'SYMBOLIC', $innerAbstract, $debug);
#				}

				if ($latexExpr->[$i-1] =~ /($trig_terms)/) {
					$outerAbstract = 'EXPRESSION:TRIGONOMETRY';

				} else {
					$outerAbstract = 'EXPRESSION:EXPONENTIAL';
				}

				# create '^{a}', '[]', or '()' fragment
				if (length($latexChar3) == 1) {
					$fragment = $latexChar1 . $latexChar3;

				} else {
					$fragment = $latexChar1 . ($latexChar2 eq '{' ? '(' : $latexChar2) . $latexChar3 . ($latexChar4 eq '}' ? ')' : $latexChar4);
				}

				$fragment =~ s/^\\+(.*)$/$1/;
				
				if ($debug) { print STDERR "COLLAPSE bracket frag: $fragment, IA: $innerAbstract, OA: $outerAbstract\n"; }

				($fragment, $temp_ia, $outerAbstract) = &detexify([$fragment], $innerAbstract, $outerAbstract);
				$innerAbstract = &Abstraction::compare_inner_abstraction($temp_ia, $innerAbstract, $debug);

				if ($debug) { print STDERR "COLLAPSE after bracket: IA: $innerAbstract, OA: $outerAbstract\n"; }

				splice @$latexExpr, $i, 4, $fragment;
				$i = -1;

			} elsif (($latexChar1 eq '\frac') and 
			($latexExpr->[$i+4] eq "{") and
			($latexExpr->[$i+6] eq "}")) {
				# create '\frac{a}{b}' fragment
				#$fragment = &detexify([$latexChar1 . $latexChar2 . $latexChar3 . $latexChar4 . $latexExpr->[$i+4] . $latexExpr->[$i+5] . $latexExpr->[$i+6]]);

				if ($innerAbstract eq '') {
#					if ($latexChar3 =~ /^$is_number$/ and
#					$latexExpr->[$i+5] =~ /^$is_number$/) {
					if ($innerAbstract ne 'LITERAL' and
					&isLiteral($latexChar3, $debug) and
					&isLiteral($latexExpr->[$i+5], $debug)) {
						$innerAbstract = 'LITERAL';

					} else {
						$innerAbstract = 'SYMBOLIC';
					}
				}

				$fragment = '(' . $latexChar3 . ')/(' . $latexExpr->[$i+5] . ')';

				if ($debug) { print STDERR "COLLAPSE frac frag: $fragment, IA: $innerAbstract OA: $outerAbstract\n"; }

				splice @$latexExpr, $i, 7, $fragment;
				$i = -1;

			} elsif (($latexChar1 !~ /^($search_terms)$/) and
			($latexChar1 !~ /^($search_items)$/)) {
				if ($debug) { print STDERR "COLLAPSE not search terms or search items\n"; }

				# create '#()' fragment
				($fragment, $innerAbstract, $outerAbstract) = &detexify([$latexChar1 . "{" . $latexChar3 . "}"], $innerAbstract, $outerAbstract);

				# determine if expression is a set
				if ($fragment =~ /^\\?\{(.*?)\\?\}$/) {
					my $temp1 = $1;
					$outerAbstract = 'SET';

					if ($innerAbstract eq '') {
						if ($temp1 =~ /[a-zA-Z]/ or
						$temp1 eq '') {
							$innerAbstract = 'SYMBOLIC';

						} else {
							$innerAbstract = 'LITERAL';
						}
					}
				}

				if ($debug) { print STDERR "COLLAPSE #() frag: $fragment\n"; }

				splice @$latexExpr, $i, 4, $fragment;
				$i = -1;

			} elsif (($latexChar2 eq '{') and
			($latexChar4 eq '}') and
			($latexChar1 ne '\frac')) {
				$innerAbstract = ($latexChar3 =~ /^$is_number$/) ? 'LITERAL' : 'SYMBOLIC';

				# create '()' fragment
				($fragment, $innerAbstract, $outerAbstract) = &detexify(["(" . $latexChar3 . ")"], $innerAbstract, $outerAbstract);

				if ($debug) { print STDERR "COLLAPSE () frag: $fragment\n"; }

				splice @$latexExpr, $i+1, 3, $fragment;
				$i = -1; 
			}

		} elsif (($latexChar1 eq '\sqrt') and
		($latexChar2 eq "[") and
		($latexChar4 eq "]") and
		($latexExpr->[$i+4] eq "{")) {
			if ($debug) { print STDERR "COLLAPSE part three\n"; }

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

			$firstPass = 1;
			($inner_arg, $innerAbstract, $outerAbstract) = &detexify(&latexplosion($inner_arg), $innerAbstract, $outerAbstract);

			if ($debug) { print STDERR "COLLAPSE inner arg: $inner_arg\n"; }

			splice @$latexExpr, $i+5, $k-$i-5, $inner_arg;

			if ($debug) { print STDERR Dumper($latexExpr); }

			# simplify square root function to exponent
#			if ($match eq 'f') {
			$latexExpr->[$i+5] = &injectAsterixes($latexExpr->[$i+5], $debug);

			if (&isExpression($latexExpr->[$i+5], $outerAbstract, $debug)) {
				$outerAbstract = &Abstraction::compare_outer_abstraction('EXPRESSION', $outerAbstract, $debug);
			}

			$latexExpr->[$i+5] = "($latexExpr->[$i+5])";

			if ($latexExpr->[$i+5] =~ /^\((\w)\)$/) { $latexExpr->[$i+5] = $1; }

			# \sqrt[a]{b} -> (b)^(1/a)
			$fragment = $latexExpr->[$i+5] . '^(1/' . $latexChar3 . ')';

#			} else {
				# create '\sqrt[a]{b}' fragment
#				$fragment = &detexify([$latexChar1 . $latexChar2 . $latexChar3 . $latexChar4 . $latexExpr->[$i+4] . $latexExpr->[$i+5] . $latexExpr->[$i+6]]);
#			}

			if ($debug) {
				print STDERR "COLLAPSE sqrt[] frag: $fragment\n";
				print STDERR "COLLAPSE after match check: $latexExpr->[$i]\n";
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
				($fragment, $innerAbstract, $outerAbstract) = &detexify(["($latexChar2)"], $innerAbstract, $outerAbstract);
				
				if ($debug) { print STDERR "COLLAPSE () frag: $fragment\n"; }

				splice (@$latexExpr, $i, 3, $fragment);
				$i = -1;
			}

		} elsif (($latexChar1 eq '^') and
		($latexChar2 !~ /^($search_terms)$/) and
		($latexChar2 !~ /^($search_items)$/) and
		($latexExpr->[$i-1] !~ /^($search_terms)$/)) {
			# create '^a' fragment
			if ($latexChar2 ne '(') {
				($fragment, $innerAbstract, $outerAbstract) = &detexify([$latexChar1 . "(" . $latexChar2 . ")"], $innerAbstract, $outerAbstract);
			
				if ($debug) { print STDERR "COLLAPSE ^a fragment: $fragment\n"; }

				splice (@$latexExpr, $i, 2, $fragment);

			} elsif (($latexChar2 eq '(') and
			$latexChar4 and
			($latexChar4 eq ')')) {
				($fragment, $innerAbstract, $outerAbstract) = &detexify([$latexChar1 . $latexChar2 . $latexChar3 . $latexChar4], $innerAbstract, $outerAbstract);

				if ($debug) { print STDERR "COLLAPSE ^(a) fragment: $fragment\n"; }

				splice (@$latexExpr, $i, 4, $fragment);
			}

		} elsif ($latexChar2 =~ /^[_\^][\{\(].*[\)\}]/) {
			$latexChar2 =~ s/\{/(/;
			$latexChar2 =~ s/\}/)/;

			if ($debug) { print STDERR "COLLAPSE ^{a} frag\n"; }

			#create 'a^b' fragment
			($fragment, $temp_ia, $outerAbstract) = &detexify([$latexChar1 . $latexChar2], $innerAbstract, $outerAbstract);

			if ($debug) { print STDERR "COLLAPSE before a^b $latexChar2: IA: $temp_ia, OA: $outerAbstract\n"; }

			if ($temp_ia ne 'LITERAL') {
				if ($latexChar2 =~ /^\^/) {
					$innerAbstract = &Abstraction::compare_inner_abstraction((($latexChar1 =~ /$is_number/) and ($latexChar2 =~ /^\^\($is_number\)$/)) ? 'LITERAL' : 'SYMBOLIC', $temp_ia, $debug);

				} elsif ($latexChar2 =~ /^_/) {
					$innerAbstract = &Abstraction::compare_inner_abstraction($latexChar2 =~ /^_\($is_number\)$/ ? 'LITERAL' : 'SYMBOLIC', $temp_ia, $debug);
				}
			}

			if ($debug) { print STDERR "COLLAPSE a^b frag: $fragment, IA: $innerAbstract\n"; }

			splice @$latexExpr, $i, 2, $fragment;
			$i = -1;

		} elsif (($latexChar1 eq '^' or
		$latexChar1 eq '_') and
		($latexChar2 =~ /\(.*\)/)) {
			# create ^a fragment
			($fragment, $innerAbstract, $outerAbstract) = &detexify([$latexChar1 . $latexChar2], $innerAbstract, $outerAbstract);

			if ($debug) { print STDERR "COLLAPSE split a^b frag: $fragment\n"; }
			
			splice @$latexExpr, $i, 2, $fragment;
			$i = -1;

		} elsif (($latexChar1 eq '{') and
		($latexChar3 eq '}') and
		$latexChar4 and
		($latexChar4 ne '}')) {
			# create a^b fragment
			($fragment, $innerAbstract, $outerAbstract) = &detexify([$latexChar1 . $latexChar2 . $latexChar3 . $latexChar4], $innerAbstract, $outerAbstract);
			
			if ($debug) { print STDERR "COLLAPSE {a}^b frag: $fragment\n"; }

			splice @$latexExpr, $i, 4, $fragment;
			$i = -1;
		
		} elsif (($latexChar1 eq '{') and
		$latexChar4 and
		($latexChar4 eq '}')) {
			if ($debug) { print STDERR "COLLAPSE a, b => ab: $fragment\n"; }

			# "{, a, b, }" => "{a*b}"
			if (($latexChar2 =~ /\d$/) and
			($latexChar3 =~ /^\d/)) {
				($fragment, $innerAbstract, $outerAbstract) = &detexify([$latexChar2 . '*' . $latexChar3], $innerAbstract, $outerAbstract);

			# "{, a, b, }" => "{ab}"
			} else {
				($fragment, $innerAbstract, $outerAbstract) = &detexify([$latexChar2 . $latexChar3], $innerAbstract, $outerAbstract);
			}

			splice @$latexExpr, $i+1, 2, $fragment;
			$i = -1;

		} elsif (($latexChar1 eq '[') and
		($latexChar3 eq ']')) {
			$fragment = "[$latexChar2]";

			if ($latexChar2 =~ /,/) {
				$outerAbstract = 'INTERVAL';
			}

			if ($debug) { print STDERR "COLLAPSE []: $fragment\n"; }

			splice @$latexExpr, $i, 3, $fragment;
			$i = -1;

		} elsif (($latexChar1 =~ /^_\{.*?\}$/) and
		($latexChar2 eq '(')) {
			my $inner_arg = $latexChar3;
			my $delims = 1;
			my $k = $i+3;

			while ($delims > 0) {
				if ($latexExpr->[$k] eq '(') { $delims++; }
				elsif ($latexExpr->[$k] eq ')') { $delims--; }

				if ($delims > 0) {
					$inner_arg .= $latexExpr->[$k];
					$k++;
				}
			}

			($inner_arg, $innerAbstract, $outerAbstract) = &detexify([$inner_arg], $innerAbstract, $outerAbstract);

			if ($debug) { print STDERR "COLLAPSE inner arg: $inner_arg\n"; }

			splice @$latexExpr, $i+2, $k-$i-2, $inner_arg;

		} elsif ($latexChar1 =~ /\\[bp]mod/) {
			if ($debug) { print STDERR "preparing modulus\n"; }

			$innerAbstract = &Abstraction::compare_inner_abstraction(&isLiteral($latexExpr->[$i-1], $debug) ? 'LITERAL' : 'SYMBOLIC', &isLiteral($latexChar2, $debug) ? 'LITERAL' : 'SYMBOLIC', $debug);
			$outerAbstract = 'EXPRESSION:MODULAR';
			$fragment = "mod($latexExpr->[$i-1]," . substr($latexChar2, 1, -1) . ")";

			splice @$latexExpr, $i-1, 3, $fragment;
			$i = -1;

		} elsif (not(($latexChar1 =~ /^($search_items)$/) or
		($latexChar2 =~ /^($search_terms)$/) or
		($latexChar1 =~ /^($search_terms)$/) or
		($latexChar2 =~ /^($search_items)$/)) and
		not($latexChar1 eq '(') and
		not($latexChar2 eq ')')) {
			if ($debug) { print STDERR "COLLAPSE catch-all\n"; }

			if (($latexChar1 =~ /\w$/) and
			($latexChar2 =~ /^\w/) and
			($latexChar2 ne '_')) {
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

			if ($innerAbstract eq '') {
				$innerAbstract = ($latexChar1 =~ /[a-zA-Z]$/ and $latexChar2 =~ /^[_\^]/) ? 'SYMBOLIC' : $innerAbstract;
			}

			$fragment = $latexChar1 . $latexChar2;

			if ($debug) { print STDERR "COLLAPSE combine: $fragment, IA: $innerAbstract OA: $outerAbstract\n"; }

			splice @$latexExpr, $i, 2, $fragment;
			$i = -1;

		} elsif (($latexChar1 eq '(') and
		($latexChar3 eq ')')) {
			if ($latexChar2 =~ /,/) {
				$outerAbstract = 'ORDEREDSET';

				foreach ((split(',', $latexChar2))) {
					$firstPass = 1;
					$innerAbstract = &Abstraction::compare_inner_abstraction((&detexify([$_], $innerAbstract, $outerAbstract))[1], $innerAbstract, $debug);

					if ($innerAbstract eq 'SYMBOLIC') { last; }
				}

			} elsif ($innerAbstract eq '') {
				$innerAbstract = &isLiteral($latexChar2, $debug) ? 'LITERAL' : 'SYMBOLIC';
			}

			$fragment = "($latexChar2)";

			if ($debug) { print STDERR "COLLAPSE sandwiching: $fragment\n"; }

			splice @$latexExpr, $i, 3, $fragment;
			$i = -1;

		} elsif (($latexChar1 eq '(') and
		$latexChar4 and
		($latexChar4 eq ')')) {
			if (($latexChar2 =~ /\d$/) and
			($latexChar3 =~ /^\d/)) {
				$latexChar2 .= '*';

			} elsif ("$latexChar2$latexChar3" =~ /,/) {
				$outerAbstract = 'ORDEREDSET';

				foreach ((split(',', "$latexChar2$latexChar3"))) {
					$firstPass = 1;
					$innerAbstract = &Abstraction::compare_inner_abstraction((&detexify([$_], $innerAbstract, $outerAbstract))[1], $innerAbstract, $debug);

					if ($innerAbstract eq 'SYMBOLIC') { last; }
				}

			} elsif ("$latexChar2$latexChar3" =~ /^(\d+)\/\d+$/) {
				if ($1 eq '1') {
					$outerAbstract = 'EXPRESSION:ROOT';

				} else {
					$outerAbstract = 'EXPRESSION';
				}

				$innerAbstract = 'LITERAL';

			} elsif ("$latexChar2$latexChar3" =~ /^(\d+)\/[a-zA-Z]$/) {
				if ($1 eq '1') {
					$outerAbstract = 'EXPRESSION:ROOT';

				} else {
					$outerAbstract = 'EXPRESSION';
				}

				$innerAbstract = 'SYMBOLIC';

			} elsif ("$latexChar2$latexChar3" =~ /^[a-zA-Z]\/[a-zA-Z]$/) {
				$innerAbstract = 'SYMBOLIC';
				$outerAbstract = 'EXPRESSION';
			}

			$fragment = "(" . $latexChar2 . $latexChar3 . ")";

			# TEMPORARY, to prevent keeping SYMBOLIC:FRACTION
#			if ($fragment =~ /\//) {
#				$outerAbstract = 'EXPRESSION';
#			}

			if ($debug) { print STDERR "COLLAPSE double-decker sandwich: $fragment\n"; }

			splice @$latexExpr, $i, 4, $fragment;
			$i = -1;

		} elsif (($latexChar1 =~ /[\*\)]$/) and
		($latexChar2 =~ /^[\w\d]+$/)) {
			$fragment = $latexChar1 . $latexChar2;

			if ($debug) { print STDERR "COLLAPSE combining single variable: $fragment\n"; }

			splice @$latexExpr, $i, 2, $fragment;
			$i = -1;

		} elsif (($latexChar1 =~ /^($search_terms)$/) and
		($latexChar2 =~ /^\([^\(\)]+?\)$/)) {
			$fragment = $latexChar1 . $latexChar2;

			if ($debug) { print STDERR "COLLAPSE concat function with argument: $fragment\n"; }

			splice @$latexExpr, $i, 2, $fragment;
			$i = -1;
		}
	
		$i += 1;
	}

	if ($debug) { print STDERR "COLLAPSE returning IA: $innerAbstract, OA: $outerAbstract\n"; }

	return $innerAbstract, $outerAbstract;
}
###############################################################################

1;
