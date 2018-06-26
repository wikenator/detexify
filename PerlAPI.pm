package PerlAPI;

use strict;
use warnings;
use Exporter;
use IPC::Open2;
use Data::Dumper;
use vars qw(@ISA @EXPORT @EXPORT_OK %EXPORT_TAGS);

# edit this variable ONLY if you need to call detex from another directory ####
our $detexify_path = '/home/arnold/git_repos/detexify';
our $abstract_path = '/home/arnold/git_repos/math-abstraction';
###############################################################################

@ISA = qw(Exporter);
@EXPORT = ();
@EXPORT_OK = qw(getLatexSplit getSearchItems getLatexTag getSearchTermsTag getLatexConstants getConstantTerms getLatexFunc getSearchTermsFunc getTrigTag getTrigTerms preClean detex abstract expand_expr num_compare verify injectAsterixes removeOuterParens cleanParens unbalancedCharacter condense latexplosion movePi condenseArrayExponents removeArrayBlanks isLiteral isExpression determineOuterAbstract);
%EXPORT_TAGS = (
        DEFAULT => [qw(&detex &expand_expr)],
        All     => [qw(&detex &abstract &expand_expr &num_compare &verify &removeArrayBlanks &condenseArrayExponents &injectAsterixes &removeOuterParens &cleanParens &unbalancedCharacter &condense &latexplosion &movePi)],
	Constants => [qw(getLatexSplit getSearchItems getLatexTag getSearchTermsTag getLatexConstants getConstantTerms getTrigTag getTrigTerms determineOuterAbstract)]
);

our @latexSplit = qw(\{ \} \[ \] \^);
our @latexTag;
our @latexConstants;
our @latexFunc;
our @trigTag;
{
	no warnings 'qw';
	@latexTag = qw(\\overline \\frac \\sqrt \\sinh \\cosh \\tanh \\csch \\coth \\sech \\sin \\cos \\tan \\csc \\cot \\sec \\pi \\log \\ln \\angle \\infty \\gcd \\pmod \\mod \\bmod inf sqrt pi log ln abs #sin #cos #tan #sec #csc #cot #sinh #cosh #tanh #csch #sech #coth #ln #log #angle);
	@latexConstants = qw(\\theta \\pi \\varphi \\phi \\rho \\sigma \\gamma \\Gamma \\beta \\alpha \\epsilon \\beth \\aleph \\omega \\delta \\chi chi delta omega aleph beth epsilon alpha beta theta pi varphi phi rho sigma gamma Gamma #pi);
	@latexFunc = qw(sqrt sinh cosh tanh csch coth sech asin acos atan acsc asec acot log ln abs sin cos tan csc sec cot gcd not overline vector pmod mod bmod #sin #cos #tan #csc #sec #cot #csch #sech #coth #sinh #cosh #tanh #ln #log);
	@trigTag = qw(\\sin \\cos \\tan \\csc \\sec \\cot \\sinh \\cosh \\tanh \\csch \\coth \\sech arcsin arccos arctan arccsc arcsec arccot asin acos atan acsc asec acot #sin #cos #tan #csc #sec #cot #sinh #cosh #tanh #csch #sech #coth #asin #acos #atan #acsc #asec #acot);
}
our $search_items = join('|', @latexSplit);
our $search_terms_tag = join('|', @latexTag);
our $constant_terms = join('|', @latexConstants);
our $search_terms_func = join('|', @latexFunc);
our $trig_terms = join('|', @trigTag);

sub getLatexSplit { return @latexSplit; }
sub getLatexTag { return @latexTag; }
sub getLatexConstants { return @latexConstants; }
sub getLatexFunc { return @latexFunc; }
sub getTrigTag { return @trigTag; }
sub getSearchItems { return $search_items; }
sub getSearchTermsTag {
	$search_terms_tag =~ s/\\/\\\\/g;
	return $search_terms_tag;
}
sub getConstantTerms {
	$constant_terms =~ s/\\/\\\\/g;
	return $constant_terms;
}
sub getSearchTermsFunc {
	$search_terms_func =~ s/\\/\\\\/g;
	return $search_terms_func;
}
sub getTrigTerms {
	$trig_terms =~ s/\\/\\\\/g;
	return $trig_terms;
}
### Standard Data Cleaning for All Procedures #################################
sub preClean {
	my $expr = shift;

	$expr =~ s/(\\[\,\!\s])+/ /g;	# remove tex space (escaped , ! whitespace)
	$expr =~ s/\\\[/\$\$/g;		# remove escaped [
	$expr =~ s/\\\]/\$\$/g;		# remove escaped ]
#	$expr =~ s/\\\{/\(/g;		# remove escaped {
#	$expr =~ s/\\\}/\)/g;		# remove escaped }
	$expr =~ s/\\\$//g;		# remove escaped dollar signs
	$expr =~ s/[\?\$]//g;		# remove punctuation and latex delimiters
	$expr =~ s/\\%/%/g;		# remove backslashes before percent signs
	$expr =~ s/\*\*/\^/g;		# replace python ** with sage ^
	$expr =~ s/(\w)\*(\D)/$1$2/g;	# remove verbose multiplication
	$expr =~ s/\\nobreak//g;	# remove nobreak tags
	$expr =~ s/\\break//g;		# remove break tags
	$expr =~ s/\\displaystyle//g;	# remove displaystyle tags
	$expr =~ s/\\limits//g;		# remove limits tags
	$expr =~ s/\\pounds//g;		# remove pounds tags
	$expr =~ s/\\math(frak|bb|cal|bf)\{(.)\}/$2/g; # remove font-related tags
	$expr =~ s/[dt]frac/frac/g;	# replace \dfrac and \tfrac with \frac
	$expr =~ s/\^(-.)/\^\($1\)/g;	# replace a^-b with a^(-b)
	$expr =~ s/\\left//g;		# remove \left tags
	$expr =~ s/\\right//g;		# remove \right tags
	$expr =~ s/\\break//g;		# remove break tags
	$expr =~ s/\\q?quad(\s+\(\d\))?//g; # remove qquad, quad tags with following reference
	$expr =~ s/\\lbrack/\(/g;	# replace lbrack with (
	$expr =~ s/\\rbrack/\)/g;	# replace rbrack with )
	$expr =~ s/\\[lc]?dots/.../g;	# replace \dots, \ldots, \cdots with ...
	$expr =~ s/\\cdot/*/g;		# replace \cdot with *
	$expr =~ s/\\([gl])eq/\\$1e/g;	# replace \geq and \leq with \ge and \le
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
	our $detexify_path;
        my $detexPath = $detexify_path . '/detex.pl';
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

### Math Object Abstraction ###################################################
sub abstract {
        my $prob = shift;
	my $match = shift;
	my $debug = shift;
	$match = 'f' if not defined $match;
	$debug = 0 if not defined $debug;
	our $abstract_path;
        my $abstractPath = $abstract_path . '/abstract.pl';
#	my $cmd = "$abstractPath" . ($match eq 't' ? " -m t " : "") . ($debug ? " -d " : "");
	my $cmd = "$abstractPath" . ($debug ? " -d " : "");

	my $abstractID = open2(\*pipeRead, \*pipeWrite, "$cmd");

        print pipeWrite "$prob\n";
        close (pipeWrite);

        my $abstractResult = <pipeRead>;
        close (pipeRead);

        waitpid ($abstractID, 0);

        return $abstractResult;
}
###############################################################################

### Clean String of Parentheses ###############################################
sub cleanParens {
	my $expr = shift;
	my $debug = shift;
	$debug = 0 if not defined $debug;
	our $detexify_path;
	my $cleanPath = $detexify_path . '/clean_parens.pl';
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
		if ($debug) { print STDERR "\tAPI:ARRBLANK slice $i: " . $arr->[$i] . "\n"; }

		if ($arr->[$i] ne '0') {
			if (not($arr->[$i]) or ($arr->[$i] eq '')) {
				splice @$arr, $i, 1;
				$arraySize--;

				if ($debug) { print STDERR "\tAPI:ARRBLANK ----------\n"; }
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
		if ($debug) { print STDERR "\tAPI:CONDENSEARR slice $i: " . $arr->[$i] . "\n"; }

		if ($arr->[$i] eq '/') {
			if (($arr->[$i-3] =~ /\^$/) and
			($arr->[$i-2] eq '(') and
			($arr->[$i-1] =~ /\w+/) and
			($arr->[$i+1] =~ /\w+/) and
			($arr->[$i+2] eq ')')) {
				splice @$arr, $i-3, 6, $arr->[$i-3] . $arr->[$i-2] . $arr->[$i-1] . $arr->[$i] . $arr->[$i+1] . $arr->[$i+2];
				$arraySize -= 5;
				$i -= 2;

				if ($debug) { print STDERR "\tAPI:CONDENSEARR ----------\n"; }
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

	$expr =~ s/([\w]+)\s?\((.*?)\)/$1*($2)/g;	# a(x) -> a*(x)
	# run second time for deeper nested expressions
	$expr =~ s/([\w]+)\s?\((.*?)\)/$1*($2)/g;	# a(x) -> a*(x)
	$expr =~ s/(\w[^\*])?([a-zA-Z])\*\((.)\)/$1$2($3)/g;	# f*(x) -> f(x)
	# fix for subscript
	$expr =~ s/_\*/_/g;
	$expr =~ s/([\(\{])(.*?)([\)\}])\s?(#?[\w]+)/$1$2$3*$4/g;  # (x)a -> (x)*a OR {x}a -> {x}*a
	$expr =~ s/([\)\}])([\(\{])/$1*$2/g;                       # )( -> )*(

	if ($debug) { print STDERR "\tAPI:INJECTAST before ab->a*b: $expr\n"; }

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
	# fix previous conversion of constants
	$expr =~ s/([^#])(p\*i)/$1#$2/g;
	$expr =~ s/([^#])(t\*h\*e\*t\*a)/$1#$2/g;
	$expr =~ s/([^#])(p\*h\*i)/$1#$2/g;
	$expr =~ s/([^#])(v\*a\*r\*)#?(p\*h\*i)/$1#$2$3/g;
	$expr =~ s/(#v\*a\*r\*)#?(p\*h\*i)/$1$2/g;
	$expr =~ s/([^#])(r\*h\*o)/$1#$2/g;
	$expr =~ s/([^#])(s\*i\*g\*m\*a)/$1#$2/g;
	$expr =~ s/([^#])(b\*e\*t\*a)/$1#$2/g;
	$expr =~ s/([^#])(b\*e\*t\*h)/$1#$2/g;
	$expr =~ s/([^#])(a\*l\*p\*h\*a)/$1#$2/g;
	$expr =~ s/([^#])(a\*l\*e\*p\*h)/$1#$2/g;
	$expr =~ s/([^#])(o\*m\*e\*g\*a)/$1#$2/g;
	$expr =~ s/([^#])(d\*e\*l\*t\*a)/$1#$2/g;
	$expr =~ s/([^#])(c\*h\*i)/$1#$2/g;
	$expr =~ s/([^#])(e\*p\*s\*i\*l\*o\*n)/$1#$2/g;

	if ($debug) { print STDERR "\tAPI:INJECTAST during ab->a*b 1: $expr\n"; }

	# fix split for pi
	$expr =~ s/#p\*i([\+\-\*\/]?)/pi$1/g;
	$expr =~ s/pi\*$/pi/;
	# fix split for constants
	$expr =~ s/#t\*h\*e\*t\*a([\+\-\*\/]?)/theta$1/g;
	$expr =~ s/theta\*$/theta/g;
	$expr =~ s/#p\*h\*i([\+\-\*\/]?)/phi$1/g;
	$expr =~ s/phi\*$/phi/g;
	$expr =~ s/#v\*a\*r\*p\*h\*i([\+\-\*\/]?)/varphi$1/g;
	$expr =~ s/varphi\*$/varphi/g;
	$expr =~ s/#r\*h\*o([\+\-\*\/]?)/rho$1/g;
	$expr =~ s/rho\*$/rho/g;
	$expr =~ s/#s\*i\*g\*m\*a([\+\-\*\/]?)/sigma$1/g;
	$expr =~ s/sigma\*$/sigma/g;
	$expr =~ s/#([Gg])\*a\*m\*m\*a([\+\-\*\/]?)/$1amma$2/g;
	$expr =~ s/([Gg])amma\*$/$1amma/g;
	$expr =~ s/#b\*e\*t\*a([\+\-\*\/]?)/beta$1/g;
	$expr =~ s/beta\*$/beta/g;
	$expr =~ s/#b\*e\*t\*h([\+\-\*\/]?)/beth$1/g;
	$expr =~ s/beth\*$/beth/g;
	$expr =~ s/#a\*l\*p\*h\*a([\+\-\*\/]?)/alpha$1/g;
	$expr =~ s/alpha\*$/alpha/g;
	$expr =~ s/#a\*l\*e\*p\*h([\+\-\*\/]?)/aleph$1/g;
	$expr =~ s/aleph\*$/aleph/g;
	$expr =~ s/#o\*m\*e\*g\*a([\+\-\*\/]?)/omega$1/g;
	$expr =~ s/omega\*$/omega/g;
	$expr =~ s/#d\*e\*l\*t\*a([\+\-\*\/]?)/delta$1/g;
	$expr =~ s/delta\*$/delta/g;
	$expr =~ s/#c\*h\*i([\+\-\*\/]?)/chi$1/g;
	$expr =~ s/chi\*$/chi/g;
	$expr =~ s/#e\*p\*s\*i\*l\*o\*n([\+\-\*\/]?)/epsilon$1/g;
	$expr =~ s/epsilon\*$/epsilon/g;
	$expr =~ s/($constant_terms)\*?\(/$1(/g;

	## TEMP split into 4 sections, werx for now
	# fix split for log/ln
	if ($expr =~ /#l\*o\*g\*?(^\(?.+?\)?)\*(\(.+?\))/) {
		if ($debug) { print STDERR "\tAPI:INJECTAST log 1\n"; }

		$expr =~ s/#l\*o\*g\*?(^\(?.+?\)?)\*(\(.+?\))/log$1$2/g;

	} elsif ($expr =~ /#l\*n\*?(^\(?.+?\)?)\*(\(.+?\))/) {
		if ($debug) { print STDERR "\tAPI:INJECTAST ln 1\n"; }

		$expr =~ s/#l\*n\*?(^\(?.+?\)?)\*(\(.+?\))/ln$1$2/g;

	} elsif ($expr =~ /#l\*o\*g\*?(_\(?.+?\)?)\*(\(.+\))/) {
		if ($debug) { print STDERR "\tAPI:INJECTAST log 2\n"; }

		$expr =~ s/#l\*o\*g\*?(_\(?.+?\)?)\*(\(.+\))/log$1$2/g;

	} elsif ($expr =~ /#l\*n\*?(_\(?.+?\)?)\*(\(.+\))/) {
		if ($debug) { print STDERR "\tAPI:INJECTAST ln 2\n"; }

		$expr =~ s/#l\*n\*?(_\(?.+?\)?)\*(\(.+\))/ln$1$2/g;

	} elsif ($expr =~ /#l\*o\*g\*?([_\^]\(?.+?\)?)([_\^]\(?.+?\)?)\*(\(?.+\)?)/) {
		if ($debug) { print STDERR "\tAPI:INJECTAST log 3\n"; }

		my $temp3 = $3;

		if ($temp3 !~ /^\(.+\)$/) { $temp3 = "($temp3)"; }

		$expr =~ s/#l\*o\*g\*?([_\^]\(?.+?\)?)([_\^]\(?.+?\)?)\*\(?.+\)?/log$1$2$temp3/g;

	} elsif ($expr =~ /#l\*n\*?([_\^]\(?.+?\)?)([_\^]\(?.+?\)?)\*(\(?.+\)?)/) {
		if ($debug) { print STDERR "\tAPI:INJECTAST ln 3\n"; }

		my $temp3 = $3;

		if ($temp3 !~ /^\(.+\)$/) { $temp3 = "($temp3)"; }

		$expr =~ s/#l\*n\*?([_\^]\(?.+?\)?)([_\^]\(?.+?\)?)\*\(?.+\)?/ln$1$2$temp3/g;

	} elsif ($expr =~ /#l\*o\*g\*?(\(.+\))/ or
	$expr =~ /#l\*o\*g\*?([^\+\-\*\/]+)/) {
		if ($debug) { print STDERR "\tAPI:INJECTAST log 4\n"; }

		my $temp1 = $1;

		if ($temp1 !~ /^\(.+\)$/) { $temp1 = "($temp1)"; }

		$expr =~ s/#l\*o\*g\*?(\(?.+\)?)/log$temp1/g;

	} elsif ($expr =~ /#l\*n\*?(\(.+\))/ or
	$expr =~ /#l\*n\*?([^\+\-\*\/]+)/) {
		if ($debug) { print STDERR "\tAPI:INJECTAST ln 4\n"; }

		my $temp1 = $1;

		if ($temp1 !~ /^\(.+\)$/) { $temp1 = "($temp1)"; }

		$expr =~ s/#l\*n\*?(\(?.+\)?)/ln$temp1/g;
	}

	if ($debug) { print STDERR "\tAPI:INJECTAST ln/log fix: $expr\n"; }

	# fix split for ln
#       $detexExpr =~ s/#l\*n\*?(\()/ln$1/g; 
	# fix split for (arc/hyperbolic) trig 
	$expr =~ s/#(((a?)\*?))([sct])\*([aieos])\*([cnst])\*?(h?)\*?((\^-?\d+)?)\*?\(/$3$4$5$6$7$8(/g;
	$expr =~ s/#(((a?)\*?))([sct])\*([aieos])\*([cnst])\*?(h?)\*?((\^[\(\{][\w\-\+\*\/]+[\)\}])?)\*?\(/$3$4$5$6$7$8(/g;
	# fix split for trig 
#       $detexExpr =~ s/#([sct])\*([aieo])\*([cnst])\*?(\^\(?\d+\)?)?\*?(\()/$1$2$3$4$5/g;
	# fix split for sqrt
	$expr =~ s/s\*q\*r\*t\*?\(/sqrt\(/g;
	# fix split for abs
	$expr =~ s/a\*b\*s\*?\(/abs\(/g;
	# fix split for emptyset
	$expr =~ s/#e\*m\*p\*t\*y\*#?s\*e\*t/emptyset/g;
	# fix split for infinity
	$expr =~ s/i\*n\*f/inf/g;
	# fix split for null
	$expr =~ s/n\*u\*l\*l/null/g;
	# fix split for angle
	$expr =~ s/a\*n\*g\*l\*e\*?/angle /g;
	# fix split for gcd
	$expr =~ s/g\*c\*d\*?\(/gcd(/g;
	# fix split for mod
	$expr =~ s/m\*o\*d\*?\(/mod(/g;
	# fix split for overline
	$expr =~ s/o\*v\*e\*r\*l\*i\*n\*e\*?\(/not(/g;
	# fix split for operatorname
	$expr =~ s/o\*p\*e\*r\*a\*t\*o\*r\*n\*a\*m\*e\*?//g;
	# fix split for curl
	$expr =~ s/\(?c\*u\*r\*l\)?\*?/curl/g;
	# fix split for div
	$expr =~ s/\(?d\*i\*v\)?\*?/div/g;
	# fix split for vector notation
	$expr =~ s/o\*v\*e\*r\*#?set\(h\*a\*r\*p\*o\*o\*n\*u\*p\)\*\{([abcijkABCIJKF]|sigma)\}/vector($1)/g;
	$expr =~ s/vector\(sigma\)\*\(t\)/vector(sigma(t))/g;

	if ($debug) { print STDERR "\tAPI:INJECTAST during ab->a*b 2: $expr\n"; }

	$expr = &movePi($expr, $debug);

	# replace * before log and ln
	$expr =~ s/([\w\)])(log|ln)/$1*$2/g;

	### complete trig expression handling here
#       $detexExpr =~ s/([^(sin|cos|tan|csc|cot|sec|du|dv|-|\+|\*|\/)])([^(sin|cos|tan|csc|cot|sec|du|dv|^)])/$1*$2/g;  # ab -> a*b

	if ($debug) { print STDERR "\tAPI:INJECTAST after ab->a*b: $expr\n"; }

	# remove ending periods
	$expr =~ s/([^\.][^\.])\.$/$1/g;

	# clean unnecessary parentheses from expression
	$expr = &cleanParens($expr, $debug);

	if ($debug) { print STDERR "\tAPI:INJECTAST after paren cleaning 1: $expr\n"; }

	my $mid_expr;
	my $balanced = 1;

	if (&unbalancedCharacter(substr($expr, 1, -1), '{', '}', $debug) != 0 or
	&unbalancedCharacter(substr($expr, 1, -1), '(', ')', $debug) != 0) {
		$mid_expr = $expr;
		$balanced = 0;

	} else {
		$mid_expr = substr $expr, 1, -1;
	}

	if ($mid_expr =~ /[\{\}]/g) {
		$mid_expr =~ s/\{/(/g;  # replace curly braces with parentheses
		$mid_expr =~ s/\}/)/g;  # replace curly braces with parentheses

		# clean unnecessary parentheses from expression after bracket to parenthesis conversion
		if ($balanced) {
			$expr = substr($expr, 0, 1) . &cleanParens($mid_expr, $debug) . substr($expr, -1, 1);
		}

		if ($debug) { print STDERR "\tAPI:INJECTAST after paren cleaning 2: $expr\n"; }
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

	if ($expr =~ /a?(ln|log|cosh|sinh|tanh|csch|sech|coth|cos|sin|tan|csc|sec|cot)\^\(?-?\d+\)?\(.*?\)\^/) {
		$expr =~ s/(a?)(ln|log|cosh|sinh|tanh|csch|sech|coth|cos|sin|tan|csc|sec|cot)(\^\(?-?\d+\)?)(\(.*?\))/($1$2$4$3)/g;

	} else {
		$expr =~ s/(a?)(ln|log|cosh|sinh|tanh|csch|sech|coth|cos|sin|tan|csc|sec|cot)(\^\(?-?\d+\)?)(\(.*?\))/$1$2$4$3/g;
	}

	$expr =~ s/(a?)(ln|log|cosh|sinh|tanh|csch|sech|coth|cos|sin|tan|csc|sec|cot)(\^\(?-?\d+\)?)(.)/$1$2($4)$3/g;
	$expr =~ s/(a?)(ln|log|cosh|sinh|tanh|csch|sech|coth|cos|sin|tan|csc|sec|cot)(\(.*?\))\^\((\d)\)/$1$2$3^$4/g;

	if ($debug) { print STDERR "\tAPI:INJECTAST after trig exponent move: $expr\n"; }

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

		} elsif (grep(/^.+?#/, $subExpr->[$i])) {
			@fragment = split(/#/, $subExpr->[$i]);
			splice (@$subExpr, $i, 0, $fragment[0]);
			splice (@$subExpr, $i+1, 1, "#$fragment[1]");
		}
	}

	if ($debug) {
		print STDERR "\tAPI:PLOSION before blank removal: ";
		print STDERR Dumper($subExpr);
	}

	$subExpr = &removeArrayBlanks($subExpr, $debug);

	if ($debug) {
		print STDERR "\tAPI:PLOSION after blank removal: ";
		print STDERR Dumper($subExpr);
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
				if ($debug) { print STDERR "\tAPI:MOVEPI move pi 1: $1\n"; }
	
				$expr =~ s/(pi)\*(\(.*?\)\^\(.*?\)\*?)/$2*$1/g;
	
			# pi*(a)^{b} -> (a)^{b}*pi
			} elsif ($expr =~ /pi\*(\([^\+\-\(\)]\)\^\{.*?\})/) {
				if ($debug) { print STDERR "\tAPI:MOVEPI move pi 2: $1\n"; }
	
				$expr =~ s/(pi)\*(\(.*?\)\^\{.*?\})/$2*$1/g;
	
			# pi*a^b -> a^b*pi
			} elsif ($expr =~ /pi\*([^\+\-\(\)]+\^\{.*?\})/) {
				if ($debug) { print STDERR "\tAPI:MOVEPI move pi 3: $1\n"; }
	
				$expr =~ s/(pi)\*([^\+\-\(\)]+\^\{.*?\})/$2*$1/g;

			# pi*(a) -> (a)*pi
			} elsif ($expr =~ /pi\*(\([^\+\-\(\)]\)\*?)/) {
				if ($debug) { print STDERR "\tAPI:MOVEPI move pi 4: $1\n"; }

				$expr =~ s/(pi)\*(\(.*?\)\*?)/$2*$1/g;
	
			# pi*a -> a*pi
			} elsif ($expr =~ /pi\*([^\+\-\(\)]+\*?)/) {
				my $temp_results = $1;

				if ($debug) { print STDERR "\tAPI:MOVEPI move pi 5: $1\n"; }

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

	if ($debug) { print STDERR "\tAPI:REMOVEOUTER outer: $outerExpr\n"; }

	$innerExpr =~ s/^\((.*?)\)$/$1/;

	if ($debug) { print STDERR "\tAPI:REMOVEOUTER inner: $innerExpr\n"; }

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

        if ($debug) { print STDERR "\tAPI:CONDENSE before condense: $num\n"; }

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

### Determine if string is a literal ##########################################
sub isLiteral {
	my $expr = shift;
	my $debug = shift;
	my $is_number = '-?(\d{1,3}\,?)+(\.\d+)?';

	if ($expr =~ /^[\(\{]?$is_number[\)\}]?(\\?%)?$/ or
	$expr =~ /^-?\(?-?\d*\.?\d+\)?\/\(?\d*\.?\d+\)?(\\?%)?$/ or
	$expr =~ /^\(?-?\d+\)?\^\(?($is_number|\d+\/\d+|\d+)\)?$/ or
	$expr =~ /^\(?$is_number\)?$/) {
		return 1;
	}

	return 0;
}
###############################################################################

### Determine if string is an expression ######################################
sub isExpression {
	my $expr = shift;
	my $oa = shift;
	my $debug = shift;

	if ((split(':', $oa))[0] and
	(split(':', $oa))[0] eq 'FRACTION' and
	$expr =~ /^[\da-zA-Z]+\+[\da-zA-Z]+\/[\da-zA-Z]+(\\?\%)?$/) {
		return 0;
	}

	if ($debug) { print STDERR "\tAPI:ISEXPR determining if expression: $expr\n"; }

	if ($expr =~ /[+\*]/) {
		if ($debug) { print STDERR "\tAPI:ISEXPR is expression\n"; }

		return 1;

	} elsif ($expr =~ /[\w\d]-[\w\d]/ or
	$expr =~ /[\w\d]\)?-\(?[\w\d]/) {
		if ($debug) { print STDERR "\tAPI:ISEXPR operator found\n"; }

		return 1;

#	} elsif ($expr =~ /\//) {
#		if ($debug) { print STDERR "checking division\n"; }

#		if ($expr !~ /\^\(?-?.\/.\)?/ or
#		$expr !~ /[^\^]\(?-?.\/.\)?/) {
#			return 1;
#		}
	}

	return 0;
}
###############################################################################

### Determine outer abstraction based on function or tag ######################
sub determineOuterAbstract {
	my $expr = shift;
	my $debug = shift;

	if ($expr =~ /(log|ln)/) {
		return 'EXPRESSION:LOGARITHM';

	} elsif ($expr =~ /($trig_terms)/) {
		return 'EXPRESSION:TRIGONOMETRY';
	}
}
###############################################################################

1;
