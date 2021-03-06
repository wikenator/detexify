# DeTeXify
DeTeXify removes LaTeX and TeX tags from an input string and returns a computer-evaluatable string.

[Live Demo Here](https://www.wireandkloudready.com/wkrcp/detexifier.php "Live Demo")

## Configuration
In order to call the main detex.pl file from locations other than the root directory of this repository, you may need to update the `use lib` statements in `detex.pl` and `clean_parens.pl`, as well as the `detexify_path` variable in `PerlAPI.pm`.

## Usage
```
./detex.pl [--debug | -d] [--match=<f | t> | -m <f | t>]
```

`--debug | -d` activates debugging output.

`--match=<f | t> | -m <f | t>` activates the "match" option (described below).

### Command Line
Execute detex.pl in the detexify folder, then input your LaTeX or TeX string on the command line. Press enter and watch for your detexified string.
```
> ./detex.pl
\frac{1}{2}
1/2
> 
```

You can also supply a "match" option (either "t" or "f", symbolizing "true" or "false" respectively) after your input with a `-m` or `--match` option. This is currently only used for DeTeXifying square root commands. A "match" option of false is the default behavior for detex.pl.
```
> ./detex.pl
\sqrt{2}
2^(1/2)
>
> ./detex.pl --match=f
\sqrt{2}
2^(1/2)
> 
> ./detex.pl -m t
\sqrt{2}
sqrt(2)
>
```

### Piping from Other Programs
You can open detex.pl as a pipe from another program, regardless of what language the calling program is written in. You just need to write your LaTeX or TeX string to detex.pl once a pipe is open, and then read the result string from detex.pl before closing the pipe.

## Example Conversions:
- \\frac{1}{2} => 1/2
- \\sqrt{2} => 2^(1/2)
- \\frac{x+y}{3} => (x+y)/3

### DeTeXify currently handles the following LaTeX and TeX tags with infinite recursion (conversion):
- \\frac{a}{b} => a/b
- \\sqrt{a} => a^(1/2)
- \\sqrt[a]{b} => b^(1/a)
- a^-b => a^(-b)
- \\ln(a), \\log(b) => ln(a), log(b)
- trigonometric functions (regular, inverse, and hyperbolic) e.g. \sin(a) => sin(a)
- \\abs(a) => abs(a)
- \\lbrack, \\rbrack => [, ]
- \\pi => pi
- \\infty => inf
- \\emptyset => null
- \\exp(a) => e^a
- \\% => %
- \\[, \\] => $$
- \\{, \\} => (, )
- a**b => a^b

### DeTeXify currently handles the following LaTeX and TeX tags (removal):
- \\break
- \\displaystyle
- \\left, \\right
- \\circ
- \\operatorname
- \\immediate
- \\write18
- \\write
- \\$
- leading and trailing spaces
