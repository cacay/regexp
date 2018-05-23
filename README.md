# regexp

[![Build Status](https://travis-ci.com/cacay/regexp.svg?branch=master)](https://travis-ci.com/cacay/regexp)

This is a regular expression library for Haskell that focuses on higher level
operations like computing the intersection of regular expressions or deciding
whether two regular expressions match the same set of strings. This is in stark
contrast to pretty much every single regular expression library out there (including
ones for other languages), which are only concerned with matching strings. Unfortunately,
deprioritizing string matching means it isn't very efficient, so if that's all you need,
you should use a different library.

Here is a summary of supported features:
* Intersection and complement
* Derivatives à la [Brzozowski](https://en.wikipedia.org/wiki/Brzozowski_derivative)
* Equivalence checking
* Solving systems of linear equations with regular expression coefficients
  (which can be used to implement intersection, complement, and more)
* Arbitrary alphabets, even infinite ones!


## Usage and Development

We use [Stack](https://docs.haskellstack.org) so it's pretty much
trivial to get started. If you don't have Stack already,
[install](https://docs.haskellstack.org/en/stable/README/#how-to-install)
it and set it up by running 
```shell
stack setup
```
in your shell. You only need to do this once. Then, you can run
```shell
stack repl
```
to be dropped in GHCi where you can play around with the library. This will
install all dependencies, build the library, and do whatever is necessary so
everything "Just Works™".
```shell
stack haddock --open regexp
```
will open the documentation in your browser and
```shell
stack test
```
will run the test suite.

Stack is all about reproducible builds, so you should not run into any issues.


## Examples

Load up the library in GHCi:
```shell
stack repl
```

### Creating Regular Expressions

The simplest regular expressions are `rZero`, which matches no strings, and
`rOne`, which matches only the empty string. You can combine regular expressions
using `rPlus` and `rTimes` (choice and sequencing). Kleene star is implemented
by `rStar`. For example:
```haskell
rOne
rStar rZero
rOne `rTimes` (rZero `rPlus` rOne)
```
are all valid expressions, though they are boring since they are all equivalent to
`rOne`. More interesting expressions can be constructed using _character
classes_. Standard Haskell string notation is interpreted as a character class
containing all characters in the string. For example,
```haskell
"abc" :: RegExp Char
```
is the (regular expression formed by) the character class containing the characters
`a`, `b`, and `c`. This expression will match single character strings `"a"`, `"b"`,
and `"c"` and nothing else. Note that the type annotation is required for Haskell
to interpret the string as a regular expression.


### String Matching

We can check that this is indeed how character classes behave by trying to match them
against strings:
```haskell
matches ("abc" :: RegExp Char) "a"
==> True

matches ("abc" :: RegExp Char) "ab"
==> False

matches (rStar "abc" :: RegExp Char) "ab"
==> True
```


### Checking Equivalence

We can check if two regular expressions are equivalent and get a counter example
in the case they are not:
```haskell
equivalent ("abc" :: RegExp Char) ("abc" `rPlus` rZero) 
==> Right ()

equivalent ("abc" :: RegExp Char) ("ab") 
==> Left "c"

equivalent (rStar "abc" :: RegExp Char) ("abc" `rTimes` rStar "abc") 
==> Left ""
```


### Intersection and Complement

We can compute intersections and complements:
```haskell
intersection (rStar "ab" :: RegExp Char) (rStar "a") 
==> rStar "a"

intersection (rStar "a" :: RegExp Char) (RegExp.Operations.complement $ rStar "a") 
==> rZero
```
