# Regexp

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
trivial to get started. After installing Stack, simply run
```shell
stack repl
```
to be dropped in GHCi where you can play around with the library. This will
install all dependencies, build the library, and do whatever is necessary so
everything "Just Works (TM)".
```shell
stack hoddock --open regexp
```
will open the documentation in your browser and
```shell
stack test
```
will run the test suite.
