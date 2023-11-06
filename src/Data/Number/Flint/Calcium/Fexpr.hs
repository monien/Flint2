{-|
module      :  Data.Number.Flint.Calcium.Fexpr
copyright   :  (c) 2023 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

This module supports working with symbolic expressions.

== Introduction

Formally, a symbolic expression is either:

* An atom being one of 

     * An integer, for example 0 or -34.
     * A symbol, for example x, Mul, SomeUserNamedSymbol. 
     Symbols should be valid C identifiers (containing 
     only the characters A-Z, a-z, 0-9, _, and not starting with a digit).

     * A string, for example "Hello, world!". For the moment, we only 
     consider ASCII strings, but there is no obstacle in principle 
     to supporting UTF-8.

* A non-atomic expression, \(e_0(e_1,e_2,\ldots e_n)\) 
representing a function call where \((e_1,\ldots,e_n)\) are 
symbolic expressions.

The meaning of an expression depends on the interpretation of symbols
in a given context. For example, with a standard interpretation (used
within Calcium) of the symbols @Mul@, @Add@ and @Neg@, the expression
@Mul(3, Add(Neg(x), y))@ encodes the formula \(3 \cdot ((-x)+y)\)
where @x@ and @y@ are symbolic variables. See @fexpr-builtin@ for
documentation of builtin symbols.

== Computing and embedding data 

Symbolic expressions are usually not the best data structure to use
directly for heavy-duty computations. Functions acting on symbolic
expressions will typically convert to a dedicated data structure (e.g.
polynomials) internally and (optionally) convert the final result back
to a symbolic expression.

Symbolic expressions do not allow embedding arbitrary binary objects
such as Flint\/Arb\/Antic\/Calcium types as atoms. This is done on
purpose to make symbolic expressions easy to use as a data exchange
format. To embed an object in an expression, one has the following
options:

* Represent the object structurally using atoms supported natively by
symbolic expressions (for example, an integer polynomial can be
represented as a list of coefficients or as an arithmetic expression
tree).

* Introduce a dummy symbol to represent the object, maintaining an
external translation table mapping this symbol to the intended value.

* Encode the object using a string or symbol name. This is generally
not recommended, as it requires parsing; properly used, symbolic
expressions have the benefit of being able to represent the parsed
structure.

== Flat-packed representation

Symbolic expressions are often implemented using trees of pointers
(often together with hash tables for uniqueness), requiring some form of
memory management. The @fexpr_t@ type, by contrast, stores a symbolic
expression using a \"flat-packed\" representation without internal
pointers. The expression data is just an array of words (@ulong@). The
first word is a header encoding type information (whether the expression
is a function call or an atom, and the type of the atom) and the total
number of words in the expression. For atoms, the data is stored either
in the header word itself (small integers and short symbols\/strings) or
in the following words. For function calls, the header is followed by
the expressions \(e_0\), ..., \(e_n\) packed contiguously in memory.

Pros:

* Memory management is trivial.

* Copying an expression is just copying an array of words.

* Comparing expressions for equality is just comparing arrays of words.

* Merging expressions is basically just concatenating arrays of words.

*Expression data can be shared freely in binary form between threads
and even between machines (as long as all machines have the same word
size and endianness).  

Cons:

* Repeated instances of the same subexpression cannot share memory (a
workaround is to introduce local dummy symbols for repeated
subexpressions).

* Extracting a subexpression for modification generally requires
making a complete copy of that subxepression (however, for read-only
access to subexpressions, one can use “view” expressions which have
zero overhead).

* Manipulating a part of an expression generally requires rebuilding the whole expression.

* Building an expression incrementally is typically
 \(O\left(n^2\right)\). As a workaround, it is a good idea to work with
balanced (low-depth) expressions and try to construct an expression in
one go (for example, to create a sum, create a single Add expression
with many arguments instead of chaining binary Add operations).

-}
module Data.Number.Flint.Calcium.Fexpr (
  module Data.Number.Flint.Calcium.Fexpr.FFI
  ) where
  
import Data.Number.Flint.Calcium.Fexpr.FFI
