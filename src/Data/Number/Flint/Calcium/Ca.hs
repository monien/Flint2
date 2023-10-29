{-|
module      :  Data.Number.Flint.Calcium.Ca
copyright   :  (c) 2023 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de

== Exact real and complex numbers

A @Ca@ represents a real or complex number in a form suitable for
exact field arithmetic or comparison. Exceptionally, a @Ca@ may
represent a special nonnumerical value, such as an infinity.

== Introduction: numbers 

A /Calcium number/ is a real or complex number represented as an element
of a formal field \(K = \mathbb{Q}(a_1, \ldots, a_n)\) where the 
symbols \(a_k\) denote fixed algebraic or transcendental numbers called
/extension numbers/. For example, \(e^{\,- 2 \pi} - 3i\) may be
represented as \((1 - 3 a_2^2 a_1) / a_2^2\) in the
field \(\mathbb{Q}(a_1,a_2)\) with \(a_1 = i, a_2 = e^{\pi}\). 
Extension numbers
and fields are documented in the following separate modules:

The user does not need to construct extension numbers or formal
extension fields explicitly: each @Ca@ contains an internal pointer to
its formal field, and operations on Calcium numbers generate and cache
fields automatically as needed to express the results.

This representation is not canonical (in general). A given complex
number can be represented in different ways depending on the choice of
formal field /K/. Even within a fixed field /K/, a number can have
different representations if there are algebraic relations between the
extension numbers. Two numbers /x/ and /y/ can be tested for inequality
using numerical evaluation; to test for equality, it may be necessary to
eliminate dependencies between extension numbers. One of the central
goals of Calcium will be to implement heuristics for such elimination.

Together with each formal field /K/, Calcium stores a /reduction ideal/
 \(I = \{g_1,\ldots,g_m\}\) with \(g_i \in \mathbb{Z}[a_1,\ldots,a_n]\),
defining a set of algebraic relations \( g_i(a_1,\ldots,a_n) = 0\). Relations
can be absolute, say \(g_i = a_j^2 + 1\), or relative, say
 \(g_i = 2 a_j - 4 a_k - a_l a_m\). The reduction ideal effectively
partitions \(K\) into equivalence classes of complex numbers (e.g.
 \(i^2 = -1\) or \(2 \log(\pi i) = 4 \log(\sqrt{\pi}) + \pi i\)),
enabling simplifications and equality proving.

Extension numbers are always sorted
 \(a_1 \succ a_2 \succ \ldots \succ a_n\) where \(\succ\) denotes a
structural ordering (see @ca_cmp_repr@). If the reduction ideal is
triangular and the multivariate polynomial arithmetic uses lexicographic
ordering, reduction by /I/ eliminates numbers \(a_i\) with higher
complexity in the sense of \(\succ\).

The reduction ideal is an imperfect computational crutch: it is not
guaranteed to capture /all/ algebraic relations, and reduction is not
guaranteed to produce uniquely defined representatives. However, in the
specific case of an absolute number field \(K = \mathbb{Q}(a)\) where
/a/ is a @qqbar_t@ extension, the reduction ideal (consisting of a
single minimal polynomial) is canonical and field elements of /K/ can be
chosen canonically.

== Introduction: special values

In order to provide a closed arithmetic system and express limiting
cases of operators and special functions, a @Ca@ can hold any of the
following special values besides ordinary numbers:

The distinction between /Calcium numbers/ (which must represent elements
of \(\mathbb{C}\)) and the different kinds of nonnumerical values
(infinities, Undefined or Unknown) is essential. Nonnumerical values may
not be used as field extension numbers \(a_k\), and the denominator of a
formal field element must always represent a nonzero complex number.
Accordingly, for any given Calcium value /x/ that is not /Unknown/, it
is exactly known whether /x/ represents A) a number, B) unsigned
infinity, C) a signed infinity, or D) Undefined.
-}
module Data.Number.Flint.Calcium.Ca (
  module Data.Number.Flint.Calcium.Ca.FFI
  ) where
  
import GHC.Exts
import Data.Number.Flint.Calcium.Ca.FFI
