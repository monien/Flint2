{-|
module      :  Data.Number.Flint.Hypgeom
copyright   :  (c) 2022 Hartmut Monien
license     :  GNU GPL, version 2 or above (see LICENSE)
maintainer  :  hmonien@uni-bonn.de  

== Support for hypergeometric series

This module provides functions for high-precision evaluation of series
of the form

\[
  \sum_{k=0}^{n-1} \frac{A(k)}{B(k)} \prod_{j=1}^k \frac{P(k)}{Q(k)} z^k
\]

where \(A, B, P, Q\) are polynomials. The present version only supports
A, B, P, Q in mathbb{Z}[k] (represented using the FLINT /fmpz_poly_t/
type). This module also provides functions for high-precision evaluation
of infinite series (n to infty), with automatic, rigorous error
bounding.

Note that we can standardize to \(A = B = 1\) by
setting \(\tilde P(k) = P(k) A(k) B(k-1), \tilde Q(k) = Q(k) A(k-1) B(k)\).
However, separating out \(A\) and \(B\) is convenient and improves
efficiency during evaluation.

== Strategy for error bounding 

We wish to evaluate \(S(z) = \sum_{k=0}^{\infty} T(k) z^k\) where \(T(k)\) 
satisfies \(T(0) = 1\) and

\[
  T(k) = R(k) T(k-1) = \left( \frac{P(k)}{Q(k)} \right) T(k-1)
\]

for given polynomials

\[\begin{align}
  P(k) &= a_p k^p + a_{p-1} k^{p-1} + \ldots a_0\\
  Q(k) &= b_q k^q + b_{q-1} k^{q-1} + \ldots b_0.
\end{align}\]

For convergence, we require \(p < q\), or \(p = q\) with \(|z| |a_p| < |b_q|\).
We also assume that \(P(k)\) and \(Q(k)\) have no
roots among the positive integers (if there are positive integer roots,
the sum is either finite or undefined). With these conditions satisfied,
our goal is to find a parameter \(n \ge 0\) such that

\[
  {\left\lvert \sum_{k=n}^{\infty} T(k) z^k \right\rvert} \le 2^{\\-d}.
\]

We can rewrite the hypergeometric term ratio as

\[
  \[z R(k) = z \frac{P(k)}{Q(k)} =
  z \left( \frac{a_p}{b_q} \right) \frac{1}{k^{q-p}} F(k)
\]

where

\[
  F(k) = \frac{
  1 + \tilde a_{1} / k + \tilde a_{2} / k^2 + \ldots + \tilde a_q / k^p
  }{
  1 + \tilde b_{1} / k + \tilde b_{2} / k^2 + \ldots + \tilde b_q / k^q
  } = 1 + O(1/k)
\]

and where \(\tilde a_i = a_{p-i} / a_p\), \(\tilde b_i = b_{q-i} / b_q\). 
Next, we define

\[
  C = \max_{1 \le i \le p} |\tilde a_i|^{(1/i)},
  \quad D = \max_{1 \le i \le q} |\tilde b_i|^{(1/i)}.
\]

Now, if \(k > C\), the magnitude of the numerator of \(F(k)\) is bounded
from above by

\[
  1 + \sum_{i=1}^p \left(\frac{C}{k}\right)^i \le 1 + \frac{C}{k-C}
\]

and if \(k > 2D\), the magnitude of the denominator of \(F(k)\) is
bounded from below by

\[
  1 - \sum_{i=1}^q \left(\frac{D}{k}\right)^i \ge 1 + \frac{D}{D-k}.
\]

Putting the inequalities together gives the following bound, 
valid for \(k > K = \max(C, 2D)\):

\[
  |F(k)| \le \frac{k (k-D)}{(k-C)(k-2D)} = \left(1 + \frac{C}{k-C} \right)
  \left(1 + \frac{D}{k-2D} \right).
\]

Let \(r = q-p\) and \(\tilde z = |z a_p / b_q|\).
Assuming \(k > max(C,2D, {\tilde z}^{1/r})\), we have

\[
  |z R(k)| \le G(k) = \frac{\tilde z F(k)}{k^r}
\]

where \(G(k)\) is monotonically decreasing. Now we just need to find an
n such that \(G(n) < 1\) and for 
which \(|T(n)| / (1 - G(n)) \le 2^{\\-d}\). This can be done by computing a
floating-point guess for \(n\) then trying successively larger values.

This strategy leaves room for some improvement. For example, 
if \(\tilde b_1\) is positive and large, the bound \(B\) becomes 
very pessimistic (a
larger positive \(\tilde b_1\) causes faster convergence, not slower
convergence).
-}


module Data.Number.Flint.Hypgeom (
    module Data.Number.Flint.Hypgeom.FFI
) where

import Data.Number.Flint.Hypgeom.FFI

