{- |
module      : Data.Number.Flint.Dirichlet
copyright   :  (c) 2023 Hartmut Monien
license     :  BSD-style (see LICENSE)
maintainer  : hmonien@uni-bonn.de

__Warning: the interfaces in this module are experimental and may change without notice.__

This module allows working with Dirichlet characters algebraically. For
evaluations of characters as complex numbers, see @acb-dirichlet@.

= Dirichlet characters 

Working with Dirichlet characters mod /q/ consists mainly in going from
residue classes mod /q/ to exponents on a set of generators of the
group.

This implementation relies on the Conrey numbering scheme introduced in
the
<http://www.lmfdb.org/Character/Dirichlet L-functions and Modular Forms DataBase>,
which is an explicit choice of generators allowing to represent
Dirichlet characters via the pairing

\[\begin{aligned}
\begin{array}{ccccc}
(\mathbb Z/q\mathbb Z)^\times \times (\mathbb Z/q\mathbb Z)^\times & \to & \bigoplus_i \mathbb Z/\phi_i\mathbb Z \times \mathbb Z/\phi_i\mathbb Z & \to &\mathbb C \\
(m,n) & \mapsto& (a_i,b_i) &\mapsto& \chi_q(m,n) = \exp(2i\pi\sum \frac{a_ib_i}{\phi_i} )
\end{array}
\end{aligned}\]

We call /number/ a residue class \(m\) modulo /q/, and /log/ the
corresponding vector \((a_i)\) of exponents of Conrey generators.

Going from a /log/ to the corresponding /number/ is a cheap operation we
call exponential, while the converse requires computing discrete
logarithms.

-}

module Data.Number.Flint.Groups.Dirichlet (
  module Data.Number.Flint.Groups.Dirichlet.FFI,
) where

import Data.Number.Flint.Groups.Dirichlet.FFI

