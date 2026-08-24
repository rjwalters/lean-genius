# Extremal normal-form base-slice relaxation

This audit locates the exact global content still missing from the sharp
normal form in `SIZE_TWO_CYCLIC_EXTREMAL_PERMUTATION_NORMAL_FORM.md`.

Put `R=Z/q\{0,1}` and let `D` be the allowed target-fibre set.  For a fixed
base `x`, reindex a local permutation by its output label and write

```
L_x(t,s) = u,
r_x(t,s) = -t-s-u.
```

Thus `s=psi_(x,t)(r)` and `u` is the target fibre of that dart.

The following are necessary consequences of the extremal reciprocal normal
form, but omit the shifted-base involution equation.

1. For every row `t`, `s -> r_x(t,s)` is a permutation of `R`.
2. Every row `s -> L_x(t,s)` has one missing and one doubled value in `D`.
3. For every column `s`, `t -> L_x(t,s)` is a permutation of `D`.

The third property follows from the cell permutation `Q_s`.  Indeed a dart
with reverse label `s` and target fibre `u` sends base `x` to
`x-s-u`; hence bijectivity of `Q_s` makes the fibre map a permutation at
each fixed input base.

## Exact bounded result

An integer finite-domain encoding of (1)--(3) is satisfiable at

```
q=4,a=1; q=6,a=1; q=8,a=1; q=8,a=2.
```

Dropping only condition (1), the row-sharp/column-permutation array is also
satisfiable at q12.  The bounded full q10/q12 slice runs were inconclusive
and are not used as evidence.

Consequently the q8 extremal contradiction is not a parity theorem for one
near-Latin base slice.  It must use the equation omitted above:

```
psi_(x+t+r,u)(s) = r,       u=-t-r-s.                    (I)
```

Equation (I) couples the slice at base `x` to a generally different slice
at base `x+t+r`.  Equivalently, the fixed affine involution

```
J(x,t,r,s) = (x+t+r,-t-r-s,s,r)
```

must preserve the union of all local permutation graphs.  Row repair signs,
column permutation signs, and aggregate defect flow can all be realized
before imposing this shifted-base invariance.

## Local sign flexibility

Direct enumeration of the 720 permutations of `R` at q8 also shows that
the sign of `psi_(x,t)` is not fixed by its missing/doubled fibre pair.
Depending on `(a,t,m,d)`, both signs occur, and the two duplicate dart labels
may have either equal or opposite parity.  For example, at `q=8,a=1,t=0`,
the profile `(m,d)=(3,0)` occurs with both permutation signs.

Thus a viable sign proof needs a **transported** product around (I), not a
local sign assigned to a sharp word.  This agrees with the existing Lean
repair checkerboard: choosing either duplicate occurrence flips the repair
sign, and no canonical local choice is available.

## Surviving endpoint target

The sharp endpoint is now a base-shifted compatibility theorem: prove that
no family of satisfiable slice arrays can be glued around the translations
`x -> x+t+r` so that (I) holds when `q=2^k`, `k>=3`.  Any proposed proof that
uses only a single `x` slice, aggregate block counts, or the signs of isolated
near-orthomorphisms is refuted by this relaxation.
