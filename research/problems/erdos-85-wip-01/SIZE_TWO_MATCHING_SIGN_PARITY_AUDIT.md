# Size-two matching-sign parity audit

## Question

Could the residual reflection sign of the two perfect matchings in every
two-regular factor give a ternary obstruction?  The answer is no at the
determinant-sign level: every via tile has positive total matching sign for a
formal reason, and the resulting Latin-square parity is compatible with
reciprocity when `4 | 2q`.

## Four matchings in one tile

Choose a perfect-matching decomposition of two composable factors and write

```text
X_ce = P (I + sigma),
X_ed = R (I + tau).
```

After moving the first relative permutation across `R`, the four permutation
matrices in the binary product `Y_e^(c,d)=X_ce X_ed` have the form

```text
p,  p beta,  p alpha,  p alpha beta
```

for permutations `p,alpha,beta` of the target shore.  Binaryness says these
four matchings are edge-disjoint, but it is not needed for their signs.  Their
product is

```text
sgn(p)^4 sgn(alpha)^2 sgn(beta)^2 = +1.               (1)
```

Thus grouping the `2q` perfect matchings of the complete `J` tiling into its
`q/2` via tiles forces the product of all symbol-matching signs to be `+1`.
This conclusion is independent of whether the relative permutations are
cycles, and it contains no phase or fiber-position information.

## Latin-square parity gives no terminal

The `2q` disjoint permutation matrices summing to `J` are a Latin-square
one-factorization of `K_(2q,2q)`.  The standard relation among row, column,
and symbol parities has right-hand sign

```text
(-1)^((2q)(2q-1)/2).
```

For the active binary branch `q` is divisible by four, so `2q` is divisible
by eight and this sign is `+1`.  Equation (1) therefore says only that row
and column parity agree.  Transpose reciprocity already exchanges those two
parities, so it supplies exactly the same equality and no contradiction.

## Verdict

Determinants, products of reflection signs, and any exterior-minor invariant
collapsed to the sign of each matching cannot prove the all-size-two
terminal.  A viable dihedral cocycle must retain the actual fiber labels or
relative positions inside the incidence cycles.  This is the same boundary
identified by the earlier conjugacy-class holonomy countermodels, now checked
for the tempting Latin-square/sign refinement.
