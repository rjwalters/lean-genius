# SIZE-TWO-CYCLIC: consecutive-hole Mahler-moment audit

## Candidate

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

For fixed `(x,t)`, the routing permutation is a bijection

```text
P_(x,t) : Z/q \\ {t,t+1}  ->  Z/q \\ {0,-1}.
```

Because the two domain holes are consecutive, one might hope that applying
integer-valued binomial polynomials (the Mahler basis) and reducing modulo
powers of two gives a binary-only obstruction stronger than the existing
first and second displacement moments.

## Exact identity, and why it is automatic

In fact every function `F : Z/q -> A` into an additive commutative group
satisfies

```text
sum_(r != t,t+1) (F(P_(x,t)(r)) - F(r))
  = F(t) + F(t+1) - F(0) - F(-1).
```

This is just reindexing the first sum across the bijection and subtracting
the two complements.  It does not use reciprocity, agreement caps, or even
that `q` is even.  Polynomial moments and Mahler/binomial moments are only
specializations of this identity.  For example, in `Z/q`, choosing `F(z)=z`
gives

```text
sum_r (P_(x,t)(r) - r) = 2t + 2.
```

Choosing higher powers determines the corresponding difference of power
sums from the holes, but supplies no constraint on the permutation beyond
bijectivity.  Choosing integer representatives before applying binomial
polynomials adds wrap-count terms; those terms encode the arbitrary choice
of lifts rather than a new invariant of the cyclic code.

Summing the identity over the base `x` only multiplies both sides by `q`.
Summing over fibres `t`, or pairing directed routes with their reversals,
again produces an endpoint-reindexing identity.  Thus a hierarchy of
single-permutation 2-adic moments would be another linear conservation-law
lane and cannot reach the quadratic packing cap.

## What would be genuinely new

The first nonautomatic moment must involve two source rows, for example a
mixed correlation

```text
sum_r F(P_(x,t)(r), P_(x+d,t)(r-d))
```

over their common domain.  Equality of the two outputs is precisely the
agreement/common-target statistic, and is not determined by the four hole
locations.  Any useful 2-adic or Mahler argument must therefore be a
*polarized* identity controlling these two-row correlations, preferably
while retaining a fixed source row pair and distinct target cells as in
`SIZE_TWO_CYCLIC_THREE_CAP_VALUATION_AUDIT.md`.

This cuts unpolarized higher moments as a route.  It does not cut a
quadratic group-algebra/character argument whose coefficients are row-inner
products; that is exactly where the unproved packing information begins.
