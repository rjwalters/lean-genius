# Binary augmentation-filtration probe for the cyclic size-two code

Date: 2026-08-24

Owner: codex-sol-1

Scope: `BinarySizeTwoCyclicPackingBound`; bounded divergence-round #7 probe

## Verdict

The modular group algebra does retain information which complex Fourier
analysis discards: over

```text
R_q = F_2[Z/q] = F_2[z]/(z^q-1) = F_2[epsilon]/(epsilon^q),
epsilon = z+1,
```

for `q=2^k`, every consecutive two-hole boundary has augmentation valuation
exactly one.  This gives an exact binary fingerprint for every routing
block.

It does **not**, from the present reciprocal-permutation-code axioms, produce
a three-fiber contradiction.  Reciprocity transposes individual routed
darts after an affine shear; it supplies no convolution or matrix-product
identity equating a product of three boundary polynomials to one boundary
polynomial.  Agreement at most one is a coefficientwise integer inequality,
not such an identity.  Therefore the tempting valuation jump
`1+1+1 > 1` has nothing valid to compare.  The route stops at a precise
missing link rather than opening another formal leaf:

> derive a genuine three-fiber convolution/holonomy identity from
> reciprocity and agreement, or augmentation valuation cannot couple the
> fibers.

## Exact one-block calculation

Use the absolute-coordinate partial permutation matrix from
`SIZE_TWO_CYCLIC_MULTI_SEQUENCE_LITERATURE.md`.  For fixed state `(x,t)`,
write

```text
F_(x,t)(Y,Z) = sum_(y,z in M_(x,t)) Y^y Z^z
```

in `R_q tensor R_q`.  Its row and column marginals are determined without
knowing the permutation:

```text
F_(x,t)(Y,1)
  = H(Y) + Y^(x+t)(1+Y),

F_(x,t)(1,Z)
  = H(Z) + Z^(x-1)(1+Z),

H(U) = 1+U+...+U^(q-1).
```

The plus signs are also subtraction in characteristic two.  Since

```text
U^q-1 = (U+1)^q,
H(U)  = (U+1)^(q-1),
```

putting `epsilon=U+1` gives

```text
H(U) + U^c(1+U)
  = epsilon^(q-1) + (1+epsilon)^c epsilon.
```

For `q>2`, the coefficient of `epsilon` is one, so both marginals have
augmentation valuation exactly one.  Translation changes the higher
coefficients but not this leading term.  This is the promised information
which order-two complex characters collapse to a single parity value.

## What reciprocity says in these coordinates

A route is more naturally written in state coordinates as

```text
(x,t) --r--> (y,s),       y=x+r,
```

where the absolute partial-permutation column is `z=y+s`.  Reciprocity is
the literal reversal

```text
(x,t) --r--> (y,s)
(y,s) --(-r)--> (x,t).
```

Thus the global four-variable indicator

```text
K(X,T;Y,S) = sum_routes X^x T^t Y^y S^s
```

is invariant under swapping `(X,T)` and `(Y,S)`.  Passing between `K` and
the block polynomial `F_(x,t)(Y,Z)` uses the shear `Z=YS`.  This is a valid
transpose symmetry, but it is linear: it relates coefficients of one block
to coefficients of other blocks one dart at a time.

In particular, it does not assert any of

```text
F_t F_s = F_u,
F_t F_s F_u = a prescribed hole polynomial,
K^2 = a prescribed group-ring element.
```

The last possibility is especially tempting but unavailable.  C4-freeness
only says that distinct vertices have at most one common neighbor.  Hence
off-diagonal coefficients of the integer square of the adjacency matrix are
in `{0,1}`; their locations are not fixed.  Reducing modulo two preserves
the unknown support rather than turning the square into a known element.

## Why the naive three-factor valuation argument fails

Multiplying three marginal boundary polynomials certainly gives an element
of augmentation valuation at least three.  To obtain a contradiction one
would need the same element, by a separately proved routing identity, to
equal a translate of a one-boundary polynomial of valuation one.  Neither
reciprocity nor shifted agreement supplies that equality:

- reciprocity pairs each dart with its reverse in a generally different
  fiber and at a translated base;
- a collision at `(x,t)` reverses to two different base states in the target
  fiber, not to one target collision;
- agreement at most one bounds overlaps at one prescribed alignment, while
  convolution sums over all intermediate alignments.

Replacing the missing equality by an inequality does not help in `F_2`:
the augmentation filtration is multiplicative for products and exact for
equalities, but is not monotone under coefficientwise integer inequalities
after reduction modulo two.

## Outside-literature boundary

Classical augmentation-ideal and group-ring methods are strongest for
difference sets, difference matrices, and developed designs because those
objects satisfy exact group-ring product identities.  The current code is a
packing: it has moving holes and upper bounds on selected correlations.
The survey hit therefore confirms the algebraic diagnosis rather than
supplying the missing identity.  Relevant general anchors are Passi,
*Group Rings and Their Augmentation Ideals* (LNM 715, 1979), and the modern
2-group difference-matrix literature; their product identities are extra
hypotheses here.

## Surviving bounded candidates

The augmentation idea should be reopened only if one of the following is
first derived independently:

1. a three-fiber closed-walk identity with a prescribed right-hand side;
2. a `q -> q/2` descent in which the odd-lift cocycle has an exact boundary;
3. a binary incidence-rank identity for the collision partial linear space.

Absent one of these, taking more powers, more augmentation coefficients, or
more formal consequences of the one-block valuation is the same one-fiber
hill climb already ruled out by goal #36.
