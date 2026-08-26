# H7 finite-field rank pivot audit

## Question

Can the canonical `H7/T0` block identities already contradict the existence
of the low adjacency block after reduction modulo a small prime?

Write the full adjacency matrix as

```text
A = [ 0  B ]
    [ Bᵀ C ]
```

where `B` is the fixed `7 × 42` high/low support-incidence matrix and `C` is
the symmetric zero-diagonal low adjacency matrix.  Canonical semantics give

```text
BBᵀ = 7I + J,        BC = J,
```

and hence, by symmetry, `CBᵀ = Jᵀ`.

## Exact consequences

Let `U = {x : 1ᵀx = 0}`.  For every coefficient ring and every `x ∈ U`,

```text
C(Bᵀx) = Jᵀx = 0.
```

The singleton columns of `B` contain two literal copies of every standard
basis vector of the seven-label space.  Therefore `Bᵀ` is injective over
every field, including characteristics two and seven.  It follows that

```text
dim ker C ≥ 6
```

over every field.  In particular `X^6` divides the characteristic polynomial
of `C`; this is an integral identity, not a specifically modular obstruction.
It is the same six-dimensional sector that produces the fixed
`±sqrt(7)` eigenvalues of the full block matrix.

Modulo seven, `BBᵀ = J` has rank one although `B` has rank seven.  The six
label-difference rows are a totally isotropic radical for the Gram form, but
this is permitted in characteristic seven and does not lower `rank B`.
Modulo two, `BBᵀ = I + J` has rank six while `B` still has rank seven; again
there is no rank contradiction.

## Decisive linear feasibility probe

I row-reduced the exact linear system over `F_7` whose 861 variables are the
unordered entries of symmetric zero-diagonal `C`.

The equations `CBᵀ = Jᵀ` give 294 scalar equations.  They are consistent,
have rank 273, and leave dimension 588.

Adding all 42 exact row-degree equations modulo seven and all 21 pinned empty
edge equations for the hard representative `F6/t2` (mask `1048903`) remains
consistent:

```text
equations = 357
variables = 861
rank      = 329
dimension = 532
```

The probe constructs `B` directly from the canonical ordering (7 empty
supports, two singleton copies for each label, then the 21 unordered label
pairs) and performs sparse modular Gaussian elimination.  Thus neither the
block equations, degrees, nor the pinned hard mask yield a linear
characteristic-seven obstruction.

## Verdict

**CUT the pure finite-field rank/divisibility lane.**  Its strongest immediate
conclusion is the already-visible six-dimensional kernel of `C`, and the
hard pinned system retains 532 linear degrees of freedom over `F_7`.

A nonlinear polynomial-calculus or moment argument could still use the C4
constraints, but that is a different mechanism and should face its own
bounded degree/basis-growth test.  Do not formalize the modular rank facts as
an H7 exclusion route unless a nonlinear consumer first appears.
