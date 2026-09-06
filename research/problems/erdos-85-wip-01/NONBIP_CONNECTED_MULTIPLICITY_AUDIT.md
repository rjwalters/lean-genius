# NONBIP-CONNECTED: designated multiplicity audit

## Scope

This is the dimension-side sibling of the incidence-energy audit under
`A-REG-NONBIP -> NONBIP-CONNECTED [q]`.  It asks exactly how strong an
upper bound on the designated primary sector must be to contradict the
banked trace-growth theorem.  It does not add another conditional Lean
wrapper.

## The banked lower scale

`connectedNonbipartite_designatedFactor_finrank_sq_growth` proves that a
designated primary restriction of dimension `m` and trace `-q` satisfies

```text
q^2 < 2(q-1)m^2.                                      (1)
```

Therefore the exact division-free terminal input is

```text
2(q-1)m^2 <= q^2.                                     (2)
```

Equivalently, one needs `m` at most about `sqrt(q/2)`.  An `O(q)` or
`O(q^2)` multiplicity theorem is not close enough.  This scale should be
written into any proposed designated-factor lane before work begins.

## The blind factor is sharper

On the `mu = -1` defect eigenspace the adjacency roots are
`+sqrt(q), -sqrt(q)`.  When `k` is even, write `q = t^2`.  If this sector
alone carries trace `-q`, its sign imbalance is exactly `-t`, so its total
multiplicity is at least `t = sqrt(q)`.  Thus a pure-blind even-`k` terminal
would follow from the still stronger coordinate bound

```text
mult_D(-1) < sqrt(q).                                 (3)
```

For odd `k`, `sqrt(q)` is irrational and Galois pairing makes the blind
trace zero; the non-blind designated factors remain, as recorded in the
main endgame audit.

## Why standard multiplicity bounds do not reach the scale

General connected-regular graph bounds are much too large and do not use
the ambient square-root identity.  For example, the sharp generic bound
for an eigenvalue `mu` other than `-1,0` is

```text
mult_D(mu) <= ((r-1)/(r+1)) n,
```

for an `r`-regular graph on `n` vertices (Peter Rowlinson,
"Eigenvalue multiplicity in regular graphs",
<https://doi.org/10.1016/j.dam.2018.07.023>).  At `r=q-1`, `n=q^2` this is
of order `q^2`, versus the required order `sqrt(q)`, and it explicitly does
not cover the blind eigenvalue `-1`.  Standard star-complement/codimension
bounds have the same scale mismatch.

The C4-free spectral-radius bounds also control eigenvalue magnitude, not
multiplicity.  They are already subsumed here by the banked strict bound
`theta^2 < 2(q-1)` used to prove (1).

## Formal odd closed-walk congruences pass; dimension parity does not

Assume the residual sectors are sign-paired and the even-`k` blind sector
has trace `-q`.  Its contribution to every odd moment is

```text
tr_blind(A^(2s+1)) = -q^(s+1),
```

so after adding the principal eigenvalue,

```text
tr(A^(2s+1)) = q^(s+1)(q^s - 1).                     (4)
```

For an odd prime `ell=2s+1`, rotation of closed walks requires divisibility
by `ell`.  But even `k` makes `q` a square modulo every odd prime not
dividing `q`, and Euler's criterion gives `q^s = 1 (mod ell)`.  Hence (4)
automatically satisfies the prime closed-walk congruence. This verifies
only that formal moment test. The assumed fully sign-paired residual
spectrum is nevertheless impossible by the dimension argument below.

## Viable missing statement

The shortest non-tautological target is therefore an **ambient-coordinate
multiplicity bound**, not a generic spectral theorem:

> **AXIOM A-REG-DESIGNATED-DIMENSION.** For every designated primary factor
> `g` carrying trace `-q` in a connected binary-square C4-free instance,
> with `m = finrank ker(g(T))`, one has `2(q-1)m^2 <= q^2`.

For the pure even blind factor this can be replaced by the concrete sharper
target `mult_D(-1) < sqrt(q)`.  Any proof must use entrywise information from
`A^2 = qI + complement(D)` (zero diagonal, zero-one entries, or eigenvector
coordinates); connected regular graph theory alone misses the required
scale by a factor of order `q^(3/2)`.

## Verdict

**NO TERMINAL from known generic multiplicity or odd-moment results.**  The
dimension route remains plausible only as a new ambient-coordinate theorem
at the `sqrt(q)` scale.  This is genuinely different from the unsupported
CUBE-UPPER axiom and is not refuted by the disconnected `q=4` energy
control, but no such bound is currently banked.

## Correction: multiplicity does not determine the sign budget (2026-09-06)

For even exponent, put `q=s²`, so `s` is an even integer. Let
`m±=mult_A(±s)`, `m=m+ + m−=mult_D(−1)`, and let `R` denote the
trace on all nonprincipal sectors other than this blind sector. The exact
trace-zero equation is

```text
0 = q + s(m+ − m−) + R,
s(m− − m+) = q + R.
```

For the particular case `R=0`, a choice of nonnegative integer multiplicities exists exactly when
`m>=s` and `m≡s (mod 2)`, with `m−=(m+s)/2` and `m+=(m−s)/2`.
This is a sign-allocation criterion, not an existence theorem for an
ambient graph. Merely having a nonzero negative eigenspace is also not
equivalent to `m>=s`.

There is a further obstruction to the fully sign-paired residual case
assumed in the formal odd-moment calculation above. Connected `D` makes
`A²=L_D+J` positive definite, so `A` has no zero eigenvalue. The principal
eigenvalue has multiplicity one, and every remaining nonzero sign pair contributes
an even dimension, say `2r`. Hence

```text
q² = 1 + m + 2r.
```

Since `q²` is even, `m` is odd. But `R=0` forces `m≡s≡0 (mod 2)`.
This is a contradiction. No C4-free counting or connected-defect
multiplicity estimate is needed for this narrower case.

The distinction between **trace zero** and **sign paired** is essential.
An unpaired odd-dimensional sector can have trace zero and avoid this
dimension argument; sectors with nonzero `R` change the sign budget
altogether. The existing older integral Capell completion is not excluded:
its non-blind sectors need not have zero total trace. Neither this correction
nor the formal odd-moment calculation supplies an A-REG terminal. The
remaining designated-factor dimension conjecture above stays unproved.

The stored actual `q=4` graph illustrates why the connectedness/zero-mode
scope matters: its adjacency characteristic polynomial is

```text
x (x−4) (x+2)² (x²−2)² (x⁴−8x²+14)².
```

The blind sector has dimension two and trace `−4`; the other nonprincipal
sectors have trace zero, but their dimension is thirteen, including the
single zero eigenvalue. Its defect is disconnected, so it does not satisfy
the invertibility hypothesis above. The parity argument does not reject
this actual graph.
