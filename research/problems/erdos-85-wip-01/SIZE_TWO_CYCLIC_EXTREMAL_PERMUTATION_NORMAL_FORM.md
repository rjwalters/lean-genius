# Extremal reciprocal-permutation normal form

Node: `BinarySizeTwoCyclicPackingBound`, first positive-variance stratum.

This note removes both affine moving-hole systems from the extremal endpoint
and packages all remaining content into a family of local permutations with
one explicit reciprocal involution.  It uses no cap and no internal-support
hypothesis.

## Local coordinates

Put

```text
R = Z/q \ {0,1}.
```

Fix a source cell `p=(x,t)`.  A target row has the unique form

```text
y = x+t+r,       r in R,
```

because the missing target rows are `x+t,x+t+1`.  Write the absolute target
column as `c=x+k`.  Its two forbidden values give
`k in Z/q \ {0,-1}`.  The exact row and column hit laws therefore say that
the neighbours of `p` are the graph of a bijection

```text
k = phi_p(r),
phi_p : R -> Z/q \ {0,-1}.
```

Negation identifies the codomain with `R`.  Hence

```text
psi_p(r) := -phi_p(r)
```

is a permutation of the single fixed set `R` for every cell `p`.

The target cell of the dart `(p,r)` is

```text
T(p,r) = ((x+t+r, u), psi_p(r)),
u = -t-r-psi_p(r).                                  (1)
```

The final coordinate in (1) is the reverse dart label, not part of the
target cell.

## Reciprocity becomes one pointwise inverse law

Let `v=(x+t+r,u)` be the target cell in (1), and put `s=psi_p(r)`.
Viewed from `v`, the row coordinate of the reverse edge is `s`, and its
negated column coordinate is `r`.  Thus entrywise block transpose is exactly

```text
psi_v(s) = r,                                        (2)
```

or equivalently `T(T(p,r))=(p,r)`.  Since loops are excluded by the probe's
edge convention, `T` is a fixed-point-free involution on `Cells x R`.

Conversely, any family of permutations `psi_p in Sym(R)` satisfying
(1)--(2) reconstructs a reciprocal routing code with both exact affine hit
laws.  Thus the cap-free extremal endpoint is not merely mapped into this
normal form: it is equivalent to it, after imposing the load condition
below.

For an undirected edge between fibres `t,u`, with its two local labels
`r,s`, (1) also gives the useful symmetric voltage law

```text
r+s = -t-u.                                          (3)
```

## The extremal load condition

At `p=(x,t)`, the multiset of target fibres is

```text
U_p = { -t-r-psi_p(r) : r in R }.
```

Minimal positive block variance says that `U_p` contains every allowed
fibre once except for one missing value `m_p` and one doubled value `d_p`.
This formulation makes clear that the condition is a near-orthomorphism
condition on `psi_p`, while (2) couples different near-orthomorphisms
entrywise.

For `4 | q`, summing (1) recovers the fixed-difference law without any
internal-support assumption.  Indeed

```text
sum_(r in R) r = q/2-1,
sum U_p = 2(t+1),
sum D = q/2+1,
```

where `D` is the allowed-fibre set.  Therefore

```text
d_p-m_p = c_t := 2t+1-q/2.                           (4)
```

## Scope-corrected bounded evidence

The q8 reciprocal/no-cap query remains UNSAT after removing
`--require-internal-full-support` entirely:

```text
python3 size_two_cyclic_full_probe.py 8 --a 1 \
  --no-caps --minimal-block-variance
```

returns `unsat`.  The grouped reciprocity core in this scope is

```text
33, 34, 37, 45, 47, 55, 57, 77.
```

Thus the q8 endpoint obstruction belongs to (1)--(4), not to internal
support or the pair caps.  The directed control is SAT, so (2) is essential.

## Exact remaining endpoint theorem

The q-generic endpoint can now be stated without graph-incidence notation:

> For binary `q>=8`, there is no family `psi_p in Sym(R)` such that the map
> `T` in (1) is an involution and every multiset `U_p` has one missing and
> one doubled allowed value.

A proof of this statement would finish the extremal endpoint independently
of caps.  The cap is still needed in the separate descent from arbitrary
positive variance.  The most plausible algebraic targets in this normal
form are a sign/product invariant for the coupled permutations `psi_p`, or
an orbit-voltage obstruction obtained by summing (3) along the cycles of a
canonical permutation derived from `T`.  Aggregate defect counts alone are
known to be satisfiable and therefore are not enough.

