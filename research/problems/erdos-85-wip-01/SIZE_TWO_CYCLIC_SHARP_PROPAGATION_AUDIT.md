# Size-two cyclic sharp-source propagation audit

## Scope

This note isolates the quantitative statement suggested by the cap-free
sharp-source census.  It is a prospective intermediate lemma for
`BinarySizeTwoCyclicPackingBound`, not a finite-order replacement for that
theorem.

For a source cell `p=(x,t)`, write

```text
b_p(u) = number of neighbours of p in target fibre u,
e_p(u) = b_p(u)-1,
r(p)   = sum_u max(e_p(u),0).
```

The exact degree law gives `sum_u e_p(u)=0`, so `r(p)` is also the total
missing mass.  The uniform stratum has `r=0`; it is already impossible.  A
sharp source has `r=1`, equivalently one zero, one double, and all other
loads one.  Every nonuniform nonsharp source has `r>=2`.

## Candidate q-generic amplification lemma

For binary `q=2^k`, `k>=3`, exact row/absolute-column hits and loopless
reciprocity should imply

```text
sum_p r(p) >= q^2.                                      (RANK-q2)
```

The stronger sharp-count conjecture says that at most

```text
q(q-2)-2q = q(q-4)
```

sources can be sharp.  It implies (RANK-q2), because each sharp source has
rank one and each other nonuniform source has rank at least two.  The
converse is false: rank excess may concentrate at a few high-rank sources.
Thus (RANK-q2) is the weaker but more additive prospective invariant, and
the sharp-threshold data alone do not yet verify it.

The block-row variance satisfies the exact identity

```text
V = sum_p,u e_p(u)^2 = 2 * sum_p,u choose(b_p(u),2).
```

Since `e^2 >= |e|` for integer `e`, (RANK-q2) would give `V>=2q^2`.
Equality forces every load to lie in `{0,1,2}`.  Thus the equality case is
an especially rigid defect-circulation stratum: every source has `r=1` or
`r=2`, and exactly `2q` units of rank lie above the sharp baseline.

## Verified bounded evidence

The sound pure-Boolean encoding in `size_two_cyclic_full_probe.py` gives:

```text
q=8, a=1: 32 sharp SAT, 33 sharp UNSAT
q=8, a=2: 32 sharp SAT, 33 sharp UNSAT
q=10,a=1: 61 sharp UNSAT; the equality-side 60 query is pending
```

The additive statement has also been tested directly, rather than inferred
from the sharp census:

```text
q=8, a=1: sum r <= 63 UNSAT; sum r <= 64 SAT
q=8, a=2: sum r <= 63 UNSAT
```

Here `r(p)` is encoded as the number of zero-load fibres at `p`.  This is
exactly the defect rank because `sum_u (b_p(u)-1)=0`; it uses only Boolean
pseudo-cardinality constraints.  The DIMACS theory-atom validator accepts
the generated CNFs, and Kissat proves both rank-63 instances UNSAT.  Thus
q8 genuinely verifies (RANK-q2), including its sharp equality, rather than
only the stronger-looking but logically different sharp-count threshold.

At q=8 both SAT witnesses attain `sum r=64=q^2` and `V=128=2q^2`.
They have genuinely different exceptional-set geometries:

* for `a=1`, the sharp set is `all x × {0,2,5,7}` and the two remaining
  source fibres are wholly rank two;
* for `a=2`, fibres 4 and 6 are wholly sharp, while fibres 0, 1, 3 and 7
  split by base parity and have four sharp and four rank-two sources each.

Therefore no proof of (RANK-q2) may assume that exceptional sources contain
whole fibres, meet every fibre, or have a uniform number per base.  The two
q=8 witnesses also show that `V>=2q^2`, if true, is sharp before the
same-difference common-target caps are imposed.

The calibration orders remain important: q=4 permits every source sharp,
while at q=6 even one sharp source is impossible although the unrestricted
cap-free system is satisfiable.  The proposed statement is intentionally
restricted to binary q at least 8.

## Near-orthomorphism literature cut

For fixed `p=(x,t)`, the normal form sends a dart label `r` to

```text
u = -t-r-psi_p(r),
```

where `psi_p` is a permutation of the two-hole label set.  Thus a sharp
source is a two-hole near orthomorphism: the sum map has one repeated and
one missing value.  This is the quantitative neighbourhood of the
Hall--Paige complete-mapping obstruction, not an unrelated Latin-square
phenomenon.

The classical literature also closes the purely local route.  Cheng-De
Wang, *On Special Near Orthomorphisms*, JCMCC 21 (1996), proves existence of
special near orthomorphisms for abelian groups with cyclic Sylow 2-subgroup
of order greater than 6 and gives an explicit `Z_8` example:

```text
https://combinatorialpress.com/article/jcmcc/Volume%20021/vol-21-paper%2013.pdf
```

The paper's canonical deleted pair is not automatically identical to every
pair of holes in this packing problem, but its existence theorem agrees with
our exhaustive local q8 enumeration: near-complete-mapping theory supplies
individual sharp rows rather than excluding them.  The missing theorem is
therefore a *coupled* near-orthomorphism result for the affine reciprocal
involution across all bases.  Standard Hall--Paige or local
near-orthomorphism nonexistence cannot yield (RANK-q2).

## What the statement would and would not prove

(RANK-q2) is a real amplification over the pointwise first-moment bound
`r(p)>=1`, but it is not the packing contradiction: the cap ceiling

```text
V <= q(q-1)(q-2)
```

is much larger than `2q^2`.  A scalar variance comparison therefore cannot
finish the theorem.  The useful prospective chain is instead:

1. prove (RANK-q2) from the shifted-base reciprocal involution;
2. classify or descend its equality stratum, where all loads are at most 2;
3. show that the same-difference caps force additional rank/variance in a
   new orbit whenever an equality-stratum defect is repaired;
4. iterate a cap-preserving amplification, rather than spending all caps in
   one global upper bound.

Aggregate defect flow cannot prove step 1: the previously banked sharp-flow
relaxation is satisfiable.  Single-base row/column permutation parity cannot
prove it either: the full base-slice relaxation is satisfiable at q=8.  The
remaining information is exactly the shifted-base law

```text
psi_(x+t+r,u)(s) = r,
u = -t-r-s,
```

so a proof must charge rank along orbits that actually change the base
coordinate.  The equality witnesses suggest that this charge can be
periodic (period one for `a=1`, period two for `a=2`), which rules out an
argument based only on aperiodicity.

## First cap-sensitive equality core

The rank interface composes with the existing grouped cap/reciprocity core
mode.  At `q=8`, `a=1`, imposing `sum r <= 64` together with every cap and
every reciprocal block is UNSAT.  A bounded deletion pass retained the
sufficient subsystem

```text
cap fibres: 2,3,4,5
reciprocity blocks:
  22,23,24,25,27,
  33,34,35,37,
  44,45,47,
  55,57.
```

Thus the displayed core drops every reciprocal block involving fibre `0`,
drops `77`, and uses only four of the six cap colours.  As in the earlier
core audits, UNKNOWN during a five-second deletion retains an assumption;
the list is sufficient and order-dependent, not minimum.

The useful conclusion is consequently modest but cap-sensitive.  The sharp
rank equality stratum is already incompatible with a proper subsystem of
the full packing laws, but this deletion did not expose a one-cap-fibre
contradiction.  The next bounded discriminator is to retain all reciprocal
blocks and explicitly test each singleton cap fibre, followed by cap-fibre
subsets.  If every singleton is SAT, the first cap amplification lemma must
couple collision graphs from multiple source fibres; if one is UNSAT, its
single-colour collision graph is the right equality object to classify.

## Next falsifiable interface

At the next orders the bounded probe should not merely extend the sharp
threshold.  It should ask whether `sum r <= q^2-1` is inconsistent directly,
leaving all individual source ranks unrestricted.  A negative verdict at
q10 would give the first cross-order evidence for the rank formulation; a
model would refute it even if the sharp-count bound survives.  The
corresponding proof target is an orbit charge whose total is at least `2q`
above the pointwise baseline and which is invariant under the two distinct
q=8 equality geometries above.

## Reciprocal-adjacency cocycle cut

The probe option `--dump-sharp-edge-census` classifies reciprocal graph edges
by whether their endpoints have rank one (sharp) or higher rank.  On q8
`N=32` equality witnesses it gives:

```text
a=1: SS=64, SN=64, NN=16; sharp components 16+16
a=2: SS=66, SN=60, NN=18; sharp component 32
```

In the a1 witness every nonsharp vertex has four sharp neighbours.  In the
a2 witness the nonsharp-to-sharp degrees range from three to five, while
sharp-to-sharp degrees range from two to six.  In both cases the nonsharp
vertices themselves induce a connected graph; for a2 the 32 sharp vertices
also induce one connected graph with many cycles.

This cuts the simplest repair-frustration picture in which the `2q`
nonsharp cells form a separator, independent set, feedback set, or uniform
boundary of the reciprocal graph.  A surviving cocycle proof would need
edge labels/orientations from the actual near-orthomorphism repairs: the
unlabelled sharp/nonsharp adjacency graph does not carry the charge.

## Adjacent-base rank localization

Pointwise reflection symmetry and per-base sharp parity are both cut.  A
q8 `a=1` unrestricted model has reflected source ranks one and two, and a
q8 `a=2` rank-64 model has an odd number of sharp sources at one base.  The
correct equality geometries can distribute their `2q` exceptional sources
as `2+2` or alternating `3+1` across adjacent bases.

The surviving direct statement is instead

```text
if sum_x R(x) <= q^2, then 2q <= R(x) + R(x+1) for every x,
R(x) = sum_t r(x,t).
```

At q8, asking for `R(0)+R(1)<=15` is UNSAT for every hole representative
under the global rank-64 bound.  For `a=0,1,3` the local query is already
UNSAT without that global bound; `a=2` is the unique geometry needing the
global-to-local hypothesis.  Summing the displayed adjacent inequalities
counts each `R(x)` twice and gives `(RANK-q2)` immediately.  This arithmetic
consumer is formalized as
`card_mul_le_sum_of_two_mul_le_adjacent`.

Constraint ablation shows that the local inequality is genuinely a coupled
normal-form phenomenon.  For both `a=1` and `a=2`, under total rank at most
64 and adjacent rank at most 15:

```text
drop exact target-row hits:       SAT;
drop exact absolute-column hits:  SAT.
```

Thus neither projection family plus reciprocity suffices.  A proof must use
the interaction of the row and column permutations, not merely one family
with a reflected-rank or sign argument.  Dropping reciprocity in the same
tight query was UNKNOWN at the bounded solver budget, so this audit makes
no claim that reciprocity is independently necessary.
