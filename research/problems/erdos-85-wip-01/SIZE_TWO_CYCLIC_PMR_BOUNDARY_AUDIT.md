# Parity-missing-rank boundary audit

Node: the structural PMR inequality beneath
`BinarySizeTwoCyclicPackingBound`.

## Aggregate Hall deficiency is not the mechanism

For the q8/a2 cap-free witness with

```text
total defect rank <= 70,
R(0)+R(1) <= 15,
```

the two aggregate difference-multiplicity support graphs are both connected
and have perfect matchings.  Relative to a maximum matching, each directed
Dulmage--Mendelsohn graph is one strongly connected component on all twelve
row/column vertices.  The separate zero-slot and positive-excess graphs
also have several components.  Hence PMR cannot be proved by claiming that
a bad adjacent pair creates a unique Hall-deficient component in either
aggregate base matrix.

The rank-64 equality witness gives the same negative diagnosis.  Its
parity-selected zero-slot graphs have two or three components in every
adjacent window, not one propagating component.

## Exact boundary permutations

`size_two_cyclic_full_probe.py --dump-route-table` prints, for every source
cell `(x,t)`, the exact map from target base `y` to target-difference fibre
`u`.  This exposes the shared-hole interface directly.

For adjacent bases `x,x+1`, take the unique route from `(x,t)` in the first
column outside their shared column hole, `c=x+1`, and the unique route from
`(x+1,t)` in the opposite boundary column `c=x-1`.  Exact column hits make
their target-fibre labels two permutations `L_x,R_x` of the allowed
difference set.  Define the boundary monodromy

```text
P_x = R_x^{-1} L_x.
```

In the rank-70 witness at its bad pair `x=0`, the permutations are

```text
L = {0:3, 1:6, 3:7, 4:1, 6:0, 7:4},
R = {0:3, 1:0, 3:6, 4:7, 6:1, 7:4},
P cycles = (0)(7)(1 3 4 6).
```

Thus the boundary object has two fixed fibres and one cycle on the other
`q-4` fibres.  This is the first concrete alternating component aligned
with the adjacent-rank dip.

For comparison, a rank-64 q8/a2 equality model is period two in `x`; its
boundary-monodromy cycle types alternate

```text
5+1,  4+2,  5+1,  4+2, ... .
```

The observed cycle types come from individual witnesses.  Sampling the
rank-70 query with Z3 seeds 1 through 8 falsifies their invariance: the bad
pair realizes cycle types

```text
1+1+4,  1+2+3,  and  2+4.
```

In particular neither two fixed fibres nor one prescribed long cycle is
forced.  The boundary permutations are canonical data, but their ordinary
cycle type is not the propagating invariant.  What survives this audit is
only the negative conclusion: neither aggregate Hall/DM components,
parity-zero components, nor unweighted boundary-monodromy cycles explain
PMR.  A viable boundary argument must retain labels/weights (missing and
positive-excess tokens, or the parity charge `Q`) rather than just support
connectivity.

## Weighted PMR dips have a global rank cost

The repeatable option `--max-parity-missing-at-adjacent-bases` allows
several window bounds in one query.  Write a *dip* for `M(x) <= q-1`.
At q8/a2 without caps, exact threshold queries give:

| prescribed dip windows | largest UNSAT rank bound | first SAT rank bound |
|---|---:|---:|
| `{0}` | 65 | 66 |
| `{0,2}` | 67 | 68 |
| `{0,2,4}` | 67 | 68 |
| `{0,2,4,6}` | 67 | 68 |
| adjacent `{0,1}` | 70 | at most 72 |

Thus dips need not be unique and four alternating dips are compatible with
rank `q^2+4`; a linear independent cost per dip is false.  But every tested
dip costs at least two ranks above `q^2`, and adjacency is substantially
more expensive.  Across eight unconstrained rank-70 samples, the weighted
window-surplus sequence has exactly one value `2`, all other values at least
`4`, and total `44=2(sum R-q(q-2))` as forced by the balanced-cut identity.

The zero-surplus case must also be retained.  The cap-free q8/a2 query
`M(0) <= 6` is SAT without a rank bound, so an unconditional local lower
bound of surplus two is false.  Its exact tested rank threshold is much
higher:

```text
M(0) <= 6: UNSAT at total-rank bounds 64,66,68,70; SAT at 72.
```

Thus surplus zero first appears with total surplus
`2(72-8(8-2))=48`, while `4q=32`.  The clean structural target covering
every PMR failure is therefore

```text
window surplus < 4  ==>  total surplus > 4q.             (WSP)
```

All-row binary deviation parity makes window surplus an even nonnegative
integer, so (WSP) includes both possible bad values zero and two.  Under
`sum R <= q^2`, the balanced partition identity gives total surplus at most
`4q`; hence (WSP) forces every window surplus at least four and proves PMR.
No classification or pairing of all positive rows is needed.

## Minimum-rank dips are antipodally paired at q8/a2

The option `--dump-parity-charge` prints the complete per-base vectors
`R,A,B,Q=A-B,M,S`.  At the sharp one-dip threshold `sum R <= 66`, twelve
seeded witnesses all
acquire a second dip at the antipodal window `x+q/2`.  Their surplus
sequences are period four, with observed forms

```text
[2,8,4,4,2,8,4,4],
[2,6,4,6,2,6,4,6],
[2,4,4,8,2,4,4,8].
```

The direct query `M(0)<=7`, `M(4)>=8` is UNSAT at rank bound 66 and SAT at
67.  Hence antipodal propagation is a genuine equality-case law, not a
universal invariant.  It is distinct from the refuted naive dyadic fold of
the whole code: only the minimal weighted defect pattern folds, while the
allowed-fibre interface still has the exceptional lifts documented in the
dyadic-fold audit.

One representative has

```text
R = [8,9,8,8,8,9,8,8],
Q = [0,3,0,0,0,3,0,0],
S = [2,8,4,4,2,8,4,4].
```

The charge compensation is concentrated in one base after each dip, so a
gradual Green-function/winding slope is false.  The surviving candidate is
instead characteristic-two quantization: a bad weighted window may force
its translate by the unique order-two base shift `q/2`.  At q8 this paired
local block already accounts for the strict `4q+4` total-surplus floor.
Whether the antipodal implication persists for general binary `q` is the
next bounded structural question; it is not yet claimed.

## Opposite-parity dips are a separate, expensive sector

The simultaneous cap-free q8/a2 query in the two adjacent, opposite-parity
windows

```text
M(0) <= 7, M(1) <= 7
```

is UNSAT at every total-rank bound from 66 through 70 and first SAT at 71.
This sharply contrasts with two same-parity antipodal dips, whose minimum
remains 66.  Thus the weighted obstruction is not one global scalar charge:
same-parity dips can share a quantized compensation event, while activating
the other parity sector is substantially more expensive.

A first rank-71 witness has

```text
R = [8,7,9,11,8,9,8,11],
Q = [0,1,3,-1,0,-1,0,1],
S = [2,2,12,6,6,4,6,8].
```

The two adjacent dips are followed by a surplus-12 spike.  This points to a
two-sector or vector-valued invariant coupled at adjacent boundaries, rather
than scalar winding.  Any q-generic WSP mechanism should preserve the parity
class of the selected window and explain why cross-sector dips cannot share
the cheap antipodal compensation available within one class.

## Scope across small orders and hole phases

The same cap-free reciprocal query clarifies the scope of any generic WSP
lemma.  At `q=4,a=0`, WSP is false already at total rank eight: every one of
the eight sources is sharp, the two target-fibre loads alternate between
`(0,2)` and `(2,0)`, and `M(0)=2<4`.  Thus the binary theorem must retain its
actual `q>=8` (equivalently `k>=3`) hypothesis; the order-four case is not a
harmless induction base.

Order six does not provide a non-binary counterexample: for both inequivalent
hole choices `a=0,1`, the query `M(0)<=5` is UNSAT even with no total-rank
bound.  At order eight there is a useful phase separation:

```text
a=0: M(0)<=7 SAT without a rank bound;
a=1: M(0)<=7 UNSAT without a rank bound;
a=2: M(0)<=7 SAT without a rank bound;
a=3: M(0)<=7 UNSAT without a rank bound.
```

The `a=1,3` directed controls are SAT, so their unconditional PMR still uses
reciprocity rather than following from the two exact-hit families alone.
The hard low-rank case is consequently concentrated in the even hole phases:
`a=0` already has cap-free minimum total rank 78, while `a=2` reaches rank
`q^2=64` and is the sharp WSP phase studied above.

## Aggregate transpose symmetry is insufficient

Full reciprocity implies the aggregate transpose law

```text
sum_x m_x(t,u) = sum_x m_x(u,t),
```

formalized as `sizeTwoCyclicTargetDifferenceMultiplicity_sum_symm`.  It is
tempting to combine this with the fixed-base doubly-stochastic margins and
the exact affine row moments and discard the base-resolved route tensor.
That relaxation is too weak.

For q8/a2, put the allowed fibres in the order `[0,1,3,4,6,7]`.  A HiGHS
integer-feasibility solve found four fixed-base multiplicity matrices,
repeated with period four over the eight bases, satisfying:

```text
each row and column sum = 6;
sum_u m_x(t,u) u = 2(t+1) mod 8;
sum_x m_x(t,u) = sum_x m_x(u,t);
total zero count over eight bases = 62;
selected zero count in window 0 = 7.
```

The zero counts of the four matrices are `[7,8,8,8]`.  Thus the repeated
relaxation has global rank `62 < q^2` while violating PMR.  The affine
moments include their order-two reductions, so adding the all-row Fourier
parity theorem does not remove this countermodel.

One explicit certificate (rows and columns in the fibre order above) is:

```text
M0 = [[1,1,1,2,1,0], [2,1,0,0,2,1], [1,0,1,2,1,1],
      [1,2,1,0,1,1], [1,1,1,1,0,2], [0,1,2,1,1,1]]
M1 = [[0,2,2,1,1,0], [2,0,1,1,1,1], [2,0,0,1,1,2],
      [2,1,0,1,1,1], [0,2,1,1,1,1], [0,1,2,1,1,1]]
M2 = [[0,2,2,1,1,0], [2,0,1,1,1,1], [1,2,1,1,0,1],
      [1,0,1,1,2,1], [1,0,0,1,2,2], [1,2,1,1,0,1]]
M3 = [[2,1,0,1,1,1], [0,2,1,2,0,1], [1,1,1,0,1,2],
      [1,1,2,1,0,1], [2,1,1,1,1,0], [0,0,1,1,3,1]]
```

Consequently WSP cannot be proved from fixed-base margins, all local
moments, and aggregate transpose symmetry alone.  A successful invariant
must retain the base-resolved reciprocity coordinates of the directed
darts (or equivalent information stronger than the aggregate multiplicity
matrix).  This is a positive scope cut for the group-ring approach: its
coefficients must remember route displacement/base, not only source and
target fibre labels.
