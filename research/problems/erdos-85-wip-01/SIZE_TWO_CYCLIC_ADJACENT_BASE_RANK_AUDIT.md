# Adjacent-base defect-rank localization

Node: `BinarySizeTwoCyclicPackingBound`, under `GAP A-REG-NONBIP`.

For a base `x`, write

```text
R(x) = sum_t #{u : the (x,t)-source has zero load in target fibre u}.
```

Thus the total defect rank is `sum_x R(x)`.  The full-code probe options
`--max-defect-rank-at-adjacent-bases X N`,
`--max-nonsharp-at-adjacent-bases X N`,
`--require-reflection-rank-imbalance X T`, and
`--require-odd-sharp-count-at-base X` make the following statements
reproducible without altering the exact-hit or reciprocal constraints.

## Refuted pointwise routes

Neither of the tempting one-slice reflection statements is valid.

* At `q=8,a=1`, a reciprocal cap-free code has
  `r(0,0)=1` and `r(0,7)=2`, so pointwise reflected ranks need not agree.
* Odd sharp count at one fixed base is SAT for both `a=1,2` without a rank
  bound.  It remains SAT for `a=2` at the minimum global rank `64`.

Consequently neither reflection-pair rank equality nor per-base sharp parity
can prove the `q^2` rank floor.

## Surviving adjacent-base statement

At `q=8`, requiring

```text
R(0) + R(1) <= 15 = 2q-1
```

is UNSAT for `a=0,1,3` even without a global rank bound.  For `a=2` it is
SAT unrestricted, but becomes UNSAT under `sum_x R(x) <= 64=q^2`.
Therefore all four hole placements verify the conditional localization

```text
sum_x R(x) <= q^2  ==>  R(x)+R(x+1) >= 2q  for every x.       (ABR)
```

Translation symmetry makes the tested base pair representative of every
adjacent pair.  Summing (ABR) cyclically counts every `R(x)` twice and gives

```text
2q^2 <= sum_x (R(x)+R(x+1)) = 2 sum_x R(x),
```

which is exactly the desired `sum_x R(x) >= q^2` bound.

## Parity-selected partition refinement

There is a sharper version that removes the factor-two double count.  Let
`M(x)` count only missing slots based at `x` or `x+1` whose missing target
fibre `u` has the same mod-two parity as `x`.  The option
`--max-parity-missing-at-adjacent-bases X N` tests this quantity.

Under the global bound `sum_x R(x)<=64`, the q8 query `M(x)<=7` is UNSAT
for all four hole placements and for representatives `x=0,1` of both base
parities.  Translation by two covers every other base.  Without the global
rank bound the same query is already UNSAT for `a=1,3`, but SAT for
`a=0,2`; the extremal hypothesis is therefore essential in the latter
geometries.

Every missing slot `(b,t,u)` belongs to exactly one selected adjacent pair:
choose `x=b` when `u` and `b` have the same parity, and choose `x=b-1`
otherwise.  Hence

```text
sum_x M(x) = sum_x R(x).
```

The most resolved prospective lemma is consequently

```text
sum_x R(x) <= q^2  ==>  M(x) >= q for every x.         (PMR)
```

Summing (PMR) gives RANK-q2 directly.  Equivalently, if `Q(x)` is the
signed number of missing target fibres weighted by `(-1)^(x+u)`, then PMR
is the telescoping-potential inequality

```text
R(x)+R(x+1) - (Q(x+1)-Q(x)) >= 2q.
```

This formulation exposes the characteristic-two charge that the coupled
row/column projections must control.

## PMR is cap-free but reciprocity-dependent at q8

The same PMR-violation query was rerun after deleting every same-difference
common-target cap (`--no-caps`).  For each hole representative
`a=0,1,2,3`,

```text
total rank <= 64, M(0) <= 7, no caps: UNSAT.
```

Thus the q8 PMR phenomenon does not use collision caps at all.  This sharply
narrows the generic proof target: exact target-row hits, exact absolute-column
hits, and route reciprocity already suffice in the tested order.  Conversely,
with reciprocity removed (`--directed --no-caps`), the same query is SAT for
both a nonexceptional and exceptional representative (`a=1,2`).  Earlier
ablations also make it SAT when either exact projection family is removed.
Without the global rank bound, the cap-free query is SAT for `a=0,2` and
UNSAT for `a=1,3`, exactly matching the full-cap separation; the extremal
hypothesis, rather than the caps, supplies the missing force in the
exceptional geometries.
The minimal experimental core is therefore precisely

```text
exact row hits + exact column hits + reciprocity + total rank <= q^2.
```

This cuts off the blocker/trade route for PMR itself.  The appropriate
q-generic object is the symmetric base-resolved `0/1` route tensor: its fixed
source-base fibre matrix has constant row and column margins, and its
order-two target character is the potential `Q`.  What remains is a
quantitative adjacent-charge inequality for that symmetric tensor.

## Exact `a=2` tradeoff

The exceptional hole placement has a sharper two-level behavior:

```text
R(0)+R(1) <= 14: UNSAT without a global rank bound;
R(0)+R(1) <= 15 and total rank <= 69: UNSAT;
R(0)+R(1) <= 15 and total rank <= 70: SAT.
```

So dropping the adjacent sum from `2q` to `2q-1` costs at least
`q-2=6` global rank units at `q=8`.  The corresponding q-generic target is
the dichotomy

```text
R(x)+R(x+1) >= 2q,
or
R(x)+R(x+1) = 2q-1 and total rank >= q^2+q-2.
```

Equivalently, put `E(x)=R(x)-(q-2)`, the excess above the rank-one
baseline for the `q-2` sources at base `x`.  The exceptional q8 witness has

```text
E(0)+E(1)=3,       sum_x E(x)=22=3q-2.
```

So the second branch asks for a propagation theorem: losing one unit from
the desired adjacent excess four forces global excess at least `3q-2`, not
merely the `2q` needed for the rank-`q^2` floor.  This formulation isolates
the missing combinatorial charge without triangular-number bookkeeping.

As a nonbinary calibration, the cap-free q6 query
`R(0)+R(1) <= 11 = 2q-1` is unconditionally UNSAT for all three hole
representatives `a=0,1,2`, even with no global-rank bound.  Thus the
exceptional equality branch is not a generic feature of every even order;
it first appears in the tested data at binary q8/a2.

This is genuinely shifted-base information.  It survives both q8 equality
geometries: `a=1` has adjacent nonsharp counts `2+2`, while an `a=2`
minimum witness alternates `3+1`.  A proof must use the base translation in
route reversal; a single-base near-orthomorphism or reflection-parity
argument is already refuted above.

## Global route sign does not explain the localization

The fact that every q8 minimum-rank model has even global route sign suggests
a tempting two-step proof: show that an adjacent-rank violation forces odd
sign, then exclude it in the low-rank stratum.  The exceptional `a=2`
geometry refutes the first step.  The queries

```text
R(0)+R(1) <= 15, global route sign even:                 SAT;
R(0)+R(1) <= 15, total rank <= 70, global sign even:     SAT.
```

The second witness is at the first feasible global threshold: rank at most
69 is UNSAT even without a sign condition.  Thus the adjacent defect costs
six global rank units while remaining in the even component.  Global route
orientation cannot be the missing charge; a proof of the exact tradeoff
must retain more local sign/repair data or a genuinely quantitative
shifted-base potential.
