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
