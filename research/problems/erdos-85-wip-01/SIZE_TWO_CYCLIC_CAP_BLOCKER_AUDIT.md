# Same-fibre cap blocker audit

Node: cap-preserving descent beneath `BinarySizeTwoCyclicPackingBound`.

## Exact transition criterion

For same-fibre sources `p,q`, write

```text
C(p,q)  = sum_v A(p,v) A(q,v),
Delta    = A' - A.
```

Then

```text
C'(p,q) - C(p,q)
  = sum_v (A(p,v) Delta(q,v)
           + A(q,v) Delta(p,v)
           + Delta(p,v) Delta(q,v)).
```

If the old code satisfies the cap `C(p,q) <= 1`, a trade breaks it in one
of two logically distinct ways:

```text
old-saturated blocker: C = 1 and C' >= 2;
double-creation blocker: C = 0 and C' >= 2.
```

The saturated-pair census counts the first class exactly by collision mass.
It does **not** count the second class.  Thus a sparse-saturated-blocker
argument needs an additional lemma saying that its candidate trades cannot
create two common targets for an old-disjoint source pair.  Exact degree
preservation alone does not imply that lemma: two equal-size neighbour sets
can move from disjoint to sharing two elements while preserving both sizes.

## Witness instrumentation

`size_two_cyclic_full_trade_probe.py` now reports, for every SAT witness,
all endpoint cap violations and separates old transitions `0 -> >=2`,
`1 -> >=2`, and `>=2 -> >=2`.  It also accepts `--old-caps`, imposing all
same-fibre caps only on the source code.  This is the direct finite test of
whether saturated pairs form a complete blocker set.

The sharp cap-free q8 `a=1`, rank `76 -> 64`, support-eight witness has 16
new-code cap violations, all `2 -> 2`; its source is already uncapped, so it
cannot decide completeness of the blocker set.  At q4, every `--old-caps`
strict descent query with support 4, 6, or 8 is UNSAT.  This is also
inconclusive: the smallest all-cap model has no rank-lowering trade at all.

## Required repair of the proposed dichotomy

A correct sparse/dense descent theorem must do one of the following.

1. Prove a trade-family-specific `C=0 -> C'<=1` lemma, after which the
   saturated-pair census is complete.
2. Count double-creation blockers as well as saturated blockers and bound
   their incidence with candidate descents.
3. Replace source-only blocking by a two-endpoint potential whose change
   includes the quadratic `Delta(p,v)Delta(q,v)` term.

Until one of these is supplied, density of saturated pairs alone does not
certify that every rank-lowering trade is blocked.
