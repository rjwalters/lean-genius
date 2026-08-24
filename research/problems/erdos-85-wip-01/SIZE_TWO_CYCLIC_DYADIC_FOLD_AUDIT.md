# Dyadic-fold interface audit

This is the first exact gate for divergence round 15's proposed induction
from `q=2n` to `n`.  It fails before any perfect-matching or cap-selection
question arises.

Write the two forbidden differences upstairs as

```
h0 = a,                    h1 = -1-a        in Z/(2n).
```

Reduce differences modulo `n`.  Their images are distinct when `n` is even:
equality would say `2a+1 = 0 (mod n)`, impossible because the left side is
odd and `n` is a positive power of two.  Nevertheless the allowed fibres do
**not** become two copies of the lower allowed-fibre set.

For a lower difference other than `h0 mod n` and `h1 mod n`, both of its
two upper lifts are allowed.  Over each of the two lower forbidden
differences, exactly one lift is forbidden and the other lift is allowed.
Thus the upper allowed set has the precise decomposition

```
D_(2n) = (two lifts of every element of D_n)
         disjoint-union
         {one exceptional lift over h0, one exceptional lift over h1}.
```

The cardinality check is

```
2(n-2) + 2 = 2n-2.
```

Those two exceptional fibre classes fold onto cells that do not exist in a
`SizeTwoCyclicSameDifferenceCode n (a mod n)`.  Simply deleting them is not
a restriction of the code interface: the exact target-row and target-column
hit laws quantify over all allowed target cells, and deletion changes the
required degree from `2n-2` without supplying the lower degree `n-2` or a
canonical repair.

There is a second parameter obstruction.  The upper assumptions `a != 0`
and `a != -1` in `Z/(2n)` do not imply their lower counterparts: `a=n`
reduces to zero, and `a=n-1` reduces to `-1`.  Hence even a successful edge
selection would not give an inductive instance of
`BinarySizeTwoCyclicPackingBound` for every permitted upper parameter.

## Verdict

The naive dyadic fold / reciprocal perfect-matching induction is **cut**.
Before Hall or cap control can be invoked it needs a new, nontrivial surgery
that simultaneously removes the two exceptional lifted fibres, repairs all
row/column hits, and treats the parameters reducing to `0` or `-1`.  That
surgery is essentially as strong as the original packing problem, so a
claim that the code merely folds to order `n` is false.

This does not rule out a more elaborate four-cell orbit quotient, but such a
quotient must state and prove its repaired lower interface explicitly; lift
selection alone is not a q-generic chain to the named terminal.
