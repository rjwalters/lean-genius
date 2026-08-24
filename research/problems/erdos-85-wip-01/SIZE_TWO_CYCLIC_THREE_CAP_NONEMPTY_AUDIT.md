# SIZE-TWO-CYCLIC: three-cap middle-nonemptiness audit

## Candidate leaf

At `q=8, a=2`, let the left and middle difference fibres be `0` and `4`,
and let `d1=1`, `d2=2`.  The three cap groups

```text
(left,d1), (left,d2), (middle,d1)
```

force the selected middle-fibre graph to contain an edge.  Deleting any one
cap makes an empty middle graph satisfiable.  This is the nonemptiness half of
the four-short step-cycle mechanism.

## Larger cyclic control

The natural order-four geometry is

```text
m = 2*d2,  4*d2 = 0,
middle = left+m,  right = left-d2.
```

The first manageable larger control was `q=12, a=1`, with
`left=0`, `middle=6`, `right=9`, `d1=1`, and `d2=3`.  The exact graph probe
with the three caps and an empty middle graph returned `unknown` at 300
seconds.  Dropping either all row laws or all column laws returned SAT
immediately.  Therefore this run neither verifies nor refutes a generic
nonemptiness theorem, but confirms that both positional marginal systems are
essential.

## Target-fibre localization at `q=8`

The most economical two-fibre explanation is false.  If each retained cap
counts common neighbours only in the opposite left/middle target block, the
empty-middle system is SAT.

More sharply, the allowed target fibres are

```text
{0,1,3,4,6,7}.
```

Rebuild the three cap constraints while counting common neighbours in every
target fibre except one.  The exact results are:

| omitted target fibre | result with middle graph empty |
|---:|---|
| `0` | SAT |
| `1` | SAT |
| `3` | SAT |
| `4` | UNSAT |
| `6` | SAT |
| `7` | SAT |

Fibre `4` is irrelevant to the cap counts under the empty-middle assumption,
as expected.  Every one of the five non-middle target fibres is individually
essential: omitting any one restores SAT.

## Consequence and stop

The three *source-cap* groups do not define a three-fibre proof.  Their
nonemptiness pressure is a global packing effect spread across the entire
complement of the middle target fibre.  A proof confined to the left-middle
cross-incidence block, or to any fixed proper subset of the remaining target
fibres, cannot establish the q8 claim.

The viable generic shape is consequently an all-target-fibre capacity sum:
under an empty middle block, bound the common-target budget contributed by
each of the `q-3` remaining target fibres and show the exact row/column totals
exceed their combined capacity.  The present computation identifies that
shape but does not supply the required q-generic inequality.
