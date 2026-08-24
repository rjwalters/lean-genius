# SIZE-TWO-CYCLIC: Hall--Paige defect-index audit

## Proposed binary mechanism

For each source fibre, the target-difference map is a two-punctured analogue
of an orthomorphism.  `not_injective_targetDifference_of_four_dvd` already
formalizes the cyclic-2-group obstruction: when `4 ∣ q`, every such map has a
repeated target difference.  A tempting strengthening is to grade every
repetition pair by the 2-adic valuation of its row separation, sum these
defects over all source fibres, and use reciprocity to pair every contribution
except an antipodal survivor.

This would be useful only if the defect multiset were closed under
reciprocity.  It is not.

## Exact failure of closure

If rows `r₁,r₂` in a source block have the same target difference, the two
routed darts land in a common target fibre.  Reversing them produces two
different source bases in that target fibre.  Thus reciprocity sends

```text
within-block repeated target difference
    -> between-base common-neighbour pair,
```

not another within-block repeated target difference.  The 2-adic separation
is preserved, as recorded by the augmentation-filtration audit, but the
*kind* of object changes.  Consequently there is no involution on the proposed
defect multiset and no parity sum to which the Hall--Paige obstruction applies.

## Bounded model check

The translation-invariant exact probe was extended with `--dump-defects` to
print repetition pairs by `v2` level.  The output confirms that the raw defect
parities are unconstrained even at `q=8`:

| retained q8 caps | all-fibre defect levels |
|---|---|
| none | `{0:54, 1:24, 2:12}` |
| `left:d2`, `right:d2` | `{0:18, 1:4}` |
| `left:d1` only | `{0:6, 1:5}` |
| `right:d2` only | `{0:12, 1:4, 2:4}` |
| `left:d1`, `middle:d1` | `{0:4, 1:2, 2:4}` |

In particular the single-cap model has an odd level-1 total.  This is an
explicit witness that reciprocity does not pair the within-block defects at a
fixed 2-adic level, even for a binary modulus.

For comparison, the exact translation-invariant `q=12` four-cap empty-middle
countermodel has defect levels `{0:24, 1:15, 2:3, 3:4}`.  The histogram sees
the binary/nonbinary arithmetic but supplies no contradiction in either case.

## Verdict

The route

```text
Hall--Paige non-orthomorphism
  -> one repetition per fibre
  -> reciprocal parity of repetitions
  -> antipodal double owner
```

stops at the second arrow.  The first statement is valid and already banked;
the proposed reciprocal parity is false because reversal changes a fibre
defect into a cross-base collision.  Reviving this idea would require a new
closed state space containing both kinds of objects and a conservation law
between them.  Counting only target-difference repetitions cannot prove
`BinarySizeTwoCyclicPackingBound`.
