# Trace-color subsystem audit

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

## Purpose

The colored trace-reversal audit showed that, at `q=8`, the combination of
all degree-three and degree-four closed-word reversal identities separates a
directed full-cap empty-fibre model from reciprocal models.  The raw tracked
core contained hundreds of individual identities and did not identify a
theorem-shaped subsystem.

This audit groups those identities by fibre colors and asks two sharper
questions:

1. Is the separator supported on the small four-fibre transpose core found
   by the entrywise-reciprocity solver?
2. Does the separator actually use the empty diagonal block, or does it only
   detect the independent translation-invariant full-cap obstruction?

## Probe extensions

`size_two_cyclic_translation_invariant_probe.py` now supports:

- `--trace-colors t,u,...`, restricting imposed triangle and four-cycle
  reversal identities to closed words all of whose colors lie in the listed
  set;
- `--trace-color-core`, which tracks all identities with the same sorted
  color multiset under one assumption and greedily deletes whole groups; and
- `--core-check-timeout-ms`, a separate short timeout for each deletion
  check, preventing grouped shrinking from becoming an unbounded solver
  lane.

The trace-color mode uses directed edge variables.  An initial test exposed a
mode-selection bug in which the new flag accidentally retained the ordinary
reciprocal `edge_key`; that was fixed before any verdict below was recorded.
The corrected runs have 288 directed orbit variables at q8, versus roughly
half that count in the reciprocal encoding.

## The four-fibre core is insufficient

Use all caps on all allowed fibres at `q=8,a=2`, make fibre 4 empty, impose
both trace-reversal degrees, but retain only the entrywise core colors:

```bash
--trace-colors 3,4,6,7
```

The result is SAT.  Thus the `K4`/two-triangle shapes found by greedy
entrywise transpose deletion do not support the weaker trace mechanism.
Trace reversal needs information exported through additional fibre colors.

## Every allowed fibre color is essential in the leave-one-out test

The allowed colors are

```text
{0,1,3,4,6,7}.
```

With fibre 4 empty and every same-fibre cap imposed, both trace families on
the full six-color set are UNSAT (the original separator).  Restricting trace
words to any one of the six five-color subsets is SAT:

```text
trace colors {1,3,4,6,7}       SAT   (omit 0)
trace colors {0,3,4,6,7}       SAT   (omit 1)
trace colors {0,1,4,6,7}       SAT   (omit 3)
trace colors {0,1,3,6,7}       SAT   (omit 4)
trace colors {0,1,3,4,7}       SAT   (omit 6)
trace colors {0,1,3,4,6}       SAT   (omit 7)
```

These are satisfiability controls, not claims of uniqueness or minimum
constraint cardinality.  They do prove that no proper five-color restriction
of this particular full trace family is already contradictory.  Consequently
the proof target should sum or propagate around the entire allowed-fibre
family rather than focus on the q8 four-fibre core.

## The empty block remains essential to the trace separator

Remove only `--empty-fiber 4`, retain all q8 caps and impose every triangle
and four-cycle reversal identity on all six colors.  The result is SAT:

```text
q=8 a=2 orbit_variables=288: sat
```

This differs from entrywise reciprocity: the fully reciprocal TI all-cap
system is UNSAT even without an empty-fibre constraint.  Therefore low-degree
trace reversal is genuinely weaker and isolates a mechanism closer to the
general Lean target:

```text
full caps + empty diagonal block + global color family
  + degree-3 reversal + degree-4 reversal -> contradiction       (q8 TI).
```

Neither trace degree alone suffices, every color is needed in the
leave-one-out test, and the empty diagonal is needed.  Those three facts make
the separator substantially more faithful to the desired base-dependent
empty-fibre theorem than the raw TI reciprocity UNSAT result.

## Grouped core result and limitation

Grouping by exact color multiset is semantically natural, but greedy deletion
is still computationally diffuse.  With a 250 ms timeout per deletion, most
groups remain because an `unknown` result cannot justify removing an
assumption.  The resulting long list is not evidence that every multiset is
mathematically necessary.  The reliable theorem-shaped evidence is the
six explicit leave-one-color-out SAT controls above.

## Corrected proof target

The next analytic statement should use the full family of allowed colors and
combine odd and even closed words.  A plausible form is a global sum of
triangle-reversal defects weighted by the two affine projection characters,
whose square or transport is evaluated using four-cycle reversal.  The empty
diagonal must leave a boundary term.  Any formula involving only one trace
degree, one fixed source fibre, or the q8 four-fibre transpose core is now
refuted by the controls.

The TI experiment still does not prove the arbitrary-block statement.  Its
value is that the hypotheses of a prospective lift are now sharply scoped:
global color propagation, the selected zero diagonal block, and the
interaction of degree 3 with degree 4.
