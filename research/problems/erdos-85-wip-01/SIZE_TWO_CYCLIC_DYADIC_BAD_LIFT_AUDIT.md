# SIZE-TWO-CYCLIC: dyadic bad-lift audit

## The two fibres that do not survive folding

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

Let the upper modulus be `q=2n`, with forbidden difference fibres

```text
a, b=-1-a  in Z/(2n).
```

After projection to `Z/n`, the forbidden lower fibres are `a mod n` and
`b mod n`.  Each has two upper lifts.  One lift is already forbidden
upstairs; the other lift is allowed upstairs but projects to a forbidden
lower fibre.  These two **bad lifts** are

```text
a+n, b+n  in Z/(2n).
```

(Addition by `n` means the unique other lift, so the formula is independent
of representatives.)  Thus an upper allowed target fibre descends to a
lower allowed fibre exactly when it is not one of these two bad lifts.

This is a concrete obstruction omitted by the raw q-to-q/2 fold.  Even
before addressing multiplicity-two hits or reciprocal selection, a common
target token can disappear because its target difference becomes a hole in
the quotient.

## Correct two-target fold classification

For a fixed source pair with two distinct common target cells, first classify
their target fibres against the bad-lift set.

1. If either target uses a bad-lift fibre, the pair does not descend intact.
   A cap-dependent theorem must show that this leakage already creates the
   designated short/antipodal violation, or transports the leaking cell to a
   good fibre.
2. If both target fibres are good, their projected cells are valid lower
   cells.  If the two projected cells remain distinct, they are candidates
   for an intact lower double token.  If they coincide, the upper cells
   differ by a half-turn in their lift bits and belong to the immediate
   antipodal/rectangle branch.

This arithmetic trichotomy still does **not** prove that projected routes
form a lower exact code: the raw fold has multiplicity-two hits.  It only
isolates the first place where the third/fourth caps can make coherent
halving possible.  Any selection theorem must also choose the same lift for
both target cells and respect route reversal.

## q8 calibration

At `q=8,a=2`, the upper forbidden fibres are `2,5`, the lower forbidden
fibres modulo four are `2,1`, and the allowed bad lifts are

```text
6 and 1.
```

With only caps `(0,1)` and `(0,2)`, the seed-7 SAT model has a double support
at `(t,d)=(6,2)` with targets

```text
(u,base) = (1,2), (3,3).
```

The first target fibre `u=1` is a bad lift, while `u=3` is good.  This mixed
pair cannot descend intact, and indeed the same model has no double support
at the doubled separation `4` in any fibre.  This explains the previously
observed failure of weak doubling more precisely than a missing histogram
entry.

After adding the third cap `(4,1)`, the calibrated SAT model has all its
double supports at the antipodal source separation `4`; their target fibres
are `7,3,4,0`, all good modulo four.  The displayed target pairs differ by
the upper half-turn in base (`2` versus `6`) and collapse to one lower cell,
placing them exactly in the immediate antipodal branch.  This is model
evidence, not yet a universal three-cap theorem.

## Sharpened missing lemma and falsifier

The coherent-halving candidate should now be split into two named claims:

```text
bad-lift elimination:
  under the full short-cap pattern, a double token using a bad-lift target
  fibre already forces a designated cap violation;

good-pair coherence:
  a double token with two good targets either collapses as a half-turn pair
  or admits one reciprocity-stable lift selection carrying both targets to
  a lower double token.
```

For a q16 tuple witness, print the bad-lift status and lower projection of
each target in every double support.  One mixed good/bad pair surviving all
short caps without a designated violation refutes the first claim.  Two good
targets whose required route lift choices disagree refute the second.  This
is strictly stronger and more diagnostic than checking only whether some
double support exists at separation `2d`.
