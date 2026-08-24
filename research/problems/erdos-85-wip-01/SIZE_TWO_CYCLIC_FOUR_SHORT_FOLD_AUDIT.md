# SIZE-TWO-CYCLIC: four-short half-turn fold audit

## Live leaf

For `q = 8`, `a = 2`, retain only the four cap groups

```text
(0,1), (0,2), (4,1), (6,2).
```

The verified generic interface is
`SizeTwoCyclicLooplessFourCellAntipodalForcing`: these four caps should force
two middle-fibre agreements at the half-turn separation.  Directly forbidding
every internal antipodal `K₂,₂` is UNSAT, so the finite obstruction really is
a middle-fibre rectangle and not merely an artifact of minimizing excess.

## Rejected global mechanisms

The probe reports codegree excess over unordered source pairs.  At the
half-turn, the formal sum over all bases counts every pair twice.  Four-short
models realize unordered middle excess `2` and `4`, hence directed formal
excess `4` and `8`.  This falsifies a proposed directed congruence
`excess ≡ 2 (mod 4)`.

The bare group-ring differential also carries no obstruction.  Over
`F₂`, on each free half-turn orbit, `D = 1 + τ` has matrix

```text
1 1
1 1
```

and therefore `D² = 0` but `ker D = im D`.  Any group-ring proof must use the
extra fibre/cap grading rather than the homology of `D` alone.

Finally, a global folded-capacity pigeonhole is in the wrong direction.
Across twelve four-short models, the middle internal graph had only four
edges in eleven models and eight edges in one.  The six folded quotient-pair
occupancies were respectively

```text
[0,0,0,0,0,4]
[0,0,0,0,4,4].
```

This is far below the rectangle-free capacity of three edges in every
quotient-pair slot.

## Exact local packet test

The same data suggest a local law: an occupied folded middle edge occurs with
all four lifts.  This was tested adversarially, not by sampling.  Add one
disjunction requiring either

- a middle antipodal diameter edge; or
- an internal middle edge between two half-turn orbits whose other three
  lifts are not all present.

Under the four short caps the resulting solver instance is UNSAT.  Thus every
middle internal edge in every `q = 8`, `a = 2` four-short model belongs to a
complete antipodal `K₂,₂`.  Combined with the independently verified UNSAT
test forbidding all such rectangles, the finite obstruction factors as

```text
four short caps
  => middle internal graph is nonempty
  => every occupied folded slot is a four-lift packet
  => middle antipodal rectangle.
```

The two implications have different minimal cap cores.  Requiring the middle
internal graph to be empty is already UNSAT under the three caps

```text
(left,d₁), (left,d₂), (middle,d₁).
```

The `(right,d₂)` cap is unnecessary for nonemptiness, while deleting any one
of those three makes an empty middle graph SAT.  In contrast, the local
four-lift packet law needs all four caps: after deleting any one cap, a model
with a partial occupied folded slot is SAT; with all four it is UNSAT.

Accordingly, the generic proof should split into a three-cell
left-to-middle nonemptiness or mass-transfer lemma and a genuinely ternary
four-cell cocycle lemma in which `(right,d₂)` upgrades an occupied middle slot
to all four lifts.

The q-generic proof target is now this local four-lift packet law together
with nonemptiness.  A 2-lift cocycle or a fibre-graded group-ring identity is
compatible with the evidence; raw excess parity and global density are not.

This file records exact finite evidence, not a proof at general `q`.
