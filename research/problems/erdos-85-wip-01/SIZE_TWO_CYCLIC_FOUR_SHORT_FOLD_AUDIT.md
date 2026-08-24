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

## q-generic support caveat

The appealing q8 restatement “the middle graph is supported on `±d₂`” does
not yet generalize.  A cap-deletion audit separates the reasons that the
other q8 steps disappear:

- middle separations `3` and `4` are impossible even with no agreement caps;
  the route-admissibility holes of middle fibre `t=4` already exclude them;
- the remaining competing separation `1` is excluded by exactly the two
  caps `(left,d₂)` and `(right,d₂)`; deleting either makes such an edge SAT,
  while the two `d₁` caps are unnecessary for this exclusion.

Consequently q8 has only one admissible competing undirected step.  At a
larger binary modulus there are many more admissible steps, and no current
theorem eliminates them.  The order-four step-cycle consumer is therefore a
correct factorization of the q8 obstruction, not yet a uniform architecture
for general `q = 2^k`.  A generic proof needs either a new all-other-steps
elimination theorem or a cycle argument that tolerates additional support.

The analogous statement is outright false for general even modulus.  The
translation-invariant exact reciprocal model at

```text
q=12, a=1, left=0, middle=6, right=9, d₁=1, d₂=3
```

has a SAT realization with an empty middle induced graph under the three
caps `(left,d₁)`, `(left,d₂)`, `(middle,d₁)`.  It remains SAT after adding the
fourth cap `(right,d₂)`.  This explicit countermodel lies inside the highly
symmetric translation-invariant subclass and is produced by
`size_two_cyclic_translation_invariant_probe.py` in under one second.  Hence
any surviving uniform theorem must use a specifically binary property; the
natural order-four selector relations alone are insufficient.

The stronger five-cap control is also SAT.  Adding the omitted involutive
middle cap `(middle,6)` while retaining the empty middle graph gives a model
in about one second:

```text
python3 size_two_cyclic_translation_invariant_probe.py 12 --a 1 \
  --cap 0:1 --cap 0:3 --cap 6:1 --cap 6:6 --cap 9:3 \
  --empty-fiber 6 --timeout-ms 300000
```

Thus at q12 not only four-short nonemptiness but the entire five-cell
exclusion is false: all five local agreement caps, exact row/column hits,
looplessness, reciprocity, and an empty selected middle fibre coexist.  The
q8 five-cell MUS is genuinely binary/small-order; it cannot be promoted to
arbitrary even q by changing only the final antipodal terminal.

At q8 the proof target is this local four-lift packet law together with
nonemptiness.  For general q, the first unresolved issue is whether any
analogue can tolerate or eliminate the additional admissible steps.  A
fibre-graded identity remains compatible with the evidence; raw excess
parity, global density, and an unqualified order-four support claim are not.

This file records exact finite evidence, not a proof at general `q`.
