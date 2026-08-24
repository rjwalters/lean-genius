# Translation-invariant full-cap scope audit

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

## Scope correction

The first reports of the q10 and q12 full-cap verdicts were discussed next to
the empty-fibre collision theorem.  Their exact solver invocations did **not**
contain an empty-fibre constraint.  They establish the stronger statement
inside the translation-invariant ansatz

```text
no reciprocal translation-invariant code satisfies every same-fibre cap,
```

at the tested orders.  They do not directly test the general, base-dependent
empty-fibre merger theorem needed by the Lean proof.

This distinction is essential.  The probe identifies an edge orbit by only
three residues `E(t,u,r)` and therefore assumes invariance under simultaneous
translation of both endpoint bases.  `SizeTwoCyclicFullPermutationCode` in
Lean retains a separate permutation at every base `x`; no theorem currently
reduces it to this invariant subclass.

## Exact q8 no-empty control

With forbidden fibres `{2,5}`, impose every nonzero-separation cap on every
allowed fibre and no empty block:

```bash
cap_args=()
for t in 0 1 3 4 6 7; do
  for d in {1..7}; do cap_args+=(--cap "$t:$d"); done
done
python3 size_two_cyclic_translation_invariant_probe.py 8 --a 2 \
  "${cap_args[@]}" --reciprocity-core --timeout-ms 300000
```

The result is immediate UNSAT.  Greedy deletion leaves

```text
(3,4), (3,6), (3,7), (4,6), (4,7), (6,7), (7,7).
```

The non-loop portion is the complete graph on fibre labels `{3,4,6,7}`;
one self-block `(7,7)` is also required relative to this deletion order.
Thus the empty `(4,4)` constraint used in earlier q8 experiments was not
needed once all cap families were imposed.

This also explains why the smaller empty-fibre transpose cores should not be
treated as canonical global trace shapes.  Removing the empty constraint
changes which self block and closing edge participate.

## Exact q10 no-empty control

Claude's original q10 command used holes `{1,8}` and all caps on the eight
allowed fibres, with no `--empty-fiber`.  Repeating it with grouped
reciprocity assumptions gives:

```bash
cap_args=()
for t in 0 2 3 4 5 6 7 9; do
  for d in {1..9}; do cap_args+=(--cap "$t:$d"); done
done
python3 size_two_cyclic_translation_invariant_probe.py 10 --a 1 \
  "${cap_args[@]}" --reciprocity-core --timeout-ms 300000
```

The result is UNSAT.  The greedy core is

```text
(2,7), (2,9),
(3,4), (3,5), (3,6), (3,7), (3,9),
(4,5), (4,6), (4,7), (4,9),
(5,5), (5,6), (5,7), (5,9),
(6,7), (6,9),
(7,7), (7,9),
(9,9).
```

Its non-loop restriction to `{3,4,5,6,7,9}` is `K_6`; it additionally uses
self blocks `(5,5),(7,7),(9,9)` and the two edges from fibre `2` to `7,9`.
Unlike q8, this greedy core does not isolate a small pair of triangles.  The
difference is a warning against promoting the q8 core graph itself to a
uniform theorem.

The ungrouped q10 instance has 328 reciprocal orbit variables and was also
UNSAT.  The grouped directed encoding has 640 variables because both
orientations exist before tracked transpose equations are assumed.

## q12 and current evidence

The q12 instance with holes `{1,10}` likewise imposed all caps on all ten
allowed fibres and no empty block.  Its exported CNF had 6,276 variables and
166,900 clauses and Kissat proved UNSAT.  Together the exact evidence is now:

```text
q=8:  TI + reciprocity + all caps, no empty assumption -> UNSAT
q=10: TI + reciprocity + all caps, no empty assumption -> UNSAT
q=12: TI + reciprocity + all caps, no empty assumption -> UNSAT
```

The q8 directed model remains SAT even with all caps and an empty fibre, so
block transpose is still an essential separator inside the ansatz.

## Consequences for theorem selection

There are now two logically distinct targets:

1. **TI algebra theorem:** a Hermitian group-ring block matrix satisfying the
   two exact projection identities cannot satisfy all coefficientwise caps.
   No empty diagonal block is needed in the tested orders.
2. **General Lean theorem:** a base-dependent reciprocal permutation code
   with the structural empty fibre forced upstream cannot satisfy all caps.
   Translation-invariant UNSAT is evidence about mechanisms, not a proof or
   even a direct finite falsifier for this statement.

A group-ring trace identity proved only for circulant blocks closes target 1
but does not close A-REG-NONBIP unless accompanied by a new symmetrization
reduction.  Conversely, the owner-edge lower bound and merger problem belong
to target 2 and should not cite q10/q12 TI UNSAT as if those solvers included
the empty-fibre hypothesis or arbitrary base dependence.

The correct use of the TI cores is diagnostic: locate a transpose-sensitive,
color-preserving identity, then restate it for arbitrary q-by-q base blocks.
The changing q8/q10 core graphs show that the identity should be global in
the fibre colors rather than tied to one fixed four-fibre pattern.
