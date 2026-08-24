# SIZE-TWO-CYCLIC: simultaneous projection-rank audit

## Candidate rank mechanism

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

For one source difference fibre `t`, let `B_t` be the binary incidence
matrix between its `q` source bases and all absolute target cells.  Aggregate
target-cell columns first by their row base and then by their column base.
The exact hit laws give two deterministic circulant projections:

```text
R_t = J + X^t + X^(t+1),
C   = J + 1 + X^(-1)
```

over `F2[C_q]` (up to the harmless choice of circulant orientation).  For
`q=2^k`, write `z=1+X`; then `J=z^(q-1)`, and both displayed polynomials are
`z` times a unit.  Hence both projections have rank exactly `q-1`.

This is a genuine binary structural fact, but it is still linear.  The
question is whether the two simultaneous high-rank projections, the empty
target-fibre slab, and all same-fibre caps already force a repeated pair of
columns for one row pair.

## Directed q8 countermodel

They do not.  The translation-invariant probe now has `--directed`, which
drops only the reciprocity identification

```text
E(t,u,r) = E(u,t,-r)
```

and otherwise retains looplessness, every exact target-row and target-column
hit equation, optional empty-fibre constraints, and all requested caps.

At `q=8,a=2`, impose every nonzero same-fibre cap on every allowed fibre and
make fibre `4` empty.  The directed system is SAT:

```text
cap_args=()
for t in 0 1 3 4 6 7; do
  for d in {1..7}; do cap_args+=(--cap "$t:$d"); done
done
python3 size_two_cyclic_translation_invariant_probe.py 8 --a 2 \
  --directed "${cap_args[@]}" --empty-fiber 4 \
  --timeout-ms 300000 --dump-pair-supports
```

The seed-zero model has 288 directed orbit variables and solves immediately.
Every printed fixed-pair support has cardinality one, so all caps genuinely
hold; fibre `4` has no internal step.  Since the exact hit equations are
present, both rank-`7` projections are present as well.

The otherwise identical reciprocal instance is UNSAT immediately: remove
only `--directed` from the displayed command.  Thus the bounded A/B control
changes exactly one family of equations and gives

```text
directed (no block transpose): SAT
reciprocal block transpose:    UNSAT.
```

In the translation-invariant q8 class, reciprocity is therefore the entire
observed feasibility separator after the projections, full caps, empty
fibre, and looplessness have all been fixed.

Thus no argument from the two projection ranks, their kernels, Cauchy--Binet
minors of one block, the empty slab, and the full cap family can prove the
merger.  Such data admit a countermodel even in the intended binary modulus.

## Surviving rank route

Reciprocity is not optional decoration: a viable rank theorem must use the
simultaneous block identities

```text
B_(t,u) = transpose(B_(u,t))
```

across the *entire* fibre family.  In particular, a proof that studies only
`B_t`, or invokes transpose symmetry only after taking its row/column
marginals, is refuted by the directed model.

The remaining algebraic target is a global self-dual block-matrix theorem:
show that the symmetric completion of all high-rank projection blocks cannot
have one empty diagonal block while every within-fibre Gram off-diagonal is
at most one.  This is nonlinear and coupled; no current rank identity proves
it.  The q12 all-cap reciprocal solver is the bounded test of whether such a
theorem may even be generic rather than binary.

## Grouped reciprocity core and cap minimization

The probe option `--reciprocity-core` uses directed variables, adds every
unordered fibre-pair transpose law as a tracked assumption, and greedily
shrinks a sufficient UNSAT core.  On the q8 all-cap empty-4 instance it finds
the five-block irredundant core

```text
(3,4), (3,6), (3,7), (4,6), (4,7).
```

The exact core depends on deletion order, but this one is independently
sufficient and every listed block is necessary relative to the final greedy
set.  It contains no fibre `0` or `1` block, so the bounded contradiction is
far smaller than the entire six-fibre transpose family.

Its graph on fibre labels has additional structure: it is `K4` on
`{3,4,6,7}` with the edge `(6,7)` removed.  Equivalently, it is exactly the
union of two transpose triangles

```text
(3,4,6) and (3,4,7)
```

sharing the block `(3,4)`.  This makes a genuine three-colour block trace a
plausible next diagnostic, but an unweighted triangle trace is still
tautological under transpose.  A separating identity must compare the two
triangles while retaining the different weighted-column shifts/fibre colors
on their `6` and `7` closing blocks.

Cap-family deletion sharpens the subsystem further.  Retain reciprocity
globally, keep fibre `4` empty, and impose all nonzero-separation caps only
on the listed fibre sets.  At `q=8,a=2`:

```text
capped fibres {4,3}:     UNSAT
capped fibres {4,6}:     SAT
capped fibres {4,7}:     SAT
capped fibres {4,6,7}:   SAT.
```

Thus the smallest observed cap target is the empty middle fibre `4` together
with its adjacent fibre `3`; the obstruction is directional, not merely
"empty fibre plus any partner".

Rerunning greedy transpose-core extraction with *only* those cap families
changes the sufficient core to

```text
(3,3), (3,6), (3,7), (4,6), (4,7), (6,6), (6,7), (7,7).
```

Its non-loop block graph is `K4` on `{3,4,6,7}` with `(3,4)` removed: two
triangles `(3,6,7)` and `(4,6,7)` share `(6,7)`.  It also uses self-transpose
constraints on the auxiliary fibres `3,6,7`; the empty self-block `(4,4)` is
already fixed to zero and needs no transpose assumption.  Therefore the
earlier all-cap two-triangle core is not canonical.  What persists across
both deletion experiments is a pair of colored transpose triangles on the
same four fibres, but the shared edge moves when unused cap families are
removed.  Any proposed triangle identity must be checked against the
minimized-cap core, including its self-block symmetries.

At the cap-cell level, translation invariance identifies the caps at `d` and
`-d`, so only shifts `1,2,3,4` need be tested at q8.  Greedy deletion and a
final necessity check reduce the q8 empty-4 UNSAT instance to exactly

```text
cap (3,1), cap (4,1), cap (4,3).
```

Removing any one of these three caps makes the instance SAT.  This explains
why the transpose core is organized around one capped predecessor fibre and
the empty fibre rather than all six allowed fibres.

The natural q12 analogue is not uniform: with `a=1`, fibre `6` empty, and
only caps `(5,1)`, `(6,1)`, `(6,5)`, the reciprocal system is SAT.  Its empty
fibre has a six-target support at antipodal shift `6`, while the three named
caps remain respected.  Thus this exact three-cap terminal is q8 calibration
only; it must not replace the full-cap uniform-even target supported by the
q8/q10/q12 all-cap UNSAT controls.

This two-fibre statement is binary-specific in the bounded controls.  At
`q=12,a=1` with fibre `6` empty, each of the following is SAT:

```text
caps only on {6};
caps only on {6,5};
caps only on {6,7}.
```

The q16 analogue (empty `8`, caps on `{8,7}`) did not return within a bounded
30-second Z3 probe and was stopped rather than promoted to another long
solver lane.  The resulting theorem candidate is precise: explain why, in a
cyclic binary reciprocal code, an empty fibre and the full cap families on
that fibre and its predecessor are incompatible.  A proof still must use
the small transpose-block core above; the directed countermodel rules out a
two-fibre one-block argument that forgets reciprocity.
