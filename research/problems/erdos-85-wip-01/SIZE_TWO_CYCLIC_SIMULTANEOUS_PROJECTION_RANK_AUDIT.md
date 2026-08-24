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
