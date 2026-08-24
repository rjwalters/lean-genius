# Size-two cyclic internal-fibre budget audit

## Corrected target

`SizeTwoCyclicPackingExclusion` has no empty-fibre hypothesis.  One possible
bridge to the banked empty-fibre machinery would be a theorem that every
reciprocal full-cap code has at least one empty internal fibre.

For an allowed difference fibre `t`, write

```text
m_t = number of unordered internal edges in A_tt.
```

The full arbitrary-base probe now has two diagnostics:

- `--dump-internal-profile` prints `m_t`, occupied bases, and internal
  degrees of a SAT model;
- `--require-internal-fibres` requires `m_t > 0` for every allowed `t`.

These options do not change the default encoding.

## q4 calibration

At `q=4,a=1`, requiring every allowed internal fibre to be nonempty is UNSAT
even after deleting every cap:

```text
python3 size_two_cyclic_full_probe.py 4 --a 1 --no-caps \
  --require-internal-fibres --dump-internal-profile

q=4 a=1 vertices=8 edge_variables=28: unsat
```

Without that requirement, Z3 returns a model with both allowed internal
fibres empty.  This proves only the existential statement that the exact q4
hit/reciprocity system forces **some** empty fibre; it does not assert that
every q4 solution has the displayed all-zero profile.

## q8 falsifier for a projection-only argument

At `q=8,a=2`, exact hits and reciprocity without caps admit all six internal
fibres nonempty:

```text
python3 size_two_cyclic_full_probe.py 8 --a 2 --no-caps \
  --require-internal-fibres --dump-internal-profile

q=8 a=2 vertices=48 edge_variables=1128: sat
internal edge counts on fibres 0,1,3,4,6,7: 1,1,3,3,1,1
```

The ten internal edges occupy respectively `2,2,5,5,2,2` bases.  Hence no
identity derived only from the exact row/column projection laws and
reciprocity can force an empty fibre at the first relevant order.  The full
cap family must enter any such theorem essentially.

The same q8 system also has a no-cap SAT model in which every internal fibre
is empty.  Therefore the projection equations do not determine the internal
profile or even its support size; they permit both extremes.

## Consequence

The force-empty bridge remains logically possible but is not a cheap first-
moment consequence.  A valid proof must derive a quantitative collision
inequality in which assuming `m_t >= 1` for all allowed `t` forces a cap
violation.  The natural next statement is not a formula for `sum_t m_t`;
it is a lower bound on same-fibre common-target collisions in terms of the
internal occupied-base profiles.

Until that inequality is named, the empty-fibre T3/T4 and owner-edge results
remain a subcase rather than a proof of the no-empty packing exclusion.
