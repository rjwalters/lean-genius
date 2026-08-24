# SIZE-TWO-CYCLIC: missing-fibre excess inside the `q = 8` parity core

## Purpose

For `q = 8`, the loopless parity-class target needs three agreement fibres:
at the critical parameter `a = 2`, every two-fibre subsystem is satisfiable,
but either complete allowed parity class is not.  This audit measures the
smallest failure forced in the omitted third fibre.

For a source difference `t`, write

```text
X_t = sum over unordered source pairs {A,B} in fibre t of
      choose(|N(A) intersect N(B)|, 2).
```

Thus `X_t = 0` is exactly the same-fibre common-neighbour cap.  The probe's
`--codegree-excess-cap N` directly asserts `X_t <= N`.

## Exact `a = 2` table

The two allowed parity classes are

```text
even: {0,4,6}
odd:  {1,3,7}.
```

For each row, the two non-omitted fibres were capped and `X_t` was minimized
in the omitted fibre.

| parity | capped fibres | omitted `t` | exact minimum `X_t` |
|---|---|---:|---:|
| even | `{4,6}` | `0` | `8` |
| even | `{0,6}` | `4` | `2` |
| even | `{0,4}` | `6` | `8` |
| odd | `{3,7}` | `1` | `8` |
| odd | `{1,7}` | `3` | `2` |
| odd | `{1,3}` | `7` | `8` |

Every lower bound is an UNSAT check at the preceding cap (`7` or `1`), and
every upper bound is a SAT witness at the displayed cap.  Representative
minimum profiles are:

```text
X_0 = 8: separation 2 has eight pairs of codegree 2; all others <= 1.
X_4 = 2: separation 4 has two pairs of codegree 2; all others <= 1.
X_6 = 8: separations 2 and 3 each have four pairs of codegree 2.
```

The odd class has the reflected profiles `X_7 = X_0`, `X_3 = X_4`, and
`X_1 = X_6` in the returned minimum witnesses.

Typical verification command (the cap-1 UNSAT side for the middle even
fibre) was:

```bash
python3 size_two_cyclic_exact_graph_probe.py 8 --a 2 \
  --c4-pair-mode same-difference --c4-difference 0 --c4-difference 6 \
  --codegree-profile-difference 4 --codegree-excess-cap 1 \
  --quiet-model --timeout-ms 300000
```

Replacing the final cap by `2` returns SAT.

## Interpretation and stop

The three-fibre obstruction is not merely “the omitted fibre has a
collision”: the exact forced defect depends strongly on its position inside
the parity class.  In particular, any proof that sums three symmetric lower
bounds will miss the `2,8,8` profile.

This suggests targeting a weighted or separation-resolved identity.  The
middle fibre can concentrate its unavoidable defect in the antipodal
separation, while an endpoint must spread eight defects over a full cyclic
orbit (or two four-element orbits).  A useful next theorem would couple these
separation orbits under reciprocity and show that all three zero-excess
requirements cannot coexist.  The computation does not itself provide that
q-generic coupling, so no exclusion theorem is claimed here.
