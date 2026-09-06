# Integral reciprocal cross block: a binary witness with a four-cycle

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: exact finite witness at `q=16` to the integral reciprocal
cross-block equations. The off-diagonal exterior Gram condition fails.
No ambient graph or uniform extension theorem is asserted.

## Stronger than the fractional relaxation

Use the C-shore circulant carrier from
`NONBIP_MIXED_SIZE_TWO_TRIPLE_COMPANION_AUDIT.md`, with `n=q-2=14`,
`|C|=32`, and `F=E(L)` of size 224. The new matrix T is an actual symmetric
zero-one matrix, has zero diagonal and row sums n, and satisfies

```text
HB+BT=J.
```

In particular, for every selector edge e, the T-neighbors of e form a
perfect matching in L on `C\(N_H(a) union N_H(b))`, where `e={a,b}`.
All these matchings coexist reciprocally in one matrix T. The exterior
Gram diagonal also holds: `(BᵀB+T²)_ee=2+n=q`.

This strengthens the previous fractional example by removing its
integrality failure. It rules out excluding this binary parameter from
the integral cross-block conditions alone. It does not rule out an
argument at other parameters or using the off-diagonal exterior Gram law.

## Exact record and verification

`size_two_integral_cross_block_q16.json` lists 50 nonzero translation
orbits of unordered pairs of selector edges. An orbit means all shifts
of both edges by the same residue modulo 32; reversing an unordered pair
is included. Unlisted pairs have value zero. Reflection invariance is not
imposed and the witness is not reflection invariant.

```sh
python3 research/problems/erdos-85-wip-01/check_size_two_integral_cross_block.py
```

The standard-library checker reconstructs the complete matrix using sets,
checks all 7,168 cross-block entries, verifies the actual local perfect
matchings, symmetry, zero diagonal, row sums, and translation invariance.
It also constructs and checks the reflected witness. All checks use exact
integer operations, independently of the mixed-integer solver.

Discovery: a bounded search with both translation and reflection
invariance reported infeasible; this was not treated as an unrestricted
obstruction. A subsequent 30-second-bounded search imposing translation
invariance only found the recorded zero-one solution. Only the exact
expanded witness is used as mathematical evidence.

## Explicit failure of the common-neighbor cap

The exterior labels

```text
{0,1}, {14,15}, {2,10}, {18,19}
```

are four distinct vertices of F and form a T-cycle in the displayed order.
Thus `{0,1}` and `{2,10}` have the two common neighbors `{14,15}` and
`{18,19}`. Since the two selectors are disjoint, their `BᵀB` entry is zero;
their `T²` entry is at least two. No zero-one defect adjacency `D_F` can
make `BᵀB+T²=(q-1)I+J-D_F` hold at this entry.

The checker finds maximum T-codegree eight and 4,912 unordered pairs with
codegree above one. Incident selector pairs have codegree zero, exactly as
the cross-block matching law requires. The uncontrolled disjoint-selector
pairs are therefore the precise failure, not an error in local matching.

## The local transition-cycle condition also holds

Keep only T-edges whose selector labels share a C-endpoint. On each parity
shore, these edges form a 2-factor J on the 96 same-parity selector labels:
each selector has one such neighbor through each of its two endpoints.
Opposite-parity selectors have no J-neighbors. The checker verifies the
degrees and traverses every component. On each parity shore the complete
list of J-cycle lengths is

```text
8, 8, 16, 32, 32.
```

Thus every J-cycle has length at least five, even though the full T has
the explicit four-cycle above. The proposed transition-system condition
alone does not exclude this witness. A successful use of that 2-factor
must also constrain its interaction with T-edges between disjoint
selectors; no claim is made that those interactions are feasible.

## Consequence for the blossom relaxation

Let `T'` be the reflection of T and set `S=(T+T')/2`. Both summands satisfy
the integral reciprocal cross-block conditions. The matrix S is invariant
under translations and reflection; each column is the average of two
actual perfect matchings on its required support.

Therefore S satisfies every local perfect-matching odd-cut inequality:
an odd subset of the supported vertices has an odd, hence positive,
number of crossing edges in each matching, so its S-cut capacity is at
least one. This is a proof for all odd subsets, not a sampled cut check.

The violated odd cuts in the earlier fractional witnesses were real, but
adding all of them cannot make the dihedral convex-matching relaxation
infeasible at q=16: S is a witness. A cutting-plane search targeting that
relaxation is therefore unnecessary.

## Remaining link

Integrality, reciprocity, all local matching polytopes, and the exterior
Gram diagonal are jointly feasible at this parameter. A closing argument
for this carrier must use the off-diagonal common-neighbor cap (or an
additional consequence not present here). The global Erdős 85 objective
and the q-generic A-REG-NONBIP node remain open.
