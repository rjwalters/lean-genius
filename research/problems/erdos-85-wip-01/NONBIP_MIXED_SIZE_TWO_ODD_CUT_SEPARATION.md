# Size-two fractional witnesses violate matching odd cuts

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: exact separation of the two banked fractional witnesses from the
stronger columnwise matching relaxation. This does not disprove existence
of another fractional witness satisfying all matching inequalities, or of
an integral exterior extension. It identifies constraints missing from the
current witnesses and gives the next bounded test.

Update: that next test is now settled at q=16 by the independently reviewed
integral reciprocal witness in
`NONBIP_MIXED_SIZE_TWO_INTEGRAL_CROSS_BLOCK_CUT.md`. The certificates below
remain valid for the older fractional witnesses, but the stronger joint
matching relaxation is feasible at q=16. Its off-diagonal Gram/C4
condition remains the unresolved requirement.

## The necessary inequality

Use `F=E(L)`, `H`, `B`, and the symmetric fractional exterior matrix T from
`NONBIP_MIXED_SIZE_TWO_SYMMETRIC_FRACTIONAL_CUT.md`. For a column
`e={a,b}`, the cross equation says its edge weights have degree one on

```
V_e = C \ (N_H(a) union N_H(b))
```

and degree zero elsewhere. In an actual integral extension these edges
form a perfect matching of `L[V_e]`, avoiding e itself.

For every odd-cardinality subset `U` of V_e, a matching can use at most
`(|U|-1)/2` edges wholly inside U. Hence every convex combination of
such matchings obeys

```
sum_{f subset U} T[f,e] <= (|U|-1)/2.                    (1)
```

The degree-one equations give

```
2 sum_{f subset U} T[f,e]
  + sum_{|f intersect U|=1} T[f,e] = |U|.
```

Thus (1) is equivalent to the odd-cut inequality

```
sum_{|f intersect U|=1} T[f,e] >= 1.                    (2)
```

This elementary argument proves necessity without requiring a polyhedral
characterization theorem. Symmetry plus degree-one equations and bounds
alone do not imply it, as the exact certificates below show.

## Exact violations in the existing artifacts

All labels are residues modulo 2q. The tested values are those stored in
`size_two_symmetric_fractional_witnesses.json`.

| q | Column e | Odd set U | Cut weight (required >=1) |
| --- | --- | --- | --- |
| 12 | {0,10} | {3,5,7,13,15,19,21} | 851/1798 |
| 16 | {0,1} | {4,8,10,12,14,18,22,24,26,28,30} | 43324984/278573383 |
| 16 | {0,12} | {0,10,24} | 221067650/278573383 |

Each U avoids the four excluded H-neighbors for its column. In particular,
the last certificate is a triangle inequality: the total weight on the
three L-edges among `{0,10,24}` in column `{0,12}` equals

```
614652499 / 557146766 > 1.
```

At most one edge of a matching can lie in a triangle. Thus this column is
not even a convex combination of its valid local matchings. This is
stronger than observing fractional entries or a squared-norm deficit.

`check_size_two_odd_cut_certificates.py` independently expands only the
relevant columns from the stored dihedral orbits, checks degree one on
V_e, and directly sums both internal and crossing weights using exact
`Fraction` arithmetic. It requires no optimizer or graph package. All
three certificates pass.

## Discovery and next test

The witnesses were found using integer-capacity Gomory-Hu cut trees after
scaling the rational columns by their common denominators. Odd shores of
the tree's fundamental cuts supply separating inequalities. This follows
the minimum-odd-cut method described in Algorithm 1 of Letchford and
Theis, [*Odd Minimum Cut Sets and b-Matchings Revisited*](https://arxiv.org/abs/math/0607088).
The saved certificates need only direct summation, so their validity does
not depend on trusting the separation algorithm or its implementation.

The proposed next test was the **joint** symmetric linear relaxation with each
column constrained by these matching inequalities, adding violated cuts
and their symmetry translates. The existing fractional witnesses cannot
settle that stronger interface. Conversely, the independent integral
columns of `NONBIP_MIXED_SIZE_TWO_COLUMN_MATCHING_CUT.md` do not settle it
either: those columns fail reciprocity.

The integral reciprocal q=16 witness now settles that test affirmatively
at this parameter. Averaging it with its reflection gives a dihedrally
invariant symmetric cross block whose columns are averages of two actual
perfect matchings. All odd-cut inequalities therefore hold, without
enumerating odd sets. The independent review checked every cross-block
entry and the actual column matchings. A cutting-plane rerun is unnecessary.

That witness has an explicit exterior four-cycle, so it fails the
off-diagonal Gram/common-neighbor cap. These finite separations and the
replacement witness provide neither a uniform nonexistence theorem nor
an ambient construction or closure of A-REG-NONBIP. Continue with the
disjoint-selector common-neighbor cap, rather than more matching-polytope
constraints at q=16.
