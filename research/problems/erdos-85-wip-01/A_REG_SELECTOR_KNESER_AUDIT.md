# A-REG selector/Kneser audit

Status: q-generic negative audit under `A-REG-NONBIP`, 22 August 2026.

## Candidate

For each defect component `c`, send an ambient vertex `x` to its component
selector

```text
S_c(x) = N_A(x) ∩ c.
```

If `|c|=q m_c`, every selector has size `m_c`.  A defect edge `xy` has no
common ambient neighbor, hence `S_c(x)` and `S_c(y)` are disjoint for every
coordinate `c`.  This suggests embedding each connected defect component in
a product of Kneser graphs and trying to use connectivity or regularity.

## Existing API already gives the exact representation

This is not a new structural theorem.  The repository already proves:

- `componentNeighborFinset_disjoint_of_secondOrderDefect_adj`;
- `secondOrderDefect_adj_iff_componentNeighborFinset_disjoint_forall`;
- `not_secondOrderDefect_adj_iff_existsUnique_component_selector_inter_nonempty`.

Thus `D` is exactly the intersection of the coordinatewise Kneser
disjointness relations.  A defect pair is disjoint in every coordinate, and
every nondefect pair overlaps in exactly one owner coordinate.  The proposed
embedding is therefore a reformulation of a stronger banked interface, not a
new child of `A-REG-NONBIP`.

For every coordinate with `m_c>=2`, the single-coordinate selector map is
already injective: if two distinct ambient vertices had the same selector,
they would have at least two common neighbors, contradicting C4-freeness.
The size-two modules package this injectivity and sharpen the range to an
exact complement-edge design.  For larger weights, injectivity has too much
room to exert pressure.

## Quantitative slack for weights at least three

A weight-`m` coordinate maps `q^2` ambient vertices into

```text
binom(qm,m)
```

possible selectors.  At the smallest untreated weight `m=3`,

```text
binom(3q,3) / q^2
  = (3q-1)(3q-2) / (2q),
```

which is asymptotic to `(9/2)q`.  The state space therefore has growing,
not shrinking, slack.  For larger fixed `m` the ratio grows as
`Theta(q^(m-2))`.

The Kneser host `KG(qm,m)` also supplies no coarse obstruction:

- it contains triangles because `qm>=3m` for every relevant `q>=3`;
- its degree is `binom(qm-m,m)`, vastly larger than the required defect
  degree `q-1`;
- hence neither nonbipartiteness, odd girth, nor local degree excludes a
  connected `(q-1)`-regular image.

Taking the product of coordinates only restores the exact already-proved
owner-colored design law.  Without using which selector points are joined by
the internal component adjacency, it adds no numerical pressure.

## Disposition

The bare selector/Kneser embedding route is closed.  The missing input is not
coordinatewise disjointness—it is already known exactly—but compatibility
between that disjointness representation and the internal adjacency of each
connected defect component.  Any future consumer should begin from the three
banked exact selector theorems above and add a genuinely internal-`D`
condition, rather than rebuilding the Kneser representation.
