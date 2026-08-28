# Size-two faithful ternary page-parity audit

Date: 2026-08-27.  Node: `A-REG-NONBIP / NONBIP-MIXED`, faithful
`ThreeSizeTwoViaTripleExclusionPrinciple` branch.

Status: **scalar parity routes cut; page-sensitive support remains open**.

## Faithful composition input

For endpoint components `c,e,f` and routing color `d`, the proved theorem
`binarySquare_regular_sizeTwoRoutingColor_comp` gives

```text
R_d^(ce) R_d^(ef)
  = 2 R_d^(cf) + B_dc^T A_(d,e) B_df.                 (1)
```

Here every column of `B_dc` and `B_df` has weight two, and in the cyclic
ternary branch `A_(d,e)` is the adjacency matrix of a Hamilton cycle.  The
correction entry at `(x,w)` therefore counts the owner-cycle edges between
the two-point traces of `x` and `w` inside `d`.  This is the first term in
the routing composition that sees the self-indexed owner pages rather than
only coherent edge-label bijections.

## The first parities are tautological

Reducing (1) modulo two removes the direct-routing term, but supplies no odd
class.  Since both trace-incidence matrices have even margins and the cycle
matrix is two-regular, every row and column sum of

```text
C_(d;e;c,f) = B_dc^T A_(d,e) B_df
```

is even.  This is the matrix form of the already-proved four-cells-per-row
via-color law, not a new obstruction.

The integer total is equally fixed.  The product on the left of (1) has
mass `32q`, the doubled direct relation has mass `16q`, and the correction
has mass `16q`.  Summing, tracing against the all-ones matrix, or applying
an endpoint parity weight therefore recovers only the known margins.

Cycle-permutation signs do not improve this.  Coherent ambient labeling
gives `P_ca P_bc P_ab=1`, so the product of the three signs is `+1`
definitionally.  An individual sign is not coordinate-free: translating
one cyclic edge coordinate by one step reverses the sign at even order while
preserving adjacency, disjointness, and every routing margin.  Thus neither
the sign product nor a single-factor sign can prove the ternary exclusion.

## Hall--Paige does not acquire a canonical completion

A single normalized cyclic routing block is a two-punctured near
orthomorphism.  Ordinary Hall--Paige cannot exclude it; special near
orthomorphisms exist at binary cyclic orders.  The faithful third via color
does not canonically fill the two holes.

Indeed, for fixed distinct source and target components, every size-two via
color occupies exactly **four** cells in each endpoint row, by
`binarySquare_regular_threeSizeTwoParts_routing_row_card_eq_four`.  The full
row has `2q` cells and is tiled by all `q/2` component colors.  At `q=8`,
three colors cover twelve of the sixteen cells and the fourth color still
occupies four.  Selecting one of a third color's four cells to fill a
particular puncture is an extra choice, and different choices are not
identified by the two-fold star cover.  Hence the faithful three-color
interface does not promote the near orthomorphism to a choice-free complete
mapping.

## Bounded disposition

The affine coherent-ODC countermodel already cuts every argument using only
edge-bijection coherence, pairwise star matchings, or pairwise spectra.  The
calculations above additionally cut the first page-sensitive scalar
invariants: correction row/column parity, total correction mass, cyclic sign
holonomy, and a three-color Hall--Paige completion.

The remaining non-tautological object is the **entrywise support or rank
profile** of the correction matrix `B_dc^T A_(d,e) B_df`, especially a
cyclic product of three such corrections with the common ambient labels
retained.  No current theorem forces an odd diagonal, a rank excess, or a
support overlap incompatible with routing-color disjointness.  Without one
of those consumers, the faithful ternary parity lane is stopped under goal
36 and should not produce a Lean wrapper.
