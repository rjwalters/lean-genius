# Consecutive-hole design literature audit

## Target

Node: `BinarySizeTwoCyclicPackingBound` under A.5.3 / `GAP
A-REG-NONBIP`.

The reduced cyclic routing array resembles a Howell design or Room frame,
but those generic classes are broadly existential.  This audit asked whether
the *moving consecutive* empty cells, together with cyclic translation and
transpose reciprocity, have a named obstruction in the design literature.

## Closest named object: cyclic difference covering arrays

The closest precise match found is a cyclic difference covering array
`DCA*(k,2n;2n)`.  Demirkale--Donovan--Hall--Khodkar--Rao define its nonzero
columns to be permutations of `Z/(2n)` and require every nonzero difference
between two such columns to occur.  Their standard consequence is sharper:
the difference multiset is

```text
{1,2,...,n,n,...,2n-1},
```

so the antipode `n` occurs twice and every other nonzero element once.  They
also give an explicit cyclic `DCA*(3,2n;2n)` for every `n >= 2`; the
four-column existence spectrum is almost complete.  See
[Difference Covering Arrays and Pseudo-Orthogonal Latin Squares](https://arxiv.org/abs/1502.02332),
especially the definition and construction preceding its equation (1).

This is a useful identification, but not a new terminal.  In our language it
is the same local phenomenon already supplied by the Hall--Paige defect
lemma: a punctured permutation comparison must repeat the antipodal
difference.  It does not say that two defect tokens in different route rows
merge onto one fixed source pair with two distinct common targets.  Reversal
again changes the object type from a within-route repeated difference to a
cross-base common-neighbour token.

## Howell and frame results do not retain the moving-hole coupling

Generalized Howell designs impose row/column resolutions and pair caps, but
allow empty cells as an unlabelled pattern.  Existence results even cover
families with exactly two empty cells per row and column; for example
Abel--Bailey--Burgess--Danziger--Mendelsohn prove broad two-empty-cell
existence for block size three in
[On generalized Howell designs with block size three](https://arxiv.org/abs/1501.02502).
Room-frame and skew-Howell constructions likewise treat holes as groups or
subarrays, commonly filled recursively.

Those equivalences allow independent row, column, and symbol relabellings.
They therefore forget the datum essential here:

```text
source fibre t
  -> missing target rows t,t+1
  -> fixed missing columns 0,-1
  -> transpose/reversal identifies the target fibre with a new source fibre.
```

Calling the two missing rows "consecutive" has no invariant meaning after
the standard design isomorphisms unless this affine label coupling is kept.
No theorem located in Howell/Room-frame terminology retains all four parts
of this diagram.  `Z`-cyclic Room-square results preserve development by a
cyclic group, but again concern construction/existence and do not impose the
moving two-hole/transpose compatibility above.

## Near-complete mappings name the sharp local profile, not its coupling

There is a second, closer vocabulary for the new defect-rank endpoint.
Paige's **proper near complete mappings** (equivalently, near
orthomorphisms or maximal near transversals of a group table) are the
standard replacement for complete mappings when the Sylow `2`-subgroup is
nontrivial cyclic.  See the summary and references in Bowtell--Montgomery,
[Latin squares with maximal partial transversals of many
lengths](https://doi.org/10.1016/j.jcta.2021.105403), Section 5.  Bedford's
**quasi-complete mappings** are another one-defect relaxation, introduced
to construct quasi-orthogonal Latin squares; see
[Quasi-Orthogonal Latin Squares and Related
Designs](https://combinatorialpress.com/jcmcc-articles/volume-026/quasi-orthogonal-latin-squares-and-related-designs/).

These names are relevant because, in the extremal permutation coordinates,
each source has a permutation `psi : R -> R` and its block defect is the
failure of

```text
r |-> -t-r-psi(r)
```

to permute the target-fibre set.  A rank-one source has exactly the familiar
one-missing/one-repeated near-complete profile.  But the published objects
do not retain our fixed two-puncture domain `R = Z/q \\ {0,1}`, nor do they
couple a family of such maps by the shifted-base involution

```text
psi_(x+t+r,u)(s) = r,       u = -t-r-s.
```

This distinction is substantive rather than terminological.  Wang's
[On Special Near Orthomorphisms](https://combinatorialpress.com/article/jcmcc/Volume%20021/vol-21-paper%2013.pdf)
constructs special near orthomorphisms for broad even-order abelian groups
with cyclic Sylow `2`-subgroup (and gives an explicit `Z/8` example).
Thus local near-orthomorphisms are plentiful in precisely the binary cyclic
regime where the full reciprocal family is obstructed.  The q8 bound
`sum_p r(p) >= q^2` therefore cannot follow from a stronger prohibition on
one local permutation: it is genuinely a theorem, still absent from the
literature located here, about the total defect of a *coupled family* of
near-complete mappings.

## Verdict and usable residue

The generic Howell/Room-frame literature route remains **cut**.  The more
specific DCA literature supplies a clean name for the local antipodal
duplicate, but it stops at exactly the already-documented missing arrow:

```text
forced local antipodal defect
  -/-> two common targets owned by one fixed source pair.
```

The literature does suggest the right boundary for any future import: it
must be a theorem about a *self-dual family* of cyclic DCAs whose omitted
rows depend affinely on the column/fibre label.  A theorem about a single
DCA, Howell design, Room square, frame, or arbitrary two-empty-cell array
cannot see the required token merging.  No such named self-dual moving-hole
theorem was found in this bounded search.
