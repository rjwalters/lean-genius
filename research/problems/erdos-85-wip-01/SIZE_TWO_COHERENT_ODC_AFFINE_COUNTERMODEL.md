# Affine countermodel to the coherent-ODC abstraction

## Purpose

The graph-level size-two dictionary gives, for each normalized component
`a`, a `q`-regular selector graph `S_a` on `2q` vertices and a common ambient
label set of order `q^2`, identified with `E(S_a)`.  For distinct components,
the induced edge bijection sends adjacent edges of one selector graph to
disjoint edges of the other.  Because all bijections use the same ambient
label, they compose coherently.

Coherent composition is not by itself a no-go.  The construction below gives
arbitrarily large triples (indeed, larger families) with exactly these
properties.

## Construction

Let `q` be a prime power and let `P = AG(2,q)`.  Its `q+1` parallel classes
are called directions.  Choose six distinct directions

`d_1, d_2, ..., d_6`

and group them into three pairs.  This is possible when `q >= 5`, in
particular for every binary order `q = 2^k >= 8`.

For the pair `(d_{2i-1}, d_{2i})`, let `S_i = K_{q,q}` whose two shores are
the `q` lines in the two chosen directions.  Every point `p in P` lies on one
line of each direction, so label `p` by the edge

`e_p^i = (the d_{2i-1}-line through p, the d_{2i}-line through p)`.

This is a bijection `P -> E(S_i)`.

## Verified properties

1. In `L(S_i)`, labels `p` and `p'` are adjacent exactly when the two points
   lie on a common line in direction `d_{2i-1}` or `d_{2i}`.

2. The three line graphs are pairwise edge-disjoint.  Two distinct affine
   points determine a unique direction, and the three direction pairs are
   disjoint.

3. The edge bijections are coherently ambient-labelled:

   `psi_jk (psi_ij (e_p^i)) = e_p^k`.

4. A star of `S_i` maps to a perfect matching of `S_j`.  A fixed affine line
   in one source direction meets every line in either target direction once,
   so its `q` point-labels give `q` pairwise disjoint target edges covering
   both shores.

Thus the construction realizes the coherent common-star orthogonal-double-
cover abstraction exactly.  Pairwise spectra, ranks, perfect-matching stars,
and the cocycle law are all compatible.

## Consequence for A-REG-SIZE2-VIA-TRIPLE

Any valid proof of `ThreeSizeTwoViaTripleExclusionPrinciple` must use data
absent from the abstraction above.  The remaining graph-specific input is
the self-indexed diagonal placement: each selector graph's `2q` vertices are
themselves a distinguished subset of the common `q^2` ambient labels, and
the other owner colors restricted to those distinguished labels must be
Hamilton cycles.  The affine construction does not provide that placement.

Therefore none of the following can prove the principle alone:

- coherent composition of the edge bijections;
- pairwise line-graph disjointness;
- the common-star perfect-matching property;
- pairwise spectral or rank identities.

The honest remaining target is a self-indexed coherent-ODC obstruction, not
an ordinary ODC-composition theorem.

## Binary obstruction to loopless affine self-indexing

The missing self-indexing cannot be added to the Desarguesian affine model
while its selector graphs remain the split `K_{q,q}` graphs.  The reason is
an absolute-point calculation for the associated biaffine plane.

Delete one parallel class from `AG(2,q)`.  The retained incidence structure
has the `q^2` affine points and the `q^2` nonvertical affine lines; this is a
biaffine plane (a type-C elliptic semiplane).  A common ambient labeling that
makes its point--line incidence matrix symmetric is a polarity of this
biaffine plane.  The unique projective closure lets us represent it by a
projective correlation preserving the retained point and line sets.

Use homogeneous point coordinates

```text
u = (x,y,1)
```

and choose line coordinates so that the retained nonvertical lines are
exactly those whose `y`-coefficient is nonzero.  If `M` represents the
correlation, that coefficient in `M u` must be nonzero for every affine
pair `(x,y)`.  A linear function of `(x,y,1)` with no zero on `F_q^2` must
have zero `x`- and `y`-coefficients and a nonzero constant coefficient.
After scaling coordinates, and using that a polarity has a symmetric matrix,
`M` therefore has the form

```text
M = [[a,0,b],
     [0,0,c],
     [b,c,d]],
```

with

```text
det(M) = -a c^2.
```

Nondegeneracy forces `a,c != 0`.  An affine point is absolute precisely when

```text
u^T M u = a x^2 + 2b x + 2c y + d = 0.             (A)
```

For binary `q`, equation (A) reduces to

```text
a x^2 + d = 0.
```

The Frobenius map `x |-> x^2` is a bijection of `F_q`, so there is exactly
one solution for `x` and every `y` is then free.  Thus every such polarity
has exactly `q` affine absolute points.

In the symmetric incidence graph those absolute points are diagonal ones,
i.e. loops.  Consequently:

> **No Desarguesian binary biaffine polarity is loopless.**  The coherent
> affine `K_{q,q}` selector model cannot satisfy the simple-graph diagonal
> condition for any binary `q`.

This sharpens the scope of the affine countermodel.  It still proves that
ordinary coherent ODC data are feasible, but it cannot be promoted to the
ambient graph merely by choosing a clever symmetric labeling.  Any affine
countermodel lane must change the selector incidences themselves through a
coherent trade that removes all `q` absolute incidences while preserving the
mutual cross products.

For calibration, each selector graph in the formalized `q=4`
`sixteenRegular` exception is exactly four edge replacements from a best
split model: relative to a suitable balanced shore partition it is obtained from
`K_{4,4}` by deleting one cross perfect matching and adding a perfect
matching inside each shore.  Its defect complement is thereby connected.
The unresolved construction question is whether that shore trade can be
made simultaneously in every affine direction pair at general binary
order; the untraded model is now decisively excluded.

### Exact coherence of the `q=4` shore trade

The local trade normal form is compatible across the two selector colors,
but only by giving up symmetry before the trade.  This was checked by a
complete small enumeration from the formalized `sixteenRegular` edge list.

Each selector has four balanced cuts attaining its maximum cut `12` out of
`16`.  For each cut, delete the four internal selector edges and reassign
their four ambient labels to the four missing cross-shore edges.  There are

```text
4 * 4! = 96
```

labeled `K_(4,4)` completions per selector.  Among the `96^2` pairs of
completions, exactly `16` retain the cross-star law: every ground vertex of
the first selector and every ground vertex of the second selector are
incident with exactly one common ambient label.  Equivalently, the completed
edge bijection remains an ordinary coherent affine ODC.

For all `16` coherent completions, however, the assembled ambient incidence
matrix has

```text
diagonal ones                         0,
asymmetric unordered vertex pairs   16.
```

No completion is symmetric.  This is the finite shadow of the polarity
calculation above: the split incidence can be symmetric only by accepting
absolute points, while a loopless split labeling pays a reciprocity defect.
The `sixteenRegular` shore trades repair all sixteen asymmetric pairs while
turning both selector complements connected.

Thus `q=4` is not merely componentwise close to the affine model; it is a
genuine coherent deformation of it.  The sharpened general question is
quantitative and simultaneous: can `q/2` coherent shore trades repair the
unavoidable loop/asymmetry defect of binary biaffine incidence while
preserving every intermediate-factor tiling?  Neither ordinary ODC
existence nor the absolute-point count alone answers that traded problem.
