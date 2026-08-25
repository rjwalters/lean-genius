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
