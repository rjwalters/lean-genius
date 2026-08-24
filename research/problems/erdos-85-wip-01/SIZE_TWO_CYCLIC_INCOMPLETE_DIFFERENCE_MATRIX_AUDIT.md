# SIZE-TWO-CYCLIC: incomplete difference-matrix literature audit

## Question

Could `BinarySizeTwoCyclicPackingBound` follow from a classical
nonexistence theorem for mutually orthogonal partial permutations on a
cyclic 2-group?

## Literature verdict

Not from the usual incomplete-difference-matrix obstruction.  Pan, Abel,
Bunjamin, Feng, Tsang Ung, and Wang, [*Difference matrices with five rows
over finite abelian groups*](https://doi.org/10.1007/s10623-021-00981-6),
Designs, Codes and Cryptography 90 (2022), Example 1, give an explicit
`(16,2,5,1)` incomplete cyclic difference matrix.

An `(G,H,5,1)` incomplete difference matrix has five rows and `|G|-|H|`
columns; the difference of every pair of rows lists every element of
`G \ H` exactly once.  For `G = Z/16` and its order-two subgroup
`H = {0,8}`, the cited example therefore supplies four mutually orthogonal
partial permutations with two holes.  The paper prints the full `5 x 14`
matrix.  It also uses this `(16,2,5,1)` object as a recursive ingredient for
larger 2-group constructions.

This complements Wang's special-near-orthomorphism theorem: deleting two
points does not merely permit a single cyclic binary near orthomorphism;
at order 16 it permits a substantial pairwise-orthogonal family.

## Exact boundary with our code

The example is **not** a counterexample to the cyclic routing code.  Its
omitted differences form the fixed subgroup `{0,8}`.  Our source row holes
are consecutive and move with the difference fibre (`{t,t+1}`), while the
absolute column holes are `{0,-1}`; reciprocity also couples different
source fibres after a base shear.  A translation or automorphism of
`Z/16` cannot send the antipodal pair `{0,8}` to the consecutive pair
`{0,1}` because it preserves element order.

Consequently the literature sharply identifies what a viable theorem must
use:

1. the holes are a **consecutive coset boundary**, not an arbitrary
   two-element puncture or subgroup hole;
2. those holes move affinely with the fibre label;
3. all blocks obey the route-reversal shear simultaneously; and
4. the selected same-fibre correlations are capped.

A theorem stated only as “cyclic 2-groups admit no sufficiently large
family of mutually orthogonal two-hole partial permutations” is false.
Likewise, augmentation valuation of the hole polynomial alone is
insufficient: the order-16 incomplete difference matrix already has a
large orthogonal family in the same binary group algebra.  The surviving
three-cap valuation-change lemma must explicitly exploit the consecutive
hole geometry and reciprocity shear.

## Useful translation target

The closest classical language is a *holey/incomplete difference matrix
with non-subgroup, row-dependent holes and an involutive transpose shear*.
No standard existence/nonexistence theorem located in this search includes
all three qualifiers.  If the cyclic routing problem is exported to design
theory, these qualifiers must appear in the definition; otherwise known
order-16 constructions immediately evade the proposed obstruction.
