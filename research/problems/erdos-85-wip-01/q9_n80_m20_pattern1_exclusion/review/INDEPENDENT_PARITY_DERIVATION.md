# Exclusion of the four-partite degree-three N80/Z20 quotient

Proposed paper argument by codex-sol-3, 2026-09-11. Requires independent review.
No graph enumeration or SAT call is used.

Consider the first quotient in accepted review2147: four vertex orbits of
size20 under a semiregular cyclic action, no internal edges, and exactly
three neighbors in every other orbit. All vertices have degree9. Suppose
the graph is C4-free, so every pair of distinct vertices has at most one
common neighbor.

Fix an orbit i and one of its vertices v. There are27 length-two walks from
v back into orbit i: each of the three other orbits contributes3·3. Exactly9
walks return to v. The other18 walks have distinct endpoints by C4-freeness.
Of the19 other vertices in orbit i, exactly one therefore has no common
neighbor with v.

Label each orbit by Z20 so the generator adds1. The block (A²)_ii of the
adjacency square is a symmetric circulant. Its diagonal is9; among its19
nonzero-shift entries,18 are1 and exactly one is0. Symmetry forces the lone
missing shift to be its own negative, hence shift10. Thus

    (A²)_ii = 8I + J − P10,

where P10 is the antipodal permutation matrix.

Evaluate the block-circulant adjacency at the character χ(t)=(−1)^t of Z20.
The four-by-four Fourier matrix H is real symmetric. Its diagonal entries
are0. Each offdiagonal entry H_ij is a sum of three signs, one for each
cross-edge offset, so H_ij is odd and H_ij²≡1 modulo8.

Consequently (H²)_ii is a sum of three odd squares and is congruent to3
modulo8. But the Fourier value of8I+J−P10 is8+0−1=7: the character is
nontrivial, while χ(10)=1. Fourier evaluation preserves multiplication, so
(H²)_ii=7, a contradiction.

Therefore this quotient type has no C4-free lift. This does not by itself
exclude all N80/Z20 graphs: the other types in2147 require their own proofs.
No minimum-degree problem has been restricted by assumption, no frozen CNF
has been changed, and no Lean or global Erdős85 result is claimed.
