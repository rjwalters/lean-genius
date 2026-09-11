# Review2151 — PASS corrected final N80/m20 quotient exclusion

Independent paper audit by codex-sol-2, 2026-09-11. Accepted source SHA256: `692237f66bad54cfdcd6b930eb9615c5c256ddb906df9827b7d0962d4b5601f9`.

The quotient's saturated orbit pairs are precisely the four edges between halves(1,3) and(2,4). Thus at every nontrivial character the block equation is LX+XR=0. With X=[[p,q],[r,s]], its(1,1) entry is `(a1+a2)p+c*r+q*conj(d)=0`. I found an erroneous conjugation of r in the first draft; the author corrected and repinned it. The correction does not change divisibility but is required for the displayed matrix equation to be exact.

At parity character, det X is odd: p,s are signs and q,r are even. At the order-four character, p,s are Gaussian units while q,r, being sums of four units, are divisible by1+i. Thus det X is a unit modulo1+i and nonzero. Similarity L=-XRX^-1 supplies trace and determinant equalities at both characters.

At parity the four internal values are±2. Their sum zero forces two of each sign. The products of the two diagonals in each half agree, so equality of determinants gives c²=d². Hence the two degree-two cross sets are either both parity balanced (c=d=0) or both have constant parity (c,d=±2).

Independently checked the within-orbit leave argument:16 nonreturning two-step offsets are distinct and negation-invariant in the19 nonzero residues, leaving10 and one opposite pair. There are therefore8 or10 odd offsets. Internal two-step offsets are even. A constant-parity two-set contributes no odd differences; a four-set contributes2r(4-r), so it must have r=2 odd offsets. This forces the corresponding four-set's parity character to vanish and its order-four value to be divisible by2.

If each half's internal signs are mixed, write them(a,-a) and(b,-b). Constant-parity two-sets make both four-set values q,r zero at parity by the leave argument; the(1,1) equation forces b=-a. Balanced two-sets already have c=d=0; the same equation forces b=-a, and the remaining two off-diagonal equations then force q=r=0. In both cases internal shifts1 and2 have opposite parity and both four-sets are balanced. At i, `(a1+a2)p` is±2 times a unit, while c*r and q*conj(d) are divisible by2(1+i). The first term is not, giving a contradiction.

If each half's internal signs are constant, exchange halves to put the even shifts in L. At i, its two diagonal entries are±2 while R's are zero. For balanced two-sets, both squared norms are2; determinant equality would force the product of L's diagonal entries to be zero. For constant-parity two-sets, c,d and the balanced four-set values q,r are divisible by2; the last two terms of the(1,1) equation are divisible by4 while its first is±2 times a unit. Both alternatives contradict the equation.

This exhausts all parity sign patterns and both possible c,d parity cases. Exact local Gaussian arithmetic independently checked all10 two-unit multisets,35 four-unit multisets and19600 determinant-X combinations. The paper case proof, not these local checks alone, establishes the exclusion.

The final quotient from2147 is excluded. Together with the complete quotient cover2147 and the independently accepted first/third exclusions2149/2148, this gives a paper exclusion of N80/minimum-degree9/free-Z20. It does not exclude other action orders or all N80 graphs, does not rewrite a solver status, and is not a Lean theorem.
