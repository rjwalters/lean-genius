# A residue criterion forces a weight-three exterior defect component

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-3,3]`.

Status: mathematical exclusion of a connected full exterior completion
of the particular q=16 triangle decomposition in
`NONBIP_MIXED_WEIGHT_THREE_TRIANGLE_FREE_GRAM_CUT.md`. No symmetry is
assumed for the exterior adjacency. This is not an exclusion of other
triangle decompositions, all triangle-free carriers, or the full branch.
The argument is a proof audit with exact finite input checks, not a Lean
formalization.

## Uniform conditional criterion

Let q>4 with q congruent to 1 modulo 3, let |C|=3q and
|F|=q(q-3), and put n=q-3. Suppose:

- B is a binary C-by-F matrix with row sum n and column sum 3;
- H is a symmetric matrix on C with every row sum 3;
- Z is a set of q labels in F whose B-columns partition C,
  so B 1_Z=1_C;
- a point-charge vector w over Z/3 satisfies
  w^T B=1_F^T-1_Z^T and w^T(J-HB)=0;
- T is a symmetric binary matrix with HB+BT=J;
- a simple graph D_F satisfies
  B^T B+T^2=(q-1)I+J-D_F.

Then Z is a closed K_q in D_F. In particular D_F cannot be connected.
These are conditional hypotheses, not assertions about all weight-three
carriers. No carrier automorphism is required of T.

Indeed, column sums of the cross equation give 9+3 deg_T(e)=3q,
so T has row and column sum n. Applying w^T to the same equation yields
(n-k_e)=0 modulo 3, where k_e=(T 1_Z)_e. Since n is congruent to 1,
every nonnegative integer k_e is at least 1. Symmetry gives
sum k_e=|Z|n=|F|, hence all k_e=1. Multiplying the full exterior Gram
identity by 1_Z now gives

```text
B^T B 1_Z+T^2 1_Z=(3+n)1_F=q 1_F,
D_F 1_Z=(q-1)1_Z.
```

Simplicity makes the induced graph on Z complete, and nonnegativity
forbids an edge from Z to its complement. Since |F|=q(q-3)>q,
connectedness fails. This proof does not need the C Gram identity or a
zero diagonal for T beyond the displayed assumptions.

The concrete example below verifies the charge hypotheses. However,
the companion Gram audit now gives an earlier parity obstruction to
its symmetric integral cross equation, uniformly for all three-odd-
reflection H with that interval defect graph. The example is therefore
already excluded without the exterior Gram. The independent value here
is the explicit conditional residue criterion; deriving its charge
hypotheses for other carriers remains open.

## The exact carrier being excluded

Let `C=Z/48`, `q=16`, `n=q-3=13`. Internal H-neighbors of x are
`1-x,3-x,7-x`. The exterior labels F are the 208 triples from the banked
decomposition. Separate them into:

- 192 translates of `{0,a,c}` for `(a,b,c)` equal to
  `(7,8,15),(5,9,14),(3,10,13),(1,11,12)`;
- the 16 equilateral triples `Z={{x,x+16,x+32}:0<=x<16}`.

Write B for the vertex/triple incidence matrix. The triples in Z partition
C, so `B 1_Z=1_C`. Every B-row has degree13 and every B-column has size3.
The already verified C Gram equation is retained.

Suppose T is a symmetric zero-one matrix on F, with zero diagonal, which
satisfies `HB+BT=J`. A connected full exterior completion would additionally
have a simple connected defect graph D_F satisfying

```text
B^TB+T^2=15 I_F+J_F-D_F.                               (1)
```

We prove these hypotheses inconsistent. T is not assumed to preserve any
translation, reflection, or other automorphism of the carrier.

## Modulo three forces a neighbor in Z

Column sums of the cross equation give

```text
9+3 deg_T(e)=48,       deg_T(e)=13.                     (2)
```

The H-neighborhoods of the three points in each selector e are disjoint
(verified by the C Gram data). The cross equation therefore says that
the 13 triple labels in `N_T(e)` partition `C\H(e)`.

Let the residue weight of a point be its label modulo3. Wraparound modulo48
does not change that residue. Every generic triple has weight1:

```text
a+c = 22,19,16,13, all congruent to1 modulo3.
```

Every equilateral triple has weight0. The total weight of C is0, and the
three H-neighbors of any point x have total weight
`11-3x=2 modulo3`. Hence H(e), consisting of three such disjoint triples,
also has total weight0. The covered set `C\H(e)` has weight0.

If `k_e=|N_T(e) intersect Z|`, the 13 covered triples therefore give

```text
13-k_e = 0 modulo3,       k_e = 1 modulo3.              (3)
```

In particular `k_e>=1` for every exterior label. This is an integrality
argument; it would not follow for arbitrary fractional T.

## Symmetry makes the lower bound exact everywhere

By symmetry and regularity,

```text
sum_(e in F) k_e = sum_(z in Z) deg_T(z)
                = 16*13 = 208 = |F|.
```

There are 208 nonnegative integer k_e, each at least1. They all equal1:

```text
T 1_Z=1_F.                                             (4)
```

Thus Z meets each exterior neighborhood exactly once. Together with
`B 1_Z=1_C`, it meets every neighborhood of the entire candidate ambient
graph exactly once.

## The full Gram equation forces Z to be defect-closed

Multiply (1) by `1_Z`. The left side is

```text
B^T B 1_Z+T^2 1_Z = B^T1_C+T1_F
                   =3*1_F+13*1_F=16*1_F.
```

The right side is `15*1_Z+16*1_F-D_F1_Z`. Therefore

```text
D_F1_Z=15*1_Z.                                         (5)
```

Every vertex outside Z has zero defect neighbors in Z. Each vertex of Z
has all 15 other Z-vertices as defect neighbors. So Z is a K16 connected
component of D_F. Since `0<|Z|=16<208=|F|`, D_F is not connected,
contradicting the stipulated exterior component of weight13.

Equivalently, for the full ambient adjacency A we have `A1_Z=1`, and
`A^2 1_Z=16*1`; the square-order Gram identity gives the same defect
closure. No assertion about other defect-component partitions is needed.

## Verification and scope

`check_weight_three_residue_obstruction.py` independently reconstructs
the 208 triples, verifies the C Gram off-diagonal entries, all block
weights, the partition Z, all 208 covered-set residue sums, and the
arithmetic bounds used in (2)--(4). It does not use a SAT/MILP verdict or
assume an unverified exterior witness. The contradiction is the proof
above, not a finite search result.

```sh
python3 research/problems/erdos-85-wip-01/check_weight_three_residue_obstruction.py
```

The companion parity proof already excludes the symmetric cross equation
for this model, independently of the block decomposition. The argument
here supplies a different conditional obstruction. The residue-one property of every
generic block is a property of this selected triangle decomposition;
it has not been derived for arbitrary B with the same H and D_C.
Different decompositions could mix residues and evade (3), though they
remain subject to the companion parity obstruction for this fixed H,D_C. The
weight-three triangle/C5 completeness reduction and A-REG-NONBIP remain
open until those other carriers are treated.
