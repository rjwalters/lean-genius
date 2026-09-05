# Size-two triangle carrier: diagonal Gram packing

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: exact q-generic packing consequence combining both block identities;
no terminal claimed.

## Setup

Use the size-two triangle carrier from
`NONBIP_MIXED_EVEN_EXTERIOR_CARRIER_AUDIT.md` and the notation of
`NONBIP_MIXED_SIZE_TWO_CARRIER_OWNER_DICHOTOMY.md`.  Thus the exterior
component `F` has weight `n=q-2`, the defect triangle in `C` produces
pairwise disjoint sets

```text
S_i=N_B(c_i),             |S_i|=n,
```

and `D_F[S_i]` is empty.  The exterior diagonal Gram block is

```text
H_F^2 + B^T B = (q-1)I + J - D_F.                       (1)
```

## Pairwise-disjoint ambient neighborhoods

Take distinct `f,g in S_i`.  They share `c_i` as a `B`-neighbor.  The
ambient C4 cap prevents a second common `B`-neighbor, so

```text
(B^T B)_(f,g)=1.
```

The first carrier block identity already gives `D_F(f,g)=0`.  Evaluating
(1) off the diagonal therefore yields

```text
(H_F^2)_(f,g)=0.                                        (2)
```

Equivalently, distinct points of `S_i` have disjoint `H_F`-neighborhoods.
Each point has internal ambient degree `n`, so the family

```text
{N_H_F(f) : f in S_i}
```

consists of `n` pairwise-disjoint `n`-sets.  It covers exactly `n^2` of the
`qn` exterior labels.  Define its hole set

```text
U_i = F \\ union_{f in S_i} N_H_F(f).
```

Then

```text
|U_i| = qn-n^2 = n(q-n)=2n.                             (3)
```

The pointwise form, which is stronger than the cardinality alone, is

```text
deg_H_F(v,S_i) <= 1                    for every v in F. (4)
```

Thus every carrier fiber is a distance-two packing in `H_F` whose
neighborhoods miss only `2n` labels.

## Exact placement of carrier points in the holes

Retain the owner-dichotomy parameters

```text
a_i  = #{f in S_i : H_C(c_i,r_f)},
b_ij = #{f in S_j : H_C(c_i,r_f)},
h_ij = 1_{H_C(c_i,c_j)}.
```

The self-part equation says exactly that the `a_i` isolated points of
`H_F[S_i]` are the points of `S_i` lying in `U_i`:

```text
|U_i intersect S_i|=a_i.                                (5)
```

For `j != i`, the cross-part equation

```text
h_ij + 1_{H_C(c_i,r_f)} + deg_H_F(f,S_i)=1,
        f in S_j,
```

gives

```text
|U_i intersect S_j| = if h_ij=1 then n else b_ij.       (6)
```

In particular, when `c_i c_j` is an ambient edge, all of `S_j` lies in
`U_i` and all of `S_i` lies in `U_j`.  If `S=S_0 union S_1 union S_2`,
(3), (5), and (6) also determine the number of holes outside the carrier:

```text
|U_i \\ S|
  = 2n - a_i
      - sum_{j != i} (if h_ij=1 then n else b_ij).       (7)
```

The right side is nonnegative.  This couples the small integer owner ledger
to an actual family of size-`2n` subsets of the exterior component; the
parameters are no longer merely scalar edge counts.

## Pairwise hole intersections

The diagonal Gram identity also determines the pairwise intersections of
the holes.  Let

```text
R_i = {r_f : f in S_i},
delta_ji = #{f in S_i : D_C(c_j,r_f)},
p_ij = |R_i intersect R_j|.
```

Companion injectivity gives `|R_i|=n`.  For `i != j`, the defect intertwiner
calculation from the first carrier audit refines pointwise, for `f in S_i`,
to

```text
deg_D_F(f,S_j)=1+1_{D_C(c_j,r_f)}.
```

Summing over the single shore `S_i` counts each undirected cross edge once
(one endpoint is prescribed in `S_i`), so there is no factor two and

```text
e_D_F(S_i,S_j)=n+delta_ji.                               (8)
```

Symmetry of the left side also proves `delta_ji=delta_ij`.

Write `T_i=F\\U_i`, the `n^2` labels covered by the disjoint neighborhood
family of `S_i`.  Because each label has at most one `H_F`-neighbor in each
fiber, common covered labels are counted without multiplicity:

```text
|T_i intersect T_j|
  = sum_{f in S_i, g in S_j} (H_F^2)_(f,g).              (9)
```

For a cross-fiber pair `(f,g)`, its two `B`-neighbor sets can meet only when
`r_f=r_g`: neither companion can be the other triangle vertex, since the
`S_i` are disjoint.  Hence the sum of `(B^T B)_(f,g)` over the cross block is
exactly `p_ij`.  Summing the off-diagonal entries of (1) gives

```text
|T_i intersect T_j|=n^2-(n+delta_ji)-p_ij.              (10)
```

Finally inclusion-exclusion with `|F|=qn`, `|T_i|=|T_j|=n^2`, and `q-n=2`
yields the exact hole-intersection law

```text
|U_i intersect U_j|=n-delta_ji-p_ij.                    (11)
```

In particular

```text
delta_ji+p_ij <= n.                                     (12)
```

Thus the pairwise hole intersections are not free: they are paid for by the
defect incidence of one companion system against the opposite triangle
vertex and by overlap of the two companion systems.

## Disposition

The diagonal Gram identity upgrades the carrier to three near-partitions of
`F` by disjoint ambient neighborhoods, with exact holes (3)--(12).  This is a
genuine spatial constraint and is uniform in binary `q>=8`.

It does not alone contradict `[q-2,2]`: the hole cardinalities, pairwise
intersection law, and parity conditions `a_i = n (mod 2)` still admit many
integer ledgers.  A terminal must control the triple intersection of the
`U_i`, or constrain `delta_ji` and `p_ij` by the remaining owner laws.  No
finite-order census is promoted by this audit.
