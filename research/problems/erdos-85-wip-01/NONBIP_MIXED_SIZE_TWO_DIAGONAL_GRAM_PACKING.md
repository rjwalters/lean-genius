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

## Disposition

The diagonal Gram identity upgrades the carrier to three near-partitions of
`F` by disjoint ambient neighborhoods, with exact holes (3)--(7).  This is a
genuine spatial constraint and is uniform in binary `q>=8`.

It does not alone contradict `[q-2,2]`: the hole cardinalities and the parity
conditions `a_i = n (mod 2)` admit many integer ledgers.  A terminal must
control intersections among the three hole sets `U_i`, or combine their
near-partitions with the defect cross-degrees between the `S_i`.  No finite
order census is promoted by this audit.
