# NONBIP-MIXED even exterior-carrier audit

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED`, the even-weight
two-component siblings `[6,2]` and `[4,4]` at `q=8`.

Status: exact norm/Bockstein identity; scalar mod-4 route cut; a surviving
q-generic support consequence for a size-two nonbipartite component.

## Setup

Use the block notation of
`NONBIP_MIXED_EXTERIOR_SELF_INDEX_TRANSPORT_AUDIT.md`.  Thus `C,F` have
orders `qm,qn`, respectively,

```text
B = A_G[C,F],
```

and `B` has row sum `n` and column sum `m`.  Let `Q` be the vertex set of an
induced odd cycle of length `ell` in `D_C`, put `x=1_Q` over the integers,
and set

```text
y = B^T x.
```

Every coordinate `y_f` is the number of `G`-neighbors of `f` on the cycle,
so `0 <= y_f <= m` and

```text
sum_f y_f = n ell.                                      (1)
```

## The norm is exactly an owner-edge census

The cross-incidence Gram block is

```text
B B^T = n I + O_F[C,C],                                 (2)
```

where `O_F` is the owner graph of component `F`.  Therefore

```text
||y||^2 = x^T B B^T x
        = n ell + 2 e_F(Q),                              (3)
```

with `e_F(Q)` the number of `F`-owned edges induced by the cycle vertices.
Equivalently, the first integral Bockstein after removing the forced total
is not a new invariant:

```text
(||y||^2 - sum_f y_f) / 2
  = sum_f choose(y_f,2)
  = e_F(Q).                                               (4)
```

Thus for even `n`, reducing the norm modulo four gives only the parity of an
existing owner-edge count:

```text
||y||^2 = n ell + 2 e_F(Q)                 (mod 4).       (5)
```

There is no parity contribution from the odd cycle beyond `n ell`.

The diagonal component equation supplies the complementary tautology.  If
`H_C=A_G[C,C]`, then

```text
H_C^2 + B B^T = (q-1)I + J - D_C,
```

and, because `x^T D_C x=2 ell`,

```text
||H_C x||^2 = ell^2 + (m-3)ell - 2e_F(Q).                (6)
```

Subtracting `sum H_Cx=m ell` and dividing by two says only

```text
sum_c choose((H_Cx)_c,2)
  = ell(ell-3)/2 - e_F(Q),                               (7)
```

the number of complementary chords owned by `C`.  Equations (4) and (7)
partition the `ell(ell-3)/2` non-cycle pairs of an induced cycle by their
unique owner color; they create no residue.

## Faithful `q=4`, `[2,2]` calibration

Direct enumeration of `sixteenRegular` gives eight induced 5-cycles in each
defect component.  For every one of the sixteen oriented component/cycle
choices, the exterior carrier has sorted coordinate profile

```text
(1,1,1,1,1,1,2,2).
```

Hence `sum y=10`, `||y||^2=14=6 (mod 8)`, and

```text
(14-10)/2 = 2 = e_F(Q).
```

The known exception therefore satisfies the norm identity sharply; neither
mod four nor mod eight produces a contradiction.

## Arithmetic flexibility at the order-64 even strata

Even before imposing the transported boundary equation, the forced total,
coordinate bound, and norm Bockstein permit both owner-edge parities.
For `ell=5`, explicit sorted carrier profiles are:

```text
[6,2], C weight 6, exterior n=2, |F|=16, y_f<=6:
  even e_F:  0^6, 1^10
  odd  e_F:  0^7, 1^8, 2

[6,2], C weight 2, exterior n=6, |F|=48, y_f<=2:
  even e_F:  0^18, 1^30
  odd  e_F:  0^19, 1^28, 2

[4,4], exterior n=4, |F|=32, y_f<=4:
  even e_F:  0^12, 1^20
  odd  e_F:  0^13, 1^18, 2.
```

In every row the two profiles have the same forced total `n ell`; inserting
one coordinate of value two changes the Bockstein parity.  These are scalar
profiles, not block-matrix models, so they do not refute a consumer of the
full simultaneous transport equations.  They do prove that no conclusion
about `e_F(Q) mod 2` follows from carrier weight, coordinate bounds, and
`||B^T x||^2` alone.

## A vector-support consequence survives the scalar cut

Let `o(y) = #{f : y_f is odd}`.  For every nonnegative integer `t`,

```text
t <= (t mod 2) + 2 choose(t,2).
```

Summing over the coordinates of `y`, then using (1), (4), and the fact that
all `F`-owned pairs inside an induced `D_C`-cycle are non-cycle pairs, gives

```text
n ell <= o(y) + 2 e_F(Q)
      <= o(y) + ell(ell-3),
```

and hence

```text
o(y) >= ell (n-ell+3).                                  (8)
```

Thus `y mod 2` is forced nonzero whenever `ell<n+3`.  Unlike (5), this is
vector information: it measures how many exterior coordinates survive,
not a residue of their norm.

There is a useful q-generic specialization to a nonbipartite component of
weight two.  Such a component has `2q` vertices and its defect graph is
`(q-1)`-regular.  For `q>=8`, `q-1 > 2(2q)/5`.  The triangle-free
minimum-degree theorem of Andrasfai--Erdos--Sos therefore implies that a
nonbipartite `D_C` contains a triangle.  Every exterior vertex has at most
one `G`-neighbor on this defect triangle: two such neighbors would give a
common neighbor to a pair joined in `D_C`, contradicting the owner/defect
partition.  Consequently every coordinate of `y=B^T x` is zero or one and,
for every exterior component of weight `n`,

```text
|supp(y)| = sum_f y_f = 3n.                             (9)
```

This support has an exact three-fiber localization.  Label the defect
triangle `Q={c_0,c_1,c_2}` and put

```text
S_i = N_B(c_i) subset F.
```

The three sets are pairwise disjoint (a point in an intersection would be a
common `G`-neighbor of a defect pair), each has cardinality `n`, and their
union is `supp(y)`.  Because `C` has weight two, every `f in S_i` has
exactly one other `B`-neighbor `r_f != c_i`.  The same common-neighbor
observation gives `r_f notin N_D(c_i)`.  Reading the `(c_i,f)` entry of
`D_C B=B D_F` therefore gives

```text
deg_D_F(f,S_i) = 0.                                    (10)
```

For `j != i`, the triangle edge says `c_i in N_D(c_j)`.  The same entrywise
identity, now at `(c_j,f)`, counts the two `B`-neighbors of `f` which lie in
`N_D(c_j)` and yields

```text
1 <= deg_D_F(f,S_j) <= 2.                              (11)
```

Thus the carrier does not merely have forced size: `D_F` induces on it a
tripartite graph with independent parts of size `n`, and every vertex has
between one and two neighbors in each of the other two parts.  Equations
(10)--(11) are the first spatial consumer of the exact intertwiner.

For `[6,2]` at order 64, orienting from the weight-two component therefore
forces a binary exterior carrier of support `18`.  More generally this is
uniform for binary `q>=8`, with support `3(q-2)` in `[q-2,2]`; it is not an
order-64 enumeration.

Literature input: B. Andrasfai, P. Erdos, and V. T. Sos, *On the connection
between chromatic number, maximal clique and minimal degree of a graph*,
Discrete Mathematics 8 (1974), 205--218, Theorem 1.1 / Lemma 1.2 and Remark
1.6.  The invoked `r=3` consequence is that a triangle-free graph on `N`
vertices with minimum degree strictly greater than `2N/5` is bipartite.
This consequence is not left as an external axiom: the pinned Mathlib theorem
`SimpleGraph.colorable_of_cliqueFree_lt_minDegree` yields the cold-built,
standard-axiom Lean specialization

```text
not_cliqueFree_three_of_card_two_mul_regular_not_bipartite
```

in `Erdos85BinarySquareSizeTwoDefectTriangle.lean`.

## Disposition

The proposed mod-4/8 norm route reduces exactly to owner-edge parity and is
cut at that interface.  This agrees with the earlier instruction to stop if
the Bockstein contains no information beyond the owner census.

The support bound (8), and especially the binary carrier (9), are the
surviving first vector layer.  They are not yet a contradiction: a consumer
must use where that support lies.  The even-weight strata therefore require
a genuinely vector-valued second layer: use
the exact equation `D_F y=B^T D_Cx` (or its integral lift) together with
`H_Fy+B^TH_Cx=1`, rather than another scalar moment of `y`.  In particular,
the odd-total shortcut available for `[5,3]` has no even-weight analogue in
the first norm or first Bockstein.
