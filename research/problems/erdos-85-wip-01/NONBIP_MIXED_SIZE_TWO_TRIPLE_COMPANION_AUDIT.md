# Size-two triple companions: scalar route cut

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: exact occupancy identities and a q-generic C-shore construction.
The companion scalar constraints, even together with the C-shore diagonal
Gram equation and commutation, do not give a contradiction. No ambient
graph, exterior adjacency, or terminal is asserted.

## Exact occupancy

Use the notation of `NONBIP_MIXED_SIZE_TWO_RAINBOW_CENTER_SELF_INDEX.md`:
`n=q-2`, the defect triangle `Q={c_0,c_1,c_2}`, and
`R_i=N_L(c_i)`, each of size `n` in the `2n+1`-set `C\Q`. Put

```text
Delta = delta_01 + delta_02 + delta_12,
Gamma = gamma_01 + gamma_02 + gamma_12,
t = |R_0 intersect R_1 intersect R_2|.
```

Let `N_j` count labels in `C\Q` belonging to exactly `j` companion sets.
The pair intersection law gives `sum p_ij=3n-Delta-Gamma`. Counting
memberships and pairs of memberships, followed by inclusion-exclusion,
gives exactly

```text
N_0 = 2n+1-Delta-Gamma-t,
N_1 = 2Delta+2Gamma+3t-3n,
N_2 = 3n-Delta-Gamma-3t,
N_3 = t.                                                    (1)
```

All four quantities are nonnegative. In particular,

```text
Delta+Gamma+t <= 2n+1,
2Delta+2Gamma+3t >= 3n,
Delta+Gamma+3t <= 3n.                                       (2)
```

These constraints retain the triple overlap that pairwise matching
differences discard. The following construction shows that the entire
scalar system still has room, including its realization by actual
companion neighborhoods in a commuting C-shore graph system.

## A C-shore construction for every even q >= 8

Take `C=Z/(2q)` and use Cayley graphs with the following difference sets:

```text
H: {1,-1},
K: {2,-2},
D: (all odd residues except 1,-1) union {q},
L: (all nonzero residues) \ (D union K).                    (3)
```

Here the same letter denotes a graph, its adjacency matrix, or its
difference set when unambiguous. The sets are inverse-closed and exclude
zero. Since `q` is even, the antipodal difference `q` is even and distinct
from `0,2,-2`. Thus the degrees are respectively

```text
2, 2, q-1, q-2,
```

and `L+D+K=J-I`. All matrices commute, as convolution matrices on the
abelian cyclic group. The cycle `H` has length `2q>=16`, so

```text
H^2=2I+K.                                                 (4)
```

The defect graph `D` is connected: its difference set contains `3,5`,
which generate the cyclic group together (their integer gcd is one).
It is nonbipartite, since

```text
Q=(0,q,3)
```

is a triangle: its differences are `q`, `3`, and `q-3`, all in `D`.
Its H-neighborhoods

```text
W_0={-1,1}, W_1={q-1,q+1}, W_2={2,4}
```

are pairwise disjoint for `q>=8`.

There is also an actual cross-incidence block at this interface. Let
`F=E(L)` and let `B` be the vertex-edge incidence matrix of `L`.
Then `|F|=q(q-2)`, the row and column degrees are `n` and `2`, and
distinct columns are distinct selectors. Simplicity gives

```text
BB^T=nI+L,
H^2+BB^T=(q-1)I+J-D.                                    (5)
```

Thus this is stronger than an arbitrary Venn ledger: it realizes the
entire C-shore diagonal Gram equation, its zero/one common-neighbor
partition, and the required commutation of the C-shore relations.

## The triple ledger in this construction

The companion neighborhoods of `Q` are explicit. With residues understood
modulo `2q`,

```text
R_0 = (even residues \ {0,2,-2,q}) union {1,-1},
R_1 = (even residues \ {q,q-2,q+2,0}) union {q-1,q+1},
R_2 = (odd residues \ {3,1,5,q+3}) union {2,4}.            (6)
```

Their intersections have sizes `p_01=n-4`, `p_02=2`, `p_12=4`, and
their triple intersection is exactly `{4}`. For example, the first two
sets share the even residues outside a six-set and no odd residue;
`R_0 intersect R_2={4,-1}` and
`R_1 intersect R_2={2,4,q-1,q+1}`.

Compute `gamma_ij=|R_i intersect N_K(c_j)|` and
`delta_ij=|R_i intersect N_D(c_j)|`. The exact ledger is

| Pair | delta | p | gamma |
| --- | ---: | ---: | ---: |
| 01 | 2 | n-4 | 2 |
| 02 | n-3 | 2 | 1 |
| 12 | n-4 | 4 | 0 |

In every row `delta+p+gamma=n`. Consequently

```text
Delta=2n-5, Gamma=3, t=1,
(N_0,N_1,N_2,N_3)=(2,n-1,n-1,1).                        (7)
```

All scalar inequalities (2) hold. The three cross-block L-edge counts
`e_L(W_i,W_j)` are respectively `2,1,0`, so `e_L(W)=Gamma=3`.
With `X=C\W`, degree counting therefore gives

```text
|E(L[X])|=n(n-4)+3,                                     (8)
```

the same count required of rainbow centers by the ambient argument.
One can define the formal holes as the edge stars of `W_i` in `L`;
their sizes are `2n`, their pair intersections are the three gamma values,
and their triple intersection is empty. These are edge-star sets, not
neighborhood holes of a constructed exterior graph.

## The defect intertwiner has a separate disconnected lift

There is also a uniform zero-one symmetric solution of the defect
intertwiner alone. Translation by any `d in D` permutes the selector edges.
Let `P_d` denote its permutation matrix on `C` and `Ptilde_d` its permutation
matrix on `E(L)`. Equivariance of incidence gives

```text
B Ptilde_d = P_d B.
```

Set `Dtilde_F=sum_{d in D} Ptilde_d`. The translation action on `E(L)`
is free: a nonzero translation fixing a two-set must exchange its points,
so the translation would be `q` and the edge would be antipodal. But
antipodal pairs are excluded from `L`. Thus the sum is zero-one with zero
diagonal. Inverse closure gives symmetry, and its degree is `q-1`.
Summing the equivariance identities proves

```text
B Dtilde_F = D B.                                         (9)
```

This lift has exactly `n/2` connected components of order `2q`, one for
each unsigned L-difference. Each component is a copy of `D`, since the
translation action is free and the allowed shifts generate `C`.
In particular the lift is **not** the required connected defect component
on `F`, and is not claimed to be compatible with any `H_F`. It cuts only
an obstruction based on the defect intertwiner, its symmetry, integrality,
and degree without that connectedness or the joint Gram relation.

## Verification and the exact remaining gap

`check_size_two_triple_companion.py` builds adjacency lists and the actual
incidence rows of `B`, checks (4)--(5) entrywise, checks connectivity and
the triangle, and independently computes the companion ledger, cross-block
counts, and (8). It also constructs the translation lift, checks every
column of (9), and verifies the sizes of all its components. The default
checks are `q=8,10,12,16,32,64`; these are
regressions for the uniform construction (3), not an enumeration of
ambient candidates and not a Lean proof.

Nothing here supplies `H_F` or a connected `D_F` compatible with it. In
particular it does not check the simultaneous system

```text
H B + B H_F = J,
D B = B D_F,
H_F^2 + B^T B = (q-1)I + J - D_F.                       (10)
```

The definition of formal holes cannot substitute for (10). Nor does (8)
produce rainbow triples, their proper edge colorings, or the simultaneous
perfect matchings with prescribed companion pairs. Those are additional
exterior compatibility conditions.

Disposition: cut a terminal using only triple-companion occupancies,
C-shore commutation, the diagonal Gram partition, or the six-label edge
counts. This construction satisfies them at every binary `q>=8`.
Continue at (10) and its simultaneous matching/owner-label consequences;
the A-REG-NONBIP node remains open.
