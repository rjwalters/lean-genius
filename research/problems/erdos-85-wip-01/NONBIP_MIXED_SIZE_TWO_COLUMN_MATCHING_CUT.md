# Size-two circulant carrier: local column matching is feasible

Node: `A.5.3 / A-REG-NONBIP / NONBIP-MIXED / [q-2,2]`.

Status: q-generic countermodel to the **individual-column** extension
interface, for every even `q >= 12` (hence binary `q >= 16`). Prose proof;
not a Lean theorem. Symmetric exterior adjacency and the exterior diagonal
Gram equation remain unproved and are not asserted by this construction.

## The C-shore family

Use Sol2's circulant candidate on `C = Z/(2q)`, with `n=q-2`:

```
H differences = {1,-1},
K differences = {2,-2},
D differences = {odd residues other than 1,-1} union {q},
L differences = all nonzero residues outside D and K.
```

These simple undirected graphs have degrees `2,2,q-1,q-2`, respectively.
The difference sets partition the nonzero residues among `D,K,L`;
`H^2=2I+K`. Let `F=E(L)` and let `B` be the unsigned vertex-edge
incidence matrix of `L`. Then `BB^T=nI+L`, and therefore

```
H^2 + BB^T = (q-1)I + J - D.
```

All these C-shore adjacency matrices commute because their difference
sets define circulants. The graph D is connected: its differences include
3 and 5, which generate the cyclic group together. It is nonbipartite:
`{0,q,3}` is a triangle, with differences `q,3,q-3`.

The only L-edges between the two parity classes of C are the H-cycle
edges. Inside either parity class, L is the complete graph on q vertices
minus the two cycle neighbors (differences `+2,-2`) and the antipodal
neighbor (difference q). Thus each parity-induced graph is `(q-4)`-regular.

## What one exterior column must do

For an L-edge `e={a,b}`, put

```
W_e=N_H(a) union N_H(b).
```

The two H-neighborhoods are disjoint: otherwise a and b would be joined
by K, whereas e lies in L. Hence `|W_e|=4`. Column e of `HB` is exactly
the indicator of W_e.

A zero-one column indexed by F solves

```
(B T)[:,e] = (J-HB)[:,e]
```

if and only if its selected L-edges form a perfect matching of
`L[C\W_e]`. Requiring `T[e,e]=0` additionally forbids selecting e itself.
The matching then has `q-2=n` edges. This equivalence is pointwise:
each vertex outside W_e must have exactly one selected incident edge,
and every vertex in W_e must have none.

## Elementary matching lemma

A simple graph of even order N and minimum degree at least N/2 has a
perfect matching. For completeness, choose a maximum matching M. If it
leaves vertices u,v unmatched, these vertices are nonadjacent, and every
neighbor of either is matched. A matched edge has at most two incidences
to {u,v}: three incidences would allow replacing it by two edges incident
to u and v, enlarging M. Consequently

```
deg(u)+deg(v) <= 2|M| <= N-2,
```

contrary to `deg(u)+deg(v)>=N`.

## Every column is feasible for even q >= 12

We construct each matching using only same-parity L-edges.

If a,b have the same parity, W_e consists of four vertices of the opposite
parity. The surviving parity blocks have sizes q and q-4. In the first
block, also delete edge e to enforce the zero diagonal. Its minimum degree
is at least q-5. The other block has minimum degree at least q-8. Both
orders are even, and

```
q-5 >= q/2,             q-8 >= (q-4)/2       (q >= 12).
```

The matching lemma applies independently to both blocks.

If a,b have opposite parity, e is an H-cycle edge. W_e removes two
vertices of each parity. Each surviving parity block has even order q-2
and minimum degree at least q-6, with

```
q-6 >= (q-2)/2                              (q >= 12).
```

Again both blocks have perfect matchings. Neither can include e because
they use only same-parity edges (also the endpoints of e belong to W_e).

In either case the union of the two matchings is an admissible matching
M_e on `C\W_e`, avoiding e.

## A nonsymmetric solution of the complete cross block

Choose such an M_e independently for every e in F and define

```
T[f,e] = 1 if f belongs to M_e, otherwise 0.
```

Then simultaneously

```
T is zero-one,             diagonal(T)=0,
every column sum is n,     H B + B T = J.
```

This is an actual solution of all column equations, not merely a scalar
degree ledger. It is necessarily nonsymmetric: the row of every
opposite-parity edge f is zero, because no M_e uses such an edge; but its
column has n>0 entries. Opposite-parity edges exist (the H-cycle edges).

This shows why independently solving each matching demand cannot exclude
the circulant C-shore family at general binary q. It does **not** show
that a different, symmetric choice is impossible or possible. The next
load-bearing requirements are reciprocity

```
f in M_e iff e in M_f
```

and the exterior diagonal Gram equation, with the required defect graph
on F. The construction supplies no such defect graph, no ambient witness,
and no closure of A-REG. It makes no assertion about local feasibility at
q=8; the uniform inequalities above start at even q=12.

## Verification

`check_size_two_column_matching.py` constructs the actual matchings and
checks every vertex incidence of every column, the zero diagonal, and an
explicit symmetry failure. It passed at q=12,14,16,32 (120,168,224,960
columns). These finite checks verify the implementation of the construction;
the minimum-degree proof above supplies the uniform conclusion.
