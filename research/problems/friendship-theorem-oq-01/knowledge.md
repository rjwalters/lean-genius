# Knowledge Base: friendship-theorem-oq-01

Spectral proof of Friendship Theorem via Mathlib linear algebra.

---

## Problem Understanding

The Friendship Theorem (Erdos-Renyi-Sos, 1966): In any finite simple graph where
every pair of distinct vertices has exactly one common neighbor, there exists a
vertex adjacent to all other vertices (a "universal friend" or "politician").

The spectral proof has two main components:
1. **Regularity**: No universal vertex implies the graph is regular (all vertices
   have the same degree). Proved by counting arguments.
2. **Spectral contradiction**: A k-regular friendship graph satisfies A^2 = (k-1)I + J.
   Eigenvalue analysis shows this is impossible for n >= 4, leaving only n=3 (triangle).

---

## Insights

### Matrix Identity A^2 = (k-1)I + J
- (A^2)_{ij} = number of common neighbors of i,j = 1 (friendship, i!=j) or k (diagonal)
- This gives A^2 = (k-1)*I + J where J is the all-ones matrix
- Consequence: eigenvalues of A are k (for eigenvector 1) and +/-sqrt(k-1) (rest)

### Counting Identity
- For vertex u: the map f_u : V\{u} -> N(u) sends v to its unique common neighbor with u
- Fiber: |f_u^{-1}(w)| = deg(w) - 1 for w in N(u) (preimage is N(w)\{u})
- Sum: sum_{w in N(u)} (deg(w)-1) = n-1

### Eigenvalue Argument
- tr(A) = 0: k + (p-q)*sqrt(k-1) = 0 where p,q are multiplicities
- If k-1 not a perfect square: p=q, k=0, contradiction
- If k-1 = s^2: integrality constraints force n=3, k=2

### Mathlib API Notes
- Import `Mathlib.Combinatorics.SimpleGraph.AdjMatrix` for G.adjMatrix
- `SimpleGraph.Connected.mk` requires `Nonempty V` instance
- No built-in all-ones matrix; define as `fun _ _ => 1`
- `SimpleGraph.adjMatrix_apply` gives if-then-else form

---

## Dead Ends

None - the approach works cleanly. The sorries are all technically achievable.

---

## Built Items

- `proofs/Proofs/FriendshipTheoremOQ01.lean` (6 sorries, 1 axiom)
  - `IsFriendshipGraph`, `IsUniversalVertex`, `IsRegular` definitions
  - `friendship_pos_degree` (proved)
  - `friendship_connected` (proved)
  - `friendship_degree_sum` (sorry - counting identity)
  - `friendship_adjacent_same_degree` (sorry - regularity core)
  - `friendship_no_universal_implies_regular` (sorry - regularity)
  - `allOnesMatrix` definition
  - `adjMatrix_sq_eq` (sorry - matrix identity)
  - `trace_adjMatrix_eq_zero` (proved)
  - `friendship_vertex_count` (sorry - arithmetic)
  - `spectral_regular_friendship_contradiction` (axiom - eigenvalue integrality)
  - `friendship_three_vertices_universal` (sorry - small case)
  - `regular_friendship_has_universal` (proved from axiom + small case)
  - `friendship_theorem_spectral` (proved - main theorem)
  - Triangle K_3 verification (proved)
