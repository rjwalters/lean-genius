# Problem: Complete the Friendship Theorem — the Non-Regular Case

**Slug**: friendship-theorem-oq-01-oq-02
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $G$ be a finite simple graph in which every two distinct vertices have
**exactly one** common neighbour (the friendship condition). Then $G$ has a
**universal vertex** (a vertex adjacent to all others), and hence $G$ is a
windmill graph — a collection of triangles sharing one common vertex.

The parent proof `FriendshipTheoremOQ01` already establishes the **regular
case**: every $k$-regular friendship graph satisfies $k = 2$, so it is the
triangle $K_3$. The remaining piece is:

$$
G \text{ friendship graph} \;\Longrightarrow\; G \text{ is regular} \ \text{OR}\ G \text{ has a universal vertex}.
$$

Combined with the parent, this yields the full Erdős–Rényi–Sós theorem.

### Plain Language

The classical proof of the Friendship Theorem splits into two parts. The hard
spectral part — "if the graph is regular then $k=2$" — is already formalized in
`FriendshipTheoremOQ01.lean`. This problem asks for the *combinatorial* part:
show that a friendship graph is either regular or contains a vertex joined to
everyone. The standard argument counts common neighbours to prove that any two
**non-adjacent** vertices have the same degree; a short case analysis then forces
either global regularity or the existence of a universal vertex. Assembling this
with the parent gives a complete, axiom-free formal proof of the whole theorem.

### Why This Matters

The Friendship Theorem (Erdős–Rényi–Sós, 1966) is a landmark combinatorial
result and a standard test case for formalization because its usual proof mixes
spectral graph theory with elementary counting. The spectral half is already in
the gallery with 0 axioms and 0 sorries; completing the combinatorial half
closes the gap and delivers the full theorem, not just its regular case.

## Known Results

### What's Already Proven

- Parent `friendship-theorem-oq-01` (`Proofs/FriendshipTheoremOQ01.lean`):
  every $k$-regular friendship graph has $k = 2$ and is $K_3$, proved via
  characteristic-polynomial identities, the Weinstein–Aronszajn formula, and a
  prime-divisibility argument — **without** the spectral theorem for symmetric
  matrices (0 axioms, 0 sorries, 84 theorems).
- Base entry `friendship-theorem`: statement and definitions of the friendship
  condition and the windmill/universal-vertex structure.

### What's Still Open

- The **non-regularity step**: two non-adjacent vertices in a friendship graph
  have equal degree.
- The case analysis assembling "regular or universal vertex".
- The **combination**: chaining the non-regular reduction into the parent's
  regular result to obtain the full theorem.

### Our Goal

Formalize the combinatorial non-regularity argument in Lean 4 and combine it
with `FriendshipTheoremOQ01` to state and prove the full Friendship Theorem
(existence of a universal vertex / windmill structure), keeping the proof
axiom-free.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| friendship-theorem-oq-01 | Regular case $k=2$ (the spectral half) | char. polynomial, Weinstein–Aronszajn, UFD in ℤ[X] |
| friendship-theorem | Base definitions of the friendship condition | SimpleGraph, common neighbours |

## Initial Thoughts

### Potential Approaches

1. **Equal-degree lemma via double counting**: For non-adjacent $u, v$, count
   paths of length 2 to show $\deg u = \deg v$; propagate equality across the
   graph.
   - Risk: The "counting common friends" bijection needs care in Mathlib's
     `SimpleGraph` API (neighbor finsets, `Finset.card` bijections).
2. **Contrapositive / universal vertex extraction**: Assume no universal vertex,
   derive regularity, then invoke the parent to force $k=2$ and a contradiction
   with non-triviality.
   - Risk: Bookkeeping the degree-equality graph (adjacency of "same degree")
     and its connectivity.

### Key Difficulties

- Translating the classical "two non-adjacent vertices have the same degree"
  counting argument into Mathlib's `SimpleGraph` neighbor-finset API.
- Cleanly interfacing with the parent's regular-case theorem so the final
  statement is the full theorem, not a restatement.
