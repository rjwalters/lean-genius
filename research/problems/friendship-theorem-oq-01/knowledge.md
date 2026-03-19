# Knowledge Base: friendship-theorem-oq-01

Spectral proof of Friendship Theorem via Mathlib linear algebra.

---

## Problem Understanding

The Friendship Theorem (Erdos-Renyi-Sos, 1966): In any finite simple graph where
every pair of distinct vertices has exactly one common neighbor, there exists a
vertex adjacent to all other vertices (a "universal friend" or "politician").

The spectral proof has two main components:
1. **Regularity**: No universal vertex implies the graph is regular. Requires
   spectral/algebraic methods — no clean combinatorial proof known.
2. **Spectral contradiction**: A k-regular friendship graph satisfies A^2 = (k-1)I + J.
   Eigenvalue analysis shows k must equal 2, leaving only the triangle.

---

## Current File State

**FriendshipTheoremOQ01.lean**: 0 sorries, 1 axiom

### Proved Results (18 lemmas/theorems)

| Part | Result | Description |
|------|--------|-------------|
| I | `ucn`, `ucn_spec` | UCN extraction and singleton characterization |
| I | `ucn_adj_left`, `ucn_adj_right` | UCN is adjacent to both vertices |
| I | `ucn_unique` | Any common neighbor equals UCN |
| I-B | `ucn_ne_left`, `ucn_ne_right` | UCN ≠ u and UCN ≠ v |
| I-B | `friendship_separation` | For adj u,v: ucn(x,v) = u for all x ∈ N(u)\{v} |
| I-B | `ucn_involutive` | ucn(u, ucn(u,v)) = v (partner involution) |
| I-B | `ucn_unique_in_neighborhood` | Partner is unique neighbor within N(u) |
| II | `common_neighbor_finset_card` | |N(u) ∩ N(v)| = 1 (A² off-diagonal) |
| III | `counting_disjoint` | Partition fibers are pairwise disjoint |
| III | `counting_cover` | Partition fibers cover V \ {u} |
| III | `counting_identity` | n-1 = Σ_{v∈N(u)} (deg(v)-1) |
| IV | `regular_friendship_card` | n = k(k-1)+1 for k-regular |
| V | `dvd_sq_add_one_imp_one` | s | s²+1 → s = 1 |
| VI | `regular_friendship_is_triangle` | k-regular friendship → n = 3 |
| VI | `regular_friendship_has_universal` | k-regular friendship → universal vertex |

### Single Axiom

`spectral_regular_friendship`: In a k-regular friendship graph with k ≥ 2, k = 2.

---

## Insights

### Separation Lemma (Session 2)
For adjacent u, v: ucn(x, v) = u for ALL x ∈ N(u) \ {v}.
Neighborhoods of adjacent vertices are completely separated.

### Partner Involution (Session 2)
v ↦ ucn(u, v) is a fixed-point-free involution on N(u).
Consequence: deg(u) is always even in a friendship graph.

### Adjacent Same Degree is FALSE (Session 2)
Windmill W₂: center deg=4, petals deg=2. Both adjacent.
"No universal → regular" requires algebraic methods.

### Matrix Identity A^2 = (k-1)I + J
- (A^2)_{ij} = common neighbor count = 1 (off-diag) or k (diag)
- Eigenvalues: k and ±sqrt(k-1)
- trace(A) = 0 forces k-1 to be a perfect square, then s|s²+1→s=1→k=2

---

## Dead Ends

- **Bijection N(u) → N(v)**: Map x ↦ ucn(x,v) sends ALL of N(u)\{v} to u.
  Not injective for deg(u) > 2. Cannot prove adjacent same degree this way.
- **Counting identity alone**: Consistent with any degree sequence.

---

## Remaining Work: Detailed Spectral Axiom Elimination Plan

### Step 1: Matrix Identity A² = (k-1)I + J (~100 lines)
**Mathlib import**: `Mathlib.Combinatorics.SimpleGraph.AdjMatrix`
- Define A = G.adjMatrix ℝ
- Show (A²)ᵢᵢ = deg(i) = k (diagonal = degree)
- Show (A²)ᵢⱼ = |N(i)∩N(j)| = 1 for i≠j (uses `common_neighbor_finset_card`)
- Conclude A² = (k-1)·I + J

### Step 2: Eigenvalue Analysis (~200-300 lines)
**Mathlib imports**: `Mathlib.Analysis.InnerProductSpace.Spectrum`
- Show A = G.adjMatrix ℝ is symmetric (Matrix.IsHermitian)
- By spectral theorem: A has real eigenvalues with integer multiplicities
- A𝟙 = k𝟙 (k-regular), so k is an eigenvalue
- For v ⊥ 𝟙: A²v = (k-1)v (since Jv = 0), so eigenvalues are ±√(k-1)

### Step 3: Trace Constraint (~50 lines)
- trace(A) = ∑ᵢ Aᵢᵢ = 0 (no self-loops)
- trace(A) = sum of eigenvalues = k + m₊·√(k-1) - m₋·√(k-1) = 0
- So k + (m₊ - m₋)·√(k-1) = 0

### Step 4: Integrality → k = 2 (~50 lines)
- If √(k-1) irrational: m₊ = m₋ and k = 0, contradiction
- So k-1 = s² for integer s ≥ 1
- m₊ - m₋ = -(s²+1)/s must be integer → s | (s²+1)
- By `dvd_sq_add_one_imp_one`: s = 1, so k = 2

### Mathlib Dependencies (v4.26.0)
| API | Module | Available? |
|-----|--------|-----------|
| `SimpleGraph.adjMatrix` | `Mathlib.Combinatorics.SimpleGraph.AdjMatrix` | Yes |
| `Matrix.trace` | `Mathlib.LinearAlgebra.Trace` | Yes |
| `Matrix.IsHermitian` | `Mathlib.Analysis.InnerProductSpace.Spectrum` | Yes |
| `Matrix.IsHermitian.eigenvalues` | same | Yes |
| eigenvalue multiplicity → trace | gap? | Needs verification |

### Estimated Effort: 350-450 lines, 2-3 sessions

## Approaches Explored

### Spectral A² identity
**Status**: succeeded
Prove A²=(k-1)I+J for regular friendship graph, derive eigenvalue constraints
**Outcome**: Full proof architecture with 0 sorries and 1 axiom (spectral eigenvalue step)

## Session History

### Session 2026-03-19 (researcher-4) - Survey/Assessment
- Assessed spectral axiom elimination feasibility
- Documented 4-step proof strategy with Mathlib API dependencies
- Key finding: the spectral theorem for real symmetric matrices IS in Mathlib
- Key gap: connecting eigenvalue multiplicities to trace constraint
- Decision: SURVEY — multi-session task, needs eigenvalue theory formalization
- Status: knowledge documented, ready for DEEP DIVE in next session
