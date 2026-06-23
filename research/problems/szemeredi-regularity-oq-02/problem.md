# Problem: Szemerédi Regularity: Frieze-Kannan Weak Regularity Comparison

## Statement

### Plain Language

The Frieze-Kannan weak regularity lemma (1999) gives an approximation of any graph's edge density
using a cut-norm bound, with only exponential (not tower-type) partition size. The question is:
can we formalize Frieze-Kannan weak regularity in Lean 4, compare it precisely to the full
Szemerédi regularity lemma, and show it can serve as a simpler stepping stone toward the full
result?

Specifically: does there exist a partition into at most exp(O(ε⁻²)) parts such that the
bipartite graph between every pair of parts differs from a "pure" bipartite graph (all edges
or no edges) by at most ε|V|² edges (in cut-norm sense)?

### Formal Statement

$$
\forall \varepsilon > 0,\ \forall G = (V, E),\ \exists \mathcal{P} \text{ with } |\mathcal{P}| \le 2^{O(\varepsilon^{-2})}
$$
$$
\text{such that } \max_{S, T \subseteq V} \left| e(S, T) - \sum_{A \in \mathcal{P}, B \in \mathcal{P}} d(A, B)|S \cap A||T \cap B| \right| \le \varepsilon |V|^2
$$

where $d(A, B)$ is the edge density between parts $A$ and $B$.

## Classification

```yaml
tier: A
significance: 8
tractability: 6
tags:
  - combinatorics
  - graph-theory
  - szemeredi
  - regularity
  - frieze-kannan
  - cut-norm
  - weak-regularity
```

**Significance**: 8/10 — Frieze-Kannan is the "easy" version of Szemerédi regularity; having
both formalized creates a natural pedagogical ladder and enables comparison proofs.

**Tractability**: 6/10 — The existing gallery proof already provides Mathlib bridge theorems and
the energy-increment argument; Frieze-Kannan avoids the tower bound and uses a simpler
direct construction via cut-norm optimization.

## Why This Matters

1. **Simpler complexity**: Frieze-Kannan gives 2^O(ε⁻²) parts vs tower-type T(ε⁻⁵) for full
   Szemerédi — dramatically simpler to verify computationally.
2. **Algorithmic stepping stone**: The weak regularity lemma is the basis for many
   approximation algorithms in graph theory; a Lean formalization would be immediately
   useful for verified algorithms.
3. **Comparison theorem**: Formalizing both allows proving the gap (full regularity is strictly
   stronger) and identifying exactly where the tower bound arises.
4. **Gallery ladder**: Creates a natural progression from the existing
   `szemeredi-regularity` (Mathlib bridge) → `szemeredi-regularity-oq-02` (Frieze-Kannan
   comparison) → `szemeredi-counting-oq-02` (hypergraph) → `szemeredi-full-oq-01` (Furstenberg).

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `szemeredi-regularity` | Parent proof — provides energy machinery and Mathlib bridge |
| `szemeredi-counting-oq-02` | Next step — hypergraph counting lemma formalization |
| `szemeredi-full-oq-01` | Long-term goal — Furstenberg ergodic proof |
| `szemeredi-regularity-oq-04` | Strong regularity (Alon-Fischer 2000) — harder sibling |

## Suggested First Steps (OBSERVE phase)

1. **Survey existing Lean/Mathlib**: Check if `Mathlib.Combinatorics.SimpleGraph.Regularity` has
   any Frieze-Kannan content; check `szemeredi_regularity` statement for cut-norm formulation.
2. **Read Frieze-Kannan 1999**: The original paper "Quick approximation to matrices and applications"
   gives the direct proof via random sampling or greedy optimization.
3. **Define cut-norm in Lean**: The key definition is `‖M‖_□ = max_{S,T} |∑_{i∈S,j∈T} m_{ij}|`.
   Check if this exists in Mathlib or needs to be defined.
4. **Compare definitions**: Map the existing gallery's `IsEpsilonRegular` to the Frieze-Kannan
   cut-norm bound — they are not equivalent but related.

## Key Lean Definitions to Build

```lean
-- Cut norm of a bipartite function
noncomputable def cutNorm (f : V → V → ℝ) : ℝ :=
  ⨆ (S T : Finset V), |∑ i ∈ S, ∑ j ∈ T, f i j|

-- Weak regularity: cut-norm approximation by step function
def IsWeaklyRegular (G : SimpleGraph V) (P : Finpartition (Finset.univ (α := V))) (ε : ℝ) : Prop :=
  cutNorm (fun i j => if G.Adj i j then 1 else 0 - stepDensity P i j) ≤ ε * (Finset.univ.card : ℝ)^2

-- Main theorem to prove:
-- theorem friezeKannan (G : SimpleGraph V) (ε : ℝ) (hε : 0 < ε) :
--   ∃ P : Finpartition (Finset.univ (α := V)),
--     P.parts.card ≤ 2 ^ ⌈4 / ε^2⌉ ∧ IsWeaklyRegular G P ε
```

## Known Obstacles

- **Cut-norm supremum**: Lean's `⨆` over `Finset V × Finset V` should be computable but may
  need cardinality bounds to be bounded.
- **Greedy construction**: The Frieze-Kannan proof uses a "cut maximization" step — the Lean
  equivalent requires a constructive maximizer, which Classical logic can provide.
- **Gap from Szemerédi**: Proving weak regularity does NOT imply ε-regularity for all pairs
  requires a counterexample witness.

## Phase

OBSERVE — Initial exploration of cut-norm definitions and Mathlib survey.
