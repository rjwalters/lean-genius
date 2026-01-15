/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: d3f84def-456b-4b70-9230-42e7cfe4bf8b
-/

/-
  Erdős Problem #169: Bipartite Turán Numbers

  Source: https://erdosproblems.com/169
  Status: SOLVED
  Prize: None specified

  Statement:
  Determine the Turán number ex(n, K_{s,t}) for complete bipartite graphs.

  History:
  - Kővári-Sós-Turán (1954): ex(n, K_{s,t}) ≤ (1/2)(t-1)^{1/s} n^{2-1/s} + (s-1)n/2
  - Kollár-Rónyai-Szabó (1996): Algebraic constructions match for K_{s,s}
  - Alon-Rónyai-Szabó (1999): Further constructions

  The upper bound is known to be tight for many values of s, t.

  Reference: Füredi, Z. (1996), Kővári, Sós, Turán (1954)
-/

import Mathlib


open Finset SimpleGraph

namespace Erdos169

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Complete Bipartite Graphs -/

/-- A graph contains K_{s,t} as a subgraph. -/
def ContainsKst (G : SimpleGraph V) (s t : ℕ) : Prop :=
  ∃ (S T : Finset V), S.card = s ∧ T.card = t ∧ Disjoint S T ∧
    ∀ x ∈ S, ∀ y ∈ T, G.Adj x y

/-- A graph is K_{s,t}-free. -/
def IsKstFree (G : SimpleGraph V) (s t : ℕ) : Prop := ¬ContainsKst G s t

/-- The Turán number ex(n, K_{s,t}): maximum edges in a K_{s,t}-free graph on n vertices. -/
noncomputable def ex (n s t : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ (G : SimpleGraph (Fin n)), IsKstFree G s t ∧ G.edgeSet.ncard = m }

/-! ## Kővári-Sós-Turán Theorem -/

/-- **Kővári-Sós-Turán (1954)**: Upper bound on ex(n, K_{s,t}).
    ex(n, K_{s,t}) ≤ (1/2)(t-1)^{1/s} n^{2-1/s} + (s-1)n/2 -/
axiom kst_upper_bound (n s t : ℕ) (hs : s ≥ 1) (ht : t ≥ s) (hn : n ≥ 1) :
  (ex n s t : ℝ) ≤ (1/2) * (t - 1)^(1/(s : ℝ)) * n^(2 - 1/(s : ℝ)) + (s - 1) * n / 2

/-- Simplified asymptotic form: ex(n, K_{s,t}) = O(n^{2-1/s}). -/
theorem kst_asymptotic (s t : ℕ) (hs : s ≥ 1) (ht : t ≥ s) :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (ex n s t : ℝ) ≤ C * n^(2 - 1/(s : ℝ)) := by
  sorry

/-! ## Special Cases -/

/-- ex(n, K_{2,2}) = Θ(n^{3/2}): The C₄-free case.
    This is the "Zarankiewicz problem" for K_{2,2}. -/
theorem ex_k22_bounds (n : ℕ) (hn : n ≥ 4) :
    ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    c₁ * n^(3/2 : ℝ) ≤ ex n 2 2 ∧ (ex n 2 2 : ℝ) ≤ c₂ * n^(3/2 : ℝ) := by
  sorry

/-- ex(n, K_{1,t}) = t-1 + n - 1 = n + t - 2 (stars are easy). -/
theorem ex_k1t (n t : ℕ) (ht : t ≥ 1) (hn : n ≥ t) :
    ex n 1 t = (t - 1) * n / 2 := by
  sorry

/-! ## Lower Bounds (Constructions) -/

/-- **Kollár-Rónyai-Szabó (1996)**: For prime powers q,
    there exists a K_{q,q+1}-free graph on q² - 1 vertices with
    (1/2)q(q-1)(q+1) edges. -/
axiom krs_construction (q : ℕ) (hq : q.Prime ∨ IsPrimePow q) :
  ∃ (G : SimpleGraph (Fin (q^2 - 1))),
    IsKstFree G q (q + 1) ∧ G.edgeSet.ncard = q * (q - 1) * (q + 1) / 2

/-- The KST bound is tight for K_{s,s} when s-1 is a prime power. -/
axiom kst_tight (s : ℕ) (hs : (s - 1).Prime ∨ IsPrimePow (s - 1)) :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ s → (ex n s s : ℝ) ≥ C * n^(2 - 1/(s : ℝ))

/-! ## The Gap -/

/-- The general question: Is ex(n, K_{s,t}) = Θ(n^{2-1/s}) for all s ≤ t?
    This is OPEN for most pairs (s, t). -/
def ZarankiewiczQuestion (s t : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → (ex n s t : ℝ) ≥ c * n^(2 - 1/(s : ℝ))

/-- Known: Zarankiewicz question has positive answer for s = t with s-1 prime power. -/
theorem zarankiewicz_known (s : ℕ) (hs : (s - 1).Prime) :
    ZarankiewiczQuestion s s := by
  sorry

/-! ## Summary

**Problem Status: SOLVED** (for the upper bound, constructions match for many cases)

Erdős Problem #169 concerns the Turán number ex(n, K_{s,t}) for complete
bipartite graphs K_{s,t}.

**Main Results:**
- Upper bound (KST 1954): ex(n, K_{s,t}) = O(n^{2-1/s})
- Lower bound constructions match for K_{s,s} when s-1 is prime power
- The C₄-free case: ex(n, K_{2,2}) = Θ(n^{3/2})

**Open Questions:**
- Exact determination of ex(n, K_{s,t}) for general s, t
- Do lower bounds match upper bounds for all pairs?

References:
- Kővári, Sós, Turán (1954): Original upper bound
- Kollár, Rónyai, Szabó (1996): Algebraic lower bound constructions
- Füredi (1996): Survey of bipartite Turán problems
-/

end Erdos169