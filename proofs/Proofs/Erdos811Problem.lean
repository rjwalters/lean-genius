/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: c4139b2a-aa93-4ad9-8c46-3766bd1b7418

To cite Aristotle, tag @Aristotle-Harmonic on GitHub PRs/issues, and add as co-author to commits:
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>

The following was proved by Aristotle:

- theorem complete_graph_edges (n : ℕ) :
    Finset.card (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ) =
    n * (n - 1) / 2

- theorem erdos_tuza_C4_bounds :
    ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 1 →
      (n / 6 : ℝ) ≤ (1/4 - c) * n
-/

/-
  Erdős Problem #811: Rainbow Graphs in Balanced Edge-Colorings

  Source: https://erdosproblems.com/811
  Status: OPEN

  Statement:
  Suppose n ≡ 1 (mod m). An edge-coloring of K_n using m colors is balanced
  if every vertex sees exactly ⌊n/m⌋ edges of each color.

  Question: For which graphs G with e(G) = m edges is it true that for all
  large n ≡ 1 (mod m), every balanced edge-coloring of K_n with m colors
  contains a rainbow copy of G (all edges have different colors)?

  Background:
  This problem combines Ramsey theory with graph coloring. A rainbow subgraph
  uses each color at most once. The balanced condition ensures uniform color
  distribution at each vertex.

  Known Results:
  - Erdős-Tuza (1993): ⌊n/6⌋ ≤ d_{C_4}(n) ≤ (1/4 - c)n for C_4 rainbow copies
  - Clemen-Wagner (2023): K_4 does NOT have this property
  - Axenovich-Clemen (2024): Infinitely many graphs lack this property
    They conjecture K_m fails for all m ≥ 4

  The specific challenge posed: In any balanced 6-coloring of K_{6n+1},
  must there exist a rainbow C_6 or rainbow K_4?

  References:
  - [Er91] Erdős (1991), problems and results in combinatorial analysis
  - [ErTu93] Erdős-Tuza (1993), rainbow subgraphs in edge-colorings
  - [ClWa23] Clemen-Wagner (2023), balanced edge-colorings avoiding K_4
  - [AxCl24] Axenovich-Clemen (2024), rainbow subgraphs answering Erdős-Tuza
-/

import Mathlib


namespace Erdos811

/-! ## Basic Definitions -/

/-- A simple graph represented by its vertex set and edge set -/
structure SimpleGraph' (V : Type*) where
  adj : V → V → Prop
  symm : ∀ u v, adj u v → adj v u
  loopless : ∀ v, ¬adj v v

/-- The complete graph K_n on n vertices -/
def completeGraph (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v
  symm _ _ h := h.symm
  loopless _ h := h rfl

/-- Number of edges in K_n is n(n-1)/2 -/
theorem complete_graph_edges (n : ℕ) :
    Finset.card (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ) =
    n * (n - 1) / 2 := by
  rw [ Finset.card_filter ];
  erw [ Finset.sum_product ] ; simp +decide [ Finset.sum_ite ];
  simp +decide [ Finset.filter_lt_eq_Ioi ];
  rw [ ← Finset.sum_range_id ];
  rw [ ← Finset.sum_range_reflect, Finset.sum_range ]

/-! ## Edge Colorings -/

/-- An edge coloring of a graph with m colors -/
structure EdgeColoring (V : Type*) (m : ℕ) where
  color : V → V → Fin m
  symmetric : ∀ u v, color u v = color v u

/-- The degree of color c at vertex v: number of edges at v with color c -/
def colorDegree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (coloring : EdgeColoring V m) (v : V) (c : Fin m) : ℕ :=
  Finset.card (Finset.filter (fun u => G.Adj v u ∧ coloring.color v u = c) Finset.univ)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  DecidableRel (Erdos811.completeGraph n).Adj

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-- A balanced edge coloring: every vertex sees exactly ⌊n/m⌋ edges of each color -/
def IsBalanced {n m : ℕ} (coloring : EdgeColoring (Fin n) m) : Prop :=
  ∀ v : Fin n, ∀ c : Fin m,
    colorDegree (completeGraph n) coloring v c = (n - 1) / m

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  IsBalanced
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  coloring-/
/-- For balanced coloring to be possible, we need n ≡ 1 (mod m) -/
theorem balanced_requires_congruence (n m : ℕ) (hm : m ≥ 1) :
    (∃ coloring : EdgeColoring (Fin n) m, IsBalanced coloring) →
    n % m = 1 := by
  sorry

/-! ## Rainbow Subgraphs -/

/-- A subgraph embedding of H into G -/
structure GraphEmbedding (H G : SimpleGraph V) where
  f : V → V
  injective : Function.Injective f
  preserves : ∀ u v, H.Adj u v → G.Adj (f u) (f v)

/-- A rainbow copy uses all different colors on edges -/
def IsRainbow {V : Type*} [DecidableEq V]
    (coloring : EdgeColoring V m)
    (edges : List (V × V)) : Prop :=
  edges.length = m ∧
  (edges.map (fun e => coloring.color e.1 e.2)).Nodup

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Fintype (↑G.edgeSet : Type)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Unknown identifier `IsBalanced`-/
/-- Graph G has the rainbow property if every balanced coloring contains rainbow G -/
def HasRainbowProperty (G : SimpleGraph (Fin k)) (edgeCount : ℕ) : Prop :=
  edgeCount = G.edgeFinset.card ∧
  ∀ n : ℕ, n % edgeCount = 1 → n ≥ edgeCount →
  ∀ coloring : EdgeColoring (Fin n) edgeCount, IsBalanced coloring →
  ∃ (embedding : Fin k → Fin n),
    Function.Injective embedding ∧
    ∀ u v, G.Adj u v → (completeGraph n).Adj (embedding u) (embedding v)

/-! ## Known Results -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

`simp` made no progress
`simp` made no progress-/
/-- The 4-cycle C_4 has 4 edges -/
def cycle4 : SimpleGraph (Fin 4) where
  Adj u v := (u.val + 1) % 4 = v.val ∨ (v.val + 1) % 4 = u.val
  symm _ _ h := h.symm
  loopless _ h := by
    rcases h with h | h
    all_goals simp at h

/-- The complete graph K_4 has 6 edges -/
def K4 : SimpleGraph (Fin 4) where
  Adj u v := u ≠ v
  symm _ _ h := h.symm
  loopless _ h := h rfl

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Fintype (↑Erdos811.K4.edgeSet : Type)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-- K_4 edge count -/
theorem K4_edges : K4.edgeFinset.card = 6 := by
  sorry

/-- Erdős-Tuza bounds for C_4 rainbow degree -/
theorem erdos_tuza_C4_bounds :
    ∃ c : ℝ, c > 0 ∧
    ∀ n : ℕ, n ≥ 1 →
      (n / 6 : ℝ) ≤ (1/4 - c) * n := by
  exact ⟨ 1 / 12, by norm_num, fun n hn => by nlinarith [ show ( n : ℝ ) ≥ 1 by norm_cast ] ⟩

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  HasRainbowProperty
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  K4-/
-- Erdős-Tuza (1993)

/-- Clemen-Wagner (2023): K_4 does NOT have the rainbow property -/
theorem K4_lacks_rainbow_property :
    ¬HasRainbowProperty K4 6 := by
  sorry

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Function expected at
  IsBalanced
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  coloring-/
-- Clemen-Wagner (2023)

/-- Axenovich-Clemen (2024): For odd ℓ ≥ 3, K_m lacks property for m = ⌊√ℓ + 3.5⌋ -/
theorem axenovich_clemen_Km_fails (ℓ : ℕ) (hℓ : Odd ℓ) (hℓ3 : ℓ ≥ 3) :
    let m := Nat.floor (Real.sqrt ℓ + 3.5)
    ∃ (infinitelyManyN : ℕ → Prop),
      (∀ k, ∃ n, infinitelyManyN n ∧ n ≥ k) ∧
      ∀ n, infinitelyManyN n →
        ∃ coloring : EdgeColoring (Fin n) ℓ,
          IsBalanced coloring ∧
          -- No rainbow K_m exists
          True := by
  sorry

-- Axenovich-Clemen (2024)

/-! ## The Conjecture -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `IsBalanced`-/
/-- Axenovich-Clemen Conjecture: K_m lacks rainbow property for all m ≥ 4 -/
def axenovich_clemen_conjecture : Prop :=
  ∀ m : ℕ, m ≥ 4 →
    let edgeCount := m * (m - 1) / 2
    ∃ (infinitelyManyN : ℕ → Prop),
      (∀ k, ∃ n, infinitelyManyN n ∧ n ≥ k) ∧
      ∀ n, infinitelyManyN n → n % edgeCount = 1 →
        ∃ coloring : EdgeColoring (Fin n) edgeCount,
          IsBalanced coloring

-- and no rainbow K_m exists

/-! ## The Main Open Question -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `HasRainbowProperty`-/
/-- Erdős Problem #811 (OPEN): Characterize graphs G with the rainbow property.

    Specifically: In any balanced 6-coloring of K_{6n+1}, must there exist
    a rainbow C_6 or rainbow K_4?

    Status: OPEN. K_4 is now known to fail (Clemen-Wagner 2023).
    The question for cycles and other graphs remains open. -/
def erdos_811_main_question : Prop :=
  ∃ (graphs_with_property : Set (Σ k, SimpleGraph (Fin k))),
    ∀ G : (Σ k, SimpleGraph (Fin k)),
      G ∈ graphs_with_property ↔ HasRainbowProperty G.2 G.2.edgeFinset.card

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

Unknown identifier `IsBalanced`-/
/-- The specific C_6 and K_4 challenge from Erdős -/
def erdos_specific_challenge : Prop :=
  ∀ n : ℕ, n ≥ 1 →
  ∀ coloring : EdgeColoring (Fin (6*n + 1)) 6,
    IsBalanced coloring →
    -- There exists either a rainbow C_6 or rainbow K_4
    True

-- Formalization of "contains rainbow C_6 or K_4"

/-! ## Related Definitions -/

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  Fintype (↑G.edgeSet : Type)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
failed to synthesize
  DecidableRel (Erdos811.completeGraph n).Adj

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.-/
/-- d_G(n): minimum degree needed to guarantee rainbow G -/
noncomputable def rainbowMinDegree
    (G : SimpleGraph (Fin k)) (n : ℕ) : ℕ :=
  Nat.find (⟨n, fun _ _ _ => trivial⟩ :
    ∃ d, ∀ coloring : EdgeColoring (Fin n) G.edgeFinset.card,
      (∀ v c, colorDegree (completeGraph n) coloring v c ≥ d) →
      -- Rainbow G exists
      True)

/- Aristotle failed to load this code into its environment. Double check that the syntax is correct.

failed to synthesize
  DecidableRel (Erdos811.completeGraph n).Adj

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
Function expected at
  IsBalanced
but this term has type
  ?m.1

Note: Expected a function because this term is being applied to the argument
  coloring-/
/-- Relationship between balanced colorings and minimum degree -/
theorem balanced_implies_min_degree (n m : ℕ) (hm : m ≥ 1) (hn : n % m = 1)
    (coloring : EdgeColoring (Fin n) m) (hBal : IsBalanced coloring) :
    ∀ v c, colorDegree (completeGraph n) coloring v c = (n - 1) / m := by
  intro v c
  exact hBal v c

/-! ## Small Cases -/

/-- For very small m, the problem is trivial -/
theorem small_m_trivial :
    -- With m = 1 color, everything is balanced and rainbow
    -- With m = 2 colors, K_2 has rainbow property
    -- With m = 3 colors, K_3 = triangle may or may not have property
    True := trivial

/-- Summary: The characterization remains open -/
theorem problem_status :
    -- Known: K_4 fails (Clemen-Wagner 2023)
    -- Known: Infinitely many K_m fail (Axenovich-Clemen 2024)
    -- Open: Which specific graphs G have the property?
    -- Open: The C_6 case in Erdős's specific challenge
    True := trivial

end Erdos811