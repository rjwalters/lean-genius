/-
Erdős Problem #810: Rainbow C₄ in Edge-Colored Dense Graphs

Source: https://erdosproblems.com/810
Status: OPEN (Burr, Erdős, Graham, Sós)

## Statement

Does there exist ε > 0 such that for all sufficiently large n, there exists
a graph G on n vertices with at least εn² edges whose edges can be colored
with n colors so that every C₄ receives 4 distinct colors?

## Background

A problem of Burr, Erdős, Graham, and Sós [Er91]. See also Problem #809.
The Kővári-Sós-Turán theorem gives ex(n; C₄) = O(n^{3/2}), so C₄-free
graphs (which vacuously satisfy the rainbow condition) are too sparse.
Any positive answer must involve graphs with many C₄s, all of which
are rainbow — a delicate balance between density and structure.

## Approach

We formalize edge colorings, the C₄ structure, and the rainbow property.
The main conjecture is stated as a Prop definition (not an axiom, since it is OPEN).
The Kővári-Sós-Turán sparsity bound for C₄-free graphs is axiomatized.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Erdos810

variable {n : ℕ}

-- ## Part I: Edge Colorings and Rainbow Subgraphs

/-- An edge coloring of a graph on Fin n using n colors.
    Assigns a color in Fin n to each edge (unordered pair). -/
def EdgeColoringN (G : SimpleGraph (Fin n)) :=
  ∀ (u v : Fin n), G.Adj u v → Fin n

/-- A 4-cycle in G given by four distinct vertices forming a cycle:
    v₁ -- v₂ -- v₃ -- v₄ -- v₁ -/
structure CycleFour (G : SimpleGraph (Fin n)) where
  v₁ : Fin n
  v₂ : Fin n
  v₃ : Fin n
  v₄ : Fin n
  distinct : ({v₁, v₂, v₃, v₄} : Finset (Fin n)).card = 4
  edge12 : G.Adj v₁ v₂
  edge23 : G.Adj v₂ v₃
  edge34 : G.Adj v₃ v₄
  edge41 : G.Adj v₄ v₁

/-- A C₄ is rainbow under a coloring if all 4 edges have distinct colors. -/
def CycleFour.isRainbow {G : SimpleGraph (Fin n)} (C : CycleFour G)
    (χ : EdgeColoringN G) : Prop :=
  let c₁ := χ C.v₁ C.v₂ C.edge12
  let c₂ := χ C.v₂ C.v₃ C.edge23
  let c₃ := χ C.v₃ C.v₄ C.edge34
  let c₄ := χ C.v₄ C.v₁ C.edge41
  ({c₁, c₂, c₃, c₄} : Finset (Fin n)).card = 4

/-- An edge coloring is rainbow-C₄ if every C₄ in G is rainbow. -/
def IsRainbowC4Coloring (G : SimpleGraph (Fin n)) (χ : EdgeColoringN G) : Prop :=
  ∀ C : CycleFour G, C.isRainbow χ

-- ## Part II: Dense Graphs with Rainbow-C₄ Colorings

/-- A graph on n vertices has a rainbow-C₄ n-coloring and at least εn² edges. -/
def HasDenseRainbowC4 (n : ℕ) (ε : ℝ) : Prop :=
  ∃ (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj),
    ε * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ) ∧
    ∃ χ : EdgeColoringN G, IsRainbowC4Coloring G χ

-- ## Part III: The Burr-Erdős-Graham-Sós Conjecture (OPEN)

/-- **Erdős Problem 810** (Burr-Erdős-Graham-Sós conjecture):
    Does there exist ε > 0 such that for all sufficiently large n,
    there is a graph on n vertices with at least εn² edges admitting
    an n-coloring where every C₄ is rainbow?

    This is an OPEN problem — stated as a Prop, not asserted as true. -/
def ErdosProblem810 : Prop :=
  ∃ ε : ℝ, ε > 0 ∧
    ∀ᶠ n in Filter.atTop, HasDenseRainbowC4 n ε

-- ## Part IV: Known Results (Axioms)

/-- **Kővári-Sós-Turán bound for C₄:**
    C₄-free graphs on n vertices have O(n^{3/2}) edges.
    This means C₄-free graphs (which vacuously satisfy the rainbow condition)
    have too few edges to achieve the quadratic density εn². -/
axiom kovari_sos_turan_C4 :
  ∃ C : ℝ, C > 0 ∧
    ∀ (n : ℕ) (hn : 1 ≤ n)
      (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ C4 : CycleFour G, False) →
        (G.edgeFinset.card : ℝ) ≤ C * (n : ℝ) ^ (3 / 2 : ℝ)

/-- **Dense graphs contain C₄s (for large n):**
    For any ε > 0, all sufficiently large C₄-free graphs have fewer than
    εn² edges. Contrapositively: dense graphs on large vertex sets must
    contain C₄s. This follows from KST by the arithmetic:
    C·n^{3/2} < ε·n² when n > (C/ε)².

    Note: The previous axiom `dense_graph_has_C4` claimed this for ALL
    n ≥ 2, but that's too strong (a 2-vertex graph with 1 edge can have
    ε·4 ≤ 1 for small ε, yet has no C₄). The correct version requires
    n sufficiently large (depending on ε and the KST constant C). -/
theorem dense_graph_has_C4_large_n (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ (n : ℕ) (hn : N₀ ≤ n)
      (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hd : ε * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ)),
    Nonempty (CycleFour G) := by
  -- From KST: ∃ C > 0, C₄-free ⟹ |E| ≤ C·n^{3/2}
  -- For n > (C/ε)²: ε·n² > C·n^{3/2}, so a graph with ≥ εn² edges
  -- cannot be C₄-free. The N₀ depends on C and ε.
  obtain ⟨C, hC_pos, hKST⟩ := kovari_sos_turan_C4
  -- Choose N₀ so that n ≥ N₀ implies ε·n² > C·n^{3/2}
  refine ⟨Nat.ceil ((C / ε) ^ 2) + 2, fun n hn G _ hd => ?_⟩
  -- By contradiction: suppose G has no C₄
  by_contra h_no
  rw [not_nonempty_iff] at h_no
  -- h_no : ∀ C4 : CycleFour G, False  (G is C₄-free)
  have hn1 : 1 ≤ n := by omega
  have hE := hKST n hn1 G h_no  -- |E| ≤ C·n^{3/2}
  -- Combined: ε·n² ≤ C·n^{3/2}
  have h_combined : ε * (↑n : ℝ) ^ 2 ≤ C * (↑n : ℝ) ^ ((3 : ℝ) / 2) :=
    le_trans hd hE
  -- But n is large enough that C·n^{3/2} < ε·n²: contradiction
  -- Key: n > (C/ε)², so √n > C/ε, so ε·√n > C
  have hn_pos : (0 : ℝ) < (↑n : ℝ) := Nat.cast_pos.mpr (by omega)
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt (↑n : ℝ) := Real.sqrt_pos.mpr hn_pos
  -- n > (C/ε)²
  have h_n_large : (C / ε) ^ 2 < (↑n : ℝ) := by
    have h1 : (C / ε) ^ 2 ≤ ↑(Nat.ceil ((C / ε) ^ 2)) :=
      Nat.le_ceil ((C / ε) ^ 2)
    have h2 : (↑(Nat.ceil ((C / ε) ^ 2) + 2) : ℝ) ≤ (↑n : ℝ) := by exact_mod_cast hn
    push_cast at h2
    linarith
  -- √n > C/ε
  have h_sqrt_large : C / ε < Real.sqrt (↑n : ℝ) := by
    rw [← Real.sqrt_sq (le_of_lt (div_pos hC_pos hε))]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) h_n_large
  -- ε·√n > C
  have h_key : C < ε * Real.sqrt (↑n : ℝ) := by
    have := h_sqrt_large
    rw [div_lt_iff₀ hε] at this
    linarith
  -- Decompose: n^{3/2} = n · √n, n² = n · n
  have h32 : (↑n : ℝ) ^ ((3 : ℝ) / 2) = ↑n * Real.sqrt ↑n := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 from by norm_num]
    rw [Real.rpow_add hn_pos]
    rw [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h_sq : (↑n : ℝ) ^ 2 = ↑n * ↑n := sq (↑n : ℝ)
  rw [h32, h_sq] at h_combined
  -- h_combined : ε * (↑n * ↑n) ≤ C * (↑n * √↑n)
  -- Cancel ↑n > 0 from both sides
  have h_cancel1 : ε * ↑n ≤ C * Real.sqrt ↑n := by
    nlinarith [mul_comm (↑n : ℝ) (Real.sqrt ↑n)]
  -- Use n = √n * √n to cancel √n > 0
  have h_cancel2 : ε * Real.sqrt ↑n ≤ C := by
    have hsq : (↑n : ℝ) = Real.sqrt ↑n * Real.sqrt ↑n :=
      (Real.mul_self_sqrt (Nat.cast_nonneg n)).symm
    nlinarith [mul_comm (ε * Real.sqrt ↑n) (Real.sqrt ↑n)]
  -- Contradiction: h_cancel2 says ε·√n ≤ C, h_key says C < ε·√n
  linarith

-- ## Part V: Structural Observations

/-- C₄-free graphs vacuously satisfy the rainbow condition. -/
theorem c4_free_vacuously_rainbow
    (G : SimpleGraph (Fin n)) (χ : EdgeColoringN G)
    (hfree : ∀ C4 : CycleFour G, False) :
    IsRainbowC4Coloring G χ :=
  fun C => False.elim (hfree C)

/-- **Any witness graph for Problem 810 must contain C₄s.**
    If a graph G has εn² edges and admits a rainbow-C₄ coloring, then for
    large n it must contain C₄s (since C₄-free graphs have O(n^{3/2}) edges).
    The rainbow condition is non-vacuous. -/
theorem witness_must_contain_C4 (ε : ℝ) (hε : ε > 0) :
    ∃ N₀ : ℕ, ∀ (n : ℕ) (hn : N₀ ≤ n)
      (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (hd : ε * (n : ℝ) ^ 2 ≤ (G.edgeFinset.card : ℝ))
      (_χ : EdgeColoringN G) (_hR : IsRainbowC4Coloring G _χ),
    Nonempty (CycleFour G) := by
  obtain ⟨N₀, hN⟩ := dense_graph_has_C4_large_n ε hε
  exact ⟨N₀, fun n hn G _ hd _ _ => hN n hn G hd⟩

/-- **Rainbow C₄ requires n ≥ 4.**
    To have a C₄ with 4 distinct colors from Fin n, we need n ≥ 4. -/
theorem rainbow_C4_needs_4_colors {m : ℕ} (G : SimpleGraph (Fin m))
    (χ : EdgeColoringN G) (C : CycleFour G)
    (hR : C.isRainbow χ) : 4 ≤ m := by
  -- The 4 colors are in Fin m, and they form a set of size 4
  unfold CycleFour.isRainbow at hR
  -- A Finset of Fin m with card = 4 implies Fin m has ≥ 4 elements
  have : (Finset.univ : Finset (Fin m)).card = m := Finset.card_fin m
  have h4 : ({χ C.v₁ C.v₂ C.edge12, χ C.v₂ C.v₃ C.edge23,
              χ C.v₃ C.v₄ C.edge34, χ C.v₄ C.v₁ C.edge41} : Finset (Fin m)).card = 4 := hR
  have hsub : {χ C.v₁ C.v₂ C.edge12, χ C.v₂ C.v₃ C.edge23,
               χ C.v₃ C.v₄ C.edge34, χ C.v₄ C.v₁ C.edge41} ⊆ Finset.univ :=
    Finset.subset_univ _
  have := Finset.card_le_card hsub
  omega

end Erdos810
