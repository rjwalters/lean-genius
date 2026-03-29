/-
Erdős Problem #753: List Chromatic Number of Graph and Complement

Source: https://erdosproblems.com/753
Status: SOLVED/DISPROVED (Alon 1992)

Statement:
Does there exist some constant c > 0 such that
  χ_L(G) + χ_L(G^c) > n^{1/2 + c}
for every graph G on n vertices (where G^c is the complement)?

Answer: NO (Alon 1992)
For every n, there exists a graph G on n vertices such that
  χ_L(G) + χ_L(G^c) ≪ (n log n)^{1/2}

Background:
- χ_L(G) = list chromatic number (choosability)
- G^c = complement graph (non-edges become edges)
- Question: How large must χ_L(G) + χ_L(G^c) be?

Origin: Problem of Erdős, Rubin, and Taylor

Tags: graph-theory, list-coloring, chromatic-number, complement-graph
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open SimpleGraph Real

namespace Erdos753

variable {V : Type*} [Fintype V] [DecidableEq V]

/-
## Part I: List Coloring Definitions
-/

/--
**List Assignment:**
A list assignment L assigns a set (list) of colors to each vertex.
Different vertices may have different lists.
-/
def ListAssignment (V : Type*) (C : Type*) := V → Set C

/--
**k-List Assignment:**
A list assignment where each vertex has at least k colors.
-/
def IsKListAssignment (L : ListAssignment V ℕ) (k : ℕ) : Prop :=
  ∀ v : V, (L v).Finite ∧ k ≤ Set.ncard (L v)

/--
**L-Coloring:**
A coloring from list L assigns each vertex v a color from L(v).
-/
def IsLColoring (G : SimpleGraph V) [DecidableRel G.Adj]
    (L : ListAssignment V ℕ) (c : V → ℕ) : Prop :=
  (∀ v, c v ∈ L v) ∧ (∀ v w, G.Adj v w → c v ≠ c w)

/--
**k-Choosable (List Chromatic Number):**
A graph is k-choosable if for every k-list assignment L,
there exists a proper L-coloring.
-/
def IsKChoosable (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) : Prop :=
  ∀ L : ListAssignment V ℕ, IsKListAssignment L k →
    ∃ c : V → ℕ, IsLColoring G L c

/--
**List Chromatic Number χ_L(G):**
The minimum k such that G is k-choosable.
Axiomatized as exact computation is complex.
-/
axiom listChromaticNumber (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ

/-
## Part II: Complement Graph
-/

/--
**Complement Graph G^c:**
The complement has an edge iff G doesn't (and vice versa).
-/
def complementGraph (G : SimpleGraph V) : SimpleGraph V where
  Adj v w := v ≠ w ∧ ¬G.Adj v w
  symm := by
    intro v w ⟨hne, hnadj⟩
    exact ⟨hne.symm, fun h => hnadj (G.symm h)⟩
  loopless := by
    intro v ⟨hne, _⟩
    exact hne rfl

/--
**Complement is involutive:**
(G^c)^c = G
-/
theorem complement_complement (G : SimpleGraph V) :
    complementGraph (complementGraph G) = G := by
  ext v w
  simp only [complementGraph]
  by_cases h : G.Adj v w
  · simp [h, G.ne_of_adj h]
  · by_cases hne : v = w
    · simp [hne, G.loopless]
    · simp [h, hne]

/-
## Part III: The Conjecture
-/

/--
**The Erdős-Rubin-Taylor Conjecture:**
Does there exist c > 0 such that for all graphs G on n vertices,
χ_L(G) + χ_L(G^c) > n^{1/2 + c}?
-/
def ERTConjecture : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 → ∀ V : Type, ∀ _ : Fintype V,
    Fintype.card V = n → ∀ _ : DecidableEq V,
    ∀ G : SimpleGraph V, ∀ _ : DecidableRel G.Adj, ∀ _ : DecidableRel (complementGraph G).Adj,
    (listChromaticNumber G + listChromaticNumber (complementGraph G) : ℝ) > n ^ (1/2 + c)

/-
## Part IV: Alon's Counterexample (1992)

The conjecture is FALSE.
-/

/--
**Alon's Theorem (1992):**
For every n, there exists a graph G on n vertices such that
χ_L(G) + χ_L(G^c) ≪ (n log n)^{1/2}.
-/
axiom alon_counterexample :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
    ∃ V : Type, ∃ _ : Fintype V, Fintype.card V = n ∧
    ∃ _ : DecidableEq V, ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
    ∃ _ : DecidableRel (complementGraph G).Adj,
    (listChromaticNumber G + listChromaticNumber (complementGraph G) : ℝ) ≤
      C * Real.sqrt (n * Real.log n)

/--
**The conjecture is FALSE.**
-/
theorem conjecture_false : ¬ERTConjecture := by
  intro ⟨c, hc, hconj⟩
  obtain ⟨C, hC, hcounter⟩ := alon_counterexample
  -- Strategy: for large N, C * √(N * log N) < N^(1/2+c), contradicting
  -- the combination of hconj (lower bound) and hcounter (upper bound).
  -- Step 1: From isLittleO, log x ≤ x^c for large x
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_atTop hc).bound (show (0 : ℝ) < 1 by norm_num))
  -- Step 2: Choose N large enough
  set N := max ⌈R⌉₊ (max (⌈C ^ (2 / c)⌉₊ + 1) 2)
  have hN2 : N ≥ 2 := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) le_rfl
  have hN_pos : (0 : ℝ) < (↑N : ℝ) := by positivity
  have hN_nn : (0 : ℝ) ≤ (↑N : ℝ) := le_of_lt hN_pos
  have hN_ge1 : (1 : ℝ) ≤ (↑N : ℝ) := by exact_mod_cast show 1 ≤ N by omega
  -- Step 3: Get Alon counterexample at N
  obtain ⟨V, hFin, hcard, hDecEq, G, hDecAdj, hDecComp, hle⟩ := hcounter N (by omega)
  -- Step 4: Get ERT lower bound for same graph
  have hgt := hconj N (by omega) V hFin hcard hDecEq G hDecAdj hDecComp
  -- Now: N^(1/2+c) < sum ≤ C * √(N * log N). Need contradiction.
  -- Step 5: log N ≤ N^c (from isLittleO bound)
  have hR_le : (R : ℝ) ≤ (↑N : ℝ) :=
    le_trans (Nat.le_ceil R) (by exact_mod_cast (show ⌈R⌉₊ ≤ N from le_max_left _ _))
  have hlog_raw := hR (↑N : ℝ) hR_le
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hN_ge1),
      abs_of_nonneg (rpow_nonneg hN_nn _)] at hlog_raw
  have hlog_le : Real.log (↑N : ℝ) ≤ (↑N : ℝ) ^ c := by linarith
  -- Step 6: N * log N ≤ N^(1+c)
  have hlog_nn : (0 : ℝ) ≤ Real.log (↑N : ℝ) := Real.log_nonneg hN_ge1
  have hprod_le : (↑N : ℝ) * Real.log (↑N : ℝ) ≤ (↑N : ℝ) ^ ((1 : ℝ) + c) := by
    calc (↑N : ℝ) * Real.log (↑N : ℝ)
        ≤ (↑N : ℝ) * (↑N : ℝ) ^ c :=
          mul_le_mul_of_nonneg_left hlog_le hN_nn
      _ = (↑N : ℝ) ^ ((1 : ℝ) + c) := by
          rw [rpow_add hN_pos, rpow_one]
  -- Step 7: √(N * log N) ≤ N^((1+c)/2)
  have hsqrt_le : Real.sqrt ((↑N : ℝ) * Real.log (↑N : ℝ)) ≤ (↑N : ℝ) ^ (((1 : ℝ) + c) / 2) := by
    have h1 : Real.sqrt ((↑N : ℝ) * Real.log (↑N : ℝ)) ≤
        Real.sqrt ((↑N : ℝ) ^ ((1 : ℝ) + c)) :=
      Real.sqrt_le_sqrt hprod_le
    have h2 : Real.sqrt ((↑N : ℝ) ^ ((1 : ℝ) + c)) = (↑N : ℝ) ^ (((1 : ℝ) + c) / 2) := by
      rw [Real.sqrt_eq_rpow, ← rpow_mul hN_nn]; congr 1; ring
    linarith
  -- Step 8: C < N^(c/2) (from N > C^(2/c))
  have hC_lt : C < (↑N : ℝ) ^ (c / 2) := by
    have hN_gt_C : (↑N : ℝ) > C ^ (2 / c) := by
      have h1 : ⌈C ^ (2 / c)⌉₊ + 1 ≤ N :=
        le_trans (le_max_left _ _) (le_max_right _ _)
      calc (↑N : ℝ) ≥ ↑(⌈C ^ (2 / c)⌉₊ + 1) := by exact_mod_cast h1
        _ = ↑⌈C ^ (2 / c)⌉₊ + 1 := by push_cast; ring
        _ > C ^ (2 / c) := by linarith [Nat.le_ceil (C ^ (2 / c))]
    have h_exp : (2 : ℝ) / c * (c / 2) = 1 := by field_simp
    calc C = (C ^ (2 / c)) ^ (c / 2) := by
            rw [← rpow_mul hC.le, h_exp, rpow_one]
      _ < (↑N : ℝ) ^ (c / 2) := rpow_lt_rpow (rpow_nonneg hC.le _) hN_gt_C (by linarith)
  -- Step 9: C * N^((1+c)/2) < N^(1/2+c)
  have hfinal : C * (↑N : ℝ) ^ (((1 : ℝ) + c) / 2) < (↑N : ℝ) ^ (1 / 2 + c) := by
    calc C * (↑N : ℝ) ^ (((1 : ℝ) + c) / 2)
        < (↑N : ℝ) ^ (c / 2) * (↑N : ℝ) ^ (((1 : ℝ) + c) / 2) := by
          nlinarith [rpow_pos_of_pos hN_pos (((1 : ℝ) + c) / 2)]
      _ = (↑N : ℝ) ^ (1 / 2 + c) := by
          rw [← rpow_add hN_pos]; congr 1; ring
  -- Step 10: Contradiction
  have : C * Real.sqrt (↑N * Real.log ↑N) < (↑N : ℝ) ^ (1 / 2 + c) := by
    calc C * Real.sqrt (↑N * Real.log ↑N)
        ≤ C * (↑N : ℝ) ^ (((1 : ℝ) + c) / 2) :=
          mul_le_mul_of_nonneg_left hsqrt_le hC.le
      _ < (↑N : ℝ) ^ (1 / 2 + c) := hfinal
  linarith

/-
## Part V: Bounds and Relations
-/

/-
**χ_L(G) ≥ χ(G):**
List chromatic number is at least the ordinary chromatic number.
-/

/-
**Trivial Lower Bound:**
χ_L(G) + χ_L(G^c) ≥ √n for most graphs.
-/

/-
**Upper Bound:**
χ_L(G) ≤ Δ(G) + 1 where Δ is max degree (greedy coloring).
-/

/-
## Part VI: Probabilistic Construction

**Alon's Construction:**
The counterexample uses random graphs near the threshold p = 1/2.
The construction exploits the near-balance between G and G^c.

**Random Graph G(n, 1/2):**
At probability 1/2, G and G^c have similar structure.
-/

/-
## Part VII: Related Results

**Ordinary Chromatic Number:**
χ(G) + χ(G^c) ≥ 2√n (Nordhaus-Gaddum).

**Nordhaus-Gaddum Upper Bound:**
χ(G) + χ(G^c) ≤ n + 1.

**List vs Ordinary:**
χ_L and χ can differ significantly (Voigt's example).
-/

/-
## Part VIII: Choosability Properties

**Bipartite Graphs:**
Not all bipartite graphs are 2-choosable (unlike 2-colorable).

**Complete Graphs:**
K_n has χ_L(K_n) = n (same as χ).

**Complete Bipartite:**
K_{n,n} has χ_L = 1 + ⌈log₂ n⌉ (Galvin's theorem).
-/

/-
## Part IX: Summary

**Erdős Problem #753: Status SOLVED/DISPROVED** (Alon 1992)

**Question:** Does there exist c > 0 such that
χ_L(G) + χ_L(G^c) > n^{1/2 + c} for all G on n vertices?

**Answer:** NO! Alon showed χ_L(G) + χ_L(G^c) ≤ O((n log n)^{1/2})
for suitable graphs.

**Key Points:**
- List chromatic number measures choosability
- The conjecture aimed to strengthen Nordhaus-Gaddum for χ_L
- Probabilistic methods give counterexamples
- Random G(n, 1/2) graphs have G ≈ G^c structure

**References:**
- Erdős, Rubin, Taylor: Original problem
- Alon (1992): Counterexample via probabilistic method
-/

theorem erdos_753_summary :
    -- The conjecture is FALSE
    ¬ERTConjecture ∧
    -- Alon's counterexample exists
    (∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 →
      ∃ V : Type, ∃ _ : Fintype V, Fintype.card V = n ∧
      ∃ _ : DecidableEq V, ∃ G : SimpleGraph V, ∃ _ : DecidableRel G.Adj,
      ∃ _ : DecidableRel (complementGraph G).Adj,
      (listChromaticNumber G + listChromaticNumber (complementGraph G) : ℝ) ≤
        C * Real.sqrt (n * Real.log n)) := by
  exact ⟨conjecture_false, alon_counterexample⟩

end Erdos753
