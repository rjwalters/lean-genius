/-
  Tetrahedral Reciprocals — Depth-2 Telescoping

  Result:  ∑_{n=1}^∞ 1/Tet_n = 3/2,  where  Tet_n = n(n+1)(n+2)/6  is the n-th
  tetrahedral number.  Equivalently, with the index shifted to n : ℕ (running term
  being n+1, n+2, n+3),

      ∑_{n=0}^∞ 6/((n+1)(n+2)(n+3)) = 3/2.

  This is the depth-2 analogue of the classical depth-1 triangular-reciprocal sum
  ∑ 2/(n(n+1)) = 2  (`TriangularNumberReciprocals.lean`).  Where the depth-1 sum
  telescopes via 2/(n(n+1)) = 2/n - 2/(n+1), the tetrahedral sum telescopes via the
  depth-2 partial fraction

      6/((n+1)(n+2)(n+3)) = 3/((n+1)(n+2)) - 3/((n+2)(n+3)),

  i.e. f(n) = g(n) - g(n+1) with g(n) = 3/((n+1)(n+2)).  Hence the partial sum is

      ∑_{i<N} f(i) = g(0) - g(N) = 3/2 - 3/((N+1)(N+2))  →  3/2.

  Proof outline:
    1. tetrahedral_partial_fraction : the depth-2 telescoping identity (field_simp/ring).
    2. partial_sum_closed_form      : ∑_{i<N} f i = 3/2 - 3/((N+1)(N+2))  (induction on N).
    3. tail_to_zero                 : 3/((N+1)(N+2)) → 0  (squeeze by 3/(N+1)).
    4. tetrahedral_reciprocals      : HasSum f (3/2)  via hasSum_iff_tendsto_nat_of_nonneg.

  No axioms, no sorries.
-/

import Mathlib

set_option linter.unusedVariables false

open Finset BigOperators Filter Topology Real

namespace TriangularReciprocalsOQ04

/-- The shifted summand 6/((n+1)(n+2)(n+3)) = 1/Tet_{n+1}. -/
noncomputable def tetReciprocal (n : ℕ) : ℝ :=
  6 / (((n : ℝ) + 1) * ((n : ℝ) + 2) * ((n : ℝ) + 3))

/-- The telescoping antiderivative g(n) = 3/((n+1)(n+2)). -/
noncomputable def gTele (n : ℕ) : ℝ :=
  3 / (((n : ℝ) + 1) * ((n : ℝ) + 2))

-- ═══════════════════════════════════════════════════
-- Lemma 1: Depth-2 telescoping partial fraction
-- ═══════════════════════════════════════════════════

/-- 6/((n+1)(n+2)(n+3)) = 3/((n+1)(n+2)) - 3/((n+2)(n+3)) = g(n) - g(n+1). -/
theorem tetrahedral_partial_fraction (n : ℕ) :
    tetReciprocal n = gTele n - gTele (n + 1) := by
  unfold tetReciprocal gTele
  have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
  have h3 : ((n : ℝ) + 3) ≠ 0 := by positivity
  have hcast : (((n : ℝ) + 1) + 1) = (n : ℝ) + 2 := by ring
  have hcast2 : (((n : ℝ) + 1) + 2) = (n : ℝ) + 3 := by ring
  push_cast
  rw [hcast, hcast2]
  field_simp
  ring

-- ═══════════════════════════════════════════════════
-- Lemma 2: Closed form for the partial sum
-- ═══════════════════════════════════════════════════

/-- ∑_{i<N} 6/((i+1)(i+2)(i+3)) = 3/2 - 3/((N+1)(N+2)). -/
theorem partial_sum_closed_form (N : ℕ) :
    ∑ i ∈ Finset.range N, tetReciprocal i =
      3 / 2 - 3 / (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
  induction N with
  | zero => simp [tetReciprocal]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    -- After adding the (M)-th term, telescoping collapses to the M+1 closed form.
    unfold tetReciprocal
    have h1 : ((M : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((M : ℝ) + 2) ≠ 0 := by positivity
    have h3 : ((M : ℝ) + 3) ≠ 0 := by positivity
    push_cast
    field_simp
    ring

-- ═══════════════════════════════════════════════════
-- Lemma 3: Tail 3/((N+1)(N+2)) → 0
-- ═══════════════════════════════════════════════════

/-- 3/((N+1)(N+2)) → 0 as N → ∞ (squeezed below 3/(N+1)). -/
theorem tail_to_zero :
    Tendsto (fun N : ℕ => 3 / (((N : ℝ) + 1) * ((N : ℝ) + 2)))
      atTop (𝓝 0) := by
  have h0 : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hg : Tendsto (fun N : ℕ => 3 * ((1 : ℝ) / ((N : ℝ) + 1))) atTop (𝓝 (3 * 0)) :=
    h0.const_mul 3
  rw [mul_zero] at hg
  apply squeeze_zero (g := fun N : ℕ => 3 * ((1 : ℝ) / ((N : ℝ) + 1)))
  · intro N; positivity
  · intro N
    have hb : ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) * ((N : ℝ) + 2) := by
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    rw [mul_one_div]
    gcongr
  · exact hg

-- ═══════════════════════════════════════════════════
-- Main Theorem
-- ═══════════════════════════════════════════════════

/-- **Tetrahedral Reciprocals.**  The reciprocals of the tetrahedral numbers sum to 3/2:

      ∑_{n=0}^∞ 6/((n+1)(n+2)(n+3)) = 3/2.

    Since 1/Tet_m = 6/(m(m+1)(m+2)), with the running tetrahedral index m = n+1 this is
    exactly ∑_{m=1}^∞ 1/Tet_m = 3/2. -/
theorem tetrahedral_reciprocals : HasSum tetReciprocal (3 / 2 : ℝ) := by
  have h_nonneg : ∀ n : ℕ, 0 ≤ tetReciprocal n := by
    intro n; unfold tetReciprocal; positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg h_nonneg]
  -- Partial sums equal 3/2 - 3/((N+1)(N+2)).
  rw [show (fun N : ℕ => ∑ i ∈ Finset.range N, tetReciprocal i) =
        fun N : ℕ => 3 / 2 - 3 / (((N : ℝ) + 1) * ((N : ℝ) + 2)) from
      funext partial_sum_closed_form]
  -- 3/2 - (3/((N+1)(N+2))) → 3/2 - 0 = 3/2.
  have h_lim : Tendsto
      (fun N : ℕ => (3 / 2 : ℝ) - 3 / (((N : ℝ) + 1) * ((N : ℝ) + 2)))
      atTop (𝓝 ((3 / 2 : ℝ) - 0)) :=
    tendsto_const_nhds.sub tail_to_zero
  rw [sub_zero] at h_lim
  exact h_lim

/-- tsum version of the tetrahedral reciprocal sum. -/
theorem tetrahedral_reciprocals_tsum :
    ∑' n : ℕ, tetReciprocal n = (3 / 2 : ℝ) :=
  tetrahedral_reciprocals.tsum_eq

-- ═══════════════════════════════════════════════════
-- Sanity checks of the closed form
-- ═══════════════════════════════════════════════════

/-- First term (n = 0): 6/(1·2·3) = 1 = 1/Tet_1. -/
example : tetReciprocal 0 = 1 := by unfold tetReciprocal; norm_num

/-- Partial sum of the first two terms is 5/4. -/
example : ∑ i ∈ Finset.range 2, tetReciprocal i = 5 / 4 := by
  rw [partial_sum_closed_form]; norm_num

end TriangularReciprocalsOQ04
