/-
  Erdős Problem #490 OQ-01: Does lim max|A||B|·log N/N² Exist?

  The parent problem (Erdős #490) asks about pairs A, B ⊆ {1,...,N}
  with all products ab (a ∈ A, b ∈ B) distinct. Szemerédi (1976) proved
  |A||B| ≤ C·N²/log N. The optimal example (A = [1, N/2], B = primes
  in (N/2, N]) achieves |A||B| ~ N²/(2 log N).

  This open question asks: does the limit
    L = lim_{N→∞} max_{A,B} |A||B| · log N / N²
  exist? If so, what is its value?

  We formalize:
  1. The product ratio sequence and its basic properties (§1-2)
  2. Boundedness: the sequence is bounded above and below (§3)
  3. Limsup/liminf sandwich: c ≤ productRatio ≤ C (§4)
  4. Limit existence → limit in [c, C] (§5)
  5. Structural analysis: cardinality bounds, trivial bound (§6)

  Sorry count: 0
  Axiom count: 3 (Szemerédi bound, optimal example lower bound, maxProd existence)
-/

import Mathlib

open Finset Real Filter

-- ============================================================================
-- § 1. Basic Definitions
-- ============================================================================

/-- A set A ⊆ {1,...,N}. -/
def IsSubsetUpTo' (A : Finset ℕ) (N : ℕ) : Prop :=
  ∀ a ∈ A, 1 ≤ a ∧ a ≤ N

/-- All products ab with a ∈ A, b ∈ B are distinct (product map is injective). -/
def HasDistinctProducts' (A B : Finset ℕ) : Prop :=
  ∀ a₁ a₂ b₁ b₂, a₁ ∈ A → a₂ ∈ A → b₁ ∈ B → b₂ ∈ B →
    a₁ * b₁ = a₂ * b₂ → (a₁ = a₂ ∧ b₁ = b₂)

-- ============================================================================
-- § 2. The Maximum Product Size
-- ============================================================================

/-- The maximum of |A|·|B| over all valid pairs with distinct products in {1,...,N}.
    We axiomatize its existence since the optimization is over finite sets. -/
axiom maxProd_exists (N : ℕ) (hN : 2 ≤ N) :
  ∃ M : ℕ, (∀ A B : Finset ℕ, IsSubsetUpTo' A N → IsSubsetUpTo' B N →
      HasDistinctProducts' A B → A.card * B.card ≤ M) ∧
    (∃ A B : Finset ℕ, IsSubsetUpTo' A N ∧ IsSubsetUpTo' B N ∧
      HasDistinctProducts' A B ∧ A.card * B.card = M)

/-- The maximum product size for parameter N. -/
noncomputable def maxProd (N : ℕ) (hN : 2 ≤ N) : ℕ :=
  (maxProd_exists N hN).choose

theorem maxProd_is_upper (N : ℕ) (hN : 2 ≤ N) (A B : Finset ℕ)
    (hA : IsSubsetUpTo' A N) (hB : IsSubsetUpTo' B N)
    (hd : HasDistinctProducts' A B) : A.card * B.card ≤ maxProd N hN :=
  (maxProd_exists N hN).choose_spec.1 A B hA hB hd

theorem maxProd_is_achieved (N : ℕ) (hN : 2 ≤ N) :
    ∃ A B : Finset ℕ, IsSubsetUpTo' A N ∧ IsSubsetUpTo' B N ∧
      HasDistinctProducts' A B ∧ A.card * B.card = maxProd N hN :=
  (maxProd_exists N hN).choose_spec.2

-- ============================================================================
-- § 3. Bounds on maxProd
-- ============================================================================

/-- **Szemerédi bound (axiom)**: maxProd(N) ≤ C·N²/log N for some constant C. -/
axiom szemeredi_upper : ∃ C : ℝ, 0 < C ∧
  ∀ N : ℕ, (hN : 2 ≤ N) → (maxProd N hN : ℝ) ≤ C * (N : ℝ)^2 / Real.log (N : ℝ)

/-- **Optimal example bound (axiom)**: maxProd(N) ≥ c·N²/log N for some c > 0. -/
axiom optimal_lower : ∃ c : ℝ, 0 < c ∧
  ∀ N : ℕ, (hN : 2 ≤ N) → c * (N : ℝ)^2 / Real.log (N : ℝ) ≤ (maxProd N hN : ℝ)

-- ============================================================================
-- § 4. The Product Ratio Sequence
-- ============================================================================

/-- The normalized product ratio: maxProd(N) · log(N) / N².
    This is the quantity whose limit (if it exists) we study. -/
noncomputable def productRatio' (N : ℕ) (hN : 2 ≤ N) : ℝ :=
  (maxProd N hN : ℝ) * Real.log (N : ℝ) / (N : ℝ)^2

/-- The product ratio is bounded above by the Szemerédi constant. -/
theorem productRatio_bounded_above :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, (hN : 2 ≤ N) → productRatio' N hN ≤ C := by
  obtain ⟨C, hC, hbound⟩ := szemeredi_upper
  refine ⟨C, hC, fun N hN => ?_⟩
  unfold productRatio'
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hN2_pos : (0 : ℝ) < (N : ℝ)^2 := by positivity
  rw [div_le_iff hN2_pos]
  calc (maxProd N hN : ℝ) * Real.log ↑N
      = Real.log ↑N * (maxProd N hN : ℝ) := by ring
    _ ≤ Real.log ↑N * (C * ↑N ^ 2 / Real.log ↑N) := by
        exact mul_le_mul_of_nonneg_left (hbound N hN) hlog_pos.le
    _ = C * ↑N ^ 2 := by field_simp

/-- The product ratio is bounded below by the optimal constant. -/
theorem productRatio_bounded_below :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, (hN : 2 ≤ N) → c ≤ productRatio' N hN := by
  obtain ⟨c, hc, hbound⟩ := optimal_lower
  refine ⟨c, hc, fun N hN => ?_⟩
  unfold productRatio'
  have hlog_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hN2_pos : (0 : ℝ) < (N : ℝ)^2 := by positivity
  rw [le_div_iff hN2_pos]
  calc c * ↑N ^ 2
      = Real.log ↑N * (c * ↑N ^ 2 / Real.log ↑N) := by field_simp
    _ ≤ Real.log ↑N * (maxProd N hN : ℝ) := by
        exact mul_le_mul_of_nonneg_left (hbound N hN) hlog_pos.le
    _ = (maxProd N hN : ℝ) * Real.log ↑N := by ring

-- ============================================================================
-- § 5. The Limit Question
-- ============================================================================

/-- The main open question: does lim productRatio'(N) exist? -/
def LimitExists' : Prop :=
  ∃ L : ℝ, ∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ, (hN : 2 ≤ N) → N₀ ≤ N →
    |productRatio' N hN - L| < ε

/-- If the limit exists, it lies in [c, C]. -/
theorem limit_in_sandwich :
    LimitExists' →
    ∃ L : ℝ,
      (∀ ε > 0, ∃ N₀ : ℕ, ∀ N : ℕ, (hN : 2 ≤ N) → N₀ ≤ N →
        |productRatio' N hN - L| < ε) ∧
      (∃ c : ℝ, 0 < c ∧ c ≤ L) ∧
      (∃ C : ℝ, 0 < C ∧ L ≤ C) := by
  intro ⟨L, hL⟩
  refine ⟨L, hL, ?_, ?_⟩
  · obtain ⟨c, hc_pos, hc_bound⟩ := productRatio_bounded_below
    refine ⟨c, hc_pos, ?_⟩
    by_contra h
    push_neg at h
    have hε : 0 < c - L := by linarith
    obtain ⟨N₀, hN₀⟩ := hL (c - L) hε
    have hN₀_bound := hN₀ (max N₀ 2) (by omega) (by omega)
    have hc_at_N₀ := hc_bound (max N₀ 2) (by omega)
    rw [abs_lt] at hN₀_bound
    linarith
  · obtain ⟨C, hC_pos, hC_bound⟩ := productRatio_bounded_above
    refine ⟨C, hC_pos, ?_⟩
    by_contra h
    push_neg at h
    have hε : 0 < L - C := by linarith
    obtain ⟨N₀, hN₀⟩ := hL (L - C) hε
    have hN₀_bound := hN₀ (max N₀ 2) (by omega) (by omega)
    have hC_at_N₀ := hC_bound (max N₀ 2) (by omega)
    rw [abs_lt] at hN₀_bound
    linarith

-- ============================================================================
-- § 6. Structural Analysis
-- ============================================================================

/-- The product ratio is nonneg. -/
theorem productRatio_nonneg (N : ℕ) (hN : 2 ≤ N) :
    0 ≤ productRatio' N hN := by
  unfold productRatio'
  apply div_nonneg
  · apply mul_nonneg
    · exact Nat.cast_nonneg
    · exact (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).le
  · positivity

/-- Cardinality bound: if A ⊆ {1,...,N} then |A| ≤ N. -/
theorem card_le_of_subset_upto (A : Finset ℕ) (N : ℕ) (hA : IsSubsetUpTo' A N) :
    A.card ≤ N := by
  calc A.card ≤ (Finset.Icc 1 N).card := by
        apply Finset.card_le_card
        intro a ha
        exact Finset.mem_Icc.mpr (hA a ha)
    _ = N := by simp [Finset.card_Icc]

/-- maxProd(N) ≤ N² (trivial bound). -/
theorem maxProd_le_sq (N : ℕ) (hN : 2 ≤ N) :
    maxProd N hN ≤ N^2 := by
  obtain ⟨A, B, hA, hB, _, heq⟩ := maxProd_is_achieved N hN
  rw [← heq]
  calc A.card * B.card
      ≤ N * N := Nat.mul_le_mul (card_le_of_subset_upto A N hA)
                                  (card_le_of_subset_upto B N hB)
    _ = N^2 := by ring

/-- Full sandwich: positive constants c ≤ C bracket all ratios. -/
theorem productRatio_sandwich :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ c ≤ C ∧
      ∀ N : ℕ, (hN : 2 ≤ N) →
        c ≤ productRatio' N hN ∧ productRatio' N hN ≤ C := by
  obtain ⟨c, hc, hc_bound⟩ := productRatio_bounded_below
  obtain ⟨C, hC, hC_bound⟩ := productRatio_bounded_above
  refine ⟨c, C, hc, hC, ?_, fun N hN => ⟨hc_bound N hN, hC_bound N hN⟩⟩
  have h2 := hc_bound 2 (by omega)
  have h2' := hC_bound 2 (by omega)
  linarith

-- ============================================================================
-- Summary
-- ============================================================================

#check @maxProd_is_upper
#check @maxProd_is_achieved
#check @productRatio_bounded_above
#check @productRatio_bounded_below
#check @limit_in_sandwich
#check @productRatio_nonneg
#check @card_le_of_subset_upto
#check @maxProd_le_sq
#check @productRatio_sandwich
