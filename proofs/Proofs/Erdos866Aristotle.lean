/-
  Aristotle targets for Erdős Problem #866
  Routine supporting lemmas for automated proof search.
  See Erdos866Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (monotonicity, cardinality, bounds, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)

  Targets:
  1. upperExponent_increasing: geometric sequence monotonicity
  2. oddNumbers_card: counting odd numbers in {1,...,2N}
  3. oddNumbers_no_triple: parity pigeonhole argument
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Finset Real

namespace Erdos866

/-- The interval {1, 2, ..., 2N}. -/
def Interval (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * N + 1)).filter (fun n => n ≥ 1)

/-- A set A has all pairwise sums of b₁,...,b_k if for all i < j,
    b_i + b_j ∈ A. -/
def HasAllPairwiseSums (A : Finset ℕ) (b : Fin k → ℤ) : Prop :=
  ∀ i j : Fin k, i < j → (b i + b j).toNat ∈ A

/-- The set of odd numbers in {1,...,2N}. -/
def oddNumbers (N : ℕ) : Finset ℕ :=
  (Interval N).filter (fun n => n % 2 = 1)

/-- The exponent 1 - 2^{-k} in the upper bound. -/
noncomputable def upperExponent (k : ℕ) : ℝ :=
  1 - (2 : ℝ)⁻¹ ^ k

-- Routine lemma: geometric sequence is strictly decreasing,
-- so 1 - (1/2)^k < 1 - (1/2)^(k+1)
theorem upperExponent_increasing (k : ℕ) (hk : k ≥ 1) :
    upperExponent k < upperExponent (k + 1) := by
  simp only [upperExponent, sub_lt_sub_iff_left]
  exact pow_lt_pow_right (by norm_num : (2:ℝ)⁻¹ < 1) (by omega)

-- Routine lemma: the odd numbers in {1,...,2N} have cardinality N
theorem oddNumbers_card (N : ℕ) : (oddNumbers N).card = N := by
  have : oddNumbers N = (Finset.range N).image (fun k => 2 * k + 1) := by
    ext n
    simp only [oddNumbers, Interval, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · intro ⟨⟨hlt, hge⟩, hodd⟩
      exact ⟨n / 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨by omega, by omega⟩, by omega⟩
  rw [this, Finset.card_image_of_injective _ (by intro a b h; omega), Finset.card_range]

-- Routine lemma: parity pigeonhole — among any 3 integers,
-- two share parity, so their sum is even and not in oddNumbers
theorem oddNumbers_no_triple (N : ℕ) :
    ¬∃ b : Fin 3 → ℤ, HasAllPairwiseSums (oddNumbers N) b := by
  intro ⟨b, hb⟩
  have h01 := hb 0 1 (by omega)
  have h02 := hb 0 2 (by omega)
  have h12 := hb 1 2 (by omega)
  simp only [oddNumbers, Interval, Finset.mem_filter, Finset.mem_range] at h01 h02 h12
  obtain ⟨⟨_, _⟩, _⟩ := h01
  obtain ⟨⟨_, _⟩, _⟩ := h02
  obtain ⟨⟨_, _⟩, _⟩ := h12
  omega

end Erdos866
