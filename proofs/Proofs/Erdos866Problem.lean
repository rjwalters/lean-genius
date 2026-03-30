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
import Mathlib

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

/-
PROBLEM
Routine lemma: geometric sequence is strictly decreasing,
so 1 - (1/2)^k < 1 - (1/2)^(k+1)

PROVIDED SOLUTION
Unfold upperExponent, then use sub_lt_sub_iff_left to reduce to showing (2:ℝ)⁻¹ ^ (k+1) < (2:ℝ)⁻¹ ^ k. Use pow_lt_pow_of_lt_one or pow_lt_pow_right_of_lt_one with 0 < (2:ℝ)⁻¹ < 1.
-/
theorem upperExponent_increasing (k : ℕ) (hk : k ≥ 1) :
    upperExponent k < upperExponent (k + 1) := by
      exact sub_lt_sub_left ( pow_lt_pow_right_of_lt_one₀ ( by norm_num ) ( by norm_num ) ( Nat.lt_succ_self _ ) ) _

/-
PROBLEM
Routine lemma: the odd numbers in {1,...,2N} have cardinality N

PROVIDED SOLUTION
Show oddNumbers N = (Finset.range N).image (fun k => 2 * k + 1) by ext and omega. Then use card_image_of_injective (injectivity by omega) and card_range.
-/
theorem oddNumbers_card (N : ℕ) : (oddNumbers N).card = N := by
  unfold oddNumbers;
  rw [ show { n ∈ Interval N | n % 2 = 1 } = Finset.image ( fun n => 2 * n + 1 ) ( Finset.range N ) from ?_, Finset.card_image_of_injective ] <;> norm_num [ Function.Injective ];
  ext ( _ | n ) <;> simp +arith +decide [ Interval ];
  exact ⟨ fun h => ⟨ n / 2, by omega, by omega ⟩, fun ⟨ a, ha, ha' ⟩ => ⟨ by omega, by omega ⟩ ⟩

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