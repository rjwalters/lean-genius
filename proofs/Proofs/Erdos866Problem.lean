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

-- Routine lemma: geometric sequence is strictly decreasing,
-- so 1 - (1/2)^k < 1 - (1/2)^(k+1)
theorem upperExponent_increasing (k : ℕ) (hk : k ≥ 1) :
    upperExponent k < upperExponent (k + 1) := by
  simp only [upperExponent, sub_lt_sub_iff_left]
  exact pow_lt_pow_right_of_lt_one₀ (by positivity) (by norm_num) (by omega)

/-
PROBLEM
Routine lemma: the odd numbers in {1,...,2N} have cardinality N

PROVIDED SOLUTION
Show oddNumbers N = (Finset.range N).image (fun k => 2 * k + 1), then use card_image_of_injective and card_range. The bijection: for n odd in {1,...,2N}, map n to n/2; conversely k maps to 2k+1.
-/
theorem oddNumbers_card (N : ℕ) : (oddNumbers N).card = N := by
  unfold oddNumbers Interval; norm_num [ Finset.card_image_of_injective, Function.Injective, Nat.cast_add, Nat.cast_one ] ;
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => 2 * i + 1;
  · exact fun a ha => ⟨ a / 2, by norm_num at *; omega, by linarith [ Nat.mod_add_div a 2, ( Finset.mem_filter.mp ha ) |>.2 ] ⟩;
  · grind +ring;
  · aesop

/-
PROBLEM
Routine lemma: parity pigeonhole — among any 3 integers,
two share parity, so their sum is even and not in oddNumbers

PROVIDED SOLUTION
Unfold HasAllPairwiseSums, get that b0+b1, b0+b2, b1+b2 are all in oddNumbers N, hence their toNat values are odd. But among b0, b1, b2 (integers), by pigeonhole at least two have the same parity, so their sum is even. Use omega after extracting the membership/oddness conditions from all three pairs.
-/
theorem oddNumbers_no_triple (N : ℕ) :
    ¬∃ b : Fin 3 → ℤ, HasAllPairwiseSums (oddNumbers N) b := by
  by_contra! h_contra;
  obtain ⟨ b, hb ⟩ := h_contra;
  -- Since $b_0 + b_1$, $b_0 + b_2$, and $b_1 + b_2$ are all in $oddNumbers N$, their toNat values are odd.
  have h_odd_sums : ∀ i j : Fin 3, i < j → (b i + b j).toNat % 2 = 1 := by
    intro i j hij; have := hb i j hij; unfold oddNumbers at this; aesop;
  simp_all +decide [ Fin.forall_fin_succ ];
  grind +ring

end Erdos866