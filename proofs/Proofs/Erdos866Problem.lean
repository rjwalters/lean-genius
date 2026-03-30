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
Unfold upperExponent, then use sub_lt_sub_iff_left to reduce to showing (2⁻¹)^(k+1) < (2⁻¹)^k. Use pow_lt_pow_of_lt_one or pow_lt_pow_right with 0 < 2⁻¹ < 1 and k+1 > k (from hk ≥ 1).
-/
theorem upperExponent_increasing (k : ℕ) (hk : k ≥ 1) :
    upperExponent k < upperExponent (k + 1) := by
      exact sub_lt_sub_left ( pow_lt_pow_right_of_lt_one₀ ( by norm_num ) ( by norm_num ) ( by linarith ) ) _

/-
PROBLEM
Routine lemma: the odd numbers in {1,...,2N} have cardinality N

PROVIDED SOLUTION
Show oddNumbers N = (Finset.range N).image (fun k => 2 * k + 1) by ext and omega. Then use card_image_of_injective (injectivity by omega) and card_range.
-/
theorem oddNumbers_card (N : ℕ) : (oddNumbers N).card = N := by
  unfold oddNumbers;
  unfold Interval;
  rw [ Finset.card_eq_of_bijective ];
  use fun i hi => 2 * i + 1;
  · exact fun n hn => ⟨ n / 2, by linarith [ Nat.mod_add_div n 2, Finset.mem_filter.mp hn, Finset.mem_filter.mp ( Finset.mem_filter.mp hn |>.1 ), Finset.mem_range.mp ( Finset.mem_filter.mp ( Finset.mem_filter.mp hn |>.1 ) |>.1 ) ], by linarith [ Nat.mod_add_div n 2, Finset.mem_filter.mp hn, Finset.mem_filter.mp ( Finset.mem_filter.mp hn |>.1 ) ] ⟩;
  · grind;
  · aesop

/-
PROBLEM
Routine lemma: parity pigeonhole — among any 3 integers,
two share parity, so their sum is even and not in oddNumbers

PROVIDED SOLUTION
Assume ⟨b, hb⟩. Extract h01, h02, h12 from hb for pairs (0,1), (0,2), (1,2). Simp oddNumbers/Interval membership to get that (b i + b j).toNat is odd and in range. Among b 0, b 1, b 2, by pigeonhole two have the same parity mod 2, so their sum is even, contradicting the oddness requirement. Use omega to derive contradiction after unfolding membership.
-/
theorem oddNumbers_no_triple (N : ℕ) :
    ¬∃ b : Fin 3 → ℤ, HasAllPairwiseSums (oddNumbers N) b := by
      rintro ⟨ b, hb ⟩;
      -- By definition of $oddNumbers$, we know that for any $i < j$, $(b i + b j).toNat$ is odd.
      have h_odd : ∀ i j : Fin 3, i < j → (b i + b j).toNat % 2 = 1 := by
        intro i j hij; have := hb i j hij; unfold oddNumbers at this; aesop;
      simp_all +decide [ Fin.forall_fin_succ ];
      grind +ring

end Erdos866