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
Unfold upperExponent. We need 1 - (2⁻¹)^k < 1 - (2⁻¹)^(k+1). This is equivalent to (2⁻¹)^(k+1) < (2⁻¹)^k. Since 0 < 2⁻¹ < 1 and k+1 > k ≥ 1, use pow_lt_pow_of_lt_one or similar.
-/
theorem upperExponent_increasing (k : ℕ) (hk : k ≥ 1) :
    upperExponent k < upperExponent (k + 1) := by
      unfold upperExponent; norm_num [ pow_succ ] ;

/-
PROBLEM
Routine lemma: the odd numbers in {1,...,2N} have cardinality N

PROVIDED SOLUTION
Unfold oddNumbers and Interval. We need to count elements n in Finset.range(2*N+1) with n ≥ 1 and n % 2 = 1. These are {1, 3, 5, ..., 2N-1}, which has N elements. Try using decide for small cases or establishing a bijection with Finset.range N. One approach: show this equals (Finset.range (2*N+1)).filter (fun n => n % 2 = 1) minus {0} but 0 is even so it's the same. The odd numbers in {0,...,2N} are {1,3,...,2N-1} which has N elements. Use Finset.card_filter or Nat.count_odd or similar combinatorial lemmas.
-/
theorem oddNumbers_card (N : ℕ) : (oddNumbers N).card = N := by
  rw [ show oddNumbers N = Finset.image ( fun k => 2 * k + 1 ) ( Finset.range N ) from ?_ ];
  · rw [ Finset.card_image_of_injective ] <;> aesop_cat;
  · ext n
    simp [oddNumbers, Interval];
    exact ⟨ fun h => ⟨ n / 2, by linarith [ Nat.mod_add_div n 2 ], by linarith [ Nat.mod_add_div n 2 ] ⟩, by rintro ⟨ a, ha, rfl ⟩ ; exact ⟨ ⟨ by linarith, by linarith ⟩, by norm_num [ Nat.add_mod ] ⟩ ⟩

/-
PROBLEM
Routine lemma: parity pigeonhole — among any 3 integers,
two share parity, so their sum is even and not in oddNumbers

PROVIDED SOLUTION
Assume for contradiction there exist b : Fin 3 → ℤ with HasAllPairwiseSums (oddNumbers N) b. By the pigeonhole principle on parity (Fin 3 → ZMod 2), among b 0, b 1, b 2, at least two have the same parity mod 2. Say b i and b j (i < j) have the same parity. Then b i + b j is even, meaning (b i + b j) % 2 = 0. But HasAllPairwiseSums says (b i + b j).toNat ∈ oddNumbers N, which by definition means (b i + b j).toNat % 2 = 1 (odd). We need to connect these: if b i + b j is even as an integer, then either it's negative (toNat = 0, which is even, not odd) or it's a non-negative even number (toNat is even, not odd). Either way contradiction. Key: use Int.even_iff or similar to connect integer parity to Nat parity via toNat.
-/
theorem oddNumbers_no_triple (N : ℕ) :
    ¬∃ b : Fin 3 → ℤ, HasAllPairwiseSums (oddNumbers N) b := by
      -- Assume for contradiction that there exists a set $b : Fin 3 → ℤ$ such that all pairwise sums are oddNumbers.
      by_contra h
      obtain ⟨b, hb⟩ := h

      -- By the pigeonhole principle, among $b 0$, $b 1$, and $b 2$, at least two have the same parity.
      have h_parity : ∃ i j, i < j ∧ (b i) % 2 = (b j) % 2 := by
        by_contra! h; simp_all +decide [ Fin.forall_fin_succ ] ; omega;
      obtain ⟨ i, j, hij, h ⟩ := h_parity; have := hb i j hij; simp_all +decide [ Finset.mem_filter, oddNumbers ] ;
      grind +ring

end Erdos866