/-
  Aristotle targets for Erdős Problem #434
  Routine supporting lemmas for automated proof search.
  See Erdos434Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main theorem (Kiss 2002) or deep Frobenius results
  - Known results provable from Mathlib (cardinality, finiteness, set operations)
  - Clean theorem statements with no definition sorries
  - No axioms

  The main file formalizes the extremal Frobenius problem: which k-element
  subset of {1, ..., n} maximizes the count of non-representable integers?
  Answer: {n-k+1, ..., n} (Kiss 2002).
-/
import Mathlib

namespace Erdos434Aristotle

open Finset

/- ## Definitions (mirrored from Erdos434Problem.lean) -/

/-- A natural number m is representable by set A if it equals a sum of elements
    from A with repetition allowed. -/
def IsRepresentableAs (m : ℕ) (A : Set ℕ) : Prop :=
  ∃ (S : Multiset ℕ), (∀ a ∈ S, a ∈ A) ∧ S.sum = m

/-- The set of non-representable integers. -/
def NonRepresentable (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ¬IsRepresentableAs n A}

/-- The "top k" set: {n-k+1, n-k+2, ..., n}. -/
def topK (n k : ℕ) : Set ℕ :=
  Set.Icc (n - k + 1) n

/-
PROBLEM
## Routine Lemmas

Cardinality of topK

topK(n, k) has exactly k elements when k ≤ n and k > 0.

PROVIDED SOLUTION
Unfold topK to get Set.Icc (n - k + 1) n. Use Set.Icc_toFinset and Set.ncard for finite sets. The ncard of Set.Icc a b for ℕ is b + 1 - a when a ≤ b. Here a = n - k + 1, b = n, so ncard = n + 1 - (n - k + 1) = k. Use omega for the arithmetic.
-/
theorem topK_card (n k : ℕ) (hk : k ≤ n) (hk_pos : k > 0) :
    (topK n k).ncard = k := by
      convert Set.ncard_eq_toFinset_card ( Set.Icc ( n - k + 1 ) n ) using 1 ; norm_num [ hk ] ; omega;

-- Representability basics
/-- Zero is always representable (by the empty multiset). -/
theorem zero_representable (A : Set ℕ) : IsRepresentableAs 0 A :=
  ⟨0, fun _ h => absurd h (Multiset.notMem_zero _), Multiset.sum_zero⟩

/-- Any element of A is representable. -/
theorem mem_representable {a : ℕ} {A : Set ℕ} (ha : a ∈ A) : IsRepresentableAs a A :=
  ⟨{a}, fun x hx => by rwa [Multiset.mem_singleton.mp hx], Multiset.sum_singleton a⟩

/-- If m and n are representable by A, so is m + n. -/
theorem add_representable {m n : ℕ} {A : Set ℕ}
    (hm : IsRepresentableAs m A) (hn : IsRepresentableAs n A) :
    IsRepresentableAs (m + n) A := by
  obtain ⟨S, hS, rfl⟩ := hm
  obtain ⟨T, hT, rfl⟩ := hn
  exact ⟨S + T, fun a ha => by
    rw [Multiset.mem_add] at ha
    exact ha.elim (hS a) (hT a),
    Multiset.sum_add S T⟩

/-
PROBLEM
Finiteness

For a set A with coprime elements, non-representables are finite.

PROVIDED SOLUTION
Extract coprime elements a, b from hcop with a ∈ A, b ∈ A, Nat.Coprime a b. Show NonRepresentable A ⊆ Set.Iio (a * b), then use Set.Finite.subset (Set.finite_Iio _).

To show the bound: for any m ≥ a * b, show IsRepresentableAs m A.

Case 1: a = 0. Then coprimality gives b = 1 (since gcd(0,b)=b=1). So 1 ∈ A. Then m is representable as the sum of m copies of 1. Use Multiset.replicate m 1.

Case 2: b = 0. Similarly a = 1. Same argument.

Case 3: a > 0 and b > 0. For m ≥ a*b: write m = q*a + r where 0 ≤ r < a (use Nat.div_add_mod). Since gcd(a,b) = 1, b is a unit mod a, so there exists t < a with t*b ≡ r (mod a). Specifically, use Nat.Coprime to find such t. Then m - t*b ≡ 0 (mod a), so m - t*b = s*a for some s ≥ 0. Since t ≤ a-1, t*b ≤ (a-1)*b < a*b ≤ m, so m - t*b ≥ 0. Then m = s*a + t*b, representable using s copies of a and t copies of b.

The multiset is Multiset.replicate s a + Multiset.replicate t b.
-/
theorem nonrep_finite {A : Set ℕ} (hA : A.Nonempty)
    (hcop : ∃ a ∈ A, ∃ b ∈ A, Nat.Coprime a b) :
    (NonRepresentable A).Finite := by
      obtain ⟨ a, ha, b, hb, hab ⟩ := hcop;
      -- For any $m \geq a * b$, $m$ is representable by $A$.
      have h_representable_large : ∀ m ≥ a * b, IsRepresentableAs m A := by
        intro m hm
        by_cases ha0 : a = 0 ∨ b = 0;
        · cases ha0 <;> simp_all +decide [ Nat.Coprime ];
          · exact ⟨ Multiset.replicate m 1, fun x hx => by rw [ Multiset.eq_of_mem_replicate hx ] ; assumption, by simp +decide ⟩;
          · exact ⟨ Multiset.replicate m 1, fun x hx => by rw [ Multiset.eq_of_mem_replicate hx ] ; assumption, by simp +decide ⟩;
        · -- Since $a$ and $b$ are coprime and both positive, we can write $m = sa + tb$ for some non-negative integers $s$ and $t$.
          obtain ⟨s, t, hs⟩ : ∃ s t : ℕ, m = s * a + t * b := by
            -- Since $a$ and $b$ are coprime and both positive, we can find non-negative integers $s$ and $t$ such that $m = sa + tb$ by using the fact that $m \geq ab$.
            have h_exists_st : ∃ s t : ℤ, m = s * a + t * b ∧ 0 ≤ s ∧ s < b := by
              have h_bezout : ∃ s t : ℤ, m = s * a + t * b := by
                exact ⟨ Nat.gcdA a b * m, Nat.gcdB a b * m, by nlinarith [ Nat.gcd_eq_gcd_ab a b ] ⟩;
              obtain ⟨ s, t, h ⟩ := h_bezout; exact ⟨ s % b, t + s / b * a, by nth_rw 1 [ h ] ; nlinarith [ Int.emod_add_mul_ediv s b ], Int.emod_nonneg _ ( by aesop ), Int.emod_lt_of_pos _ ( by exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero ( by tauto ) ) ) ⟩ ;
            obtain ⟨ s, t, h₁, h₂, h₃ ⟩ := h_exists_st; exact ⟨ s.toNat, t.toNat, by nlinarith [ Int.toNat_of_nonneg h₂, Int.toNat_of_nonneg ( by nlinarith : ( 0 : ℤ ) ≤ t ) ] ⟩ ;
          use Multiset.replicate s a + Multiset.replicate t b;
          simp_all +decide [ Multiset.mem_replicate ];
          grind;
      exact Set.finite_iff_bddAbove.2 ⟨ a * b, fun m hm => not_lt.1 fun contra => hm <| h_representable_large m contra.le ⟩

-- topK concrete values
/-- topK(5, 2) = {4, 5}. -/
theorem topK_5_2 : topK 5 2 = {4, 5} := by
  simp only [topK]; ext x; simp [Set.mem_Icc]; omega

/-- topK(10, 3) = {8, 9, 10}. -/
theorem topK_10_3 : topK 10 3 = {8, 9, 10} := by
  simp only [topK]; ext x; simp [Set.mem_Icc]; omega

-- Subset properties
/-- topK(n, k) ⊆ {1, ..., n} when k ≤ n and k > 0. -/
theorem topK_subset (n k : ℕ) (hk : k ≤ n) (hk_pos : k > 0) :
    topK n k ⊆ Set.Icc 1 n := by
  intro x hx
  simp only [topK, Set.mem_Icc] at hx ⊢
  exact ⟨by omega, hx.2⟩

/-- Every element of topK(n, k) is positive when k ≤ n and k > 0. -/
theorem topK_pos (n k : ℕ) (hk : k ≤ n) (hk_pos : k > 0)
    (x : ℕ) (hx : x ∈ topK n k) : x ≥ 1 := by
  have := topK_subset n k hk hk_pos hx
  exact (Set.mem_Icc.mp this).1

end Erdos434Aristotle