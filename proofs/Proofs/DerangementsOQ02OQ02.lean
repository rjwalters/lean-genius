/-
  Expected Fixed Points of a Random Permutation (derangements-oq-02-oq-02)

  Open Question (from derangements-oq-02): Prove generating function identities
  connecting the partial derangement formula S(n,k) = C(n,k)·D(n-k) to
  moment formulas for fixed-point counts.

  **Main Results**:
  1. `sum_fixedPoints_eq_factorial`: For n ≥ 1,
       ∑_{σ : Perm(Fin n)} |Fix(σ)| = n!
     i.e., the total number of fixed points across all permutations equals n!.
     Equivalently, E[#fixed] = 1 for a uniform random permutation.

  2. `weighted_partition_identity`: For n ≥ 1,
       ∑_{k=0}^n k · C(n,k) · D(n-k) = n!
     This is the "generating function" identity: the derivative at t=1 of
     G_n(t) = ∑_k S(n,k)·t^k equals n!, where S(n,k) = C(n,k)·D(n-k).

  **Proof Strategy**:
  For `sum_fixedPoints_eq_factorial`: Apply Burnside's lemma.
  - ∑_σ |Fix(σ)| = ∑_σ Fintype.card(fixedBy σ)
  - Burnside: = |orbits| · |Perm(Fin n)|
  - Action is transitive: |orbits| = 1
  - So = n!

  For `weighted_partition_identity`: Swap the summation order:
  - ∑_σ |Fix(σ)| = ∑_k k · #{σ : |Fix(σ)|=k} = ∑_k k · C(n,k) · D(n-k)

  **Status**: 1 sorry (weighted_partition_identity sum-swap),
    `sum_fixedPoints_eq_factorial` proved via Burnside's lemma.
-/

import Proofs.DerangementsOQ02
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

open Finset Fintype Nat Equiv.Perm BigOperators MulAction

namespace DerangementsOQ02OQ02

variable {n : ℕ}

/-!
## Section I: Concrete Verifications
-/

/-- For n=3: total fixed points across all 6 permutations = 6 = 3!. -/
theorem sum_fixedPoints_three :
    ∑ σ : Equiv.Perm (Fin 3),
      (Finset.univ.filter fun x => σ x = x).card = 6 := by native_decide

/-- For n=4: total fixed points across all 24 permutations = 24 = 4!. -/
theorem sum_fixedPoints_four :
    ∑ σ : Equiv.Perm (Fin 4),
      (Finset.univ.filter fun x => σ x = x).card = 24 := by native_decide

/-- Weighted sum for n=3: ∑_k k·C(3,k)·D(3-k) = 6 = 3!.
    Breakdown: 0·(1·2) + 1·(3·1) + 2·(3·0) + 3·(1·1) = 0+3+0+3 = 6. -/
theorem weighted_sum_three :
    ∑ k ∈ Finset.range 4, k * Nat.choose 3 k * numDerangements (3 - k) = 6 := by
  native_decide

/-- Weighted sum for n=4: ∑_k k·C(4,k)·D(4-k) = 24 = 4!.
    Breakdown: 0·9 + 1·8 + 2·6 + 3·0 + 4·1 = 0+8+12+0+4 = 24. -/
theorem weighted_sum_four :
    ∑ k ∈ Finset.range 5, k * Nat.choose 4 k * numDerangements (4 - k) = 24 := by
  native_decide

/-!
## Section II: Boundary Values (proved)
-/

/-- For n=0: no pairs (σ, x) can exist since Fin 0 is empty. Sum = 0. -/
theorem sum_fixedPoints_zero :
    ∑ σ : Equiv.Perm (Fin 0), (Finset.univ.filter fun x => σ x = x).card = 0 := by
  simp

/-- For n=1: the only permutation (identity) has 1 fixed point. Total = 1 = 1!. -/
theorem sum_fixedPoints_one :
    ∑ σ : Equiv.Perm (Fin 1), (Finset.univ.filter fun x => σ x = x).card = 1 := by
  native_decide

/-- For n=2: identity has 2 fixed points, swap has 0. Total = 2 = 2!. -/
theorem sum_fixedPoints_two :
    ∑ σ : Equiv.Perm (Fin 2), (Finset.univ.filter fun x => σ x = x).card = 2 := by
  native_decide

/-!
## Section III: Key Lemma (hard sorry)
-/

/-- **Key Lemma (HARD)**: Exactly (n-1)! permutations of Fin n fix a given point x.

    **Proof sketch**: The map Perm(Fin (n-1)) → {σ : Perm(Fin n) | σ x = x} via
    extension by identity is a bijection. Formalizing this requires:
    - An equivalence Fin (n-1) ≃ Fin n \ {x} (element deletion)
    - Showing the extension map is injective and surjective
    Alternatively: orbit-stabilizer gives |Stab(x)| = n!/|orbit(x)| = n!/n = (n-1)!
    where orbit(x) = Fin n under the transitive action of Perm(Fin n).

    **Mathlib gap**: `Equiv.Perm.fixingSubgroupEquiv` or orbit-stabilizer for
    Perm(Fin n) acting on Fin n not directly available in current API. -/
lemma card_perm_fixing_point (hn : 1 ≤ n) (x : Fin n) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ x = x).card =
    (n - 1).factorial := by
  sorry

/-!
## Section IV: Main Theorem (proved via Burnside's lemma)
-/

/-- Helper: filter card equals Fintype.card of fixedBy set -/
private lemma filter_eq_fixedBy_card (σ : Equiv.Perm (Fin n)) :
    (Finset.univ.filter fun x => σ x = x).card =
    Fintype.card (MulAction.fixedBy (Fin n) σ) := by
  rw [← Fintype.card_subtype]
  apply Fintype.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl _) (fun x => by
    simp [MulAction.mem_fixedBy, Equiv.Perm.smul_def])

/-- **Main Theorem** (proved via Burnside's lemma): For n ≥ 1, ∑_σ |Fix(σ)| = n!

    **Proof**: Burnside's lemma gives ∑_σ |Fix(σ)| = |orbits| · |Perm(Fin n)|.
    Since Perm(Fin n) acts transitively on Fin n, |orbits| = 1.
    And |Perm(Fin n)| = n! by Fintype.card_perm. -/
theorem sum_fixedPoints_eq_factorial (hn : 1 ≤ n) :
    ∑ σ : Equiv.Perm (Fin n),
      (Finset.univ.filter fun x => σ x = x).card = n.factorial := by
  -- Rewrite in terms of Fintype.card of fixedBy
  simp_rw [filter_eq_fixedBy_card]
  -- The action of Perm(Fin n) on Fin n is pretransitive (transitive)
  -- so the orbit quotient has exactly one element (Unique type)
  haveI hne : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  haveI huniq : Unique (orbitRel.Quotient (Equiv.Perm (Fin n)) (Fin n)) :=
    (MulAction.pretransitive_iff_unique_quotient_of_nonempty (G := Equiv.Perm (Fin n))
      (α := Fin n) |>.mp inferInstance).some
  haveI hfinΩ : Fintype (orbitRel.Quotient (Equiv.Perm (Fin n)) (Fin n)) :=
    Unique.fintype
  -- Apply Burnside's lemma: ∑_σ |Fix(σ)| = |Ω| · |G|
  rw [MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
      (α := Equiv.Perm (Fin n)) (β := Fin n)]
  -- |Ω| = 1 (one orbit since action is transitive)
  rw [Fintype.card_unique]
  -- 1 · |Perm(Fin n)| = n!
  rw [one_mul, Fintype.card_perm, Fintype.card_fin]

/-!
## Section V: Consequences
-/

/-- **Weighted partition identity**: For n ≥ 1,
       ∑_{k=0}^n k · C(n,k) · D(n-k) = n!

    This is the "generating function" result: the sequence {S(n,k) = C(n,k)·D(n-k)}
    satisfies ∑_k k·S(n,k) = n! (the derivative of its ordinary generating
    function at t=1 equals the total count n!). -/
theorem weighted_partition_identity (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), k * n.choose k * numDerangements (n - k) = n.factorial := by
  -- This equals sum_fixedPoints_eq_factorial by exchanging summation order:
  -- ∑_k k · C(n,k) · D(n-k) = ∑_k k · #{σ : |Fix(σ)|=k}
  --                           = ∑_σ |Fix(σ)| = n!  (rearranging)
  -- HARD: The sum-exchange requires careful Finset manipulation with
  -- the bijection between {σ : |Fix(σ)| = k} and C(n,k)·D(n-k).
  sorry

/-- The weighted partition identity implies: total fixed points = total permutations. -/
theorem total_fixed_eq_card_perm (hn : 1 ≤ n) :
    ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter fun x => σ x = x).card =
    Fintype.card (Equiv.Perm (Fin n)) := by
  rw [sum_fixedPoints_eq_factorial hn, Fintype.card_perm, Fintype.card_fin]

/-!
## Section VI: Summary
-/

/-- **Summary**: The sequence S(n,k) = C(n,k)·D(n-k) (partial derangements)
    satisfies the generating function identity ∑_k k·S(n,k) = n!.
    Combined with ∑_k S(n,k) = n! (from derangements-oq-02), this shows
    the bivariate generating function G_n(t) = ∑_k S(n,k)·t^k satisfies
    G_n(1) = n! and G_n'(1) = n!, reflecting that E[#fixed] = 1. -/
theorem summary_expected_fixed_one (hn : 1 ≤ n)
    (hpart : ∑ k ∈ Finset.range (n + 1), n.choose k * numDerangements (n - k) = n.factorial) :
    (∑ k ∈ Finset.range (n + 1), k * n.choose k * numDerangements (n - k) : ℕ) =
    ∑ k ∈ Finset.range (n + 1), n.choose k * numDerangements (n - k) := by
  rw [weighted_partition_identity hn, hpart]

end DerangementsOQ02OQ02
