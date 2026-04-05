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

  **Status**: All proved. 0 sorries, 0 axioms. 11 theorems + 1 lemma.
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
## Section III: Key Lemma (proved via orbit-stabilizer)
-/

/-- **Key Lemma**: Exactly (n-1)! permutations of Fin n fix a given point x.

    **Proof**: Orbit-stabilizer theorem.
    1. Connect filter to stabilizer: {σ | σ x = x} = Stab_G(x) as subgroup of Perm(Fin n).
    2. The orbit of x is all of Fin n: Equiv.swap x y maps x to y for any y.
       So |orbit(x)| = n (pretransitive action).
    3. Orbit-stabilizer: |orbit| · |stab| = |G| gives n · |stab| = n!
    4. Therefore |stab| = (n-1)! by cancellation. -/
lemma card_perm_fixing_point (hn : 1 ≤ n) (x : Fin n) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ x = x).card =
    (n - 1).factorial := by
  -- Step 1: Rewrite filter card as Nat.card of stabilizer subgroup
  -- {σ | σ x = x} = stabilizer Perm(Fin n) x (since σ • x = σ x for Equiv.Perm)
  have hstab_eq : (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => σ x = x).card =
                  Nat.card ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) x) := by
    rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) (fun σ => by
      simp [MulAction.mem_stabilizer_iff, Finset.mem_filter]))
  -- Step 2: Orbit of x = Set.univ (Equiv.swap x y is a perm sending x to y)
  have horbit_univ : MulAction.orbit (Equiv.Perm (Fin n)) x = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true, MulAction.mem_orbit_iff]
    exact ⟨Equiv.swap x y, Equiv.swap_apply_left x y⟩
  -- Step 3: |orbit(x)| = n (since orbit = Fin n via Equiv.Set.univ)
  have hcard_orbit : Nat.card ↥(MulAction.orbit (Equiv.Perm (Fin n)) x) = n := by
    rw [horbit_univ, Nat.card_congr (Equiv.Set.univ _)]
    simp [Nat.card_eq_fintype_card, Fintype.card_fin]
  -- Step 4: Orbit-stabilizer: |orbit| · |stab| = |G| = n!
  -- Uses MulAction.orbitEquivQuotientStabilizer and Subgroup.card_mul_index
  have h_os : Nat.card ↥(MulAction.orbit (Equiv.Perm (Fin n)) x) *
              Nat.card ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) x) =
              Nat.card (Equiv.Perm (Fin n)) := by
    rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (Equiv.Perm (Fin n)) x),
        mul_comm]
    exact Subgroup.card_mul_index (MulAction.stabilizer (Equiv.Perm (Fin n)) x)
  -- Step 5: |G| = n!
  have hG : Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  -- Step 6: Conclude |stab| = (n-1)! by cancellation: n · |stab| = n! = n · (n-1)!
  rw [hcard_orbit, hG] at h_os
  rw [hstab_eq]
  have hn0 : n ≠ 0 := by omega
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < n)
    (h_os.trans (Nat.mul_factorial_pred hn0).symm)

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

-- Proof by double counting:
-- ∑_k k·C(n,k)·D(n-k) = ∑_k k·|A_k| = ∑_k ∑_{A_k} fp = ∑_σ fp = n!
-- where A_k = {σ : fp(σ) = k} and fp(σ) = |Fix(σ)|.
set_option maxHeartbeats 800000 in
/-- **Weighted partition identity**: For n ≥ 1,
       ∑_{k=0}^n k · C(n,k) · D(n-k) = n!

    This is the "generating function" result: the sequence {S(n,k) = C(n,k)·D(n-k)}
    satisfies ∑_k k·S(n,k) = n! (the derivative of its ordinary generating
    function at t=1 equals the total count n!).

    **Proof by double counting**:
    ∑_k k·C(n,k)·D(n-k)
    = ∑_k k·|A_k|                       [card_perms_with_kfixed, A_k = {σ : fp=k}]
    = ∑_k ∑_{σ ∈ A_k} fp(σ)             [k is constant on A_k]
    = ∑_σ fp(σ)                         [Finset.sum_fiberwise_of_maps_to]
    = n!                                [sum_fixedPoints_eq_factorial] -/
theorem weighted_partition_identity (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), k * n.choose k * numDerangements (n - k) = n.factorial := by
  -- Step 1: k·C(n,k)·D(n-k) = ∑_{σ ∈ A_k} fp(σ)
  -- (first use card_perms_with_kfixed, then convert k·|A_k| to a sum over A_k)
  have step1 : ∀ k ∈ Finset.range (n + 1), k * n.choose k * numDerangements (n - k) =
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (Finset.univ.filter fun x => σ x = x).card = k),
        (Finset.univ.filter fun x => σ x = x).card := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [mul_assoc, ← PartialDerangements.card_perms_with_kfixed n k (by omega), mul_comm]
    exact (Finset.sum_const_nat (fun σ hσ => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ; exact hσ)).symm
  -- Step 2: Fiberwise identity ∑_k ∑_{A_k} fp(σ) = ∑_σ fp(σ)
  have step2 : ∑ k ∈ Finset.range (n + 1),
      ∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (Finset.univ.filter fun x => σ x = x).card = k),
      (Finset.univ.filter fun x => σ x = x).card =
      ∑ σ : Equiv.Perm (Fin n), (Finset.univ.filter fun x => σ x = x).card :=
    Finset.sum_fiberwise_of_maps_to
      (g := fun σ : Equiv.Perm (Fin n) => (Finset.univ.filter fun x => σ x = x).card)
      (s := Finset.univ)
      (fun σ _ => Finset.mem_range.mpr (Nat.lt_succ_of_le
        ((Finset.card_le_univ _).trans_eq (Fintype.card_fin n))))
      (fun σ => (Finset.univ.filter fun x => σ x = x).card)
  -- Chain: ∑_k k·C·D = ∑_k ∑_{A_k} fp = ∑_σ fp = n!
  rw [Finset.sum_congr rfl step1, step2]
  exact sum_fixedPoints_eq_factorial hn

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
