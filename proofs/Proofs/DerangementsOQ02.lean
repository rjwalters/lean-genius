/-
  Partial Derangements: Permutations with Exactly k Fixed Points
  Open Question: derangements-oq-02

  Classical Theorem: The number of permutations of Fin n with exactly k fixed points is:

    S(n,k) = C(n,k) · D(n-k)

  where D(m) = numDerangements(m) is the number of derangements of m elements.

  Proof Strategy:
  1. Fixed-point count k ↔ support size n-k (support = non-fixed points)
  2. For each (n-k)-element set S ⊆ Fin n, permutations with support exactly S
     biject with derangements of ↑S:
     - Forward: σ ↦ σ.subtypePerm h (derangement since x ∈ S = support ⟹ σ x ≠ x)
     - Backward: τ ↦ ofSubtype τ (extension by identity; support = S by support_ofSubtype)
  3. There are C(n, n-k) = C(n, k) choices of S
  4. Total = C(n,k) · D(n-k)

  Verified by native_decide: S(3,k) = {2,3,0,1} and S(4,k) = {9,8,6,0,1}

  Key Mathlib API:
  - Equiv.Perm.mem_support : x ∈ σ.support ↔ σ x ≠ x
  - Equiv.Perm.subtypePerm : restrict to invariant subtype
  - Equiv.Perm.ofSubtype : extend by identity
  - Equiv.Perm.support_ofSubtype : support = map of subtype support
  - card_derangements_eq_numDerangements : D(|α|) = Fintype.card (derangements α)
-/

import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic

open Finset Fintype Nat Equiv.Perm

namespace PartialDerangements

variable {n : ℕ}

/-!
## Section I: Fixed Points vs Support
-/

/-- k fixed-point count ↔ support.card = n-k.
    Fixed points = supportᶜ; this follows from card_compl. -/
theorem kFixed_iff_support_card (σ : Equiv.Perm (Fin n)) (k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun x => σ x = x)).card = k ↔ σ.support.card = n - k := by
  have hS : Finset.univ.filter (fun x => σ x = x) = σ.supportᶜ := by
    ext x; simp [Equiv.Perm.mem_support]
  rw [hS, Finset.card_compl, Fintype.card_fin]
  have hle : σ.support.card ≤ n := by
    have := Finset.card_le_univ σ.support; simp [Fintype.card_fin] at this; exact this
  omega

/-- Support invariance: x ∈ support ↔ σ x ∈ support.
    Proof: both are equivalent to σ x ≠ x (by injectivity). -/
theorem support_mem_iff_smul_mem (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    x ∈ σ.support ↔ σ x ∈ σ.support := by
  simp only [Equiv.Perm.mem_support]
  exact ⟨fun h hc => h (σ.injective hc), fun h hc => h (congrArg σ hc)⟩

/-!
## Section II: Bijection Components
-/

/-- Restricting σ (with σ.support = S) to ↑S gives a derangement.
    Every element of S is in the support, hence moved by σ. -/
theorem subtypePerm_of_support_is_derangement
    {σ : Equiv.Perm (Fin n)} {S : Finset (Fin n)} (hS : σ.support = S) :
    σ.subtypePerm (fun x => by rw [← hS]; exact (support_mem_iff_smul_mem σ x).symm) ∈
    derangements {x : Fin n // x ∈ S} := by
  intro ⟨x, hx⟩
  simp only [Equiv.Perm.subtypePerm_apply, ne_eq, Subtype.mk.injEq]
  rw [← hS] at hx
  exact Equiv.Perm.mem_support.mp hx

/-- The support of (ofSubtype τ) equals S when τ : derangements ↑S.
    Key: support_ofSubtype says support = map(subtype embed)(τ.support);
    derangement ⟹ τ.support = univ; map(univ) = S. -/
theorem ofSubtype_derangement_support {S : Finset (Fin n)}
    {τ : Equiv.Perm {x : Fin n // x ∈ S}} (hτ : τ ∈ derangements {x : Fin n // x ∈ S}) :
    (Equiv.Perm.ofSubtype τ).support = S := by
  ext x
  simp only [Equiv.Perm.mem_support]
  constructor
  · intro hne
    by_contra hx
    exact hne (Equiv.Perm.ofSubtype_apply_of_not_mem τ hx)
  · intro hx hfixed
    exact hτ ⟨x, hx⟩ (Subtype.ext ((ofSubtype_apply_of_mem τ hx).symm.trans hfixed))

/-!
## Section III: The Bijection
-/

/-- The bijection {σ | σ.support = S} ≃ derangements ↑S.

    Mathematical proof:
    - Forward: restrict σ to S; derangement since S = support ⟹ every element moves
    - Backward: extend τ by identity outside S; support = S since τ deranges all of ↑S

    The round-trips hold by:
    - left_inv: ofSubtype(subtypePerm σ h) = σ because:
        * On S: ofSubtype applies σ (via subtypePerm)
        * Off S: ofSubtype is identity = σ (σ fixes its complement)
    - right_inv: subtypePerm(ofSubtype τ) h = τ because:
        * (ofSubtype τ) x = τ ⟨x, hx⟩ for x ∈ S

    Relevant Mathlib API: ofSubtype_apply_mem, ofSubtype_apply_not_mem,
    or equivalently: dsimp [Equiv.Perm.ofSubtype] + dif_pos/dif_neg -/
noncomputable def permSupportEqEquiv (S : Finset (Fin n)) :
    {σ : Equiv.Perm (Fin n) | σ.support = S} ≃ derangements {x : Fin n // x ∈ S} where
  toFun := fun ⟨σ, hS⟩ =>
    ⟨σ.subtypePerm (fun x => by rw [← hS]; exact (support_mem_iff_smul_mem σ x).symm),
     subtypePerm_of_support_is_derangement hS⟩
  invFun := fun ⟨τ, hτ⟩ =>
    ⟨Equiv.Perm.ofSubtype τ, ofSubtype_derangement_support hτ⟩
  left_inv := by
    intro ⟨σ, hS⟩
    ext : 1
    -- ofSubtype (subtypePerm σ h) = σ via ofSubtype_subtypePerm
    apply ofSubtype_subtypePerm
    -- h2: ∀ x, σ x ≠ x → x ∈ S (non-fixed points are in support = S)
    intro x hne; rw [← hS]; exact Equiv.Perm.mem_support.mpr hne
  right_inv := by
    intro ⟨τ, hτ⟩
    -- subtypePerm (ofSubtype τ) h = τ  element-wise via ofSubtype_apply_of_mem
    ext : 1; ext ⟨x, hx⟩
    simp

/-- Cardinality of each support class = D(|S|). -/
theorem card_perms_with_support_eq (S : Finset (Fin n)) :
    Fintype.card {σ : Equiv.Perm (Fin n) | σ.support = S} =
    numDerangements S.card := by
  rw [Fintype.card_congr (permSupportEqEquiv S), card_derangements_eq_numDerangements,
      Fintype.card_coe]

/-!
## Section IV: Main Counting Theorem
-/

/-- **Main Theorem**: S(n,k) = C(n,k) · D(n-k).

    The number of permutations of Fin n with exactly k fixed points
    equals C(n,k) · D(n-k).

    Proof outline:
    1. Rewrite: k fixed pts ↔ support.card = n-k
    2. Partition: {σ | sup.card=n-k} = ⊔_{S,|S|=n-k} {σ | sup=S} (disjoint)
    3. Each piece has D(n-k) elements (by permSupportEqEquiv + card_derangements)
    4. C(n,n-k) = C(n,k) choices of S
    5. Total = C(n,k) · D(n-k)

    The biUnion step uses Finset.card_biUnion with Set.PairwiseDisjoint. -/
theorem card_perms_with_kfixed (n k : ℕ) (hk : k ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (Finset.univ.filter (fun x => σ x = x)).card = k)).card =
    n.choose k * numDerangements (n - k) := by
  -- Step 1: rewrite fixed-point count as support size
  rw [show Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
        (Finset.univ.filter (fun x => σ x = x)).card = k) =
      Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.support.card = n - k) from by
    ext σ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact kFixed_iff_support_card σ k hk]
  -- Step 2: decompose as biUnion over (n-k)-element subsets
  rw [show Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.support.card = n - k) =
      (Finset.univ.powersetCard (n - k)).biUnion
        (fun S => Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.support = S)) from by
    ext σ; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
                      Finset.mem_powersetCard]
    exact ⟨fun h => ⟨σ.support, ⟨Finset.subset_univ _, h⟩, rfl⟩,
           fun ⟨S, ⟨_, hc⟩, hs⟩ => hs ▸ hc⟩]
  -- Step 3: count via disjoint union
  rw [Finset.card_biUnion (by
    intro S _ T _ hST
    apply Finset.disjoint_left.mpr
    intro σ hσS hσT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσS hσT
    exact hST (hσS.symm.trans hσT))]
  -- Step 4: each piece has numDerangements (n-k) elements
  rw [Finset.sum_congr rfl (fun S hS => by
    simp only [Finset.mem_powersetCard] at hS
    rw [show (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.support = S)).card =
          Fintype.card {σ : Equiv.Perm (Fin n) | σ.support = S} from by
      rw [Fintype.card_subtype]; simp,
      card_perms_with_support_eq, hS.2])]
  -- Step 5: C(n,n-k) choices × D(n-k) = C(n,k) × D(n-k)
  rw [Finset.sum_const, smul_eq_mul, Finset.card_powersetCard,
      Finset.card_univ, Fintype.card_fin, Nat.choose_symm hk]

/-!
## Section V: Concrete Verifications (native_decide)
-/

-- n=3: C(3,k)·D(3-k) = {1·2, 3·1, 3·0, 1·1} = {2, 3, 0, 1}; sum=6=3!

/-- S(3,0) = 2 = D(3) -/
example : (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) =>
    (Finset.univ.filter fun x => σ x = x).card = 0).card = 2 := by native_decide

/-- S(3,1) = 3 = C(3,1)·D(2) -/
example : (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) =>
    (Finset.univ.filter fun x => σ x = x).card = 1).card = 3 := by native_decide

/-- S(3,2) = 0 = C(3,2)·D(1) -/
example : (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) =>
    (Finset.univ.filter fun x => σ x = x).card = 2).card = 0 := by native_decide

/-- S(3,3) = 1 = C(3,3)·D(0) -/
example : (Finset.univ.filter fun σ : Equiv.Perm (Fin 3) =>
    (Finset.univ.filter fun x => σ x = x).card = 3).card = 1 := by native_decide

-- n=4: C(4,k)·D(4-k) = {1·9, 4·2, 6·1, 4·0, 1·1} = {9, 8, 6, 0, 1}; sum=24=4!

/-- S(4,0) = 9 -/
example : (Finset.univ.filter fun σ : Equiv.Perm (Fin 4) =>
    (Finset.univ.filter fun x => σ x = x).card = 0).card = 9 := by native_decide

/-- S(4,1) = 8 -/
example : (Finset.univ.filter fun σ : Equiv.Perm (Fin 4) =>
    (Finset.univ.filter fun x => σ x = x).card = 1).card = 8 := by native_decide

/-- S(4,2) = 6 -/
example : (Finset.univ.filter fun σ : Equiv.Perm (Fin 4) =>
    (Finset.univ.filter fun x => σ x = x).card = 2).card = 6 := by native_decide

/-- S(4,3) = 0 -/
example : (Finset.univ.filter fun σ : Equiv.Perm (Fin 4) =>
    (Finset.univ.filter fun x => σ x = x).card = 3).card = 0 := by native_decide

/-- S(4,4) = 1 -/
example : (Finset.univ.filter fun σ : Equiv.Perm (Fin 4) =>
    (Finset.univ.filter fun x => σ x = x).card = 4).card = 1 := by native_decide

-- n=5: spot check S(5,2) = C(5,2)·D(3) = 10·2 = 20
/-- S(5,2) = 20 -/
example : (Finset.univ.filter fun σ : Equiv.Perm (Fin 5) =>
    (Finset.univ.filter fun x => σ x = x).card = 2).card = 20 := by native_decide

/-!
## Section VI: Special Cases
-/

/-- S(n,0) = D(n): no fixed points = derangement count -/
theorem permsWithZeroFixed_eq_derangement_count :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (Finset.univ.filter (fun x => σ x = x)).card = 0)).card =
    numDerangements n := by
  -- {σ | 0 fixed pts} = {σ | support.card = n} = {σ | support = univ}
  -- Bijection with derangements(Fin n) via card_derangements_eq_numDerangements
  rw [show (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (Finset.univ.filter (fun x => σ x = x)).card = 0)) =
      Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.support = Finset.univ) from by
    ext σ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [kFixed_iff_support_card σ 0 (Nat.zero_le n), Nat.sub_zero]
    constructor
    · intro h; exact Finset.eq_univ_of_card _ (by rwa [Fintype.card_fin])
    · intro h; rw [h, Finset.card_univ, Fintype.card_fin]]
  rw [show (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ.support = Finset.univ)).card =
      Fintype.card {σ : Equiv.Perm (Fin n) | σ.support = Finset.univ} from by
    rw [Fintype.card_subtype]; simp]
  rw [card_perms_with_support_eq, Finset.card_univ, Fintype.card_fin]

/-- S(n,n) = 1: identity is the unique permutation with all n fixed points -/
theorem permsWithAllFixed_card_eq_one :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (Finset.univ.filter (fun x => σ x = x)).card = n)).card = 1 := by
  convert_to ({1} : Finset (Equiv.Perm (Fin n))).card = 1
  · congr 1
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      have hfull : Finset.univ.filter (fun x => σ x = x) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rwa [Fintype.card_fin])
      ext x
      exact (Finset.mem_filter.mp (hfull ▸ Finset.mem_univ x)).2.symm ▸ rfl
    · intro h; subst h; simp [Fintype.card_fin]
  · exact Finset.card_singleton _

/-- S(n, n-1) = 0 for n ≥ 2: can't have exactly n-1 fixed points (the last is forced fixed) -/
theorem permsWithNMinus1Fixed_eq_zero {n : ℕ} (hn : 2 ≤ n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) =>
      (Finset.univ.filter (fun x => σ x = x)).card = n - 1)).card = 0 := by
  apply Finset.card_eq_zero.mpr
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
  intro hk
  -- If n-1 elements are fixed, the remaining element must also be fixed (injective map on Fin n)
  -- so support.card ≤ 1; but support.card = n - (n-1) = 1 → support = {i} for some i
  -- → σ swaps nothing → σ = id → but id has n fixed points, not n-1. Contradiction.
  have hsupp : σ.support.card = n - (n - 1) := (kFixed_iff_support_card σ (n-1) (Nat.sub_le n 1)).mp hk
  have h1 : n - (n - 1) = 1 := Nat.sub_sub_self (by omega)
  rw [h1] at hsupp
  -- support has exactly 1 element, but Equiv.Perm.card_support_ne_one says this is impossible
  exact absurd hsupp (Equiv.Perm.card_support_ne_one σ)

/-!
## Section VII: Algebraic Identity
-/

/-- ∑_{k=0}^{n} S(n,k) = n! (every permutation is counted exactly once) -/
theorem sum_permsWithKFixed_eq_factorial :
    (∑ k ∈ Finset.range (n + 1), (Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
      (Finset.univ.filter fun x => σ x = x).card = k).card) = n ! := by
  -- Each permutation is counted in exactly one filter class (its fixed-point count)
  -- so the sum equals card of the biUnion = card Finset.univ = n!
  have hcover : (Finset.range (n + 1)).biUnion (fun k => Finset.univ.filter
      (fun σ : Equiv.Perm (Fin n) => (Finset.univ.filter fun x => σ x = x).card = k)) =
      Finset.univ := by
    ext σ
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro _; trivial
    · intro _
      refine ⟨(Finset.univ.filter fun x => σ x = x).card, ?_, rfl⟩
      exact Nat.lt_succ_of_le ((Finset.card_le_univ _).trans (Fintype.card_fin n).le)
  rw [← Finset.card_biUnion (by
    intro k _ k' _ hne
    apply Finset.disjoint_left.mpr
    intro σ hk hk'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk hk'
    exact hne (hk.symm.trans hk')),
    hcover, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-!
## Summary

### Partial Derangement Formula: S(n,k) = C(n,k) · D(n-k)

### Proved (0 sorries in these):
1. `kFixed_iff_support_card` — k fixed points ↔ support.card = n-k
2. `support_mem_iff_smul_mem` — support is σ-invariant
3. `subtypePerm_of_support_is_derangement` — restriction to support is derangement
4. `ofSubtype_derangement_support` — extension has correct support
5. `permSupportEqEquiv` — bijection structure (round trips are sorry)
6. `card_perms_with_support_eq` — cardinality D(|S|)
7. All 11 examples verified by native_decide (n=3,4,5)
8. `permsWithZeroFixed_eq_derangement_count` — S(n,0) = D(n) ✓
9. `permsWithAllFixed_card_eq_one` — S(n,n) = 1 ✓
10. `permsWithNMinus1Fixed_eq_zero` — S(n,n-1) = 0 (uses card_support_ne_one) ✓
11. `sum_permsWithKFixed_eq_factorial` — ∑ S(n,k) = n! ✓

### Proved (0 sorries):
- All theorems fully proved using correct Mathlib 4 API

### Key Insights:
- support_ofSubtype: (ofSubtype τ).support = map(incl)(τ.support)
- derangement ⟹ τ.support = univ ⟹ (ofSubtype τ).support = S
- D(n-1) = 0 (numDerangements 1 = 0) explains S(n,n-1) = 0
-/

end PartialDerangements
