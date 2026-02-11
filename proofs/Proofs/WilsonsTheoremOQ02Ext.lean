import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic

/-
# Gauss-Wilson Theorem: Non-Cyclic Product Infrastructure

This file provides the infrastructure to prove the non-cyclic case of the
Gauss-Wilson theorem: when (ZMod n)ˣ is not cyclic, ∏ units = 1.

## Key Results
- `even_card_of_fpf_involution`: FPF involution → even cardinality
- `prod_involution_const`: FPF involution with constant pair product → product = power
- `card_sq_eq_one_ge_three_of_not_cyclic_zmod`: For (ZMod n)ˣ with n ≥ 3,
  ¬cyclic → |{x | x²=1}| ≥ 3 (1 sorry - correctly specialized, NOT the false general version)
- `prod_units_one_of_not_cyclic_ext`: Complete proof using two-involution trick
- `gaussWilson_abstract_ext`: ∏ units = -1 ↔ cyclic

## Proof Strategy (Two-Involution Trick)
Given S = {x ∈ G | x² = 1} with |S| ≥ 3, pick c, d ∈ S \ {1} distinct.
- Involution x ↦ cx: ∏ S = c^(|S|/2)
- Involution x ↦ cdx: ∏ S = (cd)^(|S|/2) = c^(|S|/2) · d^(|S|/2)
- Therefore d^(|S|/2) = 1, and symmetrically c^(|S|/2) = 1
- So ∏ S = c^(|S|/2) = 1
-/

namespace WilsonsTheoremOQ02Ext

open Nat Finset ZMod

-- ============================================================================
-- Section 1: Basic Group Lemmas
-- ============================================================================

private theorem units_val_prod {ι : Type*} {M : Type*} [CommMonoid M]
    (s : Finset ι) (f : ι → Mˣ) :
    (↑(∏ i ∈ s, f i) : M) = ∏ i ∈ s, (↑(f i) : M) :=
  map_prod (Units.coeHom M) f s

/-- In a finite commutative group, c² = 1 and x² = 1 imply (c*x)² = 1. -/
lemma mul_sq_eq_one {G : Type*} [CommGroup G]
    {c x : G} (hc : c ^ 2 = 1) (hx : x ^ 2 = 1) : (c * x) ^ 2 = 1 := by
  rw [mul_pow, hc, hx, one_mul]

-- ============================================================================
-- Section 2: Fixed-Point-Free Involution Infrastructure
-- ============================================================================

/-- A fixed-point-free involution on a Finset gives even cardinality.
    Proof by strong induction: remove a pair {x, σ(x)} and recurse. -/
theorem even_card_of_fpf_involution {α : Type*} [DecidableEq α]
    {S : Finset α} {σ : α → α}
    (hσ_mem : ∀ x ∈ S, σ x ∈ S)
    (hσ_inv : ∀ x ∈ S, σ (σ x) = x)
    (hσ_ne : ∀ x ∈ S, σ x ≠ x) :
    Even S.card := by
  induction S using Finset.strongInduction with
  | ind S ih =>
    by_cases hS : S = ∅
    · subst hS; exact ⟨0, by simp⟩
    · rw [Finset.nonempty_iff_ne_empty] at hS
      obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty hS
      have hσa_ne : σ a ≠ a := hσ_ne a ha
      set T := S \ {a, σ a}
      have hpair_sub : {a, σ a} ⊆ S := by
        intro x hx; simp at hx; rcases hx with rfl | rfl
        · exact ha
        · exact hσ_mem a ha
      have hT_mem : ∀ x ∈ T, σ x ∈ T := by
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        refine ⟨hσ_mem x hx.1, ?_, ?_⟩
        · intro heq; exact hx.2 (Or.inr (by rw [← hσ_inv x hx.1, heq]))
        · intro heq
          have : x = a := by rw [← hσ_inv x hx.1, heq, hσ_inv a ha]
          exact hx.2 (Or.inl this)
      have hT_inv : ∀ x ∈ T, σ (σ x) = x :=
        fun x hx => hσ_inv x (Finset.mem_sdiff.mp hx).1
      have hT_ne : ∀ x ∈ T, σ x ≠ x :=
        fun x hx => hσ_ne x (Finset.mem_sdiff.mp hx).1
      have hT_lt : T ⊂ S :=
        Finset.sdiff_ssubset (by exact ⟨a, ha, Finset.mem_insert_self a _⟩)
      obtain ⟨k, hk⟩ := ih T hT_lt hT_mem hT_inv hT_ne
      have hcard_pair : ({a, σ a} : Finset α).card = 2 :=
        Finset.card_pair hσa_ne.symm
      exact ⟨k + 1, by rw [Finset.card_sdiff hpair_sub, hcard_pair] at hk; omega⟩

/-- Product over a Finset with a constant-product FPF involution.
    If σ is an FPF involution on S with x * σ(x) = c for all x ∈ S,
    then ∏ S = c^(|S|/2). Proof by strong induction, removing pairs. -/
theorem prod_involution_const {G : Type*} [CommGroup G] [DecidableEq G]
    {S : Finset G} {σ : G → G} {c : G}
    (hσ_mem : ∀ x ∈ S, σ x ∈ S)
    (hσ_inv : ∀ x ∈ S, σ (σ x) = x)
    (hσ_ne : ∀ x ∈ S, σ x ≠ x)
    (hσ_prod : ∀ x ∈ S, x * σ x = c) :
    ∏ x ∈ S, x = c ^ (S.card / 2) := by
  induction S using Finset.strongInduction with
  | ind S ih =>
    by_cases hS : S = ∅
    · subst hS; simp
    · rw [Finset.nonempty_iff_ne_empty] at hS
      obtain ⟨a, ha⟩ := Finset.nonempty_of_ne_empty hS
      have hσa_ne : σ a ≠ a := hσ_ne a ha
      set T := S \ {a, σ a}
      have hpair_sub : {a, σ a} ⊆ S := by
        intro x hx; simp at hx; rcases hx with rfl | rfl
        · exact ha
        · exact hσ_mem a ha
      have hcard_pair : ({a, σ a} : Finset G).card = 2 :=
        Finset.card_pair hσa_ne.symm
      have hT_mem : ∀ x ∈ T, σ x ∈ T := by
        intro x hx
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hx ⊢
        refine ⟨hσ_mem x hx.1, ?_, ?_⟩
        · intro heq; exact hx.2 (Or.inr (by rw [← hσ_inv x hx.1, heq]))
        · intro heq
          have : x = a := by rw [← hσ_inv x hx.1, heq, hσ_inv a ha]
          exact hx.2 (Or.inl this)
      have hT_inv : ∀ x ∈ T, σ (σ x) = x :=
        fun x hx => hσ_inv x (Finset.mem_sdiff.mp hx).1
      have hT_ne : ∀ x ∈ T, σ x ≠ x :=
        fun x hx => hσ_ne x (Finset.mem_sdiff.mp hx).1
      have hT_prod : ∀ x ∈ T, x * σ x = c :=
        fun x hx => hσ_prod x (Finset.mem_sdiff.mp hx).1
      have hT_lt : T ⊂ S :=
        Finset.sdiff_ssubset (by exact ⟨a, ha, Finset.mem_insert_self a _⟩)
      have hih := ih T hT_lt hT_mem hT_inv hT_ne hT_prod
      -- ∏ S = ∏ {a, σ a} * ∏ T = c * c^(T.card/2)
      have hsplit : ∏ x ∈ S, x = (∏ x ∈ ({a, σ a} : Finset G), x) * ∏ x ∈ T, x :=
        (Finset.prod_sdiff hpair_sub).symm
      have hprod_pair : ∏ x ∈ ({a, σ a} : Finset G), x = c := by
        rw [Finset.prod_pair hσa_ne.symm]; exact hσ_prod a ha
      rw [hsplit, hprod_pair, hih]
      -- S.card/2 = T.card/2 + 1 (since T has even cardinality)
      have hT_even := even_card_of_fpf_involution hT_mem hT_inv hT_ne
      obtain ⟨k, hk⟩ := hT_even
      rw [show T.card / 2 = k from by omega]
      rw [show S.card / 2 = k + 1 from by
        rw [Finset.card_sdiff hpair_sub, hcard_pair] at hk; omega]
      ring

-- ============================================================================
-- Section 3: Non-Cyclic Group 2-Torsion Bound
-- ============================================================================

/-- **WARNING**: The general statement "¬IsCyclic G → |{x | x² = 1}| ≥ 3" is FALSE
    for arbitrary finite commutative groups. Counterexample: Z/3 × Z/3 is not cyclic
    but has only 1 element with x² = 1 (the identity).

    However, for (ZMod n)ˣ with n ≥ 3, the statement IS true (and in fact |S| ≥ 4).
    This is because:
    - When n ∉ {1,2,4,p^k,2p^k}, by CRT, (ZMod n)ˣ decomposes into ≥ 2 factors
      each contributing an independent element of order 2
    - For n = 2^k with k ≥ 3, (ZMod 2^k)ˣ ≅ Z/2 × Z/2^(k-2) has 4 elements of order ≤ 2

    Verified computationally for n ≤ 300 via gaussWilson_verified_le_300. -/
theorem card_sq_eq_one_ge_three_of_not_cyclic_zmod
    {n : ℕ} (hn : n ≥ 3) [hne : NeZero n] (hncyc : ¬IsCyclic (ZMod n)ˣ) :
    3 ≤ (Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1)).card := by
  by_contra h; push_neg at h
  -- h : |{x ∈ (ZMod n)ˣ | x² = 1}| < 3
  -- Since n ≥ 3, both 1 and -1 are in S and are distinct, so |S| ≥ 2.
  -- We have |S| ≤ 2, so |S| = 2 and S = {1, -1}.
  -- By IsCyclic.card_pow_eq_one_le (converse via isCyclic_of_card_pow_eq_one_le),
  -- and the specific structure of (ZMod n)ˣ, this implies IsCyclic.
  --
  -- Proof path: Use ZMod.isCyclic_units_iff to show that when n ∉ {cyclic forms},
  -- n decomposes via CRT into coprime factors each contributing independent
  -- 2-torsion, giving |S| ≥ 4 — contradicting |S| ≤ 2.
  --
  -- This requires: ZMod.chineseRemainder (ring iso for coprime moduli) +
  -- the induced units isomorphism + 2-torsion product formula.
  sorry

-- ============================================================================
-- Section 4: Involution Product Lemmas (from OQ02 main file)
-- ============================================================================

-- Import-free restatements of lemmas from WilsonsTheoremOQ02

/-- ∏ G = ∏ {x | x² = 1} in any finite commutative group. -/
theorem prod_eq_prod_sq_eq_one (G : Type*) [CommGroup G] [Fintype G] [DecidableEq G] :
    ∏ x : G, x = ∏ x ∈ Finset.univ.filter (fun x : G => x ^ 2 = 1), x := by
  have hsplit : ∏ x : G, x =
      (∏ x ∈ Finset.univ.filter (fun x : G => x ^ 2 = 1), x) *
      (∏ x ∈ Finset.univ.filter (fun x : G => ¬(x ^ 2 = 1)), x) :=
    (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun x : G => x ^ 2 = 1) id).symm
  have hrest : ∏ x ∈ Finset.univ.filter (fun x : G => ¬(x ^ 2 = 1)), x = 1 := by
    apply Finset.prod_involution (fun x _ => x⁻¹)
    · intros a _; exact mul_inv_cancel a
    · intro a ha _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
      intro heq
      exact ha ((sq_eq_one_iff_eq_inv a).mpr heq.symm)
    · intro a ha
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
      rwa [inv_pow, inv_eq_one]
    · intros a _; exact inv_inv a
  rw [hsplit, hrest, mul_one]
  where
    sq_eq_one_iff_eq_inv {G : Type*} [CommGroup G] (x : G) : x ^ 2 = 1 ↔ x = x⁻¹ := by
      rw [sq, mul_eq_one_iff_eq_inv]

-- ============================================================================
-- Section 5: Main Result
-- ============================================================================

/-- **Involution helper**: For c ∈ S = {x | x² = 1} with c ≠ 1, the map x ↦ cx
    is an FPF involution on S with pair product c. -/
private theorem mul_involution_on_sq_eq_one {G : Type*} [CommGroup G] [DecidableEq G]
    {c : G} (hc_sq : c ^ 2 = 1) (hc_ne : c ≠ 1) :
    let S := Finset.univ.filter (fun x : G => x ^ 2 = 1)
    (∀ x ∈ S, c * x ∈ S) ∧
    (∀ x ∈ S, c * (c * x) = x) ∧
    (∀ x ∈ S, c * x ≠ x) ∧
    (∀ x ∈ S, x * (c * x) = c) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- c * x ∈ S when x ∈ S
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact mul_sq_eq_one hc_sq hx
  · -- c * (c * x) = x (involution)
    intro x _; rw [← mul_assoc, ← sq, hc_sq, one_mul]
  · -- c * x ≠ x (fixed-point-free)
    intro x _ h; exact hc_ne (mul_right_cancel h)
  · -- x * (c * x) = c (constant pair product)
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [mul_comm x (c * x), mul_assoc, ← sq, hx, mul_one]

/-- When (ZMod n)ˣ is not cyclic and n ≥ 3, the product of units is 1.

    Proof: Two-involution trick. See module docstring for details. -/
theorem prod_units_one_of_not_cyclic_ext {n : ℕ} (hn : n ≥ 3)
    [hne : NeZero n] (hncyc : ¬ IsCyclic (ZMod n)ˣ) :
    ∏ x : (ZMod n)ˣ, (x : ZMod n) = 1 := by
  suffices hprod : ∏ x : (ZMod n)ˣ, x = 1 by
    rw [show (∏ x : (ZMod n)ˣ, (x : ZMod n)) = (↑(∏ x : (ZMod n)ˣ, x) : ZMod n) from
      (units_val_prod _ _).symm, hprod]
    simp
  -- Step 1: ∏ G = ∏ S where S = {x | x² = 1}
  rw [prod_eq_prod_sq_eq_one]
  set S := Finset.univ.filter (fun x : (ZMod n)ˣ => x ^ 2 = 1)
  -- Step 2: |S| ≥ 3
  have hS_card : 3 ≤ S.card := card_sq_eq_one_ge_three_of_not_cyclic_zmod hn hncyc
  -- S membership gives x² = 1
  have hS_mem_sq : ∀ x ∈ S, x ^ 2 = 1 := fun x hx => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx; exact hx
  -- Step 3: Pick c ∈ S \ {1}
  have hS_sub1_nonempty : (S \ {1}).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hempty
    have : S ⊆ {1} := by
      intro x hx; by_contra hxne
      exact Finset.not_mem_empty x (hempty ▸ Finset.mem_sdiff.mpr ⟨hx, hxne⟩)
    have := Finset.card_le_card this; simp at this; omega
  obtain ⟨c, hc_mem⟩ := hS_sub1_nonempty
  have hc_in_S : c ∈ S := (Finset.mem_sdiff.mp hc_mem).1
  have hc_ne_1 : c ≠ 1 := by intro h; exact (Finset.mem_sdiff.mp hc_mem).2 (by simp [h])
  have hc_sq : c ^ 2 = 1 := hS_mem_sq c hc_in_S
  -- Step 4: Pick d ∈ S \ {1, c}
  have hS_sub2_nonempty : (S \ {1, c}).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]; intro hempty
    have : S ⊆ {1, c} := by
      intro x hx; by_contra hxne
      simp only [Finset.mem_insert, Finset.mem_singleton] at hxne; push_neg at hxne
      exact Finset.not_mem_empty x (hempty ▸ Finset.mem_sdiff.mpr ⟨hx, by
        simp only [Finset.mem_insert, Finset.mem_singleton]; push_neg; exact hxne⟩)
    have := Finset.card_le_card this
    have : ({1, c} : Finset (ZMod n)ˣ).card ≤ 2 := Finset.card_insert_le _ _
    omega
  obtain ⟨d, hd_mem⟩ := hS_sub2_nonempty
  have hd_in_S : d ∈ S := (Finset.mem_sdiff.mp hd_mem).1
  have hd_ne_1 : d ≠ 1 := by
    intro h; exact (Finset.mem_sdiff.mp hd_mem).2 (by simp [h])
  have hd_ne_c : d ≠ c := by
    intro h; exact (Finset.mem_sdiff.mp hd_mem).2 (by simp [h])
  have hd_sq : d ^ 2 = 1 := hS_mem_sq d hd_in_S
  -- cd ≠ 1
  have hcd_sq : (c * d) ^ 2 = 1 := mul_sq_eq_one hc_sq hd_sq
  have hcd_ne_1 : c * d ≠ 1 := by
    intro h
    have : d = c⁻¹ := by rwa [mul_eq_one_iff_eq_inv] at h
    have : d = c := by
      rw [this, inv_eq_of_mul_eq_one_right]; rw [← sq]; exact hc_sq
    exact hd_ne_c this
  -- Step 5: Get involution properties
  obtain ⟨hσc_mem, hσc_inv, hσc_ne, hσc_prod⟩ :=
    mul_involution_on_sq_eq_one hc_sq hc_ne_1
  obtain ⟨hσd_mem, hσd_inv, hσd_ne, hσd_prod⟩ :=
    mul_involution_on_sq_eq_one hd_sq hd_ne_1
  obtain ⟨hσcd_mem, hσcd_inv, hσcd_ne, hσcd_prod⟩ :=
    mul_involution_on_sq_eq_one hcd_sq hcd_ne_1
  -- Step 6: Apply prod_involution_const
  have hP_eq_c : ∏ x ∈ S, x = c ^ (S.card / 2) :=
    prod_involution_const hσc_mem hσc_inv hσc_ne hσc_prod
  have hP_eq_d : ∏ x ∈ S, x = d ^ (S.card / 2) :=
    prod_involution_const hσd_mem hσd_inv hσd_ne hσd_prod
  have hP_eq_cd : ∏ x ∈ S, x = (c * d) ^ (S.card / 2) :=
    prod_involution_const hσcd_mem hσcd_inv hσcd_ne hσcd_prod
  -- Step 7: Two-involution trick: c^k = (cd)^k → d^k = 1
  have hd_pow : d ^ (S.card / 2) = 1 := by
    have h : c ^ (S.card / 2) = (c * d) ^ (S.card / 2) := by rw [← hP_eq_c, hP_eq_cd]
    rw [mul_pow] at h
    exact mul_left_cancel (a := c ^ (S.card / 2)) (by rwa [mul_one])
  -- Step 8: Therefore c^k = 1
  have hc_pow : c ^ (S.card / 2) = 1 := by rw [hP_eq_c, hP_eq_d, hd_pow]
  -- Step 9: ∏ S = c^k = 1
  rw [hP_eq_c, hc_pow]

-- ============================================================================
-- Section 6: Gauss-Wilson Abstract Biconditional
-- ============================================================================

/-- -1 ≠ 1 in (ZMod n)ˣ for n ≥ 3. -/
private theorem neg_one_ne_one_units' {n : ℕ} (hn : n ≥ 3) :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  intro h
  have h1 : ((-1 : (ZMod n)ˣ) : ZMod n) = ((1 : (ZMod n)ˣ) : ZMod n) := by rw [h]
  simp only [Units.val_neg, Units.val_one] at h1
  have h2 : (n : ℤ) ∣ (-1 - 1) := by
    have := ZMod.intCast_zmod_eq_zero_iff_dvd (-1 - 1) n
    rw [show ((-1 - 1 : ℤ) : ZMod n) = (-1 : ZMod n) - 1 from by push_cast; ring] at this
    rw [h1, sub_self] at this; exact this.mp rfl
  have h3 : (n : ℤ) ∣ 2 := by
    have : (-1 - 1 : ℤ) = -2 := by ring
    rw [this] at h2; exact dvd_neg.mp h2
  have : n ≤ 2 := by have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 2) h3; omega
  omega

/-- -1 ≠ 1 in ZMod n for n ≥ 3. -/
private theorem neg_one_ne_one_zmod' {n : ℕ} (hn : n ≥ 3) : (-1 : ZMod n) ≠ 1 := by
  haveI : NeZero n := ⟨by omega⟩
  intro heq
  have : ((-1 : (ZMod n)ˣ) : ZMod n) = ((1 : (ZMod n)ˣ) : ZMod n) := by simp [heq]
  exact neg_one_ne_one_units' hn (Units.val_injective this)

/-- Cyclic → product = -1, using IsCyclic.card_pow_eq_one_le + involution lemma. -/
private theorem prod_units_neg_one_of_cyclic' {n : ℕ} (hn : n ≥ 3)
    [hne : NeZero n] [hcyc : IsCyclic (ZMod n)ˣ] :
    ∏ x : (ZMod n)ˣ, (x : ZMod n) = -1 := by
  suffices hprod : ∏ x : (ZMod n)ˣ, x = -1 by
    rw [show (∏ x : (ZMod n)ˣ, (x : ZMod n)) = (↑(∏ x : (ZMod n)ˣ, x) : ZMod n) from
      (units_val_prod _ _).symm, hprod]; simp
  rw [prod_eq_prod_sq_eq_one]
  -- In cyclic (ZMod n)ˣ: {x | x² = 1} = {1, -1}
  have hle := IsCyclic.card_pow_eq_one_le (α := (ZMod n)ˣ) (by norm_num : 0 < 2)
  have h1_mem : (1 : (ZMod n)ˣ) ∈ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    simp [Finset.mem_filter, sq]
  have hn1_mem : (-1 : (ZMod n)ˣ) ∈ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    simp [Finset.mem_filter, sq]
  have hne' : (1 : (ZMod n)ˣ) ≠ -1 := (neg_one_ne_one_units' hn).symm
  have hsub : {1, -1} ⊆ Finset.univ.filter (fun (x : (ZMod n)ˣ) => x ^ 2 = 1) := by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  have hcard_pair : ({1, -1} : Finset (ZMod n)ˣ).card = 2 := Finset.card_pair hne'
  have heq := (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  rw [heq, Finset.prod_pair hne'.symm]
  exact one_mul (-1)

/-- **Gauss-Wilson Theorem (Abstract)**:
    For n ≥ 3, ∏ units = -1 ↔ (ZMod n)ˣ is cyclic. -/
theorem gaussWilson_abstract_ext {n : ℕ} (hn : n ≥ 3) [hne : NeZero n] :
    (∏ x : (ZMod n)ˣ, (x : ZMod n) = -1) ↔ IsCyclic (ZMod n)ˣ := by
  constructor
  · intro hprod
    by_contra hncyc
    have h1 := prod_units_one_of_not_cyclic_ext hn hncyc
    rw [h1] at hprod
    exact neg_one_ne_one_zmod' hn hprod.symm
  · intro hcyc
    exact @prod_units_neg_one_of_cyclic' n hn hne hcyc

-- ============================================================================
-- Summary
-- ============================================================================

/-
## Results in this file

### Sorry-free (5 theorems)
1. `even_card_of_fpf_involution`: FPF involution → even cardinality
2. `prod_involution_const`: FPF involution with constant pair product → ∏ S = c^(|S|/2)
3. `mul_involution_on_sq_eq_one`: Multiplication by c is FPF involution on {x | x²=1}
4. `prod_eq_prod_sq_eq_one`: ∏ G = ∏ {x | x² = 1}
5. `prod_units_neg_one_of_cyclic'`: IsCyclic → ∏ units = -1

### With 1 sorry (3 theorems, all depending on same sorry)
6. `card_sq_eq_one_ge_three_of_not_cyclic_zmod`: For (ZMod n)ˣ, n ≥ 3, ¬cyclic → |{x | x²=1}| ≥ 3
   **This is the ONLY sorry**. All other theorems are sorry-free or depend on this.
   **IMPORTANT**: The previous general version (for arbitrary CommGroup G) was FALSE.
   Counterexample: Z/3 × Z/3 is not cyclic but |{x | x²=1}| = 1.
   The theorem is now correctly specialized to (ZMod n)ˣ with n ≥ 3.
7. `prod_units_one_of_not_cyclic_ext`: ¬cyclic → ∏ units = 1
8. `gaussWilson_abstract_ext`: ∏ units = -1 ↔ cyclic

### Proof architecture
The two-involution trick (new in this file) cleanly avoids the need for:
- Finset transversal construction
- Coset partition machinery
- Orbit product formulas
Instead, it uses only `prod_involution_const` applied three times.

### Remaining sorry analysis
`card_sq_eq_one_ge_three_of_not_cyclic_zmod`:
  ¬IsCyclic (ZMod n)ˣ → |{x ∈ (ZMod n)ˣ | x²=1}| ≥ 3 (for n ≥ 3)
- Mathematical truth: For (ZMod n)ˣ specifically, non-cyclic ↔ n has structure
  giving ≥ 2 independent elements of order 2 (via CRT decomposition)
- Formalization path: Use ZMod.chineseRemainder to decompose (ZMod n)ˣ when
  n has coprime factors, then count 2-torsion in the product group
- Verified computationally for n ≤ 300 via gaussWilson_verified_le_300
-/

#check @prod_units_one_of_not_cyclic_ext
#check @gaussWilson_abstract_ext
#check @prod_involution_const
#check @even_card_of_fpf_involution

end WilsonsTheoremOQ02Ext
