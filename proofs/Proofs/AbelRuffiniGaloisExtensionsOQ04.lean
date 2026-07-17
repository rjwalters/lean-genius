/-
  Jordan-Hölder Uniqueness Theorem for Finite Groups (OQ-04)

  Instantiates `JordanHolderLattice` for `Subgroup G` (filling a Mathlib TODO)
  and derives the Jordan-Hölder theorem for finite groups.

  ## Main Results

  1. `instJordanHolderLatticeSubgroup` — `JordanHolderLattice (Subgroup G)` instance
  2. `jordan_holder_subgroups` — Jordan-Hölder theorem for groups

  ## Mathlib Gap

  As of Mathlib 2026, `JordanHolderLattice (Subgroup G)` is a TODO in
  `Mathlib.Order.JordanHolder` with the note "it is not entirely clear how this
  should be done." This file fills that gap.

  ## Proof Status

  All three `JordanHolderLattice` axioms are fully proved (0 sorries):
  - `sup_eq_of_isMaximal`: proved via subgroupOf_sup + maximality argument
  - `isMaximal_inf_left_of_isMaximal_sup`: proved via element-wise decomposition (Subgroup.mem_sup)
  - `second_iso`: proved via first isomorphism theorem (avoids sup_comm rewrite failure)
-/

import Mathlib.Tactic
import Mathlib.Order.JordanHolder
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Subgroup.Simple
import Proofs.AbelRuffiniGaloisExtensions

namespace AbelRuffiniGaloisExtensionsOQ04

open Subgroup QuotientGroup

variable {G : Type*} [Group G]

-- ============================================================
-- PART I: Predicates
-- ============================================================

/-- H is a maximal normal subgroup of K:
    H < K, H is relatively normal in K, and every normal-in-K subgroup
    between H and K equals H or K.

    This is equivalent to `IsSimpleGroup (K ⧸ H.subgroupOf K)` by the
    correspondence theorem, but avoids quotient typeclass issues. -/
def IsMaxNorm (H K : Subgroup G) : Prop :=
  H < K ∧
  (H.subgroupOf K).Normal ∧
  ∀ N : Subgroup G, H ≤ N → N ≤ K → (N.subgroupOf K).Normal → N = H ∨ N = K

/-- Quotient iso: K₁/H₁ ≃* K₂/H₂, carrying normality evidence. -/
def GroupQuotIso (X Y : Subgroup G × Subgroup G) : Prop :=
  ∃ (hn1 : (X.1.subgroupOf X.2).Normal) (hn2 : (Y.1.subgroupOf Y.2).Normal),
    letI := hn1; letI := hn2
    Nonempty (X.2 ⧸ X.1.subgroupOf X.2 ≃* Y.2 ⧸ Y.1.subgroupOf Y.2)

-- ============================================================
-- PART II: Key Normalizer Lemma
-- ============================================================

/-- If H is relatively normal in H ⊔ K, then K ≤ Subgroup.normalizer H. -/
lemma le_normalizer_of_normal_in_sup {H K : Subgroup G}
    (hn : (H.subgroupOf (H ⊔ K)).Normal) : K ≤ Subgroup.normalizer H :=
  le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn)

/-- If `H` is relatively normal in `H ⊔ K` then every element of `H ⊔ K`
    decomposes as `h₀ * k₀` with `h₀ ∈ H`, `k₀ ∈ K`. -/
lemma sup_decomp {H K : Subgroup G} (hn : (H.subgroupOf (H ⊔ K)).Normal)
    {g : G} (hg : g ∈ H ⊔ K) : ∃ h₀ ∈ H, ∃ k₀ ∈ K, h₀ * k₀ = g := by
  haveI := hn
  have hg' : (⟨g, hg⟩ : ↥(H ⊔ K)) ∈ H.subgroupOf (H ⊔ K) ⊔ K.subgroupOf (H ⊔ K) := by
    rw [← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self]
    exact mem_top _
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_left.mp hg'
  refine ⟨(a : G), mem_subgroupOf.mp ha, (b : G), mem_subgroupOf.mp hb, ?_⟩
  have hcast := congrArg (Subtype.val) hab
  simpa using hcast

/-- Correspondence-style normality: if `N` is normal in `x` (with `N ≤ x`) and
    `y` is normal in `x ⊔ y`, then `N ⊔ y` is normal in `x ⊔ y`. -/
lemma sup_subgroupOf_normal {x y N : Subgroup G}
    (hNx : (N.subgroupOf x).Normal) (hNle : N ≤ x)
    (hy : (y.subgroupOf (x ⊔ y)).Normal) :
    ((N ⊔ y).subgroupOf (x ⊔ y)).Normal := by
  -- conjugation by an element of `x` preserves `N`
  have hNconj : ∀ a ∈ x, ∀ n ∈ N, a * n * a⁻¹ ∈ N := by
    intro a ha n hn
    have key := hNx.conj_mem ⟨n, hNle hn⟩ (mem_subgroupOf.mpr hn) ⟨a, ha⟩
    rw [mem_subgroupOf] at key
    simpa using key
  -- conjugation by an element of `x ⊔ y` preserves `y`
  have hyconj : ∀ a ∈ x ⊔ y, ∀ b ∈ y, a * b * a⁻¹ ∈ y := by
    intro a ha b hb
    have key := hy.conj_mem ⟨b, mem_sup_right hb⟩ (mem_subgroupOf.mpr hb) ⟨a, ha⟩
    rw [mem_subgroupOf] at key
    simpa using key
  -- conjugation by an element of `x` preserves `N ⊔ y`
  have hpres : ∀ a ∈ x, ∀ h ∈ N ⊔ y, a * h * a⁻¹ ∈ N ⊔ y := by
    intro a ha h hh
    rw [sup_eq_closure] at hh
    refine Subgroup.closure_induction
      (p := fun g _ => a * g * a⁻¹ ∈ N ⊔ y) ?_ ?_ ?_ ?_ hh
    · rintro g (hg | hg)
      · exact mem_sup_left (hNconj a ha g hg)
      · exact mem_sup_right (hyconj a (mem_sup_left ha) g hg)
    · simpa using (N ⊔ y).one_mem
    · intro p q _ _ ihp ihq
      have hpq : a * (p * q) * a⁻¹ = (a * p * a⁻¹) * (a * q * a⁻¹) := by group
      rw [hpq]; exact (N ⊔ y).mul_mem ihp ihq
    · intro p _ ihp
      have hpi : a * p⁻¹ * a⁻¹ = (a * p * a⁻¹)⁻¹ := by group
      rw [hpi]; exact (N ⊔ y).inv_mem ihp
  have hNyle : N ⊔ y ≤ x ⊔ y := sup_le_sup_right hNle y
  rw [normal_subgroupOf_iff_le_normalizer hNyle]
  refine sup_le ?_ (le_sup_right.trans le_normalizer)
  intro a ha
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh; exact hpres a ha h hh
  · intro hh
    have hinv := hpres a⁻¹ (x.inv_mem ha) _ hh
    have hcancel : a⁻¹ * (a * h * a⁻¹) * a⁻¹⁻¹ = h := by group
    rwa [hcancel] at hinv

-- ============================================================
-- PART III: JordanHolderLattice Instance
-- ============================================================

noncomputable instance instJordanHolderLatticeSubgroup :
    JordanHolderLattice (Subgroup G) where

  IsMaximal := IsMaxNorm

  lt_of_isMaximal := fun h => h.1

  sup_eq_of_isMaximal := by
    /- Proof: x, y both maximal normal in z (with x ≠ y).
       Strategy: apply x's maximality to x⊔y (which is normal in z via subgroupOf_sup),
       getting x⊔y = x or x⊔y = z. The first case gives y ≤ x, then y's maximality
       applied to x in z gives a contradiction with x ≠ y or x not maximal. -/
    intro x y z hxz hyz hne
    have hx_le_z : x ≤ z := hxz.1.le
    have hy_le_z : y ≤ z := hyz.1.le
    have hn_xy_z : ((x ⊔ y).subgroupOf z).Normal := by
      rw [subgroupOf_sup hx_le_z hy_le_z]
      haveI := hxz.2.1; haveI := hyz.2.1
      infer_instance
    rcases hxz.2.2 (x ⊔ y) le_sup_left (sup_le hx_le_z hy_le_z) hn_xy_z with h | h
    · have hyx : y ≤ x := h ▸ le_sup_right
      rcases hyz.2.2 x hyx hx_le_z hxz.2.1 with h2 | h2
      · exact absurd h2 hne
      · exact absurd h2 (ne_of_lt hxz.1)
    · exact h

  isMaximal_inf_left_of_isMaximal_sup := by
    /- Proof: x, y both maximal normal in x⊔y. Want: x⊓y maximal normal in x.
       Three parts: (1) x⊓y < x via inf_le_left + contradiction; (2) normality via
       inf_subgroupOf_right; (3) maximality via element-wise argument — for N⊔y = x⊔y,
       any a ∈ x decomposes as n*b with n ∈ N ≤ x, b ∈ y∩x = x⊓y ≤ N, so a ∈ N. -/
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · -- x ⊓ y < x
      apply lt_of_le_of_ne inf_le_left
      intro h_eq
      have hxy : x ≤ y := h_eq ▸ inf_le_right
      have hsup : x ⊔ y = y := sup_eq_right.mpr hxy
      exact absurd (hy.1.trans_eq hsup) (lt_irrefl y)
    · -- (x ⊓ y).subgroupOf x is Normal
      have hxle_yn : x ≤ Subgroup.normalizer y := by
        have := (normal_subgroupOf_iff_le_normalizer le_sup_right).mp hy.2.1
        exact le_trans le_sup_left this
      have : (y.subgroupOf x).Normal := normal_subgroupOf_of_le_normalizer hxle_yn
      rwa [inf_comm, inf_subgroupOf_right]
    · -- maximality: ∀ N, x ⊓ y ≤ N ≤ x → (N.subgroupOf x).Normal → N = x ⊓ y ∨ N = x
      intro N hN_lo hN_hi hN_norm
      -- Use second_iso direction: x/(x⊓y) ≃* (x⊔y)/y
      -- N⊔y is between y and x⊔y, and is normal in x⊔y (correspondence),
      -- so maximality of y in x⊔y forces N⊔y = y or N⊔y = x⊔y.
      have hNy_le : N ⊔ y ≤ x ⊔ y := sup_le_sup_right hN_hi y
      have hy_le_Ny : y ≤ N ⊔ y := le_sup_right
      -- y is normal in N⊔y (used for the element decomposition below)
      have hxle_yn : x ≤ Subgroup.normalizer y := by
        have := (normal_subgroupOf_iff_le_normalizer le_sup_right).mp hy.2.1
        exact le_trans le_sup_left this
      have hN_le_yn : N ≤ Subgroup.normalizer y := hN_hi.trans hxle_yn
      have hn_y_Ny : (y.subgroupOf (N ⊔ y)).Normal :=
        (normal_subgroupOf_iff_le_normalizer hy_le_Ny).mpr
          (sup_le hN_le_yn le_normalizer)
      -- N⊔y is normal in x⊔y (correspondence theorem)
      have hn_Ny_sup : ((N ⊔ y).subgroupOf (x ⊔ y)).Normal :=
        sup_subgroupOf_normal hN_norm hN_hi hy.2.1
      -- Apply maximality of y in x⊔y to N⊔y
      rcases hy.2.2 (N ⊔ y) hy_le_Ny hNy_le hn_Ny_sup with h | h
      · -- N ⊔ y = y → N ≤ y → N = x ⊓ y
        left
        have hNy : N ≤ y := le_sup_left.trans (le_of_eq h)
        exact le_antisymm (le_inf hN_hi hNy) hN_lo
      · -- N ⊔ y = x ⊔ y: element-wise argument directly gives x ≤ N, so N = x.
        -- For any a ∈ x: a ∈ x ⊔ y = N ⊔ y = y ⊔ N, so ∃ p ∈ y, n ∈ N, p*n = a.
        -- Then p = a*n⁻¹ ∈ x (since n ∈ N ≤ x and a ∈ x) ∩ y = x⊓y ≤ N.
        -- So a = p*n ∈ N. Hence x ≤ N, and with N ≤ x: N = x.
        right
        apply le_antisymm hN_hi
        intro a haA
        have ha_in_yN : a ∈ y ⊔ N := by rw [sup_comm, h]; exact mem_sup_left haA
        have hn_y_yN : (y.subgroupOf (y ⊔ N)).Normal := by rw [sup_comm]; exact hn_y_Ny
        obtain ⟨p, hpy, n, hnN, hpn_eq⟩ := sup_decomp hn_y_yN ha_in_yN
        have hnx : n ∈ x := hN_hi hnN
        have hpx : p ∈ x := by
          have h_eq : p = a * n⁻¹ := by rw [← hpn_eq]; group
          rw [h_eq]; exact x.mul_mem haA (x.inv_mem hnx)
        have hpN : p ∈ N := hN_lo (Subgroup.mem_inf.mpr ⟨hpx, hpy⟩)
        rw [← hpn_eq]
        exact N.mul_mem hpN hnN

  Iso := GroupQuotIso

  iso_symm := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨hn1, hn2, f⟩
    refine ⟨hn2, hn1, ?_⟩
    haveI := hn1; haveI := hn2
    exact f.map (·.symm)

  iso_trans := by
    rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩ ⟨hn1, hn2, f⟩ ⟨hn2', hn3, g⟩
    refine ⟨hn1, hn3, ?_⟩
    haveI := hn1; haveI := hn2; haveI := hn2'; haveI := hn3
    rcases f with ⟨e1⟩; rcases g with ⟨e2⟩; exact ⟨e1.trans e2⟩

  second_iso := by
    /- Proof: (x ⊔ y) ⧸ x ≃* y ⧸ (x ⊓ y) via Noether's second isomorphism.
       Key insight: construct φ : y →* (x ⊔ y) ⧸ x directly as mk' ∘ inclusion,
       avoiding rw [sup_comm] which fails due to Normal typeclass dependency.
       ker φ = (x ⊓ y).subgroupOf y; φ surjective by decomposing elements of x ⊔ y.
       Apply quotientKerEquivOfSurjective to get the isomorphism. -/
    intro x y hx
    have hn_sup : (x.subgroupOf (x ⊔ y)).Normal := hx.2.1
    have hle : y ≤ Subgroup.normalizer x := le_normalizer_of_normal_in_sup hn_sup
    have hn_inf : ((x ⊓ y).subgroupOf y).Normal := by
      rw [inf_subgroupOf_right]
      exact normal_subgroupOf_of_le_normalizer hle
    refine ⟨hn_sup, hn_inf, ?_⟩
    haveI := hn_sup; haveI := hn_inf
    let φ : y →* ↥(x ⊔ y) ⧸ x.subgroupOf (x ⊔ y) :=
      (mk' (x.subgroupOf (x ⊔ y))).comp (inclusion le_sup_right)
    have hker : φ.ker = (x ⊓ y).subgroupOf y := by
      ext ⟨g, hg⟩
      rw [MonoidHom.mem_ker,
          show φ ⟨g, hg⟩ = (mk' (x.subgroupOf (x ⊔ y))) (inclusion le_sup_right ⟨g, hg⟩) from rfl,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf, mem_inf]
      constructor
      · intro h; exact ⟨h, hg⟩
      · intro h; exact h.1
    have hφ_surj : Function.Surjective φ := by
      intro q
      refine QuotientGroup.induction_on' (C := fun w => ∃ a, φ a = w) q (fun z => ?_)
      obtain ⟨a, ha, b, hb, hab⟩ := sup_decomp hn_sup z.2
      refine ⟨⟨b, hb⟩, ?_⟩
      have hval : (↑((inclusion (le_sup_right : y ≤ x ⊔ y) ⟨b, hb⟩)⁻¹ * z) : G) = b⁻¹ * ↑z := by
        simp [coe_inclusion]
      have hbn : b⁻¹ * a * b ∈ x := by
        have hnb := (mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem (hle hb)) a).mp ha
        simpa using hnb
      show (mk' (x.subgroupOf (x ⊔ y))) (inclusion le_sup_right ⟨b, hb⟩) = (↑z : _)
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf, hval, ← hab, ← mul_assoc]
      exact hbn
    haveI : (φ.ker).Normal := by rw [hker]; infer_instance
    have e := QuotientGroup.quotientKerEquivOfSurjective φ hφ_surj
    exact ⟨e.symm.trans (QuotientGroup.quotientMulEquivOfEq hker)⟩

-- ============================================================
-- PART IV: Jordan-Hölder Theorem
-- ============================================================

/-- **Jordan-Hölder Theorem**: Any two composition series of a group with the
    same endpoints are equivalent (same length, same composition factors). -/
theorem jordan_holder_subgroups
    (s₁ s₂ : CompositionSeries (Subgroup G))
    (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) :
    CompositionSeries.Equivalent s₁ s₂ :=
  CompositionSeries.jordan_holder s₁ s₂ hb ht

/-- Jordan-Hölder for finite groups. -/
theorem jordan_holder_finite_groups [Finite G]
    (s₁ s₂ : CompositionSeries (Subgroup G))
    (hb : s₁.head = s₂.head) (ht : s₁.last = s₂.last) :
    CompositionSeries.Equivalent s₁ s₂ :=
  jordan_holder_subgroups s₁ s₂ hb ht

-- ============================================================
-- PART V: Verification
-- ============================================================

#check @jordan_holder_subgroups
#check @instJordanHolderLatticeSubgroup

end AbelRuffiniGaloisExtensionsOQ04
