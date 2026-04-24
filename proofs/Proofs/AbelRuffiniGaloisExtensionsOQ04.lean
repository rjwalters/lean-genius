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

  ## Note on Sorries

  `sup_eq_of_isMaximal` and `second_iso` are proved.
  `isMaximal_inf_left_of_isMaximal_sup` has 1 sorry remaining:
  the maximality step requires transferring simplicity of (x⊔y)/y through
  the second isomorphism to x/(x⊓y), then applying the correspondence theorem.
  This is a HARD goal for Aristotle.
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

/-- If H is relatively normal in H ⊔ K, then K ≤ H.normalizer. -/
lemma le_normalizer_of_normal_in_sup {H K : Subgroup G}
    (hn : (H.subgroupOf (H ⊔ K)).Normal) : K ≤ H.normalizer :=
  le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn)

-- ============================================================
-- PART III: JordanHolderLattice Instance
-- ============================================================

noncomputable instance instJordanHolderLatticeSubgroup :
    JordanHolderLattice (Subgroup G) where

  IsMaximal := IsMaxNorm

  lt_of_isMaximal := fun h => h.1

  sup_eq_of_isMaximal := by
    /- Proof sketch (sorry'd):
       x, y both maximal normal in z (with x ≠ y).
       • Both relatively normal in z → x⊔y relatively normal in z
         (product of normal subgroups is normal)
       • x ≤ x⊔y ≤ z; image of x⊔y in z/x is normal in z/x
       • z/x is "simple" (from IsMaxNorm x z): the only normal subgroups of z
         between x and z are x and z; hence x⊔y = x or x⊔y = z
       • x⊔y = x ⟹ y ≤ x ⟹ y/x is trivial ⟹ x is in between y and z, but y
         maximal in z — contradicts x ≠ y both maximal.
       • Therefore x⊔y = z. -/
    intro x y z hxz hyz hne
    have hx_le_z : x ≤ z := hxz.1.le
    have hy_le_z : y ≤ z := hyz.1.le
    have hn_xy_z : ((x ⊔ y).subgroupOf z).Normal := by
      rw [subgroupOf_sup hx_le_z hy_le_z]
      haveI := hxz.2.1; haveI := hyz.2.1
      infer_instance
    rcases hxz.2.2 le_sup_left (sup_le hx_le_z hy_le_z) hn_xy_z with h | h
    · have hyx : y ≤ x := h ▸ le_sup_right
      rcases hyz.2.2 hyx hx_le_z hxz.2.1 with h2 | h2
      · exact absurd h2 hne
      · exact absurd h2 (ne_of_lt hxz.1)
    · exact h

  isMaximal_inf_left_of_isMaximal_sup := by
    /- Proof sketch (sorry'd):
       x, y both maximal normal in x⊔y. Want: x⊓y maximal normal in x.
       • IsMaxNorm y (x⊔y) → y relatively normal in x⊔y
         → x ≤ x⊔y ≤ y.normalizer → (y.subgroupOf x).Normal
         → (using inf_subgroupOf_right): ((x⊓y).subgroupOf x).Normal. ✓
       • x⊓y < x: if x⊓y = x then x ≤ y → x⊔y = y, contradicts y < x⊔y. ✓
       • Simplicity of x/(x⊓y): by second_iso, (x⊔y)/y ≃* x/(x⊓y).
         Transfer simplicity of (x⊔y)/y (from IsMaxNorm y (x⊔y)) to x/(x⊓y). ✓ -/
    intro x y hx hy
    refine ⟨?_, ?_, ?_⟩
    · -- x ⊓ y < x
      apply lt_of_le_of_ne inf_le_left
      intro h_eq
      have hxy : x ≤ y := h_eq ▸ inf_le_right
      rcases hy.2.2 hxy hx.1.le hx.2.1 with h | h
      · simp only [h, sup_idem] at hx; exact lt_irrefl _ hx.1
      · exact absurd h.symm hx.1.ne'
    · -- (x ⊓ y).subgroupOf x is Normal
      have hxle_yn : x ≤ y.normalizer := by
        have := (normal_subgroupOf_iff_le_normalizer le_sup_right).mp hy.2.1
        exact le_trans le_sup_left this
      have : (y.subgroupOf x).Normal := normal_subgroupOf_of_le_normalizer hxle_yn
      rwa [inf_comm, inf_subgroupOf_right]
    · -- maximality: ∀ N, x ⊓ y ≤ N ≤ x → (N.subgroupOf x).Normal → N = x ⊓ y ∨ N = x
      intro N hN_lo hN_hi hN_norm
      -- Use second_iso direction: x/(x⊓y) ≃* (x⊔y)/y
      -- N/x⊓y is a subquotient; transfer to a subgroup between y and x⊔y
      -- then use maximality of y in x⊔y
      -- N⊔y is between y and x⊔y
      have hNy_le : N ⊔ y ≤ x ⊔ y := sup_le_sup_right hN_hi y
      have hy_le_Ny : y ≤ N ⊔ y := le_sup_right
      -- (y.subgroupOf (N⊔y)).Normal: need y normal in N⊔y
      have hxle_yn : x ≤ y.normalizer := by
        have := (normal_subgroupOf_iff_le_normalizer le_sup_right).mp hy.2.1
        exact le_trans le_sup_left this
      have hN_le_yn : N ≤ y.normalizer := hN_hi.trans hxle_yn
      have hn_y_Ny : (y.subgroupOf (N ⊔ y)).Normal :=
        (normal_subgroupOf_iff_le_normalizer hy_le_Ny).mpr
          (sup_le hN_le_yn (le_normalizer y))
      -- Apply maximality of y in x⊔y to N⊔y
      rcases hy.2.2 hy_le_Ny hNy_le hn_y_Ny with h | h
      · -- N ⊔ y = y → N ≤ y → N = x ⊓ y
        left
        have hNy : N ≤ y := le_sup_left.trans (h ▸ le_refl _)
        exact le_antisymm (le_inf hN_hi hNy) hN_lo
      · -- N ⊔ y = x ⊔ y: x/(x⊓y) ≃* (x⊔y)/y simple; N normal in x → N = x⊓y or N = x
        -- (HARD: requires transferring simplicity through second_iso; left as sorry)
        sorry

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
    /- Proof sketch (sorry'd due to Lean 4 "motive not type correct" rewrite issue):
       Want: GroupQuotIso (x, x ⊔ y) (x ⊓ y, y)
         = ∃ hn1 hn2, Nonempty ((x ⊔ y) ⧸ x.subgroupOf (x ⊔ y) ≃* y ⧸ (x ⊓ y).subgroupOf y)
       Strategy:
       1. hn_sup : (x.subgroupOf (x ⊔ y)).Normal  from  hx.2.1
       2. hle : y ≤ x.normalizer  from  le_normalizer_of_normal_in_sup hn_sup
       3. hn_inf : ((x ⊓ y).subgroupOf y).Normal  via  inf_subgroupOf_right + hle
       4. Noether: quotientInfEquivProdNormalizerQuotient y x hle gives
            y ⧸ x.subgroupOf y ≃* (y ⊔ x) ⧸ x.subgroupOf (y ⊔ x)
          After .symm: (y ⊔ x) ⧸ x.subgroupOf (y ⊔ x) ≃* y ⧸ x.subgroupOf y
       5. Transport along sup_comm (y ⊔ x = x ⊔ y) and inf_subgroupOf_right.
       Blocked: rw [sup_comm y x] at key fails — "motive not type correct"
         because quotient type ↥_ ⧸ x.subgroupOf _ has Normal instance
         depending on the rewritten term; rw cannot abstract this.
       Fix needed: use MulEquiv.subgroupCongr or direct Quotient.congr construction. -/
    intro x y hx
    have hn_sup : (x.subgroupOf (x ⊔ y)).Normal := hx.2.1
    have hle : y ≤ x.normalizer := le_normalizer_of_normal_in_sup hn_sup
    have hn_inf : ((x ⊓ y).subgroupOf y).Normal := by
      rw [inf_comm, inf_subgroupOf_right]
      exact normal_subgroupOf_of_le_normalizer hle
    refine ⟨hn_sup, hn_inf, ?_⟩
    haveI := hn_sup; haveI := hn_inf
    let φ : y →* (x ⊔ y) ⧸ x.subgroupOf (x ⊔ y) :=
      (mk' (x.subgroupOf (x ⊔ y))).comp (inclusion le_sup_right)
    have hker : φ.ker = (x ⊓ y).subgroupOf y := by
      ext ⟨g, hg⟩
      simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, inclusion_mk, mk'_apply,
                 QuotientGroup.eq_one_iff, mem_subgroupOf, mem_inf, hg, and_true]
    have hφ_surj : Function.Surjective φ := fun q =>
      q.inductionOn' fun ⟨g, hg⟩ => by
        obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.mp hg
        refine ⟨⟨b, hb⟩, QuotientGroup.eq.mpr ?_⟩
        simp only [φ, MonoidHom.comp_apply, inclusion_mk, leftRel_apply, mem_subgroupOf]
        have key := hn_sup.conj_mem
          (show (⟨a, Subgroup.mem_sup_left ha⟩ : (x ⊔ y)) ∈ x.subgroupOf (x ⊔ y)
           from Subgroup.mem_subgroupOf.mpr ha)
          (⟨b, Subgroup.mem_sup_right hb⟩ : (x ⊔ y))
        rw [Subgroup.mem_subgroupOf] at key
        rw [← mul_assoc]; exact key
    haveI : (φ.ker).Normal := by rw [hker]; infer_instance
    have e := QuotientGroup.quotientKerEquivOfSurjective φ hφ_surj
    rw [hker] at e
    exact ⟨e.symm⟩

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
