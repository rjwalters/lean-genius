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

  `sup_eq_of_isMaximal` is fully proved. `second_iso` is proved via Noether's
  second isomorphism theorem + `QuotientGroup.congr` to avoid `rw` on quotient types.
  `isMaximal_inf_left_of_isMaximal_sup` has Parts 1 (lt) and 2 (normality) proved;
  Part 3 (maximality, the hard step) requires the quotient correspondence theorem
  (Noether's 3rd) and is sorry'd pending Aristotle proof search.
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
    intro x y z hxz hyz hne
    -- hxz : IsMaxNorm x z, hyz : IsMaxNorm y z, hne : x ≠ y
    -- Goal: x ⊔ y = z
    have hxz_le : x ≤ z := hxz.1.le
    have hyz_le : y ≤ z := hyz.1.le
    have hxy_le_z : x ⊔ y ≤ z := sup_le hxz_le hyz_le
    -- (x ⊔ y).subgroupOf z is normal: it equals x.subgroupOf z ⊔ y.subgroupOf z
    have hxy_normal : ((x ⊔ y).subgroupOf z).Normal := by
      rw [Subgroup.subgroupOf_sup hxz_le hyz_le]
      haveI := hxz.2.1
      haveI := hyz.2.1
      exact Subgroup.sup_normal _ _
    -- Apply maximality of x in z to x ⊔ y (with x ≤ x ⊔ y ≤ z, normal)
    rcases hxz.2.2 (x ⊔ y) le_sup_left hxy_le_z hxy_normal with h | h
    · -- h : x ⊔ y = x → y ≤ x; apply maximality of y in z to x
      exfalso
      have hy_le_x : y ≤ x := le_sup_right.trans h.le
      rcases hyz.2.2 x hy_le_x hxz_le hxz.2.1 with hyx | hxz_eq
      · exact hne (le_antisymm hy_le_x hyx.le)
      · exact absurd hxz_eq hxz.1.ne'
    · exact h

  isMaximal_inf_left_of_isMaximal_sup := by
    intro x y hx hy
    -- hx : IsMaxNorm x (x ⊔ y), hy : IsMaxNorm y (x ⊔ y)
    -- Goal: IsMaxNorm (x ⊓ y) x
    -- Part 1: x ⊓ y < x
    have hlt : x ⊓ y < x := by
      rcases (inf_le_left (a := x) (b := y)).lt_or_eq with h | h
      · exact h
      · exfalso
        -- h : x ⊓ y = x → x ≤ y → x ⊔ y = y, contradicts hy.1 : y < x ⊔ y
        have hxy : x ≤ y := h ▸ inf_le_right
        exact absurd (sup_of_le_right hxy ▸ hy.1) (lt_irrefl _)
    -- Part 2: ((x ⊓ y).subgroupOf x).Normal
    -- hy.2.1 : (y.subgroupOf (x ⊔ y)).Normal
    -- Transport via sup_comm to get (y.subgroupOf (y ⊔ x)).Normal
    -- Then x ≤ y.normalizer, so (y.subgroupOf x).Normal
    -- And inf_subgroupOf_left gives ((x ⊓ y).subgroupOf x).Normal
    have hle : x ≤ y.normalizer :=
      le_normalizer_of_normal_in_sup (sup_comm x y ▸ hy.2.1)
    have hn_y_x : (y.subgroupOf x).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hle
    have hn_inf : ((x ⊓ y).subgroupOf x).Normal :=
      Subgroup.inf_subgroupOf_left y x ▸ hn_y_x
    -- Part 3: maximality of x ⊓ y in x
    -- Proof: for N with x ⊓ y ≤ N ≤ x and (N.subgroupOf x).Normal,
    -- map N ↦ N ⊔ y and use maximality of y in x ⊔ y.
    -- The case N ⊔ y = y gives N = x ⊓ y; the case N ⊔ y = x ⊔ y needs
    -- the second isomorphism to transfer simplicity, which requires the
    -- quotient correspondence theorem (Noether 3rd).
    have hmax : ∀ N : Subgroup G, x ⊓ y ≤ N → N ≤ x →
        (N.subgroupOf x).Normal → N = x ⊓ y ∨ N = x := by
      -- Full proof requires the quotient group correspondence theorem:
      -- the isomorphism x/(x ⊓ y) ≃* (x ⊔ y)/y (Noether 2nd) transfers
      -- simplicity of (x ⊔ y)/y (from hy) to x/(x ⊓ y), hence N = x ⊓ y or N = x.
      -- The N ↦ N ⊔ y approach fails because (N ⊔ y).subgroupOf (x ⊔ y) is not
      -- generally normal when N is only relatively normal in x (not in x ⊔ y).
      sorry
    exact ⟨hlt, hn_inf, hmax⟩

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
    -- Goal: IsMaximal x (x ⊔ y) → GroupQuotIso (x, x ⊔ y) (x ⊓ y, y)
    -- i.e. ∃ hn1 hn2, Nonempty ((x ⊔ y) ⧸ x.subgroupOf (x ⊔ y) ≃* y ⧸ (x ⊓ y).subgroupOf y)
    intro x y hx
    obtain ⟨_, hn_sup, _⟩ := hx
    -- hn_sup : (x.subgroupOf (x ⊔ y)).Normal
    have hle : y ≤ x.normalizer := le_normalizer_of_normal_in_sup hn_sup
    -- ((x ⊓ y).subgroupOf y).Normal via inf_subgroupOf_right and normalizer
    have hn_inf : ((x ⊓ y).subgroupOf y).Normal :=
      Subgroup.inf_subgroupOf_right x y ▸ Subgroup.normal_subgroupOf_of_le_normalizer hle
    refine ⟨hn_sup, hn_inf, ?_⟩
    -- Build: (x ⊔ y) ⧸ x.subgroupOf (x ⊔ y)  ≃*  y ⧸ (x ⊓ y).subgroupOf y
    -- by composing three equivs:
    --   e1: (x ⊔ y) ⧸ x.subgroupOf (x ⊔ y)  ≃*  (y ⊔ x) ⧸ x.subgroupOf (y ⊔ x)
    --       via QuotientGroup.congr + MulEquiv.subgroupCongr (sup_comm x y)
    --   e2: (y ⊔ x) ⧸ x.subgroupOf (y ⊔ x)  ≃*  y ⧸ x.subgroupOf y
    --       via (quotientInfEquivProdNormalizerQuotient y x hle).symm
    --   e3: y ⧸ x.subgroupOf y  ≃*  y ⧸ (x ⊓ y).subgroupOf y
    --       via quotientMulEquivOfEq (inf_subgroupOf_right x y).symm
    haveI := hn_sup
    haveI := hn_inf
    haveI hn_xy : (x.subgroupOf y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hle
    haveI hn_yx : (x.subgroupOf (y ⊔ x)).Normal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hle
    -- e1: congr via sup_comm — avoids rw on quotient types using QuotientGroup.congr
    have he1 : (x.subgroupOf (x ⊔ y)).map (MulEquiv.subgroupCongr (sup_comm x y)) =
        x.subgroupOf (y ⊔ x) := by
      apply Subgroup.ext
      intro ⟨g, hg⟩
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨a, ha, heq⟩
        have hag : (a : G) = g := by
          have h := congrArg Subtype.val heq
          simp only [MulEquiv.subgroupCongr_apply] at h
          exact h
        rwa [← hag]
      · intro hgx
        exact ⟨⟨g, sup_comm y x ▸ hg⟩, hgx,
          Subtype.ext (MulEquiv.subgroupCongr_apply (sup_comm x y) ⟨g, sup_comm y x ▸ hg⟩)⟩
    have e1 : (x ⊔ y : Subgroup G) ⧸ x.subgroupOf (x ⊔ y) ≃*
              (y ⊔ x : Subgroup G) ⧸ x.subgroupOf (y ⊔ x) :=
      QuotientGroup.congr (MulEquiv.subgroupCongr (sup_comm x y)) he1
    -- e2: Noether's second isomorphism theorem, symm direction
    have e2 : (y ⊔ x : Subgroup G) ⧸ x.subgroupOf (y ⊔ x) ≃* y ⧸ x.subgroupOf y :=
      (quotientInfEquivProdNormalizerQuotient y x hle).symm
    -- e3: transport the RHS subgroupOf via inf_subgroupOf_right
    have e3 : y ⧸ x.subgroupOf y ≃* y ⧸ (x ⊓ y).subgroupOf y :=
      QuotientGroup.quotientMulEquivOfEq (Subgroup.inf_subgroupOf_right x y).symm
    exact ⟨(e1.trans e2).trans e3⟩

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
