/-
  Ideal-Theoretic Chinese Remainder Theorem: R/⨅Iᵢ ≅ ∏ R/Iᵢ

  Open Question (bezout-identity-oq-03-oq-01-oq-01-oq-01):
  Formalize the ideal-theoretic Chinese Remainder Theorem:
  for pairwise coprime ideals I₁, ..., Iₖ in a commutative ring R,
  R / (I₁ ∩ ... ∩ Iₖ) ≅ (R/I₁) × ... × (R/Iₖ).

  This is the abstract algebra generalization of the integer CRT
  (parent: BezoutIdentityOQ03OQ01OQ01.lean, k-fold ℤ/nℤ version).

  Status (0 axioms, 0 sorries)
  Parent: BezoutIdentityOQ03OQ01OQ01.lean (0 axioms, 0 sorries)

  References:
  - Lang (2002): "Algebra", Ch. II §2
  - Atiyah-Macdonald (1969): "Introduction to Commutative Algebra", Prop. 1.10
-/
import Mathlib

namespace BezoutIdentityCRTIdeals

open Ideal

variable {R : Type*} [CommRing R]

-- ============================================================
-- Part I: Coprimality of Ideals
-- ============================================================

/-- Two ideals are coprime iff their sum is the whole ring. -/
theorem coprime_iff_sup_eq_top (I J : Ideal R) :
    IsCoprime I J ↔ I ⊔ J = ⊤ :=
  Ideal.isCoprime_iff_sup_eq

/-- For coprime ideals, the intersection equals the product.
    This is the key structural fact connecting ∩ and ·. -/
theorem inf_eq_mul_of_coprime {I J : Ideal R} (h : I ⊔ J = ⊤) :
    I ⊓ J = I * J := by
  apply le_antisymm
  · intro x hx
    rw [Submodule.mem_inf] at hx
    rw [Ideal.eq_top_iff_one, Submodule.mem_sup] at h
    obtain ⟨a, ha, b, hb, hab⟩ := h
    have : x = x * a + x * b := by rw [← mul_add, hab, mul_one]
    rw [this]
    exact Ideal.add_mem _ (mul_comm x a ▸ Ideal.mul_mem_mul ha hx.2)
      (Ideal.mul_mem_mul hx.1 hb)
  · exact Ideal.mul_le_inf

-- ============================================================
-- Part II: Two-Fold CRT
-- ============================================================

/-- The 2-fold ideal CRT: for coprime I, J in a commutative ring R,
    R / (I ∩ J) ≅ (R/I) × (R/J) as rings. -/
noncomputable def crt_two (I J : Ideal R) (h : IsCoprime I J) :
    R ⧸ (I ⊓ J) ≃+* (R ⧸ I) × (R ⧸ J) :=
  Ideal.quotientInfEquivQuotientProd I J h

/-- Surjectivity of the 2-fold CRT map. -/
theorem crt_two_surjective (I J : Ideal R) (h : IsCoprime I J) :
    Function.Surjective (crt_two I J h) :=
  (crt_two I J h).surjective

/-- Injectivity of the 2-fold CRT map. -/
theorem crt_two_injective (I J : Ideal R) (h : IsCoprime I J) :
    Function.Injective (crt_two I J h) :=
  (crt_two I J h).injective

-- ============================================================
-- Part III: General k-Fold CRT
-- ============================================================

/-- **The Ideal-Theoretic Chinese Remainder Theorem (k-fold)**:
    For a finite family of pairwise coprime ideals {Iᵢ}_{i∈ι} in R,
    R / (⨅ i, Iᵢ) ≅ ∏ᵢ (R / Iᵢ) as rings.

    This is the abstract algebra generalization of the classical CRT.
    The coprimality condition means Iᵢ + Iⱼ = R for all i ≠ j. -/
noncomputable def crt_general {ι : Type*} [Finite ι]
    (I : ι → Ideal R) (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) :
    R ⧸ (⨅ i, I i) ≃+* ∀ i, R ⧸ I i :=
  Ideal.quotientInfRingEquivPiQuotient I (fun i j hij => hI i j hij)

/-- The CRT isomorphism is surjective: every tuple of residues is achievable. -/
theorem crt_general_surjective {ι : Type*} [Finite ι]
    (I : ι → Ideal R) (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) :
    Function.Surjective (crt_general I hI) :=
  (crt_general I hI).surjective

/-- The CRT isomorphism is injective: an element in ⨅ Iᵢ iff zero in every quotient. -/
theorem crt_general_injective {ι : Type*} [Finite ι]
    (I : ι → Ideal R) (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) :
    Function.Injective (crt_general I hI) :=
  (crt_general I hI).injective

-- ============================================================
-- Part IV: CRT for Products (not just Intersections)
-- ============================================================

/-- For coprime ideals, R/(I·J) ≅ R/(I∩J) ≅ (R/I) × (R/J).
    The first equivalence uses I·J = I∩J for coprime ideals. -/
noncomputable def crt_product {I J : Ideal R} (h : IsCoprime I J) :
    R ⧸ (I * J) ≃+* (R ⧸ I) × (R ⧸ J) := by
  have hinf : I ⊓ J = I * J := inf_eq_mul_of_coprime (isCoprime_iff_sup_eq.mp h)
  exact hinf ▸ crt_two I J h

-- ============================================================
-- Part V: Key Corollaries
-- ============================================================

/-- If I and J are coprime and x ≡ a (mod I) and x ≡ b (mod J),
    then x is unique modulo I ∩ J. -/
theorem crt_unique {I J : Ideal R} (_h : IsCoprime I J)
    {x y : R} (hxI : Ideal.Quotient.mk I x = Ideal.Quotient.mk I y)
    (hxJ : Ideal.Quotient.mk J x = Ideal.Quotient.mk J y) :
    Ideal.Quotient.mk (I ⊓ J) x = Ideal.Quotient.mk (I ⊓ J) y := by
  rw [Ideal.Quotient.eq] at hxI hxJ ⊢
  exact Submodule.mem_inf.mpr ⟨hxI, hxJ⟩

/-- Coprimality is symmetric. -/
theorem isCoprime_comm_ideal {I J : Ideal R} (h : IsCoprime I J) :
    IsCoprime J I :=
  h.symm

/-- If I₁ is coprime to both I₂ and I₃, then I₁ is coprime to I₂ ∩ I₃
    (more generally, I₁ is coprime to I₂ · I₃). -/
theorem isCoprime_of_coprime_inf {I J K : Ideal R}
    (hIJ : IsCoprime I J) (hIK : IsCoprime I K) :
    IsCoprime I (J ⊓ K) := by
  -- IsCoprime I J and IsCoprime I K give IsCoprime I (J * K)
  -- Since J * K ≤ J ⊓ K, coprimality with J * K implies coprimality with J ⊓ K
  have hprod : IsCoprime I (J * K) := hIJ.mul_right hIK
  rw [Ideal.isCoprime_iff_sup_eq] at hprod ⊢
  exact top_le_iff.mp (hprod ▸ sup_le_sup_left (Ideal.mul_le_inf) I)

/-
  Summary

  This file formalizes the ideal-theoretic Chinese Remainder Theorem
  with 12 theorems, 0 sorries, 0 axioms.

  Part I: Coprimality characterization (I + J = R ↔ IsCoprime I J)
  Part II: 2-fold CRT (R/(I∩J) ≅ R/I × R/J)
  Part III: k-fold CRT (R/⨅Iᵢ ≅ ∏ R/Iᵢ for finite pairwise coprime family)
  Part IV: Product version (R/(I·J) ≅ R/I × R/J using I·J = I∩J)
  Part V: Corollaries (uniqueness, symmetry, coprimality inheritance)

  Key Insight:
    The abstract CRT is an immediate consequence of
    `Ideal.quotientInfRingEquivPiQuotient` from Mathlib.
    The formalization's value is in:
    1. Making the coprimality conditions explicit and user-friendly
    2. Connecting intersection with product for coprime ideals
    3. Proving coprimality inheritance (I coprime to J,K ⟹ I coprime to J∩K)
       via the lattice distributive law sup_inf_left
-/

end BezoutIdentityCRTIdeals
