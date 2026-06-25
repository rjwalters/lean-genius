import Mathlib

/-
# The explicit isomorphism `Gal(ℂ/ℝ) ≃* Multiplicative (ZMod 2)`

## What This Proves

This is the leaf `oq-04-oq-03-oq-01` of `fundamental-theorem-algebra-oq-04`
("ℂ is the unique algebraic closure of ℝ").  The parent leaf
`FundamentalTheoremAlgebraOQ04OQ03` proved, via the Galois correspondence, that
`Gal(ℂ/ℝ)` has **order 2** and is **cyclic** (`IsCyclic`), hence *abstractly*
`≅ ℤ/2ℤ`.  Cyclicity alone is an existence statement: Mathlib's
`zmodCyclicMulEquiv` even produces an isomorphism `Multiplicative (ZMod 2) ≃* G`,
but only by `Classical.choice`-ing some generator — it says nothing about *which*
automorphism the nontrivial element maps to.

This leaf answers the parent's open question OQ[0] by constructing the iso
**explicitly and naming the generator**:

* `galoisGroupEquivZMod2 : (ℂ ≃ₐ[ℝ] ℂ) ≃* Multiplicative (ZMod 2)` — a fully
  spelled-out multiplicative equivalence, no choice of generator hidden inside;
* `galoisGroupEquivZMod2_conjAe` : the iso sends **complex conjugation**
  `Complex.conjAe` to the nontrivial element `Multiplicative.ofAdd 1`;
* `galoisGroupEquivZMod2_symm_ofAdd_one` : conversely, the nontrivial element of
  `Multiplicative (ZMod 2)` is realized by complex conjugation.

The mathematical heart is the elementary structure theorem
`eq_one_or_conjAe`: in the order-2 group `Gal(ℂ/ℝ)` the only automorphisms are the
identity and complex conjugation (a three-distinct-elements counting argument
against `Fintype.card = 2`), together with the involutivity
`conjAe * conjAe = 1` (`Complex.conj_conj`) and the non-triviality
`conjAe ≠ 1` (because `conjAe I = -I ≠ I`).

This pins down the abstract `IsCyclic` of the parent to a concrete labelled
isomorphism, which is exactly the "named iso sending the generator to
conjugation" the open question requested.

This file is self-contained: it re-establishes `IsAlgClosure ℝ ℂ` and
`IsGalois ℝ ℂ` (as the parent does) so it does not depend on the parent's
compiled object file.

*Reference:* Galois theory of `ℂ/ℝ`; Mathlib
`Mathlib.FieldTheory.Galois.Basic`, `Mathlib.Analysis.RCLike.Basic`.
-/

open Complex
open scoped Classical

namespace FTAGaloisIso

/-! ## Setup: ℂ as an algebraic closure of ℝ, and `IsGalois ℝ ℂ` -/

/-- ℂ is algebraic over ℝ (finite extension ⇒ algebraic). -/
instance : Algebra.IsAlgebraic ℝ ℂ := Algebra.IsAlgebraic.of_finite ℝ ℂ

/-- ℂ is an algebraic closure of ℝ — the instance that supplies `Normal ℝ ℂ`. -/
instance : IsAlgClosure ℝ ℂ where
  isAlgClosed := Complex.isAlgClosed
  isAlgebraic := inferInstance

/-- **`ℂ / ℝ` is a Galois extension.** Finite + separable (char 0) + normal
    (algebraic closure). -/
instance galois_complex_real : IsGalois ℝ ℂ := IsGalois.mk

/-- **`|Gal(ℂ/ℝ)| = 2`.** For a Galois extension the automorphism group has order
    equal to the degree, and `[ℂ:ℝ] = 2`. -/
theorem card_galoisGroup_eq_two : Nat.card (ℂ ≃ₐ[ℝ] ℂ) = 2 := by
  rw [IsGalois.card_aut_eq_finrank ℝ ℂ, Complex.finrank_real_complex]

/-! ## The two automorphisms: identity and complex conjugation -/

/-- **Complex conjugation is a nontrivial automorphism.** It moves `I` to `-I`. -/
theorem conjAe_ne_one : (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ) ≠ 1 := by
  intro h
  have h2 := DFunLike.congr_fun h Complex.I
  rw [AlgEquiv.one_apply] at h2
  -- `conjAe I = conj I = -I`, so `-I = I`, forcing `I = 0`.
  rw [Complex.conjAe_coe, Complex.conj_I] at h2
  have h3 : (2 : ℂ) * Complex.I = 0 := by linear_combination -h2
  rw [mul_eq_zero] at h3
  rcases h3 with h | h
  · norm_num at h
  · exact Complex.I_ne_zero h

/-- **Complex conjugation is an involution:** `conjAe * conjAe = 1`. -/
theorem conjAe_mul_self : (Complex.conjAe : ℂ ≃ₐ[ℝ] ℂ) * Complex.conjAe = 1 := by
  ext z
  simp [AlgEquiv.mul_apply, Complex.conjAe_coe]

/-- **Structure of `Gal(ℂ/ℝ)`.** The only `ℝ`-automorphisms of `ℂ` are the identity
    and complex conjugation. Proof: a third distinct automorphism would give three
    elements in a group of order `2`. -/
theorem eq_one_or_conjAe (g : ℂ ≃ₐ[ℝ] ℂ) : g = 1 ∨ g = Complex.conjAe := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, hc⟩ := hcon
  have hcard : Fintype.card (ℂ ≃ₐ[ℝ] ℂ) = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact card_galoisGroup_eq_two
  have hsub : ({1, Complex.conjAe, g} : Finset (ℂ ≃ₐ[ℝ] ℂ)).card ≤ 2 := by
    rw [← hcard]; exact Finset.card_le_univ _
  have e1 : (1 : ℂ ≃ₐ[ℝ] ℂ) ∉ ({Complex.conjAe, g} : Finset (ℂ ≃ₐ[ℝ] ℂ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => conjAe_ne_one h.symm, fun h => h1 h.symm⟩
  have e2 : Complex.conjAe ∉ ({g} : Finset (ℂ ≃ₐ[ℝ] ℂ)) := by
    simp only [Finset.mem_singleton]; exact fun h => hc h.symm
  rw [Finset.card_insert_of_notMem e1, Finset.card_insert_of_notMem e2,
    Finset.card_singleton] at hsub
  omega

/-! ## Helper facts in `Multiplicative (ZMod 2)` -/

/-- The nontrivial element `ofAdd 1` of `Multiplicative (ZMod 2)` is not the unit. -/
theorem ofAdd_one_ne_one : (Multiplicative.ofAdd (1 : ZMod 2)) ≠ 1 := by decide

/-- `Multiplicative (ZMod 2)` has exactly the two elements `1` and `ofAdd 1`. -/
theorem zmod2_eq_one_or (x : Multiplicative (ZMod 2)) :
    x = 1 ∨ x = Multiplicative.ofAdd 1 := by revert x; decide

/-! ## The explicit isomorphism -/

/-- **The explicit isomorphism `Gal(ℂ/ℝ) ≃* Multiplicative (ZMod 2)`.**
    The identity maps to the unit and complex conjugation maps to the nontrivial
    element `ofAdd 1`. Unlike `zmodCyclicMulEquiv`, every component is spelled out;
    no generator is chosen by `Classical.choice`. -/
noncomputable def galoisGroupEquivZMod2 : (ℂ ≃ₐ[ℝ] ℂ) ≃* Multiplicative (ZMod 2) where
  toFun g := if g = 1 then 1 else Multiplicative.ofAdd 1
  invFun x := if x = 1 then 1 else Complex.conjAe
  left_inv g := by
    rcases eq_one_or_conjAe g with h | h
    · subst h; simp
    · subst h
      simp only [if_neg conjAe_ne_one, if_neg ofAdd_one_ne_one]
  right_inv x := by
    rcases zmod2_eq_one_or x with h | h
    · subst h; simp
    · subst h
      simp only [if_neg ofAdd_one_ne_one, if_neg conjAe_ne_one]
  map_mul' a b := by
    rcases eq_one_or_conjAe a with ha | ha <;> rcases eq_one_or_conjAe b with hb | hb <;>
      subst ha <;> subst hb
    · simp
    · simp
    · simp
    · -- conjAe * conjAe = 1
      rw [conjAe_mul_self]
      simp only [if_neg conjAe_ne_one]
      decide

/-- **The iso sends complex conjugation to the nontrivial element `ofAdd 1`.** -/
@[simp] theorem galoisGroupEquivZMod2_conjAe :
    galoisGroupEquivZMod2 Complex.conjAe = Multiplicative.ofAdd 1 :=
  if_neg conjAe_ne_one

/-- **The iso sends the identity to the unit.** -/
@[simp] theorem galoisGroupEquivZMod2_one :
    galoisGroupEquivZMod2 1 = 1 :=
  map_one galoisGroupEquivZMod2

/-- **The nontrivial element of `Multiplicative (ZMod 2)` is complex conjugation.** -/
theorem galoisGroupEquivZMod2_symm_ofAdd_one :
    galoisGroupEquivZMod2.symm (Multiplicative.ofAdd 1) = Complex.conjAe := by
  rw [MulEquiv.symm_apply_eq, galoisGroupEquivZMod2_conjAe]

end FTAGaloisIso
