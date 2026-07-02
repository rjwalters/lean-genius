import Proofs.FourthRoot2GaloisClosure

/-
# The Galois closure of ℚ(⁴√2) is Galois of degree 8: |Gal(ℚ(⁴√2, i)/ℚ)| = 8
  (fourth-root-2-irrational OQ-03)

The parent entry `FourthRoot2GaloisClosure.lean` (research
`fourth-root-2-irrational-oq-01`) builds the quadratic tower
`ℚ ⊂ ℚ(⁴√2) ⊂ ℚ(⁴√2, i)` and secures the **degree** `[ℚ(⁴√2, i) : ℚ] = 8`, but
it explicitly defers the *group-theoretic* content:

> "The full identification of the Galois group with D₄ (constructing the 8
> automorphisms and the group isomorphism) is left for a follow-up; here we
> secure the degree and the tower."

This file supplies the quantitative heart of that deferred step — the fact that
`ℚ(⁴√2, i)` is a **Galois** extension of ℚ and that its automorphism group has
**order exactly 8**:

  * `isSplittingField`   — `X⁴ − 2` has `ℚ(⁴√2, i)` as its splitting field over ℚ;
  * `isGalois`           — hence `ℚ(⁴√2, i) / ℚ` is Galois (separable + normal);
  * `normal`             — the normality half, packaged separately;
  * `card_gal`           — `#Gal(ℚ(⁴√2, i)/ℚ) = 8`.

`card_gal` is the exact prerequisite for the D₄ identification: the Galois group
is a group of order 8, and Galois theory now guarantees it acts faithfully with
`ℚ` as its fixed field. Pinning `#Gal = [K : ℚ] = 8` is the step Galois theory
adds on top of the parent's pure degree computation.

## Method

`ℚ(⁴√2, i)` is generated over ℚ by the four roots `±⁴√2, ±i·⁴√2` of `X⁴ − 2`:
each satisfies `z⁴ = 2`, and conversely `z⁴ = 2 = (⁴√2)⁴` forces
`(z / ⁴√2)⁴ = 1`, so `z / ⁴√2` is a fourth root of unity `∈ {1, −1, i, −i}` and
`z ∈ {±⁴√2, ±i·⁴√2}` (the factorisation
`z⁴ − a⁴ = (z−a)(z+a)(z−ia)(z+ia)`, valid because `i² = −1`).  Hence
`adjoin ℚ (rootSet (X⁴−2)) = ℚ(⁴√2, i)`, which is Mathlib's definition of a
splitting field; `X⁴ − 2` is separable (irreducible over the characteristic-zero
field ℚ, being `minpoly ℚ (⁴√2)`), so the splitting field is Galois, and
`IsGalois.card_aut_eq_finrank` turns the parent's degree `8` into `#Gal = 8`.

Zero axioms; reuses only Mathlib and the parent `FourthRoot2GaloisClosure`.
-/

open Polynomial IntermediateField FourthRoot2GaloisClosure

namespace FourthRoot2GaloisClosureOQ03

open scoped Classical

/-- The defining polynomial `X⁴ − 2 ∈ ℚ[X]`. -/
noncomputable def p : ℚ[X] := X ^ 4 - C 2

/-- `X⁴ − 2 = minpoly ℚ (⁴√2)`, hence irreducible over ℚ. -/
theorem p_irreducible : Irreducible p := by
  have h : p = minpoly ℚ a := minpoly_a.symm
  rw [h]
  exact minpoly.irreducible a_isIntegral

theorem p_ne_zero : p ≠ 0 := p_irreducible.ne_zero

/-- `X⁴ − 2` is separable: it is irreducible over the characteristic-zero field ℚ. -/
theorem p_separable : p.Separable := p_irreducible.separable

/-- `⁴√2 ≠ 0`, since `(⁴√2)⁴ = 2 ≠ 0`. -/
theorem a_ne_zero : a ≠ 0 := fun h => by simpa [h] using a_pow_four

/-- `⁴√2` is a root of `X⁴ − 2`. -/
theorem a_mem_rootSet : a ∈ p.rootSet ℂ := by
  rw [mem_rootSet]
  refine ⟨p_ne_zero, ?_⟩
  simp only [p, map_sub, map_pow, aeval_X, map_ofNat]
  rw [a_pow_four]; norm_num

/-- `i·⁴√2` is a root of `X⁴ − 2`. -/
theorem Ia_mem_rootSet : Complex.I * a ∈ p.rootSet ℂ := by
  rw [mem_rootSet]
  refine ⟨p_ne_zero, ?_⟩
  simp only [p, map_sub, map_pow, aeval_X, map_ofNat]
  rw [I_mul_a_pow_four]; norm_num

/-- The splitting set of `X⁴ − 2` in ℂ generates exactly `ℚ(⁴√2, i)`. -/
theorem adjoin_rootSet_eq : adjoin ℚ (p.rootSet ℂ) = ℚ⟮a, Complex.I⟯ := by
  apply le_antisymm
  · -- `adjoin ℚ (rootSet) ≤ ℚ(⁴√2, i)`: every root `z` (`z⁴ = 2`) lies in the closure.
    rw [adjoin_le_iff]
    intro z hz
    rw [mem_rootSet] at hz
    have hz4 : z ^ 4 = 2 := by
      have h0 := hz.2
      simp only [p, map_sub, map_pow, aeval_X, map_ofNat, sub_eq_zero] at h0
      exact h0
    have key : (z - a) * (z + a) * (z - Complex.I * a) * (z + Complex.I * a)
        = z ^ 4 - a ^ 4 := by
      have h := Complex.I_sq
      linear_combination (a ^ 4 - a ^ 2 * z ^ 2) * h
    have hzero : (z - a) * (z + a) * (z - Complex.I * a) * (z + Complex.I * a) = 0 := by
      rw [key, hz4, a_pow_four]; norm_num
    obtain ⟨hA, hnA, hIA, hnIA⟩ := roots_mem_closure
    rcases mul_eq_zero.mp hzero with h | h4
    · rcases mul_eq_zero.mp h with h | h3
      · rcases mul_eq_zero.mp h with h1 | h2
        · rw [sub_eq_zero] at h1; rw [h1]; exact hA
        · rw [add_eq_zero_iff_eq_neg] at h2; rw [h2]; exact hnA
      · rw [sub_eq_zero] at h3; rw [h3]; exact hIA
    · rw [add_eq_zero_iff_eq_neg] at h4; rw [h4]; exact hnIA
  · -- `ℚ(⁴√2, i) ≤ adjoin ℚ (rootSet)`: `⁴√2` and `i` both lie in the adjoined field.
    have ha_mem : a ∈ adjoin ℚ (p.rootSet ℂ) := subset_adjoin ℚ _ a_mem_rootSet
    have hIa_mem : Complex.I * a ∈ adjoin ℚ (p.rootSet ℂ) := subset_adjoin ℚ _ Ia_mem_rootSet
    have hI_eq : Complex.I * a * a⁻¹ = Complex.I := by
      rw [mul_assoc, mul_inv_cancel₀ a_ne_zero, mul_one]
    have hI_mem : Complex.I ∈ adjoin ℚ (p.rootSet ℂ) :=
      hI_eq ▸ mul_mem hIa_mem (inv_mem ha_mem)
    rw [adjoin_le_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨ha_mem, hI_mem⟩

/-- `X⁴ − 2` has `ℚ(⁴√2, i)` as a splitting field over ℚ. -/
theorem isSplittingField : p.IsSplittingField ℚ ℚ⟮a, Complex.I⟯ := by
  have hsplit : (p.map (algebraMap ℚ ℂ)).Splits := IsAlgClosed.splits_codomain p
  have inst : p.IsSplittingField ℚ (adjoin ℚ (p.rootSet ℂ)) :=
    IntermediateField.adjoin_rootSet_isSplittingField hsplit
  rwa [adjoin_rootSet_eq] at inst

/-- **The Galois closure `ℚ(⁴√2, i)` is Galois over ℚ.** -/
instance isGalois : IsGalois ℚ ℚ⟮a, Complex.I⟯ := by
  haveI : p.IsSplittingField ℚ ℚ⟮a, Complex.I⟯ := isSplittingField
  exact IsGalois.of_separable_splitting_field p_separable

/-- The normality half of `isGalois`, packaged separately. -/
theorem normal : Normal ℚ ℚ⟮a, Complex.I⟯ := IsGalois.to_normal

/-- `ℚ(⁴√2, i) / ℚ` is finite-dimensional: as a splitting field it is finite over ℚ.
This supplies the `Fintype` instance on the Galois group needed by `card_gal`. -/
instance finiteDimensional : FiniteDimensional ℚ ℚ⟮a, Complex.I⟯ := by
  haveI := isSplittingField
  exact Polynomial.IsSplittingField.finiteDimensional ℚ⟮a, Complex.I⟯ p

/-- **The Galois group of `ℚ(⁴√2, i)` over ℚ has order 8.**
`#Gal(ℚ(⁴√2, i)/ℚ) = [ℚ(⁴√2, i) : ℚ] = 8`.  This is the group-order input to the
`D₄` identification, obtained by combining the parent's degree computation with
the Galois property proved here. -/
theorem card_gal :
    Fintype.card (ℚ⟮a, Complex.I⟯ ≃ₐ[ℚ] ℚ⟮a, Complex.I⟯) = 8 := by
  rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank ℚ ℚ⟮a, Complex.I⟯]
  exact finrank_galois_closure

end FourthRoot2GaloisClosureOQ03
