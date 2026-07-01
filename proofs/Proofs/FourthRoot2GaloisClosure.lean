/-
Proof: the Galois closure of ℚ(⁴√2) is ℚ(⁴√2, i), a degree-8 extension of ℚ.

Research: fourth-root-2-irrational-oq-01
Parent: fourth-root-2-irrational (⁴√2 has degree 4 over ℚ, X⁴ − 2 irreducible via
Eisenstein + Gauss). The parent's first open question asks for the Galois closure:
since X⁴ − 2 has the non-real roots ±i·⁴√2, its splitting field is ℚ(⁴√2, i), a
degree-8 extension whose Galois group is the dihedral group D₄.

This entry formalizes the DEGREE and the FIELD-THEORETIC STRUCTURE of that closure.
Modeling ⁴√2 as the real number `a = √√2` coerced into ℂ, and adjoining
`i = Complex.I`, we prove the quadratic tower

    ℚ  ⊂  ℚ(⁴√2)  ⊂  ℚ(⁴√2, i)
        (degree 4)   (degree 2)

so that `[ℚ(⁴√2, i) : ℚ] = 8`. The crux is the *strict* second step: `i ∉ ℚ(⁴√2)`.
This is where the "closure" genuinely enlarges the field. Since `a` is real, the
whole field ℚ(⁴√2) lies inside the reals ℝ ⊂ ℂ; but `i` is not real, so it cannot
already be present. We package "lies inside ℝ" as an explicit intermediate field
`realIF : IntermediateField ℚ ℂ` (the complex numbers with zero imaginary part)
and show `ℚ(⁴√2) ≤ realIF < ℂ ∋ i`.

Results:
  * `a_pow_four` / `a_im` — `a⁴ = 2` in ℂ and `a` is real;
  * `minpoly_a` / `finrank_adjoin_a` — `X⁴ − 2 = minpoly ℚ a`, `[ℚ(a) : ℚ] = 4`;
  * `realIF` — the intermediate field ℝ ⊂ ℂ (zero imaginary part);
  * `adjoin_a_le_realIF` — `ℚ(a) ⊆ ℝ`;
  * `I_not_mem_adjoin_a` — **`i ∉ ℚ(⁴√2)`** (the crux; the closure is proper);
  * `minpoly_I_over_adjoin_a` — `X² + 1 = minpoly_{ℚ(a)} i`;
  * `finrank_step_two` — `[ℚ(a)(i) : ℚ(a)] = 2`;
  * `finrank_galois_closure` — **`[ℚ(⁴√2, i) : ℚ] = 8`**;
  * `galois_closure_eq_adjoin_pair` — `ℚ(a)(i) = ℚ(⁴√2, i)` as intermediate fields.

The full identification of the Galois group with D₄ (constructing the 8
automorphisms and the group isomorphism) is left for a follow-up; here we secure
the degree and the tower, which is the quantitative heart of the statement.
-/

import Mathlib
import Proofs.FourthRoot2Degree4

open Polynomial IntermediateField

namespace FourthRoot2GaloisClosure

open scoped Classical

/-- The complex fourth root of 2, the real `⁴√2 = √√2` viewed in ℂ. -/
noncomputable def a : ℂ := (FourthRoot2Degree4.fr2 : ℝ)

/-- `a⁴ = 2` in ℂ, inherited from the real identity `(⁴√2)⁴ = 2`. -/
theorem a_pow_four : a ^ 4 = 2 := by
  have h : (FourthRoot2Degree4.fr2 : ℝ) ^ 4 = 2 := FourthRoot2Degree4.fr2_pow_four
  unfold a
  rw [← Complex.ofReal_pow, h]
  norm_num

/-- `a` is real: its imaginary part vanishes. -/
theorem a_im : a.im = 0 := by
  unfold a; exact Complex.ofReal_im _

/-- `a` is integral over ℚ, a root of the monic polynomial `X⁴ − 2`. -/
theorem a_isIntegral : IsIntegral ℚ a :=
  ⟨X ^ 4 - C 2, monic_X_pow_sub_C _ (by norm_num), by
    simp [a_pow_four]⟩

/-- **`X⁴ − 2` is the minimal polynomial of `a = ⁴√2` over ℚ.** Irreducibility is
the parent result (Eisenstein at 2 + Gauss); `a` is a root; the polynomial is
monic. -/
theorem minpoly_a : minpoly ℚ a = X ^ 4 - C 2 :=
  (minpoly.eq_of_irreducible_of_monic
    FourthRoot2Degree4.irreducible_X4_sub_2_rat
    (by simp [a_pow_four])
    (monic_X_pow_sub_C _ (by norm_num))).symm

theorem minpoly_a_natDegree : (minpoly ℚ a).natDegree = 4 := by
  rw [minpoly_a, natDegree_X_pow_sub_C]

/-- **`[ℚ(⁴√2) : ℚ] = 4`.** -/
theorem finrank_adjoin_a : Module.finrank ℚ ℚ⟮a⟯ = 4 := by
  rw [IntermediateField.adjoin.finrank a_isIntegral, minpoly_a_natDegree]

/-! ### The real subfield ℝ ⊂ ℂ as an intermediate field -/

/-- The subfield of ℂ consisting of numbers with zero imaginary part (a concrete
copy of ℝ inside ℂ). -/
def realSubfield : Subfield ℂ where
  carrier := {z | z.im = 0}
  mul_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Complex.mul_im] at *
    rw [hx, hy]; ring
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, Complex.add_im] at *
    rw [hx, hy]; ring
  zero_mem' := by simp
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, Complex.neg_im] at *
    rw [hx]; ring
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, Complex.inv_im] at *
    rw [hx]; ring

@[simp] theorem mem_realSubfield {z : ℂ} : z ∈ realSubfield ↔ z.im = 0 := Iff.rfl

/-- The reals as an intermediate field `ℚ ⊆ ℝ ⊆ ℂ`. -/
def realIF : IntermediateField ℚ ℂ :=
  realSubfield.toIntermediateField (by
    intro q
    rw [mem_realSubfield]
    simp)

@[simp] theorem mem_realIF {z : ℂ} : z ∈ realIF ↔ z.im = 0 := Iff.rfl

/-- `ℚ(⁴√2) ⊆ ℝ`: every element of `ℚ(⁴√2)` is real, because the generator `a`
is real. -/
theorem adjoin_a_le_realIF : ℚ⟮a⟯ ≤ realIF := by
  rw [IntermediateField.adjoin_le_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx, SetLike.mem_coe, mem_realIF]
  exact a_im

/-- **The crux: `i ∉ ℚ(⁴√2)`.** The closure genuinely enlarges the field. If `i`
were in `ℚ(⁴√2)` it would be real (that field lies in ℝ), but `Im i = 1 ≠ 0`. -/
theorem I_not_mem_adjoin_a : Complex.I ∉ ℚ⟮a⟯ := by
  intro hI
  have : Complex.I ∈ realIF := adjoin_a_le_realIF hI
  rw [mem_realIF, Complex.I_im] at this
  exact one_ne_zero this

/-! ### Second step of the tower: adjoining `i` -/

/-- `i` is integral over `ℚ(⁴√2)`: a root of the monic `X² + 1` (written
`X² − C (−1)` to reuse the `X^n − C a` API). -/
theorem I_isIntegral : IsIntegral ℚ⟮a⟯ Complex.I :=
  ⟨X ^ 2 - C (-1), monic_X_pow_sub_C _ (by norm_num), by
    simp [Complex.I_sq]⟩

/-- `X² + 1` has no root in `ℚ(⁴√2)`: any root would satisfy `x² = −1`, but every
element of `ℚ(⁴√2)` is real, and a real square is nonnegative. -/
theorem X2_add_one_no_root (x : ℚ⟮a⟯) :
    ¬ (X ^ 2 - C (-1 : ℚ⟮a⟯)).IsRoot x := by
  intro hx
  rw [IsRoot.def] at hx
  simp only [eval_sub, eval_pow, eval_X, eval_C, sub_neg_eq_add] at hx
  -- hx : x ^ 2 + 1 = 0 in ↥ℚ⟮a⟯; transport to ℂ
  have hxC : (x : ℂ) ^ 2 + 1 = 0 := by
    have h := congrArg (algebraMap ℚ⟮a⟯ ℂ) hx
    push_cast at h
    simpa using h
  have hreal : (x : ℂ).im = 0 := by
    have hmem : (x : ℂ) ∈ realIF := adjoin_a_le_realIF x.2
    rwa [mem_realIF] at hmem
  have hsq : (x : ℂ) ^ 2 = -1 := by linear_combination hxC
  have hre : ((x : ℂ) ^ 2).re = (-1 : ℂ).re := by rw [hsq]
  rw [pow_two, Complex.mul_re, hreal] at hre
  simp only [Complex.neg_re, Complex.one_re, mul_zero, sub_zero] at hre
  nlinarith [hre, sq_nonneg (x : ℂ).re]

/-- **`X² + 1` is the minimal polynomial of `i` over `ℚ(⁴√2)`.** -/
theorem minpoly_I : minpoly ℚ⟮a⟯ Complex.I = X ^ 2 - C (-1) := by
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_
    (monic_X_pow_sub_C _ (by norm_num))).symm
  · exact irreducible_of_degree_le_three_of_not_isRoot
      (by rw [natDegree_X_pow_sub_C]; decide) X2_add_one_no_root
  · simp [Complex.I_sq]

theorem minpoly_I_natDegree : (minpoly ℚ⟮a⟯ Complex.I).natDegree = 2 := by
  rw [minpoly_I, natDegree_X_pow_sub_C]

/-- **`[ℚ(⁴√2, i) : ℚ(⁴√2)] = 2`.** The second, strict step of the tower. -/
theorem finrank_step_two : Module.finrank ℚ⟮a⟯ ℚ⟮a⟯⟮Complex.I⟯ = 2 := by
  rw [IntermediateField.adjoin.finrank I_isIntegral, minpoly_I_natDegree]

/-! ### The degree of the Galois closure -/

/-- `ℚ(⁴√2)(i)` is finite-dimensional over `ℚ(⁴√2)` (`i` is integral). -/
instance : FiniteDimensional ℚ⟮a⟯ ℚ⟮a⟯⟮Complex.I⟯ :=
  IntermediateField.finiteDimensional_adjoin
    (fun x hx => by rw [Set.mem_singleton_iff] at hx; subst hx; exact I_isIntegral)

set_option synthInstance.maxHeartbeats 1000000 in
/-- `[ℚ(⁴√2, i) : ℚ] = 8`, packaged on the two-step tower `ℚ(⁴√2)(i)`. -/
theorem finrank_tower : Module.finrank ℚ ℚ⟮a⟯⟮Complex.I⟯ = 8 := by
  have h := Module.finrank_mul_finrank (F := ℚ) (K := ℚ⟮a⟯) (A := ℚ⟮a⟯⟮Complex.I⟯)
  rw [finrank_adjoin_a, finrank_step_two] at h
  rw [← h]

/-- `ℚ(⁴√2)(i) = ℚ(⁴√2, i)` as intermediate fields over ℚ. -/
theorem galois_closure_eq_adjoin_pair :
    ℚ⟮a⟯⟮Complex.I⟯.restrictScalars ℚ = ℚ⟮a, Complex.I⟯ :=
  IntermediateField.adjoin_simple_adjoin_simple ℚ a Complex.I

/-- **The Galois closure of `ℚ(⁴√2)` has degree 8 over ℚ.**
`[ℚ(⁴√2, i) : ℚ] = 8`. -/
theorem finrank_galois_closure : Module.finrank ℚ ℚ⟮a, Complex.I⟯ = 8 := by
  rw [← galois_closure_eq_adjoin_pair]
  exact finrank_tower

/-! ### The four roots of `X⁴ − 2` and the splitting set

The closure `ℚ(⁴√2, i)` contains all four roots `±⁴√2, ±i·⁴√2`, so `X⁴ − 2`
splits over it; this is why it is the splitting field. -/

/-- The non-real root `i·⁴√2` also satisfies `z⁴ = 2` (since `i⁴ = 1`). -/
theorem I_mul_a_pow_four : (Complex.I * a) ^ 4 = 2 := by
  have hI4 : Complex.I ^ 4 = 1 := by
    have h : Complex.I ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
    rw [h, Complex.I_sq]; norm_num
  rw [mul_pow, hI4, a_pow_four]; ring

/-- **All four roots `±⁴√2, ±i·⁴√2` of `X⁴ − 2` lie in the closure `ℚ(⁴√2, i)`.**
Hence `X⁴ − 2` splits there. -/
theorem roots_mem_closure :
    a ∈ ℚ⟮a, Complex.I⟯ ∧ (-a) ∈ ℚ⟮a, Complex.I⟯ ∧
      (Complex.I * a) ∈ ℚ⟮a, Complex.I⟯ ∧ (-(Complex.I * a)) ∈ ℚ⟮a, Complex.I⟯ := by
  have ha : a ∈ ℚ⟮a, Complex.I⟯ :=
    IntermediateField.subset_adjoin ℚ {a, Complex.I} (by simp)
  have hI : Complex.I ∈ ℚ⟮a, Complex.I⟯ :=
    IntermediateField.subset_adjoin ℚ {a, Complex.I} (by simp)
  exact ⟨ha, neg_mem ha, mul_mem hI ha, neg_mem (mul_mem hI ha)⟩

end FourthRoot2GaloisClosure
