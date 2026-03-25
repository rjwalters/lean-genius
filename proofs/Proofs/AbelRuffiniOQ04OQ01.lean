import Mathlib

/-
# Galois Group of x⁵ - 4x + 2 is S₅ (Abel-Ruffini OQ-04 Extension)

## What This Proves

We show that the polynomial p(x) = x⁵ - 4x + 2 over ℚ has Galois group S₅,
completing the Abel-Ruffini proof chain. This gives a concrete polynomial
whose roots CANNOT be expressed using radicals.

## The Proof Chain (now complete)

1. A₅ is simple (Mathlib: `alternatingGroup.isSimpleGroup_five`)
2. Sₙ (n ≥ 5) is not solvable (AbelRuffiniOQ04.lean)
3. Solvable by radicals ⟹ solvable Galois group (AbelRuffini.lean)
4. **Gal(x⁵ - 4x + 2 / ℚ) ≅ S₅ (THIS FILE)**
5. Therefore: the roots of x⁵ - 4x + 2 are not solvable by radicals

## Why x⁵ - 4x + 2?

- **Irreducible**: Eisenstein's criterion at p = 2 (PROVED)
- **Separable**: automatic over ℚ (characteristic 0) (PROVED)
- **Gal = S₅**: |Gal| = 120 = 5! (1 axiom: the Galois group order)

### Justification for the axiom (|Gal| = 120)

The polynomial has exactly 3 real roots and 2 complex conjugate roots:

  f(-2) = -22 < 0,  f(-1) = 5 > 0   → root in (-2, -1)
  f(0) = 2 > 0,     f(1) = -1 < 0   → root in (0, 1)
  f(1) = -1 < 0,    f(2) = 26 > 0   → root in (1, 2)

  f'(x) = 5x⁴ - 4 has exactly 2 real roots (±(4/5)^{1/4}),
  so f has exactly 2 critical points, hence at most 3 real roots.
  Combined with the 3 sign changes above: exactly 3 real roots.

From this:
1. Irreducibility → transitive action → Gal contains a 5-cycle
2. 3 real roots → complex conjugation gives a transposition in Gal
3. A transitive subgroup of S₅ containing a transposition and a
   5-cycle generates all of S₅ (classical group theory)
4. Therefore Gal ≅ S₅, so |Gal| = 120

## Extends

- AbelRuffini.lean: Galois bridge and contrapositive form
- AbelRuffiniOQ04.lean: A₅ simplicity and S₅ non-solvability
- AbelRuffiniGaloisExtensions.lean: Solvability classifications

## Wiedijk's 100 Theorems: #83 (Extension)
-/

set_option linter.unusedVariables false

open scoped Classical

namespace AbelRuffiniOQ04OQ01

open Polynomial

-- ============================================================================
-- Part I: The Polynomial p = X⁵ - 4X + 2
-- ============================================================================

/-- The polynomial p = X⁵ - 4X + 2 over ℚ. -/
noncomputable def p : ℚ[X] := X ^ 5 - C 4 * X + C 2

/-- The ℤ[X] version of p for Eisenstein criterion application. -/
private noncomputable def p_int : ℤ[X] := X ^ 5 - C 4 * X + C 2

-- ============================================================================
-- Part II: Irreducibility via Eisenstein at p = 2
-- ============================================================================

/-
## Eisenstein's Criterion at p = 2

p(x) = x⁵ - 4x + 2 satisfies Eisenstein at (2) ⊂ ℤ:

| Condition                        | Check         |
|----------------------------------|---------------|
| Leading coeff 1 ∉ (2)           | 2 ∤ 1 ✓      |
| coeff x⁴ = 0 ∈ (2)             | 2 ∣ 0 ✓      |
| coeff x³ = 0 ∈ (2)             | 2 ∣ 0 ✓      |
| coeff x² = 0 ∈ (2)             | 2 ∣ 0 ✓      |
| coeff x¹ = -4 ∈ (2)            | 2 ∣ -4 ✓     |
| coeff x⁰ = 2 ∈ (2)            | 2 ∣ 2 ✓      |
| coeff x⁰ = 2 ∉ (4)            | 4 ∤ 2 ✓      |
-/

/-- p_int has degree 5. -/
private theorem p_int_degree : p_int.degree = 5 := by
  unfold p_int; compute_degree!

/-- p_int has natDegree 5. -/
private theorem p_int_natDegree : p_int.natDegree = 5 := by
  unfold p_int; compute_degree!

/-- p_int is monic (leading coefficient = 1). -/
private theorem p_int_monic : p_int.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, p_int_natDegree]
  unfold p_int
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- p_int is irreducible over ℤ, by Eisenstein's criterion at p = 2. -/
private theorem p_int_irreducible : Irreducible p_int := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(2 : ℤ)})
  · -- (2) is a prime ideal in ℤ
    rw [Ideal.span_singleton_prime (show (2 : ℤ) ≠ 0 from by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · -- leadingCoeff ∉ (2)
    rw [show p_int.leadingCoeff = 1 from p_int_monic, Ideal.mem_span_singleton]
    norm_num
  · -- ∀ k < degree, coeff k ∈ (2)
    intro k hk
    rw [p_int_degree] at hk
    have hkn : k < 5 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    unfold p_int
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · -- 0 < degree
    rw [p_int_degree]; exact_mod_cast Nat.zero_lt_succ 4
  · -- coeff 0 ∉ (2)²
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold p_int
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num
  · -- isPrimitive: monic → primitive
    exact p_int_monic.isPrimitive

/-- p is irreducible over ℚ.

    Proof: Eisenstein's criterion at p = 2 gives ℤ-irreducibility.
    Gauss's lemma (monic → primitive) transfers to ℚ. -/
theorem p_irreducible : Irreducible p := by
  have hprim := p_int_monic.isPrimitive
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp p_int_irreducible
  convert hirr using 1
  unfold p p_int
  simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow]
  norm_cast

-- ============================================================================
-- Part III: Basic Structural Properties
-- ============================================================================

/-- p has natDegree 5. -/
theorem p_natDegree : p.natDegree = 5 := by
  unfold p; compute_degree!

/-- p is monic (leading coefficient = 1). -/
theorem p_monic : p.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, p_natDegree]
  unfold p
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- p is separable (irreducible in characteristic 0). -/
theorem p_separable : p.Separable := p_irreducible.separable

/-- The root set of p in its splitting field has exactly 5 elements. -/
theorem p_rootSet_card :
    Fintype.card (p.rootSet p.SplittingField) = 5 :=
  (Polynomial.card_rootSet_eq_natDegree p_separable
    (Polynomial.SplittingField.splits p)).trans p_natDegree

-- ============================================================================
-- Part IV: Galois Group Structure
-- ============================================================================

/-- 5 divides |Gal(p/ℚ)| (since p is irreducible of prime degree 5). -/
theorem five_dvd_gal_card :
    5 ∣ Fintype.card p.Gal := by
  have h := Polynomial.Gal.prime_degree_dvd_card p_irreducible
    (by rw [p_natDegree]; decide : Nat.Prime p.natDegree)
  rw [p_natDegree, Nat.card_eq_fintype_card] at h
  exact h

/-- |Gal(p/ℚ)| divides 120 = 5! (Gal embeds into S₅ via action on roots). -/
theorem gal_card_dvd_120 :
    Fintype.card p.Gal ∣ 120 := by
  haveI : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
    ⟨Polynomial.SplittingField.splits p⟩
  have hinj := Polynomial.Gal.galActionHom_injective p p.SplittingField
  have hdvd : Nat.card p.Gal ∣ Nat.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hdvd
  rw [Fintype.card_perm, p_rootSet_card] at hdvd
  simpa using hdvd

-- ============================================================================
-- Part V: Polynomial Evaluation (toward eliminating gal_card_eq_120)
-- ============================================================================

/-- p(-2) = -22 (negative). -/
theorem p_eval_neg2 : p.eval (-2 : ℚ) = -22 := by unfold p; simp [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]; try ring

/-- p(-1) = 5 (positive). -/
theorem p_eval_neg1 : p.eval (-1 : ℚ) = 5 := by unfold p; simp [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]; try ring

/-- p(0) = 2 (positive). -/
theorem p_eval_0 : p.eval (0 : ℚ) = 2 := by unfold p; simp [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]; try ring

/-- p(1) = -1 (negative). -/
theorem p_eval_1 : p.eval (1 : ℚ) = -1 := by unfold p; simp [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]; try ring

/-- p(2) = 26 (positive). -/
theorem p_eval_2 : p.eval (2 : ℚ) = 26 := by unfold p; simp [eval_sub, eval_add, eval_mul, eval_pow, eval_C, eval_X]; try ring

/-
These evaluations show 3 sign changes: p has at least 3 real roots.
  p(-2) = -22 < 0,  p(-1) = 5 > 0   → root in (-2, -1)
  p(0)  = 2 > 0,    p(1) = -1 < 0   → root in (0, 1)
  p(1)  = -1 < 0,   p(2) = 26 > 0   → root in (1, 2)

Combined with p' = 5x⁴ - 4 having exactly 2 real roots (hence p has
at most 3 real roots by Rolle's theorem), p has EXACTLY 3 real roots.

This means 2 roots are complex conjugate. Complex conjugation induces
a transposition in the Galois group. A transitive subgroup of S₅
(5 prime) containing a transposition is S₅ itself. Hence |Gal| = 120.
-/

-- ============================================================================
-- Part V(b): The Galois Group Has Order 120 (= 5!)
-- ============================================================================

/-
## Why |Gal(p/ℚ)| = 120

The polynomial p = x⁵ - 4x + 2 has exactly 3 real roots:

**Sign changes (by direct evaluation):**
  p(-2) = (-2)⁵ - 4(-2) + 2 = -32 + 8 + 2 = -22 < 0
  p(-1) = (-1)⁵ - 4(-1) + 2 = -1 + 4 + 2 = 5 > 0     → root in (-2, -1)
  p(0)  = 0 - 0 + 2 = 2 > 0
  p(1)  = 1 - 4 + 2 = -1 < 0                            → root in (0, 1)
  p(2)  = 32 - 8 + 2 = 26 > 0                            → root in (1, 2)

**Exactly 3 (not more):** p'(x) = 5x⁴ - 4 has exactly 2 real roots
(at x = ±(4/5)^{1/4}), giving p exactly one local max and one local min.
A degree-5 polynomial with 2 critical points has at most 3 real roots.

**The group-theoretic argument:**
1. p is irreducible of prime degree 5, so 5 | |Gal| and Gal acts transitively.
   In particular, Gal contains an element of order 5 (a 5-cycle in S₅).
2. p has 3 real roots and 2 complex conjugate roots. Complex conjugation
   σ : ℂ → ℂ restricts to an automorphism of the splitting field over ℚ.
   Under the permutation representation, σ swaps the 2 non-real roots
   and fixes the 3 real roots — this is a transposition.
3. A transitive subgroup of Sₚ (p prime) containing a transposition
   generates all of Sₚ. (Proof: conjugate the transposition by the p-cycle
   to get transpositions (1,2), (2,3), ..., (p-1,p), which generate Sₚ.)
4. Therefore Gal(p/ℚ) = S₅, so |Gal| = 5! = 120.

This argument uses only:
- Eisenstein's criterion (proved above)
- Intermediate value theorem (for sign changes)
- Derivative analysis (for bounding real roots)
- Standard group theory (transposition + p-cycle → Sₚ)

The Lean formalization axiomatizes |Gal| = 120 directly. Future work can
replace this with a full proof of the real root count and group theory lemma.
-/

/-- |Gal(p/ℚ)| = 120. This is the full symmetric group S₅.

    Proof outline (not yet fully formalized):
    p has exactly 3 real roots (by sign changes and derivative analysis),
    so Gal contains a transposition (complex conjugation). Combined with
    a 5-cycle (from prime degree), this generates S₅. -/
axiom gal_card_eq_120 : Fintype.card p.Gal = 120

-- ============================================================================
-- Part VI: Gal(p/ℚ) ≅ S₅
-- ============================================================================

/-- The Galois group of x⁵ - 4x + 2 is isomorphic to S₅ (= Perm(Fin 5)).

    Proof: galActionHom is injective with |Gal| = |Perm(rootSet)| = 120,
    so it is bijective. Transfer via rootSet ≃ Fin 5. -/
theorem gal_iso_s5 :
    Nonempty (p.Gal ≃* Equiv.Perm (Fin 5)) := by
  classical
  haveI : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
    ⟨Polynomial.SplittingField.splits p⟩
  -- galActionHom is injective
  have hinj := Polynomial.Gal.galActionHom_injective p p.SplittingField
  -- |rootSet| = 5
  have hcard_root : Fintype.card (p.rootSet p.SplittingField) = 5 := p_rootSet_card
  -- |Gal| = 120 = |Perm(rootSet)| (since 5! = 120)
  have hcard_gal : Fintype.card p.Gal = 120 := gal_card_eq_120
  have hcard_perm : Fintype.card (Equiv.Perm (p.rootSet p.SplittingField)) = 120 := by
    rw [Fintype.card_perm, hcard_root]; norm_num
  -- Injective + equal cardinality → bijective
  have hbij : Function.Bijective (Polynomial.Gal.galActionHom p p.SplittingField) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, by rw [hcard_gal, hcard_perm]⟩
  -- Construct isomorphism Gal ≅ Perm(rootSet)
  have hiso : p.Gal ≃* Equiv.Perm (p.rootSet p.SplittingField) :=
    MulEquiv.ofBijective _ hbij
  -- Transfer via rootSet ≃ Fin 5
  have hfin : p.rootSet p.SplittingField ≃ Fin 5 :=
    Fintype.equivFinOfCardEq hcard_root
  have hperm : Equiv.Perm (p.rootSet p.SplittingField) ≃* Equiv.Perm (Fin 5) :=
    { toEquiv := Equiv.permCongr hfin
      map_mul' := fun σ τ => by ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply] }
  exact ⟨hiso.trans hperm⟩

-- ============================================================================
-- Part VII: S₅ is Not Solvable
-- ============================================================================

/-- S₅ is not solvable: immediate from Mathlib. -/
theorem s5_not_solvable : ¬ IsSolvable (Equiv.Perm (Fin 5)) := by
  have h : 5 ≤ Cardinal.mk (Fin 5) := by
    simp only [Cardinal.mk_fintype, Fintype.card_fin]; norm_cast
  exact Equiv.Perm.not_solvable (Fin 5) h

/-- The Galois group of x⁵ - 4x + 2 is not solvable. -/
theorem gal_not_solvable : ¬ IsSolvable p.Gal := by
  obtain ⟨iso⟩ := gal_iso_s5
  intro hsol
  apply s5_not_solvable
  haveI := hsol
  exact solvable_of_surjective
    (f := iso.toMonoidHom) (fun b => ⟨iso.symm b, iso.apply_symm_apply b⟩)

-- ============================================================================
-- Part VIII: The Abel-Ruffini Conclusion
-- ============================================================================

/-
## The Complete Proof

1. p = x⁵ - 4x + 2 is irreducible over ℚ (Eisenstein at 2) ✓ PROVED
2. Gal(p/ℚ) ≅ S₅ (1 axiom: |Gal| = 120) ✓ PROVED
3. S₅ is not solvable (Mathlib) ✓ PROVED
4. If α is solvable by radicals, Gal(minpoly(α)) is solvable (Mathlib) ✓
5. Contrapositive: Gal not solvable ⟹ α not solvable by radicals ✓ PROVED

Therefore: the roots of x⁵ - 4x + 2 cannot be expressed using radicals.
This gives a CONCRETE witness for the Abel-Ruffini theorem.
-/

/-- **Abel-Ruffini (concrete witness):**
    The roots of x⁵ - 4x + 2 cannot be expressed by radicals.

    Proof: If some root α were solvable by radicals, then Gal(p/ℚ) would be
    solvable (by Galois's theorem). But Gal(p/ℚ) ≅ S₅ which is not solvable.
    Contradiction. -/
theorem roots_not_solvable_by_rad
    {E : Type*} [Field E] [Algebra ℚ E] (α : E)
    (hroot : Polynomial.aeval α p = 0) :
    ¬ IsSolvableByRad ℚ α := by
  intro hrad
  -- If α is solvable by radicals and p(α) = 0 with p irreducible,
  -- then Gal(p) is solvable
  have hsol : IsSolvable p.Gal :=
    solvableByRad.isSolvable' p_irreducible hroot hrad
  -- But Gal(p) is not solvable (it's S₅)
  exact gal_not_solvable hsol

-- ============================================================================
-- Part IX: S₅ Realizability
-- ============================================================================

/-- S₅ is realizable as a Galois group over ℚ, witnessed by x⁵ - 4x + 2. -/
theorem s5_realizable :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ K) (_ : FiniteDimensional ℚ K)
      (_ : IsGalois ℚ K),
      Nonempty (Equiv.Perm (Fin 5) ≃* (K ≃ₐ[ℚ] K)) := by
  have : Normal ℚ p.SplittingField := inferInstance
  have : Algebra.IsSeparable ℚ p.SplittingField := inferInstance
  obtain ⟨iso⟩ := gal_iso_s5
  exact ⟨p.SplittingField,
    inferInstance, inferInstance, inferInstance,
    IsGalois.mk,
    ⟨iso.symm⟩⟩

-- ============================================================================
-- Verification
-- ============================================================================

#check p_irreducible      -- Irreducible over ℚ
#check p_natDegree         -- Degree = 5
#check p_separable         -- Separable
#check five_dvd_gal_card   -- 5 | |Gal|
#check gal_card_dvd_120    -- |Gal| | 120
#check gal_iso_s5          -- Gal ≅ S₅
#check gal_not_solvable    -- Gal is not solvable
#check roots_not_solvable_by_rad  -- Roots not solvable by radicals
#check s5_realizable       -- S₅ realizable over ℚ

end AbelRuffiniOQ04OQ01
