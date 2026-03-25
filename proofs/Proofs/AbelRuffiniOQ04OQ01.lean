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
- **Gal = S₅**: |Gal| = 120 = 5! (PROVED from 2 transparent axioms)

### Proof that |Gal| = 120 (Axiom Decomposition)

The original opaque axiom gal_card_eq_120 has been decomposed into two
narrower, well-motivated axioms plus a complete proof:

**Axiom A (Dedekind at p = 13):** 3 | |Gal(p/ℚ)|.
  x⁵ - 4x + 2 mod 13 factors as (x-2)(x-5)(x³+7x²+8) where the cubic
  is irreducible over F₁₃ (no roots by exhaustive check). By Dedekind's
  theorem, Gal contains a Frobenius element with cycle type (1,1,3),
  hence an element of order divisible by 3.

**Axiom B (Discriminant non-square):** Gal(p/ℚ) ⊄ A₅.
  disc(p) = Res(p, p') = -212144 < 0. Since ∏(rᵢ-rⱼ)² = disc(p) < 0,
  the Vandermonde product Δ = ∏(rⱼ-rᵢ) satisfies Δ² < 0 in ℚ, so Δ ∉ ℚ.
  Since σ(Δ) = sign(σ)·Δ and Δ ∉ ℚ, some σ has sign(σ) = -1.

**Theorem (from A + B + existing results):**
  5 | |Gal| (proved), 3 | |Gal| (A), |Gal| | 120 (proved).
  So 15 | |Gal| and |Gal| ∈ {15, 30, 60, 120}.
  - Not 15: no subgroup of S₅ has order 15 (Sylow theory + native_decide)
  - Not 30: no subgroup of S₅ has order 30 (A₅ simplicity)
  - Not 60: A₅ is the unique subgroup of S₅ of order 60, but Gal ⊄ A₅ (B)
  Therefore |Gal| = 120.

## Extends

- AbelRuffini.lean: Galois bridge and contrapositive form
- AbelRuffiniOQ04.lean: A₅ simplicity and S₅ non-solvability
- AbelRuffiniGaloisExtensions.lean: Solvability classifications

## Wiedijk's 100 Theorems: #83 (Extension)
-/

set_option linter.unusedVariables false

-- ============================================================================
-- Computational Lemmas (BEFORE `open scoped Classical` for native_decide)
-- ============================================================================

/-- No element of order 5 commutes with any element of order 3 in S₅.
    Used to prove no subgroup of S₅ has order 15. -/
theorem perm_fin5_order5_order3_not_commute :
    ∀ (σ τ : Equiv.Perm (Fin 5)),
      σ ^ 5 = 1 → σ ≠ 1 → τ ^ 3 = 1 → τ ≠ 1 → σ * τ ≠ τ * σ := by
  native_decide

/-- No element of S₅ has order 15. -/
theorem perm_fin5_no_order_15 :
    ∀ σ : Equiv.Perm (Fin 5), σ ^ 15 = 1 → σ ^ 5 = 1 ∨ σ ^ 3 = 1 := by
  native_decide

/-- x⁵ - 4x + 2 ≡ 0 (mod 13) when x = 2.
    Verification: 2⁵ - 4·2 + 2 = 32 - 8 + 2 = 26 = 2·13. -/
theorem p_root_mod13_at_2 : (2 ^ 5 - 4 * 2 + 2 : ZMod 13) = 0 := by native_decide

/-- x⁵ - 4x + 2 ≡ 0 (mod 13) when x = 5.
    Verification: 5⁵ - 4·5 + 2 = 3125 - 20 + 2 = 3107 = 239·13. -/
theorem p_root_mod13_at_5 : (5 ^ 5 - 4 * 5 + 2 : ZMod 13) = 0 := by native_decide

/-- The cubic residue x³ + 7x² + 8 has no roots mod 13.
    (Exhaustive check: all 13 values of x give nonzero residue.) -/
theorem cubic_factor_no_roots_mod13 :
    ∀ x : ZMod 13, x ^ 3 + 7 * x ^ 2 + 8 ≠ 0 := by native_decide

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
-- Part V(b): Group Theory — 5-Cycle + Transposition Generates S₅
-- ============================================================================

/-
## Key Group Theory Lemma

A transitive subgroup of S₅ containing a transposition is S₅.

**Proof**: By conjugating the transposition with the 5-cycle (guaranteed by
transitivity + prime degree), we generate all 10 transpositions. Since every
permutation is a product of transpositions, the subgroup is S₅.

The chain:
  1. swap(k, k+1) = c₅ᵏ · swap(0,1) · c₅⁻ᵏ          (adjacent swaps)
  2. swap(0, k+1) = swap(0,k) · swap(k,k+1) · swap(0,k)  (star swaps)
  3. swap(a, b) = swap(0,a) · swap(0,b) · swap(0,a)       (all swaps)
-/

-- The standard 5-cycle (0 1 2 3 4)
private def c5 : Equiv.Perm (Fin 5) where
  toFun := fun i => ⟨(i.val + 1) % 5, Nat.mod_lt _ (by omega)⟩
  invFun := fun i => ⟨(i.val + 4) % 5, Nat.mod_lt _ (by omega)⟩
  left_inv := by intro ⟨i, hi⟩; simp [Fin.ext_iff]; omega
  right_inv := by intro ⟨i, hi⟩; simp [Fin.ext_iff]; omega

/-- The closure of a 5-cycle and a transposition in S₅ is all of S₅.

    Proof: Conjugation generates all transpositions; every permutation
    is a product of transpositions (Equiv.Perm.swap_induction_on). -/
private theorem closure_cycle_swap_eq_top :
    Subgroup.closure ({c5, Equiv.swap (0 : Fin 5) 1} : Set (Equiv.Perm (Fin 5))) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  -- Every permutation is a product of swaps
  -- Helper: show every swap is in the closure
  suffices hsw : ∀ a b : Fin 5, a ≠ b →
      Equiv.swap a b ∈ Subgroup.closure ({c5, Equiv.swap (0 : Fin 5) 1} : Set (Equiv.Perm (Fin 5))) by
    induction g using Equiv.Perm.swap_induction_on with
    | one => exact Subgroup.one_mem _
    | swap_mul f a b hab ih => exact Subgroup.mul_mem _ (hsw a b hab) (ih trivial)
  -- Prove all 10 transpositions are in the closure
  intro a b hab
  set S := Subgroup.closure ({c5, Equiv.swap (0 : Fin 5) 1} : Set (Equiv.Perm (Fin 5)))
  -- Generators are in S
  have hc : c5 ∈ S := Subgroup.subset_closure (Set.mem_insert _ _)
  have hs01 : Equiv.swap (0 : Fin 5) 1 ∈ S :=
    Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inr rfl))
  -- Adjacent swaps via c5-conjugation (verified computationally)
  have hs12 : Equiv.swap (1 : Fin 5) 2 ∈ S := by
    have : c5 * Equiv.swap (0 : Fin 5) 1 * c5⁻¹ = Equiv.swap (1 : Fin 5) 2 := by native_decide
    rw [← this]; exact S.mul_mem (S.mul_mem hc hs01) (S.inv_mem hc)
  have hs23 : Equiv.swap (2 : Fin 5) 3 ∈ S := by
    have : c5 ^ 2 * Equiv.swap (0 : Fin 5) 1 * (c5 ^ 2)⁻¹ = Equiv.swap (2 : Fin 5) 3 := by
      native_decide
    rw [← this]; exact S.mul_mem (S.mul_mem (S.pow_mem hc 2) hs01) (S.inv_mem (S.pow_mem hc 2))
  have hs34 : Equiv.swap (3 : Fin 5) 4 ∈ S := by
    have : c5 ^ 3 * Equiv.swap (0 : Fin 5) 1 * (c5 ^ 3)⁻¹ = Equiv.swap (3 : Fin 5) 4 := by
      native_decide
    rw [← this]; exact S.mul_mem (S.mul_mem (S.pow_mem hc 3) hs01) (S.inv_mem (S.pow_mem hc 3))
  -- Star swaps via double conjugation
  have hs02 : Equiv.swap (0 : Fin 5) 2 ∈ S := by
    have : Equiv.swap (0 : Fin 5) 1 * Equiv.swap (1 : Fin 5) 2 *
      Equiv.swap (0 : Fin 5) 1 = Equiv.swap (0 : Fin 5) 2 := by native_decide
    rw [← this]; exact S.mul_mem (S.mul_mem hs01 hs12) hs01
  have hs03 : Equiv.swap (0 : Fin 5) 3 ∈ S := by
    have : Equiv.swap (0 : Fin 5) 2 * Equiv.swap (2 : Fin 5) 3 *
      Equiv.swap (0 : Fin 5) 2 = Equiv.swap (0 : Fin 5) 3 := by native_decide
    rw [← this]; exact S.mul_mem (S.mul_mem hs02 hs23) hs02
  have hs04 : Equiv.swap (0 : Fin 5) 4 ∈ S := by
    have : Equiv.swap (0 : Fin 5) 3 * Equiv.swap (3 : Fin 5) 4 *
      Equiv.swap (0 : Fin 5) 3 = Equiv.swap (0 : Fin 5) 4 := by native_decide
    rw [← this]; exact S.mul_mem (S.mul_mem hs03 hs34) hs03
  -- Remaining swaps via star conjugation
  have hs13 : Equiv.swap (1 : Fin 5) 3 ∈ S := by
    have : Equiv.swap (0 : Fin 5) 1 * Equiv.swap (0 : Fin 5) 3 *
      Equiv.swap (0 : Fin 5) 1 = Equiv.swap (1 : Fin 5) 3 := by native_decide
    rw [← this]; exact S.mul_mem (S.mul_mem hs01 hs03) hs01
  have hs14 : Equiv.swap (1 : Fin 5) 4 ∈ S := by
    have : Equiv.swap (0 : Fin 5) 1 * Equiv.swap (0 : Fin 5) 4 *
      Equiv.swap (0 : Fin 5) 1 = Equiv.swap (1 : Fin 5) 4 := by native_decide
    rw [← this]; exact S.mul_mem (S.mul_mem hs01 hs04) hs01
  have hs24 : Equiv.swap (2 : Fin 5) 4 ∈ S := by
    have : Equiv.swap (0 : Fin 5) 2 * Equiv.swap (0 : Fin 5) 4 *
      Equiv.swap (0 : Fin 5) 2 = Equiv.swap (2 : Fin 5) 4 := by native_decide
    rw [← this]; exact S.mul_mem (S.mul_mem hs02 hs04) hs02
  -- Case-split on a, b to select the right swap
  fin_cases a <;> fin_cases b <;> simp_all <;> first
    | exact hs01 | exact hs02 | exact hs03 | exact hs04
    | exact hs12 | exact hs13 | exact hs14
    | exact hs23 | exact hs24 | exact hs34
    | (rw [Equiv.swap_comm]; assumption)

-- ============================================================================
-- Part V(c): Galois Group Infrastructure
-- ============================================================================

/-- The splitting field is a Galois extension. -/
instance : Normal ℚ p.SplittingField := inferInstance
instance : Algebra.IsSeparable ℚ p.SplittingField := inferInstance

/-- The map (algebraMap ...) p splits in the splitting field. -/
instance p_splits_fact : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
  ⟨Polynomial.SplittingField.splits p⟩

/-- Permutation homomorphism from Gal(p) to Perm(rootSet) using galActionAux.
    Uses galActionAux (direct action) to avoid an instance diamond between
    galActionAux and galAction when E = SplittingField. -/
private noncomputable def galPermHomAux : p.Gal →* Equiv.Perm (p.rootSet p.SplittingField) :=
  @MulAction.toPermHom _ _ _ (@Polynomial.Gal.galActionAux ℚ _ p)

/-- galPermHomAux is injective — the Galois group acts faithfully on roots. -/
private theorem galPermHomAux_injective : Function.Injective galPermHomAux := by
  rw [injective_iff_map_eq_one]
  intro ϕ hϕ
  ext (x hx)
  exact congrArg Subtype.val (Equiv.Perm.ext_iff.mp hϕ ⟨x, hx⟩)

/-- Composite injection Gal(p) →* Perm(Fin 5) via root enumeration. -/
noncomputable def galToPerm5 : p.Gal →* Equiv.Perm (Fin 5) :=
  let rootEquiv : p.rootSet p.SplittingField ≃ Fin 5 :=
    Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin])
  let permEquiv : Equiv.Perm (p.rootSet p.SplittingField) ≃* Equiv.Perm (Fin 5) :=
    { toEquiv := Equiv.permCongr rootEquiv
      map_mul' := fun σ τ => by
        ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply] }
  permEquiv.toMonoidHom.comp galPermHomAux

/-- galToPerm5 is injective. -/
theorem galToPerm5_injective : Function.Injective galToPerm5 := by
  unfold galToPerm5
  exact (Equiv.permCongr
    (Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]))).injective.comp
    galPermHomAux_injective

/-- The sign of a Galois element in S₅. -/
noncomputable def galSign (σ : p.Gal) : ℤˣ :=
  Equiv.Perm.sign (galToPerm5 σ)

-- ============================================================================
-- Part V(d): Structural Lemmas — No Subgroups of Order 15 or 30 in S₅
-- ============================================================================

/-- No subgroup of S₅ has order 15.

    Proof: In any group of order 15 = 3·5, Sylow theory gives unique
    normal P₅ and P₃. Their elements commute. But no order-5 element
    commutes with any order-3 element in S₅ (native_decide). -/
theorem no_subgroup_order_15 (H : Subgroup (Equiv.Perm (Fin 5)))
    (hcard : Nat.card H = 15) : False := by
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI hft : Fintype H := Fintype.ofFinite H
  have hcard_ft : Fintype.card H = 15 := by rwa [Nat.card_eq_fintype_card] at hcard
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card (p := 5)
    (show 5 ∣ Fintype.card H by rw [hcard_ft]; norm_num)
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card (p := 3)
    (show 3 ∣ Fintype.card H by rw [hcard_ft]; norm_num)
  have hσ5 : (σ : Equiv.Perm (Fin 5)) ^ 5 = 1 := by
    have : σ ^ 5 = (1 : ↥H) :=
      calc σ ^ 5 = σ ^ orderOf σ := by congr 1; exact hσ.symm
        _ = 1 := pow_orderOf_eq_one σ
    simpa using congr_arg Subtype.val this
  have hσ_ne : (σ : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro heq
    exact absurd hσ (by rw [show σ = (1 : ↥H) from Subtype.ext heq, orderOf_one]; norm_num)
  have hτ3 : (τ : Equiv.Perm (Fin 5)) ^ 3 = 1 := by
    have : τ ^ 3 = (1 : ↥H) :=
      calc τ ^ 3 = τ ^ orderOf τ := by congr 1; exact hτ.symm
        _ = 1 := pow_orderOf_eq_one τ
    simpa using congr_arg Subtype.val this
  have hτ_ne : (τ : Equiv.Perm (Fin 5)) ≠ 1 := by
    intro heq
    exact absurd hτ (by rw [show τ = (1 : ↥H) from Subtype.ext heq, orderOf_one]; norm_num)
  exact perm_fin5_order5_order3_not_commute _ _ hσ5 hσ_ne hτ3 hτ_ne (by
    suffices hsuff : (σ : ↥H) * τ = τ * σ by
      have h1 := congr_arg Subtype.val hsuff
      simp only [Subgroup.coe_mul] at h1; exact h1
    have hn₅ : Nat.card (Sylow 5 ↥H) = 1 := by
      have h_mod := card_sylow_modEq_one 5 ↥H
      obtain ⟨P⟩ := Sylow.nonempty (p := 5) (G := ↥H)
      have h_P_card : Nat.card (↑P : Subgroup ↥H) = 5 := by
        rw [P.card_eq_multiplicity, hcard]; native_decide
      have h_idx : (↑P : Subgroup ↥H).index = 3 := by
        have := (↑P : Subgroup ↥H).index_mul_card; rw [h_P_card, hcard] at this; omega
      have h_dvd := Sylow.card_dvd_index P; rw [h_idx] at h_dvd
      rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd _ h_dvd with h | h
      · exact h
      · exfalso; rw [h] at h_mod; simp [Nat.ModEq] at h_mod
    haveI : Subsingleton (Sylow 5 ↥H) := by
      haveI := Fintype.ofFinite (Sylow 5 ↥H)
      rw [← Fintype.card_le_one_iff_subsingleton, ← Nat.card_eq_fintype_card]; omega
    have hn₃ : Nat.card (Sylow 3 ↥H) = 1 := by
      have h_mod := card_sylow_modEq_one 3 ↥H
      obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := ↥H)
      have h_P_card : Nat.card (↑P : Subgroup ↥H) = 3 := by
        rw [P.card_eq_multiplicity, hcard]; native_decide
      have h_idx : (↑P : Subgroup ↥H).index = 5 := by
        have := (↑P : Subgroup ↥H).index_mul_card; rw [h_P_card, hcard] at this; omega
      have h_dvd := Sylow.card_dvd_index P; rw [h_idx] at h_dvd
      rcases (by norm_num : Nat.Prime 5).eq_one_or_self_of_dvd _ h_dvd with h | h
      · exact h
      · exfalso; rw [h] at h_mod; simp [Nat.ModEq] at h_mod
    haveI : Subsingleton (Sylow 3 ↥H) := by
      haveI := Fintype.ofFinite (Sylow 3 ↥H)
      rw [← Fintype.card_le_one_iff_subsingleton, ← Nat.card_eq_fintype_card]; omega
    obtain ⟨P₅⟩ := Sylow.nonempty (p := 5) (G := ↥H)
    obtain ⟨P₃⟩ := Sylow.nonempty (p := 3) (G := ↥H)
    haveI hN₅ : (↑P₅ : Subgroup ↥H).Normal := by
      apply Subgroup.Normal.mk; intro n hn g
      have : g • P₅ = P₅ := Subsingleton.elim _ _
      rw [Sylow.smul_eq_iff_mem_normalizer] at this
      exact ((Subgroup.mem_normalizer_iff.mp this) n).mp hn
    haveI hN₃ : (↑P₃ : Subgroup ↥H).Normal := by
      apply Subgroup.Normal.mk; intro n hn g
      have : g • P₃ = P₃ := Subsingleton.elim _ _
      rw [Sylow.smul_eq_iff_mem_normalizer] at this
      exact ((Subgroup.mem_normalizer_iff.mp this) n).mp hn
    have hσ_mem : σ ∈ (↑P₅ : Subgroup ↥H) := by
      have h_pg : IsPGroup 5 (Subgroup.zpowers σ) :=
        IsPGroup.iff_card.mpr ⟨1, by rw [pow_one, Nat.card_zpowers, hσ]⟩
      obtain ⟨Q, hQ⟩ := h_pg.exists_le_sylow
      exact (show Q = P₅ from Subsingleton.elim Q P₅) ▸ hQ (Subgroup.mem_zpowers σ)
    have hτ_mem : τ ∈ (↑P₃ : Subgroup ↥H) := by
      have h_pg : IsPGroup 3 (Subgroup.zpowers τ) :=
        IsPGroup.iff_card.mpr ⟨1, by rw [pow_one, Nat.card_zpowers, hτ]⟩
      obtain ⟨Q, hQ⟩ := h_pg.exists_le_sylow
      exact (show Q = P₃ from Subsingleton.elim Q P₃) ▸ hQ (Subgroup.mem_zpowers τ)
    set c := σ * τ * σ⁻¹ * τ⁻¹ with hc_def
    have hc₅ : c ∈ (↑P₅ : Subgroup ↥H) := by
      rw [hc_def]; show σ * τ * σ⁻¹ * τ⁻¹ ∈ ↑P₅
      have := hN₅.conj_mem σ⁻¹ ((↑P₅ : Subgroup ↥H).inv_mem hσ_mem) τ
      have hprod := (↑P₅ : Subgroup ↥H).mul_mem hσ_mem this
      convert hprod using 1
    have hc₃ : c ∈ (↑P₃ : Subgroup ↥H) := by
      rw [hc_def]; show σ * τ * σ⁻¹ * τ⁻¹ ∈ ↑P₃
      have := hN₃.conj_mem τ hτ_mem σ
      exact (↑P₃ : Subgroup ↥H).mul_mem this ((↑P₃ : Subgroup ↥H).inv_mem hτ_mem)
    have hc_one : c = 1 := by
      have ⟨k₅, hk₅⟩ := P₅.isPGroup' ⟨c, hc₅⟩
      have ⟨k₃, hk₃⟩ := P₃.isPGroup' ⟨c, hc₃⟩
      have h5 : orderOf c ∣ 5 ^ k₅ := orderOf_dvd_of_pow_eq_one (by
        simpa using congr_arg Subtype.val hk₅)
      have h3 : orderOf c ∣ 3 ^ k₃ := orderOf_dvd_of_pow_eq_one (by
        simpa using congr_arg Subtype.val hk₃)
      have hcop : Nat.Coprime (5 ^ k₅) (3 ^ k₃) := (by norm_num : Nat.Coprime 5 3).pow k₅ k₃
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd h5 h3))
    rw [show σ * τ = c * (τ * σ) from by simp only [hc_def]; group, hc_one, one_mul])

/-- A₅ has 60 elements. -/
theorem a5_card : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
  native_decide

/-- No subgroup of S₅ has order 30.

    Proof: If H ≤ S₅ has |H| = 30, then H ∩ A₅ has order 15 or 30.
    Order 30 → H ⊆ A₅, index 2, normal, contradicts A₅ simple.
    Order 15 → contradicts no_subgroup_order_15. -/
theorem no_subgroup_order_30 (H : Subgroup (Equiv.Perm (Fin 5)))
    (hcard : Nat.card H = 30) : False := by
  haveI : Finite H := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : Fintype H := Fintype.ofFinite H
  by_cases hle : H ≤ alternatingGroup (Fin 5)
  · let H' := H.subgroupOf (alternatingGroup (Fin 5))
    have hH'_card : Nat.card ↥H' = 30 := by
      rw [show Nat.card ↥H' = Nat.card ↥H from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hcard]
    have hA5_card : Nat.card (alternatingGroup (Fin 5) : Type _) = 60 := by
      rw [Nat.card_eq_fintype_card]; decide
    have hindex : H'.index = 2 := by
      have := Subgroup.card_mul_index H'
      rw [hA5_card, hH'_card] at this; omega
    haveI : H'.Normal := Subgroup.normal_of_index_eq_two hindex
    rcases alternatingGroup.isSimpleGroup_five.eq_bot_or_eq_top_of_normal H' inferInstance
      with h | h
    · rw [h] at hH'_card; simp at hH'_card
    · rw [h, Nat.card_congr Subgroup.topEquiv.toEquiv, hA5_card] at hH'_card
      norm_num at hH'_card
  · obtain ⟨x, hxH, hxA⟩ : ∃ x ∈ H, x ∉ alternatingGroup (Fin 5) := by
      by_contra h; push_neg at h; exact hle h
    let signH : ↥H →* ℤˣ := Equiv.Perm.sign.comp H.subtype
    let K := signH.ker.map H.subtype
    have hK_card : Nat.card ↥K = 15 := by
      have h_eq : Nat.card ↥K = Nat.card ↥signH.ker :=
        (Nat.card_congr
          (signH.ker.equivMapOfInjective H.subtype Subtype.val_injective).toEquiv).symm
      rw [h_eq]
      have h_mul := Subgroup.card_mul_index signH.ker
      have h_idx_dvd : signH.ker.index ∣ 2 := by
        have h_iso : signH.ker.index = Nat.card ↥signH.range := by
          rw [Subgroup.index]
          exact Nat.card_congr (QuotientGroup.quotientKerEquivRange signH).toEquiv
        rw [h_iso]
        calc Nat.card ↥signH.range
            ∣ Nat.card ℤˣ := Subgroup.card_subgroup_dvd_card signH.range
          _ = 2 := by rw [Nat.card_eq_fintype_card]; decide
      have h_idx_ne : signH.ker.index ≠ 1 := by
        intro heq
        have hker_top : signH.ker = ⊤ := Subgroup.index_eq_one.mp heq
        have : (⟨x, hxH⟩ : ↥H) ∈ signH.ker := hker_top ▸ Subgroup.mem_top _
        rw [MonoidHom.mem_ker] at this
        simp only [signH, MonoidHom.comp_apply, Subgroup.coe_subtype] at this
        exact hxA (Equiv.Perm.mem_alternatingGroup.mpr this)
      have h_idx : signH.ker.index = 2 :=
        (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ h_idx_dvd).resolve_left h_idx_ne
      rw [hcard, h_idx] at h_mul; omega
    exact no_subgroup_order_15 K hK_card

-- ============================================================================
-- Part V(e): Vandermonde Product and Discriminant → Odd Permutation
-- ============================================================================

/-
## Vandermonde Product Approach

The Vandermonde product Δ = det(vandermonde(rootEnum)) satisfies:
  σ(Δ) = sign(σ) · Δ for every σ ∈ Gal(p/ℚ).

If Δ² ∈ ℚ is not a perfect square, then Δ ∉ ℚ, so some σ has sign(σ) = -1.

For p = x⁵ - 4x + 2: disc(p) = Δ² = -212144 < 0 (not a perfect square in ℚ),
so Gal(p) contains an odd permutation (Gal ⊄ A₅).

The approach follows InverseGaloisA5.lean's Vandermonde infrastructure.
-/

-- Abbreviation for the splitting field
private abbrev SF := p.SplittingField

-- Section E1: Root Enumeration
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- Canonical enumeration of the 5 roots of p in its splitting field. -/
noncomputable def rootEnum : Fin 5 → SF :=
  fun i => ((Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]) :
    p.rootSet p.SplittingField ≃ Fin 5).symm i : SF)

/-- Each value of rootEnum is a root of p. -/
theorem rootEnum_is_root (i : Fin 5) :
    Polynomial.aeval (rootEnum i) p = 0 := by
  unfold rootEnum
  have hmem := ((Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]) :
    p.rootSet p.SplittingField ≃ Fin 5).symm i).prop
  rw [Polynomial.mem_rootSet] at hmem
  exact hmem.2

/-- The roots are distinct (p is separable). -/
theorem rootEnum_injective : Function.Injective rootEnum := by
  intro i j hij
  unfold rootEnum at hij
  have hsub : (Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]) :
    p.rootSet p.SplittingField ≃ Fin 5).symm i =
    (Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]) :
    p.rootSet p.SplittingField ≃ Fin 5).symm j := Subtype.ext hij
  exact (Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin]) :
    p.rootSet p.SplittingField ≃ Fin 5).symm.injective hsub

-- Section E2: Vandermonde Product
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- The Vandermonde product of p's roots:
    Δ = det(vandermonde(rootEnum)) = ∏_{i<j} (rootEnum j - rootEnum i). -/
noncomputable def vandermondeProduct : SF :=
  Matrix.det (Matrix.vandermonde rootEnum)

/-- The Vandermonde product is nonzero (since p is separable, all roots are distinct). -/
theorem vandermondeProduct_ne_zero : vandermondeProduct ≠ 0 := by
  unfold vandermondeProduct
  rw [Matrix.det_vandermonde]
  intro h
  rw [Finset.prod_eq_zero_iff] at h
  obtain ⟨i, _, hi⟩ := h
  rw [Finset.prod_eq_zero_iff] at hi
  obtain ⟨j, hj, hij⟩ := hi
  have hne : j ≠ i := by simp [Finset.mem_Iio] at hj; omega
  exact hne (rootEnum_injective (sub_eq_zero.mp hij))

-- Section E3: Galois Action on Vandermonde Product
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- The Galois group permutes roots according to galToPerm5. -/
theorem gal_permutes_roots (σ : p.Gal) (i : Fin 5) :
    σ (rootEnum i) = rootEnum (galToPerm5 σ i) := by
  unfold rootEnum galToPerm5 galPermHomAux
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.coe_mk,
    Equiv.toFun_as_coe, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    MulAction.toPermHom_apply]
  rfl

/-- Vandermonde with permuted input = row-permuted Vandermonde. -/
private theorem vandermonde_comp_eq_submatrix
    (v : Fin 5 → SF) (π : Equiv.Perm (Fin 5)) :
    Matrix.vandermonde (v ∘ π) = (Matrix.vandermonde v).submatrix π id := by
  ext i j; simp [Matrix.vandermonde, Matrix.submatrix, Function.comp]

/-- Vandermonde permutation: det(V(v ∘ π)) = sign(π) · det(V(v)). -/
private theorem vandermonde_perm_det
    (v : Fin 5 → SF) (π : Equiv.Perm (Fin 5)) :
    (Matrix.vandermonde (v ∘ π)).det =
    ↑↑(Equiv.Perm.sign π) * (Matrix.vandermonde v).det := by
  rw [vandermonde_comp_eq_submatrix]
  exact Matrix.det_permute π (Matrix.vandermonde v)

/-- σ maps the Vandermonde matrix entry-wise according to root permutation. -/
private theorem gal_map_vandermonde_entry (σ : p.Gal) (i j : Fin 5) :
    σ ((Matrix.vandermonde rootEnum) i j) =
    (Matrix.vandermonde (rootEnum ∘ galToPerm5 σ)) i j := by
  simp only [Matrix.vandermonde, Matrix.of_apply, Function.comp]
  rw [map_pow]
  congr 1
  exact gal_permutes_roots σ i

/-- **σ(Δ) = galSign(σ) · Δ** — the Galois action on the Vandermonde determinant
    equals the sign of the induced permutation times the determinant. -/
theorem gal_acts_on_vandermondeProduct (σ : p.Gal) :
    σ vandermondeProduct = ↑↑(galSign σ) * vandermondeProduct := by
  unfold vandermondeProduct galSign
  trans (Matrix.vandermonde (rootEnum ∘ galToPerm5 σ)).det
  · change σ.toAlgHom.toRingHom (Matrix.vandermonde rootEnum).det =
      (Matrix.vandermonde (rootEnum ∘ galToPerm5 σ)).det
    rw [RingHom.map_det]
    congr 1; ext i j
    simp only [RingHom.mapMatrix_apply]
    change σ ((Matrix.vandermonde rootEnum) i j) =
      (Matrix.vandermonde (rootEnum ∘ galToPerm5 σ)) i j
    exact gal_map_vandermonde_entry σ i j
  · exact vandermonde_perm_det rootEnum (galToPerm5 σ)

-- Section E4: Discriminant Value (Axiom)
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- **Axiom (discriminant computation)**: Δ² = -212144 in the splitting field.

    This is a verifiable computation: disc(x⁵-4x+2) = 256(-4)⁵+3125·2⁴ = -212144.
    The Sylvester matrix of p and p' = 5x⁴-4 is a 9×9 integer matrix whose
    determinant equals -212144.

    Axiomatized because computing resultants of explicit polynomials requires
    API that is not yet available in Lean4/Mathlib v4.26.0. -/
axiom vandermondeProduct_sq_val :
  vandermondeProduct ^ 2 = algebraMap ℚ SF (-212144)

-- Section E5: Negative Discriminant → Odd Permutation
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- The Vandermonde product is NOT in the range of algebraMap ℚ SF.

    Proof: Δ² = algebraMap ℤ SF (-212144). If Δ = algebraMap ℚ SF r for some r,
    then r² = -212144 in ℚ. But r² ≥ 0 in ℚ (characteristic 0, ordered field),
    contradiction. -/
theorem vandermondeProduct_not_rational :
    vandermondeProduct ∉ Set.range (algebraMap ℚ SF) := by
  intro ⟨r, hr⟩
  have hinj : Function.Injective (algebraMap ℚ SF) := (algebraMap ℚ SF).injective
  have hr2 : r ^ 2 = (-212144 : ℚ) := hinj (by rw [map_pow, hr]; exact vandermondeProduct_sq_val)
  linarith [sq_nonneg r]

/-- Helper: in the Galois splitting field, elements fixed by ALL automorphisms
    lie in the base field ℚ.

    This is one direction of the Fundamental Theorem of Galois Theory.
    Proof: fixingSubgroup(⊥) = ⊤ (every ℚ-alg. aut. fixes ℚ), and by
    IsGalois.fixedField_fixingSubgroup, fixedField(fixingSubgroup(⊥)) = ⊥. -/
private theorem fixed_by_all_gal_is_rational (x : SF)
    (hfix : ∀ σ : SF ≃ₐ[ℚ] SF, σ x = x) :
    x ∈ Set.range (algebraMap ℚ SF) := by
  haveI : IsGalois ℚ SF := IsGalois.mk
  -- x ∈ fixedField(⊤)
  have hmem : x ∈ IntermediateField.fixedField (⊤ : Subgroup (SF ≃ₐ[ℚ] SF)) := by
    rw [IntermediateField.mem_fixedField_iff]
    exact fun σ _ => hfix σ
  -- fixingSubgroup(⊥) = ⊤: every automorphism fixes ℚ
  have hfix_bot : (⊥ : IntermediateField ℚ SF).fixingSubgroup = ⊤ := by
    rw [eq_top_iff]; intro σ _ y
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp y.prop
    show σ • (y : SF) = (y : SF)
    rw [show (y : SF) = algebraMap ℚ SF r from hr.symm]
    exact σ.commutes r
  -- fixedField(fixingSubgroup(⊥)) = ⊥ (FTGT)
  have hftgt : IntermediateField.fixedField (⊤ : Subgroup (SF ≃ₐ[ℚ] SF)) = ⊥ := by
    rw [← hfix_bot]; exact IsGalois.fixedField_fixingSubgroup ⊥
  rw [hftgt] at hmem
  exact IntermediateField.mem_bot.mp hmem

/-- Not all Galois signs are positive: some σ has galSign(σ) = -1.

    Proof: If all signs were +1, then σ(Δ) = Δ for all σ, which would mean
    Δ is fixed by the entire Galois group, hence Δ ∈ ℚ. But Δ ∉ ℚ. -/
theorem exists_odd_galSign :
    ∃ σ : p.Gal, galSign σ = -1 := by
  by_contra hall
  push_neg at hall
  have hall_one : ∀ σ : p.Gal, galSign σ = 1 := fun σ =>
    (Int.units_eq_one_or (galSign σ)).resolve_right (hall σ)
  have hfix : ∀ σ : p.Gal, σ vandermondeProduct = vandermondeProduct := by
    intro σ
    have h := gal_acts_on_vandermondeProduct σ
    rw [hall_one σ] at h; simpa using h
  exact vandermondeProduct_not_rational (fixed_by_all_gal_is_rational vandermondeProduct hfix)

/-- **THEOREM** (formerly Axiom B): The Galois group contains an odd permutation.
    Proved from the Vandermonde product approach and disc(p) = -212144 < 0. -/
theorem gal_has_odd_perm :
  ∃ σ : p.Gal, Equiv.Perm.sign (galToPerm5 σ) = -1 := exists_odd_galSign

-- Section E6: Remaining Axiom
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~

/-- **Axiom A**: 3 divides |Gal(p)|.

    By Dedekind's theorem at p = 13: x⁵-4x+2 mod 13 factors as
    (x-2)(x-5)(x³+7x²+8) where the cubic is irreducible over F₁₃
    (no roots: cubic_factor_no_roots_mod13). The Frobenius element
    at 13 has cycle type (1,1,3), hence order divisible by 3.

    Axiomatized because Mathlib lacks Dedekind's theorem.
    Supporting evidence: p_root_mod13_at_2, p_root_mod13_at_5,
    cubic_factor_no_roots_mod13 verify the factorization. -/
axiom three_dvd_gal_card : 3 ∣ Fintype.card p.Gal

-- ============================================================================
-- Part V(f): |Gal(p/ℚ)| = 120 (PROVED from Axioms A, B)
-- ============================================================================

/-- |Gal(p)| ≠ 15: Gal embeds into S₅ which has no subgroup of order 15. -/
private theorem gal_card_ne_15 : Fintype.card p.Gal ≠ 15 := by
  intro hc
  let rootEquiv : p.rootSet p.SplittingField ≃ Fin 5 :=
    Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin])
  let permEquiv : Equiv.Perm (p.rootSet p.SplittingField) ≃* Equiv.Perm (Fin 5) :=
    { toEquiv := Equiv.permCongr rootEquiv
      map_mul' := fun σ τ => by
        ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply] }
  let φ := permEquiv.toMonoidHom.comp (Polynomial.Gal.galActionHom p p.SplittingField)
  have hinj : Function.Injective φ :=
    permEquiv.injective.comp (Polynomial.Gal.galActionHom_injective p p.SplittingField)
  exact no_subgroup_order_15 φ.range (by
    rw [show Nat.card φ.range = Nat.card p.Gal from
      Nat.card_congr (Equiv.ofBijective φ.rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h),
         φ.rangeRestrict_surjective⟩).symm,
      Nat.card_eq_fintype_card, hc])

/-- |Gal(p)| ≠ 30: Gal embeds into S₅ which has no subgroup of order 30. -/
private theorem gal_card_ne_30 : Fintype.card p.Gal ≠ 30 := by
  intro hc
  let rootEquiv : p.rootSet p.SplittingField ≃ Fin 5 :=
    Fintype.equivOfCardEq (by rw [p_rootSet_card, Fintype.card_fin])
  let permEquiv : Equiv.Perm (p.rootSet p.SplittingField) ≃* Equiv.Perm (Fin 5) :=
    { toEquiv := Equiv.permCongr rootEquiv
      map_mul' := fun σ τ => by
        ext x; simp [Equiv.permCongr_apply, Equiv.Perm.mul_apply] }
  let φ := permEquiv.toMonoidHom.comp (Polynomial.Gal.galActionHom p p.SplittingField)
  have hinj : Function.Injective φ :=
    permEquiv.injective.comp (Polynomial.Gal.galActionHom_injective p p.SplittingField)
  exact no_subgroup_order_30 φ.range (by
    rw [show Nat.card φ.range = Nat.card p.Gal from
      Nat.card_congr (Equiv.ofBijective φ.rangeRestrict
        ⟨fun a b h => hinj (congrArg Subtype.val h),
         φ.rangeRestrict_surjective⟩).symm,
      Nat.card_eq_fintype_card, hc])

/-- |Gal(p)| ≠ 60: the unique subgroup of S₅ of order 60 is A₅,
    but Gal(p) ⊄ A₅ (Axiom B). -/
private theorem gal_card_ne_60 : Fintype.card p.Gal ≠ 60 := by
  intro hc
  -- galToPerm5 is an injection into Perm(Fin 5)
  -- Image has cardinality 60, so image ≅ A₅ (unique order-60 subgroup)
  have hrange_card : Nat.card galToPerm5.range = 60 := by
    rw [show Nat.card galToPerm5.range = Nat.card p.Gal from
      Nat.card_congr (Equiv.ofBijective galToPerm5.rangeRestrict
        ⟨fun a b h => galToPerm5_injective (congrArg Subtype.val h),
         galToPerm5.rangeRestrict_surjective⟩).symm,
      Nat.card_eq_fintype_card, hc]
  -- A subgroup of S₅ of order 60 must be ≤ A₅
  -- (A₅ has index 2, so any element of G outside A₅ would create a surjection
  --  G → ℤ/2 with kernel G ∩ A₅ of order 30, contradicting no_subgroup_order_30)
  have hle : galToPerm5.range ≤ alternatingGroup (Fin 5) := by
    by_contra hle_neg
    have ⟨x, hxG, hxA⟩ : ∃ x ∈ galToPerm5.range, x ∉ alternatingGroup (Fin 5) := by
      by_contra h; push_neg at h; exact hle_neg h
    let signG : ↥galToPerm5.range →* ℤˣ := Equiv.Perm.sign.comp galToPerm5.range.subtype
    let K := signG.ker.map galToPerm5.range.subtype
    -- K = galToPerm5.range ∩ A₅, has order 30 (index 2)
    have hK_card : Nat.card ↥K = 30 := by
      have h_eq : Nat.card ↥K = Nat.card ↥signG.ker :=
        (Nat.card_congr
          (signG.ker.equivMapOfInjective galToPerm5.range.subtype
            Subtype.val_injective).toEquiv).symm
      rw [h_eq]
      have h_mul := Subgroup.card_mul_index signG.ker
      have h_idx_dvd : signG.ker.index ∣ 2 := by
        have h_iso : signG.ker.index = Nat.card ↥signG.range := by
          rw [Subgroup.index]
          exact Nat.card_congr (QuotientGroup.quotientKerEquivRange signG).toEquiv
        rw [h_iso]
        calc Nat.card ↥signG.range
            ∣ Nat.card ℤˣ := Subgroup.card_subgroup_dvd_card signG.range
          _ = 2 := by rw [Nat.card_eq_fintype_card]; decide
      have h_idx_ne : signG.ker.index ≠ 1 := by
        intro heq
        have hker_top : signG.ker = ⊤ := Subgroup.index_eq_one.mp heq
        have : (⟨x, hxG⟩ : ↥galToPerm5.range) ∈ signG.ker := hker_top ▸ Subgroup.mem_top _
        rw [MonoidHom.mem_ker] at this
        simp only [signG, MonoidHom.comp_apply, Subgroup.coe_subtype] at this
        exact hxA (Equiv.Perm.mem_alternatingGroup.mpr this)
      have h_idx : signG.ker.index = 2 :=
        (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _ h_idx_dvd).resolve_left h_idx_ne
      rw [hrange_card, h_idx] at h_mul; omega
    exact no_subgroup_order_30 K hK_card
  -- But Axiom B says Gal has an odd permutation, contradicting Gal ⊆ A₅
  obtain ⟨σ, hσ⟩ := gal_has_odd_perm
  have hmem : galToPerm5 σ ∈ alternatingGroup (Fin 5) :=
    hle (MonoidHom.mem_range.mpr ⟨σ, rfl⟩)
  rw [Equiv.Perm.mem_alternatingGroup] at hmem
  rw [hmem] at hσ
  exact absurd hσ (by decide)

/-- **THEOREM** (formerly axiom): |Gal(p/ℚ)| = 120.

    Proof: 5 | |Gal| (five_dvd_gal_card) and 3 | |Gal| (Axiom A).
    So 15 | |Gal| and |Gal| | 120, giving |Gal| ∈ {15, 30, 60, 120}.
    |Gal| ≠ 15 (no_subgroup_order_15), ≠ 30 (no_subgroup_order_30),
    ≠ 60 (Gal ⊄ A₅ by Axiom B). Therefore |Gal| = 120. -/
theorem gal_card_eq_120 : Fintype.card p.Gal = 120 := by
  have h5 := five_dvd_gal_card
  have h3 := three_dvd_gal_card
  have h120 := gal_card_dvd_120
  -- 15 | |Gal| (from 5 | and 3 |, coprime)
  have h15 : 15 ∣ Fintype.card p.Gal := by
    have : Nat.Coprime 5 3 := by norm_num
    exact this.mul_dvd_of_dvd_of_dvd h5 h3
  -- |Gal| | 120 and 15 | |Gal| → |Gal| ∈ {15, 30, 60, 120}
  have hpos : 0 < Fintype.card p.Gal := Fintype.card_pos
  -- By divisibility, the only options are 15, 30, 60, 120
  have hmem : Fintype.card p.Gal ∈ ({15, 30, 60, 120} : Finset ℕ) := by
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    -- |Gal| = 15a for some a, and 15a | 120
    obtain ⟨a, ha⟩ := h15
    have hapos : 0 < a := Nat.pos_of_ne_zero (by omega)
    have h15a_dvd : 15 * a ∣ 120 := ha ▸ h120
    have hale : a ≤ 8 := by
      have := Nat.le_of_dvd (by norm_num : 0 < 120) h15a_dvd
      omega
    -- a ∈ {1..8} and 15a | 120 → a ∈ {1,2,4,8}
    interval_cases a <;> simp_all
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact absurd h gal_card_ne_15
  · exact absurd h gal_card_ne_30
  · exact absurd h gal_card_ne_60
  · exact h

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
