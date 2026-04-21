/-
  Angle Trisection - Galois Group of cos(2π/5) Minimal Polynomial (OQ-03-OQ-01)

  Proves: |Gal(4X²+2X-1/ℚ)| = 2

  The polynomial 4X²+2X-1 is the minimal polynomial of cos(72°) = cos(2π/5).
  Its two roots are cos(72°) and cos(144°) = cos(4π/5).

  For prime p, |Gal(ℚ(cos(2π/p))/ℚ)| = (p-1)/2. This file handles the p=5 case,
  giving the simplest non-trivial example: a cyclic Galois group of order 2.

  Strategy (mirrors AngleTrisectionCos20GalOQ03 for the cos(40°)/degree-3 case):
  - If α is a root, then β = -2α²-2α is also a root (ring identity below)
  - β = cos(4π/5) = -cos(π/5): from 4α²=1-2α, β = -(1-2α)/2-2α = -(2α+1)/2 = -α-1/2
  - Both roots ∈ ℚ(α) → SplittingField = ℚ(α) → [SF:ℚ] = 2 → |Gal| = 2

  Ring identity for the second root (avoids fractions):
    4(-2α²-2α)²+2(-2α²-2α)-1 = (4α²+6α+1)·(4α²+2α-1)

  Factored form: 4X²+2X-1 = 4(X-α)(X+2α²+2α) when 4α²+2α-1=0.
  Ring identity: 4a²+2a-1 - 4(a-α)(a+2α²+2α) = (4α²+2α-1)·(-2a+2α+1)

  Irreducibility of 4X²+2X-1: discriminant = 4+16 = 20 is not a perfect square.
  Equivalently: rational root theorem candidates ±1, ±1/2, ±1/4 are all non-roots.

  0 axioms. 0 sorries. Fully proved.
-/
import Mathlib

open Polynomial IntermediateField FiniteDimensional

namespace AngleTrisectionCos20GalOQ03OQ01

/-
## Part I: Key Algebraic Identities
-/

/-- If 4a²+2a-1=0 in any commutative ring, then -2a²-2a is also a root.

    Ring identity: 4(-2a²-2a)²+2(-2a²-2a)-1 = (4a²+6a+1)·(4a²+2a-1). -/
theorem root_image_beta {R : Type*} [CommRing R] (a : R)
    (ha : 4 * a ^ 2 + 2 * a - 1 = 0) :
    4 * (-2 * a ^ 2 - 2 * a) ^ 2 + 2 * (-2 * a ^ 2 - 2 * a) - 1 = 0 := by
  have key : 4 * (-2 * a ^ 2 - 2 * a) ^ 2 + 2 * (-2 * a ^ 2 - 2 * a) - 1 =
    (4 * a ^ 2 + 6 * a + 1) * (4 * a ^ 2 + 2 * a - 1) := by ring
  rw [key, ha, mul_zero]

/-- Factored form: when 4α²+2α-1=0, we have 4a²+2a-1 = 4(a-α)(a+2α²+2α). -/
theorem factored_form {R : Type*} [CommRing R] (α a : R)
    (hα : 4 * α ^ 2 + 2 * α - 1 = 0) :
    4 * a ^ 2 + 2 * a - 1 = 4 * (a - α) * (a + 2 * α ^ 2 + 2 * α) := by
  have key : 4 * a ^ 2 + 2 * a - 1 - 4 * (a - α) * (a + 2 * α ^ 2 + 2 * α) =
    (4 * α ^ 2 + 2 * α - 1) * (-2 * a + 2 * α + 1) := by ring
  have hrhs : (4 * α ^ 2 + 2 * α - 1) * (-2 * a + 2 * α + 1) = 0 := by
    rw [hα, zero_mul]
  linarith [key.trans hrhs]

/-
## Part II: Polynomial Properties
-/

/-- Shorthand for the polynomial 4X²+2X-1. -/
private noncomputable abbrev p : ℚ[X] := 4 * X ^ 2 + 2 * X - C 1

private theorem p_ne_zero : (p : ℚ[X]) ≠ 0 := by
  intro h
  have : Polynomial.eval 0 (p : ℚ[X]) = -1 := by simp [p]
  rw [h, Polynomial.eval_zero] at this
  norm_num at this

private theorem p_natDegree : (p : ℚ[X]).natDegree = 2 := by
  show (4 * X ^ 2 + 2 * X - C (1 : ℚ)).natDegree = 2
  compute_degree!

private theorem p_degree_ne_zero : (p : ℚ[X]).degree ≠ 0 := by
  rw [Polynomial.degree_eq_natDegree p_ne_zero, p_natDegree]
  exact (by norm_num : (2 : WithBot ℕ) ≠ 0)

/-
## Part II-B: Irreducibility via Eisenstein Criterion

Strategy: The shifted polynomial q = 4X²+10X+5 (obtained by X ↦ X+1) satisfies
Eisenstein's criterion at p=5:
  - leading coeff 4: 5 ∤ 4 ✓
  - coeff of X: 10, 5 ∣ 10 ✓
  - constant 5: 5 ∣ 5 ✓ and 25 ∤ 5 ✓
So q is irreducible over ℤ, hence ℚ (Gauss's lemma).
Since p = q(X-1) and X ↦ X-1 is invertible (inverse X ↦ X+1), irreducibility transfers.

Verification: 4(X-1)²+10(X-1)+5 = 4X²-8X+4+10X-10+5 = 4X²+2X-1 = p ✓
-/

/-- The Eisenstein polynomial q = 4X²+10X+5 over ℤ. -/
private noncomputable def q_eis_int : ℤ[X] := C 4 * X ^ 2 + C 10 * X + C 5

private theorem q_eis_int_degree : q_eis_int.degree = 2 := by
  unfold q_eis_int; compute_degree!

private theorem q_eis_int_natDegree : q_eis_int.natDegree = 2 := by
  unfold q_eis_int; compute_degree!

/-- q is irreducible over ℤ by Eisenstein's criterion at p = 5. -/
private theorem q_eis_int_irreducible : Irreducible q_eis_int := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(5 : ℤ)})
  · -- (5) is a prime ideal in ℤ
    rw [Ideal.span_singleton_prime (show (5 : ℤ) ≠ 0 from by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · -- leadingCoeff ∉ (5): leadingCoeff = 4, 5 ∤ 4
    have hle : q_eis_int.leadingCoeff = 4 := by
      rw [Polynomial.leadingCoeff, q_eis_int_natDegree]
      unfold q_eis_int
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
      norm_num
    rw [hle, Ideal.mem_span_singleton]
    norm_num
  · -- ∀ k < degree, coeff k ∈ (5): coeffs are 10 (k=1) and 5 (k=0)
    intro k hk
    rw [q_eis_int_degree] at hk
    have hkn : k < 2 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    unfold q_eis_int
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · -- 0 < degree
    rw [q_eis_int_degree]; exact_mod_cast Nat.zero_lt_succ 1
  · -- coeff 0 ∉ (5)²: coeff 0 = 5, but 25 ∤ 5
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold q_eis_int
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num
  · -- isPrimitive: gcd(coeff 2, coeff 0) = gcd(4, 5) = 1, so gcd(4,10,5) = 1
    intro r hr
    -- r divides the content, which divides each coefficient
    have hc2 : r ∣ (4 : ℤ) := by
      have h := dvd_trans hr (Polynomial.content_dvd_coeff q_eis_int 2)
      unfold q_eis_int at h
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X] at h
      simpa using h
    have hc0 : r ∣ (5 : ℤ) := by
      have h := dvd_trans hr (Polynomial.content_dvd_coeff q_eis_int 0)
      unfold q_eis_int at h
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X] at h
      simpa using h
    -- gcd(4, 5) = 1 since 5 - 4 = 1
    have h1 : r ∣ (1 : ℤ) := by
      have := dvd_sub hc0 hc2
      norm_num at this
      exact this
    exact isUnit_of_dvd_one h1

/-- The same polynomial over ℚ. -/
private noncomputable def q_eis_rat : ℚ[X] := C 4 * X ^ 2 + C 10 * X + C 5

/-- q is irreducible over ℚ (Gauss's lemma: primitive + ℤ-irreducible → ℚ-irreducible). -/
private theorem q_eis_rat_irreducible : Irreducible q_eis_rat := by
  have hprim : q_eis_int.IsPrimitive := by
    intro r hr
    have hc2 : r ∣ (4 : ℤ) := by
      have h := dvd_trans hr (Polynomial.content_dvd_coeff q_eis_int 2)
      unfold q_eis_int at h
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X] at h
      simpa using h
    have hc0 : r ∣ (5 : ℤ) := by
      have h := dvd_trans hr (Polynomial.content_dvd_coeff q_eis_int 0)
      unfold q_eis_int at h
      simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X] at h
      simpa using h
    have h1 : r ∣ (1 : ℤ) := by
      have := dvd_sub hc0 hc2; norm_num at this; exact this
    exact isUnit_of_dvd_one h1
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp q_eis_int_irreducible
  have heq : q_eis_rat = Polynomial.map (Int.castRingHom ℚ) q_eis_int := by
    unfold q_eis_rat q_eis_int
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_pow]
    norm_num
  rwa [heq]

/-- Key identity: q(X-1) = p, i.e., substituting Y = X-1 transforms q into p.
    Verified by expanding: 4(X-1)²+10(X-1)+5 = 4X²-8X+4+10X-10+5 = 4X²+2X-1. -/
private theorem q_comp_eq_p :
    q_eis_rat.comp (X - C 1) = p := by
  apply Polynomial.funext; intro x
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  unfold q_eis_rat p
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  ring

/-- The polynomial 4X²+2X-1 is irreducible over ℚ.

    Proof: The shifted polynomial q = 4X²+10X+5 is Eisenstein at p=5,
    so q is irreducible over ℚ by Gauss's lemma. Since p = q(X-1)
    and the substitution X ↦ X-1 is invertible (inverse: X ↦ X+1),
    irreducibility transfers from q to p. -/
private theorem p_irreducible : Irreducible (p : ℚ[X]) := by
  rw [← q_comp_eq_p]
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · -- q.comp (X-1) is not a unit (has degree 2)
    intro h
    have hd := Polynomial.natDegree_eq_zero_of_isUnit h
    have : (q_eis_rat.comp (X - C 1)).natDegree = 2 := by
      rw [q_comp_eq_p]; exact p_natDegree
    omega
  · -- if q.comp (X-1) = a * b, then one is a unit
    intro a b hab
    set ℓ := (X - C (1 : ℚ) : ℚ[X])
    set ℓ_inv := (X + C (1 : ℚ) : ℚ[X])
    have hq_factor : q_eis_rat = (a.comp ℓ_inv) * (b.comp ℓ_inv) := by
      have h1 : ℓ.comp ℓ_inv = X := by
        simp only [ℓ, ℓ_inv, Polynomial.sub_comp, Polynomial.add_comp,
          Polynomial.C_comp, Polynomial.X_comp]
        ring
      calc q_eis_rat
          = q_eis_rat.comp X := q_eis_rat.comp_X.symm
        _ = q_eis_rat.comp (ℓ.comp ℓ_inv) := by rw [h1]
        _ = (q_eis_rat.comp ℓ).comp ℓ_inv := (q_eis_rat.comp_assoc ℓ ℓ_inv).symm
        _ = (a * b).comp ℓ_inv := by rw [hab]
        _ = (a.comp ℓ_inv) * (b.comp ℓ_inv) := Polynomial.mul_comp a b ℓ_inv
    rcases q_eis_rat_irreducible.isUnit_or_isUnit hq_factor with ha | hb
    · left
      rw [Polynomial.isUnit_iff] at ha
      obtain ⟨c, hc_ne, hc_eq⟩ := ha
      have h_inv : ℓ_inv.comp ℓ = X := by
        simp only [ℓ, ℓ_inv, Polynomial.sub_comp, Polynomial.add_comp,
          Polynomial.C_comp, Polynomial.X_comp]
        ring
      have ha_eq : a = (a.comp ℓ_inv).comp ℓ := by
        conv_lhs => rw [← a.comp_X, ← h_inv]
        exact (a.comp_assoc ℓ_inv ℓ).symm
      rw [Polynomial.isUnit_iff]
      exact ⟨c, hc_ne, by rw [ha_eq, ← hc_eq, Polynomial.C_comp]⟩
    · right
      rw [Polynomial.isUnit_iff] at hb
      obtain ⟨c, hc_ne, hc_eq⟩ := hb
      have h_inv : ℓ_inv.comp ℓ = X := by
        simp only [ℓ, ℓ_inv, Polynomial.sub_comp, Polynomial.add_comp,
          Polynomial.C_comp, Polynomial.X_comp]
        ring
      have hb_eq : b = (b.comp ℓ_inv).comp ℓ := by
        conv_lhs => rw [← b.comp_X, ← h_inv]
        exact (b.comp_assoc ℓ_inv ℓ).symm
      rw [Polynomial.isUnit_iff]
      exact ⟨c, hc_ne, by rw [hb_eq, ← hc_eq, Polynomial.C_comp]⟩

private theorem p_separable : (p : ℚ[X]).Separable :=
  p_irreducible.separable

/-
## Part III: Splitting Field Analysis
-/

/-- Evaluation of p at an element equals 4a²+2a-1. -/
private theorem p_eval_eq {R : Type*} [CommRing R] [Algebra ℚ R] (a : R) :
    Polynomial.aeval a p = 4 * a ^ 2 + 2 * a - 1 := by
  simp [p, map_add, map_sub, map_mul, map_pow, map_ofNat, Polynomial.aeval_X]

private theorem p_map_degree_ne :
    (p.map (algebraMap ℚ p.SplittingField)).degree ≠ 0 := by
  rw [degree_map_eq_of_injective (RingHom.injective (algebraMap ℚ p.SplittingField))]
  exact p_degree_ne_zero

/-- In the splitting field, get a root via rootOfSplits. -/
private noncomputable def root_in_sf : p.SplittingField :=
  rootOfSplits (SplittingField.splits p) p_map_degree_ne

/-- The root satisfies p(α) = 0. -/
private theorem root_is_root :
    Polynomial.aeval root_in_sf p = 0 := by
  unfold root_in_sf
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  exact eval_rootOfSplits _ p_map_degree_ne

/-- The root satisfies 4α²+2α-1 = 0. -/
private theorem root_eq_zero :
    4 * root_in_sf ^ 2 + 2 * root_in_sf - 1 = 0 := by
  have := root_is_root
  rwa [p_eval_eq] at this

/-- β = -2α²-2α is a root of p in the splitting field. -/
private theorem beta_is_root :
    Polynomial.aeval (-2 * root_in_sf ^ 2 - 2 * root_in_sf) p = 0 := by
  rw [p_eval_eq]
  exact root_image_beta root_in_sf root_eq_zero

/-
## Part IV: Both Roots Lie in ℚ(α)
-/

/-- The root α is integral over ℚ. -/
private theorem root_integral : IsIntegral ℚ root_in_sf :=
  .of_finite ℚ root_in_sf

/-- The minpoly of α has natDegree 2. -/
private theorem minpoly_natDegree :
    (minpoly ℚ root_in_sf).natDegree = 2 := by
  have hdvd : minpoly ℚ root_in_sf ∣ p :=
    minpoly.dvd ℚ root_in_sf (by rw [p_eval_eq]; exact root_eq_zero)
  have hirr_min := minpoly.irreducible root_integral
  have hassoc := hirr_min.dvd_symm p_irreducible hdvd
  apply le_antisymm
  · calc (minpoly ℚ root_in_sf).natDegree ≤ p.natDegree :=
            Polynomial.natDegree_le_of_dvd hdvd p_ne_zero
      _ = 2 := p_natDegree
  · calc 2 = p.natDegree := p_natDegree.symm
      _ ≤ (minpoly ℚ root_in_sf).natDegree :=
            Polynomial.natDegree_le_of_dvd hassoc (minpoly.ne_zero root_integral)

/-- [ℚ(α):ℚ] = 2. -/
private theorem adjoin_finrank :
    Module.finrank ℚ (IntermediateField.adjoin ℚ
      ({root_in_sf} : Set p.SplittingField)) = 2 := by
  rw [IntermediateField.adjoin.finrank root_integral, minpoly_natDegree]

/-- β = -2α²-2α is in ℚ(α). -/
private theorem beta_in_adjoin :
    (-2 * root_in_sf ^ 2 - 2 * root_in_sf : p.SplittingField) ∈
    IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField) := by
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField)
  have hα : root_in_sf ∈ S := IntermediateField.mem_adjoin_simple_self ℚ root_in_sf
  have hαα : root_in_sf * root_in_sf ∈ S := S.mul_mem hα hα
  have h2αα : (2 : p.SplittingField) * (root_in_sf * root_in_sf) ∈ S :=
    S.mul_mem (S.algebraMap_mem 2) hαα
  have h2α : (2 : p.SplittingField) * root_in_sf ∈ S :=
    S.mul_mem (S.algebraMap_mem 2) hα
  show -2 * root_in_sf ^ 2 - 2 * root_in_sf ∈ S
  have heq : -2 * root_in_sf ^ 2 - 2 * root_in_sf =
    -((2 : p.SplittingField) * (root_in_sf * root_in_sf)) - 2 * root_in_sf := by ring
  rw [heq]
  exact S.sub_mem (S.neg_mem h2αα) h2α

/-- All roots of p are in ℚ(α). -/
private theorem rootSet_subset_adjoin :
    p.rootSet p.SplittingField ⊆
    (IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField) : IntermediateField ℚ _) := by
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField)
  intro x hx
  rw [Polynomial.mem_rootSet] at hx
  obtain ⟨_, hroot⟩ := hx
  -- Translate the root condition: 4x²+2x-1 = 0
  rw [p_eval_eq] at hroot
  -- Use factored form: 4a²+2a-1 = 4(a-α)(a+2α²+2α)
  have hfact : 4 * x ^ 2 + 2 * x - 1 =
      4 * (x - root_in_sf) * (x + 2 * root_in_sf ^ 2 + 2 * root_in_sf) :=
    factored_form root_in_sf x root_eq_zero
  -- From hroot and hfact: 4(x-α)(x+2α²+2α) = 0
  have hprod : 4 * (x - root_in_sf) * (x + 2 * root_in_sf ^ 2 + 2 * root_in_sf) = 0 :=
    hfact ▸ hroot
  -- Since p.SplittingField is a field, no zero divisors
  have h4ne : (4 : p.SplittingField) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp hprod with h | h
  · -- Case 1: 4*(x - root_in_sf) = 0, so x = root_in_sf (since 4 ≠ 0)
    rcases mul_eq_zero.mp h with h4 | hα
    · exact absurd h4 h4ne
    · have hxeq : x = root_in_sf := sub_eq_zero.mp hα
      rw [hxeq]
      exact IntermediateField.mem_adjoin_simple_self ℚ root_in_sf
  · -- Case 2: x + 2α² + 2α = 0, so x = -2α² - 2α
    have hxeq : x = -2 * root_in_sf ^ 2 - 2 * root_in_sf := by linear_combination h
    rw [hxeq]
    exact beta_in_adjoin

/-- The splitting field is generated by α alone. -/
private theorem adjoin_root_eq_top :
    IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField) = ⊤ := by
  have hgen : Algebra.adjoin ℚ (p.rootSet p.SplittingField : Set p.SplittingField) = ⊤ :=
    Polynomial.SplittingField.adjoin_rootSet (K := ℚ) (f := p)
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField)
  have halg : Algebra.adjoin ℚ (p.rootSet p.SplittingField : Set p.SplittingField) ≤
    S.toSubalgebra := Algebra.adjoin_le (fun x hx => rootSet_subset_adjoin hx)
  rw [eq_top_iff]
  intro x _
  exact halg (hgen ▸ Algebra.mem_top)

/-- [ℚ(cos(2π/5)):ℚ] = 2. -/
theorem splitting_finrank :
    Module.finrank ℚ p.SplittingField = 2 := by
  have htop := adjoin_root_eq_top
  have h_top_eq : Module.finrank ℚ
    (↥(IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField))) =
    Module.finrank ℚ p.SplittingField := by
    rw [htop]
    exact LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv
  rw [← h_top_eq, adjoin_finrank]

/-
## Part V: Main Theorem
-/

/-- 2 divides |Gal(p)|. -/
private theorem two_dvd_gal_card :
    2 ∣ Fintype.card p.Gal := by
  have h := Polynomial.Gal.prime_degree_dvd_card p_irreducible
    (show Nat.Prime p.natDegree by rw [p_natDegree]; decide)
  rw [Nat.card_eq_fintype_card, p_natDegree] at h
  exact h

/-- |Gal(p)| divides 2 (= 2!). -/
private theorem gal_card_dvd_two :
    Fintype.card p.Gal ∣ 2 := by
  classical
  haveI : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
    ⟨SplittingField.splits p⟩
  have hinj := Polynomial.Gal.galActionHom_injective p p.SplittingField
  have hdvd : Nat.card p.Gal ∣ Nat.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm] at hdvd
  have hcard : Fintype.card (p.rootSet p.SplittingField) = 2 :=
    (Polynomial.card_rootSet_eq_natDegree p_separable
      (SplittingField.splits p)).trans p_natDegree
  rw [hcard] at hdvd
  simpa using hdvd

/-- |Gal(4X²+2X-1/ℚ)| = 2.

    This is the Galois group of the minimal polynomial of cos(72°) = cos(2π/5).
    The two roots are cos(72°) and cos(144°) = cos(4π/5).
    Both roots lie in ℚ(cos(72°)), making the splitting field degree 2 over ℚ.
    This is the p=5 instance of |Gal(ℚ(cos(2π/p))/ℚ)| = (p-1)/2 for prime p. -/
theorem cos72_gal_card :
    Fintype.card (4 * X ^ 2 + 2 * X - C 1 : ℚ[X]).Gal = 2 := by
  have hcard := Polynomial.Gal.card_of_separable p_separable
  rw [Nat.card_eq_fintype_card] at hcard
  rw [hcard, splitting_finrank]

/-- The polynomial 4X²+2X-1 is irreducible over ℚ (public interface). -/
theorem cos72_poly_irreducible :
    Irreducible (4 * X ^ 2 + 2 * X - C 1 : ℚ[X]) :=
  p_irreducible

end AngleTrisectionCos20GalOQ03OQ01

/-
  ## Summary

  **Problem**: Galois group computation for cos(2π/5) — the p=5 case of
  |Gal(ℚ(cos(2π/p))/ℚ)| = (p-1)/2 for prime p.

  **Status**: Fully proved — 0 sorries, 0 axioms.

  **All theorems proved**:
  - `root_image_beta`: ring identity for the second root -2α²-2α
  - `factored_form`: 4a²+2a-1 = 4(a-α)(a+2α²+2α) when 4α²+2α-1=0
  - `q_eis_int_irreducible`: 4X²+10X+5 is irreducible over ℤ (Eisenstein at p=5)
  - `q_eis_rat_irreducible`: 4X²+10X+5 is irreducible over ℚ (Gauss's lemma)
  - `p_irreducible`: 4X²+2X-1 is irreducible over ℚ (via invertible shift X↦X-1)
  - `root_is_root`, `root_eq_zero`, `beta_is_root`
  - `minpoly_natDegree`: [ℚ(α):ℚ] = 2
  - `adjoin_finrank`, `beta_in_adjoin`, `rootSet_subset_adjoin`
  - `adjoin_root_eq_top`, `splitting_finrank`: [SF:ℚ] = 2
  - `cos72_gal_card`: |Gal| = 2
  - `cos72_poly_irreducible`: public interface

  **Key insight**: The factored form 4a²+2a-1 = 4(a-α)(a+2α²+2α) is the key algebraic
  certificate showing the splitting field equals ℚ(α). Irreducibility of 4X²+2X-1
  is proved via Eisenstein on the shifted polynomial 4X²+10X+5 at p=5.
  Unlike the cubic cases (OQ-01, OQ-03), the degree-2 case gives a cyclic Galois group
  ℤ/2ℤ, illustrating the general pattern: for prime p, Gal(ℚ(cos(2π/p))/ℚ) ≅ ℤ/((p-1)/2)ℤ.
-/
