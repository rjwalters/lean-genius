import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.FieldTheory.AbelRuffini
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Proofs.NthRootIrrationalOQ01

/-
# Inverse Galois Problem: X⁴ - 2 and the Dihedral Group D₄

## What This Proves

We extend the Inverse Galois Problem formalization with analysis of X⁴ - 2
over ℚ, whose Galois group is D₄ (the dihedral group of order 8).

## Key Results

### Infrastructure (PROVED, no sorry):
1. **irreducible_natDegree_dvd_gal_card**: For any separable irreducible
   polynomial f over ℚ, natDegree(f) divides |Gal(f)|. This generalizes
   `Polynomial.Gal.prime_degree_dvd_card` to non-prime degrees.

### X²+1 Properties (PROVED, no sorry):
2. **x_sq_add_1_irreducible**: X²+1 is irreducible over ℚ (degree 2, no root)
3. **x_sq_add_1_natDegree**: natDegree(X²+1) = 2
4. **x_sq_add_1_monic**: X²+1 is monic

### X⁴-2 Properties (PROVED, no sorry):
5. **x_fourth_sub_2_irreducible**: X⁴-2 is irreducible over ℚ (Eisenstein at p=2)
6. **x_fourth_sub_2_natDegree**: natDegree(X⁴-2) = 4
7. **x_fourth_sub_2_separable**: X⁴-2 is separable
8. **four_dvd_x4_gal_card**: 4 | |Gal(X⁴-2)| (from general lemma)
9. **x4_gal_card_dvd_24**: |Gal(X⁴-2)| | 24 (embeds in S₄)

### Sorries (mathematical content clear, Lean API needed):
10. **x_sq_add_1_has_root_in_x4_splitting_field**: X²+1 has a root in SF(X⁴-2)
    (counting argument: 4 roots with ratios being 4th roots of unity)
11. **x_fourth_sub_2_gal_card = 8**: requires upper bound via ℚ(⁴√2,i) ⊂ ℝ argument

## Mathlib Dependencies
- `NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime` for Eisenstein criterion
- `Polynomial.Gal.galActionHom_injective` for embedding Gal → Perm(roots)
- `Polynomial.Gal.card_of_separable` for |Gal| = [SF:ℚ]
-/

namespace InverseGaloisX4Sub2

open Polynomial

-- ============================================================================
-- Part I: General Infrastructure — Irreducible Degree Divides |Gal|
-- ============================================================================

/--
For a separable irreducible polynomial f over ℚ, natDegree f divides |Gal(f)|.

This is a fundamental consequence of the tower law: the splitting field
contains a root α with [ℚ(α):ℚ] = deg(f), and deg(f) divides [SF:ℚ] = |Gal|.

Generalizes `Polynomial.Gal.prime_degree_dvd_card` (which requires prime degree).
-/
theorem irreducible_natDegree_dvd_gal_card
    {f : ℚ[X]}
    (hirr : Irreducible f)
    (hsep : f.Separable) :
    f.natDegree ∣ Fintype.card f.Gal := by
  -- |Gal| = [SplittingField : ℚ]
  have hcard : Nat.card f.Gal = Module.finrank ℚ f.SplittingField :=
    Polynomial.Gal.card_of_separable hsep
  rw [Nat.card_eq_fintype_card] at hcard
  rw [hcard]
  -- f has a root α in its splitting field
  have hsplits := Polynomial.SplittingField.splits f
  have hfm_deg : (f.map (algebraMap ℚ f.SplittingField)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap ℚ _).injective]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨α, hα⟩ := Polynomial.exists_root_of_splits hsplits hfm_deg
  have hα_eval : Polynomial.aeval α f = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hα
  -- minpoly ℚ α divides f, and they are associates (same degree)
  have hα_int : IsIntegral ℚ α := .of_finite ℚ α
  have hmin_dvd : minpoly ℚ α ∣ f := minpoly.dvd ℚ α hα_eval
  have hdeg : (minpoly ℚ α).natDegree = f.natDegree := by
    obtain ⟨u, hu⟩ := (minpoly.irreducible hα_int).associated_of_dvd hirr hmin_dvd
    have h1 := congr_arg Polynomial.natDegree hu
    rw [Polynomial.natDegree_mul (minpoly.ne_zero hα_int) (Units.ne_zero u)] at h1
    have h2 := Polynomial.natDegree_eq_zero_of_isUnit ⟨u, rfl⟩
    omega
  -- [ℚ(α):ℚ] = natDegree(f), and [ℚ(α):ℚ] | [SF:ℚ] by tower law
  rw [← hdeg]
  have htower := Module.finrank_mul_finrank ℚ ℚ⟮α⟯ f.SplittingField
  rw [IntermediateField.adjoin.finrank hα_int] at htower
  exact ⟨_, htower.symm⟩

-- ============================================================================
-- Part II: X²+1 Properties
-- ============================================================================

/-- X²+1 is irreducible over ℚ.
    Degree 2 with no rational root (r²+1 > 0 for all r ∈ ℚ). -/
theorem x_sq_add_1_irreducible : Irreducible (X ^ 2 + 1 : ℚ[X]) := by
  constructor
  · -- Not a unit: degree is 2 > 0
    intro hu
    have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have h2 : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree!
    linarith
  · -- Any factorization has a unit factor
    intro a b hab
    have hnoroot : ∀ r : ℚ, Polynomial.eval r (X ^ 2 + 1 : ℚ[X]) ≠ 0 := by
      intro r
      simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one]
      linarith [sq_nonneg r]
    have hprod_ne : a * b ≠ 0 := by
      rw [← hab]; intro h
      have := congr_arg Polynomial.natDegree h
      simp only [Polynomial.natDegree_zero] at this
      have : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree!
      linarith
    have ha_ne : a ≠ 0 := left_ne_zero_of_mul hprod_ne
    have hb_ne : b ≠ 0 := right_ne_zero_of_mul hprod_ne
    have hdeg_sum : a.natDegree + b.natDegree = 2 := by
      have h2 : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by compute_degree!
      rw [← Polynomial.natDegree_mul ha_ne hb_ne, ← hab, h2]
    have ha_le : a.natDegree ≤ 2 := by omega
    have ha_deg0_isUnit : a.natDegree = 0 → IsUnit a := by
      intro h0
      have heq := Polynomial.eq_C_of_natDegree_eq_zero h0
      rw [heq]
      exact Polynomial.isUnit_C.mpr
        (Ne.isUnit (fun h => ha_ne (by rw [heq, h, map_zero])))
    have hb_deg0_isUnit : b.natDegree = 0 → IsUnit b := by
      intro h0
      have heq := Polynomial.eq_C_of_natDegree_eq_zero h0
      rw [heq]
      exact Polynomial.isUnit_C.mpr
        (Ne.isUnit (fun h => hb_ne (by rw [heq, h, map_zero])))
    interval_cases a.natDegree
    · left; exact ha_deg0_isUnit rfl
    · exfalso
      have ha_deg1 : a.degree = 1 := by
        rw [Polynomial.degree_eq_natDegree ha_ne]; norm_cast
      obtain ⟨r, hr⟩ := Polynomial.exists_root_of_degree_eq_one ha_deg1
      exact hnoroot r (by rw [← hab, Polynomial.eval_mul, hr, zero_mul])
    · right; exact hb_deg0_isUnit (by omega)

/-- natDegree(X²+1) = 2. -/
theorem x_sq_add_1_natDegree : (X ^ 2 + 1 : ℚ[X]).natDegree = 2 := by
  compute_degree!

/-- X²+1 is monic. -/
theorem x_sq_add_1_monic : (X ^ 2 + 1 : ℚ[X]).Monic := by
  show (X ^ 2 + 1 : ℚ[X]).leadingCoeff = 1
  rw [Polynomial.leadingCoeff, x_sq_add_1_natDegree]
  simp [Polynomial.coeff_add, Polynomial.coeff_X_pow_self, Polynomial.coeff_one]

-- ============================================================================
-- Part III: X⁴ - 2 Galois Theory
-- ============================================================================

/-- X⁴ - 2 is irreducible over ℚ (Eisenstein at p = 2). -/
theorem x_fourth_sub_2_irreducible :
    Irreducible (X ^ 4 - C (2 : ℚ) : ℚ[X]) :=
  NthRootIrrationalOQ01.eisenstein_X_pow_sub_prime 4 2 (by omega) (by decide)

/-- natDegree(X⁴-2) = 4. -/
theorem x_fourth_sub_2_natDegree :
    (X ^ 4 - C (2 : ℚ) : ℚ[X]).natDegree = 4 :=
  NthRootIrrationalOQ01.natDegree_X_pow_sub_C_eq (by omega) (by norm_num)

/-- X⁴ - 2 is separable (irreducible in characteristic 0). -/
theorem x_fourth_sub_2_separable : (X ^ 4 - C (2 : ℚ) : ℚ[X]).Separable :=
  x_fourth_sub_2_irreducible.separable

/-- X⁴ - 2 is monic. -/
theorem x_fourth_sub_2_monic : (X ^ 4 - C (2 : ℚ) : ℚ[X]).Monic :=
  monic_X_pow_sub_C 2 (by omega)

/-- 4 | |Gal(X⁴-2/ℚ)| (from general lemma). -/
theorem four_dvd_x4_gal_card :
    4 ∣ Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal := by
  have h := irreducible_natDegree_dvd_gal_card
    x_fourth_sub_2_irreducible x_fourth_sub_2_separable
  rwa [x_fourth_sub_2_natDegree] at h

/-- |Gal(X⁴-2/ℚ)| | 24 (Gal embeds into S₄ via action on 4 roots). -/
theorem x4_gal_card_dvd_24 :
    Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal ∣ 24 := by
  classical
  set p := (X ^ 4 - C (2 : ℚ) : ℚ[X])
  haveI : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
    ⟨Polynomial.SplittingField.splits p⟩
  have hinj := Polynomial.Gal.galActionHom_injective p p.SplittingField
  have hdvd : Nat.card p.Gal ∣ Nat.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hdvd
  rw [Fintype.card_perm] at hdvd
  have hcard : Fintype.card (p.rootSet p.SplittingField) = 4 := by
    rw [Polynomial.card_rootSet_eq_natDegree x_fourth_sub_2_separable
        (Polynomial.SplittingField.splits p)]
    exact x_fourth_sub_2_natDegree
  rw [hcard] at hdvd
  simpa using hdvd

-- ============================================================================
-- Part IV: X²+1 Has a Root in SF(X⁴-2) — Toward |Gal| = 8
-- ============================================================================

/--
X²+1 has a root in the splitting field of X⁴-2.

Mathematical argument: X⁴-2 has 4 distinct roots a₁,...,a₄ with aᵢ⁴=2.
For any two roots, (aᵢ/aⱼ)⁴ = 1, so the ratio is a 4th root of unity.
If all ratios were ±1, there would be at most 2 distinct roots (each root
paired with its negative). With 4 roots, some ratio must be a primitive
4th root of unity, satisfying X²+1 = 0.
-/
theorem x_sq_add_1_has_root_in_x4_splitting_field :
    ∃ ω : (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField,
      ω ^ 2 + 1 = 0 := by
  set p := (X ^ 4 - C (2 : ℚ) : ℚ[X]) with hp_def
  -- Step 1: Get a root α of X⁴-2 in the splitting field
  have hsplits := Polynomial.SplittingField.splits p
  set pm := p.map (algebraMap ℚ p.SplittingField) with hpm_def
  have hpm_deg : pm.degree ≠ 0 := by
    rw [hpm_def, Polynomial.degree_map_eq_of_injective (algebraMap ℚ _).injective]
    exact (Polynomial.degree_pos_of_irreducible x_fourth_sub_2_irreducible).ne'
  obtain ⟨α, hα⟩ := Polynomial.exists_root_of_splits hsplits hpm_deg
  -- hα : pm.IsRoot α, i.e., pm.eval α = 0
  -- Convert to eval₂ form: α⁴ - algebraMap ℚ SF 2 = 0
  have hα_eval2 : Polynomial.eval₂ (algebraMap ℚ p.SplittingField) α p = 0 := by
    rw [Polynomial.eval₂_eq_eval_map]; exact hα
  simp only [hp_def, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C] at hα_eval2
  have hα4 : α ^ 4 = algebraMap ℚ p.SplittingField 2 := eq_of_sub_eq_zero hα_eval2
  -- α ≠ 0
  have hα_ne : α ≠ 0 := by
    intro h; rw [h, zero_pow (by norm_num : 4 ≠ 0)] at hα4
    have h2 : (algebraMap ℚ p.SplittingField) 2 = 0 := hα4.symm
    rw [← map_zero (algebraMap ℚ p.SplittingField)] at h2
    exact absurd ((algebraMap ℚ p.SplittingField).injective h2) (by norm_num : (2:ℚ) ≠ 0)
  -- Step 2: X⁴-2 has 4 roots (from separability + splits)
  -- The mapped polynomial pm factors as (X²-α²)(X²+α²) in SF[X]
  -- pm has root α (and also -α, since (-α)⁴ = α⁴ = 2)
  -- pm.roots contains the multiset of all roots
  -- Since pm splits and is separable, pm.roots.card = pm.natDegree = 4
  -- Step 3: Show X²+C(α²) has a root in SF via factorization
  -- pm = (X²-C(α²))(X²+C(α²)) in SF[X]
  -- If X²+C(α²) had no root, it would be irreducible of degree 2,
  -- but pm splits into linear factors, contradiction.
  -- Concretely: pm.roots has 4 elements, and they come from both factors.
  --
  -- We use: the roots multiset of a product is the union of roots multisets.
  -- pm.roots = (X²-C(α²)).roots + (X²+C(α²)).roots (over a domain)
  -- Since pm.roots.card = 4, and each factor contributes ≤ 2 roots,
  -- (X²+C(α²)).roots must be nonempty.
  have hmap : pm = (X ^ 2 - C (α ^ 2)) * (X ^ 2 + C (α ^ 2)) := by
    have hC_sq : (C (α ^ 2) : p.SplittingField[X]) ^ 2 = C (α ^ 4) := by
      rw [← map_pow]; congr 1; ring
    simp only [hpm_def, hp_def, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, ← hα4, ← hC_sq]
    ring
  -- pm is not zero (irreducible polynomial mapped by injective ring hom)
  have hpm_ne : pm ≠ 0 := by
    rw [hpm_def]
    exact Polynomial.map_ne_zero (x_fourth_sub_2_irreducible.ne_zero)
  -- The left factor is not zero
  have h_left_ne : (X ^ 2 - C (α ^ 2) : p.SplittingField[X]) ≠ 0 := by
    intro h; rw [hmap, h, zero_mul] at hpm_ne; exact hpm_ne rfl
  -- The right factor is not zero
  have h_right_ne : (X ^ 2 + C (α ^ 2) : p.SplittingField[X]) ≠ 0 := by
    intro h; rw [hmap, h, mul_zero] at hpm_ne; exact hpm_ne rfl
  -- Roots of the product = union of roots (over a domain)
  have hroots : pm.roots = (X ^ 2 - C (α ^ 2)).roots + (X ^ 2 + C (α ^ 2)).roots := by
    rw [hmap, Polynomial.roots_mul (mul_ne_zero h_left_ne h_right_ne)]
  -- pm.roots.card = 4 (separable split polynomial)
  have hpm_card : pm.roots.card = 4 := by
    rw [← hsplits.natDegree_eq_card_roots, hpm_def,
        Polynomial.natDegree_map, x_fourth_sub_2_natDegree]
  -- Each factor contributes ≤ 2 roots (degree bound)
  have h_left_card : (X ^ 2 - C (α ^ 2) : p.SplittingField[X]).roots.card ≤ 2 := by
    calc (X ^ 2 - C (α ^ 2)).roots.card ≤ (X ^ 2 - C (α ^ 2)).natDegree := by
          have := Polynomial.card_roots h_left_ne
          rw [Polynomial.degree_eq_natDegree h_left_ne] at this
          exact_mod_cast this
      _ ≤ 2 := by compute_degree!
  -- So the right factor has ≥ 2 roots, hence at least one root
  have h_right_nonempty : (X ^ 2 + C (α ^ 2) : p.SplittingField[X]).roots.card ≥ 2 := by
    have := congr_arg Multiset.card hroots
    rw [Multiset.card_add] at this
    omega
  have h_right_roots_ne : (X ^ 2 + C (α ^ 2) : p.SplittingField[X]).roots ≠ 0 := by
    intro h; rw [h, Multiset.card_zero] at h_right_nonempty; omega
  obtain ⟨γ, hγ_mem⟩ := Multiset.exists_mem_of_ne_zero h_right_roots_ne
  have hγ : (X ^ 2 + C (α ^ 2) : p.SplittingField[X]).IsRoot γ :=
    (Polynomial.mem_roots h_right_ne).mp hγ_mem
  -- γ² + α² = 0
  rw [Polynomial.IsRoot] at hγ
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at hγ
  -- Step 4: ω = γ * α⁻¹ satisfies ω² + 1 = 0
  refine ⟨γ * α⁻¹, ?_⟩
  have hγ2 : γ ^ 2 = -(α ^ 2) := eq_neg_of_add_eq_zero_left hγ
  rw [mul_pow, inv_pow, hγ2, neg_mul, mul_inv_cancel₀ (pow_ne_zero 2 hα_ne), neg_add_cancel]

/-- The splitting field of X⁴-2 has degree divisible by 4 (from degree of X⁴-2)
    and also contains a root of the irreducible X²+1, giving 2 | [SF:ℚ] as well. -/
theorem two_dvd_x4_splitting_field_finrank :
    2 ∣ Module.finrank ℚ (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField := by
  -- Already have 4 | finrank from four_dvd_x4_gal_card and |Gal| = finrank
  have h4 := four_dvd_x4_gal_card
  have hcard : Nat.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal =
    Module.finrank ℚ (X ^ 4 - C (2 : ℚ) : ℚ[X]).SplittingField :=
    Polynomial.Gal.card_of_separable x_fourth_sub_2_separable
  rw [Nat.card_eq_fintype_card] at hcard
  rw [← hcard]
  exact dvd_trans ⟨2, by norm_num⟩ h4

/--
**Eight divides |Gal(X⁴-2/ℚ)|**:

Lower bound: 8 | |Gal|, because:
- 4 | |Gal| from irreducible degree dividing (proved above)
- The splitting field contains a root ω of X²+1 (proved above)
- ℚ(ω) ≅ ℚ(i) is a degree-2 subextension
- X²+1 is irreducible over ℚ, so [ℚ(ω):ℚ] = 2
- By the tower law, [SF:ℚ] = [SF:ℚ(ω)] · [ℚ(ω):ℚ], so 2 | [SF:ℚ]
- Combined with 4 | [SF:ℚ] and lcm(4,2)=4: we get 4 | [SF:ℚ]
  (this only gives 4, not 8 — for 8 we need the tower through ℚ(α))

Actually, 8 | |Gal| follows from:
- α root of X⁴-2, [ℚ(α):ℚ] = 4
- ω root of X²+1, ω ∈ SF, ω ∉ ℚ(α) (since ℚ(α) ⊂ ℝ but ω² = -1)
- [ℚ(α,ω):ℚ] = [ℚ(α,ω):ℚ(α)] · [ℚ(α):ℚ] = 2 · 4 = 8
- 8 | [SF:ℚ] = |Gal|

The step "ω ∉ ℚ(α) ⊂ ℝ" requires embedding ℚ(α) into ℝ.
-/
theorem eight_dvd_x4_gal_card :
    8 ∣ Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal := by
  sorry -- Needs: ℚ(⁴√2) ⊂ ℝ, so i ∉ ℚ(⁴√2), hence [ℚ(⁴√2,i):ℚ(⁴√2)] = 2

/--
**Bounds on |Gal(X⁴-2/ℚ)|**:

Proven lower bound: 4 | |Gal| (from irreducible_natDegree_dvd_gal_card)
Proven upper bound: |Gal| | 24 (from embedding Gal → S₄)

With 8 | |Gal| and |Gal| | 24: |Gal| ∈ {8, 24}.
The splitting field is ℚ(⁴√2, i) with [ℚ(⁴√2,i):ℚ] = 8,
so |Gal| = 8 ≅ D₄.
-/
theorem x_fourth_sub_2_gal_card :
    Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal = 8 := by
  sorry -- Needs eight_dvd_x4_gal_card + upper bound argument

/--
|Gal(X⁴-2)| ∈ {4, 8, 12, 24}: the divisors of 24 that are multiples of 4.
4 | |Gal| (degree divides), |Gal| | 24 (embeds in S₄).
-/
theorem x4_gal_card_pos : 0 < Fintype.card (X ^ 4 - C (2 : ℚ) : ℚ[X]).Gal :=
  Fintype.card_pos

end InverseGaloisX4Sub2
