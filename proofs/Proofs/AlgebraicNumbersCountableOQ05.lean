import Mathlib

/-
# Algebraic Numbers Countable: Cantor's 1874 Height Function Proof

## Open Question (algebraic-numbers-countable-oq-05)

Formalize Cantor's **original 1874 proof** that algebraic numbers are countable,
using the HEIGHT FUNCTION on integer polynomials:

  H(a₀ + a₁·X + ··· + aₙ·Xⁿ) = n + |a₀| + |a₁| + ··· + |aₙ|

## What This Proves

1. `cantorHeight` — the Cantor height function on integer polynomials
2. `cantorHeight_degree_le` — height bounds the degree
3. `cantorHeight_coeff_le` — height bounds each coefficient's absolute value
4. `finite_polys_of_height` — for each h, only finitely many polynomials have height ≤ h
5. `finite_real_roots` — each nonzero integer polynomial has finitely many real roots
6. `algebraicRealsOfHeight` — real algebraic numbers stratified by Cantor height
7. `finite_algebraicRealsOfHeight` — each height stratum is **finite** (not just countable!)
8. `algebraic_reals_eq_iUnion_height` — algebraic reals = ⋃ₕ height-h stratum
9. `algebraic_reals_countable_via_height` — countability via height stratification

## Historical Context

Cantor's 1874 paper "Über eine Eigenschaft des Inbegriffes aller reellen algebraischen
Zahlen" introduced the height function to prove algebraic numbers are countable.
This was one of the first rigorous applications of cardinality reasoning.

For each height bound h:
- Only FINITELY MANY integer polynomials have height ≤ h (bounded degree + bounded coefficients)
- Each polynomial has finitely many real roots (degree bound)
- So algebraic reals of height ≤ h form a FINITE set

Algebraic reals = ⋃ₕ (finite height-h set) = countable union of finite sets = countable.

## Comparison with AlgebraicNumbersCountable.lean

The main gallery proof stratifies by **polynomial degree** — giving COUNTABLE strata.
This file formalizes Cantor's **original approach** stratifying by **height** — giving
FINITE strata. The height approach is more constructive: for each h, one can in
principle enumerate all height-≤h algebraic numbers in finite time.
-/

namespace AlgebraicNumbersCountableOQ05

open Polynomial BigOperators Finset

-- ============================================================================
-- § 1. The Cantor Height Function
-- ============================================================================

/-- The **Cantor height** of an integer polynomial.

For p = a₀ + a₁·X + ··· + aₙ·Xⁿ, the Cantor height is:
  H(p) = n + |a₀| + |a₁| + ··· + |aₙ|

Key properties:
- H(p) = 0 iff p = 0
- For each bound h, only FINITELY MANY polynomials have H(p) ≤ h
  (degree ≤ h AND each coefficient in {-h,...,h}) -/
noncomputable def cantorHeight (p : Polynomial ℤ) : ℕ :=
  p.natDegree + (Finset.range (p.natDegree + 1)).sum (fun i => (p.coeff i).natAbs)

-- ============================================================================
-- § 2. Basic Properties of Cantor Height
-- ============================================================================

/-- The degree is bounded by the Cantor height. -/
lemma cantorHeight_degree_le {p : Polynomial ℤ} {h : ℕ} (hp : cantorHeight p ≤ h) :
    p.natDegree ≤ h :=
  le_trans (Nat.le_add_right _ _) hp

/-- The coefficient sum is bounded by height. -/
lemma cantorHeight_sum_le {p : Polynomial ℤ} {h : ℕ} (hp : cantorHeight p ≤ h) :
    (Finset.range (p.natDegree + 1)).sum (fun i => (p.coeff i).natAbs) ≤ h := by
  have := hp; simp only [cantorHeight] at this; omega

/-- Each coefficient's absolute value is bounded by the Cantor height.

For i ≤ natDegree: (p.coeff i).natAbs is a non-negative term in the sum,
so each term ≤ sum ≤ h.
For i > natDegree: p.coeff i = 0 by definition. -/
lemma cantorHeight_coeff_le {p : Polynomial ℤ} {h : ℕ} (hp : cantorHeight p ≤ h) (i : ℕ) :
    (p.coeff i).natAbs ≤ h := by
  by_cases hi : i ≤ p.natDegree
  · calc (p.coeff i).natAbs
        ≤ (Finset.range (p.natDegree + 1)).sum (fun j => (p.coeff j).natAbs) :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _) _
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
      _ ≤ h := cantorHeight_sum_le hp
  · have : p.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [this]

/-- Every nonzero polynomial has positive Cantor height. -/
lemma cantorHeight_pos_of_ne_zero {p : Polynomial ℤ} (hp : p ≠ 0) : 0 < cantorHeight p := by
  simp only [cantorHeight]
  by_contra h
  push_neg at h
  have hdeg : p.natDegree = 0 := by omega
  have hsum : (Finset.range (p.natDegree + 1)).sum (fun i => (p.coeff i).natAbs) = 0 := by omega
  simp [Finset.sum_eq_zero_iff] at hsum
  have hc0 : p.coeff 0 = 0 := Int.natAbs_eq_zero.mp (hsum 0 (by simp [hdeg]))
  exact hp (Polynomial.ext fun n => by
    cases n with
    | zero => exact hc0
    | succ n => exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega))

-- ============================================================================
-- § 3. Finiteness of Polynomials of Bounded Height (Key Theorem)
-- ============================================================================

/-- Auxiliary: a polynomial of degree ≤ h equals the finite sum of its terms through h. -/
private lemma poly_eq_fin_sum (p : Polynomial ℤ) (h : ℕ) (hdeg : p.natDegree ≤ h) :
    p = ∑ i : Fin (h + 1), Polynomial.C (p.coeff i.val) * Polynomial.X ^ i.val := by
  ext n
  simp only [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
             mul_ite, mul_one, mul_zero]
  -- ∑ i : Fin(h+1), if n = ↑i then p.coeff ↑i else 0
  -- = ∑ i in range(h+1), if n = i then p.coeff i else 0  [Fin.sum_univ_eq_sum_range]
  -- = if n ∈ range(h+1) then p.coeff n else 0             [sum_ite_eq']
  -- = if n < h+1 then p.coeff n else 0                    [mem_range]
  rw [Fin.sum_univ_eq_sum_range (fun i => if n = i then p.coeff i else 0),
      Finset.sum_ite_eq', Finset.mem_range]
  split_ifs with h_lt
  · rfl
  · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)

/-- **Key Theorem**: For each h, only finitely many integer polynomials have Cantor height ≤ h.

**Proof**: Polynomials with height ≤ h have:
  - degree ≤ h (by `cantorHeight_degree_le`)
  - all coefficients in [-h, h] (by `cantorHeight_coeff_le` and `Int.natAbs_le`)

Such a polynomial is determined by (h+1) coefficients each in [-h, h], giving an injection
into the Fintype `Fin (h+1) → ↥(Set.Icc -(h:ℤ) h)`. Hence the set is finite. -/
theorem finite_polys_of_height (h : ℕ) :
    Set.Finite {p : Polynomial ℤ | cantorHeight p ≤ h} := by
  -- Embed into the range of the map f ↦ ∑ i, C(f i) * X^i
  -- from the Fintype (Fin (h+1) → ↥Icc(-h,h)) to Polynomial ℤ
  apply Set.Finite.subset (Set.finite_range
    (fun f : Fin (h + 1) → ↥(Set.Icc (-(h : ℤ)) h) =>
      ∑ i : Fin (h + 1), Polynomial.C (f i : ℤ) * Polynomial.X ^ i.val))
  intro p hp
  simp only [Set.mem_range]
  -- Witness: the coefficient tuple f i = p.coeff i (which lies in [-h, h])
  refine ⟨fun i => ⟨p.coeff i.val,
    Set.mem_Icc.mpr (Int.natAbs_le.mp (cantorHeight_coeff_le hp i.val))⟩, ?_⟩
  -- p equals the sum ∑ i, C(p.coeff i) * X^i (since natDegree ≤ h)
  simp only [Subtype.coe_mk]
  exact poly_eq_fin_sum p h (cantorHeight_degree_le hp)

-- ============================================================================
-- § 4. Finite Real Roots per Polynomial
-- ============================================================================

/-- Each nonzero integer polynomial has finitely many real roots.

A nonzero polynomial of degree n has at most n roots (fundamental theorem of algebra). -/
theorem finite_real_roots (p : Polynomial ℤ) (hp : p ≠ 0) :
    Set.Finite {x : ℝ | Polynomial.aeval x p = 0} := by
  have hfin := Polynomial.setOf_isRoot_finite (p.map (algebraMap ℤ ℝ)) (Polynomial.map_ne_zero hp)
  convert hfin using 1
  ext x
  simp [Polynomial.IsRoot, Polynomial.aeval_def]

-- ============================================================================
-- § 5. Height-Stratified Algebraic Reals
-- ============================================================================

/-- The real algebraic numbers arising as roots of integer polynomials of Cantor height ≤ h. -/
noncomputable def algebraicRealsOfHeight (h : ℕ) : Set ℝ :=
  ⋃ (p : {q : Polynomial ℤ // q ≠ 0 ∧ cantorHeight q ≤ h}),
    {x : ℝ | Polynomial.aeval x (p : Polynomial ℤ) = 0}

/-- The set of algebraic reals of Cantor height ≤ h is **finite**.

This is the key finiteness result: not merely countable, but actually finite.
The index set is finite (by `finite_polys_of_height`) and each root set is finite. -/
theorem finite_algebraicRealsOfHeight (h : ℕ) :
    Set.Finite (algebraicRealsOfHeight h) := by
  apply Set.Finite.iUnion
  · -- Index type {q // q ≠ 0 ∧ cantorHeight q ≤ h} is finite
    haveI : Finite {q : Polynomial ℤ // q ≠ 0 ∧ cantorHeight q ≤ h} :=
      Set.finite_coe_iff.mpr ((finite_polys_of_height h).subset fun p ⟨_, hp⟩ => hp)
    infer_instance
  · -- Each root set is finite
    intro ⟨p, hp_ne, _⟩
    exact finite_real_roots p hp_ne

-- ============================================================================
-- § 6. Cantor's Height Decomposition Theorem
-- ============================================================================

/-- **Cantor's Height Decomposition**: The algebraic reals equal the union over all h of
the height-h strata.

**Forward (algebraic → has some height)**: Use `integerNormalization` to clear
denominators in the rational polynomial, obtaining a nonzero integer polynomial p.
Then x ∈ algebraicRealsOfHeight (cantorHeight p).

**Backward (in height stratum → algebraic)**: Map the integer polynomial to ℚ[X],
giving a nonzero rational polynomial with the same zeros at x : ℝ. -/
theorem algebraic_reals_eq_iUnion_height :
    {x : ℝ | IsAlgebraic ℚ x} = ⋃ h : ℕ, algebraicRealsOfHeight h := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, algebraicRealsOfHeight, Set.mem_iUnion,
             Subtype.exists, exists_and_left]
  constructor
  · rintro ⟨q, hq_ne, hq_eval⟩
    -- Clear denominators: rational polynomial → integer polynomial with same roots
    set p := IsLocalization.integerNormalization (nonZeroDivisors ℤ) q
    have hp_ne : p ≠ 0 :=
      mt IsFractionRing.integerNormalization_eq_zero_iff.mp hq_ne
    have hp_eval : Polynomial.aeval x p = 0 :=
      IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) q hq_eval
    exact ⟨cantorHeight p, p, hp_ne, le_refl _, hp_eval⟩
  · rintro ⟨_, p, hp_ne, _, hp_eval⟩
    -- Map integer polynomial to ℚ[X]: still nonzero, and x is still a root
    refine ⟨p.map (algebraMap ℤ ℚ), Polynomial.map_ne_zero hp_ne, ?_⟩
    -- aeval x (p.map (algebraMap ℤ ℚ)) = aeval x p (via scalar tower ℤ → ℚ → ℝ)
    rwa [Polynomial.aeval_map_algebraMap]

-- ============================================================================
-- § 7. Main Theorem: Countability via Cantor Height Stratification
-- ============================================================================

/-- **Cantor's 1874 Theorem (Height Function Version)**: The algebraic real numbers
are countable.

The algebraic reals decompose as a **countable union of finite sets** (the height strata):
  algebraic reals = ⋃ₕ algebraicRealsOfHeight(h)

Since each `algebraicRealsOfHeight h` is finite (by `finite_algebraicRealsOfHeight`),
their countable union is countable. ∎

This is the original Cantor 1874 argument, now fully formalized in Lean 4. -/
theorem algebraic_reals_countable_via_height :
    Set.Countable {x : ℝ | IsAlgebraic ℚ x} := by
  rw [algebraic_reals_eq_iUnion_height]
  exact Set.countable_iUnion (fun h => (finite_algebraicRealsOfHeight h).countable)

-- ============================================================================
-- § 8. Structural Properties
-- ============================================================================

/-- The height strata form an increasing filtration. -/
theorem algebraicRealsOfHeight_mono (h : ℕ) :
    algebraicRealsOfHeight h ⊆ algebraicRealsOfHeight (h + 1) := by
  intro x ⟨⟨p, hp_ne, hp_height⟩, hroot⟩
  exact ⟨⟨p, hp_ne, Nat.le_succ_of_le hp_height⟩, hroot⟩

/-- Algebraic reals of bounded height have the same cardinality property. -/
theorem card_algebraic_reals_eq_aleph0 :
    Cardinal.mk {x : ℝ // IsAlgebraic ℚ x} = Cardinal.aleph0 :=
  Algebraic.cardinalMk_of_countable_of_charZero ℚ ℝ

/-- Finitely many algebraic reals have Cantor height ≤ h. -/
theorem finite_algebraicReals_bounded_height (h : ℕ) :
    Set.Finite {x : ℝ | IsAlgebraic ℚ x ∧
      ∃ p : Polynomial ℤ, p ≠ 0 ∧ cantorHeight p ≤ h ∧ Polynomial.aeval x p = 0} :=
  (finite_algebraicRealsOfHeight h).subset (by
    intro x ⟨_, p, hp_ne, hp_h, hp_eval⟩
    simp only [algebraicRealsOfHeight, Set.mem_iUnion]
    exact ⟨⟨p, hp_ne, hp_h⟩, hp_eval⟩)

/-
## Summary

### Proof Organization

§ 1–2: The Cantor height function and its basic properties.
  - cantorHeight p = natDegree p + ∑|coeff i|
  - Degree and coefficients are bounded by height.

§ 3: Key theorem — finitely many polynomials of each height.
  - Proof via injection into the finite Fintype (Fin(h+1) → Icc(-h,h))
  - The injection sends p to its coefficient tuple

§ 4: Each nonzero polynomial has finitely many real roots.
  - Direct from Polynomial.setOf_isRoot_finite

§ 5–7: The height stratification gives countability.
  - algebraicRealsOfHeight h is finite (finite index × finite fibers)
  - Every algebraic real has some height (via integerNormalization)
  - Countable union of finite sets = countable

### Formalized Results
- 0 sorries (all theorems proved)
- 0 axioms (no extra assumptions)
- Key Mathlib: setOf_isRoot_finite, integerNormalization_aeval_eq_zero,
               Finset.single_le_sum, Fin.sum_univ_eq_sum_range, sum_ite_eq', Int.natAbs_le
-/

end AlgebraicNumbersCountableOQ05
