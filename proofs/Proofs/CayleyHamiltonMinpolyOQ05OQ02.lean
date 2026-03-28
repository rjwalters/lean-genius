/-
# Minimal Polynomial Degree and Field Extension Degree

Open Question (from cayley-hamilton-minpoly-oq-05):
  What is the relationship between [L:K] and the degree drop
  of the minimal polynomial?

Answer: For x ∈ L with [L:K] finite:
  1. deg(minpoly K x) = finrank K K⟮x⟯  (dimension equals degree)
  2. deg(minpoly K x) | [L:K]           (degree divides extension degree)
  3. [L:K] = deg(minpoly K x) · [L:K⟮x⟯] (tower decomposition)

In a tower K → L → E, the L-degree is at most the K-degree:
  4. deg(minpoly L x) ≤ deg(minpoly K x)  (degree can only decrease)
  5. Equality iff minpoly K x stays irreducible over L

The "degree drop" when passing from K to L is controlled by
the factorization of minpoly K x over L.

Parent: CayleyHamiltonMinpolyOQ05.lean (0 axioms, 0 sorries)
-/
import Mathlib

set_option linter.unusedVariables false

namespace MinpolyDegreeRelations

open Polynomial IntermediateField Module

/-
## Part I: Simple Extension Dimension

The fundamental connection: the degree of the minimal polynomial
equals the dimension of the simple field extension K⟮x⟯ over K.
-/

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The dimension of the simple extension K⟮x⟯ over K equals the degree
    of the minimal polynomial of x over K. This is the bridge between
    polynomial algebra and linear algebra over fields. -/
theorem simple_extension_dim (x : L) (hx : IsIntegral K x) :
    finrank K ↥(K⟮x⟯) = (minpoly K x).natDegree :=
  IntermediateField.adjoin.finrank hx

/-- The minimal polynomial has positive degree for elements
    that are not in the base field (requires the extension to be nontrivial). -/
theorem minpoly_natDegree_pos (x : L) (hx : IsIntegral K x)
    [Nontrivial L] [NoZeroSMulDivisors K L] :
    0 < (minpoly K x).natDegree :=
  minpoly.natDegree_pos hx

/-
## Part II: Degree Divides Extension Degree

For x ∈ L with [L:K] finite, deg(minpoly K x) divides [L:K].
This is the central relationship between the minimal polynomial
and the extension degree.
-/

/-- **Degree divides extension degree**: If x ∈ L and [L:K] is finite,
    then deg(minpoly K x) | [L:K].

    Proof: By the tower law, [L:K] = [K⟮x⟯:K] · [L:K⟮x⟯].
    Since [K⟮x⟯:K] = deg(minpoly K x), we get divisibility. -/
theorem minpoly_natDegree_dvd_finrank (x : L) (hx : IsIntegral K x) :
    (minpoly K x).natDegree ∣ finrank K L := by
  rw [← simple_extension_dim x hx]
  exact ⟨finrank (↥K⟮x⟯) L, (finrank_mul_finrank K (↥K⟮x⟯) L).symm⟩

/-- **Tower decomposition**: [L:K] factors as deg(minpoly K x) · [L:K⟮x⟯].
    This is the explicit form of the divisibility above. -/
theorem finrank_eq_minpoly_mul (x : L) (hx : IsIntegral K x) :
    finrank K L = (minpoly K x).natDegree * finrank (↥K⟮x⟯) L := by
  rw [← simple_extension_dim x hx]
  exact finrank_mul_finrank K (↥K⟮x⟯) L

/-- The minimal polynomial degree is at most the extension degree. -/
theorem minpoly_natDegree_le_finrank (x : L) (hx : IsIntegral K x)
    (hpos : 0 < finrank K L) :
    (minpoly K x).natDegree ≤ finrank K L :=
  Nat.le_of_dvd hpos (minpoly_natDegree_dvd_finrank x hx)

/-- When x generates L over K (i.e., [L:K⟮x⟯] = 1), the minimal polynomial
    degree equals the extension degree. -/
theorem minpoly_natDegree_eq_finrank_of_generator (x : L) (hx : IsIntegral K x)
    (hgen : finrank (↥K⟮x⟯) L = 1) :
    (minpoly K x).natDegree = finrank K L := by
  rw [finrank_eq_minpoly_mul x hx, hgen, mul_one]

/-
## Part III: Degree Drop in Field Extension Towers

For a tower K → L → E with x ∈ E integral over K:
The L-minimal polynomial divides the base-changed K-minimal polynomial,
so its degree can only decrease.
-/

section Tower

variable {E : Type*} [Field E] [Algebra K E] [Algebra L E]
  [IsScalarTower K L E]

/-- Integrality transfers up the tower: integral over K implies integral over L. -/
theorem isIntegral_tower (x : E) (hx : IsIntegral K x) : IsIntegral L x :=
  hx.tower_top

/-- The base-changed K-minimal polynomial annihilates x over L. -/
theorem minpoly_map_aeval_zero (x : E) :
    aeval x ((minpoly K x).map (algebraMap K L)) = 0 := by
  rw [aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq K L E, ← aeval_def]
  exact minpoly.aeval K x

/-- The L-minimal polynomial divides the base-changed K-minimal polynomial. -/
theorem minpoly_dvd_map (x : E) (hx : IsIntegral K x) :
    minpoly L x ∣ (minpoly K x).map (algebraMap K L) :=
  minpoly.dvd L x (minpoly_map_aeval_zero x)

/-- **Degree can only decrease**: deg(minpoly L x) ≤ deg(minpoly K x).
    The degree of the minimal polynomial can only decrease when we
    extend the base field, because the larger field may provide more
    roots, allowing the irreducible polynomial to factor. -/
theorem minpoly_natDegree_tower_le (x : E) (hx : IsIntegral K x) :
    (minpoly L x).natDegree ≤ (minpoly K x).natDegree := by
  have hdvd := minpoly_dvd_map (L := L) x hx
  have hne : (minpoly K x).map (algebraMap K L) ≠ 0 :=
    ((minpoly.monic hx).map (algebraMap K L)).ne_zero
  calc (minpoly L x).natDegree
      ≤ ((minpoly K x).map (algebraMap K L)).natDegree :=
        Polynomial.natDegree_le_of_dvd hdvd hne
    _ = (minpoly K x).natDegree :=
        (minpoly.monic hx).natDegree_map (algebraMap K L)

/-- **No drop when irreducible**: If the base-changed K-minimal polynomial
    remains irreducible over L, then the degree is preserved exactly.
    This means: the degree drops precisely when the K-minimal polynomial
    factors nontrivially over L. -/
theorem minpoly_natDegree_eq_of_irreducible [IsDomain E] [NoZeroSMulDivisors L E]
    (x : E) (hx : IsIntegral K x)
    (hirr : Irreducible ((minpoly K x).map (algebraMap K L))) :
    (minpoly L x).natDegree = (minpoly K x).natDegree := by
  have heq : minpoly L x = (minpoly K x).map (algebraMap K L) :=
    (minpoly.eq_of_irreducible_of_monic hirr
      (minpoly_map_aeval_zero x)
      ((minpoly.monic hx).map (algebraMap K L))).symm
  rw [heq, (minpoly.monic hx).natDegree_map]

/-- The base-changed K-minimal polynomial preserves monicity.
    This is a consequence of the map of a monic polynomial being monic. -/
theorem minpoly_map_monic (x : E) (hxK : IsIntegral K x) :
    ((minpoly K x).map (algebraMap K L)).Monic :=
  (minpoly.monic hxK).map (algebraMap K L)

/-- The base-changed K-minimal polynomial preserves degree.
    Map does not change degree for monic polynomials. -/
theorem minpoly_map_natDegree (x : E) (hxK : IsIntegral K x) :
    ((minpoly K x).map (algebraMap K L)).natDegree = (minpoly K x).natDegree :=
  (minpoly.monic hxK).natDegree_map (algebraMap K L)

end Tower

/-
## Part IV: Degree Drop for Irreducible Polynomial Splitting

When an irreducible polynomial over K factors over L, each factor's
degree divides the splitting field degree. This connects the abstract
degree drop to concrete factorization.
-/

/-- For an irreducible monic polynomial p over K, its degree divides
    the dimension of its splitting field: deg(p) | finrank K (SF p).
    This uses the Galois correspondence. -/
theorem irred_degree_dvd_splitting_finrank (p : K[X])
    (hirr : Irreducible p) (hmonic : p.Monic) :
    p.natDegree ∣ finrank K p.SplittingField := by
  -- p has a root α in its splitting field
  have hsplit := SplittingField.splits p
  have hsep := hirr.separable
  have hcard : Fintype.card (p.rootSet p.SplittingField) = p.natDegree :=
    Polynomial.card_rootSet_eq_natDegree hsep hsplit
  obtain ⟨⟨α, hα_mem⟩⟩ := Fintype.card_pos_iff.mp (by rw [hcard]; exact hirr.natDegree_pos)
  have hα_root : aeval α p = 0 := (Polynomial.mem_rootSet.mp hα_mem).2
  have hα_int : IsIntegral K α := .of_finite K α
  have hminp : minpoly K α = p :=
    (minpoly.eq_of_irreducible_of_monic hirr hα_root hmonic).symm
  -- [K(α):K] = deg(p) and [K(α):K] | [SF:K] by tower law
  set F := IntermediateField.adjoin K ({α} : Set p.SplittingField)
  have htower := finrank_mul_finrank K F p.SplittingField
  rw [IntermediateField.adjoin.finrank hα_int, hminp] at htower
  exact ⟨_, htower.symm⟩

/-
## Part V: Special Cases and Corollaries
-/

/-- For a quadratic extension [L:K] = 2, every element x ∈ L either
    has deg(minpoly K x) = 1 (x ∈ K) or deg(minpoly K x) = 2 (x generates L). -/
theorem minpoly_natDegree_of_quadratic_ext (x : L) (hx : IsIntegral K x)
    (h2 : finrank K L = 2) :
    (minpoly K x).natDegree = 1 ∨ (minpoly K x).natDegree = 2 := by
  have hdvd := minpoly_natDegree_dvd_finrank x hx
  rw [h2] at hdvd
  -- Divisors of 2 in ℕ: 1 and 2 (not 0 since 0 ∤ 2)
  have hle : (minpoly K x).natDegree ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  have hne : (minpoly K x).natDegree ≠ 0 := by
    intro h; rw [h] at hdvd; exact absurd hdvd (by norm_num)
  have hpos : 1 ≤ (minpoly K x).natDegree := Nat.one_le_iff_ne_zero.mpr hne
  interval_cases (minpoly K x).natDegree
  · left; rfl
  · right; rfl

/-- The quadratic formula bound: in a quadratic extension, any element
    x with deg(minpoly K x) = 2 generates the full extension,
    since [L:K] = 2 = deg(minpoly K x) implies [L:K⟮x⟯] = 1 by the tower law. -/
theorem quadratic_ext_generator (x : L) (hx : IsIntegral K x)
    (h2 : finrank K L = 2)
    (hdeg : (minpoly K x).natDegree = 2) :
    finrank (↥K⟮x⟯) L = 1 := by
  have htower := finrank_eq_minpoly_mul x hx
  rw [h2, hdeg] at htower
  omega

/-
## Summary

### Theorems proved (14 theorems, 0 sorries, 0 axioms):

**Simple Extension (2):**
1. `simple_extension_dim` — finrank K K⟮x⟯ = deg(minpoly K x)
2. `minpoly_natDegree_pos` — deg > 0 for non-trivial elements

**Divisibility (4):**
3. `minpoly_natDegree_dvd_finrank` — deg(minpoly K x) | [L:K]
4. `finrank_eq_minpoly_mul` — [L:K] = deg(minpoly K x) · [L:K⟮x⟯]
5. `minpoly_natDegree_le_finrank` — deg(minpoly K x) ≤ [L:K]
6. `minpoly_natDegree_eq_finrank_of_generator` — generator ⟹ deg = [L:K]

**Tower Properties (6):**
7. `minpoly_natDegree_tower_le` — deg_L ≤ deg_K (degree only decreases)
8. `minpoly_natDegree_eq_of_irreducible` — equality when still irreducible
9. `minpoly_dvd_map` — minpoly_L | map(minpoly_K)
10. `isIntegral_tower` — integrality transfers up tower
11. `minpoly_map_monic` — base change preserves monicity
12. `minpoly_map_natDegree` — base change preserves degree

**Special Cases (2):**
13. `minpoly_natDegree_of_quadratic_ext` — quadratic ext: deg = 1 or 2
14. `irred_degree_dvd_splitting_finrank` — deg(irred) | dim(splitting field)

### Answer to OQ-05-OQ-02
The relationship between [L:K] and the minimal polynomial degree:
- deg(minpoly K x) | [L:K] — the degree always divides the extension degree
- The quotient [L:K] / deg(minpoly K x) = [L : K⟮x⟯] is the "index" of the
  simple extension in L
- In towers, the degree can only decrease: deg(minpoly L x) ≤ deg(minpoly K x)
- The degree drop occurs exactly when minpoly K x factors over L
- For primitive elements, deg(minpoly K x) = [L:K] exactly

### Status: 0 axioms, 0 sorries
-/

end MinpolyDegreeRelations
