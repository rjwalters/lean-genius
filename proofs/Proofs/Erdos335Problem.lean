/-
  Erdős Problem #335: Density Additivity Characterization

  Source: https://erdosproblems.com/335
  Status: OPEN

  Problem Statement:
  Characterize those A, B ⊆ ℕ with positive density such that
    d(A + B) = d(A) + d(B)

  Known Example:
  One way this can happen is if there exists θ > 0 such that
    A = { n > 0 : {nθ} ∈ X_A }  and  B = { n > 0 : {nθ} ∈ X_B }
  where {x} denotes the fractional part and X_A, X_B ⊆ ℝ/ℤ are such that
    μ(X_A + X_B) = μ(X_A) + μ(X_B)

  Open Question:
  Are all possible A and B generated in a similar way (using other groups)?

  Mathematical Background:
  - Usually d(A + B) ≥ min(d(A) + d(B), 1) (Plünnecke-Ruzsa type bounds)
  - The exact additivity d(A + B) = d(A) + d(B) is a special condition
  - The known examples arise from "structured" sets on the torus

  Tags: additive-combinatorics, density, sumsets, erdos-problem
-/

import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Set.Card
import Mathlib.Tactic

namespace Erdos335

open Set Filter

/-! ## Part I: Density Definitions -/

/-- The counting function: number of elements of A in {1,...,N}. -/
noncomputable def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  Set.ncard (A ∩ Set.Icc 1 N)

/-- The asymptotic density of a set A ⊆ ℕ (when the limit exists).
    We use lim_{N→∞} |A ∩ [1,N]| / N. -/
noncomputable def density (A : Set ℕ) : ℝ :=
  Filter.limUnder atTop (fun N => (countingFn A N : ℝ) / N)

/-- A set has positive density. -/
def HasPositiveDensity (A : Set ℕ) : Prop :=
  0 < density A

/-- The density exists (i.e., the limit converges). -/
def DensityExists (A : Set ℕ) : Prop :=
  ∃ d : ℝ, Filter.Tendsto (fun N => (countingFn A N : ℝ) / N) atTop (nhds d)

/-! ## Part II: Sumset Definition -/

/-- The sumset A + B = { a + b : a ∈ A, b ∈ B }. -/
def Sumset (A B : Set ℕ) : Set ℕ :=
  { n | ∃ a ∈ A, ∃ b ∈ B, n = a + b }

infixl:65 " +ₛ " => Sumset

/-! ## Part III: The Density Additivity Property -/

/-- The key property: d(A + B) = d(A) + d(B). -/
def DensityAdditive (A B : Set ℕ) : Prop :=
  DensityExists A ∧ DensityExists B ∧ DensityExists (A +ₛ B) ∧
  density (A +ₛ B) = density A + density B

/-! ## Part IV: Known Example - Fractional Part Construction -/

/-- Fractional part function. -/
noncomputable def frac (x : ℝ) : ℝ := x - ⌊x⌋

/-- A set constructed via fractional parts of nθ.
    A = { n > 0 : {nθ} ∈ X } -/
def FractionalPartSet (θ : ℝ) (X : Set ℝ) : Set ℕ :=
  { n | n > 0 ∧ frac (n * θ) ∈ X }

/-- Two sets X_A, X_B ⊆ [0,1) have additive measure (formally stated).
    This corresponds to μ(X_A + X_B) = μ(X_A) + μ(X_B) in ℝ/ℤ. -/
def MeasureAdditive (X_A X_B : Set ℝ) : Prop :=
  -- Simplified: the sets don't overlap "mod 1"
  -- Full definition would require measure theory on the torus
  True  -- Placeholder - full formalization requires MeasureTheory

/-- The known construction: if X_A and X_B have additive measure,
    then the corresponding fractional part sets have additive density. -/
axiom fractional_part_additive (θ : ℝ) (X_A X_B : Set ℝ)
    (hθ : θ > 0) (hirrational : Irrational θ) (hμ : MeasureAdditive X_A X_B) :
    DensityAdditive (FractionalPartSet θ X_A) (FractionalPartSet θ X_B)

/-! ## Part V: The Main Conjecture -/

/-- **Erdős Problem #335** (OPEN)

    Characterize those A, B ⊆ ℕ with positive density such that
    d(A + B) = d(A) + d(B).

    The known examples arise from fractional part constructions.
    The question asks: Are ALL such pairs generated in a similar way
    (possibly using other compact abelian groups)?

    This is an OPEN characterization problem. -/
def erdos_335 : Prop :=
  ∀ A B : Set ℕ,
    HasPositiveDensity A →
    HasPositiveDensity B →
    DensityAdditive A B →
    -- "Can be generated from a group rotation construction"
    -- This is the characterization to be determined
    True  -- Placeholder - the exact characterization is OPEN

/-! ## Part VI: Basic Properties -/

/-- The density of the empty set is 0. -/
axiom density_empty : density ∅ = 0

/-- Density is at most 1 for any set. -/
axiom density_le_one (A : Set ℕ) (hA : DensityExists A) : density A ≤ 1

/-- Density is non-negative. -/
axiom density_nonneg (A : Set ℕ) : density A ≥ 0

/-! ## Part VII: Plünnecke-Ruzsa Type Bound

For general sets, we have d(A + B) ≥ d(A) + d(B) - 1 (when the sum
exceeds 1, it gets "capped"). The exact equality d(A + B) = d(A) + d(B)
is a strong constraint that implies structured behavior.
-/

/-- The Plünnecke-Ruzsa lower bound (simplified form).
    In general, d(A + B) ≥ min(d(A) + d(B), 1). -/
axiom plunnecke_ruzsa_lower (A B : Set ℕ)
    (hA : DensityExists A) (hB : DensityExists B) (hAB : DensityExists (A +ₛ B)) :
    density (A +ₛ B) ≥ min (density A + density B) 1

/-! ## Summary

**Problem Status**: OPEN

**What we know**:
1. Fractional part constructions give examples of density-additive pairs
2. The construction uses irrational rotations on the torus
3. The condition d(A+B) = d(A) + d(B) is quite restrictive

**What we don't know**:
- Do ALL density-additive pairs arise from group rotation constructions?
- If not, what is the full characterization?
- Are there "exotic" examples not arising from groups?

**Formalization provides**:
- Definitions of density and density additivity
- Statement of the known fractional part construction
- Framework for the characterization problem
-/

#check density
#check DensityAdditive
#check erdos_335

end Erdos335
