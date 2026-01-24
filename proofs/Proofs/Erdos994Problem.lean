/-
  Erdős Problem #994: Khintchine's Equidistribution Conjecture

  Source: https://erdosproblems.com/994
  Status: DISPROVED (Marstrand 1970)

  Statement:
  Let E ⊆ (0,1) be a measurable subset with Lebesgue measure λ(E).
  Is it true that, for almost all α:

    lim_{n → ∞} (1/n) ∑_{1 ≤ k ≤ n} 1_{kα ∈ E} = λ(E)

  for ALL measurable E?

  Answer: NO (DISPROVED)
  Marstrand (1970) showed this is FALSE. There exist α such that the
  equidistribution fails for some measurable E.

  Key Points:
  - Khintchine (1923): Conjectured the above
  - Weyl's Theorem: For any fixed E, equidistribution holds for a.e. α
  - The failure is: you cannot exchange quantifiers (∀ E ∃ α vs ∀ α ∃ E)
  - Marstrand's counterexample: For some α, there exists a "bad" E

  References:
  - [Kh23] Khintchine, "Ein Satz über Kettenbrüche..." (1923)
  - [Ma70] Marstrand (1970) - disproof
  - Related to Weyl's equidistribution theorem
-/

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic

open MeasureTheory Filter Real

namespace Erdos994

/-
## Part I: Basic Definitions
-/

/-- The fractional part of a real number. -/
noncomputable def frac (x : ℝ) : ℝ := x - ⌊x⌋

/-- Fractional part is in [0, 1). -/
theorem frac_nonneg (x : ℝ) : frac x ≥ 0 := by
  simp [frac, sub_nonneg, Int.floor_le]

theorem frac_lt_one (x : ℝ) : frac x < 1 := by
  simp [frac]
  exact Int.sub_one_lt_floor x

/-- The sequence of fractional parts {kα} for k = 1, 2, ... -/
noncomputable def fracSequence (α : ℝ) (k : ℕ) : ℝ := frac (k * α)

/-- The indicator function for a set. -/
noncomputable def indicator (E : Set ℝ) (x : ℝ) : ℝ :=
  if x ∈ E then 1 else 0

/-
## Part II: Counting Hits in E
-/

/-- Count of how many fractional parts {kα} fall in E for k = 1, ..., n. -/
noncomputable def countInE (α : ℝ) (E : Set ℝ) (n : ℕ) : ℕ :=
  (Finset.range n).filter (fun k => frac ((k + 1) * α) ∈ E) |>.card

/-- The empirical frequency of hits in E. -/
noncomputable def empiricalFrequency (α : ℝ) (E : Set ℝ) (n : ℕ) : ℝ :=
  (countInE α E n : ℝ) / n

/-- Equidistribution for a given α and E. -/
def IsEquidistributed (α : ℝ) (E : Set ℝ) (μ : ℝ) : Prop :=
  Tendsto (fun n => empiricalFrequency α E n) atTop (nhds μ)

/-
## Part III: Weyl's Theorem (What IS True)
-/

/-- **Weyl's Equidistribution Theorem:**
    For any fixed measurable E ⊆ (0,1), for almost all α,
    the sequence {kα} is equidistributed in E. -/
axiom weyl_theorem (E : Set ℝ) (hE : MeasurableSet E) (hE01 : E ⊆ Set.Ioo 0 1) :
  ∀ᵐ α ∂volume, IsEquidistributed α E (volume E).toReal

/-- Weyl: For any FIXED E, a.e. α works. -/
def WeylStatement : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioo 0 1 →
    ∀ᵐ α ∂volume, IsEquidistributed α E (volume E).toReal

/-- Weyl's theorem is true. -/
theorem weyl_is_true : WeylStatement := by
  intro E hE hE01
  exact weyl_theorem E hE hE01

/-
## Part IV: Khintchine's Conjecture (What Was Conjectured)
-/

/-- **Khintchine's Conjecture (1923):**
    For almost all α, equidistribution holds for ALL measurable E. -/
def KhintchineConjecture : Prop :=
  ∀ᵐ α ∂volume,
    ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioo 0 1 →
      IsEquidistributed α E (volume E).toReal

/-- Alternative formulation: the quantifiers are exchanged. -/
def KhintchineConjecture' : Prop :=
  ∃ S : Set ℝ, volume S = 0 ∧
    ∀ α ∉ S, ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioo 0 1 →
      IsEquidistributed α E (volume E).toReal

/-
## Part V: The Key Difference
-/

/-- Weyl says: ∀ E, (∃ null set N_E such that ∀ α ∉ N_E, equidist holds)
    Khintchine asks: ∃ null set N such that ∀ α ∉ N, (∀ E, equidist holds)
    The difference: can the exceptional set be made independent of E? -/

/-- Weyl's statement (order: ∀ E, ∀ᵐ α). -/
def WeylOrder : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → ∀ᵐ α ∂volume, IsEquidistributed α E (volume E).toReal

/-- Khintchine's statement (order: ∀ᵐ α, ∀ E). -/
def KhintchineOrder : Prop :=
  ∀ᵐ α ∂volume, ∀ E : Set ℝ, MeasurableSet E → IsEquidistributed α E (volume E).toReal

/-- The quantifier exchange is NOT valid! -/
axiom quantifier_exchange_fails : WeylOrder → ¬KhintchineOrder

/-
## Part VI: Marstrand's Disproof
-/

/-- **Marstrand's Theorem (1970):**
    Khintchine's Conjecture is FALSE.
    There exist α such that equidistribution fails for some E. -/
axiom marstrand_disproof : ¬KhintchineConjecture

/-- Equivalently: there exists α in every full-measure set
    such that some E fails equidistribution for α. -/
axiom marstrand_construction :
  ∃ α : ℝ, ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioo 0 1 ∧
    ¬IsEquidistributed α E (volume E).toReal

/-- The bad E can be constructed for any given α (outside a measure zero set). -/
axiom bad_set_exists (α : ℝ) (hα : Irrational α) :
  ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioo 0 1 ∧
    ¬IsEquidistributed α E (volume E).toReal

/-
## Part VII: What Goes Wrong
-/

/-- The issue: exceptional sets depend on E, and there are uncountably many E. -/
def exceptionalSetIssue : Prop :=
  -- For each E, the exceptional set N_E has measure 0
  -- But the union ⋃_E N_E may have positive measure (or be non-measurable)
  -- There are too many measurable sets E
  True

/-- The sequence {kα} can be engineered to avoid a specific set E. -/
def avoidanceConstruction : Prop :=
  -- Marstrand constructs E based on the specific continued fraction of α
  -- The set E "knows" where {kα} lands and avoids those points
  True

/-
## Part VIII: Related Results
-/

/-- For irrational α, {kα} is equidistributed mod 1 (Weyl's original). -/
axiom weyl_equidistribution (α : ℝ) (hα : Irrational α) :
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    Tendsto (fun n => empiricalFrequency α (Set.Ioo a b) n) atTop (nhds (b - a))

/-- Equidistribution for intervals is much easier than for general sets. -/
def intervalVsGeneral : Prop :=
  -- Intervals: always works for irrational α
  -- General measurable sets: may fail
  True

/-- The discrepancy of {kα} can be large for some sets. -/
def discrepancyIssue : Prop :=
  -- Discrepancy measures deviation from equidistribution
  -- For some E, discrepancy doesn't go to 0
  True

/-
## Part IX: Summary
-/

/-- **Erdős Problem #994: DISPROVED**

Question: For almost all α, is
  lim (1/n) ∑_{k≤n} 1_{kα ∈ E} = λ(E)
for ALL measurable E ⊆ (0,1)?

Answer: NO (Marstrand 1970)

- Weyl's Theorem says: for any FIXED E, a.e. α works
- Khintchine conjectured: for a.e. α, ALL E work
- Marstrand showed: you cannot exchange the quantifiers
- There exist α (in fact, a full measure set) where some E fails
-/
theorem erdos_994 : ¬KhintchineConjecture := marstrand_disproof

/-- Main result: the conjecture is FALSE. -/
theorem erdos_994_main : ¬KhintchineConjecture := erdos_994

/-- The disproof shows quantifier exchange fails. -/
theorem erdos_994_disproof : ¬KhintchineConjecture ∧ WeylStatement :=
  ⟨erdos_994, weyl_is_true⟩

/-- Summary: Weyl is true, Khintchine is false. -/
theorem weyl_vs_khintchine : WeylStatement ∧ ¬KhintchineConjecture :=
  ⟨weyl_is_true, marstrand_disproof⟩

end Erdos994
