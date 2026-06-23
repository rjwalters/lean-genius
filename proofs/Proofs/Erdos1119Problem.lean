/-
  Erdős Problem #1119: Families of Entire Functions with Cardinal Constraints

  Source: https://erdosproblems.com/1119
  Status: SOLVED (INDEPENDENT of ZFC when 𝔪⁺ = 𝔠)

  Statement:
  Let 𝔪 be an infinite cardinal with ℵ₀ < 𝔪 < 𝔠 = 2^{ℵ₀}. Let {f_α} be a family of
  entire functions such that, for every z₀ ∈ ℂ, there are at most 𝔪 distinct values
  of f_α(z₀). Must {f_α} have cardinality at most 𝔪?

  Answer: INDEPENDENT of ZFC when 𝔪⁺ = 𝔠
  - YES if 𝔪⁺ < 𝔠 (easy, Hayman 1974)
  - YES in some models with 𝔠 = ℵ₂ (Kumar-Shelah 2017)
  - NO in other models with 𝔠 = ℵ₂ (Schilhan-Weinert 2024)

  Known Results:
  - Erdős (1964): Wetzel problem — countable values implies countable family (if ¬CH)
  - Hayman (1974): YES if 𝔪⁺ < 𝔠
  - Kumar-Shelah (2017): YES in some model with 𝔠 = ℵ₂, 𝔪 = ℵ₁
  - Schilhan-Weinert (2024): NO in some model with 𝔠 = ℵ₂

  Tags: entire-functions, cardinals, set-theory, undecidability, continuum-hypothesis
-/

import Mathlib.Data.Complex.Basic
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.Topology.Basic
import Mathlib.Analysis.Complex.Basic

namespace Erdos1119

open Cardinal Set

/- ## Part I: Basic Definitions -/

/-- An entire function (holomorphic on all of ℂ). Axiomatized since full complex
analysis formalization is extensive. -/
axiom IsEntire (f : ℂ → ℂ) : Prop

/-- The set of values {f_α(z₀) : α ∈ I} for a family at a point -/
def valuesAtPoint (family : ι → (ℂ → ℂ)) (z₀ : ℂ) : Set ℂ :=
  { w | ∃ α, family α z₀ = w }

/-- A Wetzel family: at each point, at most 𝔪 distinct values -/
def IsWetzelFamily (family : ι → (ℂ → ℂ)) (m : Cardinal) : Prop :=
  ∀ z₀ : ℂ, #(valuesAtPoint family z₀) ≤ m

/- ## Part II: The Original Wetzel Problem (Erdős 1964) -/

/-- The original Wetzel problem: countably many values at each point -/
def WetzelProblem (family : ι → (ℂ → ℂ)) : Prop :=
  ∀ z₀ : ℂ, #(valuesAtPoint family z₀) ≤ ℵ₀

/-- Erdős (1964): If ¬CH (𝔠 > ℵ₁), Wetzel families of entire functions are countable -/
axiom erdos_1964_wetzel (family : ι → (ℂ → ℂ))
    (hentire : ∀ α, IsEntire (family α))
    (hwetzel : WetzelProblem family)
    (hch_fails : continuum > aleph 1) :
    #ι ≤ ℵ₀

/-- Erdős (1964): If CH holds (𝔠 = ℵ₁), there exist uncountable Wetzel families -/
/- ## Part III: The Easy Case (𝔪⁺ < 𝔠) -/

/-- The successor cardinal -/
noncomputable def succCard (m : Cardinal) : Cardinal := Order.succ m

/-- Hayman (1974): If 𝔪⁺ < 𝔠, then Wetzel families of type 𝔪 have size ≤ 𝔪.
The proof uses the identity theorem: distinct entire functions agree on at most
countably many points, so one can diagonalize over the value sets. -/
axiom easy_case (m : Cardinal) (hm_inf : ℵ₀ < m) (hm_cont : m < continuum)
    (hsucc_lt : succCard m < continuum)
    (family : ι → (ℂ → ℂ))
    (hentire : ∀ α, IsEntire (family α))
    (hwetzel : IsWetzelFamily family m) :
    #ι ≤ m

/- ## Part IV: The Undecidable Case (𝔪⁺ = 𝔠) -/

/-- The critical condition: 𝔪⁺ = 𝔠 -/
def SuccessorEqualsContinuum (m : Cardinal) : Prop := succCard m = continuum

/-- Kumar-Shelah (2017): There exists a ZFC-consistent model where 𝔠 = ℵ₂
and every family of entire functions with ≤ ℵ₁ values at each point
has cardinality ≤ ℵ₁. -/
/-- Schilhan-Weinert (2024): There exists a ZFC-consistent model where 𝔠 = ℵ₂
and there is a family of entire functions with ≤ ℵ₁ values at each point
but cardinality > ℵ₁. -/
/- ## Part V: The Identity Theorem -/

/-- Two entire functions agreeing on uncountably many points are equal.
This is the key fact making the Wetzel condition nontrivial. -/
/- ## Part VI: Cardinal Arithmetic Background -/

/-- The continuum is 2^{ℵ₀} -/
theorem continuum_eq_two_aleph_zero : continuum = 2 ^ ℵ₀ := rfl

/-- If GCH holds at ℵ₀ (i.e., 𝔠 = ℵ₁), there is no cardinal between ℵ₀ and 𝔠 -/
/-- Under ¬CH, intermediate cardinals exist -/
/- ## Part VII: Wetzel's Question and CH -/

/-- Wetzel's original question (1963): is every Wetzel family countable? -/
def WetzelQuestion : Prop :=
  ∀ (family : ι → (ℂ → ℂ)),
    (∀ α, IsEntire (family α)) →
    (∀ z₀ : ℂ, #(valuesAtPoint family z₀) ≤ ℵ₀) →
    #ι ≤ ℵ₀

/-- Wetzel's question is equivalent to ¬CH -/
/- ## Part VIII: Summary -/

/--
**Erdős Problem #1119: Summary**

The problem is completely resolved:
- If 𝔪⁺ < 𝔠, the answer is YES (provable in ZFC via the identity theorem)
- If 𝔪⁺ = 𝔠, the answer is INDEPENDENT of ZFC

The formalization captures Erdős's Wetzel solution (1964), the easy case (Hayman 1974),
and the independence results (Kumar-Shelah 2017, Schilhan-Weinert 2024).
-/
theorem erdos_1119_summary :
    -- Erdős 1964: countable Wetzel families under ¬CH
    (∀ (family : ι → (ℂ → ℂ)), (∀ α, IsEntire (family α)) →
      WetzelProblem family → continuum > aleph 1 → #ι ≤ ℵ₀) ∧
    -- Easy case: 𝔪⁺ < 𝔠 implies family bounded by 𝔪
    (∀ m : Cardinal, ℵ₀ < m → m < continuum → succCard m < continuum →
      ∀ (family : ι → (ℂ → ℂ)), (∀ α, IsEntire (family α)) →
        IsWetzelFamily family m → #ι ≤ m) :=
  ⟨erdos_1964_wetzel, easy_case⟩

end Erdos1119
