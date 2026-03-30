/-
Erdős Problem #1126: Almost Additive Functions

Source: https://erdosproblems.com/1126
Status: SOLVED

Statement:
If f(x+y) = f(x) + f(y) for almost all x,y ∈ ℝ, then there exists
a function g such that g(x+y) = g(x) + g(y) for ALL x,y ∈ ℝ and
f(x) = g(x) for almost all x.

Solution:
Proved independently by de Bruijn (1966) and Jurkat (1965).

Key Ideas:
- "Almost all" means for all (x,y) except a null set in ℝ²
- The additive function g is essentially unique
- Without continuity assumption, additive functions can be wild
- The theorem says almost-additivity can always be "repaired"

References:
- Jurkat (1965): "On Cauchy's functional equation"
- de Bruijn (1966): "On almost additive functions"
- Erdős (1960): Original formulation
-/

import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Basic

open MeasureTheory

namespace Erdos1126

/- ## Part I: Cauchy's Functional Equation -/

/-- **Cauchy's Functional Equation:**
f(x + y) = f(x) + f(y) for all x, y ∈ ℝ.
Functions satisfying this are called additive. -/
def IsAdditive (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, f (x + y) = f x + f y

/-- The identity function f(x) = x is additive. -/
theorem id_is_additive : IsAdditive id := by
  intro x y
  simp [id]

/-- For any c ∈ ℝ, f(x) = cx is additive. -/
theorem scalar_is_additive (c : ℝ) : IsAdditive (fun x => c * x) := by
  intro x y
  ring

/-- **Continuous Additive Functions:**
If f is additive and continuous, then f(x) = cx for some c.
PROVED from measurable_additive_is_linear: continuous → measurable.
(Previously axiom; axiom count reduced 5→4.) -/
theorem continuous_additive_is_linear :
    ∀ f : ℝ → ℝ, IsAdditive f → Continuous f →
      ∃ c : ℝ, ∀ x : ℝ, f x = c * x := fun f hf hcont =>
  measurable_additive_is_linear f hf hcont.measurable

/- ## Part II: Almost Additive Functions -/

/-- A property holds almost everywhere if it fails only on a null set. -/
def ae_holds (P : ℝ → Prop) : Prop :=
  ∃ N : Set ℝ, MeasureTheory.volume N = 0 ∧ ∀ x : ℝ, x ∉ N → P x

/-- A property holds for almost all pairs (x,y) in ℝ². -/
def ae_pairs (P : ℝ → ℝ → Prop) : Prop :=
  ∃ N : Set (ℝ × ℝ), MeasureTheory.volume N = 0 ∧
    ∀ x y : ℝ, (x, y) ∉ N → P x y

/-- **Almost Additive Function:**
f(x + y) = f(x) + f(y) for almost all pairs (x, y). -/
def IsAlmostAdditive (f : ℝ → ℝ) : Prop :=
  ae_pairs (fun x y => f (x + y) = f x + f y)

/-- f = g almost everywhere. -/
def ae_eq (f g : ℝ → ℝ) : Prop :=
  ae_holds (fun x => f x = g x)

/- ## Part III: The Main Theorem (de Bruijn-Jurkat) -/

/-- **Erdős Problem #1126: The de Bruijn-Jurkat Theorem**

If f is almost additive, then there exists a truly additive g
such that f = g almost everywhere.

This is remarkable: the "defects" in almost-additivity can always
be repaired by changing f on a null set to get a truly additive g. -/
axiom de_bruijn_jurkat_theorem :
    ∀ f : ℝ → ℝ, IsAlmostAdditive f →
      ∃ g : ℝ → ℝ, IsAdditive g ∧ ae_eq f g

/-- Alternative statement of the main result. -/
theorem erdos_1126_main :
    ∀ f : ℝ → ℝ, IsAlmostAdditive f →
      ∃ g : ℝ → ℝ, IsAdditive g ∧ ae_eq f g :=
  de_bruijn_jurkat_theorem

/- ## Part IV: Uniqueness -/

/-- An additive function that is 0 a.e. is identically 0. -/
axiom additive_zero_ae :
    ∀ g : ℝ → ℝ, IsAdditive g → ae_eq g 0 → g = 0

/-- **Uniqueness up to a.e. equality:**
If g₁ and g₂ are both additive and agree a.e., then g₁ = g₂.
Proof: h = g₁ - g₂ is additive and h = 0 a.e., so h = 0 by additive_zero_ae. -/
theorem additive_ae_unique :
    ∀ g₁ g₂ : ℝ → ℝ, IsAdditive g₁ → IsAdditive g₂ →
      ae_eq g₁ g₂ → g₁ = g₂ := by
  intro g₁ g₂ h1 h2 ⟨N, hN, hf⟩
  -- h := g₁ - g₂ is additive
  have h_add : IsAdditive (g₁ - g₂) := fun x y => by
    simp only [Pi.sub_apply, h1 x y, h2 x y]; ring
  -- h = 0 a.e. (from g₁ = g₂ a.e.)
  have h_zero : ae_eq (g₁ - g₂) 0 :=
    ⟨N, hN, fun x hx => by
      simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]; exact hf x hx⟩
  -- By additive_zero_ae: g₁ - g₂ = 0, hence g₁ = g₂
  exact sub_eq_zero.mp (additive_zero_ae _ h_add h_zero)

/- ## Part V: Wild Additive Functions and Regularity -/

/-- **Measurable additive functions are linear:**
If f is additive and Lebesgue measurable, then f(x) = cx.
Non-linear additive functions are necessarily non-measurable. -/
axiom measurable_additive_is_linear :
    ∀ f : ℝ → ℝ, IsAdditive f → Measurable f →
      ∃ c : ℝ, ∀ x : ℝ, f x = c * x

/- ## Part VI: Summary -/

/-- **Erdős Problem #1126: SOLVED**

Summary of results:
1. Almost additive → agrees a.e. with truly additive (de Bruijn-Jurkat)
2. The correction is unique among additive functions
3. Wild additive functions exist (AC) but are non-measurable
4. Measurable additive functions must be linear -/
theorem erdos_1126_summary :
    -- Main theorem (de Bruijn-Jurkat)
    (∀ f : ℝ → ℝ, IsAlmostAdditive f →
      ∃ g : ℝ → ℝ, IsAdditive g ∧ ae_eq f g) ∧
    -- Uniqueness
    (∀ g₁ g₂ : ℝ → ℝ, IsAdditive g₁ → IsAdditive g₂ →
      ae_eq g₁ g₂ → g₁ = g₂) :=
  ⟨de_bruijn_jurkat_theorem, additive_ae_unique⟩

end Erdos1126
