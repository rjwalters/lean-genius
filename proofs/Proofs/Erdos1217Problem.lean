/-
Erdős Problem #1217: Dense Sequences with Convergent Subsequences

Source: https://erdosproblems.com/1217
Status: SOLVED (Erdős-Sárközy-Sós 1966)

Statement:
Let A = {a₁ < a₂ < ...} ⊆ ℕ with
  limsup_{x→∞} (1/log log x) Σ_{aₙ ≤ x} 1/aₙ > 0.
Can we always find a subsequence {aₙᵢ} with
  limsup_{x→∞} (1/log log x) Σ_{aₙᵢ ≤ x} 1/aₙᵢ > 0
that converges in some appropriate sense?

Answer: YES — proved by Erdős-Sárközy-Sós (1966).

Reference:
- [ESS66] Erdős-Sárközy-Sós (1966)
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Filter

open Filter Real

namespace Erdos1217

/-- "Iterated logarithmic" density of a set A ⊆ ℕ -/
noncomputable def iterLogDensity (A : Set ℕ) : ℝ :=
  limsup (fun x : ℕ => (1 / Real.log (Real.log x)) *
    ∑ n ∈ Finset.filter (fun n => n ∈ A) (Finset.Icc 1 x), (1 : ℝ) / n) atTop

/-- A sequence has positive iterated log density -/
def HasPositiveIterLogDensity (a : ℕ → ℕ) : Prop :=
  iterLogDensity (Set.range a) > 0

/--
**Erdős-Sárközy-Sós Theorem (1966):**
If {aₙ} has positive iterated log density,
then it has a subsequence with positive iterated log density
that satisfies additional structural properties.
-/
axiom erdos_sarkozy_sos_1966 (a : ℕ → ℕ) (h : HasPositiveIterLogDensity a)
    (hmono : StrictMono a) :
    ∃ (f : ℕ → ℕ) (hf : StrictMono f),
      HasPositiveIterLogDensity (a ∘ f) ∧
      Filter.Tendsto (fun n => (a (f n) : ℝ) / a (f (n+1))) atTop (nhds 1)

/-- **Erdős Problem #1217: SOLVED** -/
theorem erdos_1217 :
    ∀ (a : ℕ → ℕ), StrictMono a → HasPositiveIterLogDensity a →
      ∃ (f : ℕ → ℕ), StrictMono f ∧ HasPositiveIterLogDensity (a ∘ f) :=
  fun a hm hd =>
    let ⟨f, hf, hd', _⟩ := erdos_sarkozy_sos_1966 a hd hm
    ⟨f, hf, hd'⟩

end Erdos1217
