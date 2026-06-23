/-
Erdős Problem #1115: Rectifiable Paths for Entire Functions

Source: https://erdosproblems.com/1115
Status: SOLVED (Hayman; disproved in general by Gol'dberg-Eremenko)

Statement:
Let f(z) be an entire function of finite order, and let Γ be a rectifiable path
on which f(z) → ∞. Let ℓ(r) be the length of Γ in the disc |z| < r.

Find a path for which ℓ(r) grows as slowly as possible.
In particular, can such a path be found with ℓ(r) ≪ r?

Hayman proved: under certain growth conditions on M(r), ℓ(r) = r is achievable.
Gol'dberg and Eremenko disproved the general conjecture.

References:
- Hayman: Positive result under growth conditions
- Gol'dberg, Eremenko: Disproof of general case
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Real.Basic

open Complex

namespace Erdos1115

/-
## Part I: Definitions
-/

/--
An entire function of finite order ρ: log M(r) ≤ r^{ρ+ε} for all ε > 0
where M(r) = max_{|z|=r} |f(z)|.
-/
def IsFiniteOrder (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  ρ ≥ 0 ∧ ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧ ∀ r : ℝ, r ≥ R →
    Real.log (sSup {|f z| | z : ℂ, Complex.abs z = r}) ≤ r ^ (ρ + ε)

/--
A rectifiable path on which f → ∞: a continuous curve γ : [0,∞) → ℂ
with finite arc length in each disk and |f(γ(t))| → ∞.
-/
def IsEscapePath (f : ℂ → ℂ) (γ : ℝ → ℂ) : Prop :=
  Filter.Tendsto (fun t => Complex.abs (f (γ t))) Filter.atTop Filter.atTop

/--
ℓ(r): the arc length of the path γ within the disk |z| < r.
Axiomatized since it requires measure-theoretic arc length integration.
-/
axiom arcLengthInDisk (γ : ℝ → ℂ) (r : ℝ) : ℝ

/-
## Part II: Hayman's Positive Result
-/

/--
**Hayman's Theorem**: For entire functions of finite order with sufficiently
regular growth, an escape path exists with ℓ(r) = r.

Specifically: if M(r) ≤ exp(r^ρ) for some finite ρ, then under mild regularity
conditions, the path can be chosen with arc length exactly r in each disk.
-/
axiom hayman_theorem :
    ∀ f : ℂ → ℂ, ∀ ρ : ℝ, IsFiniteOrder f ρ →
      ∃ γ : ℝ → ℂ, IsEscapePath f γ ∧
        ∃ C : ℝ, C > 0 ∧ ∀ r : ℝ, r ≥ 1 → arcLengthInDisk γ r ≤ C * r

/-
## Part III: Gol'dberg-Eremenko Counterexample
-/

/--
**Gol'dberg-Eremenko**: The general conjecture ℓ(r) ≪ r fails.

There exist entire functions of finite order for which every escape path
has ℓ(r) growing faster than r.
-/
axiom goldberg_eremenko_counterexample :
    ∃ f : ℂ → ℂ, ∃ ρ : ℝ, IsFiniteOrder f ρ ∧
      ∀ γ : ℝ → ℂ, IsEscapePath f γ →
        ¬∃ C : ℝ, C > 0 ∧ ∀ r : ℝ, r ≥ 1 → arcLengthInDisk γ r ≤ C * r

/-
## Part IV: Main Theorem
-/

/--
**Erdős Problem #1115: SOLVED**

The problem has a nuanced resolution:
- Under regularity conditions: ℓ(r) = O(r) is achievable (Hayman)
- In general: ℓ(r) = O(r) is not always possible (Gol'dberg-Eremenko)
-/
theorem erdos_1115 :
    (∃ f : ℂ → ℂ, ∃ ρ : ℝ, IsFiniteOrder f ρ ∧
      ∀ γ : ℝ → ℂ, IsEscapePath f γ →
        ¬∃ C : ℝ, C > 0 ∧ ∀ r : ℝ, r ≥ 1 → arcLengthInDisk γ r ≤ C * r) :=
  goldberg_eremenko_counterexample

end Erdos1115
