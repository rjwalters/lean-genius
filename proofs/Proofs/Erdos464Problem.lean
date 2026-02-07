/-
Erdős Problem #464: Lacunary Sequences and Irrational Multiples

Source: https://erdosproblems.com/464
Status: SOLVED (de Mathan 1980, Pollington 1979)

Statement:
Let A = {n₁ < n₂ < ...} ⊂ ℕ be a lacunary sequence (n_{k+1} ≥ (1+ε)nₖ for some ε > 0).
Must there exist an irrational θ such that {‖θnₖ‖ : k ≥ 1} is not dense in [0,1]
(where ‖x‖ is the distance to the nearest integer)?

Answer: YES

Solved independently by de Mathan and Pollington, who showed that given any
lacunary sequence A, there exists θ with inf_{k≥1} ‖θnₖ‖ > 0.
Peres and Schlag improved the bound to ≫ ε/log(1/ε).

References:
- de Mathan (1980): Independent proof
- Pollington (1979): Independent proof
- Peres, Schlag: Improved quantitative bounds
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Basic

namespace Erdos464

/-
## Part I: Definitions
-/

/-- A sequence is lacunary with ratio 1 + ε. -/
def IsLacunary (a : ℕ → ℕ) (ε : ℝ) : Prop :=
  ε > 0 ∧ StrictMono a ∧ ∀ k, (a (k + 1) : ℝ) ≥ (1 + ε) * a k

/-- The distance to the nearest integer: ‖x‖ = min(x - ⌊x⌋, ⌈x⌉ - x). -/
noncomputable def distToInt (x : ℝ) : ℝ :=
  min (x - ↑(Int.floor x)) (↑(Int.ceil x) - x)

/-- The fractional multiples {‖θnₖ‖ : k ≥ 1} are not dense in [0,1]. -/
def NotDense (θ : ℝ) (a : ℕ → ℕ) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∀ k, distToInt (θ * a k) ≥ δ

/-
## Part II: de Mathan-Pollington Theorem
-/

/--
**de Mathan (1980) / Pollington (1979)**: For every lacunary sequence A,
there exists an irrational θ such that the set {‖θnₖ‖} avoids a
neighborhood of 0. In particular, {‖θnₖ‖} is not dense in [0,1].
-/
axiom de_mathan_pollington (a : ℕ → ℕ) (ε : ℝ) (h : IsLacunary a ε) :
    ∃ θ : ℝ, Irrational θ ∧ NotDense θ a

/-
## Part III: Peres-Schlag Improvement
-/

/--
**Peres-Schlag**: The gap can be bounded from below:
inf_{k≥1} ‖θnₖ‖ ≫ ε/log(1/ε) for suitable θ.
-/
axiom peres_schlag (a : ℕ → ℕ) (ε : ℝ) (h : IsLacunary a ε) (hε : ε < 1) :
    ∃ θ : ℝ, Irrational θ ∧ ∃ c : ℝ, c > 0 ∧
      ∀ k, distToInt (θ * a k) ≥ c * ε / Real.log (1 / ε)

/-
## Part IV: Main Theorem
-/

/--
**Erdős Problem #464: SOLVED**

For every lacunary sequence, there exists an irrational θ whose
multiples by the sequence elements stay bounded away from integers.
-/
theorem erdos_464 (a : ℕ → ℕ) (ε : ℝ) (h : IsLacunary a ε) :
    ∃ θ : ℝ, Irrational θ ∧ NotDense θ a :=
  de_mathan_pollington a ε h

end Erdos464
