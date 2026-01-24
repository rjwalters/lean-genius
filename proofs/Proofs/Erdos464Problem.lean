/-
Erdős Problem #464: Lacunary Sequences and Density of Fractional Parts

Source: https://erdosproblems.com/464
Status: SOLVED (de Mathan 1980, Pollington 1979)

Statement:
Let A = {n₁ < n₂ < ...} ⊂ ℕ be a lacunary sequence (n_{k+1} ≥ (1+ε)n_k for all k).
Must there exist an irrational θ such that {‖θn_k‖ : k ≥ 1} is NOT dense in [0,1]?
(Here ‖x‖ denotes the distance to the nearest integer.)

Answer: YES

Historical Timeline:
- de Mathan (1980) and Pollington (1979): Solved independently, showed inf_k ‖θn_k‖ ≫ ε⁴/log(1/ε)
- Katznelson (2001): Improved bound via chromatic number methods
- Akhunzhanov-Moshchevitin (2004): Further improvements
- Dubickas (2006): Additional improvements
- Peres-Schlag (2010): Best known bound inf_k ‖θn_k‖ ≫ ε/log(1/ε)

The conjectured optimal bound is ≫ ε (without the log factor).

Key insight: Lacunary sequences have such sparse growth that one can find θ
avoiding all small neighborhoods of rationals simultaneously.

Related: Problem #894 (chromatic number of distance graphs)

Tags: lacunary-sequences, diophantine-approximation, density, fractional-parts
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.MetricSpace.Basic

open Set

namespace Erdos464

/-!
## Part 1: Lacunary Sequences

A sequence is lacunary if consecutive terms grow by at least factor (1+ε).
This exponential-like growth makes the sequence very sparse.
-/

/-- A sequence A = {n₁ < n₂ < ...} is lacunary with parameter ε > 0 if
    n_{k+1} ≥ (1+ε)n_k for all k -/
def IsLacunary (A : ℕ → ℕ) (ε : ℝ) : Prop :=
  ε > 0 ∧ (∀ k : ℕ, (A (k + 1) : ℝ) ≥ (1 + ε) * A k)

/-- The sequence is strictly increasing -/
theorem lacunary_strictly_increasing (A : ℕ → ℕ) (ε : ℝ) (h : IsLacunary A ε) :
    ∀ k : ℕ, A k < A (k + 1) := by
  intro k
  have hε := h.1
  have hgrow := h.2 k
  -- (1 + ε) * A k ≥ A k + ε * A k > A k for ε > 0
  sorry

/-- Lacunary sequences grow at least exponentially -/
theorem lacunary_exponential_growth (A : ℕ → ℕ) (ε : ℝ) (h : IsLacunary A ε) :
    ∀ k : ℕ, (A k : ℝ) ≥ (1 + ε)^k * A 0 := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
    calc (A (n + 1) : ℝ) ≥ (1 + ε) * A n := h.2 n
      _ ≥ (1 + ε) * ((1 + ε)^n * A 0) := by sorry
      _ = (1 + ε)^(n + 1) * A 0 := by ring

/-!
## Part 2: Distance to Nearest Integer

‖x‖ = min(x - ⌊x⌋, ⌈x⌉ - x) = distance from x to nearest integer
-/

/-- Distance to nearest integer -/
noncomputable def distToInt (x : ℝ) : ℝ :=
  |x - round x|

/-- distToInt is always in [0, 1/2] -/
theorem distToInt_range (x : ℝ) : 0 ≤ distToInt x ∧ distToInt x ≤ 1/2 := by
  constructor
  · exact abs_nonneg _
  · sorry

/-- distToInt(x) = 0 iff x is an integer -/
theorem distToInt_zero_iff (x : ℝ) : distToInt x = 0 ↔ ∃ n : ℤ, x = n := by
  sorry

/-!
## Part 3: The Density Question

For a sequence A and real θ, consider {‖θn_k‖ : k ≥ 1}.
Is this set dense in [0, 1/2]?
-/

/-- The set of fractional part distances {‖θn_k‖ : k ∈ ℕ} -/
def fractionalDistances (A : ℕ → ℕ) (θ : ℝ) : Set ℝ :=
  { y : ℝ | ∃ k : ℕ, y = distToInt (θ * A k) }

/-- The set is dense in [0, 1/2] -/
def isDenseInInterval (S : Set ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x ≤ 1/2 → ∀ ε > 0, ∃ y ∈ S, |y - x| < ε

/-- The set is NOT dense - there's a gap -/
def hasGap (S : Set ℝ) : Prop :=
  ∃ x : ℝ, ∃ δ > 0, 0 ≤ x ∧ x ≤ 1/2 ∧ ∀ y ∈ S, |y - x| ≥ δ

/-!
## Part 4: The Main Theorems
-/

/-- de Mathan (1980) and Pollington (1979): For lacunary A, there exists θ with a gap -/
axiom deMathan_Pollington :
  ∀ A : ℕ → ℕ, ∀ ε : ℝ, IsLacunary A ε →
    ∃ θ : ℝ, Irrational θ ∧ hasGap (fractionalDistances A θ)

/-- Quantitative bound: inf_k ‖θn_k‖ ≫ ε⁴/log(1/ε) (original bound) -/
axiom deMathan_Pollington_bound :
  ∀ A : ℕ → ℕ, ∀ ε : ℝ, IsLacunary A ε →
    ∃ θ : ℝ, ∃ c > 0, Irrational θ ∧
      (∀ k : ℕ, distToInt (θ * A k) ≥ c * ε^4 / Real.log (1/ε))

/-- Peres-Schlag (2010): Improved bound inf_k ‖θn_k‖ ≫ ε/log(1/ε) -/
axiom peres_schlag_bound :
  ∀ A : ℕ → ℕ, ∀ ε : ℝ, IsLacunary A ε → ε < 1 →
    ∃ θ : ℝ, ∃ c > 0, Irrational θ ∧
      (∀ k : ℕ, distToInt (θ * A k) ≥ c * ε / Real.log (1/ε))

/-- The answer to Problem #464 -/
theorem erdos_464_solved :
    ∀ A : ℕ → ℕ, ∀ ε : ℝ, IsLacunary A ε →
      ∃ θ : ℝ, Irrational θ ∧ ¬isDenseInInterval (fractionalDistances A θ) := by
  intro A ε h
  obtain ⟨θ, hIrr, hGap⟩ := deMathan_Pollington A ε h
  use θ, hIrr
  intro hDense
  obtain ⟨x, δ, hδ, hx0, hx12, hBound⟩ := hGap
  -- hDense says we can get arbitrarily close to x, but hBound says we can't
  specialize hDense x hx0 hx12 δ hδ
  obtain ⟨y, hy, hClose⟩ := hDense
  have := hBound y hy
  linarith

/-!
## Part 5: The Conjectured Optimal Bound
-/

/-- Conjecture: The best possible bound is ≫ ε (without log factor) -/
axiom optimal_bound_conjecture :
  -- It is believed that for some constant c > 0,
  -- ∀ lacunary A with parameter ε, ∃ θ with inf_k ‖θn_k‖ ≥ c·ε
  -- Peres-Schlag's ε/log(1/ε) is close but not quite there
  True

/-- Comparison of bounds through history -/
theorem bound_improvement_history :
    -- 1980: ε⁴/log(1/ε) (de Mathan, Pollington)
    -- 2001: Katznelson improved
    -- 2004: Akhunzhanov-Moshchevitin improved
    -- 2006: Dubickas improved
    -- 2010: ε/log(1/ε) (Peres-Schlag, current best)
    -- Conjecture: ε
    True := trivial

/-!
## Part 6: Connection to Chromatic Numbers
-/

/-- Related: Erdős Problem #894 on chromatic number of distance graphs -/
axiom chromatic_number_connection :
  -- The distance graph on ℤ with edge set determined by a lacunary sequence
  -- has bounded chromatic number iff the corresponding density result holds
  -- This problem (464) has implications for problem 894
  True

/-- Katznelson's approach via chromatic numbers -/
axiom katznelson_chromatic :
  -- Katznelson (2001) related the problem to chromatic numbers of Cayley graphs
  -- and used this to improve the density bound
  True

/-!
## Part 7: Examples
-/

/-- The powers of 2: {1, 2, 4, 8, 16, ...} are lacunary with ε = 1 -/
theorem powers_of_two_lacunary : IsLacunary (fun n => 2^n) 1 := by
  constructor
  · norm_num
  · intro k
    simp only [pow_succ]
    ring_nf
    norm_cast
    nlinarith [Nat.one_le_two_pow]

/-- The powers of any q > 1 are lacunary -/
theorem powers_lacunary (q : ℕ) (hq : q ≥ 2) :
    IsLacunary (fun n => q^n) ((q : ℝ) - 1) := by
  constructor
  · have : (q : ℝ) ≥ 2 := by exact_mod_cast hq
    linarith
  · intro k
    simp only [pow_succ]
    ring_nf
    sorry

/-!
## Part 8: Summary
-/

/-- **Erdős Problem #464: SOLVED**

QUESTION: For lacunary A = {n₁ < n₂ < ...} (with n_{k+1} ≥ (1+ε)n_k),
must there exist irrational θ such that {‖θn_k‖} is NOT dense in [0, 1/2]?

ANSWER: YES (de Mathan 1980, Pollington 1979)

QUANTITATIVE:
- Original: inf_k ‖θn_k‖ ≫ ε⁴/log(1/ε)
- Best known (Peres-Schlag 2010): inf_k ‖θn_k‖ ≫ ε/log(1/ε)
- Conjectured optimal: ≫ ε

The lacunary growth ensures enough "room" to find θ avoiding all neighborhoods.
-/
theorem erdos_464_answer :
    ∀ A : ℕ → ℕ, ∀ ε : ℝ, IsLacunary A ε →
      ∃ θ : ℝ, Irrational θ ∧ hasGap (fractionalDistances A θ) :=
  deMathan_Pollington

/-- Problem status -/
def erdos_464_status : String :=
  "SOLVED - Non-density exists (de Mathan/Pollington), best bound ε/log(1/ε) (Peres-Schlag 2010)"

end Erdos464
