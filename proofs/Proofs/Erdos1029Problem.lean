/-
  Erdős Problem #1029: Ramsey Number Growth Rate

  Source: https://erdosproblems.com/1029
  Status: OPEN ($100 for proof, $1000 for disproof)

  Statement:
  If R(k) is the diagonal Ramsey number (minimal n such that every
  2-coloring of K_n contains a monochromatic K_k), prove that
    R(k) / (k · 2^{k/2}) → ∞

  Background:
  The Erdős-Szekeres bounds give:
    (1+o(1)) · (k/e) · 2^{k/2} ≤ R(k) ≤ C(2k-2, k-1) ≈ 4^k / √k

  The lower bound comes from the probabilistic method: a random 2-coloring
  of K_n has expected number of monochromatic K_k's roughly n^k · 2^{-C(k,2)},
  which is < 1 when n ≈ k · 2^{k/2}.

  This problem asks whether R(k) grows strictly faster than k · 2^{k/2}.
  Equivalently: is the probabilistic lower bound far from tight?

  Spencer (1975) improved the lower bound constant to √2/e, but this still
  leaves the ratio R(k)/(k · 2^{k/2}) bounded. The conjecture asserts this
  ratio tends to infinity.

  References:
  [ES35] Erdős-Szekeres, "A combinatorial problem in geometry" (1935)
  [Er93] Erdős, "On some of my favourite problems" (1993)
  [Sp75] Spencer, "Ramsey's theorem - a new lower bound" (1975)

  Tags: ramsey-theory, graph-theory, probabilistic-method, open-problem
-/

import Mathlib

open Nat Filter

/-
## Ramsey Numbers

The diagonal Ramsey number R(k) and basic properties.
-/

/-- A 2-coloring of edges of a complete graph -/
def EdgeColoring (V : Type*) := Sym2 V → Bool

/-- A set of vertices is monochromatic in color c -/
def IsMonochromatic {V : Type*} (coloring : EdgeColoring V) (S : Set V) (c : Bool) : Prop :=
  ∀ x y : V, x ∈ S → y ∈ S → x ≠ y → coloring s(x, y) = c

/-- A coloring contains a monochromatic k-clique -/
def HasMonochromaticClique {V : Type*} [Fintype V] (coloring : EdgeColoring V) (k : ℕ) : Prop :=
  ∃ S : Finset V, S.card = k ∧ (IsMonochromatic coloring S true ∨ IsMonochromatic coloring S false)

/-- The diagonal Ramsey number R(k): minimal n such that every 2-coloring
    of K_n contains a monochromatic K_k -/
noncomputable def R (k : ℕ) : ℕ :=
  Nat.find (⟨4^k, by sorry⟩ : ∃ n, ∀ coloring : EdgeColoring (Fin n), HasMonochromaticClique coloring k)

/-- R(k) is well-defined: the property holds for n = R(k) -/
theorem R_spec (k : ℕ) : ∀ coloring : EdgeColoring (Fin (R k)), HasMonochromaticClique coloring k := by
  have := Nat.find_spec (⟨4^k, by sorry⟩ : ∃ n, ∀ coloring : EdgeColoring (Fin n), HasMonochromaticClique coloring k)
  exact this

/-
## Known Bounds

The Erdős-Szekeres bounds and Spencer's improvement.
-/

/-- Erdős-Szekeres upper bound: R(k) ≤ C(2k-2, k-1) -/
axiom erdos_szekeres_upper :
  ∀ k ≥ 2, R k ≤ Nat.choose (2*k - 2) (k - 1)

/-- Asymptotic form of upper bound: R(k) ≤ 4^k / √(πk) · (1 + o(1)) -/
axiom upper_bound_asymptotic :
  ∃ C : ℝ, C > 0 ∧ ∀ k ≥ 2, (R k : ℝ) ≤ C * 4^k / Real.sqrt k

/-- Erdős-Szekeres lower bound from probabilistic method -/
axiom erdos_szekeres_lower :
  ∃ c : ℝ, c > 0 ∧ ∀ k ≥ 2, (R k : ℝ) ≥ c * k * 2^(k/2 : ℝ)

/-- Spencer's improved lower bound constant: √2/e -/
axiom spencer_lower_bound :
  ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K,
    (R k : ℝ) ≥ (Real.sqrt 2 / Real.exp 1 - ε) * k * 2^(k/2 : ℝ)

/-
## The Conjecture

The central open problem: R(k) grows faster than k · 2^{k/2}.
-/

/-- The normalized ratio R(k) / (k · 2^{k/2}) -/
noncomputable def ramseyRatio (k : ℕ) : ℝ :=
  (R k : ℝ) / (k * 2^(k/2 : ℝ))

/-- Erdős's conjecture: the ratio tends to infinity -/
def erdos1029Conjecture : Prop :=
  Tendsto ramseyRatio atTop atTop

/-- Equivalent formulation: for every M, ratio eventually exceeds M -/
def erdos1029ConjectureAlt : Prop :=
  ∀ M : ℝ, ∃ K : ℕ, ∀ k ≥ K, ramseyRatio k > M

/-- The two formulations are equivalent -/
theorem conjecture_equiv : erdos1029Conjecture ↔ erdos1029ConjectureAlt := by
  constructor
  · intro h M
    rw [Tendsto, Filter.map_atTop_atTop] at h
    obtain ⟨K, hK⟩ := h M
    exact ⟨K, fun k hk => hK k hk⟩
  · intro h
    rw [Tendsto, Filter.map_atTop_atTop]
    intro M
    obtain ⟨K, hK⟩ := h M
    exact ⟨K, fun k hk => le_of_lt (hK k hk)⟩

/-
## Lower Bound is Not Tight

What we know: the ratio is bounded below, but possibly not above.
-/

/-- The ratio is bounded below by Spencer's constant -/
axiom ratio_bounded_below :
  ∀ ε > 0, ∃ K : ℕ, ∀ k ≥ K, ramseyRatio k ≥ Real.sqrt 2 / Real.exp 1 - ε

/-- If conjecture is false, ratio is bounded -/
def conjectureNegation : Prop :=
  ∃ M : ℝ, ∀ k : ℕ, ramseyRatio k ≤ M

/-- Negation equivalence -/
theorem negation_equiv : ¬erdos1029Conjecture ↔ conjectureNegation := by
  sorry

/-
## Small Values

Known exact values of Ramsey numbers.
-/

/-- R(1) = 1 (trivial) -/
axiom R_1 : R 1 = 1

/-- R(2) = 2 (need 2 vertices for an edge) -/
axiom R_2 : R 2 = 2

/-- R(3) = 6 (classical result) -/
axiom R_3 : R 3 = 6

/-- R(4) = 18 (Greenwood-Gleason 1955) -/
axiom R_4 : R 4 = 18

/-- R(5) is between 43 and 48 -/
axiom R_5_bounds : 43 ≤ R 5 ∧ R 5 ≤ 48

/-
## Ratio Values for Small k

The ratio for known Ramsey numbers.
-/

/-- Ratio at k=3: R(3)/(3·2^{3/2}) = 6/(3·2√2) ≈ 0.707 -/
theorem ratio_3 : ramseyRatio 3 = 6 / (3 * 2^(3/2 : ℝ)) := by
  simp only [ramseyRatio, R_3]
  ring

/-- Ratio at k=4: R(4)/(4·2^2) = 18/16 = 1.125 -/
theorem ratio_4 : ramseyRatio 4 = 18 / (4 * 2^(2 : ℝ)) := by
  simp only [ramseyRatio, R_4]
  ring

/-
## The Prize Problem

Erdős offered $100 for proof, $1000 for disproof.
-/

/-- The main open question -/
def erdos1029OpenProblem : Prop := erdos1029Conjecture

#check R
#check erdos1029Conjecture
#check spencer_lower_bound
#check erdos_szekeres_upper
