/-
Erdős Problem #492: Uniform Distribution Relative to a Fixed Sequence

Source: https://erdosproblems.com/492
Status: DISPROVED (Schmidt, 1969)

Statement:
Let A = {a₁ < a₂ < ...} ⊆ ℕ be infinite such that aᵢ₊₁/aᵢ → 1. For any x ≥ a₁ let
    f(x) = (x - aᵢ)/(aᵢ₊₁ - aᵢ) ∈ [0,1)
where x ∈ [aᵢ, aᵢ₊₁). Is it true that, for almost all α, the sequence f(αn) is
uniformly distributed in [0,1)?

Known Results:
- Le Veque (1953): Proved special cases
- Davenport-LeVeque (1963): True when aₙ - aₙ₋₁ is monotonic
- Davenport-Erdős (1963): True when aₙ >> n^{1/2+ε}
- Schmidt (1969): General conjecture is FALSE

Note: When A = ℕ, f(x) = {x} is the usual fractional part, and Weyl's theorem
applies: {αn} is u.d. for irrational α.

References:
- Le Veque [LV53]: "On uniform distribution modulo a subdivision", Pacific J. Math.
- Davenport-LeVeque [DaLe63]: "Uniform distribution relative to a fixed sequence"
- Davenport-Erdős [DaEr63]: "A theorem on uniform distribution"
- Schmidt [Sc69]: "Disproof of some conjectures on Diophantine approximations"
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Instances.Real

open Set Real MeasureTheory

namespace Erdos492

/-
## Part I: Increasing Sequences Approaching Unity Ratio
-/

/--
**Increasing Sequence with Unity Ratio:**
A sequence A = {a₁ < a₂ < ...} ⊆ ℕ where consecutive ratios approach 1.
-/
structure UnityRatioSeq where
  seq : ℕ → ℕ
  strictMono : StrictMono seq
  ratioLimit : Filter.Tendsto (fun n => (seq (n + 1) : ℝ) / seq n) Filter.atTop (nhds 1)

/--
**Standard Example: The Natural Numbers.**
When A = ℕ, we have aₙ = n and aₙ₊₁/aₙ = (n+1)/n → 1.
-/
def naturalsSeq : UnityRatioSeq := {
  seq := fun n => n + 1  -- 1-indexed: a₁ = 1, a₂ = 2, ...
  strictMono := fun a b hab => Nat.add_lt_add_right hab 1
  ratioLimit := by
    -- (n+2)/(n+1) → 1 as n → ∞
    sorry
}

/--
**Powers Example.**
For any r > 1, the sequence aₙ = ⌊rⁿ⌋ has aₙ₊₁/aₙ → r, not 1.
So integer powers don't satisfy the unity ratio condition.
-/
theorem powers_not_unity (r : ℝ) (hr : r > 1) :
    ¬∃ (A : UnityRatioSeq), ∀ n, A.seq n = Nat.floor (r ^ n) := by
  sorry

/-
## Part II: The Generalized Fractional Part Function
-/

/--
**Interval Index:**
Given x ≥ a₁, find the unique i such that x ∈ [aᵢ, aᵢ₊₁).
-/
noncomputable def intervalIndex (A : UnityRatioSeq) (x : ℝ) : ℕ :=
  -- The unique i such that a_i ≤ x < a_{i+1}
  0  -- placeholder

/--
**Generalized Fractional Part:**
f(x) = (x - aᵢ)/(aᵢ₊₁ - aᵢ) where x ∈ [aᵢ, aᵢ₊₁).
This maps [aᵢ, aᵢ₊₁) linearly onto [0, 1).
-/
noncomputable def generalizedFrac (A : UnityRatioSeq) (x : ℝ) : ℝ :=
  let i := intervalIndex A x
  let aᵢ := (A.seq i : ℝ)
  let aᵢ₊₁ := (A.seq (i + 1) : ℝ)
  (x - aᵢ) / (aᵢ₊₁ - aᵢ)

/--
**Standard Case:**
When A = ℕ, f(x) = {x} is the usual fractional part.
-/
theorem naturals_frac_eq (x : ℝ) (hx : x ≥ 1) :
    generalizedFrac naturalsSeq x = Int.frac x := by
  sorry

/--
**Range of f:**
The generalized fractional part always lies in [0, 1).
-/
theorem generalizedFrac_mem_Ico (A : UnityRatioSeq) (x : ℝ) (hx : x ≥ A.seq 0) :
    generalizedFrac A x ∈ Ico 0 1 := by
  sorry

/-
## Part III: Uniform Distribution
-/

/--
**Uniform Distribution in [0,1):**
A sequence (xₙ) in [0,1) is uniformly distributed if for all 0 ≤ a < b ≤ 1,
    lim_{N→∞} (1/N) |{n ≤ N : xₙ ∈ [a,b)}| = b - a.
-/
def isUniformlyDistributed (x : ℕ → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    Filter.Tendsto
      (fun N => (Finset.filter (fun n => x n ∈ Ico a b) (Finset.range N)).card / N)
      Filter.atTop (nhds (b - a))

/--
**Weyl's Equidistribution Theorem:**
For irrational α, the sequence ({αn})_{n≥1} is u.d. mod 1.
-/
axiom weyl_equidistribution :
    ∀ α : ℝ, Irrational α → isUniformlyDistributed (fun n => Int.frac (α * n))

/--
**Erdős-Davenport Sequence:**
For A and α, the sequence f(α·n) for n = 1, 2, 3, ...
-/
noncomputable def erdosDavenportSeq (A : UnityRatioSeq) (α : ℝ) : ℕ → ℝ :=
  fun n => generalizedFrac A (α * n)

/-
## Part IV: The Conjecture and Its Fate
-/

/--
**Erdős's Conjecture (FALSE):**
For almost all α, the sequence f(αn) is uniformly distributed.
-/
def erdosConjecture (A : UnityRatioSeq) : Prop :=
  ∃ S : Set ℝ, volume.ae (· ∈ S) ∧ ∀ α ∈ S, isUniformlyDistributed (erdosDavenportSeq A α)

/--
**Schmidt's Counterexample (1969):**
There exists a sequence A satisfying the conditions for which the conjecture fails.
-/
axiom schmidt_counterexample :
    ∃ A : UnityRatioSeq, ¬erdosConjecture A

/--
**The Main Result:**
Erdős Problem #492 is DISPROVED.
-/
theorem erdos_492_disproved :
    ∃ A : UnityRatioSeq, ¬erdosConjecture A :=
  schmidt_counterexample

/-
## Part V: Positive Cases
-/

/--
**Monotonic Gap Condition:**
The sequence aₙ - aₙ₋₁ is (eventually) monotonic.
-/
def hasMonotonicGaps (A : UnityRatioSeq) : Prop :=
  ∃ N : ℕ, ∀ n ≥ N, A.seq (n + 1) - A.seq n ≤ A.seq (n + 2) - A.seq (n + 1)

/--
**Davenport-LeVeque Theorem (1963):**
If aₙ - aₙ₋₁ is monotonic, then the conjecture holds.
-/
axiom davenport_leveque :
    ∀ A : UnityRatioSeq, hasMonotonicGaps A → erdosConjecture A

/--
**Polynomial Growth Condition:**
The sequence satisfies aₙ >> n^{1/2+ε} for some ε > 0.
-/
def hasPolynomialGrowth (A : UnityRatioSeq) : Prop :=
  ∃ ε : ℝ, ε > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (A.seq n : ℝ) ≥ C * (n : ℝ) ^ (1/2 + ε)

/--
**Davenport-Erdős Theorem (1963):**
If aₙ >> n^{1/2+ε}, then the conjecture holds.
-/
axiom davenport_erdos :
    ∀ A : UnityRatioSeq, hasPolynomialGrowth A → erdosConjecture A

/--
**Natural Numbers Case:**
For A = ℕ, the conjecture holds (this is Weyl's theorem).
-/
theorem naturals_case : erdosConjecture naturalsSeq := by
  -- ℕ has monotonic gaps (all equal to 1)
  have hMono : hasMonotonicGaps naturalsSeq := by
    use 0
    intro n _
    simp [naturalsSeq]
  exact davenport_leveque naturalsSeq hMono

/-
## Part VI: The Structure of Counterexamples
-/

/--
**Schmidt's Construction Idea:**
Schmidt constructed sequences with carefully controlled oscillations in gaps
that destroy uniform distribution for most α.
-/
def schmidtTypeSeq : Prop :=
  ∃ A : UnityRatioSeq,
    -- Has rapid oscillations in gap sizes
    (∃ (f : ℕ → Bool), ∀ n, (f n = true ↔
      A.seq (n + 2) - A.seq (n + 1) < A.seq (n + 1) - A.seq n)) ∧
    -- But still satisfies unity ratio
    A.ratioLimit ≠ A.ratioLimit → False  -- tautology placeholder

/--
**The Gap Ratio:**
Define gₙ = aₙ₊₁ - aₙ, the n-th gap.
-/
noncomputable def gap (A : UnityRatioSeq) (n : ℕ) : ℕ :=
  A.seq (n + 1) - A.seq n

/--
**Gap Growth Condition:**
For the counterexample, gaps oscillate wildly while maintaining ratio → 1.
-/
def hasOscillatingGaps (A : UnityRatioSeq) : Prop :=
  ¬∃ N : ℕ, ∀ n ≥ N, gap A n ≤ gap A (n + 1)

/--
**Key Insight:**
Monotonic gaps ⟹ uniform distribution, but oscillating gaps can break it.
-/
theorem monotonic_vs_oscillating :
    (∀ A : UnityRatioSeq, hasMonotonicGaps A → erdosConjecture A) ∧
    (∃ A : UnityRatioSeq, hasOscillatingGaps A ∧ ¬erdosConjecture A) := by
  constructor
  · exact davenport_leveque
  · obtain ⟨A, hA⟩ := schmidt_counterexample
    use A
    constructor
    · -- Schmidt's counterexample has oscillating gaps
      sorry
    · exact hA

/-
## Part VII: Measure-Theoretic Formulation
-/

/--
**Almost All α:**
The set of α for which f(αn) is u.d. has full measure.
-/
def almostAllUniform (A : UnityRatioSeq) : Prop :=
  volume {α : ℝ | ¬isUniformlyDistributed (erdosDavenportSeq A α)} = 0

/--
**Equivalent Formulation:**
erdosConjecture is equivalent to almostAllUniform.
-/
theorem conjecture_iff_ae (A : UnityRatioSeq) :
    erdosConjecture A ↔ almostAllUniform A := by
  sorry

/--
**Schmidt's Measure Result:**
In the counterexample, the non-u.d. set has positive measure.
-/
axiom schmidt_positive_measure :
    ∃ A : UnityRatioSeq, volume {α : ℝ | ¬isUniformlyDistributed (erdosDavenportSeq A α)} > 0

/-
## Part VIII: Summary
-/

/--
**Erdős Problem #492 Summary:**
The conjecture that f(αn) is u.d. for a.e. α is FALSE in general,
but TRUE under additional conditions (monotonic gaps, polynomial growth).
-/
theorem erdos_492_summary :
    (-- Schmidt's counterexample exists
     ∃ A : UnityRatioSeq, ¬erdosConjecture A) ∧
    (-- Monotonic gaps imply uniform distribution
     ∀ A : UnityRatioSeq, hasMonotonicGaps A → erdosConjecture A) ∧
    (-- Polynomial growth implies uniform distribution
     ∀ A : UnityRatioSeq, hasPolynomialGrowth A → erdosConjecture A) ∧
    (-- Natural numbers work (Weyl)
     erdosConjecture naturalsSeq) := by
  exact ⟨schmidt_counterexample, davenport_leveque, davenport_erdos, naturals_case⟩

/--
**Main Theorem:**
Erdős Problem #492 is DISPROVED but has significant positive cases.
-/
theorem erdos_492 : ∃ A : UnityRatioSeq, ¬erdosConjecture A :=
  schmidt_counterexample

/--
**Open Questions:**
What conditions on A are necessary and sufficient for the conjecture?
-/
def openQuestion : Prop :=
  ∃ (P : UnityRatioSeq → Prop),
    (∀ A, P A → erdosConjecture A) ∧
    (∀ A, ¬P A → ¬erdosConjecture A)

end Erdos492
