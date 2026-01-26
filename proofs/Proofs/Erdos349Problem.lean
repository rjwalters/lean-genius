/-!
# Erdős Problem #349 — Completeness of Exponential Floor Sequences

For what values of t, α ∈ (0,∞) is the sequence ⌊tα^n⌋ complete?
(A set is complete if all sufficiently large integers are sums of
distinct elements from the set.)

Conjectured complete for all t > 0 and 1 < α < (1+√5)/2 (golden ratio).

The problem connects to the difficult question of whether ⌊(3/2)^n⌋
is odd infinitely often and even infinitely often.

Status: OPEN
Reference: https://erdosproblems.com/349
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Definition -/

/-- A set S ⊂ ℤ is additively complete if all sufficiently large
    integers are sums of distinct elements from S. -/
def IsAdditivelyComplete (S : Set ℤ) : Prop :=
  ∃ N : ℤ, ∀ m : ℤ, m ≥ N →
    ∃ T : Finset ℤ, (↑T : Set ℤ) ⊆ S ∧ T.sum id = m

/-- The exponential floor sequence: ⌊tα^n⌋ for n = 0, 1, 2, ... -/
def expFloorSeq (t α : ℝ) (n : ℕ) : ℤ := ⌊t * α ^ n⌋

/-- A pair (t,α) is "good" if the sequence ⌊tα^n⌋ is complete. -/
def IsGoodPair (t α : ℝ) : Prop :=
  IsAdditivelyComplete (Set.range (expFloorSeq t α))

/-! ## Main Question -/

/-- **Erdős Problem #349**: Characterize the pairs (t,α) with
    t > 0, α > 0 for which ⌊tα^n⌋ is a complete sequence. -/
axiom erdos_349_characterization :
  ∃ S : Set (ℝ × ℝ),
    ∀ t α : ℝ, t > 0 → α > 0 →
      (IsGoodPair t α ↔ (t, α) ∈ S)

/-! ## Golden Ratio Conjecture -/

/-- **Golden Ratio Conjecture**: The sequence ⌊tα^n⌋ is complete
    for all t > 0 and 1 < α < (1+√5)/2 ≈ 1.618. -/
axiom golden_ratio_conjecture :
  ∀ t α : ℝ, t > 0 → 1 < α → α < (1 + Real.sqrt 5) / 2 →
    IsGoodPair t α

/-! ## Known Results -/

/-- **Graham's Disjoint Segments**: For any k, there exists
    t_k ∈ (0,1) such that the set of α making ⌊t_k α^n⌋ complete
    consists of at least k disjoint intervals. -/
axiom graham_disjoint_segments :
  ∀ k : ℕ, ∃ t : ℝ, 0 < t ∧ t < 1 ∧
    ∃ intervals : Fin k → Set ℝ,
      (∀ i, ∃ a b : ℝ, a < b ∧ intervals i = Set.Ioo a b) ∧
      (∀ i j, i ≠ j → Disjoint (intervals i) (intervals j)) ∧
      (∀ i, ∀ α ∈ intervals i, IsGoodPair t α)

/-! ## Parity of ⌊(3/2)^n⌋ -/

/-- **Odd Infinitely Often?**: Is ⌊(3/2)^n⌋ odd for infinitely
    many n? This basic question remains open and is a fundamental
    obstacle to the main conjecture. -/
axiom floor_3_2_odd_infinitely :
  Set.Infinite {n : ℕ | Odd (⌊(3 / 2 : ℝ) ^ n⌋).toNat}

/-- **Even Infinitely Often?**: Is ⌊(3/2)^n⌋ even for infinitely
    many n? Also open. -/
axiom floor_3_2_even_infinitely :
  Set.Infinite {n : ℕ | Even (⌊(3 / 2 : ℝ) ^ n⌋).toNat}

/-! ## Observations -/

/-- **Waring-Type Connection**: Completeness of ⌊tα^n⌋ relates to
    representation problems in additive number theory, similar in
    spirit to Waring's problem for exponential bases. -/
axiom waring_connection : True

/-- **Fibonacci Threshold**: The golden ratio (1+√5)/2 is the
    growth rate of the Fibonacci sequence, which is known to be
    a complete sequence. The conjecture suggests completeness
    persists for slightly faster growth rates. -/
axiom fibonacci_threshold : True
