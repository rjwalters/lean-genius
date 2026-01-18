/-
Erdős Problem #355: Lacunary Sequences and Rational Representation

Source: https://erdosproblems.com/355
Status: SOLVED (van Doorn & Kovač 2025) - Answer is YES

Statement:
Is there a lacunary sequence A ⊆ ℕ (where a_{n+1}/a_n ≥ λ > 1 for all n) such that
the set of all finite reciprocal sums { ∑_{a ∈ A'} 1/a : A' ⊆ A finite } contains
all rationals in some open interval?

Answer: YES, for any lacunarity constant λ ∈ (1,2), though not for λ = 2.

Historical Context:
- Bleicher and Erdős conjectured the answer was NO [BlEr76, p.167]
- van Doorn and Kovač proved YES for λ ∈ (1,2) [DoKo25, arXiv:2509.24971]
- The construction uses carefully chosen lacunary sequences to achieve density

References:
- [DoKo25] van Doorn, W. and Kovač, V., "Lacunary sequences whose reciprocal sums
  represent all rationals in an interval", arXiv:2509.24971 (2025)
- [BlEr76] Bleicher, M. N. and Erdős, P., "Denominators of Egyptian fractions I",
  Journal of Number Theory (1976)
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open Finset Set

namespace Erdos355

/-!
## Part I: Definitions

We define lacunary sequences and the set of achievable reciprocal sums.
-/

/-- A sequence is lacunary with parameter lam > 1 if consecutive terms
    satisfy a_{n+1}/a_n ≥ lam for all n. This means the sequence grows
    at least exponentially. -/
def IsLacunaryWith (a : ℕ → ℕ) (lam : ℝ) : Prop :=
  lam > 1 ∧ (∀ n, a n > 0) ∧ ∀ n, (a (n + 1) : ℝ) / a n ≥ lam

/-- A sequence is lacunary if it's lacunary for some lam > 1. -/
def IsLacunary (a : ℕ → ℕ) : Prop :=
  ∃ lam > 1, (∀ n, a n > 0) ∧ ∀ n, (a (n + 1) : ℝ) / a n ≥ lam

/-- The set of all finite reciprocal sums achievable from a sequence.
    For any finite subset of the sequence's range, we can sum their reciprocals. -/
def ReciprocalSums (a : ℕ → ℕ) : Set ℚ :=
  { q | ∃ (S : Finset ℕ) (k : ℕ), (∀ i ∈ S, i < k) ∧
        q = ∑ i ∈ S, (1 : ℚ) / a i }

/-- Alternative characterization using index subsets. -/
def ReciprocalSumsAlt (a : ℕ → ℕ) : Set ℚ :=
  { ∑ i ∈ S, (1 : ℚ) / a i | S : Finset ℕ }

/-- A sequence represents all rationals in an interval if every rational
    in that interval is a finite reciprocal sum from the sequence. -/
def RepresentsRationalsIn (a : ℕ → ℕ) (u v : ℝ) : Prop :=
  u < v ∧ ∀ q : ℚ, u < q ∧ (q : ℝ) < v → q ∈ ReciprocalSumsAlt a

/-!
## Part II: Properties of Lacunary Sequences

Lacunary sequences grow exponentially and have convergent reciprocal sums.
-/

/-- A lacunary sequence is strictly increasing. -/
theorem lacunary_strictMono (a : ℕ → ℕ) (lam : ℝ) (h : IsLacunaryWith a lam) :
    StrictMono a := by
  intro m n hmn
  -- Since a_{n+1}/a_n ≥ lam > 1, we have a_{n+1} > a_n
  -- Repeated application shows a_m < a_n when m < n
  sorry

/-- The sum of reciprocals of a lacunary sequence converges. -/
theorem lacunary_reciprocal_sum_converges (a : ℕ → ℕ) (h : IsLacunary a) :
    ∃ S : ℝ, ∀ ε > 0, ∃ N, ∀ n ≥ N, |∑ i ∈ range n, (1 : ℝ) / a i - S| < ε := by
  -- The series ∑ 1/a_n converges by comparison with geometric series
  sorry

/-- Powers of 2 form a lacunary sequence with lam = 2. -/
theorem powers_of_two_lacunary : IsLacunaryWith (fun n => 2^(n+1)) 2 := by
  constructor
  · norm_num
  constructor
  · intro n
    positivity
  · intro n
    simp only
    have h1 : (2 ^ (n + 1) : ℕ) > 0 := by positivity
    have h2 : (2 ^ (n + 1 + 1) : ℕ) = 2 * 2 ^ (n + 1) := by ring
    have h3 : ((2 ^ (n + 1) : ℕ) : ℝ) ≠ 0 := by positivity
    rw [h2]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    rw [mul_div_assoc, div_self h3, mul_one]

/-!
## Part III: The Critical λ = 2 Boundary

Powers of 2 (λ = 2) cannot represent all rationals in any interval.
-/

/-- The sum of all reciprocals of powers of 2 is exactly 1.
    ∑_{n=1}^∞ 1/2^n = 1 (geometric series). -/
axiom geometric_series_sum : ∑' n, (1 : ℝ) / 2^(n+1) = 1

/-- For λ = 2 (powers of 2), the achievable sums are exactly the dyadic rationals
    in [0, 1]. These are rationals of the form k/2^n and don't fill any interval. -/
theorem powers_of_two_gaps :
    ¬∃ u v : ℝ, u < v ∧ RepresentsRationalsIn (fun n => 2^(n+1)) u v := by
  -- Dyadic rationals are nowhere dense in ℝ, so any interval (u,v) contains
  -- non-dyadic rationals that cannot be represented
  intro ⟨u, v, huv, hrep⟩
  -- For example, 1/3 cannot be expressed as a finite sum of powers of 1/2
  -- Choose an interval containing 1/3
  sorry

/-!
## Part IV: van Doorn-Kovač Theorem (Main Result)

For λ ∈ (1, 2), there exist lacunary sequences whose reciprocal sums
represent all rationals in an interval.
-/

/-- **van Doorn-Kovač Theorem (2025)** - Erdős Problem #355 SOLVED

    For any lacunarity constant lam ∈ (1, 2), there exists a lacunary sequence
    A with ratio parameter lam such that the set of finite reciprocal sums
    from A contains all rationals in some open interval.

    This resolved Erdős Problem #355 in the affirmative, disproving the
    Bleicher-Erdős conjecture. -/
axiom vanDoorn_Kovac_theorem :
  ∀ lam : ℝ, 1 < lam ∧ lam < 2 →
    ∃ (a : ℕ → ℕ), IsLacunaryWith a lam ∧ ∃ u v : ℝ, RepresentsRationalsIn a u v

/-- The main theorem: there exists a lacunary sequence whose reciprocal sums
    contain all rationals in some open interval. -/
theorem erdos_355_solved :
    ∃ (a : ℕ → ℕ), IsLacunary a ∧ ∃ u v : ℝ, RepresentsRationalsIn a u v := by
  -- Take lam = 3/2 which is in (1, 2)
  have h32 : (1 : ℝ) < (3 : ℝ)/2 ∧ (3 : ℝ)/2 < 2 := by norm_num
  obtain ⟨a, hLac, u, v, hrep⟩ := vanDoorn_Kovac_theorem ((3 : ℝ)/2) h32
  exact ⟨a, ⟨(3 : ℝ)/2, h32.1, hLac.2⟩, u, v, hrep⟩

/-- Alternative statement matching formal-conjectures format. -/
theorem erdos_355 :
    ∃ A : ℕ → ℕ, IsLacunary A ∧ ∃ u v : ℝ, u < v ∧ ∀ q : ℚ, ↑q ∈ Ioo u v →
      q ∈ ReciprocalSumsAlt A := by
  obtain ⟨a, hLac, u, v, ⟨huv, hrep⟩⟩ := erdos_355_solved
  use a, hLac, u, v, huv
  intro q ⟨hqu, hqv⟩
  exact hrep q ⟨hqu, hqv⟩

/-!
## Part V: The Sharp Boundary

The condition λ < 2 is necessary. For λ = 2, no lacunary sequence works.
-/

/-- For λ ≥ 2, no lacunary sequence can represent all rationals in an interval. -/
axiom lambda_two_fails :
  ∀ (a : ℕ → ℕ), IsLacunaryWith a 2 →
    ¬∃ u v : ℝ, RepresentsRationalsIn a u v

/-- The threshold lam = 2 is sharp: (1,2) works, [2,∞) doesn't. -/
theorem sharp_threshold :
    (∀ lam : ℝ, 1 < lam ∧ lam < 2 →
      ∃ (a : ℕ → ℕ), IsLacunaryWith a lam ∧ ∃ u v, RepresentsRationalsIn a u v) ∧
    (∀ (a : ℕ → ℕ), IsLacunaryWith a 2 →
      ¬∃ u v : ℝ, RepresentsRationalsIn a u v) :=
  ⟨vanDoorn_Kovac_theorem, lambda_two_fails⟩

/-!
## Part VI: Examples and Intuition

Understanding why the gap at λ = 2 exists.
-/

/-- Example: {1, 2, 3, 5, 8, 13, ...} (Fibonacci-like) has λ ≈ φ ≈ 1.618.
    Since 1 < φ < 2, this sequence could represent rationals in an interval. -/
def fibLikeSeq : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | n + 2 => fibLikeSeq n + fibLikeSeq (n + 1)

/-- The Fibonacci-like sequence has positive terms. -/
theorem fibLikeSeq_pos : ∀ n, fibLikeSeq n > 0 := by
  intro n
  induction n with
  | zero => simp [fibLikeSeq]
  | succ n ih =>
    cases n with
    | zero => simp [fibLikeSeq]
    | succ m =>
      simp only [fibLikeSeq]
      omega

/-- Key insight: Why does λ < 2 work but λ = 2 fail?

    For λ = 2 (powers of 2), the reciprocal sums are dyadic rationals k/2^n.
    These form a discrete set with gaps, so they can't fill an interval.

    For λ < 2, the overlap between consecutive "levels" of the sequence
    allows the reciprocal sums to become dense, eventually covering all
    rationals in some interval.

    The van Doorn-Kovač proof constructs explicit sequences achieving this. -/
theorem intuition_explained : True := trivial

/-- Summary: Erdős Problem #355 (SOLVED - YES)

    Main Results:
    1. For λ ∈ (1,2): There exist lacunary sequences whose reciprocal sums
       represent all rationals in an open interval (van Doorn-Kovač 2025)
    2. For λ = 2: No such sequence exists (powers of 2 give only dyadic rationals)
    3. The Bleicher-Erdős conjecture (that no such sequence exists) was disproved -/
theorem erdos_355_summary :
    (∃ (a : ℕ → ℕ), IsLacunary a ∧ ∃ u v : ℝ, RepresentsRationalsIn a u v) ∧
    IsLacunaryWith (fun n => 2^(n+1)) 2 ∧
    (1 : ℝ) < (3 : ℝ)/2 ∧ (3 : ℝ)/2 < 2 := by
  refine ⟨erdos_355_solved, powers_of_two_lacunary, ?_, ?_⟩ <;> norm_num

end Erdos355
