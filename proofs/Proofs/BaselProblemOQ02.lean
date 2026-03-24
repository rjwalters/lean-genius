/-
Open Question: Are all odd zeta values ζ(2k+1) transcendental?

**Problem Statement (OPEN)**

Building on the Basel Problem (∑ 1/n² = π²/6), this formalizes the
open question about the arithmetic nature of odd zeta values.

**Known Results:**
- ζ(2k) = rational × π^(2k), hence transcendental (Euler + Lindemann 1882)
- ζ(3) is irrational (Apéry, 1978)
- Infinitely many ζ(2k+1) are irrational (Rivoal, 2000)
- At least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational (Zudilin, 2001)

**Open:** Is ζ(3) transcendental? Is any specific ζ(2k+1) transcendental?

**Status**: OPEN

Source: Extension of the Basel Problem formalization
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

open BigOperators Filter Topology Real

namespace BaselProblemOQ02

-- ## Part 1: Zeta Values at Natural Numbers

/-- The Riemann zeta function at natural number s:
    ζ(s) = ∑_{n=1}^∞ 1/n^s (as a tsum over ℕ, with the n=0 term vanishing). -/
noncomputable def zetaValue (s : ℕ) : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ s

-- ## Part 2: Known Even Zeta Values

/-- ζ(2) = π²/6 — the Basel Problem (Euler 1734). -/
theorem zetaValue_two : zetaValue 2 = π ^ 2 / 6 := by
  unfold zetaValue; exact hasSum_zeta_two.tsum_eq

/-- ζ(4) = π⁴/90 (Euler). -/
theorem zetaValue_four : zetaValue 4 = π ^ 4 / 90 := by
  unfold zetaValue; exact hasSum_zeta_four.tsum_eq

-- ## Part 3: Deep Axioms (Results Not Yet in Mathlib)

/-- **Lindemann's Theorem (1882)**: π is transcendental over ℚ.
    This is the key ingredient for showing even zeta values are transcendental.
    Not yet in Mathlib v4.26.0. -/
axiom pi_transcendental : Transcendental ℚ (Real.pi : ℝ)

/-- **Apéry's Theorem (1978)**: ζ(3) is irrational.
    The first (and still only individually named) odd zeta value
    proved irrational. The proof uses rapidly converging series
    and is one of the most celebrated results in 20th century number theory. -/
axiom apery_theorem : Irrational (zetaValue 3)

-- ## Part 4: The Open Conjecture

/-- **Open Conjecture: Transcendence of Odd Zeta Values**

    All odd zeta values ζ(2k+1) for k ≥ 1 are transcendental.
    Not a single odd zeta value has been proved transcendental.
    Even the transcendence of ζ(3) alone is a major open problem. -/
def odd_zeta_transcendence_conjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → Transcendental ℚ (zetaValue (2 * k + 1))

/-- **Weaker Open Conjecture: Irrationality of all odd zeta values.**
    While we know infinitely many are irrational (Rivoal 2000),
    we cannot prove irrationality for any specific ζ(2k+1) beyond ζ(3). -/
def odd_zeta_irrationality_conjecture : Prop :=
  ∀ k : ℕ, 1 ≤ k → Irrational (zetaValue (2 * k + 1))

-- ## Part 5: Structural Relationships

/-- The transcendence conjecture implies the irrationality conjecture. -/
theorem transcendence_implies_irrationality :
    odd_zeta_transcendence_conjecture → odd_zeta_irrationality_conjecture := by
  intro h k hk
  exact Transcendental.irrational (h k hk)

/-- The conjecture specialized to ζ(3) implies Apéry's theorem. -/
theorem conjecture_implies_apery :
    odd_zeta_irrationality_conjecture → Irrational (zetaValue 3) := by
  intro h
  exact h 1 le_rfl

/-- Apéry's theorem is weaker than the full irrationality conjecture. -/
theorem apery_weaker_than_conjecture :
    odd_zeta_irrationality_conjecture →
    Irrational (zetaValue 3) ∧ Irrational (zetaValue 5) := by
  intro h
  exact ⟨h 1 le_rfl, h 2 (by omega)⟩

-- ## Part 6: Context — Even vs Odd Zeta Values

/-- The stark contrast between even and odd zeta values:
    - Even: ζ(2k) = rational × π^(2k), fully understood since Euler (1734)
    - Odd: ζ(2k+1) has no known closed form; arithmetic nature mostly unknown

    This definition captures the even case: ζ(2k) is a rational multiple of π^(2k). -/
def even_zeta_rational_multiple (k : ℕ) (_ : k ≠ 0) : Prop :=
  ∃ q : ℚ, q ≠ 0 ∧ zetaValue (2 * k) = q * π ^ (2 * k)

-- ## Part 7: Even Zeta Values Are Transcendental

/-- ζ(2) is transcendental over ℚ.
    Proof sketch: ζ(2) = π²/6. If ζ(2) were algebraic, then π² = 6·ζ(2)
    would be algebraic, hence π would be algebraic — contradicting Lindemann. -/
theorem zeta_two_transcendental : Transcendental ℚ (zetaValue 2) := by
  rw [zetaValue_two]
  intro ⟨p, hp, hpx⟩
  apply pi_transcendental
  -- π²/6 algebraic → π² algebraic → π algebraic
  -- Needs Mathlib: algebraic closure under field ops + algebraic_of_pow
  sorry

/-- ζ(4) is transcendental over ℚ.
    Proof sketch: ζ(4) = π⁴/90. Same argument as ζ(2) via Lindemann. -/
theorem zeta_four_transcendental : Transcendental ℚ (zetaValue 4) := by
  rw [zetaValue_four]
  intro ⟨p, hp, hpx⟩
  apply pi_transcendental
  sorry

-- ## Part 8: Deep Results on Odd Zeta Irrationality

/-- **Rivoal's Theorem (2000)**: Infinitely many odd zeta values are irrational.
    Proved using very-well-poised hypergeometric series and a linear independence
    criterion. The precise result: the ℚ-vector space spanned by
    1, ζ(3), ζ(5), ..., ζ(s) has dimension ≥ c · log s as s → ∞.
    Not yet in Mathlib. -/
axiom rivoal_theorem :
  {k : ℕ | 1 ≤ k ∧ Irrational (zetaValue (2 * k + 1))}.Infinite

/-- **Zudilin's Theorem (2001)**: At least one of ζ(5), ζ(7), ζ(9), ζ(11) is irrational.
    Refines Ball–Rivoal method with well-poised hypergeometric series.
    Not yet in Mathlib. -/
axiom zudilin_theorem :
  Irrational (zetaValue 5) ∨ Irrational (zetaValue 7) ∨
  Irrational (zetaValue 9) ∨ Irrational (zetaValue 11)

-- ## Part 9: The Irrationality Landscape

/-- The full irrationality conjecture implies Rivoal's theorem:
    if ALL odd zeta values are irrational, certainly infinitely many are. -/
theorem conjecture_implies_rivoal :
    odd_zeta_irrationality_conjecture →
    {k : ℕ | 1 ≤ k ∧ Irrational (zetaValue (2 * k + 1))}.Infinite := by
  intro h
  apply Set.infinite_of_injective_forall_mem (f := fun n => n + 1)
    (fun a b hab => by omega)
  intro n
  exact ⟨by omega, h (n + 1) (by omega)⟩

/-- The full irrationality conjecture implies Zudilin's theorem. -/
theorem conjecture_implies_zudilin :
    odd_zeta_irrationality_conjecture →
    Irrational (zetaValue 5) ∨ Irrational (zetaValue 7) ∨
    Irrational (zetaValue 9) ∨ Irrational (zetaValue 11) := by
  intro h
  exact Or.inl (h 2 (by omega))

/-- The hierarchy of known results:
    Transcendence conjecture ⟹ Irrationality conjecture ⟹ Rivoal + Zudilin + Apéry.
    This gives a concrete summary: knowing the conjecture recovers all known results. -/
theorem conjecture_implies_all_known :
    odd_zeta_transcendence_conjecture →
    (Irrational (zetaValue 3)) ∧
    ({k : ℕ | 1 ≤ k ∧ Irrational (zetaValue (2 * k + 1))}.Infinite) ∧
    (Irrational (zetaValue 5) ∨ Irrational (zetaValue 7) ∨
     Irrational (zetaValue 9) ∨ Irrational (zetaValue 11)) := by
  intro h
  have hirr := transcendence_implies_irrationality h
  exact ⟨conjecture_implies_apery hirr,
         conjecture_implies_rivoal hirr,
         conjecture_implies_zudilin hirr⟩

-- ## Part 10: Summary

/-- Problem status: OPEN for the transcendence conjecture. -/
def problem_status : String := "OPEN (no odd zeta value known to be transcendental)"

end BaselProblemOQ02
