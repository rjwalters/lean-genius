/-
  Aristotle targets for Erdős Problem #1000 OQ-01: Explicit Haight-type Sequences
  Routine supporting lemmas for automated proof search.
  See Erdos1000OQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open question (characterization of Haight-type sequences)
  - Routine factorial arithmetic: Σ (j+1)! < 2·k! for k ≥ 2
  - Clean theorem statements with no definition sorries
  - No axioms

  Sorries targeted:
  - sum_factorials_lt: (range k).sum (fun j => (j+1)!) < 2 * k! for k ≥ 2
    Strategy: induction on k ≥ 2; base case norm_num; inductive step uses
    Finset.sum_range_succ + Nat.factorial_succ + linarith.
  - sum_factorials_pos: 0 < (range k).sum (fun j => (j+1)!) for k ≥ 1
    Strategy: Finset.sum_pos + Nat.factorial_pos.
-/
import Mathlib

open Finset Nat

namespace Erdos1000OQ01Aristotle

/-- Routine: Σ_{j=0}^{k-1} (j+1)! < 2 · k! for k ≥ 2.
    The k! term dominates: all prior terms sum to less than k!.
    Strategy: induction; base k=2 gives 1!+2!=3 < 2·2!=4 by norm_num;
    inductive step: sum + (k+1)! < 2·k! + (k+1)·k! = (k+3)·k! < 2·(k+1)·k! = 2·(k+1)!
    for k ≥ 2 since k+3 < 2k+2 iff k > 1. -/
theorem sum_factorials_lt (k : ℕ) (hk : 2 ≤ k) :
    (range k).sum (fun j => (j + 1).factorial) < 2 * k.factorial := by
  sorry

/-- Routine: The factorial sum is positive for k ≥ 1.
    Each (j+1)! ≥ 1 and there is at least one term in the range.
    Strategy: Finset.sum_pos with Nat.factorial_pos. -/
theorem sum_factorials_pos (k : ℕ) (hk : 0 < k) :
    0 < (range k).sum (fun j => (j + 1).factorial) := by
  sorry

/-- Routine: (range k).sum (fun j => (j+1)!) ≥ k for k ≥ 1.
    Each term (j+1)! ≥ 1, and there are k terms.
    Strategy: induction or Finset.sum_le_sum with le_factorial. -/
theorem sum_factorials_ge_card (k : ℕ) :
    k ≤ (range k).sum (fun j => (j + 1).factorial) := by
  sorry

end Erdos1000OQ01Aristotle
