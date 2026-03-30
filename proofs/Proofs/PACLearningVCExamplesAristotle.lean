/-
  Aristotle targets for VC Dimension Examples
  Routine supporting lemmas for automated proof search.
  See PACLearningVCExamples.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known results (case analysis, convexity arguments)
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace VCDimension

open Finset BigOperators

variable {α : Type*} [DecidableEq α] [Fintype α]

-- Duplicated definitions for self-containedness
def traceOn (H : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  H.image (· ∩ S)

def Shatters (H : Finset (Finset α)) (S : Finset α) : Prop :=
  S.powerset ⊆ traceOn H S

def interval (n : ℕ) (a b : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a ≤ i.val ∧ i.val < b)

def intervalClass (n : ℕ) : Finset (Finset (Fin n)) :=
  ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).image (fun p => interval n p.1 p.2)

/-- Interval class shatters {a, b} when a.val < b.val.
    Routine case analysis: construct 4 intervals giving traces ∅, {a}, {b}, {a,b}. -/
theorem interval_shatters_pair {n : ℕ} (a b : Fin n) (hab : a.val < b.val) :
    Shatters (intervalClass n) {a, b} := by
  sorry

/-- No 3-element subset of Fin n is shattered by intervals.
    Convexity argument: for sorted p < q < r, the trace {p, r} is impossible. -/
theorem interval_not_shatters_triple {n : ℕ} (S : Finset (Fin n))
    (hS : S.card = 3) : ¬Shatters (intervalClass n) S := by
  sorry

end VCDimension
