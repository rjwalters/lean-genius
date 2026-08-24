import Mathlib.Data.Finset.Max
import Mathlib.Data.Prod.Lex

/-!
# Lexicographic exchange descent for the B.3 outer selector

The q=9 Branch4 audit selects an obstructed row by minimizing its residual
candidate count and, among ties, maximizing its forced count.  This file
packages the finite descent endgame independently of the outer geometry.
-/

namespace Erdos85

variable {V : Type*}

/-- Lexicographic score which minimizes the candidate count and maximizes the
forced count. -/
def candidateForcedLexScore
    (candidateCount forcedCount : V → ℕ) (w : V) :
    ℕ ×ₗ OrderDual ℕ :=
  toLex (candidateCount w, OrderDual.toDual (forcedCount w))

@[simp] theorem candidateForcedLexScore_lt_iff
    (candidateCount forcedCount : V → ℕ) (z w : V) :
    candidateForcedLexScore candidateCount forcedCount z <
        candidateForcedLexScore candidateCount forcedCount w ↔
      candidateCount z < candidateCount w ∨
      candidateCount z = candidateCount w ∧ forcedCount w < forcedCount z := by
  simp [candidateForcedLexScore, Prod.Lex.toLex_lt_toLex]

/-- If every failed terminal either exposes a forbidden bad row or descends
strictly in `(candidate count, reverse forced count)`, then excluding bad rows
forces the terminal at some obstructed row.  `OrderDual` encodes the second
criterion as maximization. -/
theorem exists_terminal_of_lexicographic_exchange_descent
    [Fintype V] [DecidableEq V]
    (Obstructed Bad Terminal : V → Prop) [DecidablePred Obstructed]
    (candidateCount forcedCount : V → ℕ)
    (hobstructed : ∃ w, Obstructed w)
    (hnoBad : ∀ z, ¬Bad z)
    (hexchange : ∀ w, Obstructed w → ¬Terminal w →
      (∃ z, Bad z) ∨
      ∃ z, Obstructed z ∧
        candidateForcedLexScore candidateCount forcedCount z <
          candidateForcedLexScore candidateCount forcedCount w) :
    ∃ w, Obstructed w ∧ Terminal w := by
  classical
  let rows := Finset.univ.filter Obstructed
  have hrows : rows.Nonempty := by
    obtain ⟨w, hw⟩ := hobstructed
    exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩⟩
  obtain ⟨w, hwRows, hwMin⟩ := Finset.exists_min_image rows
    (candidateForcedLexScore candidateCount forcedCount) hrows
  have hwObstructed : Obstructed w := (Finset.mem_filter.mp hwRows).2
  refine ⟨w, hwObstructed, ?_⟩
  by_contra hwTerminal
  rcases hexchange w hwObstructed hwTerminal with hbad | ⟨z, hzObs, hzlt⟩
  · obtain ⟨z, hzBad⟩ := hbad
    exact hnoBad z hzBad
  · have hzRows : z ∈ rows :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzObs⟩
    exact (not_lt_of_ge (hwMin z hzRows)) hzlt

#print axioms exists_terminal_of_lexicographic_exchange_descent

end Erdos85
