import Mathlib

/-
# Tractatus: exact independence boundary for Horn models — Aristotle problem file

Companion to https://github.com/rjwalters/tractatus and the Horn-model
development in lean-genius (`TractatusOntologyHorn.lean`). The source
proves the FAILURE direction: a single nontrivial Horn clause
`w a → w b` (with `a ≠ b`) breaks the independence of atomic facts
(TLP 2.061). This file states the exact boundary as an iff.

A Horn-constrained world for clause list `cs` is a world satisfying
`w c.1 → w c.2` for every clause `c ∈ cs`. Realizability (every
truth-value assignment is realized by some constrained world) holds
IFF every clause is trivial (`c.1 = c.2`).

Target: `horn_realizable_iff` (the only `sorry`). Hints: right-to-left,
trivial clauses impose no constraint, so the assignment itself is a
Horn world. Left-to-right, contrapose: for a clause `(a, b)` with
`a ≠ b`, the assignment `fun s => s = a` has no realizer (its realizer
would satisfy `w a`, hence `w b`, hence `b = a`).
-/

namespace TractatusHornAristotle

/-- Horn-constrained worlds: every clause `(a, b) ∈ cs` imposes
    `w a → w b`. -/
def HornWorld (S : Type) (cs : List (S × S)) :=
  { w : S → Prop // ∀ c ∈ cs, w c.1 → w c.2 }

/-
════════════════════════════════════════════════════════════════
TARGET
════════════════════════════════════════════════════════════════

Exact boundary of TLP 2.061 for Horn-clause constraints:
    realizability of every truth-value assignment holds iff every
    clause is trivial.
-/
theorem horn_realizable_iff {S : Type} (cs : List (S × S)) :
    (∀ assignment : S → Prop,
      ∃ w : HornWorld S cs, ∀ s, w.val s ↔ assignment s) ↔
    (∀ c ∈ cs, c.1 = c.2) := by
  constructor
  · intro h c hc
    obtain ⟨w, hw⟩ := h (fun s => s = c.1)
    have := w.2 c hc
    aesop
  · intro hcs assignment
    use ⟨assignment, by grind⟩
    aesop

end TractatusHornAristotle