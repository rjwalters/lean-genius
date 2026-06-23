/-
Pilot for the Harmonic `*StatementOnly.lean` Aristotle-submission format
(see Loom issue #22473, format from #22468, docs at research/SORRY-CLASSIFICATION.md
and #22466).

Extracted from `proofs/Proofs/SchroederBernsteinOQ03Aristotle.lean`
(companion file for `SchroederBernsteinOQ03.lean` — Myhill's Isomorphism
Theorem).

Statement: For every computable total function `g : ℕ → ℕ`, its
partial inverse `partialInverse g : ℕ →. ℕ` (defined via `Nat.rfind` on
`decide (g n = m)`) is partial recursive.

Formally:
    `partialInverse g m = Nat.rfind (fun n => decide (g n = m))`
    `Computable g → Partrec (partialInverse g)`

This is a routine but non-trivial result in classical computability theory:
the unbounded search operator preserves partial recursiveness when applied
to a computable decidable predicate. It is Theorem II of Rogers (1967),
Chapter 5, and underpins the hard direction of Myhill's 1955 Isomorphism
Theorem (the computable refinement of the 1898 Schroeder–Bernstein theorem).

Citations:
- Myhill, J. (1955). "Creative sets." Z. Math. Logik Grundlag. Math. 1, 97–108.
- Rogers, H. (1967). Theory of Recursive Functions and Effective Computability.
  MIT Press. Chapter 5 (recursive functions, μ-operator).
- Soare, R. (2016). Turing Computability. Springer. Chapter 3.

Past Aristotle history for this problem: no prior submission for
`schroederbernsteinoq03`. This pilot establishes the first baseline.

Answer: `Partrec (partialInverse g)`.
-/

import Mathlib

set_option maxHeartbeats 0
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option pp.fullNames true
set_option pp.structureInstances true
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true
set_option linter.all false

noncomputable section

namespace SchroederBernsteinOQ03Statement

open Function Computable

/-- Partial inverse of `g : ℕ → ℕ` via unbounded search:
    `partialInverse g m` returns the least `n` with `g n = m`,
    and is undefined if no such `n` exists. -/
def partialInverse (g : ℕ → ℕ) : ℕ →. ℕ :=
  fun m => (Nat.rfind fun n => decide (g n = m))

/--
The partial inverse of a computable total function `g : ℕ → ℕ` is
partial recursive.

This is the foundational lemma for the hard direction of Myhill's
Isomorphism Theorem (1955): given two computable injections, we want
to construct a computable bijection by alternating between their
partial inverses (a back-and-forth construction). For that to be
computable at all, each partial inverse must itself be partial
recursive — which is exactly this statement.

The proof is routine: `Nat.rfind` applied to a computable decidable
predicate yields a `Partrec` partial function. The key Mathlib lemmas
are `Partrec.rfind` and the fact that `decide ∘ (g · = m)` is
computable when `g` is computable.

Hidden gotcha (why Aristotle is likely to struggle): the search
predicate must be packaged as a `Nat → Bool` computable function of
both `m` and `n`, not just `n`. This requires `Computable₂` rather
than `Computable`, and the right Mathlib glue lemma is
`Primrec.nat_rfind` / `Partrec.rfind` applied to a `Computable₂`
predicate — a step many tactic searches miss.
-/
theorem partialInverse_partrec {g : ℕ → ℕ} (hg : Computable g) :
    Partrec (partialInverse g) := by
  sorry

-- Proof attempt: a sketched chain of the expected Mathlib glue. Aristotle
-- is free to ignore this; it exists only to seed the MCTS prior (Rivin's
-- pattern from `Polya-Szego`/`StatementOnly_*.lean`).
--
-- The intended structure is:
--   1. Show the search predicate `fun mn : ℕ × ℕ => decide (g mn.2 = mn.1)`
--      is `Computable` by combining `hg` with `Computable.decide` and
--      `Computable.eq` (or the corresponding `Primrec` variants).
--   2. Lift to `Computable₂` so that for each fixed `m`, the family
--      `fun n => decide (g n = m)` is computable uniformly in `m`.
--   3. Apply `Partrec.rfind` (Mathlib's wrapper around `Nat.rfind`):
--        Partrec.rfind : Computable₂ p → Partrec (fun m => Nat.rfind (p m ·))
--      to conclude `Partrec (partialInverse g)`.
--
-- Tactic sketch:
--   refine Partrec.rfind ?_
--   exact (Primrec.eq.comp (hg.comp Computable.snd) Computable.fst).to₂.to_comp.to_decide
--
-- (Names approximated — the real Mathlib API uses
--  `Primrec₂.comp`, `Computable.decide`, and `Partrec.rfind`.)

end SchroederBernsteinOQ03Statement
