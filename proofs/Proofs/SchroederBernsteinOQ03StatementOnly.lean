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
  -- The search predicate `fun (m n : ℕ) => decide (g n = m)` is computable:
  -- combine `g ∘ snd` and `fst` through Mathlib's `Primrec.eq` (as `Computable₂`).
  have hpred : Computable (fun x : ℕ × ℕ => decide (g x.2 = x.1)) :=
    Computable₂.comp Primrec.eq.decide.to_comp (hg.comp Computable.snd) Computable.fst
  -- `Partrec.rfind` wraps `Nat.rfind` applied to a `Partrec₂` predicate; the
  -- computable predicate above lifts to `Partrec₂` via `Computable.partrec`.
  exact Partrec.rfind hpred.partrec

-- Proof recap (now discharged directly, no Aristotle round-trip needed):
--   1. The search predicate `fun x : ℕ × ℕ => decide (g x.2 = x.1)` is
--      `Computable`: compose Mathlib's `Primrec.eq.decide` (equality test on
--      `ℕ`, lifted to `Computable₂` via `.to_comp`) with `g ∘ snd` and `fst`
--      through `Computable₂.comp`.
--   2. `Computable.partrec` lifts this to the `Partrec₂` predicate that
--      `Partrec.rfind` consumes, yielding `Partrec (fun m => Nat.rfind …)`,
--      which is definitionally `partialInverse g`.
-- Verified axiom-free (`#print axioms` reports only
-- `propext, Classical.choice, Quot.sound` — no `sorryAx`).

end SchroederBernsteinOQ03Statement
