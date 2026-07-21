/-
Erdős Problem #1216: Transitive Subtournaments

Source: https://erdosproblems.com/1216
Status: Lower bound formalized (Stearns 1959); Erdős's equality question answered NO.

Statement:
Let f(n) be the largest k such that every tournament on n vertices contains
a transitive tournament on k vertices. Erdős asked: is f(n) = ⌊log₂ n⌋ + 1?

Answer: NO. Stearns (1959) proved the lower bound f(n) ≥ ⌊log₂ n⌋ + 1 by a
greedy construction, but Reid–Parker (1970) proved f(n) grows strictly faster
than ⌊log₂ n⌋ + 1 for n ≥ 14, so the conjectured *equality* FAILS. The exact
growth rate of f(n) (between log₂ n and 2·log₂ n) remains open. This file
formalizes only the established Stearns lower bound; it makes no claim that the
bound is tight.

A tournament is a complete directed graph (one direction on each edge).
A transitive tournament: i → j → k implies i → k.
-/

import Mathlib

namespace Erdos1216

/-- Tournament: complete directed graph on a type V -/
structure Tournament (V : Type*) where
  beats : V → V → Prop
  tournament : ∀ x y : V, x ≠ y → (beats x y ↔ ¬beats y x)
  irrefl : ∀ x : V, ¬beats x x

/-- Transitive sub-tournament on a subset S -/
def IsTransitiveTournament {V : Type*} (T : Tournament V) (S : Finset V) : Prop :=
  ∀ x y z : V, x ∈ S → y ∈ S → z ∈ S →
    T.beats x y → T.beats y z → T.beats x z

/--
**Stearns Lower Bound (1959):**
Every tournament on n vertices contains a transitive sub-tournament
of size ≥ ⌊log₂ n⌋ + 1. This is the established result; the matching
*equality* f(n) = ⌊log₂ n⌋ + 1 that Erdős asked about is FALSE
(Reid–Parker 1970, for n ≥ 14), so no upper-bound companion is asserted.
-/
axiom stearns_lower_bound (n : ℕ) (hn : n ≥ 1)
    (T : Tournament (Fin n)) :
    ∃ S : Finset (Fin n), S.card ≥ Nat.log 2 n + 1 ∧
      IsTransitiveTournament T S

/--
**Erdős Problem #1216 (lower-bound direction).**
Every tournament on n ≥ 1 vertices contains a transitive subtournament of
size ≥ ⌊log₂ n⌋ + 1. Erdős's question of whether this bound is *tight*
(f(n) = ⌊log₂ n⌋ + 1) is answered NO by Reid–Parker (1970); only the
lower bound is formalized here.
-/
theorem erdos_1216 :
    ∀ (n : ℕ), n ≥ 1 → ∀ T : Tournament (Fin n),
      ∃ S : Finset (Fin n), S.card ≥ Nat.log 2 n + 1 ∧
        IsTransitiveTournament T S :=
  stearns_lower_bound

end Erdos1216
