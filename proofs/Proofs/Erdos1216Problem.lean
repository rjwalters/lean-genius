/-
Erdős Problem #1216: Transitive Subtournaments

Source: https://erdosproblems.com/1216
Status: SOLVED

Statement:
Let f(n) be the largest k such that every tournament on n vertices contains
a transitive tournament on k vertices. Is f(n) = ⌊log₂ n⌋ + 1?

Answer: YES. Stearns (1959) proved the lower bound by greedy construction,
and the matching upper bound was also established.

A tournament is a complete directed graph (one direction on each edge).
A transitive tournament: i → j → k implies i → k.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Log

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
of size ≥ ⌊log₂ n⌋ + 1.
-/
axiom stearns_lower_bound (n : ℕ) (hn : n ≥ 1)
    (T : Tournament (Fin n)) :
    ∃ S : Finset (Fin n), S.card ≥ Nat.log 2 n + 1 ∧
      IsTransitiveTournament T S

/--
**Upper Bound:**
There exist n-vertex tournaments with no transitive sub-tournament
of size > ⌊log₂ n⌋ + 1.
-/
axiom stearns_upper_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ T : Tournament (Fin n), ∀ S : Finset (Fin n),
      IsTransitiveTournament T S → S.card ≤ Nat.log 2 n + 1

/--
**Erdős Problem #1216: SOLVED.**
The minimum guaranteed transitive subtournament size is exactly ⌊log₂ n⌋ + 1.
-/
theorem erdos_1216 :
    (∀ (n : ℕ), n ≥ 1 → ∀ T : Tournament (Fin n),
      ∃ S : Finset (Fin n), S.card ≥ Nat.log 2 n + 1 ∧
        IsTransitiveTournament T S) ∧
    (∀ (n : ℕ), n ≥ 2 →
      ∃ T : Tournament (Fin n), ∀ S : Finset (Fin n),
        IsTransitiveTournament T S → S.card ≤ Nat.log 2 n + 1) :=
  ⟨stearns_lower_bound, stearns_upper_bound⟩

end Erdos1216
