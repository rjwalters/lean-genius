/-
  Aristotle targets for Erdős Problem #378
  Routine supporting lemmas for automated proof search.
  See Erdos378Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT erdos_378_density_exists, erdos_378_density_positive (deep density analysis)
  - NOT erdos_378_answer (combines density results)
  - Routine arithmetic: squarefree facts, binomial coefficient identities
  - No definition sorries
  - No axioms

  These lemmas use Mathlib's `Squarefree` (which is decidable on `ℕ`), matching the
  main file `Erdos378Problem.lean`.
-/
import Mathlib

namespace Erdos378Aristotle

open Nat

-- Routine: 1 is squarefree.
theorem squarefree_one : Squarefree (1 : ℕ) := _root_.squarefree_one

-- Routine: every prime is squarefree.
theorem squarefree_prime (p : ℕ) (hp : p.Prime) : Squarefree p :=
  hp.prime.squarefree

-- Routine: 2 is squarefree (it's prime).
theorem squarefree_two : Squarefree (2 : ℕ) := Nat.prime_two.prime.squarefree

-- Routine: 3 is squarefree (it's prime).
theorem squarefree_three : Squarefree (3 : ℕ) := Nat.prime_three.squarefree

-- Routine: 6 = 2 · 3 is squarefree (coprime product of squarefrees).
theorem squarefree_six : Squarefree (6 : ℕ) := by
  rw [show (6 : ℕ) = 2 * 3 from rfl, Nat.squarefree_mul_iff]
  exact ⟨by decide, Nat.prime_two.prime.squarefree, Nat.prime_three.squarefree⟩

-- Routine: C(n, 1) = n for n ≥ 1.
theorem choose_one (n : ℕ) : Nat.choose n 1 = n := by
  simp [Nat.choose_one_right]

-- Routine: C(n, n) = 1 for all n.
theorem choose_self (n : ℕ) : Nat.choose n n = 1 := Nat.choose_self n

-- Routine: C(n, 0) = 1 for all n.
theorem choose_zero (n : ℕ) : Nat.choose n 0 = 1 := Nat.choose_zero_right n

-- Routine: C(n, k) ≥ 1 for k ≤ n.
theorem choose_pos (n k : ℕ) (hk : k ≤ n) : Nat.choose n k ≥ 1 :=
  Nat.choose_pos hk

-- Routine: C(n, 0) = 1 is squarefree.
theorem binomialSquarefree_zero (n : ℕ) : Squarefree (Nat.choose n 0) := by
  rw [Nat.choose_zero_right]; exact _root_.squarefree_one

-- Routine: C(n, n) = 1 is squarefree.
theorem binomialSquarefree_self (n : ℕ) : Squarefree (Nat.choose n n) := by
  rw [Nat.choose_self]; exact _root_.squarefree_one

-- Routine: squarefreeness passes to divisors.
theorem squarefree_of_dvd (m n : ℕ) (hdvd : m ∣ n) (hn : Squarefree n) : Squarefree m :=
  hn.squarefree_of_dvd hdvd

end Erdos378Aristotle
