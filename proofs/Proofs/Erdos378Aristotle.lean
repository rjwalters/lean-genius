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
-/
import Mathlib

namespace Erdos378Aristotle

open Nat

/-- Squarefree: n is squarefree if no prime squared divides n. -/
def Squarefree (n : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → ¬(p * p ∣ n)

-- Routine: 1 is squarefree.
-- No prime squared divides 1, since p² ≥ 4 > 1.
theorem squarefree_one : Squarefree 1 := by
  intro p hp hdiv
  have hge : p * p ≥ 4 := by
    have := hp.two_le
    omega
  omega

-- Routine: Every prime is squarefree.
-- For prime p, p² ∤ p since p² > p.
theorem squarefree_prime (p : ℕ) (hp : p.Prime) : Squarefree p := by
  intro q hq hdvd
  have hq2 : q * q ≥ 4 := by
    have := hq.two_le; omega
  have hp2 : p ≥ 2 := hp.two_le
  have : q * q ≤ p := Nat.le_of_dvd (by omega) hdvd
  have hqle : q ≤ p := by nlinarith
  -- q divides p and q is prime, so q = p or q = 1. Since q is prime, q = p.
  have hqdvdp : q ∣ p := Nat.dvd_of_mul_dvd_mul_left (by omega) (Dvd.dvd.mul_left hdvd q)
  have := hp.eq_one_or_self_of_dvd q hqdvdp
  rcases this with h | h
  · exact hq.ne_one h
  · subst h; nlinarith

-- Routine: 2 is squarefree (it's prime).
theorem squarefree_two : Squarefree 2 := squarefree_prime 2 Nat.prime_iff.mpr ⟨by norm_num, by omega⟩

-- Routine: 3 is squarefree (it's prime).
theorem squarefree_three : Squarefree 3 := squarefree_prime 3 (by norm_num)

-- Routine: 6 is squarefree.
-- 6 = 2 · 3; the only prime squares ≥ 4, and 4 ∤ 6 and 9 ∤ 6.
theorem squarefree_six : Squarefree 6 := by
  intro p hp hdvd
  have hge : p * p ≥ 4 := by have := hp.two_le; omega
  have hle : p * p ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases p <;> simp_all

-- Routine: C(n, 1) = n for n ≥ 1.
-- The number of 1-element subsets of an n-element set is n.
theorem choose_one (n : ℕ) (hn : n ≥ 1) : Nat.choose n 1 = n := by
  simp [Nat.choose_one_right]

-- Routine: C(n, n) = 1 for all n.
-- The only n-element subset of an n-element set is the set itself.
theorem choose_self (n : ℕ) : Nat.choose n n = 1 := Nat.choose_self n

-- Routine: C(n, 0) = 1 for all n.
-- The empty set is the unique 0-element subset.
theorem choose_zero (n : ℕ) : Nat.choose n 0 = 1 := Nat.choose_zero_right n

-- Routine: C(n, k) ≥ 1 for k ≤ n.
-- There is at least one k-element subset of an n-element set.
theorem choose_pos (n k : ℕ) (hk : k ≤ n) : Nat.choose n k ≥ 1 :=
  Nat.choose_pos hk

-- Routine: 1 is squarefree, so BinomialSquarefree n 0 holds.
-- C(n, 0) = 1 which is squarefree.
theorem binomialSquarefree_zero (n : ℕ) : Squarefree (Nat.choose n 0) := by
  simp [Nat.choose_zero_right]
  exact squarefree_one

-- Routine: C(n, n) = 1 is squarefree.
theorem binomialSquarefree_self (n : ℕ) : Squarefree (Nat.choose n n) := by
  simp [Nat.choose_self]
  exact squarefree_one

-- Routine: Squarefree is preserved by divisors.
-- If n is squarefree and m ∣ n, then m is squarefree.
theorem squarefree_of_dvd (m n : ℕ) (hdvd : m ∣ n) (hn : Squarefree n) : Squarefree m := by
  intro p hp hpm
  exact hn p hp (hpm.trans hdvd)

end Erdos378Aristotle
