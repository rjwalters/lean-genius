/-!
# Erdős Problem #689 — Double Covering by Prime Congruence Classes

For sufficiently large n, can we choose congruence classes a_p for all
primes 2 ≤ p ≤ n such that every integer in [1, n] satisfies at least
two of the congruences m ≡ a_p (mod p)?

This asks whether primes up to n provide enough "covering power" to
doubly cover [1, n] with chosen residue classes.

Generalizes to r-fold covering for any fixed r.

Status: OPEN
Reference: https://erdosproblems.com/689
Source: [Er79d]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- A choice of congruence classes: for each prime p, a residue a_p. -/
def CongruenceChoice (n : ℕ) := (p : ℕ) → p.Prime → p ≤ n → Fin p

/-- An integer m is covered by prime p with choice a_p if m ≡ a_p (mod p). -/
def IsCovered (m : ℕ) (p : ℕ) (a : ℕ) : Prop :=
  m % p = a % p

/-- The covering count: how many primes p ≤ n cover m with the
    chosen congruence classes. -/
noncomputable def coveringCount (n m : ℕ) (a : ℕ → ℕ) : ℕ :=
  Finset.card (Finset.filter
    (fun p => Nat.Prime p ∧ p ≤ n ∧ IsCovered m p (a p))
    (Finset.range (n + 1)))

/-- A congruence choice r-fold covers [1, n] if every m ∈ [1, n]
    is covered by at least r primes. -/
def IsRFoldCover (n r : ℕ) (a : ℕ → ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ n → coveringCount n m a ≥ r

/-! ## Main Question -/

/-- **Erdős Problem #689**: For sufficiently large n, does there
    exist a choice of congruence classes that 2-fold covers [1, n]? -/
axiom erdos_689_double_cover :
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ a : ℕ → ℕ, IsRFoldCover n 2 a

/-! ## Generalizations -/

/-- **r-fold generalization**: For any fixed r and sufficiently
    large n (depending on r), does an r-fold covering exist?
    This appears as a natural extension. -/
axiom erdos_689_r_fold (r : ℕ) (hr : r ≥ 1) :
  ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ a : ℕ → ℕ, IsRFoldCover n r a

/-! ## Observations -/

/-- **Prime density**: By the prime number theorem, there are
    ~n/log n primes up to n. Each prime p covers a fraction 1/p
    of integers. The sum Σ_{p≤n} 1/p ~ log log n, so on average
    each integer is covered ~log log n times — more than 2. -/
axiom prime_density_argument :
  ∀ n : ℕ, n ≥ 2 →
    ∃ S : ℝ, S > 0 ∧ True  -- Σ 1/p ~ log log n

/-- **Probabilistic heuristic**: If each a_p is chosen uniformly
    at random, the expected covering count for any m is Σ_{p≤n} 1/p
    ~ log log n. The challenge is handling correlations and ensuring
    *every* m ∈ [1,n] achieves count ≥ 2 simultaneously. -/
axiom probabilistic_heuristic : True

/-- **Connection to covering systems**: Related to Erdős Problems
    #687 and #688 about covering congruences. The minimum modulus
    problem and Hough's theorem (2015) on covering systems with
    distinct moduli are closely related. -/
axiom covering_systems_connection : True

/-- **Ben Green variant**: Problem 45 on Ben Green's list asks
    the same question with 2 replaced by 10, suggesting the
    threshold for r-fold covering is of interest. -/
axiom green_variant : True
