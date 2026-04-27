/-
  Aristotle targets for Erdős Problem #240: P-Smooth Numbers with Large Gaps
  Routine supporting lemmas for automated proof search.
  See Erdos240Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main existence question (erdos240Question — deep, uses Tijdeman axiom)
  - NOT analytical growth results (require smoothEnum properties)
  - singleton_large_gaps: follows directly from finite_P_unbounded_gaps axiom
  - Simple P-smooth membership lemmas provable from definitions
  - No new axioms, no definition sorries, no open conjectures
  - No /-! docstring sections (use /- instead)

  Included targets:
  - singleton_large_gaps_ari: gapsTendToInfinity {p} for prime p
    (follows from finite_P_unbounded_gaps since {p} is a finite set)
  - isPSmooth_powers_ari: p^k is {p}-smooth for any k
  - isPSmooth_one_ari: 1 is P-smooth for any P
  - isPSmooth_mono_ari: if P ⊆ Q then P-smooth ⊆ Q-smooth
  - gap_pos_ari: gaps between consecutive smooth numbers are positive

  Excluded:
  - erdos240_answer — requires smoothEnum to be monotone/injective (no axiom)
  - tijdeman bounds — deep quantitative result
  - polya_theorem — deep number theory
-/
import Mathlib
import Proofs.Erdos240Problem

namespace Erdos240Aristotle

open Erdos240 Set

-- ═══════════════════════════════════════════════════════════════════
-- PART I: Singleton P Has Unbounded Gaps
-- ═══════════════════════════════════════════════════════════════════

/-- For a prime p, the set {p}-smooth numbers have unbounded gaps.
    Proof: {p} is a finite set of primes, so finite_P_unbounded_gaps applies. -/
theorem singleton_large_gaps_ari (p : ℕ) (hp : p.Prime) :
    gapsTendToInfinity ({p} : Set ℕ) := by
  have h : ({p} : Set ℕ) = ↑({p} : Finset ℕ) := by simp
  rw [h]
  exact finite_P_unbounded_gaps {p} (by simp [hp])

/-- For two primes p, q, the set {p, q}-smooth numbers have unbounded gaps. -/
theorem two_prime_large_gaps_ari (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    gapsTendToInfinity ({p, q} : Set ℕ) := by
  have h : ({p, q} : Set ℕ) = ↑({p, q} : Finset ℕ) := by simp
  rw [h]
  exact finite_P_unbounded_gaps {p, q} (by
    intro r hr
    simp at hr
    rcases hr with rfl | rfl <;> assumption)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: Basic P-Smooth Properties
-- ═══════════════════════════════════════════════════════════════════

/-- Powers of p are {p}-smooth.
    Proof: Every prime factor of p^k is p, which is in {p}. -/
theorem isPSmooth_prime_pow_ari (p k : ℕ) (hp : p.Prime) :
    isPSmooth ({p} : Set ℕ) (p ^ k) := by
  constructor
  · positivity
  · intro q hq hdvd
    have : q ∣ p := hq.dvd_of_dvd_pow hdvd
    have := hp.eq_one_or_self_of_dvd q this
    rcases this with h | h
    · exact absurd h hq.ne_one
    · simp [h]

/-- 1 is P-smooth for any P. -/
theorem isPSmooth_one_ari (P : Set ℕ) : isPSmooth P 1 :=
  one_isPSmooth P

/-- P-smooth numbers are monotone in P: if P ⊆ Q then isPSmooth P n → isPSmooth Q n. -/
theorem isPSmooth_mono_ari (P Q : Set ℕ) (hPQ : P ⊆ Q) (n : ℕ)
    (h : isPSmooth P n) : isPSmooth Q n := by
  exact ⟨h.1, fun p hp hdvd => hPQ (h.2 p hp hdvd)⟩

/-- If n is {p}-smooth and n > 1, then p ∣ n. -/
theorem isPSmooth_singleton_dvd_ari (p n : ℕ) (hp : p.Prime) (hn : n > 1)
    (h : isPSmooth ({p} : Set ℕ) n) : p ∣ n := by
  -- n > 1 has a prime factor q; q is {p}-smooth, so q = p
  obtain ⟨q, hq, hqn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
  have hqp : q ∈ ({p} : Set ℕ) := h.2 q hq hqn
  simp at hqp
  rw [← hqp]; exact hqn

-- ═══════════════════════════════════════════════════════════════════
-- PART III: Finite Sets Give Unbounded Gaps
-- ═══════════════════════════════════════════════════════════════════

/-- For any finite set of primes P with |P| ≤ 3, gaps tend to infinity.
    These are consequences of finite_P_unbounded_gaps. -/
theorem finite_two_primes_ari (P : Finset ℕ) (hP : P.card ≤ 2)
    (hPrime : ∀ p ∈ P, Nat.Prime p) :
    gapsTendToInfinity (↑P : Set ℕ) :=
  finite_P_unbounded_gaps P hPrime

end Erdos240Aristotle
