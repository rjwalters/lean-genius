/-
  Erdős Problem #1057 — OQ-04: Chernick's parametric family of Carmichael numbers

  Source: https://erdosproblems.com/1057  (Counting Carmichael Numbers)
  Status of this leaf: VERIFIED (0 axioms, 0 sorries)

  Context:
  The parent entry (Erdos1057Problem.lean) fully proves Korselt's criterion in both
  directions (a composite squarefree n with (p-1) | (n-1) for every prime p | n is
  exactly a number satisfying a^n ≡ a (mod n) for all a). The single remaining `axiom`
  there is the deep Alford–Granville–Pomerance (1994) infinitude theorem, which is far
  out of reach of a self-contained Lean proof.

  This leaf takes the *constructive* route to producing Carmichael numbers that does NOT
  require any axiom: **Chernick's theorem (1939)**.

      If k ≥ 1 and the three numbers
            6k+1,   12k+1,   18k+1
      are all prime, then their product
            n = (6k+1)(12k+1)(18k+1)
      is a Carmichael number.

  The proof is a direct application of Korselt's criterion:
    • n is squarefree (a product of three distinct primes);
    • n is composite (a product of three numbers each ≥ 7);
    • for each prime divisor p ∈ {6k+1, 12k+1, 18k+1} we have (p-1) | (n-1).
  The last point is an algebraic identity: writing a = 6k,
            n - 1 = 36k·(36k² + 11k + 1),
  which is visibly divisible by 6k, by 12k, and by 18k — exactly p-1 for the three
  primes. The numbers 6, 12, 18 (all multiples of 6) are what make the divisibilities
  work out, and this is the whole point of Chernick's choice of coefficients.

  Smallest instances:
    • k = 1:  7 · 13 · 19   = 1729   (the Hardy–Ramanujan taxicab number)
    • k = 6:  37 · 73 · 109 = 294409

  This is the standard way to *exhibit* infinitely many Carmichael numbers conditionally
  on Dickson's prime-tuple conjecture, and gives an unconditional, axiom-free machine
  check of the construction that underlies the lower-bound heuristics for C(x).

  Tags: number-theory, carmichael-numbers, korselt, chernick, constructive
-/

import Mathlib

open Nat

namespace Erdos1057OQ04

/-! ### Self-contained definitions (mirroring the parent entry, kept axiom-free) -/

/-- Korselt's criterion: `n` is squarefree and `(p-1) ∣ (n-1)` for every prime `p ∣ n`. -/
def satisfiesKorselt (n : ℕ) : Prop :=
  Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- A Carmichael number is a composite `n > 1` satisfying Korselt's criterion. -/
def IsCarmichael (n : ℕ) : Prop :=
  n > 1 ∧ ¬n.Prime ∧ satisfiesKorselt n

/-! ### The key algebraic identity -/

/-- The Chernick discriminant identity: with `a = 6k`,
    `(6k+1)(12k+1)(18k+1) = 36k(36k²+11k+1) + 1`. -/
theorem chernick_expand (k : ℕ) :
    (6 * k + 1) * (12 * k + 1) * (18 * k + 1)
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) + 1 := by
  ring

/-- Hence `n - 1 = 36k(36k²+11k+1)`. -/
theorem chernick_pred (k : ℕ) :
    (6 * k + 1) * (12 * k + 1) * (18 * k + 1) - 1
      = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by
  rw [chernick_expand, Nat.add_sub_cancel]

/-! ### Chernick's theorem -/

/-- **Chernick's theorem (1939).** If `6k+1`, `12k+1`, `18k+1` are all prime, then their
    product is a Carmichael number. (`k ≥ 1` is automatic from `6k+1` being prime.) -/
theorem chernick_carmichael (k : ℕ)
    (hp1 : Nat.Prime (6 * k + 1)) (hp2 : Nat.Prime (12 * k + 1))
    (hp3 : Nat.Prime (18 * k + 1)) :
    IsCarmichael ((6 * k + 1) * (12 * k + 1) * (18 * k + 1)) := by
  -- `k ≥ 1` follows from `6k+1 ≥ 2`
  have hk : 1 ≤ k := by have := hp1.two_le; omega
  -- crude lower bounds on the three prime factors
  have e1 : 7 ≤ 6 * k + 1 := by omega
  have e2 : 13 ≤ 12 * k + 1 := by omega
  have e3 : 19 ≤ 18 * k + 1 := by omega
  -- the factors are pairwise distinct
  have hne12 : (6 * k + 1) ≠ (12 * k + 1) := by omega
  have hne13 : (6 * k + 1) ≠ (18 * k + 1) := by omega
  have hne23 : (12 * k + 1) ≠ (18 * k + 1) := by omega
  set N := (6 * k + 1) * (12 * k + 1) * (18 * k + 1) with hN
  -- `N` is large, in particular `> 1`
  have hNge : 7 * 13 * 19 ≤ N := by
    rw [hN]; exact Nat.mul_le_mul (Nat.mul_le_mul e1 e2) e3
  have hN1 : 1 < N := by omega
  -- `6k+1` is a proper divisor, so `N` is composite
  have hp1n : (6 * k + 1) ∣ N := ⟨(12 * k + 1) * (18 * k + 1), by rw [hN]; ring⟩
  have hMge : (13 : ℕ) * 19 ≤ (12 * k + 1) * (18 * k + 1) := Nat.mul_le_mul e2 e3
  have hNeq : N = (6 * k + 1) * ((12 * k + 1) * (18 * k + 1)) := by rw [hN]; ring
  have hlt : (6 * k + 1) < N := by
    rw [hNeq]
    calc 6 * k + 1 = (6 * k + 1) * 1 := (mul_one _).symm
      _ < (6 * k + 1) * ((12 * k + 1) * (18 * k + 1)) :=
          mul_lt_mul_of_pos_left (by omega) (by omega)
  have hnp : ¬ N.Prime := by
    intro h
    rcases (h.eq_one_or_self_of_dvd _ hp1n) with h1 | h2 <;> omega
  -- precompute `N - 1`
  have hNpred : N - 1 = 36 * k * (36 * k ^ 2 + 11 * k + 1) := by rw [hN]; exact chernick_pred k
  -- Squarefree: product of three distinct primes
  have hcop12_3 : Nat.Coprime ((6 * k + 1) * (12 * k + 1)) (18 * k + 1) :=
    Nat.Coprime.mul_left ((Nat.coprime_primes hp1 hp3).mpr hne13)
      ((Nat.coprime_primes hp2 hp3).mpr hne23)
  have hcop1_2 : Nat.Coprime (6 * k + 1) (12 * k + 1) :=
    (Nat.coprime_primes hp1 hp2).mpr hne12
  have hsq : Squarefree N := by
    rw [hN, Nat.squarefree_mul_iff]
    refine ⟨hcop12_3, ?_, hp3.squarefree⟩
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcop1_2, hp1.squarefree, hp2.squarefree⟩
  -- assemble `IsCarmichael`
  refine ⟨hN1, hnp, hsq, ?_⟩
  intro p hp hpdvd
  -- every prime divisor of `N` is one of the three factors
  have hpcase : p = 6 * k + 1 ∨ p = 12 * k + 1 ∨ p = 18 * k + 1 := by
    have hpN : p ∣ (6 * k + 1) * (12 * k + 1) * (18 * k + 1) := by rw [← hN]; exact hpdvd
    rcases (hp.dvd_mul.mp hpN) with h12 | h3
    · rcases (hp.dvd_mul.mp h12) with h1 | h2
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp hp1).mp h1)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp hp2).mp h2))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp hp3).mp h3))
  rcases hpcase with rfl | rfl | rfl
  · rw [Nat.add_sub_cancel]
    exact ⟨6 * (36 * k ^ 2 + 11 * k + 1), by rw [hNpred]; ring⟩
  · rw [Nat.add_sub_cancel]
    exact ⟨3 * (36 * k ^ 2 + 11 * k + 1), by rw [hNpred]; ring⟩
  · rw [Nat.add_sub_cancel]
    exact ⟨2 * (36 * k ^ 2 + 11 * k + 1), by rw [hNpred]; ring⟩

/-! ### Concrete instances -/

/-- `k = 1`: `1729 = 7 · 13 · 19` is a Carmichael number (the taxicab number). -/
theorem chernick_1729 : IsCarmichael 1729 := by
  have h := chernick_carmichael 1 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

/-- `k = 6`: `294409 = 37 · 73 · 109` is a Carmichael number. -/
theorem chernick_294409 : IsCarmichael 294409 := by
  have h := chernick_carmichael 6 (by norm_num) (by norm_num) (by norm_num)
  norm_num at h
  exact h

end Erdos1057OQ04
