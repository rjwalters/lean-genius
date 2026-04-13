/-
Borsuk-Ulam Dimension Formula for Composite n (OQ-02-OQ-01-OQ-01)

The central open question from OQ-02-OQ-01: for composite n ≥ 2, is
  buDim(n, d) = max_{p | n, p prime} buDim(p, d)?

This file proves the lower bound direction (from buDim_mono in the parent
file) and axiomatizes the upper bound (the open conjecture). Specific
cases for n = 4, 6, 9 are derived as consequences.

Status:
- buDimFormula_le: PROVED (lower bound — monotonicity gives the formula ≤ buDim)
- buDim_le_formula: AXIOM (upper bound — the open conjecture)
- Specific cases for n = 4, 6, 9 are PROVED from the conjecture
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Proofs.BorsukUlamOQ02OQ01

namespace BorsukUlamCompositeFormula

open BorsukUlamOQ02OQ01

-- ## The Dimension Formula

/-- The maximum buDim over prime divisors of n.
    This is the conjectured exact value of buDim(n, d) for composite n.
    Examples:
    - buDimFormula 4 d = buDim 2 d     (primeFactors 4 = {2})
    - buDimFormula 6 d = buDim 2 d ⊔ buDim 3 d  (primeFactors 6 = {2,3})
    - buDimFormula 1 d = 0             (primeFactors 1 = ∅) -/
noncomputable def buDimFormula (n d : ℕ) : ℕ :=
  n.primeFactors.sup (fun p => buDim p d)

-- ## Lower Bound (Proved)

/-- The prime factor formula is a lower bound on buDim(n, d).
    Each prime p | n gives buDim(p, d) ≤ buDim(n, d) by monotonicity,
    so the supremum over all such p is also ≤ buDim(n, d). -/
theorem buDimFormula_le (n d : ℕ) : buDimFormula n d ≤ buDim n d := by
  apply Finset.sup_le
  intro p hp
  have hmem := Nat.mem_primeFactors.mp hp
  exact buDim_mono p n d hmem.2.1

-- ## Upper Bound (Open Conjecture, Axiomatized)

/-- **OPEN CONJECTURE**: buDim(n, d) ≤ max_{p|n, prime} buDim(p, d).
    This asserts that composite cyclic groups add no extra topological
    constraint beyond their prime subgroups.

    Evidence (not in Mathlib 4.26):
    - Holds for n = p^k via Smith theory: only prime p matters
    - Holds for standard complex representations via Yang-Borsuk lifting
    - Open for arbitrary representations and general composite n

    References: Fadell-Husseini index theory (1988), Smith theory -/
axiom buDim_le_formula (n d : ℕ) (hn : 2 ≤ n) : buDim n d ≤ buDimFormula n d

-- ## The Formula Theorem

/-- buDim(n, d) equals the prime factor formula for n ≥ 2.
    Combines the proved lower bound with the open conjecture upper bound. -/
theorem buDim_eq_formula (n d : ℕ) (hn : 2 ≤ n) :
    buDim n d = buDimFormula n d :=
  le_antisymm (buDim_le_formula n d hn) (buDimFormula_le n d)

-- ## Formula at Primes

/-- For a prime p, the formula recovers buDim(p, d).
    Proof by antisymmetry: lower bound from buDim_mono, upper from le_sup. -/
theorem buDimFormula_prime (p d : ℕ) (hp : Nat.Prime p) :
    buDimFormula p d = buDim p d := by
  apply le_antisymm
  · apply Finset.sup_le
    intro q hq
    have hmem := Nat.mem_primeFactors.mp hq
    exact buDim_mono q p d hmem.2.1
  · apply Finset.le_sup (f := fun q => buDim q d)
    rw [Nat.mem_primeFactors]
    exact ⟨hp, dvd_refl p, hp.pos.ne'⟩

/-- For a prime p, the conjecture is trivially verified: buDim(p, d) = buDim(p, d). -/
theorem buDim_prime_eq_formula (p d : ℕ) (hp : Nat.Prime p) :
    buDim p d = buDimFormula p d :=
  (buDimFormula_prime p d hp).symm

-- ## Concrete Cases

/-- buDim(4, d) = buDim(2, d): Z/4 has the same BU dimension as Z/2.
    Since the only prime factor of 4 is 2, the formula gives buDim(2, d). -/
theorem buDim_four_eq_two (d : ℕ) : buDim 4 d = buDim 2 d := by
  have h := buDim_eq_formula 4 d (by norm_num)
  simp only [buDimFormula] at h
  have hfact : Nat.primeFactors 4 = {2} := by native_decide
  rw [hfact, Finset.sup_singleton] at h
  exact h

/-- buDim(6, d) = max(buDim(2, d), buDim(3, d)).
    The prime factors of 6 are {2, 3}. -/
theorem buDim_six_eq_max (d : ℕ) : buDim 6 d = buDim 2 d ⊔ buDim 3 d := by
  have h := buDim_eq_formula 6 d (by norm_num)
  simp only [buDimFormula] at h
  have hfact : Nat.primeFactors 6 = {2, 3} := by native_decide
  rw [hfact] at h
  simp only [Finset.sup_insert, Finset.sup_singleton] at h
  exact h

/-- buDim(9, d) = buDim(3, d): Z/9 (= Z/3²) has the same BU dimension as Z/3.
    This shows prime squares don't increase the BU dimension. -/
theorem buDim_nine_eq_three (d : ℕ) : buDim 9 d = buDim 3 d := by
  have h := buDim_eq_formula 9 d (by norm_num)
  simp only [buDimFormula] at h
  have hfact : Nat.primeFactors 9 = {3} := by native_decide
  rw [hfact, Finset.sup_singleton] at h
  exact h

-- ## Specific BU Dimensions

/-- buDim(4, n+1) = n: Z/4-equivariant odd maps S^n → R^{n+1} must vanish.
    This matches the classical Z/2 result (buDim 2 (n+1) = n). -/
theorem buDim_four_succ (n : ℕ) : buDim 4 (n + 1) = n := by
  rw [buDim_four_eq_two, buDim_two]

/-- buDim(6, 2n) = 2n-1 for n ≥ 1: Z/6 has the same BU dimension as Z/2 and Z/3.
    Both prime bounds agree at 2n-1, so the maximum is also 2n-1. -/
theorem buDim_six_even (n : ℕ) (hn : 0 < n) : buDim 6 (2 * n) = 2 * n - 1 := by
  rw [buDim_six_eq_max]
  have h2 : buDim 2 (2 * n) = 2 * n - 1 := by
    have := buDim_two (2 * n - 1)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ 2 * n)] at this
  have h3 : buDim 3 (2 * n) = 2 * n - 1 :=
    buDim_prime 3 n (by decide) hn
  simp [h2, h3]

end BorsukUlamCompositeFormula
