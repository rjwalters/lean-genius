/-
Exotic G-Representations in Equivariant Borsuk-Ulam Theory (OQ-02-OQ-01-OQ-01-OQ-02)

Open Question: Are there exotic G-representations where composite groups
give strictly higher BU dimensions than any prime subgroup?

More precisely: does there exist n ≥ 2 (composite) and d such that
  buDim(n, d) > max_{p | n, p prime} buDim(p, d) = buDimFormula(n, d)?

Context:
- OQ-02-OQ-01 axiomatized buDim(n, d) and proved monotonicity
- OQ-02-OQ-01-OQ-01 axiomatized the formula conjecture: buDim ≤ buDimFormula
- This file formalizes "exotic" representations, derives structural constraints,
  and shows that no exotic representations exist under the formula conjecture

Key results proved:
- Primes are trivially non-exotic (buDimFormula(p, d) = buDim(p, d))
- Prime powers p^k are non-exotic (requires formula axiom; only prime factor is p)
- Formula is monotone under divisibility (purely structural, no axioms needed)
- Exotic representations must have ≥ 2 distinct prime factors (structural)
- Under the formula conjecture, NO exotic representations exist for n ≥ 2

References:
- Fadell & Husseini, "An ideal-valued cohomological index theory" (1988)
- Smith, "Fixed-point theorems for periodic transformations" (1941)
- Bredon, "Introduction to Compact Transformation Groups" (1972)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Lattice
import Mathlib.Tactic
import Proofs.BorsukUlamOQ02OQ01
import Proofs.BorsukUlamOQ02OQ01OQ01

namespace BorsukUlamExotic

open BorsukUlamOQ02OQ01 BorsukUlamCompositeFormula

-- ============================================================
-- PART I: Exotic Representations
-- ============================================================

/-- A representation (n, d) is exotic if the composite group BU dimension
    strictly exceeds the prime factor formula.
    Equivalently: buDim(n, d) exceeds what any prime subgroup can explain. -/
def IsExotic (n d : ℕ) : Prop := buDimFormula n d < buDim n d

/-- The exotic defect: how much the BU dimension exceeds the prime formula.
    Zero precisely when not exotic. -/
noncomputable def exoticDefect (n d : ℕ) : ℕ := buDim n d - buDimFormula n d

theorem exoticDefect_eq_zero_iff (n d : ℕ) : exoticDefect n d = 0 ↔ ¬IsExotic n d := by
  unfold exoticDefect IsExotic
  rw [Nat.sub_eq_zero_iff_le, not_lt]

-- ============================================================
-- PART II: Non-Exotic Cases
-- ============================================================

/-- Primes are never exotic: buDimFormula(p, d) = buDim(p, d). -/
theorem not_exotic_prime (p d : ℕ) (hp : Nat.Prime p) : ¬IsExotic p d := by
  simp [IsExotic, buDimFormula_prime p d hp]

/-- If n has a single prime factor p (i.e., n is a prime power), n is not exotic.
    Proof: buDimFormula(n,d) = buDim(p,d) ≥ buDim(n,d) by the formula axiom. -/
theorem not_exotic_of_singleton_primeFactors (n d p : ℕ) (hp : Nat.Prime p)
    (hset : n.primeFactors = {p}) : ¬IsExotic n d := by
  simp only [IsExotic, not_lt]
  have hn2 : 2 ≤ n := Nat.nonempty_primeFactors.mp (hset ▸ Finset.singleton_nonempty p)
  exact buDim_le_formula n d hn2

/-- Prime powers p^k (k ≥ 1) are never exotic.
    Uses buDim_le_formula: the only prime factor of p^k is p. -/
theorem not_exotic_prime_pow (p k d : ℕ) (hp : Nat.Prime p) (hk : k ≠ 0) :
    ¬IsExotic (p ^ k) d :=
  not_exotic_of_singleton_primeFactors (p ^ k) d p hp
    (Nat.primeFactors_prime_pow hk hp.prime)

/-- For any prime p and k ≥ 1: buDimFormula(p^k, d) = buDim(p, d). -/
theorem buDimFormula_prime_pow (p k d : ℕ) (hp : Nat.Prime p) (hk : k ≠ 0) :
    buDimFormula (p ^ k) d = buDim p d := by
  simp [buDimFormula, Nat.primeFactors_prime_pow hk hp.prime]

-- ============================================================
-- PART III: Formula Monotonicity (No Axioms Needed)
-- ============================================================

/-- The prime factor formula is monotone under divisibility.
    If n | m, every prime of n is also a prime of m, so the sup grows. -/
theorem buDimFormula_mono_of_dvd (n m d : ℕ) (h : n ∣ m) (hm : m ≠ 0) :
    buDimFormula n d ≤ buDimFormula m d :=
  Finset.sup_mono (Nat.primeFactors_mono h hm)

/-- The BU dimension respects divisibility: n | m → buDim n d ≤ buDim m d.
    This follows from buDim_mono which holds for all divisors, not just primes. -/
theorem buDim_dvd_mono (n m d : ℕ) (h : n ∣ m) : buDim n d ≤ buDim m d :=
  buDim_mono n m d h

-- ============================================================
-- PART IV: Structural Constraints on Exotic Representations
-- ============================================================

/-- Exotic representations are always for composite numbers. -/
theorem exotic_implies_not_prime (n d : ℕ) (he : IsExotic n d) : ¬Nat.Prime n :=
  fun hp => not_exotic_prime n d hp he

/-- Exotic requires at least 2 distinct prime factors.
    A prime or prime power cannot be exotic. -/
theorem exotic_implies_two_prime_factors (n d : ℕ) (hn : 2 ≤ n) (he : IsExotic n d) :
    2 ≤ n.primeFactors.card := by
  by_contra hlt
  push_neg at hlt
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  have hcard_pos : 0 < n.primeFactors.card := Finset.card_pos.mpr hne
  have h1 : n.primeFactors.card = 1 := by omega
  obtain ⟨p, hset⟩ := Finset.card_eq_one.mp h1
  have hmem : p ∈ n.primeFactors := by simp [hset]
  have hp : Nat.Prime p := (Nat.mem_primeFactors.mp hmem).1
  exact not_exotic_of_singleton_primeFactors n d p hp hset he

-- ============================================================
-- PART V: Equivalences with the Conjecture
-- ============================================================

/-- IsExotic is exactly the negation of the upper bound axiom for that (n, d). -/
theorem exotic_iff_refutes_conjecture (n d : ℕ) :
    IsExotic n d ↔ ¬(buDim n d ≤ buDimFormula n d) := by
  simp [IsExotic, not_le]

/-- Under the formula conjecture, no exotic representations exist for n ≥ 2. -/
theorem no_exotic_of_conjecture (n d : ℕ) (hn : 2 ≤ n) : ¬IsExotic n d := by
  simp [IsExotic, not_lt, buDim_le_formula n d hn]

/-- The formula conjecture is equivalent to the absence of all exotic representations. -/
theorem conjecture_iff_no_exotic :
    (∀ n d, 2 ≤ n → buDim n d ≤ buDimFormula n d) ↔
    (∀ n d, 2 ≤ n → ¬IsExotic n d) := by
  simp [IsExotic, not_lt]

-- ============================================================
-- PART VI: Concrete Non-Exotic Examples (Prime Powers)
-- ============================================================

theorem not_exotic_four (d : ℕ) : ¬IsExotic 4 d :=
  not_exotic_prime_pow 2 2 d (by norm_num) (by norm_num)

theorem not_exotic_eight (d : ℕ) : ¬IsExotic 8 d :=
  not_exotic_prime_pow 2 3 d (by norm_num) (by norm_num)

theorem not_exotic_nine (d : ℕ) : ¬IsExotic 9 d :=
  not_exotic_prime_pow 3 2 d (by norm_num) (by norm_num)

theorem not_exotic_twentyfive (d : ℕ) : ¬IsExotic 25 d :=
  not_exotic_prime_pow 5 2 d (by norm_num) (by norm_num)

/-- The buDimFormula for prime powers equals the prime's BU dimension. -/
theorem buDimFormula_four (d : ℕ) : buDimFormula 4 d = buDim 2 d :=
  buDimFormula_prime_pow 2 2 d (by norm_num) (by norm_num)

theorem buDimFormula_nine (d : ℕ) : buDimFormula 9 d = buDim 3 d :=
  buDimFormula_prime_pow 3 2 d (by norm_num) (by norm_num)

-- ============================================================
-- PART VII: The First Potential Exotic Case n = 6
-- ============================================================

/-- n = 6 is the smallest n ≥ 2 with ≥ 2 distinct prime factors.
    It is the first case where exotic behavior could in principle occur. -/
theorem six_has_two_prime_factors : (6 : ℕ).primeFactors.card = 2 := by native_decide

/-- buDimFormula for n = 6: max of Z/2 and Z/3 BU dimensions. -/
theorem buDimFormula_six (d : ℕ) : buDimFormula 6 d = buDim 2 d ⊔ buDim 3 d := by
  have : Nat.primeFactors 6 = {2, 3} := by native_decide
  simp [buDimFormula, this, Finset.sup_insert]

/-- All n ∈ [2, 5] are prime powers (having exactly one prime factor). -/
theorem small_n_not_exotic_shape : ∀ n ∈ Finset.Icc 2 5, n.primeFactors.card ≤ 1 := by
  decide

/-- n = 6 is not exotic under the formula conjecture (axiom). -/
theorem not_exotic_six (d : ℕ) : ¬IsExotic 6 d :=
  no_exotic_of_conjecture 6 d (by norm_num)

/-- Under the conjecture: buDim(6, d) = max(buDim(2, d), buDim(3, d)). -/
theorem buDim_six_eq_max (d : ℕ) : buDim 6 d = buDim 2 d ⊔ buDim 3 d := by
  rw [buDim_eq_formula 6 d (by norm_num), buDimFormula_six]

-- ============================================================
-- PART VIII: Exotic Defect Properties
-- ============================================================

theorem exoticDefect_prime_pow (p k d : ℕ) (hp : Nat.Prime p) (hk : k ≠ 0) :
    exoticDefect (p ^ k) d = 0 :=
  (exoticDefect_eq_zero_iff (p ^ k) d).mpr (not_exotic_prime_pow p k d hp hk)

theorem exoticDefect_zero_of_conjecture (n d : ℕ) (hn : 2 ≤ n) :
    exoticDefect n d = 0 :=
  (exoticDefect_eq_zero_iff n d).mpr (no_exotic_of_conjecture n d hn)

end BorsukUlamExotic
