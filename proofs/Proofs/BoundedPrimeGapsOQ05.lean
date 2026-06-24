/-
# Firoozbakht's Conjecture: Equivalence of the Three Standard Formulations

Farideh Firoozbakht (1982) conjectured that the sequence `p_n^{1/n}` is
*strictly decreasing*, where `p_n` denotes the n-th prime:

    p_{n+1}^{1/(n+1)} < p_n^{1/n}        (ROOT form — the original statement)

It is folklore that this is equivalent to two other commonly cited forms:

    p_{n+1} < p_n^{1 + 1/n}              (RPOW form)
    p_{n+1}^n < p_n^{n+1}               (INTEGER-POWER form, a statement in ℕ)

The conjecture itself is open (verified past 10^19), but the *equivalence of
its formulations* is an unconditional theorem of real analysis. This file
proves that equivalence — first as a pointwise three-way iff for an arbitrary
pair of positive reals, then specialized to the prime sequence.

The gallery's `BoundedPrimeGaps.lean` formalizes only the RPOW form (as
`FireoozbakhtConjecture`) together with its conditional gap/ratio consequences.
This file supplies the missing bridges: to the *original* root statement and
to the clean integer-power form, which for primes is a statement about natural
numbers and therefore the most elementary of the three.

All results below are unconditional and axiom-free.

## Main results

* `root_lt_iff`     — pointwise: root inequality ⟺ core `a^n < b^{n+1}` (real rpow)
* `rpow_lt_iff`     — pointwise: rpow inequality ⟺ same core
* `core_real_iff_nat` — core real inequality ⟺ the natural-number inequality
* `firoozbakht_forms_tfae` — the three prime formulations are equivalent
-/
import Mathlib

namespace FiroozbakhtForms

open Real

/-! ## Pointwise three-way equivalence for positive reals

Fix `a, b > 0` (think `a = p_{n+1}`, `b = p_n`) and `n ≥ 1`. Each of the three
inequalities reduces to the common core `a ^ (n : ℝ) < b ^ ((n : ℝ) + 1)`. -/

variable {a b : ℝ}

/-- **Root form ⟺ core.** For `a, b > 0` and `n ≥ 1`, the root inequality
`a^{1/(n+1)} < b^{1/n}` is equivalent to `a^n < b^{n+1}` (real rpow). -/
theorem root_lt_iff (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : 1 ≤ n) :
    a ^ ((1 : ℝ) / ((n : ℝ) + 1)) < b ^ ((1 : ℝ) / (n : ℝ))
      ↔ a ^ (n : ℝ) < b ^ ((n : ℝ) + 1) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have key := Real.rpow_lt_rpow_iff (x := a ^ ((1 : ℝ) / ((n : ℝ) + 1)))
      (y := b ^ ((1 : ℝ) / (n : ℝ))) (Real.rpow_nonneg ha.le _)
      (Real.rpow_nonneg hb.le _) (z := (n : ℝ) * ((n : ℝ) + 1))
      (mul_pos hnpos (by positivity))
  rw [← Real.rpow_mul ha.le, ← Real.rpow_mul hb.le] at key
  have e1 : (1 : ℝ) / ((n : ℝ) + 1) * ((n : ℝ) * ((n : ℝ) + 1)) = (n : ℝ) := by
    field_simp
  have e2 : (1 : ℝ) / (n : ℝ) * ((n : ℝ) * ((n : ℝ) + 1)) = (n : ℝ) + 1 := by
    field_simp
  rw [e1, e2] at key
  exact key.symm

/-- **Rpow form ⟺ core.** For `a, b > 0` and `n ≥ 1`, the inequality
`a < b^{1 + 1/n}` is equivalent to `a^n < b^{n+1}` (real rpow). -/
theorem rpow_lt_iff (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : 1 ≤ n) :
    a < b ^ (1 + (1 : ℝ) / (n : ℝ)) ↔ a ^ (n : ℝ) < b ^ ((n : ℝ) + 1) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have key := Real.rpow_lt_rpow_iff (x := a) (y := b ^ (1 + (1 : ℝ) / (n : ℝ)))
      ha.le (Real.rpow_nonneg hb.le _) (z := (n : ℝ)) hnpos
  rw [← Real.rpow_mul hb.le] at key
  have e : (1 + (1 : ℝ) / (n : ℝ)) * (n : ℝ) = (n : ℝ) + 1 := by
    field_simp
  rw [e] at key
  -- key : a ^ (n:ℝ) < b ^ (n+1) ↔ a < b ^ (1 + 1/n)
  exact key.symm

/-- **Core: real rpow ⟺ natural power.** For natural numbers `p q` with
`0 < p`, `0 < q`, the real inequality `p^n < q^{n+1}` (rpow with real
exponents) is equivalent to the natural-number inequality `p^n < q^{n+1}`. -/
theorem core_real_iff_nat {p q : ℕ} (n : ℕ) :
    (p : ℝ) ^ (n : ℝ) < (q : ℝ) ^ ((n : ℝ) + 1) ↔ p ^ n < q ^ (n + 1) := by
  have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [hcast, Real.rpow_natCast, Real.rpow_natCast, ← Nat.cast_pow, ← Nat.cast_pow,
    Nat.cast_lt]

/-! ## Specialization to the prime sequence -/

/-- The n-th prime, `p_0 = 2`, `p_1 = 3`, … (same convention as the gallery). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

theorem nthPrime_pos (n : ℕ) : 0 < nthPrime n := (Nat.prime_nth_prime n).pos

/-- **ROOT form** of Firoozbakht (the original 1982 statement): the sequence
`p_n^{1/n}` is strictly decreasing. -/
def FiroozbakhtRoot : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (nthPrime (n + 1) : ℝ) ^ ((1 : ℝ) / ((n : ℝ) + 1))
      < (nthPrime n : ℝ) ^ ((1 : ℝ) / (n : ℝ))

/-- **RPOW form** of Firoozbakht: `p_{n+1} < p_n^{1 + 1/n}`. Definitionally the
gallery's `FireoozbakhtConjecture`. -/
def FiroozbakhtRpow : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (nthPrime (n + 1) : ℝ) < (nthPrime n : ℝ) ^ (1 + (1 : ℝ) / (n : ℝ))

/-- **INTEGER-POWER form** of Firoozbakht: `p_{n+1}^n < p_n^{n+1}`, a statement
purely about natural numbers. -/
def FiroozbakhtIntPow : Prop :=
  ∀ n : ℕ, 1 ≤ n → (nthPrime (n + 1)) ^ n < (nthPrime n) ^ (n + 1)

theorem firoozbakht_root_iff_intPow : FiroozbakhtRoot ↔ FiroozbakhtIntPow := by
  constructor
  · intro h n hn
    have ha : (0 : ℝ) < (nthPrime (n + 1) : ℝ) := by exact_mod_cast nthPrime_pos (n + 1)
    have hb : (0 : ℝ) < (nthPrime n : ℝ) := by exact_mod_cast nthPrime_pos n
    exact (core_real_iff_nat n).mp ((root_lt_iff ha hb hn).mp (h n hn))
  · intro h n hn
    have ha : (0 : ℝ) < (nthPrime (n + 1) : ℝ) := by exact_mod_cast nthPrime_pos (n + 1)
    have hb : (0 : ℝ) < (nthPrime n : ℝ) := by exact_mod_cast nthPrime_pos n
    exact (root_lt_iff ha hb hn).mpr ((core_real_iff_nat n).mpr (h n hn))

theorem firoozbakht_rpow_iff_intPow : FiroozbakhtRpow ↔ FiroozbakhtIntPow := by
  constructor
  · intro h n hn
    have ha : (0 : ℝ) < (nthPrime (n + 1) : ℝ) := by exact_mod_cast nthPrime_pos (n + 1)
    have hb : (0 : ℝ) < (nthPrime n : ℝ) := by exact_mod_cast nthPrime_pos n
    exact (core_real_iff_nat n).mp ((rpow_lt_iff ha hb hn).mp (h n hn))
  · intro h n hn
    have ha : (0 : ℝ) < (nthPrime (n + 1) : ℝ) := by exact_mod_cast nthPrime_pos (n + 1)
    have hb : (0 : ℝ) < (nthPrime n : ℝ) := by exact_mod_cast nthPrime_pos n
    exact (rpow_lt_iff ha hb hn).mpr ((core_real_iff_nat n).mpr (h n hn))

theorem firoozbakht_root_iff_rpow : FiroozbakhtRoot ↔ FiroozbakhtRpow := by
  rw [firoozbakht_root_iff_intPow, firoozbakht_rpow_iff_intPow]

/-- **The three formulations of Firoozbakht's conjecture are equivalent.**
This is unconditional: it does not assert the conjecture, only that its three
standard statements coincide. -/
theorem firoozbakht_forms_tfae :
    [FiroozbakhtRoot, FiroozbakhtRpow, FiroozbakhtIntPow].TFAE := by
  tfae_have 1 ↔ 3 := firoozbakht_root_iff_intPow
  tfae_have 2 ↔ 3 := firoozbakht_rpow_iff_intPow
  tfae_finish

end FiroozbakhtForms
