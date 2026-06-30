import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-
# q-Analog Geometric Series: Quantum Integers

## What This Proves

The **quantum integer** (or *q-integer*) `[n]_q` is the q-analog of the natural
number `n`, defined as the truncated geometric series

  [n]_q  :=  1 + q + q^2 + ... + q^{n-1}  =  ∑_{i < n} q^i.

As `q → 1` every term tends to `1`, so `[n]_1 = n` and the q-integer degenerates
to the ordinary integer.  Quantum integers are the building blocks of the
q-calculus: q-factorials `[n]_q! = [1]_q [2]_q ... [n]_q` and Gaussian
(q-binomial) coefficients are assembled from them, and they appear throughout
combinatorics (counting subspaces of `𝔽_q^n`), representation theory of quantum
groups, and the theory of partitions.

This file gives a self-contained development of `[n]_q` over an arbitrary
commutative ring and proves the four structural laws that characterise it:

1. **Geometric closed form** `qNat_mul_qSub`:
     `[n]_q · (q - 1) = q^n - 1`           (valid in any commutative ring)
   and its field version `qNat_eq_div`: `[n]_q = (q^n - 1)/(q - 1)` for `q ≠ 1`.

2. **Classical limit** `qNat_at_one`: `[n]_1 = n`.

3. **Additive law** `qNat_add`:
     `[m + n]_q = [m]_q + q^m · [n]_q`.
   This is the q-analog of `m + n`; the cocycle factor `q^m` is exactly what
   makes the q-integers a *non-trivial* deformation of ℕ.

4. **Multiplicative law** `qNat_mul`:
     `[m · n]_q = [m]_{q^n} · [n]_q`.
   The base of the first factor is `q^n`, not `q` — a genuinely q-flavoured
   identity with no q = 1 analog visible (it collapses to `m·n = m·n`).

## Why Mathlib Doesn't Already Have This

Mathlib has the geometric sum `geom_sum_mul`/`geom_sum_eq` but no named
`q`-integer, q-factorial, or Gaussian-binomial theory.  The structural laws
proved here (especially the additive cocycle and the multiplicative base-change
law) are the q-analog facts those generic lemmas do not package.

## Honesty Note

These are standard, textbook q-analog identities (Kac–Cheung, *Quantum
Calculus*, Ch. 1–7).  The contribution is a faithful, fully machine-checked
Lean formalization of a structure Mathlib lacks, not a new mathematical result.
All proofs are 0-axiom (only Lean's foundational axioms).
-/

open Finset

namespace QuantumInteger

variable {R : Type*} [CommRing R]

/-- The **quantum integer** `[n]_q = ∑_{i < n} q^i = 1 + q + ⋯ + q^{n-1}`. -/
def qNat (q : R) (n : ℕ) : R := ∑ i ∈ Finset.range n, q ^ i

@[simp] theorem qNat_zero (q : R) : qNat q 0 = 0 := by
  simp [qNat]

@[simp] theorem qNat_one (q : R) : qNat q 1 = 1 := by
  simp [qNat]

/-- Recurrence in the index: appending the next power. -/
theorem qNat_succ (q : R) (n : ℕ) : qNat q (n + 1) = qNat q n + q ^ n := by
  simp [qNat, Finset.sum_range_succ]

/-- The geometric-series closed form, valid in **any** commutative ring:
`[n]_q · (q - 1) = q^n - 1`. -/
theorem qNat_mul_qSub (q : R) (n : ℕ) : qNat q n * (q - 1) = q ^ n - 1 := by
  simpa [qNat] using geom_sum_mul q n

/-- **Classical limit**: at `q = 1` the quantum integer is the ordinary integer. -/
@[simp] theorem qNat_at_one (n : ℕ) : qNat (1 : R) n = n := by
  simp [qNat]

/-- **Additive law** (q-analog of `m + n`):
`[m + n]_q = [m]_q + q^m · [n]_q`. -/
theorem qNat_add (q : R) (m n : ℕ) :
    qNat q (m + n) = qNat q m + q ^ m * qNat q n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hidx : m + (n + 1) = (m + n) + 1 := by ring
    rw [hidx, qNat_succ, ih, qNat_succ, mul_add, pow_add]
    ring

/-- **Multiplicative law** (q-analog of `m · n`):
`[m · n]_q = [m]_{q^n} · [n]_q`.  Note the base change `q ↦ q^n` in the
first factor — the hallmark of the q-deformation. -/
theorem qNat_mul (q : R) (m n : ℕ) :
    qNat q (m * n) = qNat (q ^ n) m * qNat q n := by
  induction m with
  | zero => simp
  | succ m ih =>
    -- (m+1)·n = m·n + n, split with the additive law, then reassemble.
    rw [Nat.succ_mul, qNat_add, ih, qNat_succ, add_mul]
    have hpow : (q ^ n) ^ m = q ^ (m * n) := by rw [← pow_mul, Nat.mul_comm]
    rw [hpow]

end QuantumInteger

namespace QuantumInteger

variable {K : Type*} [Field K]

/-- **Field closed form**: for `q ≠ 1`,
`[n]_q = (q^n - 1)/(q - 1)`. -/
theorem qNat_eq_div {q : K} (hq : q ≠ 1) (n : ℕ) :
    qNat q n = (q ^ n - 1) / (q - 1) := by
  simpa [qNat] using geom_sum_eq hq n

end QuantumInteger
