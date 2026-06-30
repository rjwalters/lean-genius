/-
Pell's Equation OQ-06-OQ-07: The Pell Solutions Form a Divisibility Sequence

The negative-Pell lineage (`pell-equation-oq-06` and its children) has, so far,
described the solution chain of x² − 2y² = ±1 in several lights: its closed form as
the powers of the fundamental unit (`-oq-02`), its linear recurrence (`-oq-03`), its
role as best rational approximations of √2 (`-oq-04`), the Cassini constant
determinant of consecutive solutions (`-oq-05`), and the Brahmagupta composition law
behind all of them (`-oq-06`). Every one of those is a statement about the *analytic*
or *algebraic* shape of the chain. This entry records a purely *arithmetic* (number-
theoretic) structural fact that none of the siblings touch:

  **the second coordinates Yₙ of the positive-Pell chain form a divisibility
  sequence:  m ∣ n  ⟹  Yₘ ∣ Yₙ.**

Working with the norm `+1` form x² − 2y² = 1, write the fundamental unit
γ = 3 + 2√2 ∈ ℤ[√2] and set γⁿ = Xₙ + Yₙ√2, so

    (Xₙ) = 1, 3, 17, 99, 577, …        (Yₙ) = 0, 2, 12, 70, 408, …

The engine is the **addition formula**, which is free from `γ^(m+n) = γᵐ·γⁿ` and the
multiplication of ℤ[√2]:

    Y_{m+n} = Xₘ·Yₙ + Yₘ·Xₙ,     X_{m+n} = Xₘ·Xₙ + 2·Yₘ·Yₙ.

Taking n a multiple of m and inducting, every term Y_{k·m} is a ℤ-combination whose
both summands carry a factor of Yₘ, giving Yₘ ∣ Y_{k·m}; the general divisibility
sequence property follows. This is the Pell analogue of the classical theorem that the
Fibonacci (and, more generally, every nondegenerate Lucas) sequence is a divisibility
sequence — and, like there, it is *not* a triviality of the closed form but a
consequence of the addition law.

Main results:
  • `X_add`, `Y_add`        — the addition formulas (multiplication in ℤ[√2]).
  • `X_succ`, `Y_succ`      — the step recurrence (the parent automorphism 3+2√2).
  • `pell`                  — every term solves Xₙ² − 2·Yₙ² = 1 (the norm `+1` form).
  • `isCoprime_X_Y`         — Xₙ and Yₙ are coprime (immediate from the Pell relation).
  • `Y_dvd_mul`             — Yₘ ∣ Y_{k·m} (the inductive core).
  • `Y_dvd_of_dvd`          — **m ∣ n ⟹ Yₘ ∣ Yₙ** (the divisibility sequence).
  • `two_dvd_Y`             — every Pell Yₙ is even (the `m = 1` corollary, Y₁ = 2).

All proofs are `sorry`-free and axiom-free (no `native_decide`).

The *strong* form gcd(Yₘ, Yₙ) = Y_{gcd(m,n)} (a strong divisibility sequence) is the
natural next step; it needs the coprimality `isCoprime_X_Y` proved here together with a
Euclidean (`Nat.gcd.induction`) wrap and is left as future work.

References:
- Parent: `pell-equation-oq-06`; siblings `-oq-02` (powers of ζ), `-oq-06` (Brahmagupta).
- The Fibonacci/Lucas divisibility-sequence theorem (classical; e.g. Lucas 1878).
- Mathlib `Mathlib/NumberTheory/Zsqrtd/Basic.lean` (`Zsqrtd`, `Zsqrtd.re_mul`,
  `Zsqrtd.im_mul`, `Zsqrtd.norm_def`, `Zsqrtd.norm_mul`).
-/

import Mathlib

namespace PellEquationOQ06OQ07

/-
## The positive-Pell chain as powers of the fundamental unit
-/

/-- The fundamental unit `3 + 2√2` of ℤ[√2] (of norm `+1`), generator of the
    positive-Pell solution chain. -/
def γ : ℤ√2 := ⟨3, 2⟩

/-- `Xₙ`: the first coordinate of `γⁿ = Xₙ + Yₙ√2`. -/
def X (n : ℕ) : ℤ := (γ ^ n).re

/-- `Yₙ`: the second coordinate of `γⁿ` (the "Pell number"). -/
def Y (n : ℕ) : ℤ := (γ ^ n).im

@[simp] theorem X_zero : X 0 = 1 := by decide
@[simp] theorem Y_zero : Y 0 = 0 := by decide
@[simp] theorem X_one : X 1 = 3 := by decide
@[simp] theorem Y_one : Y 1 = 2 := by decide

/-
## The norm and the Pell relation
-/

/-- `N(γ) = 3² − 2·2² = 1`: the generator has norm `+1`. -/
theorem norm_γ : γ.norm = 1 := by decide

/-- Multiplicativity of the ℤ[√d]-norm across powers, `N(zᵏ) = N(z)ᵏ`
    (a direct induction off `Zsqrtd.norm_mul`). -/
theorem norm_pow {d : ℤ} (z : ℤ√d) : ∀ k : ℕ, (z ^ k).norm = z.norm ^ k
  | 0 => by simp
  | (k + 1) => by rw [pow_succ, Zsqrtd.norm_mul, norm_pow z k, pow_succ]

/-- Each power keeps norm `1`: `N(γⁿ) = 1`. -/
theorem norm_γ_pow (n : ℕ) : (γ ^ n).norm = 1 := by
  rw [norm_pow, norm_γ, one_pow]

/-- **The Pell relation.** Every term of the chain solves `x² − 2y² = 1`. -/
theorem pell (n : ℕ) : (X n) ^ 2 - 2 * (Y n) ^ 2 = 1 := by
  have h := norm_γ_pow n
  rw [Zsqrtd.norm_def] at h
  simp only [X, Y]
  linear_combination h

/-
## The addition formulas (multiplication in ℤ[√2])
-/

/-- **Addition formula, first coordinate:** `X_{m+n} = Xₘ·Xₙ + 2·Yₘ·Yₙ`.
    This is `(γᵐ·γⁿ).re` read through `Zsqrtd.re_mul`. -/
theorem X_add (m n : ℕ) : X (m + n) = X m * X n + 2 * Y m * Y n := by
  simp only [X, Y, pow_add, Zsqrtd.re_mul]

/-- **Addition formula, second coordinate:** `Y_{m+n} = Xₘ·Yₙ + Yₘ·Xₙ`.
    This is `(γᵐ·γⁿ).im` read through `Zsqrtd.im_mul` — the engine of the
    divisibility sequence. -/
theorem Y_add (m n : ℕ) : Y (m + n) = X m * Y n + Y m * X n := by
  simp only [X, Y, pow_add, Zsqrtd.im_mul]

/-- The step recurrence on the first coordinate: `X_{n+1} = 3·Xₙ + 4·Yₙ`
    (the parent's form automorphism induced by `3 + 2√2`). -/
theorem X_succ (n : ℕ) : X (n + 1) = 3 * X n + 4 * Y n := by
  rw [X_add, X_one, Y_one]; ring

/-- The step recurrence on the second coordinate: `Y_{n+1} = 2·Xₙ + 3·Yₙ`. -/
theorem Y_succ (n : ℕ) : Y (n + 1) = 2 * X n + 3 * Y n := by
  rw [Y_add, X_one, Y_one]; ring

/-- The chain is genuine: `Xₙ ≥ 1` and `Yₙ ≥ 0` for every `n`. -/
theorem one_le_X_and_zero_le_Y : ∀ n, 1 ≤ X n ∧ 0 ≤ Y n
  | 0 => by decide
  | (n + 1) => by
    obtain ⟨hx, hy⟩ := one_le_X_and_zero_le_Y n
    rw [X_succ, Y_succ]
    exact ⟨by linarith, by linarith⟩

/-
## Coprimality
-/

/-- **`Xₙ` and `Yₙ` are coprime.** Immediate from the Pell relation
    `Xₙ·Xₙ + (−2·Yₙ)·Yₙ = 1`, a Bézout certificate. -/
theorem isCoprime_X_Y (n : ℕ) : IsCoprime (X n) (Y n) :=
  ⟨X n, -2 * Y n, by have h := pell n; linear_combination h⟩

/-
## The divisibility sequence
-/

/-- **Inductive core:** `Yₘ ∣ Y_{k·m}` for every `k`. Each step uses the addition
    formula `Y_{j·m + m} = X_{j·m}·Yₘ + Y_{j·m}·Xₘ`: the first summand carries `Yₘ`
    directly, the second carries it through the inductive hypothesis. -/
theorem Y_dvd_mul (m : ℕ) : ∀ k, Y m ∣ Y (k * m)
  | 0 => by simp
  | (k + 1) => by
    have hk := Y_dvd_mul m k
    rw [show (k + 1) * m = k * m + m from by ring, Y_add]
    exact dvd_add (dvd_mul_left (Y m) (X (k * m))) (hk.mul_right (X m))

/-- **The Pell `Y`-sequence is a divisibility sequence:** `m ∣ n ⟹ Yₘ ∣ Yₙ`. -/
theorem Y_dvd_of_dvd {m n : ℕ} (h : m ∣ n) : Y m ∣ Y n := by
  obtain ⟨k, rfl⟩ := h
  rw [mul_comm m k]
  exact Y_dvd_mul m k

/-- **Every Pell `Yₙ` is even.** The `m = 1` case, since `Y₁ = 2` and `1 ∣ n`. -/
theorem two_dvd_Y (n : ℕ) : (2 : ℤ) ∣ Y n := by
  have h : Y 1 ∣ Y n := Y_dvd_of_dvd (one_dvd n)
  rwa [Y_one] at h

/-
## Sanity checks
-/

example : X 2 = 17 ∧ Y 2 = 12 := by decide
example : X 3 = 99 ∧ Y 3 = 70 := by decide
example : Y 2 ∣ Y 6 := Y_dvd_of_dvd ⟨3, rfl⟩
example : Y 3 ∣ Y 9 := Y_dvd_of_dvd ⟨3, rfl⟩

end PellEquationOQ06OQ07
