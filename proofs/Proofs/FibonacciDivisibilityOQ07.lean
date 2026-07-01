import Mathlib

/-
# Fibonacci Divisibility Characterization: `Fₘ ∣ Fₙ ↔ m ∣ n`, with the sharp exception at m = 2

Mathlib records the *forward* half of the classical divisibility property of the
Fibonacci sequence — `Nat.fib_dvd : m ∣ n → fib m ∣ fib n` — together with the
strong-divisibility identity `Nat.fib_gcd : fib (gcd m n) = gcd (fib m) (fib n)`.
It does **not** record the converse, nor the full biconditional.

This file supplies the converse and packages the complete characterization.  The
subtlety that makes the naive biconditional *false* is the coincidence
`F₁ = F₂ = 1`: since `fib 2 = 1` divides every Fibonacci number, `fib 2 ∣ fib n`
holds for all `n`, yet `2 ∣ n` does not.  Index `m = 2` is therefore the *unique*
exception, and the sharp statement is

  `(∀ n, fib m ∣ fib n ↔ m ∣ n) ↔ m ≠ 2`.

The converse `fib m ∣ fib n → m ∣ n` for `m ≥ 3` runs through `fib_gcd`: the
hypothesis forces `fib (gcd m n) = fib m`, and strict monotonicity of `fib` on
`[2, ∞)` upgrades this to `gcd m n = m`, i.e. `m ∣ n`.

Fully verified: 0 sorries, 0 axioms, no `native_decide`.  `decide` appears only
to evaluate the closed numerals `fib 2 = 1`, `fib 3 = 2`, `fib 4 = 3` and the
ground fact `¬ (2 ∣ 1)` — these reduce in the kernel (`fib_zero/one/two` are
`rfl`) and introduce no `Lean.ofReduceBool`.
-/

namespace FibonacciDivisibilityOQ07

open Nat

/-- **Converse of `Nat.fib_dvd` for indices `m ≥ 3`.**  If `fib m ∣ fib n` then
`m ∣ n`.

Proof: by `Nat.fib_gcd`, `fib m ∣ fib n` gives `fib (gcd m n) = fib m`.  Since
`m ≥ 3` we have `fib m ≥ fib 3 = 2`, so `gcd m n` can be neither `0` (where
`fib = 0`) nor `1` (where `fib = 1`); hence `gcd m n ≥ 2`.  Strict monotonicity of
`fib` on `[2, ∞)` is injective there, so `fib (gcd m n) = fib m` forces
`gcd m n = m`, and `gcd m n ∣ n` finishes. -/
theorem dvd_of_fib_dvd_fib {m n : ℕ} (hm : 3 ≤ m) (h : fib m ∣ fib n) : m ∣ n := by
  -- `fib` of the gcd collapses to `fib m` because `fib m ∣ fib n`.
  have hg : fib (Nat.gcd m n) = fib m := by
    rw [Nat.fib_gcd]; exact Nat.gcd_eq_left h
  -- `fib m ≥ 2` from monotonicity and `fib 3 = 2`.
  have hfm : 2 ≤ fib m := by
    have h3 : fib 3 = 2 := by decide
    have : fib 3 ≤ fib m := fib_mono hm
    omega
  -- The gcd is neither 0 nor 1, hence `≥ 2`.
  have hne0 : Nat.gcd m n ≠ 0 := by
    intro h0; rw [h0, Nat.fib_zero] at hg; omega
  have hne1 : Nat.gcd m n ≠ 1 := by
    intro h1; rw [h1, Nat.fib_one] at hg; omega
  have h2 : 2 ≤ Nat.gcd m n := by omega
  -- Injectivity of `fib` on `[2, ∞)` turns `fib (gcd m n) = fib m` into equality.
  have heq : Nat.gcd m n = m :=
    fib_strictMonoOn.injOn (Set.mem_Ici.mpr h2) (Set.mem_Ici.mpr (by omega : (2 : ℕ) ≤ m)) hg
  rw [← heq]; exact Nat.gcd_dvd_right m n

/-- **Divisibility characterization for `m ≥ 3`:** `fib m ∣ fib n ↔ m ∣ n`.

The forward implication is Mathlib's `Nat.fib_dvd`; the converse is
`dvd_of_fib_dvd_fib`. -/
theorem fib_dvd_iff {m : ℕ} (hm : 3 ≤ m) (n : ℕ) : fib m ∣ fib n ↔ m ∣ n :=
  ⟨dvd_of_fib_dvd_fib hm, Nat.fib_dvd m n⟩

/-- **The sharp global characterization.**  For a fixed index `m`, the divisibility
biconditional `fib m ∣ fib n ↔ m ∣ n` holds for *every* `n` if and only if
`m ≠ 2`.

The exceptional index is exactly `m = 2`, because `fib 2 = 1` divides every
Fibonacci number while `2 ∣ n` fails for odd `n` (take `n = 1`).  The indices
`m = 0` (`fib 0 = 0`, so both sides say `n = 0`) and `m = 1` (`fib 1 = 1`, so both
sides are vacuously true) are *not* exceptions. -/
theorem fib_dvd_iff_forall (m : ℕ) : (∀ n, fib m ∣ fib n ↔ m ∣ n) ↔ m ≠ 2 := by
  constructor
  · -- If the biconditional held at `m = 2` for `n = 1` we would get `2 ∣ 1`.
    intro h hm2
    subst hm2
    have hd : fib 2 ∣ fib 1 := by decide
    have : (2 : ℕ) ∣ 1 := (h 1).mp hd
    omega
  · -- Conversely, `m ≠ 2` splits into `0`, `1`, and `≥ 3`, each handled above.
    intro hm n
    rcases m with _ | _ | _ | k
    · simp [zero_dvd_iff, Nat.fib_eq_zero]        -- m = 0 : `fib n = 0 ↔ n = 0`
    · simp                                         -- m = 1 : both sides always hold
    · exact absurd rfl hm                          -- m = 2 : excluded
    · exact fib_dvd_iff (by omega) n              -- m = k + 3

/-- **Corollary — parity of Fibonacci numbers.**  `fib n` is even iff `3 ∣ n`.
Immediate from `fib_dvd_iff` at `m = 3`, since `fib 3 = 2`. -/
theorem two_dvd_fib_iff (n : ℕ) : 2 ∣ fib n ↔ 3 ∣ n := by
  have h3 : Nat.fib 3 = 2 := by decide
  rw [← h3]; exact fib_dvd_iff (by norm_num) n

/-- **Corollary — divisibility by 3.**  `3 ∣ fib n` iff `4 ∣ n`, since `fib 4 = 3`. -/
theorem three_dvd_fib_iff (n : ℕ) : 3 ∣ fib n ↔ 4 ∣ n := by
  have h4 : Nat.fib 4 = 3 := by decide
  rw [← h4]; exact fib_dvd_iff (by norm_num) n

/-- **Sharpness witness.**  At the exceptional index `m = 2` the biconditional
fails concretely: `fib 2 ∣ fib 1` holds while `2 ∣ 1` does not. -/
theorem fib_two_exception : fib 2 ∣ fib 1 ∧ ¬ (2 ∣ 1) := by
  refine ⟨by decide, by decide⟩

end FibonacciDivisibilityOQ07
