/-
  Fibonacci Divisibility Characterization: Fₘ ∣ Fₙ ⟺ m ∣ n  (for m ≥ 3)

  The Fibonacci numbers form a *strong divisibility sequence*:
  `gcd(Fₘ, Fₙ) = F_{gcd(m,n)}` (Mathlib's `Nat.fib_gcd`). A classical corollary
  is the full divisibility characterisation

      Fₘ ∣ Fₙ  ⟺  m ∣ n.

  Mathlib provides only the **forward** implication `Nat.fib_dvd : m ∣ n → Fₘ ∣ Fₙ`.
  This entry proves the **reverse** implication — the substantive half — and
  packages the biconditional.

  A subtlety fixes the exact hypothesis: because `F₁ = F₂ = 1` divides every
  Fibonacci number, the equivalence can only hold for `m ≥ 3` (equivalently
  `Fₘ ≥ 2`). We prove necessity of that hypothesis with an explicit witness.

  Key results:
  - `dvd_of_fib_dvd`: for `3 ≤ m`, `Fₘ ∣ Fₙ → m ∣ n` (the reverse direction).
  - `fib_dvd_iff`: the characterisation `Fₘ ∣ Fₙ ↔ m ∣ n` for `3 ≤ m`.
  - `fib_dvd_iff_needs_three`: the `m ≥ 3` hypothesis is necessary.
  - `not_fib_dvd_of_not_dvd`: contrapositive convenience form.

  Édouard Lucas (1878)
-/
import Mathlib

namespace FibonacciIdentitiesOQ07

/-- **Reverse divisibility** (the new content). For `3 ≤ m`, if `Fₘ ∣ Fₙ` then
    `m ∣ n`.

    Proof. `Fₘ ∣ Fₙ` gives `gcd(Fₘ, Fₙ) = Fₘ`, and Mathlib's strong-divisibility
    identity `Nat.fib_gcd` rewrites the left side as `F_{gcd(m,n)}`, so
    `F_{gcd(m,n)} = Fₘ`. Since `m ≥ 3` we have `Fₘ ≥ F₃ = 2`, which forces
    `gcd(m,n) ≥ 2` (otherwise `F_{gcd(m,n)} ∈ {F₀, F₁} = {0, 1} < 2`). Fibonacci
    is strictly monotone — hence injective — on `[2, ∞)` (`Nat.fib_strictMonoOn`),
    so `F_{gcd(m,n)} = Fₘ` yields `gcd(m,n) = m`, i.e. `m ∣ n`. -/
theorem dvd_of_fib_dvd {m n : ℕ} (hm : 3 ≤ m) (h : Nat.fib m ∣ Nat.fib n) :
    m ∣ n := by
  -- `F_{gcd(m,n)} = Fₘ`.
  have hgcd : Nat.fib (Nat.gcd m n) = Nat.fib m := by
    rw [Nat.fib_gcd]; exact Nat.gcd_eq_left h
  -- `Fₘ ≥ F₃ = 2`.
  have hfm2 : 2 ≤ Nat.fib m :=
    calc 2 = Nat.fib 3 := by decide
      _ ≤ Nat.fib m := Nat.fib_mono hm
  -- Hence `gcd(m,n) ≥ 2`.
  have hg2 : 2 ≤ Nat.gcd m n := by
    by_contra hlt
    push_neg at hlt
    have hle1 : Nat.fib (Nat.gcd m n) ≤ 1 := by
      interval_cases (Nat.gcd m n) <;> decide
    omega
  -- Injectivity of `fib` on `[2, ∞)` gives `gcd(m,n) = m`.
  have hmgcd : Nat.gcd m n = m :=
    Nat.fib_strictMonoOn.injOn (Set.mem_Ici.mpr hg2)
      (Set.mem_Ici.mpr (le_trans (by norm_num) hm)) hgcd
  exact hmgcd ▸ Nat.gcd_dvd_right m n

/-- **Fibonacci divisibility characterisation.** For `3 ≤ m`,

        Fₘ ∣ Fₙ  ↔  m ∣ n.

    The forward direction is Mathlib's `Nat.fib_dvd`; the reverse is
    `dvd_of_fib_dvd`. -/
theorem fib_dvd_iff {m n : ℕ} (hm : 3 ≤ m) : Nat.fib m ∣ Nat.fib n ↔ m ∣ n :=
  ⟨dvd_of_fib_dvd hm, fun h => Nat.fib_dvd m n h⟩

/-- **Necessity of `m ≥ 3`.** The characterisation fails for `m = 2`: since
    `F₂ = 1` divides every Fibonacci number, `F₂ ∣ F₃` holds while `2 ∤ 3`.
    (The same obstruction rules out `m = 1`, as `F₁ = 1`.) -/
theorem fib_dvd_iff_needs_three : Nat.fib 2 ∣ Nat.fib 3 ∧ ¬ (2 ∣ 3) := by decide

/-- Contrapositive convenience form: for `3 ≤ m`, if `m ∤ n` then `Fₘ ∤ Fₙ`. -/
theorem not_fib_dvd_of_not_dvd {m n : ℕ} (hm : 3 ≤ m) (h : ¬ m ∣ n) :
    ¬ Nat.fib m ∣ Nat.fib n :=
  fun hd => h ((fib_dvd_iff hm).mp hd)

end FibonacciIdentitiesOQ07
