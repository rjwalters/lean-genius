import Mathlib

/-
# The Fibonacci numbers form a strong divisibility sequence

The Fibonacci sequence enjoys the remarkable *strong divisibility* property

  `fib (gcd m n) = gcd (fib m) (fib n)`,

i.e. the index-gcd commutes with the value-gcd.  Mathlib records this as
`Nat.fib_gcd` (Data/Nat/Fib/Basic.lean), together with the one-directional
divisibility corollary `Nat.fib_dvd : m ∣ n → fib m ∣ fib n`.

This entry packages the strong-divisibility law and draws out two consequences
that Mathlib does **not** state directly:

* **Coprimality transfer** — coprime indices give coprime Fibonacci values:
  `Nat.Coprime m n → Nat.Coprime (fib m) (fib n)`.  Immediate from the gcd law
  since `fib 1 = 1`.

* **The full divisibility characterization** — for `3 ≤ m`,
  `fib m ∣ fib n ↔ m ∣ n`.  Mathlib only has the `←` direction (`Nat.fib_dvd`);
  the forward direction is the genuinely new content here.  It says the Fibonacci
  numbers detect divisibility of indices *exactly* (away from the degenerate
  small indices `fib 1 = fib 2 = 1`).  The proof reduces `fib m ∣ fib n` to
  `fib (gcd m n) = fib m` via the strong-divisibility law, then uses strict
  monotonicity of `fib` on `Set.Ici 2` (`Nat.fib_lt_fib`) to conclude
  `gcd m n = m`, i.e. `m ∣ n`.

The hypothesis `3 ≤ m` is sharp: `fib 2 = 1` divides every `fib n`, yet `2 ∣ n`
fails for odd `n`, so the characterization genuinely needs `m ≥ 3`.

No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ02

/-- **Strong divisibility law** for the Fibonacci numbers:
`fib (gcd m n) = gcd (fib m) (fib n)`.  The headline of the family. -/
theorem fib_gcd (m n : ℕ) :
    Nat.fib (Nat.gcd m n) = Nat.gcd (Nat.fib m) (Nat.fib n) :=
  Nat.fib_gcd m n

/-- Divisibility of indices propagates to Fibonacci values:
`m ∣ n → fib m ∣ fib n`. -/
theorem fib_dvd_of_dvd {m n : ℕ} (h : m ∣ n) : Nat.fib m ∣ Nat.fib n :=
  Nat.fib_dvd m n h

/-- **Coprimality transfer**: coprime indices yield coprime Fibonacci values.
Immediate from the strong-divisibility law together with `fib 1 = 1`. -/
theorem fib_coprime_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    Nat.Coprime (Nat.fib m) (Nat.fib n) := by
  unfold Nat.Coprime at h ⊢
  rw [← Nat.fib_gcd, h, Nat.fib_one]

/-- **Full divisibility characterization** (new beyond Mathlib's one direction):
for `3 ≤ m`, `fib m ∣ fib n ↔ m ∣ n`.

The Fibonacci numbers detect index-divisibility exactly once we are past the
degenerate equal values `fib 1 = fib 2 = 1`. -/
theorem fib_dvd_iff {m n : ℕ} (hm : 3 ≤ m) :
    Nat.fib m ∣ Nat.fib n ↔ m ∣ n := by
  constructor
  · intro hdvd
    -- `fib m ∣ fib n` rephrases as `gcd (fib m) (fib n) = fib m`, which via the
    -- strong-divisibility law is `fib (gcd m n) = fib m`.
    have hg : Nat.fib (Nat.gcd m n) = Nat.fib m := by
      rw [Nat.fib_gcd]; exact Nat.gcd_eq_left hdvd
    -- `gcd m n` divides `m`, hence is at most `m`.
    have hdm : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
    have hle : Nat.gcd m n ≤ m := Nat.le_of_dvd (by omega) hdm
    -- `fib m ≥ fib 3 = 2` since `fib` is monotone and `3 ≤ m`.
    have hfm : 2 ≤ Nat.fib m := by
      have := Nat.fib_mono hm
      simpa using this
    -- Rule out the degenerate gcd values `0` and `1`: both force `fib (gcd) ≤ 1`,
    -- contradicting `fib (gcd m n) = fib m ≥ 2`.
    have hd2 : 2 ≤ Nat.gcd m n := by
      rcases Nat.lt_or_ge (Nat.gcd m n) 2 with h | h
      · exfalso
        have hfib_le : Nat.fib (Nat.gcd m n) ≤ 1 := by
          interval_cases (Nat.gcd m n) <;> decide
        omega
      · exact h
    -- Strict monotonicity of `fib` on `Ici 2` upgrades `fib (gcd) = fib m`,
    -- `gcd ≤ m` to `gcd = m`.
    have hgm : Nat.gcd m n = m := by
      rcases Nat.lt_or_ge (Nat.gcd m n) m with hlt | hge
      · have := (Nat.fib_lt_fib hd2).mpr hlt
        omega
      · omega
    exact (Nat.gcd_eq_left_iff_dvd).mp hgm
  · intro h
    exact Nat.fib_dvd m n h

/-- Worked instance of the strong-divisibility law:
`gcd 12 8 = 4`, and `fib 4 = 3 = gcd (fib 12) (fib 8) = gcd 144 21`. -/
example : Nat.fib (Nat.gcd 12 8) = Nat.gcd (Nat.fib 12) (Nat.fib 8) :=
  fib_gcd 12 8

/-- Concrete numerical check of the value gcd: `gcd (fib 12) (fib 8) = 3`. -/
example : Nat.gcd (Nat.fib 12) (Nat.fib 8) = 3 := by decide

/-- The characterization in action: `fib 3 = 2 ∣ fib n` exactly when `3 ∣ n`
(the "every third Fibonacci number is even" pattern). -/
example (n : ℕ) : Nat.fib 3 ∣ Nat.fib n ↔ 3 ∣ n :=
  fib_dvd_iff (le_refl 3)

end FibonacciIdentitiesOQ02
