import Mathlib

/-
# General Lucas sequences are divisibility sequences: `m ∣ n → U_m ∣ U_n`

The parent entry `fibonacci-identities-oq-02` shows the Fibonacci numbers form a
*strong divisibility sequence*: `fib m ∣ fib n ↔ m ∣ n` (for `3 ≤ m`), leaning on
Mathlib's `Nat.fib_gcd` / `Nat.fib_dvd`.  A sibling (`oq-02-oq-01`) shows the
*companion* Lucas numbers `Lₙ` are **not** a divisibility sequence.

This entry answers the open question:

> *Does the divisibility characterization extend to a general Lucas sequence of
> the first kind `Uₙ(P, Q)`?*

We introduce, from scratch, the first-kind Lucas sequence over `ℤ`

  `U₀ = 0,  U₁ = 1,  U_{n+2} = P · U_{n+1} − Q · Uₙ`,

so that `Uₙ(1, −1) = fib n`, and prove the **forward divisibility direction for
every choice of parameters**:

  **`m ∣ n → Uₙ(P, Q) is divisible by Uₘ(P, Q)`   (all `P Q : ℤ`).**

This is the genuinely general statement: unlike the full `↔`, the divisibility
direction needs *no* coprimality or growth hypothesis on `(P, Q)` — it is a
purely formal consequence of the index-addition law

  `U_{m+n+1} = U_{m+1} · U_{n+1} − Q · Uₘ · Uₙ`.

Mathlib records this only for `fib` (`Nat.fib_dvd`); here it is derived for the
whole two-parameter family, and the Fibonacci case is recovered as a corollary
*without* invoking `Nat.fib_dvd`, giving an independent proof.

### Scope and honesty

Only the forward direction (`m ∣ n → Uₘ ∣ Uₙ`) is universal.  The converse
(`Uₘ ∣ Uₙ → m ∣ n`) genuinely requires extra hypotheses: `gcd(P, Q) = 1` for the
strong-divisibility law `gcd(Uₘ, Uₙ) = U_{gcd(m,n)}`, plus a monotonicity/growth
condition to invert `U` — witness the companion Lucas numbers of `oq-02-oq-01`,
which fail it.  The converse is left as recorded future work; nothing here claims
it.

No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ02OQ02

/-- The **first-kind Lucas sequence** `Uₙ(P, Q)` over `ℤ`:
`U₀ = 0`, `U₁ = 1`, `U_{n+2} = P · U_{n+1} − Q · Uₙ`.
For `(P, Q) = (1, −1)` this is the Fibonacci sequence. -/
def lucasU (P Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => P * lucasU P Q (n + 1) - Q * lucasU P Q n

@[simp] theorem lucasU_zero (P Q : ℤ) : lucasU P Q 0 = 0 := rfl

@[simp] theorem lucasU_one (P Q : ℤ) : lucasU P Q 1 = 1 := rfl

/-- The defining recurrence, as a rewrite lemma. -/
theorem lucasU_add_two (P Q : ℤ) (n : ℕ) :
    lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := rfl

@[simp] theorem lucasU_two (P Q : ℤ) : lucasU P Q 2 = P := by
  rw [lucasU_add_two]; simp

/-- **Index-addition law.** `U_{m+n+1} = U_{m+1} · U_{n+1} − Q · Uₘ · Uₙ`.

Proved by a single induction on `n` carrying the statement for both `n` and
`n+1` (the sequence is second-order, so two consecutive instances are needed to
push the recurrence one step). -/
theorem lucasU_add (P Q : ℤ) (m n : ℕ) :
    lucasU P Q (m + n + 1)
      = lucasU P Q (m + 1) * lucasU P Q (n + 1) - Q * lucasU P Q m * lucasU P Q n := by
  suffices h : ∀ n,
      (lucasU P Q (m + n + 1)
          = lucasU P Q (m + 1) * lucasU P Q (n + 1) - Q * lucasU P Q m * lucasU P Q n) ∧
      (lucasU P Q (m + (n + 1) + 1)
          = lucasU P Q (m + 1) * lucasU P Q (n + 2) - Q * lucasU P Q m * lucasU P Q (n + 1))
    from (h n).1
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- `U (m+1) = U (m+1) * U 1 - Q * U m * U 0`
      simp
    · -- `U (m+2) = U (m+1) * U 2 - Q * U m * U 1`
      rw [show m + (0 + 1) + 1 = m + 2 by omega, lucasU_add_two,
        show (0 : ℕ) + 2 = 2 by rfl, show (0 : ℕ) + 1 = 1 by rfl,
        lucasU_two, lucasU_one]
      ring
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨ih2, ?_⟩
    -- Goal `A (n+2)`: `U (m+(n+2)+1) = U (m+1) * U (n+3) - Q * U m * U (n+2)`.
    -- Rewrite the index `m+(n+2)+1 = (m+n+1)+2` and unfold the recurrence.
    rw [show m + (n + 1 + 1) + 1 = (m + n + 1) + 2 by omega, lucasU_add_two]
    -- Now LHS = P * U (m+n+2) - Q * U (m+n+1).
    -- Note `m+n+1+1 = m+(n+1)+1`, so `U (m+n+2)` is the head of `ih2`.
    rw [show m + n + 1 + 1 = m + (n + 1) + 1 by omega, ih2, ih1]
    -- Reduce `U (n+3)` and `U (n+2)` to the recurrence in terms of `U (n+1), U n`.
    have hU3 : lucasU P Q (n + 1 + 2) = P * lucasU P Q (n + 2) - Q * lucasU P Q (n + 1) := by
      rw [lucasU_add_two]
    have hU2 : lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n := by
      rw [lucasU_add_two]
    rw [show n + 1 + 1 = n + 2 by omega, hU3, hU2]
    ring

/-- **Self-divisibility along multiples.** `Uₘ ∣ U_{k·m}` for all `k`.
Induction on `k` using the index-addition law to split `U_{(k+1)m}`. -/
theorem lucasU_dvd_mul (P Q : ℤ) (m k : ℕ) :
    lucasU P Q m ∣ lucasU P Q (k * m) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · -- Write `m = m' + 1`.
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      -- `(k+1)*(m'+1) = (k*(m'+1)) + m' + 1`, matching the `U_{a+b+1}` shape with
      -- `a = k*(m'+1)`, `b = m'`.
      have eidx : (k + 1) * (m' + 1) = (k * (m' + 1)) + m' + 1 := by ring
      rw [eidx, lucasU_add]
      -- `U (k*(m'+1)+1) * U (m'+1) - Q * U (k*(m'+1)) * U m'`.
      -- First summand divisible by `U (m'+1)` (explicit factor); second because
      -- `U (m'+1) ∣ U (k*(m'+1))` by the induction hypothesis.
      apply dvd_sub
      · exact Dvd.intro_left _ rfl
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left ih _) _

/-- **Forward divisibility for every Lucas sequence of the first kind.**
`m ∣ n → Uₘ(P,Q) ∣ Uₙ(P,Q)` for all `P Q : ℤ`. -/
theorem lucasU_dvd_of_dvd (P Q : ℤ) {m n : ℕ} (h : m ∣ n) :
    lucasU P Q m ∣ lucasU P Q n := by
  obtain ⟨k, rfl⟩ := h
  rw [mul_comm m k]
  exact lucasU_dvd_mul P Q m k

/-! ### Fibonacci is the case `(P, Q) = (1, −1)`

We identify `lucasU 1 (-1)` with `Nat.fib`, then recover the parent's
`fib m ∣ fib n` corollary as a specialization — an independent proof that does
not call `Nat.fib_dvd`. -/

/-- `Uₙ(1, −1) = fib n`. -/
theorem lucasU_fib (n : ℕ) : lucasU 1 (-1) n = (Nat.fib n : ℤ) := by
  suffices h : ∀ n, lucasU 1 (-1) n = (Nat.fib n : ℤ) ∧
      lucasU 1 (-1) (n + 1) = (Nat.fib (n + 1) : ℤ) from (h n).1
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨ih1, ?_⟩
    rw [lucasU_add_two, ih0, ih1, Nat.fib_add_two]
    push_cast
    ring

/-- Fibonacci divisibility recovered from the general theorem, independently of
`Nat.fib_dvd`: `m ∣ n → fib m ∣ fib n`. -/
theorem fib_dvd_of_dvd {m n : ℕ} (h : m ∣ n) : Nat.fib m ∣ Nat.fib n := by
  have hz : lucasU 1 (-1) m ∣ lucasU 1 (-1) n := lucasU_dvd_of_dvd 1 (-1) h
  rw [lucasU_fib, lucasU_fib] at hz
  exact_mod_cast hz

end FibonacciIdentitiesOQ02OQ02
