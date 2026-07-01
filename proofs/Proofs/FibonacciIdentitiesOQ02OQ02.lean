import Mathlib.Tactic

/-
# Lucas sequences are divisibility sequences: `m ∣ n → Uₘ ∣ Uₙ`

## Open Question (gallery gap)

The parent entry `fibonacci-identities-oq-02` records the Fibonacci **strong
divisibility** law and its consequence, the divisibility characterization

  `for 3 ≤ m,  fib m ∣ fib n ↔ m ∣ n`      (Fibonacci, `(P,Q) = (1,−1)`).

The natural open question is whether this extends to the **general** fundamental
Lucas sequence `Uₙ(P,Q)` (the two-parameter family with `U₀ = 0`, `U₁ = 1`,
`Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`, whose `(1,−1)` instance is Fibonacci).

## What is (and is not) true

The *forward* biconditional `Uₘ ∣ Uₙ ↔ m ∣ n` does **NOT** hold for every `(P,Q)`:
it needs non-degeneracy hypotheses that pin down when `|Uₘ| = 1` or when the sequence
fails to grow.  For example at `(P,Q) = (3,2)` one has `Uₙ = 2ⁿ − 1`, so `U₂ = 3`
divides `U₄ = 15` **and** `2 ∣ 4` — fine — but the growth/monotonicity argument the
Fibonacci proof uses (`Nat.fib_lt_fib`) has no unconditional analogue over `ℤ`
(values can be negative, can repeat, or can hit `±1` at several indices when
`gcd(P,Q) ≠ 1`).  So the biconditional is genuinely conditional and is recorded here
as the sharp-boundary follow-up, not proved unconditionally.

The *robust, unconditional* half — the direction that makes `U` a **divisibility
sequence** — does hold for **all** integer parameters `P, Q`:

  **`m ∣ n → Uₘ(P,Q) ∣ Uₙ(P,Q)`.**                                            (★)

This is the exact general-parameter lift of Mathlib's `Nat.fib_dvd`, and it is the
content this entry contributes.  Everything is elementary and over `ℤ`; no Binet
closed form, no `√D`, no field extension.

## Proof architecture

1. `U_add` — the **addition formula** `Uₘ₊ₙ₊₁ = Uₘ₊₁·Uₙ₊₁ − Q·Uₘ·Uₙ`, proved by a
   two-step induction on `n` packaged as a consecutive pair (the recurrence couples
   `n`, `n+1`, `n+2`, exactly as in the parent file's `V_eq`).

2. `U_dvd_U_of_dvd` — **(★)**.  Writing `n = m·k`, induct on `k`.  The addition
   formula splits `U_{m·(k+1)} = U_{m·k + m}` into `U_{m·k+1}·Uₘ − Q·U_{m·k}·U_{m−1}`;
   the first summand carries a visible factor `Uₘ`, the second carries `U_{m·k}`, which
   is divisible by `Uₘ` by the induction hypothesis.

## Results

* `U`                   — the fundamental Lucas sequence over `ℤ`, parameters `P, Q`.
* `U_add`               — addition formula `Uₘ₊ₙ₊₁ = Uₘ₊₁·Uₙ₊₁ − Q·Uₘ·Uₙ`.
* `U_dvd_U_of_dvd`      — **(★)** `m ∣ n → Uₘ ∣ Uₙ` (the divisibility-sequence law).
* `fib_dvd_instance`    — `(★)` at `(1,−1)`, the Fibonacci case.
* `pell_dvd_instance`   — `(★)` at `(2,−1)`, the Pell case.
* `mersenne_dvd_instance` — `(★)` at `(3,2)`, where `Uₙ = 2ⁿ − 1`.

## Axioms: 0 | Sorries: 0
-/

namespace FibonacciIdentitiesOQ02OQ02

/-- The **fundamental Lucas sequence** `Uₙ(P,Q)`: `U₀ = 0`, `U₁ = 1`,
`Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`.  For `(P,Q) = (1,−1)` this is the Fibonacci sequence. -/
def U (P Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => P * U P Q (n + 1) - Q * U P Q n

@[simp] theorem U_zero (P Q : ℤ) : U P Q 0 = 0 := rfl
@[simp] theorem U_one (P Q : ℤ) : U P Q 1 = 1 := rfl

/-- The defining recurrence `Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`. -/
theorem U_add_two (P Q : ℤ) (n : ℕ) :
    U P Q (n + 2) = P * U P Q (n + 1) - Q * U P Q n := rfl

/-- Value at index `2`: `U₂ = P`. -/
theorem U_two (P Q : ℤ) : U P Q 2 = P := by rw [U_add_two]; simp

/-- **Addition formula.** `Uₘ₊ₙ₊₁ = Uₘ₊₁·Uₙ₊₁ − Q·Uₘ·Uₙ`.

Two-step induction on `n`, strengthened to the conjunction of the statement at `n` and
at `n+1` so ordinary induction feeds the coupled recurrence
`Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`. -/
theorem U_add (P Q : ℤ) (m n : ℕ) :
    U P Q (m + n + 1) = U P Q (m + 1) * U P Q (n + 1) - Q * U P Q m * U P Q n := by
  suffices key : ∀ k : ℕ,
      (U P Q (m + k + 1) = U P Q (m + 1) * U P Q (k + 1) - Q * U P Q m * U P Q k) ∧
      (U P Q (m + (k + 1) + 1)
        = U P Q (m + 1) * U P Q (k + 1 + 1) - Q * U P Q m * U P Q (k + 1)) from (key n).1
  intro k
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp
    · -- `U_{m+2} = P·U_{m+1} − Q·U_m` versus `U_{m+1}·U₂ − Q·U_m·U₁`.
      have h1 : m + (0 + 1) + 1 = m + 2 := by omega
      rw [h1, U_add_two, U_two]; simp; ring
  | succ j ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨ih2, ?_⟩
    -- Second component of the pair at `j+1`: expand the top index by the recurrence.
    have idxL : m + (j + 1 + 1) + 1 = m + j + 1 + 2 := by omega
    have idxA : m + (j + 1) + 1 = m + j + 1 + 1 := by omega
    have hrec : U P Q (m + j + 1 + 2)
        = P * U P Q (m + j + 1 + 1) - Q * U P Q (m + j + 1) := U_add_two P Q (m + j + 1)
    have hUk2 : U P Q (j + 1 + 1 + 1) = P * U P Q (j + 1 + 1) - Q * U P Q (j + 1) :=
      U_add_two P Q (j + 1)
    have hUk1 : U P Q (j + 1 + 1) = P * U P Q (j + 1) - Q * U P Q j :=
      U_add_two P Q j
    rw [idxL, hrec, ← idxA, ih2, ih1, hUk2, hUk1]
    ring

/-- **(★) Divisibility-sequence law.** `m ∣ n → Uₘ ∣ Uₙ`, for every `(P,Q)`.

The general-parameter lift of `Nat.fib_dvd`.  Write `n = m·k`; induct on `k`, splitting
`U_{m·k+m}` by the addition formula into a term with a visible factor `Uₘ` plus a term
divisible by `Uₘ` through the induction hypothesis. -/
theorem U_dvd_U_of_dvd (P Q : ℤ) {m n : ℕ} (h : m ∣ n) : U P Q m ∣ U P Q n := by
  obtain ⟨k, rfl⟩ := h
  induction k with
  | zero => simp
  | succ j ih =>
    -- `m·(j+1) = m·j + m`.  Two cases on whether `m = 0`.
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; simp
    · -- `m = (m-1) + 1`; apply the addition formula with `a = m·j`, `b = m-1`.
      obtain ⟨p, rfl⟩ : ∃ p, m = p + 1 := ⟨m - 1, by omega⟩
      have idx : (p + 1) * (j + 1) = (p + 1) * j + p + 1 := by ring
      rw [idx]
      -- `U_{(p+1)·j + p + 1} = U_{(p+1)·j + 1}·U_{p+1} − Q·U_{(p+1)·j}·U_p`.
      have hadd := U_add P Q ((p + 1) * j) p
      rw [hadd]
      -- first summand: factor `U_{p+1}`; second: `U_{(p+1)·j}` divisible by `U_{p+1}` (ih).
      exact dvd_sub (Dvd.intro_left _ rfl) (Dvd.dvd.mul_right (ih.mul_left _) _)

/-- `(★)` at `(P,Q) = (1,−1)`: the Fibonacci case (`Uₙ = fib n`), matching `Nat.fib_dvd`. -/
theorem fib_dvd_instance {m n : ℕ} (h : m ∣ n) : U 1 (-1) m ∣ U 1 (-1) n :=
  U_dvd_U_of_dvd 1 (-1) h

/-- `(★)` at `(P,Q) = (2,−1)`: the Pell case. -/
theorem pell_dvd_instance {m n : ℕ} (h : m ∣ n) : U 2 (-1) m ∣ U 2 (-1) n :=
  U_dvd_U_of_dvd 2 (-1) h

/-- `(★)` at `(P,Q) = (3,2)`, where `Uₙ = 2ⁿ − 1`: recovers `(2ᵐ−1) ∣ (2ⁿ−1)` when
`m ∣ n`. -/
theorem mersenne_dvd_instance {m n : ℕ} (h : m ∣ n) : U 3 2 m ∣ U 3 2 n :=
  U_dvd_U_of_dvd 3 2 h

end FibonacciIdentitiesOQ02OQ02
