import Mathlib
import Proofs.FibonacciIdentitiesOQ02OQ02

/-
# The companion Lucas sequence and the doubling law `U_{2n} = Uₙ · Vₙ`

The parent entry `fibonacci-identities-oq-02-oq-02` builds the first-kind Lucas
sequence `Uₙ(P, Q)` over `ℤ` (`U₀ = 0`, `U₁ = 1`, `U_{n+2} = P·U_{n+1} − Q·Uₙ`)
and proves the *forward divisibility* law `m ∣ n → Uₘ ∣ Uₙ`.  In particular
`Uₙ ∣ U_{2n}`, but that theorem gives no information about the cofactor.

This entry answers the open question:

> *What is the explicit cofactor of `Uₙ` in `U_{2n}`?  Is there a companion
> sequence `Vₙ` with `U_{2n} = Uₙ · Vₙ`?*

We introduce the **second-kind (companion) Lucas sequence** `Vₙ(P, Q)` over `ℤ`

  `V₀ = 2,  V₁ = P,  V_{n+2} = P · V_{n+1} − Q · Vₙ`,

which satisfies `Vₙ(1, −1) = Lₙ` (the Lucas numbers `2, 1, 3, 4, 7, …`), and
prove the two classical **doubling identities**

  **`U_{2n} = Uₙ · Vₙ`**        (even index),
  **`U_{2n+1} = U_{n+1}² − Q·Uₙ²`**  (odd index).

The even identity refines the parent's divisibility statement `Uₙ ∣ U_{2n}` by
naming the exact quotient `Vₙ`.  Both are derived from the parent's
index-addition law

  `U_{m+n+1} = U_{m+1}·U_{n+1} − Q·Uₘ·Uₙ`,

together with the bridge lemma `V_{n+1} = U_{n+2} − Q·Uₙ` expressing the
companion sequence inside the first-kind sequence.

As a corollary, specialising to `(P, Q) = (1, −1)` recovers Mathlib's
`Nat.fib_two_mul` (`fib (2n) = fib n · (2·fib (n+1) − fib n)`) from the general
two-parameter doubling law — an independent proof.

No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ02OQ02OQ01

open FibonacciIdentitiesOQ02OQ02

/-- The **second-kind (companion) Lucas sequence** `Vₙ(P, Q)` over `ℤ`:
`V₀ = 2`, `V₁ = P`, `V_{n+2} = P · V_{n+1} − Q · Vₙ`.
For `(P, Q) = (1, −1)` this is the sequence of Lucas numbers. -/
def lucasV (P Q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => P
  | (n + 2) => P * lucasV P Q (n + 1) - Q * lucasV P Q n

@[simp] theorem lucasV_zero (P Q : ℤ) : lucasV P Q 0 = 2 := rfl

@[simp] theorem lucasV_one (P Q : ℤ) : lucasV P Q 1 = P := rfl

/-- The defining recurrence for `V`, as a rewrite lemma. -/
theorem lucasV_add_two (P Q : ℤ) (n : ℕ) :
    lucasV P Q (n + 2) = P * lucasV P Q (n + 1) - Q * lucasV P Q n := rfl

/-- **Bridge lemma.** The companion sequence lives inside the first-kind
sequence: `V_{n+1} = U_{n+2} − Q · Uₙ`.

Proved by induction carrying the statement for both `n` and `n+1` (both `U` and
`V` are second-order, so two consecutive instances are needed). -/
theorem lucasV_succ_eq (P Q : ℤ) (n : ℕ) :
    lucasV P Q (n + 1) = lucasU P Q (n + 2) - Q * lucasU P Q n := by
  suffices h : ∀ n,
      (lucasV P Q (n + 1) = lucasU P Q (n + 2) - Q * lucasU P Q n) ∧
      (lucasV P Q (n + 2) = lucasU P Q (n + 3) - Q * lucasU P Q (n + 1))
    from (h n).1
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- `V 1 = U 2 - Q * U 0`, i.e. `P = P - Q * 0`.
      simp
    · -- `V 2 = U 3 - Q * U 1`.
      have hu3 : lucasU P Q 3 = P * lucasU P Q 2 - Q * lucasU P Q 1 := lucasU_add_two P Q 1
      have hv2 : lucasV P Q 2 = P * lucasV P Q 1 - Q * lucasV P Q 0 := lucasV_add_two P Q 0
      rw [hv2, hu3]
      simp [lucasU_two]
      ring
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨ih2, ?_⟩
    -- Goal: `V (n+3) = U (n+4) - Q * U (n+2)`.
    have hv : lucasV P Q (n + 3) = P * lucasV P Q (n + 2) - Q * lucasV P Q (n + 1) := by
      have := lucasV_add_two P Q (n + 1); simpa using this
    have e2 : lucasU P Q (n + 2) = P * lucasU P Q (n + 1) - Q * lucasU P Q n :=
      lucasU_add_two P Q n
    have e3 : lucasU P Q (n + 3) = P * lucasU P Q (n + 2) - Q * lucasU P Q (n + 1) := by
      have := lucasU_add_two P Q (n + 1); simpa using this
    have e4 : lucasU P Q (n + 4) = P * lucasU P Q (n + 3) - Q * lucasU P Q (n + 2) := by
      have := lucasU_add_two P Q (n + 2); simpa using this
    show lucasV P Q (n + 3) = lucasU P Q (n + 4) - Q * lucasU P Q (n + 2)
    rw [hv, ih2, ih1, e4, e3, e2]
    ring

/-- **Even doubling law.** `U_{2n} = Uₙ · Vₙ`.

For `n = 0` both sides vanish.  For `n = j+1`, the parent's index-addition law
with `(m, n) = (j+1, j)` gives
`U_{2j+2} = U_{j+2}·U_{j+1} − Q·U_{j+1}·U_j = U_{j+1}·(U_{j+2} − Q·U_j)`,
and the bracket is `V_{j+1}` by `lucasV_succ_eq`. -/
theorem lucasU_two_mul (P Q : ℤ) (n : ℕ) :
    lucasU P Q (2 * n) = lucasU P Q n * lucasV P Q n := by
  rcases n with _ | j
  · simp
  · -- `n = j + 1`.
    have hidx : 2 * (j + 1) = (j + 1) + j + 1 := by ring
    have hadd := lucasU_add P Q (j + 1) j
    -- `U ((j+1)+j+1) = U (j+2) · U (j+1) − Q · U (j+1) · U j`.
    have hbridge : lucasV P Q (j + 1) = lucasU P Q (j + 2) - Q * lucasU P Q j :=
      lucasV_succ_eq P Q j
    rw [hidx, hadd, hbridge]
    ring

/-- **Odd doubling law.** `U_{2n+1} = U_{n+1}² − Q · Uₙ²`.

Immediate from the index-addition law with `m = n`. -/
theorem lucasU_two_mul_add_one (P Q : ℤ) (n : ℕ) :
    lucasU P Q (2 * n + 1) = lucasU P Q (n + 1) ^ 2 - Q * lucasU P Q n ^ 2 := by
  have hidx : 2 * n + 1 = n + n + 1 := by ring
  have hadd := lucasU_add P Q n n
  rw [hidx, hadd]
  ring

/-! ### Fibonacci / Lucas-number specialisation `(P, Q) = (1, −1)`

We identify `lucasV 1 (-1)` with the closed form `2·fib (n+1) − fib n` (the Lucas
numbers), then recover Mathlib's `Nat.fib_two_mul` from the general even doubling
law — an independent proof that does not unfold `Nat.fib_two_mul`. -/

/-- `Vₙ(1, −1) = 2·fib (n+1) − fib n` (the Lucas numbers, cast to `ℤ`). -/
theorem lucasV_fib (n : ℕ) :
    lucasV 1 (-1) n = 2 * (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ) := by
  suffices h : ∀ n,
      (lucasV 1 (-1) n = 2 * (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ)) ∧
      (lucasV 1 (-1) (n + 1) = 2 * (Nat.fib (n + 2) : ℤ) - (Nat.fib (n + 1) : ℤ))
    from (h n).1
  intro n
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> simp
  | succ n ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨ih1, ?_⟩
    have hv : lucasV 1 (-1) (n + 2) = lucasV 1 (-1) (n + 1) + lucasV 1 (-1) n := by
      rw [lucasV_add_two]; ring
    rw [hv, ih0, ih1, Nat.fib_add_two (n := n + 1)]
    push_cast
    ring

/-- Mathlib's `Nat.fib_two_mul` recovered from the general even doubling law
`U_{2n} = Uₙ · Vₙ` at `(P, Q) = (1, −1)`, cast to `ℤ`. -/
theorem fib_two_mul_via_lucas (n : ℕ) :
    (Nat.fib (2 * n) : ℤ)
      = (Nat.fib n : ℤ) * (2 * (Nat.fib (n + 1) : ℤ) - (Nat.fib n : ℤ)) := by
  have h := lucasU_two_mul 1 (-1) n
  rw [lucasU_fib, lucasU_fib, lucasV_fib] at h
  exact h

end FibonacciIdentitiesOQ02OQ02OQ01
