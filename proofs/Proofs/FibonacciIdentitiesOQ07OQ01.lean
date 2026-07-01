import Mathlib.Tactic
import Proofs.LucasSequenceDegree2Identities
import Proofs.LucasSequenceDegree2IdentitiesOQ02

/-
# Divisibility of General Lucas Sequences: `m ∣ n ⟹ Uₘ ∣ Uₙ`

## Open Question (answered — forward direction)

The parent entry `FibonacciIdentitiesOQ07` records the Fibonacci divisibility
*characterization* `Fₘ ∣ Fₙ ⟺ m ∣ n` (for `m ≥ 3`).  Its genuinely original half is the
**reverse** implication; the **forward** implication `m ∣ n ⟹ Fₘ ∣ Fₙ` is already in
Mathlib as `Nat.fib_dvd`.  This gallery line asks whether the forward divisibility — the
defining property of a *divisibility sequence* — generalizes from the Fibonacci numbers to
the **fundamental Lucas sequence** `Uₙ(P,Q)` for arbitrary integer parameters `P, Q`:

  `U₀ = 0,  U₁ = 1,  Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`     (`(P,Q) = (1,−1)` is Fibonacci).

Mathlib has **nothing** about divisibility of the general two-parameter sequence, so this
result is new infrastructure.  We prove, with no hypothesis on `P, Q` whatsoever:

  **`U_dvd_of_dvd`  :  m ∣ n  →  Uₘ ∣ Uₙ`.**

Thus every fundamental Lucas sequence — Fibonacci `(1,−1)`, Pell `(2,−1)`, the Mersenne-like
`(3,2)` with `Uₙ = 2ⁿ − 1`, … — is a divisibility sequence.

## Proof architecture

The Fibonacci proof leans on `Nat.fib_dvd`, which does not exist here, so we build from the
recurrence.  The engine is a **factor-of-2-free convolution identity**

  **`U_conv`  :  U_{m+n+1} = U_{m+1}·U_{n+1} − Q·Uₘ·Uₙ`.**

The sibling entry `LucasSequenceDegree2IdentitiesOQ02` proves the *bilinear* addition law
`2·U_{m+n} = Uₘ·Vₙ + Vₘ·Uₙ`, but the factor `2` obstructs a divisibility induction over `ℤ`
(one cannot divide by `2`).  We eliminate both `V` and the factor `2`: substitute the
companion-from-fundamental relation `Vₙ = 2·Uₙ₊₁ − P·Uₙ` (`V_eq`) into the bilinear law and
cancel `2` against the `2`'s introduced, leaving the clean quadratic recurrence above.

With `U_conv` in hand, divisibility is a one-line induction.  Writing `d = e + 1`,

  `U_{(k+1)d} = U_{kd+1}·U_d − Q·U_{kd}·U_e`,

so `U_d` divides the first term outright and, by the induction hypothesis `U_d ∣ U_{kd}`, the
second term as well.  Hence `U_d ∣ U_{kd}` for all `k`, i.e. `m ∣ n ⟹ Uₘ ∣ Uₙ`.

## Results

* `U_conv`          — `U_{m+n+1} = U_{m+1}·U_{n+1} − Q·Uₘ·Uₙ` (factor-of-2-free convolution).
* `U_dvd_U_mul`     — `U_d ∣ U_{k·d}` (divisibility along multiples).
* `U_dvd_of_dvd`    — `m ∣ n → Uₘ ∣ Uₙ` (the divisibility-sequence property, any `P, Q`).
* `U_one_neg_one`   — `U 1 (−1) n = Fₙ` (the Fibonacci specialization of the sequence).
* Fibonacci and Pell divisibility corollaries.

## Not proved here (remaining open)

The full *strong* divisibility `gcd(Uₘ, Uₙ) = U_{gcd(m,n)}` — equivalently the reverse
implication `Uₘ ∣ Uₙ → m ∣ n` — holds only under `gcd(P, Q) = 1` and needs the coprimality
`gcd(Uₙ, Uₙ₊₁) = 1`; that is left for a follow-up.

## Axioms: 0 | Sorries: 0
-/

namespace FibonacciIdentitiesOQ07OQ01

open LucasSequenceDegree2Identities LucasSequenceDegree2IdentitiesOQ02

/-- **Factor-of-2-free convolution.** `U_{m+n+1} = U_{m+1}·U_{n+1} − Q·Uₘ·Uₙ`.

Derived from the bilinear addition law `2·U_{m+n} = Uₘ·Vₙ + Vₘ·Uₙ` (`two_U_add`) by
substituting `V_eq` (`Vₖ = 2·Uₖ₊₁ − P·Uₖ`) and the recurrence to eliminate both the
companion sequence `V` and the leading factor `2`. -/
theorem U_conv (P Q : ℤ) (m n : ℕ) :
    U P Q (m + n + 1) = U P Q (m + 1) * U P Q (n + 1) - Q * U P Q m * U P Q n := by
  have h2 : 2 * U P Q (m + (n + 1)) =
      U P Q m * V P Q (n + 1) + V P Q m * U P Q (n + 1) := two_U_add P Q m (n + 1)
  have hVn1 : V P Q (n + 1) = 2 * U P Q (n + 1 + 1) - P * U P Q (n + 1) := V_eq P Q (n + 1)
  have hVm : V P Q m = 2 * U P Q (m + 1) - P * U P Q m := V_eq P Q m
  have hUn2 : U P Q (n + 1 + 1) = P * U P Q (n + 1) - Q * U P Q n := U_add_two P Q n
  have hidx : m + (n + 1) = m + n + 1 := by omega
  rw [hidx] at h2
  have key : 2 * U P Q (m + n + 1) =
      2 * (U P Q (m + 1) * U P Q (n + 1) - Q * U P Q m * U P Q n) := by
    linear_combination h2 + U P Q m * hVn1 + U P Q (n + 1) * hVm + 2 * U P Q m * hUn2
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) key

/-- **Divisibility along multiples.** `U_d ∣ U_{k·d}` for every `k`, with no hypothesis on
`P, Q`.  Induction on `k` closed by the convolution `U_conv`. -/
theorem U_dvd_U_mul (P Q : ℤ) (d k : ℕ) : U P Q d ∣ U P Q (k * d) := by
  induction k with
  | zero => simp
  | succ j ih =>
    rcases d with _ | e
    · simp
    · -- `d = e + 1`; expand `U_{(j+1)(e+1)}` via the convolution at `(m, n) = (j(e+1), e)`.
      have hconv := U_conv P Q (j * (e + 1)) e
      have hidx : (j + 1) * (e + 1) = j * (e + 1) + e + 1 := by ring
      rw [hidx, hconv]
      have h1 : U P Q (e + 1) ∣ U P Q (j * (e + 1) + 1) * U P Q (e + 1) := dvd_mul_left _ _
      have h2 : U P Q (e + 1) ∣ Q * U P Q (j * (e + 1)) * U P Q e :=
        (ih.mul_left Q).mul_right _
      exact dvd_sub h1 h2

/-- **The divisibility-sequence property.** `m ∣ n → Uₘ ∣ Uₙ` for the fundamental Lucas
sequence of *any* parameters `P, Q`.  Generalizes `Nat.fib_dvd` (the `(P,Q) = (1,−1)` case). -/
theorem U_dvd_of_dvd (P Q : ℤ) {m n : ℕ} (h : m ∣ n) : U P Q m ∣ U P Q n := by
  obtain ⟨k, rfl⟩ := h
  rw [mul_comm]
  exact U_dvd_U_mul P Q m k

/-- **Fibonacci specialization of the sequence.** `U 1 (−1) n = Fₙ`.  Proved by the two-step
(consecutive-pair) induction, since `Uₙ₊₂ = Uₙ₊₁ + Uₙ` matches `Nat.fib_add_two`. -/
theorem U_one_neg_one (n : ℕ) : U 1 (-1) n = (Nat.fib n : ℤ) := by
  suffices key : ∀ m : ℕ,
      U 1 (-1) m = (Nat.fib m : ℤ) ∧ U 1 (-1) (m + 1) = (Nat.fib (m + 1) : ℤ) from (key n).1
  intro m
  induction m with
  | zero => exact ⟨by simp, by simp⟩
  | succ k ih =>
    obtain ⟨ih0, ih1⟩ := ih
    refine ⟨ih1, ?_⟩
    have hrec : U 1 (-1) (k + 2) = 1 * U 1 (-1) (k + 1) - (-1) * U 1 (-1) k := U_add_two 1 (-1) k
    rw [show k + 1 + 1 = k + 2 from rfl, hrec, ih0, ih1, Nat.fib_add_two]
    push_cast; ring

/-- Fibonacci divisibility recovered from the general theorem: `m ∣ n → Fₘ ∣ Fₙ` over `ℤ`. -/
theorem fib_dvd_of_dvd {m n : ℕ} (h : m ∣ n) : (Nat.fib m : ℤ) ∣ (Nat.fib n : ℤ) := by
  rw [← U_one_neg_one, ← U_one_neg_one]
  exact U_dvd_of_dvd 1 (-1) h

/-- Pell divisibility: the Pell numbers `Pₙ = U 2 (−1) n` form a divisibility sequence. -/
theorem pell_dvd_of_dvd {m n : ℕ} (h : m ∣ n) : U 2 (-1) m ∣ U 2 (-1) n :=
  U_dvd_of_dvd 2 (-1) h

/-- Numeric sanity check of `U_conv` at `(1,−1)`, `m = 3, n = 4`:
`F₈ = 21` and `F₄·F₅ − (−1)·F₃·F₄ = 3·5 + 2·3 = 21`. -/
example : U 1 (-1) (3 + 4 + 1) =
    U 1 (-1) (3 + 1) * U 1 (-1) (4 + 1) - (-1) * U 1 (-1) 3 * U 1 (-1) 4 := by decide

/-- Numeric sanity check of divisibility: `F₃ = 2 ∣ F₆ = 8`. -/
example : U 1 (-1) 3 ∣ U 1 (-1) 6 := by decide

/-- Numeric sanity check of Pell divisibility: `P₂ = 2 ∣ P₆ = 70`. -/
example : U 2 (-1) 2 ∣ U 2 (-1) 6 := by decide

end FibonacciIdentitiesOQ07OQ01
