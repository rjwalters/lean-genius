import Mathlib.Tactic
import Proofs.LucasSequenceDegree2Identities

/-
# The Sharp Divisibility Bound `gcd(Uₙ, Vₙ) ∣ 2` for Coprime Parameters

## Open Question (answered)

For the two Lucas sequences of parameters `(P, Q)`

  `Uₙ` : `U₀ = 0, U₁ = 1`,   `Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`   (fundamental)
  `Vₙ` : `V₀ = 2, V₁ = P`,   `Vₙ₊₂ = P·Vₙ₊₁ − Q·Vₙ`   (companion)

the sibling entry `LucasSequenceDegree2IdentitiesOQ02` proves the *unconditional*
divisibility core `gcd(Uₙ, Vₙ) ∣ 4·Qⁿ` (and its `Q = −1` corollary `∣ 4`), from the
master identity `Vₙ² − D·Uₙ² = 4·Qⁿ`.  Its open question asks to **sharpen** this to

  **`gcd(Uₙ, Vₙ) ∣ 2`  whenever `gcd(P, Q) = 1`.**

This is the best possible constant: for the Fibonacci/Lucas case `(P,Q) = (1,−1)` one
has `gcd(F₃, L₃) = gcd(2, 4) = 2`, so the `2` cannot be improved to `1`.

## Results

* `U_succ_coprime_Q`  — `IsCoprime Uₙ₊₁ Q`  (`Uₙ₊₁ ≡ Pⁿ (mod Q)`, so coprime to `Q`).
* `U_coprime_succ`    — `IsCoprime Uₙ Uₙ₊₁`  (consecutive fundamental terms are coprime).
* `gcd_dvd_two_of_coprime` — the sharp bound `gcd(Uₙ, Vₙ) ∣ 2` for `gcd(P,Q)=1`.
* `fib_lucas_gcd_dvd_two` / `pell_gcd_dvd_two` — Fibonacci/Lucas and Pell instances.

## Proof architecture

The engine is the companion-from-fundamental relation `Vₙ = 2·Uₙ₊₁ − P·Uₙ` (`V_eq`,
proved in the base file).  Writing `g = gcd(Uₙ, Vₙ)`:

* `g ∣ Uₙ` and `g ∣ Vₙ`, so `g ∣ Vₙ + P·Uₙ = 2·Uₙ₊₁`.
* Under `gcd(P,Q) = 1`, consecutive terms `Uₙ, Uₙ₊₁` are coprime (`U_coprime_succ`),
  hence `IsCoprime g Uₙ₊₁` (as `g ∣ Uₙ`).
* From `g ∣ 2·Uₙ₊₁` and `IsCoprime g Uₙ₊₁` we cancel `Uₙ₊₁` (`IsCoprime.dvd_of_dvd_mul_right`)
  to get `g ∣ 2`.

The coprimality `U_coprime_succ` is itself an induction, and needs the auxiliary
`U_succ_coprime_Q` (`Uₙ₊₁` is coprime to `Q`) so that the step
`Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ` can be reduced modulo `Uₙ₊₁` to `−Q·Uₙ` and split by
`IsCoprime.mul_right`.

## Axioms: 0 | Sorries: 0
-/

namespace LucasSequenceDegree2IdentitiesOQ02OQ01

open LucasSequenceDegree2Identities

/-- **`Uₙ₊₁` is coprime to `Q`** when `gcd(P,Q) = 1`.  Modulo `Q` the recurrence reads
`Uₙ₊₂ ≡ P·Uₙ₊₁`, so `Uₙ₊₁ ≡ Pⁿ`; the induction step drops the `Q·Uₙ` term and splits the
product `P·Uₙ₊₁` via `IsCoprime.mul_left`. -/
theorem U_succ_coprime_Q (P Q : ℤ) (hPQ : IsCoprime P Q) :
    ∀ n : ℕ, IsCoprime (U P Q (n + 1)) Q := by
  intro n
  induction n with
  | zero =>
      -- U₁ = 1
      simpa [U_one] using (isCoprime_one_left : IsCoprime (1 : ℤ) Q)
  | succ k ih =>
      -- U_{k+2} = P·U_{k+1} − Q·U_k = (P·U_{k+1}) + Q·(−U_k)
      have hrec : U P Q (k + 1 + 1) = P * U P Q (k + 1) - Q * U P Q k := U_add_two P Q k
      have hbase : IsCoprime (P * U P Q (k + 1)) Q := hPQ.mul_left ih
      have hshift : IsCoprime (P * U P Q (k + 1) + Q * (-U P Q k)) Q :=
        hbase.add_mul_left_left (-U P Q k)
      have he : P * U P Q (k + 1) + Q * (-U P Q k) = U P Q (k + 1 + 1) := by
        rw [hrec]; ring
      rwa [he] at hshift

/-- **Consecutive fundamental terms are coprime:** `IsCoprime Uₙ Uₙ₊₁` when
`gcd(P,Q) = 1`.  Induction on `n`; the step rewrites `Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`, reduces it
modulo `Uₙ₊₁` to `−Q·Uₙ`, and splits `Q·Uₙ` using `U_succ_coprime_Q` and the symmetric
inductive hypothesis. -/
theorem U_coprime_succ (P Q : ℤ) (hPQ : IsCoprime P Q) :
    ∀ n : ℕ, IsCoprime (U P Q n) (U P Q (n + 1)) := by
  intro n
  induction n with
  | zero =>
      -- U₀ = 0, U₁ = 1 : IsCoprime 0 1
      simpa [U_zero, U_one] using (isCoprime_one_right : IsCoprime (0 : ℤ) 1)
  | succ k ih =>
      have hrec : U P Q (k + 1 + 1) = P * U P Q (k + 1) - Q * U P Q k := U_add_two P Q k
      -- IsCoprime U_{k+1} (Q · U_k):  U_{k+1} ⟂ Q  and  U_{k+1} ⟂ U_k
      have hQ : IsCoprime (U P Q (k + 1)) Q := U_succ_coprime_Q P Q hPQ k
      have hUk : IsCoprime (U P Q (k + 1)) (U P Q k) := ih.symm
      have hmul : IsCoprime (U P Q (k + 1)) (Q * U P Q k) := hQ.mul_right hUk
      -- push through the sign, then add the multiple `U_{k+1} · P`
      have hneg : IsCoprime (U P Q (k + 1)) (-(Q * U P Q k)) := hmul.neg_right
      have hadd : IsCoprime (U P Q (k + 1)) (-(Q * U P Q k) + U P Q (k + 1) * P) :=
        hneg.add_mul_left_right P
      have he : -(Q * U P Q k) + U P Q (k + 1) * P = U P Q (k + 1 + 1) := by
        rw [hrec]; ring
      rwa [he] at hadd

/-- **The sharp divisibility bound.** For coprime parameters `gcd(P,Q) = 1`,
`gcd(Uₙ, Vₙ) ∣ 2`.  This improves the sibling entry's unconditional `gcd(Uₙ, Vₙ) ∣ 4·Qⁿ`
and is sharp (`gcd(F₃, L₃) = 2`). -/
theorem gcd_dvd_two_of_coprime (P Q : ℤ) (hPQ : IsCoprime P Q) (n : ℕ) :
    (Int.gcd (U P Q n) (V P Q n) : ℤ) ∣ 2 := by
  set g : ℤ := (Int.gcd (U P Q n) (V P Q n) : ℤ) with hg
  have hUdvd : g ∣ U P Q n := by rw [hg]; exact Int.gcd_dvd_left _ _
  have hVdvd : g ∣ V P Q n := by rw [hg]; exact Int.gcd_dvd_right _ _
  -- g divides V_n + P·U_n = 2·U_{n+1}
  have h2U : g ∣ 2 * U P Q (n + 1) := by
    have hsum : g ∣ V P Q n + P * U P Q n := dvd_add hVdvd (hUdvd.mul_left P)
    have he : V P Q n + P * U P Q n = 2 * U P Q (n + 1) := by rw [V_eq]; ring
    rwa [he] at hsum
  -- g is coprime to U_{n+1} since g ∣ U_n and U_n ⟂ U_{n+1}
  have hcop : IsCoprime g (U P Q (n + 1)) :=
    (U_coprime_succ P Q hPQ n).of_isCoprime_of_dvd_left hUdvd
  -- cancel the U_{n+1} factor
  exact hcop.dvd_of_dvd_mul_right h2U

/-- **Fibonacci/Lucas instance** `(P,Q) = (1,−1)`: `gcd(Fₙ, Lₙ) ∣ 2`.  Sharp, since
`gcd(F₃, L₃) = gcd(2, 4) = 2`. -/
theorem fib_lucas_gcd_dvd_two (n : ℕ) :
    (Int.gcd (U 1 (-1) n) (V 1 (-1) n) : ℤ) ∣ 2 :=
  gcd_dvd_two_of_coprime 1 (-1) (by norm_num) n

/-- **Pell instance** `(P,Q) = (2,−1)`: `gcd(Pₙ, Qₙ) ∣ 2`. -/
theorem pell_gcd_dvd_two (n : ℕ) :
    (Int.gcd (U 2 (-1) n) (V 2 (-1) n) : ℤ) ∣ 2 :=
  gcd_dvd_two_of_coprime 2 (-1) (by norm_num) n

/-! ## Numerical sanity checks -/

/-- `gcd(F₃, L₃) = gcd(2, 4) = 2` : the bound is attained (equals 2). -/
theorem fib_lucas_gcd_three : Int.gcd (U 1 (-1) 3) (V 1 (-1) 3) = 2 := by decide

/-- `gcd(F₄, L₄) = gcd(3, 7) = 1` : the bound can also be strict. -/
theorem fib_lucas_gcd_four : Int.gcd (U 1 (-1) 4) (V 1 (-1) 4) = 1 := by decide

/-- `gcd(P₂, Q₂) = gcd(2, 6) = 2` for the Pell parameters `(2,−1)`. -/
theorem pell_gcd_two : Int.gcd (U 2 (-1) 2) (V 2 (-1) 2) = 2 := by decide

end LucasSequenceDegree2IdentitiesOQ02OQ01
