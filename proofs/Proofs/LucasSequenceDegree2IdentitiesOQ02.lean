import Mathlib.Tactic
import Proofs.LucasSequenceDegree2Identities

/-
# Bilinear Addition Laws for General Lucas Sequences

## Open Question (answered)

The parent entry `LucasSequenceDegree2Identities` establishes the master degree-2
identity `Vₙ² − D·Uₙ² = 4·Qⁿ` (with `D = P² − 4Q`) for the two Lucas sequences

  `Uₙ(P,Q)` : `U₀ = 0, U₁ = 1`,   `Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`   (fundamental)
  `Vₙ(P,Q)` : `V₀ = 2, V₁ = P`,   `Vₙ₊₂ = P·Vₙ₊₁ − Q·Vₙ`   (companion)

but only records the *self-interaction* of a single index `n`.  The genuinely
two-variable structure of the theory lives in the **bilinear addition laws**

  **(A)  `2·U_{m+n} = U_m·V_n + V_m·U_n`**
  **(B)  `2·V_{m+n} = V_m·V_n + D·U_m·U_n`**

which express `U`, `V` at a sum of indices through their values at the summands.
These are the general-parameter analogues of the classical Fibonacci/Lucas laws
`2F_{m+n} = F_m L_n + L_m F_n`, `2L_{m+n} = L_m L_n + 5 F_m F_n`.

## Results

* `two_U_add`   — (A) `2·U_{m+n} = U_m·V_n + V_m·U_n`.
* `two_V_add`   — (B) `2·V_{m+n} = V_m·V_n + (P²−4Q)·U_m·U_n`.
* `U_doubling`  — `U_{2n} = U_n·V_n`                 (answers parent OQ-01, first).
* `V_doubling`  — `V_{2n} = V_n² − 2·Q^n`            (answers parent OQ-01, second).
* `gcd_dvd_four_mul_Q_pow` — `gcd(U_n, V_n) ∣ 4·Q^n`  (unconditional divisibility core).
* `gcd_dvd_four_of_Q_neg_one` — at `Q = −1`, `gcd(U_n, V_n) ∣ 4`.
* Fibonacci/Lucas and Pell specializations of (A), (B).

## Proof architecture

The two laws are order-2 coupled in `n`, so a single ordinary induction cannot see
enough history.  We strengthen to **consecutive pairs**: prove
`(A(k) ∧ B(k)) ∧ (A(k+1) ∧ B(k+1))` by induction on `k`.  The step multiplies the two
recurrences through by the inductive pair and closes by `linear_combination`.  The two
base cases `n = 0, 1` reduce to the companion-from-fundamental relation `V_eq`
(`Vₙ = 2Uₙ₊₁ − P Uₙ`) already proved in the parent file.

The doubling formulas are the `m = n` specializations of (A), (B); `V_doubling`
additionally eliminates `D·U_n²` via the parent master identity `V_sq_sub_D_U_sq`.

## Axioms: 0 | Sorries: 0
-/

namespace LucasSequenceDegree2IdentitiesOQ02

open LucasSequenceDegree2Identities

/-- **Bilinear addition laws (paired form).** For all `k`, statements (A) and (B) hold
simultaneously at `k` and at `k+1`.  This strengthened conjunction is what makes the
order-2 recurrence amenable to ordinary induction on `k`. -/
theorem add_laws_pair (P Q : ℤ) (m k : ℕ) :
    (2 * U P Q (m + k) = U P Q m * V P Q k + V P Q m * U P Q k ∧
     2 * V P Q (m + k) = V P Q m * V P Q k + (P ^ 2 - 4 * Q) * U P Q m * U P Q k) ∧
    (2 * U P Q (m + (k + 1)) = U P Q m * V P Q (k + 1) + V P Q m * U P Q (k + 1) ∧
     2 * V P Q (m + (k + 1)) =
        V P Q m * V P Q (k + 1) + (P ^ 2 - 4 * Q) * U P Q m * U P Q (k + 1)) := by
  induction k with
  | zero =>
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · -- A(0): 2·U_m = U_m·V₀ + V_m·U₀ = U_m·2 + V_m·0
      simp only [Nat.add_zero, U_zero, V_zero]; ring
    · -- B(0): 2·V_m = V_m·V₀ + D·U_m·U₀ = V_m·2 + D·U_m·0
      simp only [Nat.add_zero, U_zero, V_zero]; ring
    · -- A(1): 2·U_{m+1} = U_m·V₁ + V_m·U₁ = U_m·P + V_m,  via V_eq
      have hv : V P Q m = 2 * U P Q (m + 1) - P * U P Q m := V_eq P Q m
      simp only [Nat.zero_add, V_one, U_one]
      linear_combination -hv
    · -- B(1): 2·V_{m+1} = V_m·V₁ + D·U_m·U₁ = V_m·P + D·U_m
      have hv : V P Q m = 2 * U P Q (m + 1) - P * U P Q m := V_eq P Q m
      have hv1 : V P Q (m + 1) = 2 * U P Q (m + 1 + 1) - P * U P Q (m + 1) := V_eq P Q (m + 1)
      have hu : U P Q (m + 1 + 1) = P * U P Q (m + 1) - Q * U P Q m := U_add_two P Q m
      simp only [Nat.zero_add, V_one, U_one]
      linear_combination 2 * hv1 + 4 * hu - P * hv
  | succ j ih =>
    obtain ⟨⟨hA0, hB0⟩, hA1, hB1⟩ := ih
    -- first component of the new pair is the second of the old pair
    refine ⟨⟨hA1, hB1⟩, ?_, ?_⟩
    · -- A(j+2)
      have hUmn : U P Q (m + (j + 1 + 1)) =
          P * U P Q (m + (j + 1)) - Q * U P Q (m + j) := U_add_two P Q (m + j)
      have hV : V P Q (j + 1 + 1) = P * V P Q (j + 1) - Q * V P Q j := V_add_two P Q j
      have hU : U P Q (j + 1 + 1) = P * U P Q (j + 1) - Q * U P Q j := U_add_two P Q j
      rw [hUmn, hV, hU]
      linear_combination P * hA1 - Q * hA0
    · -- B(j+2)
      have hVmn : V P Q (m + (j + 1 + 1)) =
          P * V P Q (m + (j + 1)) - Q * V P Q (m + j) := V_add_two P Q (m + j)
      have hV : V P Q (j + 1 + 1) = P * V P Q (j + 1) - Q * V P Q j := V_add_two P Q j
      have hU : U P Q (j + 1 + 1) = P * U P Q (j + 1) - Q * U P Q j := U_add_two P Q j
      rw [hVmn, hV, hU]
      linear_combination P * hB1 - Q * hB0

/-- **Bilinear addition law (A).** `2·U_{m+n} = U_m·V_n + V_m·U_n`. -/
theorem two_U_add (P Q : ℤ) (m n : ℕ) :
    2 * U P Q (m + n) = U P Q m * V P Q n + V P Q m * U P Q n :=
  (add_laws_pair P Q m n).1.1

/-- **Bilinear addition law (B).** `2·V_{m+n} = V_m·V_n + (P²−4Q)·U_m·U_n`. -/
theorem two_V_add (P Q : ℤ) (m n : ℕ) :
    2 * V P Q (m + n) = V P Q m * V P Q n + (P ^ 2 - 4 * Q) * U P Q m * U P Q n :=
  (add_laws_pair P Q m n).1.2

/-- **Doubling formula for `U`.** `U_{2n} = U_n·V_n` (parent OQ-01, first formula).
Immediate from (A) at `m = n` after cancelling the factor `2`. -/
theorem U_doubling (P Q : ℤ) (n : ℕ) : U P Q (2 * n) = U P Q n * V P Q n := by
  have h := two_U_add P Q n n
  rw [two_mul] at h ⊢
  linarith [h]

/-- **Doubling formula for `V`.** `V_{2n} = V_n² − 2·Q^n` (parent OQ-01, second formula).
From (B) at `m = n`, `2·V_{2n} = V_n² + D·U_n²`; eliminate `D·U_n²` with the master
identity `V_sq_sub_D_U_sq` (`V_n² − D·U_n² = 4·Q^n`). -/
theorem V_doubling (P Q : ℤ) (n : ℕ) : V P Q (2 * n) = (V P Q n) ^ 2 - 2 * Q ^ n := by
  have h := two_V_add P Q n n
  have hmaster := V_sq_sub_D_U_sq P Q n
  rw [two_mul] at h ⊢
  have key : 2 * V P Q (n + n) = 2 * ((V P Q n) ^ 2 - 2 * Q ^ n) := by
    linear_combination h - hmaster
  exact mul_left_cancel₀ (by norm_num) key

/-- **Divisibility core.** `gcd(U_n, V_n) ∣ 4·Q^n`.  Any common divisor of `U_n` and
`V_n` divides `V_n² − D·U_n² = 4·Q^n`. -/
theorem gcd_dvd_four_mul_Q_pow (P Q : ℤ) (n : ℕ) :
    (Int.gcd (U P Q n) (V P Q n) : ℤ) ∣ 4 * Q ^ n := by
  have hmaster := V_sq_sub_D_U_sq P Q n
  set g : ℤ := (Int.gcd (U P Q n) (V P Q n) : ℤ) with hg
  have hU : g ∣ U P Q n := by rw [hg]; exact Int.gcd_dvd_left _ _
  have hV : g ∣ V P Q n := by rw [hg]; exact Int.gcd_dvd_right _ _
  have h1 : g ∣ (V P Q n) ^ 2 := dvd_pow hV (by norm_num)
  have h2 : g ∣ (P ^ 2 - 4 * Q) * (U P Q n) ^ 2 := (dvd_pow hU (by norm_num)).mul_left _
  have hsub : g ∣ (V P Q n) ^ 2 - (P ^ 2 - 4 * Q) * (U P Q n) ^ 2 := dvd_sub h1 h2
  rwa [hmaster] at hsub

/-- At `Q = −1` (the Fibonacci/Lucas and Pell case) the divisibility core reads
`gcd(U_n, V_n) ∣ 4`. -/
theorem gcd_dvd_four_of_Q_neg_one (P : ℤ) (n : ℕ) :
    (Int.gcd (U P (-1) n) (V P (-1) n) : ℤ) ∣ 4 := by
  have h := gcd_dvd_four_mul_Q_pow P (-1) n
  have hd : ((Int.gcd (U P (-1) n) (V P (-1) n)) : ℤ) ∣ (4 * (-1 : ℤ) ^ n) * (-1) ^ n :=
    h.mul_right _
  have he : (4 * (-1 : ℤ) ^ n) * (-1) ^ n = 4 := by
    rw [mul_assoc, ← mul_pow]; norm_num
  rwa [he] at hd

/-- Fibonacci/Lucas specialization of (A): `2·F_{m+n} = F_m·L_n + L_m·F_n`
(`U = Fibonacci`, `V = Lucas` at `(P,Q) = (1,−1)`). -/
theorem fib_lucas_two_U_add (m n : ℕ) :
    2 * U 1 (-1) (m + n) = U 1 (-1) m * V 1 (-1) n + V 1 (-1) m * U 1 (-1) n :=
  two_U_add 1 (-1) m n

/-- Fibonacci/Lucas specialization of (B): `2·L_{m+n} = L_m·L_n + 5·F_m·F_n`. -/
theorem fib_lucas_two_V_add (m n : ℕ) :
    2 * V 1 (-1) (m + n) = V 1 (-1) m * V 1 (-1) n + 5 * (U 1 (-1) m * U 1 (-1) n) := by
  have h := two_V_add 1 (-1) m n
  norm_num at h
  linear_combination h

/-- Pell specialization of (A) at `(P,Q) = (2,−1)`: `2·P_{m+n} = P_m·Q_n + Q_m·P_n`. -/
theorem pell_two_U_add (m n : ℕ) :
    2 * U 2 (-1) (m + n) = U 2 (-1) m * V 2 (-1) n + V 2 (-1) m * U 2 (-1) n :=
  two_U_add 2 (-1) m n

/-- Numeric sanity check of (A) at `(1,−1)`, `m = 3, n = 4`:
`2·F₇ = 2·13 = 26`, and `F₃·L₄ + L₃·F₄ = 2·7 + 4·3 = 26`. -/
example : 2 * U 1 (-1) (3 + 4) = U 1 (-1) 3 * V 1 (-1) 4 + V 1 (-1) 3 * U 1 (-1) 4 := by
  decide

/-- Numeric sanity check of `U_doubling` at `(1,−1)`, `n = 4`:
`F₈ = 21`, `F₄·L₄ = 3·7 = 21`. -/
example : U 1 (-1) (2 * 4) = U 1 (-1) 4 * V 1 (-1) 4 := by decide

/-- Numeric sanity check of `V_doubling` at `(1,−1)`, `n = 3`:
`L₆ = 18`, `L₃² − 2·(−1)³ = 16 + 2 = 18`. -/
example : V 1 (-1) (2 * 3) = (V 1 (-1) 3) ^ 2 - 2 * (-1 : ℤ) ^ 3 := by decide

end LucasSequenceDegree2IdentitiesOQ02

