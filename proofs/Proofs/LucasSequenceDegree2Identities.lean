import Mathlib.Tactic

/-
# The Master Degree-2 Identity for General Lucas Sequences

## Open Question (gallery gap)

The gallery already records the degree-2 algebra of the **specific** Fibonacci/Lucas
pair `Fₙ, Lₙ` (`FibonacciIdentitiesOQ02OQ01OQ01`), e.g. the difference identity
`Lₙ² − 5·Fₙ² = 4·(−1)ⁿ` and its companion sum/cross identities.  Those are all the
`P = 1, Q = −1` instance of a far more general fact.

For **any** integer parameters `P, Q` the *Lucas sequences* are the two solutions of the
second-order recurrence `xₙ₊₂ = P·xₙ₊₁ − Q·xₙ` with the canonical initial data

  `Uₙ(P,Q)` : `U₀ = 0, U₁ = 1`        (the *fundamental* / first Lucas sequence)
  `Vₙ(P,Q)` : `V₀ = 2, V₁ = P`        (the *companion* / second Lucas sequence)

Their discriminant is `D = P² − 4Q`.  The single identity governing the whole theory is

  **`Vₙ² − D·Uₙ² = 4·Qⁿ`**                                                    (★)

Specializing recovers the gallery's results and the classical special cases:

| `(P, Q)`   | `D`  | `(★)` becomes                | sequences           |
|------------|------|------------------------------|---------------------|
| `(1, −1)`  | `5`  | `Lₙ² − 5·Fₙ² = 4·(−1)ⁿ`       | Fibonacci / Lucas   |
| `(2, −1)`  | `8`  | `Qₙ² − 8·Pₙ² = 4·(−1)ⁿ`       | Pell / Pell-Lucas   |
| `(3, 2)`   | `1`  | `Vₙ² − Uₙ² = 4·2ⁿ`            | `Uₙ = 2ⁿ−1, Vₙ = 2ⁿ+1` |

## Proof architecture (elementary, no closed form, no `√D`)

Everything is purely algebraic over `ℤ`; we never leave the integers or invoke the
Binet closed form.  Two lemmas carry the whole argument:

1. `V_eq` — the **companion-from-fundamental** relation `Vₙ = 2·Uₙ₊₁ − P·Uₙ`, proved by
   a two-step induction (the recurrence couples `n` and `n+1`).  This is what lets us
   eliminate `V` entirely and reduce `(★)` to a statement about `U` alone.

2. `U_quad` — the **invariant quadratic form** `Uₙ₊₁² − P·Uₙ·Uₙ₊₁ + Q·Uₙ² = Qⁿ`,
   proved by a single induction: the form is multiplied by exactly `Q` at each step,
   so it equals `Qⁿ`.  This is the Lucas-sequence Cassini identity in disguise
   (`U_cassini`: `Uₙ₊₁² − Uₙ₊₂·Uₙ = Qⁿ`).

Substituting `Vₙ = 2Uₙ₊₁ − P Uₙ` into `Vₙ² − D Uₙ²` collapses it to
`4·(Uₙ₊₁² − P Uₙ Uₙ₊₁ + Q Uₙ²) = 4·Qⁿ`, which is `(★)`.

The two **doubling** identities are then obtained from a single simultaneous induction
`U_doubling_pair` giving `U₂ₙ` and `U₂ₙ₊₁` together (they are coupled by the recurrence),
after which `U_two_mul` (`U₂ₙ = Uₙ·Vₙ`) and `V_sq_add_D_U_sq` (`Vₙ² + D·Uₙ² = 2·V₂ₙ`)
follow by eliminating `V` with `V_eq`.

## Results

* `U`, `V`                  — the two Lucas sequences over `ℤ`, parametrized by `P, Q`.
* `V_eq`                    — `Vₙ = 2·Uₙ₊₁ − P·Uₙ`.
* `U_quad`                  — `Uₙ₊₁² − P·Uₙ·Uₙ₊₁ + Q·Uₙ² = Qⁿ` (invariant quadratic form).
* `U_cassini`               — `Uₙ₊₁² − Uₙ₊₂·Uₙ = Qⁿ` (Lucas-sequence Cassini).
* `V_sq_sub_D_U_sq`         — **(★)** `Vₙ² − (P²−4Q)·Uₙ² = 4·Qⁿ`, the master identity.
* `U_doubling_pair`         — even/odd index-doubling pair for `U` (one joint induction).
* `U_two_mul`               — **doubling cross identity** `U₂ₙ = Uₙ·Vₙ`.
* `V_sq_add_D_U_sq`         — **doubling sum identity** `Vₙ² + (P²−4Q)·Uₙ² = 2·V₂ₙ`.
* `fib_lucas_instance`      — `(★)` at `(1,−1)`: `Vₙ² − 5·Uₙ² = 4·(−1)ⁿ`.
* `pell_instance`           — `(★)` at `(2,−1)`: `Vₙ² − 8·Uₙ² = 4·(−1)ⁿ`.
* `fib_double_instance`     — `F₂ₙ = Fₙ·Lₙ`; `lucas_sum_double_instance` — `Lₙ² + 5·Fₙ² = 2·L₂ₙ`.

## The three master degree-2 identities

Together `(★)` and its two doubling companions form the complete degree-2 algebra of a
general Lucas pair (each recovers a classical Fibonacci/Lucas relation at `(P,Q)=(1,−1)`):

| identity                        | value    | Fibonacci/Lucas case          |
|---------------------------------|----------|-------------------------------|
| `Vₙ² − D·Uₙ²`                    | `4·Qⁿ`   | `Lₙ² − 5·Fₙ² = 4·(−1)ⁿ`        |
| `Vₙ² + D·Uₙ²`                    | `2·V₂ₙ`  | `Lₙ² + 5·Fₙ² = 2·L₂ₙ`         |
| `Uₙ·Vₙ`                         | `U₂ₙ`    | `Fₙ·Lₙ = F₂ₙ`                 |

## Axioms: 0 | Sorries: 0
-/

namespace LucasSequenceDegree2Identities

/-- The **fundamental Lucas sequence** `Uₙ(P,Q)`: `U₀ = 0`, `U₁ = 1`,
`Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`.  For `(P,Q) = (1,−1)` this is the Fibonacci sequence. -/
def U (P Q : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => P * U P Q (n + 1) - Q * U P Q n

/-- The **companion Lucas sequence** `Vₙ(P,Q)`: `V₀ = 2`, `V₁ = P`,
`Vₙ₊₂ = P·Vₙ₊₁ − Q·Vₙ`.  For `(P,Q) = (1,−1)` this is the Lucas sequence `2,1,3,4,…`. -/
def V (P Q : ℤ) : ℕ → ℤ
  | 0 => 2
  | 1 => P
  | (n + 2) => P * V P Q (n + 1) - Q * V P Q n

@[simp] theorem U_zero (P Q : ℤ) : U P Q 0 = 0 := rfl
@[simp] theorem U_one (P Q : ℤ) : U P Q 1 = 1 := rfl
@[simp] theorem V_zero (P Q : ℤ) : V P Q 0 = 2 := rfl
@[simp] theorem V_one (P Q : ℤ) : V P Q 1 = P := rfl

/-- The defining recurrence of the fundamental sequence: `Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`. -/
theorem U_add_two (P Q : ℤ) (n : ℕ) :
    U P Q (n + 2) = P * U P Q (n + 1) - Q * U P Q n := rfl

/-- The defining recurrence of the companion sequence: `Vₙ₊₂ = P·Vₙ₊₁ − Q·Vₙ`. -/
theorem V_add_two (P Q : ℤ) (n : ℕ) :
    V P Q (n + 2) = P * V P Q (n + 1) - Q * V P Q n := rfl

/-- **Companion-from-fundamental relation.** `Vₙ = 2·Uₙ₊₁ − P·Uₙ`.

Proved by a two-step induction packaged as the conjunction of the statement at `n` and
at `n+1`; the recurrence `Vₙ₊₂ = P·Vₙ₊₁ − Q·Vₙ` consumes both consecutive cases. -/
theorem V_eq (P Q : ℤ) (n : ℕ) : V P Q n = 2 * U P Q (n + 1) - P * U P Q n := by
  -- Strengthen to consecutive pairs so ordinary induction suffices.
  suffices key : ∀ m : ℕ,
      (V P Q m = 2 * U P Q (m + 1) - P * U P Q m) ∧
      (V P Q (m + 1) = 2 * U P Q (m + 2) - P * U P Q (m + 1)) from (key n).1
  intro m
  induction m with
  | zero =>
    refine ⟨?_, ?_⟩
    · simp
    · rw [V_one, U_add_two, U_one, U_zero]; ring
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    refine ⟨ih2, ?_⟩
    have hV : V P Q (k + 2) = P * V P Q (k + 1) - Q * V P Q k := V_add_two P Q k
    have hU3 : U P Q (k + 3) = P * U P Q (k + 2) - Q * U P Q (k + 1) := U_add_two P Q (k + 1)
    have hU2 : U P Q (k + 2) = P * U P Q (k + 1) - Q * U P Q k := U_add_two P Q k
    rw [hV, ih1, ih2, hU3, hU2]; ring

/-- **Invariant quadratic form.** `Uₙ₊₁² − P·Uₙ·Uₙ₊₁ + Q·Uₙ² = Qⁿ`.

The form is exactly `Q`-homogeneous along the recurrence: substituting
`Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ` multiplies it by `Q`, and it starts at `1` for `n = 0`, so it
equals `Qⁿ`. -/
theorem U_quad (P Q : ℤ) (n : ℕ) :
    (U P Q (n + 1)) ^ 2 - P * U P Q n * U P Q (n + 1) + Q * (U P Q n) ^ 2 = Q ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hrec : U P Q (k + 2) = P * U P Q (k + 1) - Q * U P Q k := U_add_two P Q k
    rw [hrec, pow_succ]
    linear_combination Q * ih

/-- **Lucas-sequence Cassini identity.** `Uₙ₊₁² − Uₙ₊₂·Uₙ = Qⁿ`.

Equivalently the determinant `det [[Uₙ₊₁, Uₙ], [Uₙ₊₂, Uₙ₊₁]] = Qⁿ`; immediate from the
invariant quadratic form `U_quad` after expanding `Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`. -/
theorem U_cassini (P Q : ℤ) (n : ℕ) :
    (U P Q (n + 1)) ^ 2 - U P Q (n + 2) * U P Q n = Q ^ n := by
  have h := U_quad P Q n
  rw [U_add_two]; linear_combination h

/-- **Master degree-2 identity (★).** `Vₙ² − (P² − 4Q)·Uₙ² = 4·Qⁿ`.

The single relation from which the entire degree-2 algebra of any Lucas sequence pair
descends.  Eliminate `V` via `V_eq`, then `(★)` reduces by `linear_combination` to four
times the invariant quadratic form `U_quad`. -/
theorem V_sq_sub_D_U_sq (P Q : ℤ) (n : ℕ) :
    (V P Q n) ^ 2 - (P ^ 2 - 4 * Q) * (U P Q n) ^ 2 = 4 * Q ^ n := by
  rw [V_eq]
  linear_combination 4 * U_quad P Q n

/-- **Index-doubling pair for the fundamental sequence.**  Both halves of the doubling
formula, proved by a *single* simultaneous induction: the recurrence
`xₙ₊₂ = P·xₙ₊₁ − Q·xₙ` couples the even index `n+n` with the odd index `n+n+1`, so neither
formula closes on its own — they must be advanced together.

* even: `U₂ₙ   = 2·Uₙ·Uₙ₊₁ − P·Uₙ²`
* odd:  `U₂ₙ₊₁ = Uₙ₊₁² − Q·Uₙ²`

(The odd half is the `m = n` case of d'Ocagne's identity
`U_{m+n+1} = U_{m+1}U_{n+1} − Q·U_m U_n`.) -/
theorem U_doubling_pair (P Q : ℤ) (n : ℕ) :
    U P Q (n + n) = 2 * U P Q n * U P Q (n + 1) - P * (U P Q n) ^ 2 ∧
      U P Q (n + n + 1) = (U P Q (n + 1)) ^ 2 - Q * (U P Q n) ^ 2 := by
  induction n with
  | zero => refine ⟨?_, ?_⟩ <;> simp
  | succ k ih =>
    obtain ⟨hA, hB⟩ := ih
    -- Recurrence at the three indices the step touches.
    have rUk : U P Q (k + 1 + 1) = P * U P Q (k + 1) - Q * U P Q k := U_add_two P Q k
    have rEven : U P Q (k + k + 2) = P * U P Q (k + k + 1) - Q * U P Q (k + k) :=
      U_add_two P Q (k + k)
    have rOdd : U P Q (k + k + 1 + 2) = P * U P Q (k + k + 2) - Q * U P Q (k + k + 1) :=
      U_add_two P Q (k + k + 1)
    -- Normalise the doubled successor indices.
    have eEven : k + 1 + (k + 1) = k + k + 2 := by omega
    have eOdd : k + 1 + (k + 1) + 1 = k + k + 1 + 2 := by omega
    refine ⟨?_, ?_⟩
    · rw [eEven, rEven, hB, hA, rUk]; ring
    · rw [eOdd, rOdd, rEven, hB, hA, rUk]; ring

/-- **Doubling cross identity.** `U₂ₙ = Uₙ·Vₙ` (equivalently `Uₙ·Vₙ = U₂ₙ`).

The first generalized Fibonacci doubling formula `F₂ₙ = Fₙ·Lₙ`: eliminate `V` with `V_eq`
and the even half of `U_doubling_pair` closes it. -/
theorem U_two_mul (P Q : ℤ) (n : ℕ) :
    U P Q (n + n) = U P Q n * V P Q n := by
  rw [V_eq]
  linear_combination (U_doubling_pair P Q n).1

/-- **Doubling sum identity.** `Vₙ² + (P²−4Q)·Uₙ² = 2·V₂ₙ`.

The companion of `(★)`: where the *difference* `Vₙ² − D·Uₙ²` measures `4·Qⁿ`, the *sum*
`Vₙ² + D·Uₙ²` measures `2·V₂ₙ`.  Expand both `Vₙ` and `V₂ₙ` via `V_eq`, then both halves of
`U_doubling_pair` reduce it to a polynomial identity in `Uₙ, Uₙ₊₁`. -/
theorem V_sq_add_D_U_sq (P Q : ℤ) (n : ℕ) :
    (V P Q n) ^ 2 + (P ^ 2 - 4 * Q) * (U P Q n) ^ 2 = 2 * V P Q (n + n) := by
  obtain ⟨hA, hB⟩ := U_doubling_pair P Q n
  rw [V_eq P Q n, V_eq P Q (n + n), hA, hB]
  ring

/-- Instantiation at `(P, Q) = (1, −1)` recovers the gallery's Fibonacci/Lucas identity
`Lₙ² − 5·Fₙ² = 4·(−1)ⁿ`: here `U = Fibonacci`, `V = Lucas`, and `D = 1² − 4·(−1) = 5`. -/
theorem fib_lucas_instance (n : ℕ) :
    (V 1 (-1) n) ^ 2 - 5 * (U 1 (-1) n) ^ 2 = 4 * (-1 : ℤ) ^ n := by
  have h := V_sq_sub_D_U_sq 1 (-1) n
  norm_num at h
  linarith [h]

/-- Instantiation at `(P, Q) = (2, −1)` gives the Pell / Pell-Lucas identity
`Vₙ² − 8·Uₙ² = 4·(−1)ⁿ`: here `D = 2² − 4·(−1) = 8`. -/
theorem pell_instance (n : ℕ) :
    (V 2 (-1) n) ^ 2 - 8 * (U 2 (-1) n) ^ 2 = 4 * (-1 : ℤ) ^ n := by
  have h := V_sq_sub_D_U_sq 2 (-1) n
  norm_num at h
  linarith [h]

/-- Fibonacci doubling at `(P,Q) = (1,−1)`: `F₂ₙ = Fₙ·Lₙ`, the classical identity
expressing the even-index Fibonacci number as a product of the matching Fibonacci and
Lucas numbers. -/
theorem fib_double_instance (n : ℕ) :
    U 1 (-1) (n + n) = U 1 (-1) n * V 1 (-1) n :=
  U_two_mul 1 (-1) n

/-- Lucas doubling at `(P,Q) = (1,−1)`: `Lₙ² + 5·Fₙ² = 2·L₂ₙ`, the sum companion of the
gallery's difference identity `Lₙ² − 5·Fₙ² = 4·(−1)ⁿ`. -/
theorem lucas_sum_double_instance (n : ℕ) :
    (V 1 (-1) n) ^ 2 + 5 * (U 1 (-1) n) ^ 2 = 2 * V 1 (-1) (n + n) := by
  have h := V_sq_add_D_U_sq 1 (-1) n
  norm_num at h
  linarith [h]

/-- Numeric sanity check of the definitions and `(★)` at `(1,−1)`, `n = 5`:
`U₅ = F₅ = 5`, `V₅ = L₅ = 11`, and `11² − 5·5² = 121 − 125 = −4 = 4·(−1)⁵`. -/
example : U 1 (-1) 5 = 5 ∧ V 1 (-1) 5 = 11 ∧
    (V 1 (-1) 5) ^ 2 - 5 * (U 1 (-1) 5) ^ 2 = 4 * (-1 : ℤ) ^ 5 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Numeric sanity check at `(2,−1)` (Pell), `n = 4`:
`U₄ = 12`, `V₄ = 34`, and `34² − 8·12² = 1156 − 1152 = 4 = 4·(−1)⁴`. -/
example : U 2 (-1) 4 = 12 ∧ V 2 (-1) 4 = 34 ∧
    (V 2 (-1) 4) ^ 2 - 8 * (U 2 (-1) 4) ^ 2 = 4 * (-1 : ℤ) ^ 4 := by
  refine ⟨by decide, by decide, by decide⟩

/-- Numeric sanity check of both doubling identities at `(1,−1)`, `n = 3`:
`F₆ = 8 = F₃·L₃ = 2·4`, and `L₃² + 5·F₃² = 16 + 20 = 36 = 2·L₆ = 2·18`. -/
example : U 1 (-1) (3 + 3) = U 1 (-1) 3 * V 1 (-1) 3 ∧
    (V 1 (-1) 3) ^ 2 + 5 * (U 1 (-1) 3) ^ 2 = 2 * V 1 (-1) (3 + 3) := by
  refine ⟨by decide, by decide⟩

end LucasSequenceDegree2Identities
