/-
Pell's Equation OQ-06-OQ-03-OQ-03: The Uniform Trace Recurrence for Pell Chains

The parent entry (`pell-equation-oq-06-oq-03`) records that each coordinate of the
negative-Pell chain of `x² − 2y² = −1` satisfies the *specific* second-order
recurrence

    uₙ₊₂ = 6 uₙ₊₁ − uₙ,

the coefficient `6` being the trace of the transfer matrix `[[3,4],[2,3]]`
(multiplication by the fundamental unit `3 + 2√2` of `ℤ[√2]`). This entry proves the
*uniform* statement behind that computation, for an arbitrary real-quadratic ring
`ℤ√d` and an arbitrary generating element `z`:

    for the chain  sₙ = zⁿ · w,   both coordinates satisfy
        uₙ₊₂ = 2·(z.re)·uₙ₊₁ − N(z)·uₙ,

where `N(z) = z.re² − d·z.im²` is the norm. This is exactly the Cayley–Hamilton
relation for the `ℤ`-linear transfer map `s ↦ z·s`, whose matrix `[[z.re, d·z.im],
[z.im, z.re]]` has trace `2·z.re` and determinant `N(z)`; the characteristic
polynomial is `t² − 2(z.re)t + N(z)`.

Specializing to a *unit* `z` (norm `1`) gives the recurrence with the `−uₙ` tail seen
in the parent, with coefficient `2·(z.re)`. For `d = 2`, `z = 3 + 2√2` one has
`z.re = 3`, recovering `uₙ₊₂ = 6uₙ₊₁ − uₙ`. The base point `w` is free: taking `w` a
solution of `x² − d y² = −1` (norm `−1`) makes every chain element a negative-Pell
solution — this is recorded in `chain_norm`.

Main results:
  • `re_rec` / `im_rec`         — the general trace recurrence, coefficient `2·z.re`,
                                  tail `N(z)`, for each coordinate of `zⁿ·w`.
  • `unit_re_rec` / `unit_im_rec` — the unit case `N(z) = 1`: `uₙ₊₂ = 2(z.re)uₙ₊₁ − uₙ`.
  • `chain_norm`                — every element of the chain has norm `N(w)`; so a
                                  negative-Pell base propagates to the whole chain.
  • `rec_unique`                — the recurrence plus two initial values determines a
                                  sequence uniquely (structural payoff, general form).

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Parent entry: `pell-equation-oq-06-oq-03` (the concrete `d = 2` recurrence `6`).
- Grandparent: `pell-equation-oq-06` (the vector recurrence / unit multiplication).
- Cayley–Hamilton for `2×2`: `M² = (tr M)·M − (det M)·I`.
-/

import Mathlib

namespace PellEquationOQ06OQ03OQ03

open Zsqrtd

variable {d : ℤ}

/-
## One-step (vector) recurrence

Multiplying the chain state by the generator `z` acts as the transfer matrix
`[[z.re, d·z.im], [z.im, z.re]]`. These two lemmas are just the real/imaginary parts
of `zⁿ⁺¹·w = z·(zⁿ·w)`.
-/

/-- Real part of one chain step: `(zⁿ⁺¹·w).re = z.re·(zⁿ·w).re + d·z.im·(zⁿ·w).im`. -/
theorem re_step (z w : ℤ√d) (n : ℕ) :
    (z ^ (n + 1) * w).re = z.re * (z ^ n * w).re + d * z.im * (z ^ n * w).im := by
  have h : z ^ (n + 1) * w = z * (z ^ n * w) := by rw [pow_succ]; ring
  rw [h, re_mul]

/-- Imaginary part of one chain step: `(zⁿ⁺¹·w).im = z.re·(zⁿ·w).im + z.im·(zⁿ·w).re`. -/
theorem im_step (z w : ℤ√d) (n : ℕ) :
    (z ^ (n + 1) * w).im = z.re * (z ^ n * w).im + z.im * (z ^ n * w).re := by
  have h : z ^ (n + 1) * w = z * (z ^ n * w) := by rw [pow_succ]; ring
  rw [h, im_mul]

/-
## The uniform trace recurrence (Cayley–Hamilton)

Iterating the one-step recurrence twice and eliminating the imaginary part yields the
order-2 scalar recurrence with coefficient `2·z.re` (the trace) and tail `N(z)` (the
determinant). This is `M² = (tr M)·M − (det M)·I` applied to the chain state.
-/

/-- **General trace recurrence, first coordinate.**
    `(zⁿ⁺²·w).re = 2·(z.re)·(zⁿ⁺¹·w).re − N(z)·(zⁿ·w).re`, for any `z, w : ℤ√d`. -/
theorem re_rec (z w : ℤ√d) (n : ℕ) :
    (z ^ (n + 2) * w).re
      = 2 * z.re * (z ^ (n + 1) * w).re - z.norm * (z ^ n * w).re := by
  rw [show n + 2 = n + 1 + 1 from rfl, re_step z w (n + 1), re_step z w n,
    im_step z w n, norm_def]
  ring

/-- **General trace recurrence, second coordinate.** Same coefficients; both
    coordinates of `zⁿ·w` obey the recurrence dictated by the characteristic
    polynomial `t² − 2(z.re)t + N(z)`. -/
theorem im_rec (z w : ℤ√d) (n : ℕ) :
    (z ^ (n + 2) * w).im
      = 2 * z.re * (z ^ (n + 1) * w).im - z.norm * (z ^ n * w).im := by
  rw [show n + 2 = n + 1 + 1 from rfl, im_step z w (n + 1), im_step z w n,
    re_step z w n, norm_def]
  ring

/-
## The unit case: the negative-Pell recurrence

When the generator `z` is a unit (`N(z) = 1`), the tail coefficient collapses to `1`
and we recover the parent's shape `uₙ₊₂ = 2(z.re)·uₙ₊₁ − uₙ`.
-/

/-- **Unit trace recurrence, first coordinate.** If `N(z) = 1` then
    `(zⁿ⁺²·w).re = 2·(z.re)·(zⁿ⁺¹·w).re − (zⁿ·w).re`. For `d = 2`, `z = 3 + 2√2`
    (so `z.re = 3`) this is the parent's `uₙ₊₂ = 6uₙ₊₁ − uₙ`. -/
theorem unit_re_rec (z w : ℤ√d) (hz : z.norm = 1) (n : ℕ) :
    (z ^ (n + 2) * w).re = 2 * z.re * (z ^ (n + 1) * w).re - (z ^ n * w).re := by
  rw [re_rec, hz, one_mul]

/-- **Unit trace recurrence, second coordinate.** The companion statement for the
    `y`-values. -/
theorem unit_im_rec (z w : ℤ√d) (hz : z.norm = 1) (n : ℕ) :
    (z ^ (n + 2) * w).im = 2 * z.re * (z ^ (n + 1) * w).im - (z ^ n * w).im := by
  rw [im_rec, hz, one_mul]

/-
## Norm propagation along the chain

The multiplicativity of the norm shows every chain element shares the norm of the
base point (up to the unit generator). In particular a negative-Pell base (`N(w) = −1`)
generates a chain of negative-Pell solutions.
-/

/-- `N(zⁿ) = N(z)ⁿ`: the norm is multiplicative under powers. -/
theorem norm_pow (z : ℤ√d) (n : ℕ) : (z ^ n).norm = z.norm ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, norm_mul, ih, pow_succ]

/-- **Norm is constant along a unit-generated chain.** If `N(z) = 1` then every
    `zⁿ·w` has norm `N(w)`. Hence a base solving `x² − d y² = −1` yields a whole
    chain of solutions of the same equation. -/
theorem chain_norm (z w : ℤ√d) (hz : z.norm = 1) (n : ℕ) :
    (z ^ n * w).norm = w.norm := by
  rw [norm_mul, norm_pow, hz, one_pow, one_mul]

/-
## Structural payoff: the recurrence characterizes the sequence

The order-2 recurrence together with two initial values pins the sequence down. This
is the abstract form of the parent's `negPellSeq_fst_unique` / `..._snd_unique`,
valid for any coefficient `c`.
-/

/-- **Uniqueness.** Two integer sequences obeying `uₙ₊₂ = c·uₙ₊₁ − uₙ` with matching
    first two values coincide everywhere (standard two-step induction). -/
theorem rec_unique (c : ℤ) (u v : ℕ → ℤ)
    (hu : ∀ n, u (n + 2) = c * u (n + 1) - u n)
    (hv : ∀ n, v (n + 2) = c * v (n + 1) - v n)
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) : ∀ n, u n = v n := by
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1⟩
    | succ k ih =>
      obtain ⟨a, b⟩ := ih
      exact ⟨b, by rw [hu, hv, a, b]⟩
  exact fun n => (key n).1

/-
## Sanity checks: recovering the parent `d = 2` chain

The fundamental unit `3 + 2√2` of `ℤ[√2]` has norm `1` and real part `3`, so the unit
recurrence coefficient `2·z.re = 6` matches the parent's `uₙ₊₂ = 6uₙ₊₁ − uₙ`. The base
`1 + √2` has norm `−1`, so the generated chain solves `x² − 2y² = −1`.
-/

example : ((3 + 2 * sqrtd : ℤ√2)).norm = 1 := by decide
example : ((3 + 2 * sqrtd : ℤ√2)).re = 3 := by decide
example : 2 * ((3 + 2 * sqrtd : ℤ√2)).re = 6 := by decide
example : ((1 + sqrtd : ℤ√2)).norm = -1 := by decide

-- The concrete unit recurrence for the parent chain, obtained by specialization.
example (n : ℕ) :
    (((3 + 2 * sqrtd : ℤ√2)) ^ (n + 2) * (1 + sqrtd)).re
      = 6 * (((3 + 2 * sqrtd : ℤ√2)) ^ (n + 1) * (1 + sqrtd)).re
        - (((3 + 2 * sqrtd : ℤ√2)) ^ n * (1 + sqrtd)).re := by
  have h := unit_re_rec (3 + 2 * sqrtd : ℤ√2) (1 + sqrtd) (by decide) n
  simpa using h

-- Every element of that chain is a negative-Pell solution: norm = −1.
example (n : ℕ) : (((3 + 2 * sqrtd : ℤ√2)) ^ n * (1 + sqrtd)).norm = -1 := by
  rw [chain_norm _ _ (by decide)]; decide

#check @re_rec
#check @im_rec
#check @unit_re_rec
#check @chain_norm
#check @rec_unique

end PellEquationOQ06OQ03OQ03
