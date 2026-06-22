/-
Pell's Equation OQ-06-OQ-03: The Linear Recurrence of the Negative-Pell Chain

The parent entry (`pell-equation-oq-06`) defines the chain of solutions of
x² − 2y² = −1 by the first-order *vector* recurrence

    (xₙ₊₁, yₙ₊₁) = (3xₙ + 4yₙ, 2xₙ + 3yₙ),

i.e. iteration of the linear map with matrix M = [[3,4],[2,3]] (multiplication by
the fundamental unit 3 + 2√2 of ℤ[√2]). This entry records the *scalar* shadow of
that structure: each coordinate, on its own, satisfies the second-order linear
recurrence

    uₙ₊₂ = 6 uₙ₊₁ − uₙ.

The coefficients are forced by the Cayley–Hamilton theorem for M: its
characteristic polynomial is

    t² − (tr M) t + (det M) = t² − 6t + 1,

whose roots are the conjugate units 3 ± 2√2. Hence M² = 6M − I, and applying this
to the state vector gives the same recurrence for both coordinates. We prove the
recurrences directly from the parent's definition (a one-step `ring` identity) and,
as a structural payoff, show the recurrence together with the two initial values
(1, 7) *characterizes* the first-coordinate sequence uniquely.

Main results:
  • `negPellSeq_fst_rec`   — xₙ₊₂ = 6xₙ₊₁ − xₙ.
  • `negPellSeq_snd_rec`   — yₙ₊₂ = 6yₙ₊₁ − yₙ (same recurrence, both coordinates).
  • `negPellSeq_fst_unique`— the recurrence + initial values 1, 7 determine xₙ.
  • `negPellSeq_snd_unique`— the recurrence + initial values 1, 5 determine yₙ.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Parent entry: `pell-equation-oq-06` (the vector recurrence / unit multiplication).
- Sibling entry: `pell-equation-oq-06-oq-02` (the chain as powers of the unit 1 + √2;
  the eigenvalues 3 ± 2√2 of M are ζ², ζ⁻²).
- Cayley–Hamilton: M² = (tr M)·M − (det M)·I for a 2×2 matrix M.
-/

import Mathlib
import Proofs.PellEquationOQ06

namespace PellEquationOQ06OQ03

open PellEquationOQ06

/-
## The second-order recurrence for each coordinate
-/

/-- **The first coordinates satisfy `xₙ₊₂ = 6xₙ₊₁ − xₙ`.** This is the scalar
    recurrence whose characteristic polynomial `t² − 6t + 1` is that of the
    transfer matrix `[[3,4],[2,3]]` (trace 6, determinant 1). Proved by expanding
    two steps of the parent's vector recurrence and a single `ring` identity. -/
theorem negPellSeq_fst_rec (n : ℕ) :
    (negPellSeq (n + 2)).1 = 6 * (negPellSeq (n + 1)).1 - (negPellSeq n).1 := by
  simp only [negPellSeq_succ]
  ring

/-- **The second coordinates satisfy the same recurrence `yₙ₊₂ = 6yₙ₊₁ − yₙ`.**
    Both coordinates of the state vector obey the order-2 recurrence dictated by
    the Cayley–Hamilton relation `M² = 6M − I`. -/
theorem negPellSeq_snd_rec (n : ℕ) :
    (negPellSeq (n + 2)).2 = 6 * (negPellSeq (n + 1)).2 - (negPellSeq n).2 := by
  simp only [negPellSeq_succ]
  ring

/-
## The recurrence and initial data characterize the chain
-/

/-- **The recurrence `uₙ₊₂ = 6uₙ₊₁ − uₙ` with `u₀ = 1`, `u₁ = 7` determines the
    first-coordinate sequence.** Any integer sequence obeying the recurrence and
    matching the chain's first two `x`-values coincides with it everywhere — a
    standard two-step induction. -/
theorem negPellSeq_fst_unique (u : ℕ → ℤ)
    (h0 : u 0 = 1) (h1 : u 1 = 7)
    (hrec : ∀ n, u (n + 2) = 6 * u (n + 1) - u n) :
    ∀ n, u n = (negPellSeq n).1 := by
  have key : ∀ n, u n = (negPellSeq n).1 ∧ u (n + 1) = (negPellSeq (n + 1)).1 := by
    intro n
    induction n with
    | zero => exact ⟨h0.trans (by decide), h1.trans (by decide)⟩
    | succ k ih =>
      obtain ⟨ihk, ihk1⟩ := ih
      refine ⟨ihk1, ?_⟩
      rw [hrec k, ihk1, ihk]
      exact (negPellSeq_fst_rec k).symm
  exact fun n => (key n).1

/-- **The recurrence `uₙ₊₂ = 6uₙ₊₁ − uₙ` with `u₀ = 1`, `u₁ = 5` determines the
    second-coordinate sequence.** The companion uniqueness statement for the
    `y`-values. -/
theorem negPellSeq_snd_unique (u : ℕ → ℤ)
    (h0 : u 0 = 1) (h1 : u 1 = 5)
    (hrec : ∀ n, u (n + 2) = 6 * u (n + 1) - u n) :
    ∀ n, u n = (negPellSeq n).2 := by
  have key : ∀ n, u n = (negPellSeq n).2 ∧ u (n + 1) = (negPellSeq (n + 1)).2 := by
    intro n
    induction n with
    | zero => exact ⟨h0.trans (by decide), h1.trans (by decide)⟩
    | succ k ih =>
      obtain ⟨ihk, ihk1⟩ := ih
      refine ⟨ihk1, ?_⟩
      rw [hrec k, ihk1, ihk]
      exact (negPellSeq_snd_rec k).symm
  exact fun n => (key n).1

/-
## Sanity checks against the explicit chain
-/

-- The chain begins (1,1) → (7,5) → (41,29) → (239,169); the recurrence is visible:
--   41 = 6·7 − 1,  239 = 6·41 − 7,   29 = 6·5 − 1,  169 = 6·29 − 5.
example : (negPellSeq 2).1 = 6 * (negPellSeq 1).1 - (negPellSeq 0).1 := negPellSeq_fst_rec 0
example : (negPellSeq 3).1 = 6 * (negPellSeq 2).1 - (negPellSeq 1).1 := negPellSeq_fst_rec 1
example : (negPellSeq 2).2 = 6 * (negPellSeq 1).2 - (negPellSeq 0).2 := negPellSeq_snd_rec 0
example : (41 : ℤ) = 6 * 7 - 1 := by norm_num
example : (239 : ℤ) = 6 * 41 - 7 := by norm_num
example : (169 : ℤ) = 6 * 29 - 5 := by norm_num

#check @negPellSeq_fst_rec
#check @negPellSeq_snd_rec
#check @negPellSeq_fst_unique
#check @negPellSeq_snd_unique

end PellEquationOQ06OQ03
