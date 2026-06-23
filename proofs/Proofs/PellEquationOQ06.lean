/-
Pell's Equation OQ-06: The Negative Pell Equation x² − 2y² = −1

The classical Pell equation x² − Dy² = 1 (the norm-one equation for ℚ(√D)) is
the rank-1 case of Dirichlet's unit theorem and always has infinitely many
integer solutions for non-square D > 0. The *negative* Pell equation

    x² − D y² = −1

is more delicate: it is solvable only for special D (e.g. D = 2, 5, 10, …, those
whose continued-fraction period is odd), and Mathlib's `Pell.Solution₁ d` type is
restricted to the norm `+1` equation — the norm `−1` case is listed as future work
in `Mathlib/NumberTheory/Pell.lean`. This entry treats the smallest interesting
instance D = 2 from scratch.

The equation x² − 2y² = −1 has the fundamental solution (1, 1), and the
automorphism of the form induced by the fundamental *unit* 3 + 2√2 of norm +1,

    (x, y) ↦ (3x + 4y, 2x + 3y),

preserves the value x² − 2y² exactly (it is multiplication by 3 + 2√2 in
ℤ[√2]). Iterating it from (1, 1) produces the strictly increasing chain

    (1, 1) → (7, 5) → (41, 29) → (239, 169) → …

of solutions to x² − 2y² = −1. Distinctness (forced by strict monotonicity of the
first coordinate) gives **infinitely many integer solutions** — the analogue, for
the norm `−1` form, of the standard Pell-chain argument.

Main results:
  • `negPell_step`            — the map preserves the value x² − 2y² = −1 (exact ring identity).
  • `negPellSeq`              — the explicit solution chain from (1, 1).
  • `negPellSeq_norm`         — every term satisfies x² − 2y² = −1.
  • `negPellSeq_fst_strictMono` — the first coordinates are strictly increasing.
  • `negPell_solutions_infinite` — the integer solution set of x² − 2y² = −1 is infinite.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- https://erdosproblems.com / Dirichlet's unit theorem
- Parent entry: `pell-equation` (the norm `+1`, real-quadratic special case).
- Mathlib `Pell.Solution₁` covers only the norm `+1` equation; norm `−1` is future work.
-/

import Mathlib

namespace PellEquationOQ06

/-
## The norm form and its automorphism
-/

/-- **Step map preserves the negative-Pell form.** The substitution
    `(x, y) ↦ (3x + 4y, 2x + 3y)` (multiplication by the fundamental unit
    `3 + 2√2` of ℤ[√2]) keeps the value of `x² − 2y²` unchanged; in particular
    it sends solutions of `x² − 2y² = −1` to solutions. -/
theorem negPell_step (x y : ℤ) (h : x ^ 2 - 2 * y ^ 2 = -1) :
    (3 * x + 4 * y) ^ 2 - 2 * (2 * x + 3 * y) ^ 2 = -1 := by
  have key : (3 * x + 4 * y) ^ 2 - 2 * (2 * x + 3 * y) ^ 2 = x ^ 2 - 2 * y ^ 2 := by ring
  rw [key, h]

/-- The explicit chain of solutions to `x² − 2y² = −1`, starting from the
    fundamental solution `(1, 1)` and iterating the form automorphism. -/
def negPellSeq : ℕ → ℤ × ℤ
  | 0 => (1, 1)
  | (n + 1) => (3 * (negPellSeq n).1 + 4 * (negPellSeq n).2,
                2 * (negPellSeq n).1 + 3 * (negPellSeq n).2)

@[simp] theorem negPellSeq_zero : negPellSeq 0 = (1, 1) := rfl

theorem negPellSeq_succ (n : ℕ) :
    negPellSeq (n + 1) =
      (3 * (negPellSeq n).1 + 4 * (negPellSeq n).2,
       2 * (negPellSeq n).1 + 3 * (negPellSeq n).2) := rfl

/-- Both coordinates of the chain are positive (in fact `≥ 1`). -/
theorem negPellSeq_pos : ∀ n, 1 ≤ (negPellSeq n).1 ∧ 1 ≤ (negPellSeq n).2
  | 0 => by constructor <;> norm_num
  | (n + 1) => by
    obtain ⟨hx, hy⟩ := negPellSeq_pos n
    rw [negPellSeq_succ]
    constructor <;> dsimp <;> linarith

/-- **Every term of the chain solves the negative Pell equation** `x² − 2y² = −1`. -/
theorem negPellSeq_norm : ∀ n, (negPellSeq n).1 ^ 2 - 2 * (negPellSeq n).2 ^ 2 = -1
  | 0 => by norm_num
  | (n + 1) => by
    have ih := negPellSeq_norm n
    rw [negPellSeq_succ]
    dsimp
    have key :
        (3 * (negPellSeq n).1 + 4 * (negPellSeq n).2) ^ 2
          - 2 * (2 * (negPellSeq n).1 + 3 * (negPellSeq n).2) ^ 2
        = (negPellSeq n).1 ^ 2 - 2 * (negPellSeq n).2 ^ 2 := by ring
    rw [key, ih]

/-- The first coordinates are strictly increasing along the chain. -/
theorem negPellSeq_fst_strictMono : StrictMono (fun n => (negPellSeq n).1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨hx, hy⟩ := negPellSeq_pos n
  rw [negPellSeq_succ]
  dsimp
  linarith

/-- The chain `n ↦ negPellSeq n` is injective (strict monotonicity of the first
    coordinate forces distinct terms). -/
theorem negPellSeq_injective : Function.Injective negPellSeq := by
  intro a b hab
  exact negPellSeq_fst_strictMono.injective (congrArg Prod.fst hab)

/-
## Infinitely many solutions
-/

/-- **The negative Pell equation `x² − 2y² = −1` has infinitely many integer
    solutions.** The chain `(1,1) → (7,5) → (41,29) → …` consists of pairwise
    distinct solutions, so the solution set is infinite. This is the norm `−1`
    analogue of the standard Pell-chain argument; Mathlib's `Pell.Solution₁`
    machinery covers only the norm `+1` equation. -/
theorem negPell_solutions_infinite :
    {p : ℤ × ℤ | p.1 ^ 2 - 2 * p.2 ^ 2 = -1}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := negPellSeq) negPellSeq_injective
  intro n
  exact negPellSeq_norm n

/-
## Explicit small solutions (sanity checks)
-/

example : negPellSeq 0 = (1, 1) := rfl
example : negPellSeq 1 = (7, 5) := rfl
example : negPellSeq 2 = (41, 29) := rfl
example : negPellSeq 3 = (239, 169) := rfl

example : (1 : ℤ) ^ 2 - 2 * 1 ^ 2 = -1 := by norm_num
example : (7 : ℤ) ^ 2 - 2 * 5 ^ 2 = -1 := by norm_num
example : (41 : ℤ) ^ 2 - 2 * 29 ^ 2 = -1 := by norm_num

#check @negPell_step
#check @negPellSeq_norm
#check @negPellSeq_fst_strictMono
#check @negPell_solutions_infinite

end PellEquationOQ06
