/-
  Brahmagupta's Samasa Law and the Norm Form x² − N·y²
  Open Question: fermat-two-squares-oq-07-oq-01

  The parent entry (`FermatTwoSquaresOQ07`) develops Brahmagupta's identity for
  the *imaginary*-quadratic norm form x² + N·y² (the norm of ℤ[√−N]). Its
  historical and mathematical sibling is the *real*-quadratic samasa
  ("composition") law for x² − N·y² — the norm of ℤ[√N] — which Brahmagupta
  actually used in 628 AD to compose solutions of Pell's equation. Over any
  commutative ring the identity is

      (a² − N·b²)(c² − N·d²) = (ac + N·bd)² − N·(ad + bc)².

  This is precisely the multiplicativity of the norm N(x + y√N) = x² − N·y² on
  the quadratic ring ℤ[√N]. Its most famous consequence is the closure of the
  Pell solution set under composition: the solutions of x² − N·y² = 1 form a
  monoid (in fact a group), so a single solution generates infinitely many.

  Results proved here (for EVERY parameter N, over an arbitrary `CommRing`):
  • `brahmagupta_pell` / `brahmagupta_pell'` — the two sign-variant identities;
  • `normForm` (the `−N` form) and `normForm_mul` — norm-multiplicativity;
  • `pell_sol_mul` — closure of {x² − N·y² = 1} under composition (with identity
    solution (1,0), giving a commutative monoid);
  • `solution_mul` — the general multiplicative law: a norm-k₁ and a norm-k₂
    solution compose to a norm-(k₁·k₂) solution;
  • `neg_pell_compose` — two solutions of x² − N·y² = −1 compose to one of = 1
    (sign multiplicativity of the norm, (−1)·(−1) = 1);
  • `pell_square` — the explicit doubling formula (a,b) ↦ (a² + N·b², 2ab);
  • concrete witnesses over ℤ for N = 2: (3,2) solves x² − 2y² = 1, and its
    Brahmagupta square is exactly (17,12), which also solves it.

  This complements the parent's `+N` skeleton, giving an *elementary* witness for
  Pell-solution closure that does not unfold Mathlib's `Zsqrtd`/`Pell.Solution₁`
  machinery, and supplies the concrete composition coordinates a textbook writes.

  References:
  - Brahmagupta (628 AD), Brāhmasphuṭasiddhānta: the samasa law for x² − Ny².
  - A. Weil, Number Theory: An Approach Through History (1984).
  - FermatTwoSquaresOQ07.lean: the `+N` sibling (norm of ℤ[√−N]).
-/

import Mathlib.Tactic

namespace FermatTwoSquaresOQ07OQ01

/-! ### The samasa (composition) identity for x² − N·y² -/

/-- **Brahmagupta's samasa law** for the form `x² − N·y²`, in any commutative
ring. This is the multiplicativity of the norm on `ℤ[√N]`:

    (a² − N·b²)(c² − N·d²) = (ac + N·bd)² − N·(ad + bc)². -/
theorem brahmagupta_pell {R : Type*} [CommRing R] (N a b c d : R) :
    (a ^ 2 - N * b ^ 2) * (c ^ 2 - N * d ^ 2) =
      (a * c + N * b * d) ^ 2 - N * (a * d + b * c) ^ 2 := by
  ring

/-- The conjugate sign variant of the samasa law:

    (a² − N·b²)(c² − N·d²) = (ac − N·bd)² − N·(ad − bc)².

Choosing `d ↦ −d` swaps the two variants; both land in the represented set, the
source of multiple representations. -/
theorem brahmagupta_pell' {R : Type*} [CommRing R] (N a b c d : R) :
    (a ^ 2 - N * b ^ 2) * (c ^ 2 - N * d ^ 2) =
      (a * c - N * b * d) ^ 2 - N * (a * d - b * c) ^ 2 := by
  ring

/-! ### The norm form and its multiplicativity -/

/-- The real-quadratic norm form `f_N(x, y) = x² − N·y²` — the norm of
`x + y√N` in `ℤ[√N]`. -/
def normForm (N x y : ℤ) : ℤ := x ^ 2 - N * y ^ 2

/-- **The norm form is multiplicative.** The product of two values of `f_N` is
again a value of `f_N`, with explicit composition law on the arguments. This is
the elementary, parameter-explicit form of `Zsqrtd.norm_mul`. -/
theorem normForm_mul (N a b c d : ℤ) :
    normForm N a b * normForm N c d =
      normForm N (a * c + N * b * d) (a * d + b * c) := by
  simp only [normForm]
  ring

/-! ### Closure of the solution set under composition -/

/-- `IsSolution N k a b` means `(a, b)` solves `x² − N·y² = k`. -/
def IsSolution (N k a b : ℤ) : Prop := a ^ 2 - N * b ^ 2 = k

/-- **General multiplicative law.** A norm-`k₁` solution and a norm-`k₂` solution
compose, via Brahmagupta's coordinates, to a norm-`(k₁ · k₂)` solution. -/
theorem solution_mul {N k₁ k₂ a b c d : ℤ}
    (h₁ : IsSolution N k₁ a b) (h₂ : IsSolution N k₂ c d) :
    IsSolution N (k₁ * k₂) (a * c + N * b * d) (a * d + b * c) := by
  unfold IsSolution at *
  rw [← h₁, ← h₂]; ring

/-- **Closure of the Pell solution set under composition.** If `(a,b)` and
`(c,d)` both solve `x² − N·y² = 1`, then so does the Brahmagupta composite
`(ac + N·bd, ad + bc)`. -/
theorem pell_sol_mul {N a b c d : ℤ}
    (h₁ : a ^ 2 - N * b ^ 2 = 1) (h₂ : c ^ 2 - N * d ^ 2 = 1) :
    (a * c + N * b * d) ^ 2 - N * (a * d + b * c) ^ 2 = 1 := by
  have := solution_mul (N := N) (k₁ := 1) (k₂ := 1) h₁ h₂
  simpa [IsSolution] using this

/-- The identity solution `(1, 0)` solves `x² − N·y² = 1`, so the Pell solution
set is a (commutative) monoid under Brahmagupta composition. -/
theorem pell_sol_one (N : ℤ) : IsSolution N 1 1 0 := by
  unfold IsSolution; ring

/-- **Negative-Pell composition.** Two solutions of `x² − N·y² = −1` compose to a
solution of `x² − N·y² = 1`, since `(−1)·(−1) = 1`. This is the sign
multiplicativity of the norm. -/
theorem neg_pell_compose {N a b c d : ℤ}
    (h₁ : a ^ 2 - N * b ^ 2 = -1) (h₂ : c ^ 2 - N * d ^ 2 = -1) :
    (a * c + N * b * d) ^ 2 - N * (a * d + b * c) ^ 2 = 1 := by
  have := solution_mul (N := N) (k₁ := -1) (k₂ := -1) h₁ h₂
  simpa [IsSolution] using this

/-! ### The doubling formula -/

/-- **Doubling formula.** Composing a solution with itself sends `(a, b)` to
`(a² + N·b², 2ab)` and squares the norm: if `a² − N·b² = k` then
`(a² + N·b²)² − N·(2ab)² = k²`. Iterating this is how one solution of Pell's
equation generates infinitely many. -/
theorem pell_square {N k a b : ℤ} (h : a ^ 2 - N * b ^ 2 = k) :
    (a ^ 2 + N * b ^ 2) ^ 2 - N * (2 * a * b) ^ 2 = k ^ 2 := by
  rw [← h]; ring

/-- The doubling coordinates are the diagonal `c = a, d = b` of Brahmagupta's
composition: `(ac + N·bd, ad + bc) = (a² + N·b², 2ab)`. -/
theorem pell_square_coords (N a b : ℤ) :
    (a * a + N * b * b, a * b + b * a) = (a ^ 2 + N * b ^ 2, 2 * a * b) := by
  simp only [Prod.mk.injEq]; exact ⟨by ring, by ring⟩

/-! ### Concrete witnesses over ℤ for N = 2

The fundamental solution of `x² − 2y² = 1` is `(3, 2)` (since `9 − 8 = 1`). Its
Brahmagupta square is `(3² + 2·2², 2·3·2) = (17, 12)`, and indeed
`17² − 2·12² = 289 − 288 = 1`. -/

/-- `(3, 2)` solves `x² − 2y² = 1`. -/
theorem three_two_sol : (3 : ℤ) ^ 2 - 2 * 2 ^ 2 = 1 := by decide

/-- `(17, 12)` solves `x² − 2y² = 1`. -/
theorem seventeen_twelve_sol : (17 : ℤ) ^ 2 - 2 * 12 ^ 2 = 1 := by decide

/-- The doubling formula applied to `(3, 2)` yields exactly `(17, 12)`. -/
theorem three_two_square_is_seventeen_twelve :
    ((3 : ℤ) ^ 2 + 2 * 2 ^ 2, 2 * 3 * 2) = (17, 12) := by decide

/-- The square of `(3, 2)` solves `x² − 2y² = 1`, recovered purely from the
composition machinery: `three_two_sol` fed through `pell_square` gives a norm of
`1² = 1` at the coordinates `(17, 12)`. -/
theorem three_two_square_sol :
    ((3 : ℤ) ^ 2 + 2 * 2 ^ 2) ^ 2 - 2 * (2 * 3 * 2) ^ 2 = 1 := by
  have h := pell_square (N := 2) (k := 1) (a := 3) (b := 2) three_two_sol
  simp only [one_pow] at h; exact h

end FermatTwoSquaresOQ07OQ01
