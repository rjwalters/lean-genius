/-
  Erdős Problem #659 — open question oq-05.

  Parent (erdos-659): the Moree–Osburn construction places n points in ℝ² so
  that every 4-point subset determines ≥ 3 distances, while the total number of
  distinct distances is O(n / √log n). The points lie on the lattice
  { (x, y·√2) : x, y ∈ ℤ }, so a squared distance between two of them is an
  integer of the binary quadratic form

      Q(x, y) = x² + 2y²      (the norm form of ℤ[√-2]).

  oq-05 asks: can the construction be formalized in Lean *without axioms*, by
  proving Landau's theorem (the asymptotic density of integers represented by
  this form) purely in Mathlib? Landau's density theorem is a deep analytic
  result that is NOT yet available in Mathlib, so the full program remains open.

  This file contributes, *axiom-free and sorry-free*, a foundational algebraic
  layer of that program — the multiplicative (norm-form) structure of Q:

    * `Q_mul`             : the Brahmagupta composition law for D = 2,
    * `Q_eq_zsqrtd_norm`  : Q is exactly the norm of `ℤ√(-2)`,
    * `isRepresented_mul` : the integers represented by Q are closed under
                            multiplication (a submonoid of (ℤ, ·)),
    * `dist_sq_lattice`   : the squared Euclidean distance between two lattice
                            points equals Q of the coordinate differences.

  The multiplicativity of Q is precisely the algebraic engine behind the sparse
  distance spectrum that Landau's theorem quantifies; making it rigorous is a
  concrete, verified step toward the axiom-free formalization oq-05 requests.
  The remaining analytic density statement is the genuinely open part.
-/

import Mathlib

namespace Erdos659OQ05

open scoped BigOperators

/-- The binary quadratic form `Q(x, y) = x² + 2y²`. -/
def Q (x y : ℤ) : ℤ := x ^ 2 + 2 * y ^ 2

/-- An integer is *represented* by `Q` if `n = x² + 2y²` for some integers `x, y`. -/
def IsRepresented (n : ℤ) : Prop := ∃ x y : ℤ, n = Q x y

/-- **Composition law (Brahmagupta identity for `D = 2`).**

`(a² + 2b²)(c² + 2d²) = (ac - 2bd)² + 2(ad + bc)²`. -/
theorem Q_mul (a b c d : ℤ) :
    Q a b * Q c d = Q (a * c - 2 * b * d) (a * d + b * c) := by
  unfold Q; ring

/-- `Q` is exactly the norm form of `ℤ[√-2]`:
`norm (⟨x, y⟩ : ℤ√(-2)) = x² + 2y²`. -/
theorem Q_eq_zsqrtd_norm (x y : ℤ) :
    Zsqrtd.norm (⟨x, y⟩ : ℤ√(-2)) = Q x y := by
  rw [Zsqrtd.norm_def, Q]; ring

/-- `0` is represented: `Q 0 0 = 0`. -/
theorem isRepresented_zero : IsRepresented 0 := ⟨0, 0, by decide⟩

/-- `1` is represented: `Q 1 0 = 1`. -/
theorem isRepresented_one : IsRepresented 1 := ⟨1, 0, by decide⟩

/-- `2` is represented: `Q 0 1 = 2`. -/
theorem isRepresented_two : IsRepresented 2 := ⟨0, 1, by decide⟩

/-- Represented integers are nonnegative (squared distances cannot be negative). -/
theorem isRepresented_nonneg {n : ℤ} (hn : IsRepresented n) : 0 ≤ n := by
  obtain ⟨x, y, rfl⟩ := hn
  unfold Q; positivity

/-- **Multiplicative closure.**

The product of two integers represented by `Q` is again represented — the
algebraic mechanism behind the sparse distance spectrum of the lattice. -/
theorem isRepresented_mul {m n : ℤ} (hm : IsRepresented m) (hn : IsRepresented n) :
    IsRepresented (m * n) := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  exact ⟨a * c - 2 * b * d, a * d + b * c, Q_mul a b c d⟩

/-- The integers represented by `Q` form a submonoid of `(ℤ, ·)`. -/
def representedSubmonoid : Submonoid ℤ where
  carrier := {n | IsRepresented n}
  one_mem' := isRepresented_one
  mul_mem' := isRepresented_mul

@[simp] theorem mem_representedSubmonoid {n : ℤ} :
    n ∈ representedSubmonoid ↔ IsRepresented n := Iff.rfl

/-- A finite product of represented integers is represented. -/
theorem isRepresented_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ)
    (hf : ∀ i ∈ s, IsRepresented (f i)) : IsRepresented (∏ i ∈ s, f i) :=
  Finset.prod_induction f IsRepresented (fun _ _ => isRepresented_mul)
    isRepresented_one hf

/-- The Moree–Osburn lattice point attached to integer coordinates `(x, y)`:
the point `(x, y·√2) ∈ ℝ²`. -/
noncomputable def latticePoint (x y : ℤ) : ℝ × ℝ := ((x : ℝ), (y : ℝ) * Real.sqrt 2)

/-- **Geometric link.**

The squared Euclidean distance between two lattice points equals `Q` of the
coordinate differences:

`|P(x₁,y₁) - P(x₂,y₂)|² = (x₁-x₂)² + 2(y₁-y₂)² = Q(x₁-x₂, y₁-y₂)`.

Hence the squared distances occurring in the lattice are exactly the integers
represented by `Q`, which (by `isRepresented_mul`) form a multiplicatively
closed set. -/
theorem dist_sq_lattice (x₁ y₁ x₂ y₂ : ℤ) :
    ((latticePoint x₁ y₁).1 - (latticePoint x₂ y₂).1) ^ 2
      + ((latticePoint x₁ y₁).2 - (latticePoint x₂ y₂).2) ^ 2
      = ((Q (x₁ - x₂) (y₁ - y₂) : ℤ) : ℝ) := by
  have hsqrt : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  dsimp only [latticePoint, Q]
  push_cast
  have key : ((y₁ : ℝ) * Real.sqrt 2 - (y₂ : ℝ) * Real.sqrt 2) ^ 2
           = 2 * ((y₁ : ℝ) - (y₂ : ℝ)) ^ 2 := by
    have hfac : (y₁ : ℝ) * Real.sqrt 2 - (y₂ : ℝ) * Real.sqrt 2
              = ((y₁ : ℝ) - (y₂ : ℝ)) * Real.sqrt 2 := by ring
    rw [hfac, mul_pow, hsqrt]; ring
  rw [key]

end Erdos659OQ05
