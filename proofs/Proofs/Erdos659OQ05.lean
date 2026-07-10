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
    * `Q_eq_zero_iff`     : anisotropy — Q vanishes only at the origin (the norm
                            has trivial kernel, so `ℤ[√-2]` is a domain),
    * `Q_eq_one_iff`      : the units are `±1` — the only norm-1 vectors are `(±1,0)`,
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

/-- **Anisotropy (positive-definiteness).**  The form `Q(x, y) = x² + 2y²` vanishes
    *only* at the origin: `Q x y = 0 ↔ x = 0 ∧ y = 0`.  Equivalently the norm map
    `ℤ√(-2) → ℤ` has trivial kernel, which is the algebraic reason `ℤ[√-2]` is an
    integral domain — the multiplicative structure `Q_mul` never collapses a nonzero
    lattice vector to a zero distance. -/
theorem Q_eq_zero_iff (x y : ℤ) : Q x y = 0 ↔ x = 0 ∧ y = 0 := by
  unfold Q
  constructor
  · intro h
    have hx2 : (0 : ℤ) ≤ x ^ 2 := sq_nonneg x
    have hy2 : (0 : ℤ) ≤ y ^ 2 := sq_nonneg y
    have hxz : x ^ 2 = 0 := by omega
    have hyz : y ^ 2 = 0 := by omega
    exact ⟨pow_eq_zero_iff (by norm_num) |>.mp hxz,
           pow_eq_zero_iff (by norm_num) |>.mp hyz⟩
  · rintro ⟨rfl, rfl⟩; norm_num

/-- **The value `1` is represented only trivially — the unit group is `{±1}`.**
    `Q x y = 1 ↔ (x = 1 ∨ x = -1) ∧ y = 0`.  Since `2y² ≤ 1` forces `y = 0` and then
    `x² = 1` forces `x = ±1`, the only lattice vectors at squared distance `1` from the
    origin are `(±1, 0)`.  This is exactly the statement that the units of `ℤ[√-2]`
    (norm-`1` elements) are just `±1`, complementing the anisotropy `Q_eq_zero_iff`. -/
theorem Q_eq_one_iff (x y : ℤ) : Q x y = 1 ↔ (x = 1 ∨ x = -1) ∧ y = 0 := by
  unfold Q
  constructor
  · intro h
    have hx2 : (0 : ℤ) ≤ x ^ 2 := sq_nonneg x
    have hy2 : (0 : ℤ) ≤ y ^ 2 := sq_nonneg y
    have hyz : y ^ 2 = 0 := by omega
    have hxone : x ^ 2 = 1 := by omega
    have hy : y = 0 := pow_eq_zero_iff (by norm_num) |>.mp hyz
    have hfac : (x - 1) * (x + 1) = 0 := by linear_combination hxone
    rcases mul_eq_zero.mp hfac with hh | hh
    · exact ⟨Or.inl (by linarith), hy⟩
    · exact ⟨Or.inr (by linarith), hy⟩
  · rintro ⟨hx | hx, rfl⟩ <;> subst hx <;> norm_num

/-- **Strict positivity off the origin.**  Every nonzero lattice vector sits at a
    strictly positive squared distance from the origin: `Q x y > 0` whenever
    `(x, y) ≠ (0, 0)`.  A direct consequence of `isRepresented_nonneg` and the
    anisotropy `Q_eq_zero_iff`. -/
theorem Q_pos_of_ne (x y : ℤ) (h : ¬(x = 0 ∧ y = 0)) : 0 < Q x y := by
  rcases lt_or_eq_of_le (isRepresented_nonneg ⟨x, y, rfl⟩) with hlt | heq
  · exact hlt
  · exact absurd ((Q_eq_zero_iff x y).mp heq.symm) h

/-- **Multiplicative closure.**

The product of two integers represented by `Q` is again represented — the
algebraic mechanism behind the sparse distance spectrum of the lattice. -/
theorem isRepresented_mul {m n : ℤ} (hm : IsRepresented m) (hn : IsRepresented n) :
    IsRepresented (m * n) := by
  obtain ⟨a, b, rfl⟩ := hm
  obtain ⟨c, d, rfl⟩ := hn
  exact ⟨a * c - 2 * b * d, a * d + b * c, Q_mul a b c d⟩

/-- **Representability = being a norm of `ℤ[√-2]`.**

An integer `n` is represented by `Q(x, y) = x² + 2y²` if and only if it is the
`Zsqrtd` norm of some element of `ℤ√(-2)`.  This identifies the represented set
with the *image of the norm map* `ℤ√(-2) → ℤ`, and is the conceptual reason for
the multiplicative closure `isRepresented_mul`: `Zsqrtd.norm` is a monoid
homomorphism, so its image is closed under multiplication.  Concretely it upgrades
the coordinate-level composition law `Q_mul` to the statement that the represented
integers are exactly `Set.range (Zsqrtd.norm : ℤ√(-2) → ℤ)`. -/
theorem isRepresented_iff_isNorm {n : ℤ} :
    IsRepresented n ↔ ∃ z : ℤ√(-2), Zsqrtd.norm z = n := by
  constructor
  · rintro ⟨x, y, rfl⟩
    exact ⟨⟨x, y⟩, Q_eq_zsqrtd_norm x y⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z.re, z.im, (Q_eq_zsqrtd_norm z.re z.im).symm⟩

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
