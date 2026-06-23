/-
# Hilbert's Tenth Problem, degree 1: deciding linear *systems* via Smith normal form

Follow-up to `Hilbert10OQ04OQ03OQ02` (its open question oq-01).

The parent file `Hilbert10OQ04OQ03OQ02` reduced solvability of a linear system

  `A x = b`,  `A : Matrix (Fin m) (Fin n) ℤ`,  `b : Fin m → ℤ`,

to *membership of `b` in the ℤ-span of the columns of `A`* (`solvable_iff_mem_colSpan`),
and flagged the remaining step explicitly:

> "What is *not* claimed here is the full `Decidable` instance for `∃ x, A x = b`:
>  that requires turning column-span membership into invariant-factor divisibility
>  via the Smith normal form `U A V = D`."

This file supplies exactly that step for **square systems**. Smith normal form for an
`n × n` integer matrix `A` produces unimodular `U, V ∈ GLₙ(ℤ)` (matrices with two-sided
integer inverses) and a diagonal `D = diagonal d` of invariant factors with `U A V = D`.
We prove, *taking the Smith normal form as given data*:

* `diagonal_mulVec_solvable_iff` — the diagonal case: `(∃ x, diagonal d *ᵥ x = c) ↔ ∀ i, d i ∣ c i`.
  This is where invariant-factor divisibility enters; it is decidable on the nose.
* `solvable_iff_solvable_diagonal` — the **unimodular reduction**: if `U A V = diagonal d`
  with `U, V` invertible over `ℤ`, then `A x = b` is solvable iff the diagonalised system
  `diagonal d *ᵥ y = U *ᵥ b` is.
* `solvable_iff_invariantFactor_dvd` — composing the two: `(∃ x, A *ᵥ x = b) ↔ ∀ i, d i ∣ (U *ᵥ b) i`,
  i.e. solvability is decided by `n` divisibility tests on the transformed right-hand side `U b`.
* `decidableSolvableOfSmith` — the resulting `Decidable` instance for `∃ x, A *ᵥ x = b`,
  given a Smith normal form of `A`.

Together these complete the decision procedure *modulo the existence of the Smith normal form*.
Mathlib has the PID structure theory (`Module.Basis.SmithNormalForm`) but does not yet expose
a `Matrix`-level algorithm returning the unimodular `U, V` and the diagonal `D = U A V`; that
construction is the one remaining gap, and it is the sole input these results consume. The
rectangular `m ≠ n` case (rectangular-diagonal `D`, with zero rows forcing `cᵢ = 0`) is the
natural further generalisation.

Everything is `sorry`-free and `axiom`-free (only the foundational
`propext`/`Classical.choice`/`Quot.sound` are used; no `Lean.ofReduceBool`).
-/
import Mathlib

-- The four inverse hypotheses below assert `U, V ∈ GLₙ(ℤ)` (the unimodular data of a
-- Smith normal form); the reduction proof happens to consume only two of them.
set_option linter.unusedVariables false

open Matrix

namespace Hilbert10OQ04OQ03OQ02OQ01

variable {n : ℕ}

/-- **Diagonal case.** A diagonal integer system `diagonal d *ᵥ x = c` is solvable over `ℤ`
iff each diagonal entry divides the corresponding right-hand side: `∀ i, d i ∣ c i`. Each
coordinate decouples into the scalar equation `d i * xᵢ = c i`, whose solvability over `ℤ`
is precisely `d i ∣ c i`. This is the point at which *invariant-factor divisibility* enters
the decision procedure. -/
theorem diagonal_mulVec_solvable_iff (d c : Fin n → ℤ) :
    (∃ x : Fin n → ℤ, diagonal d *ᵥ x = c) ↔ ∀ i, d i ∣ c i := by
  constructor
  · rintro ⟨x, hx⟩ i
    refine ⟨x i, ?_⟩
    have h := congrFun hx i
    rw [mulVec_diagonal] at h
    exact h.symm
  · intro h
    refine ⟨fun i => (h i).choose, ?_⟩
    funext i
    rw [mulVec_diagonal]
    exact ((h i).choose_spec).symm

/-- **Unimodular reduction.** Let `U, V : Matrix (Fin n) (Fin n) ℤ` be invertible over `ℤ`
(`U * Ui = 1`, `Ui * U = 1`, and likewise for `V`), and suppose `U * A * V = diagonal d`
(a Smith normal form of the square matrix `A`). Then the system `A x = b` is solvable iff
the diagonalised system `diagonal d *ᵥ y = U *ᵥ b` is. The bijections `x ↦ Vi *ᵥ x` and
`y ↦ V *ᵥ y` transport solutions between the two systems. -/
theorem solvable_iff_solvable_diagonal
    (A : Matrix (Fin n) (Fin n) ℤ) (b d : Fin n → ℤ)
    (U Ui V Vi : Matrix (Fin n) (Fin n) ℤ)
    (hU : U * Ui = 1) (hUi : Ui * U = 1) (hV : V * Vi = 1) (hVi : Vi * V = 1)
    (hD : U * A * V = diagonal d) :
    (∃ x : Fin n → ℤ, A *ᵥ x = b) ↔ (∃ y : Fin n → ℤ, diagonal d *ᵥ y = U *ᵥ b) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨Vi *ᵥ x, ?_⟩
    -- `diagonal d *ᵥ (Vi x) = U A V *ᵥ (Vi x) = U *ᵥ (A *ᵥ (V *ᵥ (Vi *ᵥ x))) = U *ᵥ (A *ᵥ x) = U b`
    have hVx : V *ᵥ (Vi *ᵥ x) = x := by
      rw [mulVec_mulVec, hV, one_mulVec]
    calc diagonal d *ᵥ (Vi *ᵥ x)
        = (U * A * V) *ᵥ (Vi *ᵥ x) := by rw [hD]
      _ = U *ᵥ (A *ᵥ (V *ᵥ (Vi *ᵥ x))) := by
            rw [← mulVec_mulVec, ← mulVec_mulVec]
      _ = U *ᵥ (A *ᵥ x) := by rw [hVx]
      _ = U *ᵥ b := by rw [hx]
  · rintro ⟨y, hy⟩
    refine ⟨V *ᵥ y, ?_⟩
    -- `A x = (A V) *ᵥ y` and `A V = Ui * diagonal d`, so `A x = Ui *ᵥ (diagonal d *ᵥ y) = Ui U b = b`
    have hAV : A * V = Ui * diagonal d := by
      have : Ui * (U * A * V) = Ui * diagonal d := by rw [hD]
      rwa [← mul_assoc, ← mul_assoc, hUi, one_mul] at this
    calc A *ᵥ (V *ᵥ y)
        = (A * V) *ᵥ y := by rw [mulVec_mulVec]
      _ = (Ui * diagonal d) *ᵥ y := by rw [hAV]
      _ = Ui *ᵥ (diagonal d *ᵥ y) := by rw [← mulVec_mulVec]
      _ = Ui *ᵥ (U *ᵥ b) := by rw [hy]
      _ = (Ui * U) *ᵥ b := by rw [mulVec_mulVec]
      _ = b := by rw [hUi, one_mulVec]

/-- **Invariant-factor divisibility criterion.** Composing the unimodular reduction with the
diagonal case: given a Smith normal form `U A V = diagonal d` of the square matrix `A`
(`U, V` invertible over `ℤ`), the system `A x = b` is solvable over `ℤ` iff every invariant
factor `d i` divides the corresponding coordinate of the transformed right-hand side `U b`.
This turns column-lattice membership (the parent's `solvable_iff_mem_colSpan`) into `n`
divisibility tests. -/
theorem solvable_iff_invariantFactor_dvd
    (A : Matrix (Fin n) (Fin n) ℤ) (b d : Fin n → ℤ)
    (U Ui V Vi : Matrix (Fin n) (Fin n) ℤ)
    (hU : U * Ui = 1) (hUi : Ui * U = 1) (hV : V * Vi = 1) (hVi : Vi * V = 1)
    (hD : U * A * V = diagonal d) :
    (∃ x : Fin n → ℤ, A *ᵥ x = b) ↔ ∀ i, d i ∣ (U *ᵥ b) i :=
  (solvable_iff_solvable_diagonal A b d U Ui V Vi hU hUi hV hVi hD).trans
    (diagonal_mulVec_solvable_iff d (U *ᵥ b))

/-- **Decidability from a Smith normal form.** Given a Smith normal form `U A V = diagonal d`
of a square integer matrix `A` (with `U, V` invertible over `ℤ`), solvability of `A x = b`
over `ℤ` is decidable: run the `n` divisibility tests `d i ∣ (U *ᵥ b) i`. The only ingredient
not produced here is the Smith normal form itself; everything downstream is decidable. -/
def decidableSolvableOfSmith
    (A : Matrix (Fin n) (Fin n) ℤ) (b d : Fin n → ℤ)
    (U Ui V Vi : Matrix (Fin n) (Fin n) ℤ)
    (hU : U * Ui = 1) (hUi : Ui * U = 1) (hV : V * Vi = 1) (hVi : Vi * V = 1)
    (hD : U * A * V = diagonal d) :
    Decidable (∃ x : Fin n → ℤ, A *ᵥ x = b) :=
  decidable_of_iff (∀ i, d i ∣ (U *ᵥ b) i)
    (solvable_iff_invariantFactor_dvd A b d U Ui V Vi hU hUi hV hVi hD).symm

/-- Worked sanity check: the identity matrix is its own Smith normal form (`U = V = 1`,
`d = 1`), and `1 ∣ b i` always holds, so every system `x = b` is solvable — as it must be,
with `x = b`. -/
example (b : Fin n → ℤ) :
    (∃ x : Fin n → ℤ, (1 : Matrix (Fin n) (Fin n) ℤ) *ᵥ x = b) ↔
      ∀ i, (1 : Fin n → ℤ) i ∣ ((1 : Matrix (Fin n) (Fin n) ℤ) *ᵥ b) i := by
  have h1 : (1 : Matrix (Fin n) (Fin n) ℤ) * 1 * 1 = diagonal (1 : Fin n → ℤ) := by
    simp
  exact solvable_iff_invariantFactor_dvd 1 b 1 1 1 1 1
    (by simp) (by simp) (by simp) (by simp) h1

end Hilbert10OQ04OQ03OQ02OQ01
