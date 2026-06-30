/-
# Hilbert's Tenth Problem, degree 1: linear *systems* over ℤ

Follow-up to `Hilbert10OQ04OQ03` (open question oq-02).

The parent file `Hilbert10OQ04OQ03` decided solvability of a *single* linear
Diophantine equation `∑ aᵢ xᵢ = b` over `ℤ` by one gcd-divisibility test, and
packaged it as a `Decidable` instance. This file takes the first structural step
toward deciding a whole **system**

  `A x = b`,  `A : Matrix (Fin m) (Fin n) ℤ`,  `b : Fin m → ℤ`,

by reducing its solvability to a *membership question in the ℤ-span of the columns
of `A`* — the precise form in which Mathlib's PID structure theory
(`Module.Basis.SmithNormalForm`) is phrased.

Results:

* `solvable_iff_mem_range`  — `(∃ x, A *ᵥ x = b) ↔ b ∈ LinearMap.range A.mulVecLin`;
* `solvable_iff_mem_colSpan` — `(∃ x, A *ᵥ x = b) ↔ b ∈ span ℤ (range A.col)`,
  the **column-span bridge** (a specialization of `Matrix.range_mulVecLin`); the
  right-hand side is a finitely generated `ℤ`-submodule of `Fin m → ℤ`, exactly the
  object on which `Module.Basis.SmithNormalForm` operates;
* `solvable_single_row_iff_sum` — for `m = 1` the matrix system collapses to the
  scalar equation `∑ j, a j * x j = b`, the hypothesis form of the parent's
  `solvable_iff_gcd_dvd`; composing with the parent recovers the gcd criterion and
  confirms consistency across the two gallery entries.

What is *not* claimed here is the full `Decidable` instance for `∃ x, A x = b`:
that requires turning column-span membership into invariant-factor divisibility via
the Smith normal form `U A V = D`, an algorithm not yet wired into this development.
The bridge below is the reduction that decidability step starts from.

Everything is `sorry`-free and `axiom`-free (only the foundational
`propext`/`Classical.choice`/`Quot.sound` are used; no `Lean.ofReduceBool`).
-/
import Mathlib

open Matrix Submodule Set

namespace Hilbert10OQ04OQ03OQ02

variable {m n : ℕ}

/-- **Solvability as range membership.** The linear system `A x = b` over `ℤ` is
solvable iff `b` lies in the range of the linear map `x ↦ A *ᵥ x`. This is just the
definitional unfolding of `LinearMap.range`, recorded as the entry point to the
structural reformulation. -/
theorem solvable_iff_mem_range (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    (∃ x : Fin n → ℤ, A *ᵥ x = b) ↔ b ∈ LinearMap.range A.mulVecLin := by
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply]

/-- **Column-span bridge.** The system `A x = b` is solvable over `ℤ` iff `b` lies in
the `ℤ`-span of the columns of `A`. The right-hand side is a finitely generated
submodule of `Fin m → ℤ`, the setting of Mathlib's Smith-normal-form structure
theory `Module.Basis.SmithNormalForm`; this lemma is the reduction that a
`Decidable` instance for system solvability would build upon. -/
theorem solvable_iff_mem_colSpan (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) :
    (∃ x : Fin n → ℤ, A *ᵥ x = b) ↔ b ∈ span ℤ (range A.col) := by
  rw [solvable_iff_mem_range, Matrix.range_mulVecLin]

/-- **Single-row reduction.** For one equation (`m = 1`) the matrix system
`(of fun _ => a) *ᵥ x = (fun _ => b)` is solvable iff the scalar Diophantine equation
`∑ j, a j * x j = b` is — the exact hypothesis form of the parent file's
`Hilbert10OQ04OQ03.solvable_iff_gcd_dvd`. Composing this equivalence with the parent
shows the single-row instance of the system criterion is decided by `gcd a ∣ b`,
confirming the two gallery entries agree on their overlap. -/
theorem solvable_single_row_iff_sum (a : Fin n → ℤ) (b : ℤ) :
    (∃ x : Fin n → ℤ, (Matrix.of fun _ : Fin 1 => a) *ᵥ x = fun _ => b)
      ↔ (∃ x : Fin n → ℤ, ∑ j, a j * x j = b) := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    have := congrFun hx 0
    simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using this
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    funext i
    fin_cases i
    simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using hx

/-- Worked instance: the `2 × 2` system
`x + 2y = 5`, `3x + 4y = 11` is solvable, with witness `(x, y) = (1, 2)`
(`1 + 4 = 5`, `3 + 8 = 11`). Demonstrates the system statement is non-vacuous. -/
example :
    ∃ x : Fin 2 → ℤ,
      (Matrix.of ![![1, 2], ![3, 4]] : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ x
        = ![5, 11] := by
  refine ⟨![1, 2], ?_⟩
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.of_apply]

end Hilbert10OQ04OQ03OQ02
