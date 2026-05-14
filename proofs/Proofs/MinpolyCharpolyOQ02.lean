import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Semisimple
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Tactic
import Proofs.MinpolyCharpoly

/-
# Diagonalizable Matrices via Squarefree Minimal Polynomial

## Open Question (minpoly-charpoly-oq-02)

> Can the diagonalizability characterisation
> `M ∈ Matₙ(F) diagonalizable ⇔ minpoly M ∈ F[X] is squarefree (and splits in F)`
> be formalized in Lean 4 using this infrastructure?

This is `conclusion.openQuestions[1]` of the parent gallery entry
`minpoly-charpoly` (Minimal Polynomial vs Characteristic Polynomial of
Matrices — 17 theorems, 0 axioms). Sibling open questions:

* OQ-01 (Jordan normal form — scaffolded in `MinpolyCharpolyOQ01.lean`)
* OQ-03 (rational canonical form — scaffolded in `MinpolyCharpolyOQ03.lean`)

## Resolution (S1 OBSERVE — affirmative, no Mathlib gap)

**Yes, the diagonalizability characterisation is formalizable in Lean 4**
directly via the Mathlib `Module.End.IsSemisimple` API. The "diagonalizable"
side decomposes into "semisimple + minpoly splits", and both halves of the
biconditional are already in Mathlib `v4.26.0`:

1. **`Module.End.IsSemisimple` ↔ `Squarefree (minpoly K f)`** for a finite
   `K`-module endomorphism `f` over a field `K` of characteristic 0
   (or, more generally, when `minpoly K f` is separable). The forward
   direction is `Module.End.isSemisimple_iff_squarefree_minpoly` in
   `Mathlib.LinearAlgebra.Semisimple`.

2. **`Module.End.IsSemisimple` + minpoly splits → diagonalizable.** Over an
   algebraically closed field this is automatic; over a general field one
   needs `Polynomial.Splits (algebraMap K K) (minpoly K f)`. The composite
   "splits-and-semisimple = diagonalizable" is the operator-theoretic
   characterisation: under both hypotheses, the eigenspace decomposition
   `⨁ λ, eigenspace f λ = ⊤` holds and gives an eigenbasis.

3. **Matrix ↔ endomorphism transport.** Identifying a matrix
   `M : Matrix n n K` with the endomorphism `Matrix.toLin' M` carries the
   minpoly across (`Matrix.minpoly_toLin'`) and lets us read the
   diagonalizability claim back in matrix language.

**No Mathlib gap is required.** The remaining work for OQ-02 is purely
*integrative*: assemble these three pieces into the headline matrix-level
statement.

## Decomposition into Sub-OQs (proposed)

| Sub-OQ        | Content                                                                   | Estimated lines |
|---------------|---------------------------------------------------------------------------|-----------------|
| **OQ-02-OQ-01** | Bridge `Module.End.IsSemisimple` ↔ `Squarefree (minpoly K f)` to matrices | ~100            |
| **OQ-02-OQ-02** | "Diagonalizable" predicate on matrices + alg-closed unconditional form    | ~150            |
| **OQ-02-OQ-03** | General-field form with explicit `splits` hypothesis                       | ~120            |
| **OQ-02-OQ-04** | Char-0 specialisation: minpoly is automatically separable                  | ~80             |

Total roadmap: ≈ 450 lines (smaller than OQ-01 / OQ-03; the
`Module.End.IsSemisimple` API absorbs most of the work).

## What This File Contributes (S1 scaffold)

* **`Matrix.IsDiagonalizable`** — the matrix-level predicate: `M` is similar
  to a diagonal matrix over `K`, i.e. `∃ (P : Matrix n n K), P.Invertible ∧
  IsDiag (P⁻¹ * M * P)`. Mirrors the structure of `Matrix.IsDiag` from
  Mathlib but as an existential over similarity transforms.
* **`diagonalizable_iff_squarefree_minpoly`** — the **main theorem
  statement**, guarded by a single `sorry`. Reads:
  `IsAlgClosed K → CharZero K → (M.IsDiagonalizable ↔ Squarefree (minpoly K M))`.
  The four sub-OQs above are designed to discharge it.
* **`Matrix.IsDiagonalizable.of_isDiag`** — sanity lemma (unconditional): any
  diagonal matrix is diagonalizable (take `P = 1`).
* **`Matrix.IsDiagonalizable.zero`** — sanity lemma (unconditional): the zero
  matrix is diagonalizable.

## Why this scaffold

We follow the same S1 OBSERVE pattern used in sibling files
`MinpolyCharpolyOQ01.lean` (JNF) and `MinpolyCharpolyOQ03.lean` (RCF):
state the headline theorem with a single `sorry`, document the resolution
strategy, and provide a couple of unconditional sanity helpers so the file
exposes a non-trivial public surface even before the discharge work
begins. The four sub-OQs are the natural follow-up iterations.
-/

namespace Proofs.MinpolyCharpolyOQ02

open Matrix Polynomial

variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

/-- A square matrix `M` is **diagonalizable** if it is similar to a diagonal
matrix: there is an invertible matrix `P` over `K` such that `P⁻¹ * M * P`
is a diagonal matrix.

This is the matrix-level predicate corresponding to
`Module.End.IsSemisimple ∧ Polynomial.Splits` for the associated
endomorphism. -/
def _root_.Matrix.IsDiagonalizable (M : Matrix n n K) : Prop :=
  ∃ P : Matrix n n K, IsUnit P ∧ IsDiag (P⁻¹ * M * P)

/-- **S1 OBSERVE main theorem (statement only).** Over an algebraically
closed field of characteristic zero, a matrix is diagonalizable iff its
minimal polynomial is squarefree. The four sub-OQs (OQ-02-OQ-01 ..
OQ-02-OQ-04) are designed to discharge the `sorry`.

Note: the field hypotheses can be weakened to "perfect field + minpoly
splits", but the alg-closed-char-0 case is the headline textbook statement
and is what most callers (e.g. linear-algebra texts) expect. The general
form is the target of OQ-02-OQ-03. -/
theorem diagonalizable_iff_squarefree_minpoly
    [IsAlgClosed K] [CharZero K] (M : Matrix n n K) :
    M.IsDiagonalizable ↔ Squarefree (minpoly K M) := by
  sorry

/-- **Sanity lemma (unconditional).** A diagonal matrix is diagonalizable —
take `P = 1` as the similarity transform. -/
theorem _root_.Matrix.IsDiagonalizable.of_isDiag {M : Matrix n n K}
    (hM : IsDiag M) : M.IsDiagonalizable := by
  refine ⟨1, isUnit_one, ?_⟩
  simpa [inv_one, Matrix.one_mul, Matrix.mul_one] using hM

/-- **Sanity lemma (unconditional).** The zero matrix is diagonalizable. -/
theorem _root_.Matrix.IsDiagonalizable.zero :
    (0 : Matrix n n K).IsDiagonalizable :=
  Matrix.IsDiagonalizable.of_isDiag Matrix.isDiag_zero

end Proofs.MinpolyCharpolyOQ02
