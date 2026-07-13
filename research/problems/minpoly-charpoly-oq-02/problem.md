# Problem: Diagonalizable matrices via squarefree minimal polynomial

## Statement

### Plain Language

For an `n × n` matrix `A` over a field `K`, the following are
equivalent (under appropriate splitting hypotheses):

1. `A` is diagonalizable — there exists an invertible matrix `P` with
   `P⁻¹ A P` diagonal;
2. The minimal polynomial `minpoly K A` is **squarefree** (no repeated
   irreducible factors) **and** splits into linear factors over `K`.

Over an **algebraically closed** field (or more generally, when
`minpoly K A` already splits over `K`), condition (2) collapses to
plain *squarefreeness* of the minimal polynomial.

### Formal Statement Targets

For an arbitrary base field `K`:

```lean
-- The "matrix-level diagonalizability" predicate (definition):
def Matrix.IsDiagonalizable {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K] (A : Matrix n n K) : Prop :=
  ∃ (P : Matrix n n K), IsUnit P ∧ (P⁻¹ * A * P).IsDiag

-- The endomorphism bridge (already in-tree at OQ01):
theorem isSemisimple_iff_squarefree_minpoly
    [FiniteDimensional K V] {f : Module.End K V} :
    f.IsSemisimple ↔ Squarefree (minpoly K f) := …

-- The OQ-02 deliverable (matrix-level, with splitting):
theorem isDiagonalizable_iff_squarefree_and_splits
    {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K] (A : Matrix n n K) :
    A.IsDiagonalizable ↔
      Squarefree (minpoly K A) ∧ (minpoly K A).Splits (RingHom.id K)
    := sorry

-- Algebraically-closed corollary:
theorem isDiagonalizable_iff_squarefree
    {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [Field K] [IsAlgClosed K] (A : Matrix n n K) :
    A.IsDiagonalizable ↔ Squarefree (minpoly K A) := sorry
```

## Classification

```yaml
tier: B
significance: 7
tractability: 6
tags:
  - seeker-selected
  - linear-algebra
  - matrices
  - minimal-polynomial
  - diagonalization
  - cayley-hamilton
```

**Significance**: 7/10 — A staple of any introductory linear-algebra
course; the "natural counterpart" to the parent gallery proof
(`minpoly-charpoly`). Closes one of the parent's three explicit open
questions (`openQuestions[1]`).

**Tractability**: 6/10 — The endomorphism case is already proven in
the gallery (`isSemisimple_iff_squarefree_minpoly` in
`CayleyHamiltonMinpolyOQ01.lean:207`) via Mathlib's
`IsSemisimple.minpoly_squarefree` and
`isSemisimple_of_squarefree_aeval_eq_zero`. The remaining work is the
**translation layer** from a matrix `A : Matrix n n K` to its
left-multiplication endomorphism `Matrix.toLin' A : (n → K) →ₗ[K] (n → K)`,
plus the bridge from "semisimple endomorphism" to "diagonalizable
matrix" (which requires the splitting hypothesis or algebraic
closure). All ingredients are in Mathlib at the pinned revision.

## Why This Matters

1. **Parent open question closure.** `minpoly-charpoly` (the parent)
   has three explicit open questions; OQ-01 (Jordan normal form) and
   OQ-03 (rational canonical form) are already scaffolded with S1
   surveys (`MinpolyCharpolyOQ01.lean`, `MinpolyCharpolyOQ03.lean`).
   OQ-02 is the missing third sibling and the **cleanest** of the
   three: no nilpotent canonical form needed, no Smith normal form
   needed — just the minpoly-squarefree characterization plus a
   splitting hypothesis.

2. **Mathlib `IsSemisimple` is already strong.** The Mathlib
   abstraction `Module.End.IsSemisimple` factors the conceptual
   content out of "diagonalizable" (which is field-dependent) into a
   field-agnostic property (semisimplicity = the action decomposes as
   a direct sum of simple submodules). The biconditional with
   squarefree minpoly is what gives the *computable* criterion. This
   OQ packages that biconditional in matrix language.

3. **Decoupling from Jordan/RCF tracks.** Both OQ-01 (Jordan) and
   OQ-03 (RCF) require either a `JordanBlock` constructor (not in
   Mathlib at v4.26.0) or a Smith-normal-form-style invariant-factor
   decomposition (which routes through `Module.equiv_directSum_of_isTorsion`
   but is structurally heavier). OQ-02 needs neither — diagonalizability
   reduces to semisimplicity-plus-splitting at the abstract level, and
   the matrix-level translation is a packaging exercise. This makes
   OQ-02 substantially more tractable than its two siblings.

## The Splitting Subtlety

**Caveat to the question as stated**: The original problem-statement
claim "A is diagonalizable iff `minpoly A` is squarefree" is
**incomplete** outside of algebraically closed fields. Counterexample:
the `ℝ`-rotation matrix
```
A = [0 -1]
    [1  0]
```
has `minpoly ℝ A = X² + 1`, which is squarefree (it is
irreducible) but **does not split over `ℝ`**. The matrix `A` is
*not* diagonalizable over `ℝ` (its eigenvalues are `±i ∉ ℝ`), even
though `A.toLin'` is semisimple as an `ℝ`-endomorphism — because the
`ℝ`-irreducible factor `X² + 1` corresponds to a simple 2-dimensional
`ℝ`-submodule that is *not* a 1-eigenspace.

This is **not** a bug in the equivalence "semisimple ↔ squarefree minpoly"
(which holds over any field), but rather reflects that "diagonalizable"
is strictly stronger than "semisimple" over non-algebraically-closed
fields. The correct universal characterization is:

> `A` is diagonalizable ↔ `minpoly K A` is squarefree **and**
> `(minpoly K A).Splits (RingHom.id K)`.

Over algebraically closed `K`, splitting is automatic for any
polynomial, so the splitting clause is vacuous and the bare
"squarefree" criterion suffices. **Over a perfect non-algebraically-closed
field, both conditions are needed.**

The question's parenthetical "(F algebraically closed of char 0, or
more generally a perfect field)" appears to conflate "perfect" with
"algebraically closed". *Every* perfect field is the setting where
semisimplicity of `A.toLin'` is equivalent to squarefreeness of
`minpoly A`, *but* diagonalizability further requires splitting.

The S1 OBSERVE deliverable identifies this subtlety and refines the
S2+ targets accordingly: the **two-clause** characterization
(squarefree + splits) is the universal statement, and the
**one-clause** characterization (squarefree alone) is its algebraically
closed corollary.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `minpoly-charpoly` (parent) | Provides 17 theorems on minpoly/charpoly relationship; `openQuestions[1]` is OQ-02. |
| `minpoly-charpoly-oq-01` (sibling) | Jordan normal form; provides `MinpolyCharpolyOQ01.lean` (entry-wise Jordan block API + abstract S1 scaffold). |
| `minpoly-charpoly-oq-03` (sibling) | Rational canonical form; provides `MinpolyCharpolyOQ03.lean` (`InvariantFactorChain` data structure + abstract RCF main statement). |
| `cayley-hamilton-minpoly-oq-01` | **Provides the endomorphism-level theorem** `isSemisimple_iff_squarefree_minpoly` in `CayleyHamiltonMinpolyOQ01.lean:206-211` (proven via `IsSemisimple.minpoly_squarefree` + `isSemisimple_of_squarefree_aeval_eq_zero`). This is the load-bearing input for OQ-02. |
| `cayley-hamilton-minpoly` | Provides `Matrix.minpoly_dvd_charpoly` (the Cayley–Hamilton-style divisibility); useful for relating `Matrix n n K`-level minpoly to the endomorphism `Matrix.toLin' A`. |

## Mathlib Infrastructure Map

| Need | Mathlib name (Lean 4, v4.26.0) | Module |
|------|-------------------------------|--------|
| `Matrix.IsDiag` (definition) | `Matrix.IsDiag` | `Mathlib.LinearAlgebra.Matrix.IsDiag` |
| Matrix → endomorphism bridge | `Matrix.toLin'` | `Mathlib.LinearAlgebra.Matrix.ToLin` |
| `Module.End.IsSemisimple` | `Module.End.IsSemisimple` | `Mathlib.LinearAlgebra.Semisimple` |
| Semisimple ⇒ squarefree minpoly | `Module.End.IsSemisimple.minpoly_squarefree` | `Mathlib.LinearAlgebra.Semisimple` |
| Squarefree minpoly ⇒ semisimple | `Module.End.isSemisimple_of_squarefree_aeval_eq_zero` | `Mathlib.LinearAlgebra.Semisimple` |
| Polynomial.Splits | `Polynomial.Splits` | `Mathlib.FieldTheory.Splitting` |
| Algebraically closed ⇒ all splits | `IsAlgClosed.splits` / `IsAlgClosed.splits_iff` | `Mathlib.FieldTheory.IsAlgClosed.Basic` |
| Similar matrices (conjugation) | `Matrix.Similar` (if available) or via `IsConj` | `Mathlib.LinearAlgebra.Matrix.…` |
| Diagonal matrix constructor | `Matrix.diagonal` | `Mathlib.Data.Matrix.Basic` |
| `minpoly` for matrices | `minpoly K A` (default via `Matrix.toLin' A`) | `Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly` |
| `Polynomial.Squarefree` | `Polynomial.Squarefree` / `Squarefree` | `Mathlib.RingTheory.UniqueFactorizationDomain` |

The gallery's `CayleyHamiltonMinpolyOQ01.lean:206-211` already wires
together the two Mathlib semisimple lemmas into the biconditional
`isSemisimple_iff_squarefree_minpoly`. OQ-02 inherits this and adds
only the matrix-level packaging.

## Suggested Sub-OQ Decomposition

For follow-up iterations / child OQs, the work decomposes naturally:

| Sub-OQ | Content | Est. lines |
|--------|---------|------------|
| **OQ-02-OQ-01** | Define `Matrix.IsDiagonalizable A : Prop` and basic API (similar-to-diag definition, refl/symm/trans of conjugation, congruence under `Matrix.diagonal`). | ~80 |
| **OQ-02-OQ-02** | Bridge `Matrix.IsDiagonalizable A ↔ (Matrix.toLin' A).IsDiagonalisable` via the standard basis equivalence. Uses Mathlib's `Module.End.IsDiagonalisable` if available, else defines a local analogue. | ~120 |
| **OQ-02-OQ-03** | The **universal characterization**: `Matrix.IsDiagonalizable A ↔ Squarefree (minpoly K A) ∧ (minpoly K A).Splits (RingHom.id K)`. Routes through `isSemisimple_iff_squarefree_minpoly` (in-tree) + a splitting-to-eigenbasis lemma. | ~180 |
| **OQ-02-OQ-04** | Algebraically-closed corollary: `IsAlgClosed K → Matrix.IsDiagonalizable A ↔ Squarefree (minpoly K A)`. One-line application of `IsAlgClosed.splits` collapsing the splits-clause. | ~40 |

Total roadmap: ≈ 420 lines. Significantly smaller than either OQ-01
(~930 for JNF) or OQ-03 (~900 for RCF), reflecting the absence of
Jordan-block / Smith-normal-form infrastructure needs.

## Risk Notes

- **`Module.End.IsDiagonalisable` may not exist by that name** in
  Mathlib at v4.26.0. A grep at S2 will determine whether to use a
  Mathlib predicate or define a local one
  `Module.End.IsDiagonalisable f := ∃ B : Basis ι K V, ∀ i, ∃ μ, f (B i) = μ • B i`.
  If absent, OQ-02-OQ-02's line estimate may inflate by ~50 lines.

- **Splitting-to-eigenbasis is the only deep step.** Going from
  "`minpoly` is `∏ (X - μᵢ)` with distinct `μᵢ`" to "there exists an
  eigenbasis" is the classical eigenspace-decomposition argument:
  `V = ⨁ᵢ ker(f - μᵢ)` because the `μᵢ` are distinct roots of a
  squarefree polynomial that annihilates `f`. Mathlib has
  `Module.End.iSup_genEigenspace_eq_top` (under triangularizability)
  and the `independent_genEigenspace` lemma — but the
  *eigen*space-only version (not *gen*eigenspace) for the squarefree
  case may not be packaged. If not, S3 will need a small bridge
  lemma (≈ 50 lines).

- **Aristotle suitability.** OQ-02-OQ-01's API (definitional unfolds
  + `IsUnit` manipulation) and OQ-02-OQ-04's one-line corollary are
  reasonable Aristotle targets. OQ-02-OQ-03's eigenbasis-construction
  step is **not** an Aristotle candidate — it routes through
  Mathlib's spectral theory at a level Aristotle does not currently
  reach. Plan: S3 (the load-bearing step) is human-researcher; S2
  and S4 are Aristotle candidates after stating.

- **No axioms required.** All four sub-OQs route through Mathlib's
  proven `Module.End.IsSemisimple` API plus standard splitting
  theory. This OQ stays in the **verified** track of the gallery.

## References

- Hoffman & Kunze, *Linear Algebra* (2nd ed.), §6.4 (the minimal
  polynomial criterion for diagonalizability).
- Lang, *Algebra* (3rd ed.), Chapter XV, §4 (semisimple modules and
  the polynomial criterion).
- Mathlib `Module.End.isSemisimple_of_squarefree_aeval_eq_zero`
  (file `Mathlib.LinearAlgebra.Semisimple`, the "easier" direction).
- Mathlib `Module.End.IsSemisimple.minpoly_squarefree`
  (same file, the converse direction via the structure-of-modules
  theorem for the polynomial PID `K[X]`).
- Gallery `cayley-hamilton-minpoly-oq-01`
  (`CayleyHamiltonMinpolyOQ01.lean:206-211`) — the in-tree wiring
  that OQ-02 inherits.
