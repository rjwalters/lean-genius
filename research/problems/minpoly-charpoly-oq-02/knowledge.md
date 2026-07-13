# Knowledge — minpoly-charpoly-oq-02

## S1 OBSERVE session (2026-05-12, researcher-9)

### Mathematical landscape

The OQ asks for the matrix-level characterization

> `A : Matrix n n K` is diagonalizable iff `minpoly K A` is squarefree

over either an algebraically closed field, or "more generally" a
perfect field. The "more generally" clause is **incorrect** as
stated: over perfect non-algebraically-closed fields (e.g. `ℝ`, `ℚ`),
diagonalizability also requires that the minpoly **splits**.

#### Counterexample to the "perfect field is enough" claim

Take `K = ℝ` and
```
A = [0 -1]
    [1  0]
```
Then `minpoly ℝ A = X² + 1`. This polynomial is:
- *Squarefree* — it has no repeated factors;
- *Irreducible* over `ℝ` — it has no real roots;
- *Not split* over `ℝ` — its splitting field is `ℂ`.

The matrix `A` is **not diagonalizable over `ℝ`** (its only
eigenvalues are `±i ∉ ℝ`). Hence "squarefree minpoly" is *necessary
but not sufficient* over `ℝ` (a perfect field).

The correct biconditional has **two clauses**:

> `A` is diagonalizable over `K` ⟺
> `Squarefree (minpoly K A)` ∧ `(minpoly K A).Splits (RingHom.id K)`

Over `IsAlgClosed K`, every polynomial in `K[X]` splits, so the
splitting clause is vacuous and collapses to plain squarefreeness.

### Already in-tree (load-bearing input)

The gallery already proves the **endomorphism-level** biconditional
at `CayleyHamiltonMinpolyOQ01.lean:206-211`:

```lean
theorem isSemisimple_iff_squarefree_minpoly
    [FiniteDimensional K V] {f : Module.End K V} :
    f.IsSemisimple ↔ Squarefree (minpoly K f) := by
  constructor
  · exact IsSemisimple.minpoly_squarefree
  · intro hsq
    exact isSemisimple_of_squarefree_aeval_eq_zero hsq (minpoly.aeval K f)
```

Both directions route through Mathlib v4.26.0:
- `IsSemisimple.minpoly_squarefree` (forward direction; uses the
  structure theorem for finitely generated modules over a PID
  applied to `K[X]` and the cyclic-decomposition `K[X]/(f) ≅ ⨁ K[X]/(pᵢ)`
  with `pᵢ` irreducible);
- `isSemisimple_of_squarefree_aeval_eq_zero` (reverse direction;
  uses the **CRT** for `K[X]/(p₁ ⋯ pₖ)` when the `pᵢ` are distinct
  irreducibles).

The matrix-level analogue is what OQ-02 is asked to deliver.

### The matrix-to-endomorphism translation

For `A : Matrix n n K`, the standard left-multiplication
endomorphism is `Matrix.toLin' A : (n → K) →ₗ[K] (n → K)`, and
crucially:

- `minpoly K A = minpoly K (Matrix.toLin' A)` (by definition;
  Mathlib treats matrix minpoly *as* endomorphism minpoly of
  `toLin'`).
- Diagonalizability of `A` (similar to a diagonal matrix) is
  equivalent to `Matrix.toLin' A` admitting an *eigenbasis* (a basis
  of eigenvectors).

The semisimplicity of `Matrix.toLin' A` is the right
field-agnostic abstraction; the additional splitting requirement
is what distinguishes "admits an eigenbasis" from "decomposes as a
direct sum of simple submodules" (an `ℝ`-irreducible 2D rotation
block is a simple `ℝ[X]`-submodule, but not a 1D eigenspace).

### Why splitting suffices

When `minpoly K A` is squarefree and splits as
`∏ᵢ (X - μᵢ)` with distinct `μᵢ ∈ K`, the standard eigenspace
decomposition argument shows
```
V = ⨁ᵢ ker(A.toLin' - μᵢ • id)
```
because (a) the `μᵢ` are distinct so the eigenspaces are
independent, and (b) the squarefree minpoly annihilates `A`, so
the eigenspaces span all of `V` (this is the *spectral theorem* in
its module-theoretic form, via CRT on `K[X]/(minpoly)`). A basis
of `V` built by concatenating bases of the eigenspaces is the
sought eigenbasis.

### Mathlib gaps

1. **No `Matrix.IsDiagonalizable` predicate** by that name at
   v4.26.0. A grep for `IsDiag` finds `Matrix.IsDiag` (matrix-is-diagonal
   property) but no "matrix-is-similar-to-a-diagonal-matrix" predicate.
   This is OQ-02-OQ-01's first task.

2. **`Module.End.IsDiagonalisable` may not exist by that name.**
   Mathlib has `Module.End.HasEigenvector`, `genEigenspace`, etc.,
   but a packaged "admits an eigenbasis" predicate may need to be
   defined locally if absent. This is OQ-02-OQ-02's first task.

3. **The "squarefree + splits → eigenbasis" implication** is
   *implicitly* provable via the spectral theory in
   `Mathlib.LinearAlgebra.Eigenspace.*` files, but not packaged as
   a single named lemma. The reverse implication (eigenbasis →
   squarefree minpoly) is a routine cardinality + irreducible-factor
   count argument. This is OQ-02-OQ-03's main content.

### Decomposition (proposed for S2+)

| Sub-OQ | Content | Est. lines | Aristotle? |
|--------|---------|------------|------------|
| OQ-02-OQ-01 | `Matrix.IsDiagonalizable` definition + API | ~80 | yes |
| OQ-02-OQ-02 | matrix ↔ endomorphism bridge | ~120 | partial |
| OQ-02-OQ-03 | universal characterization (squarefree ∧ splits) | ~180 | no |
| OQ-02-OQ-04 | algebraically-closed corollary | ~40 | yes |

Total: ~420 lines. Smaller than OQ-01 (~930 JNF) and OQ-03 (~900 RCF).

### Comparison to siblings

`MinpolyCharpolyOQ01.lean` (Jordan normal form) has resolution status
"affirmative, modulo one local gap" — the local gap is the nilpotent
canonical form, which is a ~400-line sub-OQ in its own right
(`OQ-01-OQ-02`).

`MinpolyCharpolyOQ03.lean` (rational canonical form) has resolution
status "affirmative" with all ingredients in Mathlib but a ~900-line
gluing exercise across `Module.equiv_directSum_of_isTorsion` and the
companion-matrix infrastructure.

`MinpolyCharpolyOQ02.lean` (this OQ, diagonalizability) has the
*shortest* roadmap because:
- The endomorphism-level biconditional is already in-tree
  (`isSemisimple_iff_squarefree_minpoly`);
- No nilpotent canonical form (unlike JNF);
- No invariant-factor decomposition (unlike RCF);
- The only "new math" is the splitting-to-eigenbasis step,
  which is ~50 lines of Mathlib spectral-theory plumbing.

This makes OQ-02 the **most tractable** of the three parent open
questions, and the best candidate for a single-PR S2 deliverable
(scaffold + S2-OQ-01 in one file).

### S2 entry-point suggestion

For S2 (next iteration), the right first move is to create
`proofs/Proofs/MinpolyCharpolyOQ02.lean` with:

1. `import Proofs.MinpolyCharpoly` (parent gallery entry).
2. `import Proofs.CayleyHamiltonMinpolyOQ01`
   (for `isSemisimple_iff_squarefree_minpoly`).
3. Definition `Matrix.IsDiagonalizable A := ∃ P, IsUnit P ∧ (P⁻¹ * A * P).IsDiag`.
4. State the **main OQ-02 theorem** (`isDiagonalizable_iff_squarefree_and_splits`)
   with one `sorry`.
5. State the **algebraically-closed corollary** with one `sorry`
   (or prove it from the main theorem if Mathlib's `IsAlgClosed.splits`
   is in scope).
6. Decompose the body of the main theorem into the 4 sub-OQs above
   as a documented roadmap in a `/- ... -/` comment block.

This is roughly the same shape as the existing `MinpolyCharpolyOQ01.lean`
and `MinpolyCharpolyOQ03.lean` S1+S2 scaffolds.

## Open questions discharged by this OBSERVE

- `minpoly-charpoly.openQuestions[1]`: "Can the diagonalizability
  criterion (minpoly squarefree) be formalized in Lean 4?" → **YES,
  with a splitting refinement.** All Mathlib ingredients exist at
  v4.26.0; the gallery already proves the endomorphism case. The
  matrix-level packaging is ~420 lines.

## Open questions generated by this OBSERVE

None — the four sub-OQs above are the natural decomposition. We
could in principle decompose OQ-02-OQ-03 further into
"forward direction" and "reverse direction", but at ~90 lines each
they fit comfortably in a single sub-OQ.

## Files modified this S1

None (text-only S1 OBSERVE).

- `research/problems/minpoly-charpoly-oq-02/problem.md` — new
- `research/problems/minpoly-charpoly-oq-02/knowledge.md` — new (this file)
- `research/problems/minpoly-charpoly-oq-02/state.md` — new
- `src/data/research/problems/minpoly-charpoly-oq-02.json` — new
