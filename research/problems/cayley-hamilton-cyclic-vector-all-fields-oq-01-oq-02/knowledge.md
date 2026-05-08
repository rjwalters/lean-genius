# Knowledge Base: cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02

**Problem**: Rational Canonical Form — Mathlib formalization connection (nonderogatory case)
**Phase**: ORIENT
**Status**: scaffolded (Session 1 complete)

---

## Session 1 (2026-05-08) — Scaffold Existing File

**Mode**: FRESH
**Outcome**: scaffolded (gallery + research + build registration)

### What I Did

1. Discovered `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02.lean` already
   exists on `origin/main` (156 lines, 1 axiom, 0 sorries) — added inadvertently as a
   side-effect of audit-tracker PR #16881 (which also pulled in several other unregistered
   Lean files like `AbelRuffiniOQ04OQ02OQ02OQ06.lean`, `BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ01.lean`,
   and `LawOfCosinesOQ01OQ01OQ01.lean`).

2. Verified the file's structure against `origin/main`:
   - 156 lines
   - 2 definitions: `companionMx`, `cyclicMatrix`
   - 5 theorems/lemmas: `cyclicMatrix_ker` (private), `cyclicMatrix_injective`,
     `cyclicMatrix_isUnit`, `M_mul_cyclicMatrix`, `nonderogatory_similar_to_companion`
   - 1 axiom: `hMn_axiom`
   - 0 sorries
   - Imports: `Mathlib`, `CayleyHamiltonMinpolyOQ05OQ01OQ04WIP04`,
     `CayleyHamiltonCyclicVectorAllFields`, `CayleyHamiltonCyclicVectorAllFieldsOQ01OQ01`

3. Confirmed the file is **not** imported by `proofs/Proofs.lean` (the default build target).
   Adding it now so CI exercises the build.

4. Surveyed Mathlib v4.26.0 for RCF infrastructure:
   - `Matrix.SmithNormalForm` exists for PIDs
   - `Module.IsTorsion`-style structure theorems for finitely-generated modules over PIDs
   - **No** `Matrix.rationalCanonicalForm`, **no** `Matrix.companionMatrix` API,
     **no** matrix-similarity-to-companion theorem in any form
   - The closest is `Matrix.charpoly_companionMatrix` for a hand-rolled companion in some
     test/example files, but nothing for general use

5. Verified the proof's mathematical content:
   - The Krylov matrix `P[i,j] = (M^j v)_i` is the change-of-basis matrix
   - Its invertibility (when `v` is cyclic) is the algebraic reformulation of
     "{v, Mv, ..., M^{n-1}v} is a basis"
   - The conjugation identity `M·P = P·C(minpoly)` is column-by-column verification:
     - Column j (j < n-1): LHS = M^{j+1}v, RHS = M^{j+1}v (from companionMx pattern)
     - Column n-1 (last): LHS = M^n v, RHS = -∑ c_k M^k v (from companionMx coeffs)
     - The last-column equality reduces to the Cayley-Hamilton-style relation
       `M^n v = -∑ c_k M^k v` — this is what `hMn_axiom` asserts

### Key Findings

- **Mathlib RCF status (v4.26.0)**: there is no formalization. The structure-theorem
  machinery exists, but the matrix-form RCF (similarity to a block-diagonal of companion
  matrices) has not been packaged. Even the single-block (nonderogatory) case is missing
  from Mathlib proper.

- **Operational scope of OQ-01-OQ-02**: rather than a Mathlib survey, the productive
  reading of the question is "formalize the nonderogatory case of RCF as a stand-alone
  theorem" — which is exactly what the existing file does, modulo one routine axiom.

- **Axiom analysis**: `hMn_axiom` is *not* a deep mathematical statement. It is a direct
  consequence of `aeval M (minpoly K M) = 0` (which is `minpoly.aeval`) plus the monicity
  `(minpoly K M).coeff n = 1` (which is `minpoly.monic` + `Polynomial.Monic.def` rewritten
  using `hdeg`). A careful unwrap should be ~15-25 Lean lines.

- **Why the axiom was used**: likely a time-saving move during the original drafting —
  the proof of the conjugation identity needed the relation `M^n v = -∑ c_k M^k v` quickly
  to make the column-comparison go through. Eliminating it brings the file to 0 axioms.

### Files Modified (Session 1)

- `proofs/Proofs.lean` — register `CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02`
- `src/data/proofs/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02/{meta.json, index.ts, annotations.json}` — new gallery entry
- `src/data/research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02.json` — new research metadata
- `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02/{problem.md, state.md, knowledge.md}` — research scaffold

**No edits to the Lean file itself this session** — that's deferred to Session 2 (axiom elimination).

### Result

Gallery entry: status=`axiomatized`, badge=`axiom`, axiomCount=1, sorries=0, lineCount=156.

---

## Insights (cumulative)

### What's known about the proof

1. **Krylov matrix is the natural similarity matrix.** The classical RCF construction
   for a single block: pick any cyclic vector `v`, then `P = [v | Mv | M²v | ... | M^{n-1}v]`
   is the change-of-basis matrix that conjugates `M` to its companion matrix. The
   invertibility of `P` is exactly "v is cyclic" recast in matrix terms.

2. **The proof only needs one cyclic vector existence theorem as a black box.**
   `nonderogatory_has_cyclic_vector` (from the parent OQ-01) provides this.
   Once you have `v`, the rest of the proof is finite-dimensional linear algebra
   over a field — no avoidance arguments, no field-size hypotheses.

3. **The conjugation identity has a clean column-by-column proof.**
   The companion matrix is sparse: column j (j < n-1) is `e_{j+1}` (the standard basis
   vector), and column n-1 is `(-c_0, -c_1, ..., -c_{n-1})ᵀ` where `c_i` are the
   coefficients of `minpoly K M`. Comparing entries reduces to:
   - For non-last columns: `M · (M^j v) = M^{j+1} v` (trivially)
   - For the last column: `M · (M^{n-1} v) = M^n v`, which the Cayley-Hamilton
     relation rewrites as `-∑ c_k M^k v`

4. **`hMn_axiom` is the Cayley-Hamilton expansion in disguise.** It says
   `M^n v = -∑_{k<n} c_k M^k v` when `(minpoly K M).natDegree = n`. The proof:
   - `aeval M (minpoly K M) = 0` (Mathlib: `minpoly.aeval`)
   - Expand: `∑_{k≤n} c_k M^k = 0` (Mathlib: `Polynomial.aeval_eq_sum_range`)
   - Monic + hdeg: `c_n = 1` (Mathlib: `(minpoly K M).Monic.coeff_natDegree`)
   - Rearrange: `M^n = -∑_{k<n} c_k M^k`
   - Apply `mulVec v` (linearity)

### Connection to sibling entries

- **OQ-01** (`cayley-hamilton-cyclic-vector-all-fields-oq-01`): proves
  `nonderogatory → ∃ v, IsCyclicVector M v` axiom-free using primary decomposition.
  Provides the cyclic-vector existence theorem this entry consumes.

- **OQ-01-OQ-01** (`cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01`): proves the
  *converse* `IsCyclicVector M v → IsNonderogatory M`, completing the biconditional.
  Provides `minpoly_natDegree_of_cyclic`, used to establish `(minpoly K M).natDegree = n`.

- **OQ-01-OQ-02** (this entry): the next link in the chain — given a cyclic vector,
  produces an explicit similarity to the companion matrix. With OQ-01 + OQ-01-OQ-01 + OQ-01-OQ-02,
  the full nonderogatory RCF pipeline is in place over any field.

### Mathlib RCF gap

As of Mathlib v4.26.0:
- ✅ `Matrix.SmithNormalForm` for PIDs
- ✅ `Module.IsTorsion.isInternal_of_finrank_eq_one` and related structure theorems
- ❌ `Matrix.companionMatrix` — no canonical definition
- ❌ `Matrix.rationalCanonicalForm` — no statement, no proof
- ❌ Similarity-to-companion theorem in any form

This is a real gap. A future Mathlib contribution could:
1. Add `Matrix.companionMatrix : R[X] → Matrix (Fin n) (Fin n) R` (this entry has a model)
2. Prove `Matrix.similar_companionMatrix_of_nonderogatory` (this entry's `nonderogatory_similar_to_companion`)
3. Generalize to the multi-block case via the structure theorem for `K[X]`-modules

### Dead Ends / Wrong Routes

- **Don't try to use Mathlib's `Module.IsTorsion`-style structure theorem directly.** It's
  over PIDs in module-form, not matrix-form, and translating between the two is itself
  a nontrivial formalization. The Krylov-matrix approach is much more direct for the
  single-block case.

- **Don't try to define `companionMx` via `Matrix.of` and a tactic-driven match.** The
  `if-then-else` definition used in the file is cleaner and `simp`-friendly because it
  exposes the column-by-column structure used in `M_mul_cyclicMatrix`.
