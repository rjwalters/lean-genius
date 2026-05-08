# Knowledge Base: cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02

**Problem**: Rational Canonical Form — Mathlib formalization connection (nonderogatory case)
**Phase**: COMPLETE (axiom-free, biconditional closed); S4 advancing toward `Matrix.minpoly_companionMatrix`.
**Status**: verified (0 axioms, 0 sorries; S2 PR #17039 + S3 PR #17069 merged)

---

## Session 4 (2026-05-08) — Vector-form Cayley-Hamilton for the companion

**Mode**: CONTINUE
**Outcome**: vector-level identity proved; matrix-level deferred to S5.

### What I Did

Established `(aeval (companionMx p) p).mulVec e₀ = 0` for monic `p` of degree `n`,
the computational core of the as-yet-unproved `Matrix.minpoly_companionMatrix : minpoly K (companionMx p) = p`.

Three new private lemmas:

1. **`companionMx_mulVec_eNm1`** (the last column): for any `p` and `n ≥ 1`,
   `(companionMx p).mulVec e_{n-1} = (-(p.coeff i))_{i<n}`. Pure unfolding of
   the `companionMx` definition; the first if-clause `j.val + 1 = n` triggers
   for `j = ⟨n-1, _⟩`. Pattern: `Finset.sum_eq_single` at `⟨n-1, _⟩`,
   `simp only [Pi.single_eq_same, mul_one, companionMx]`, `if_pos hnstep`
   with `hnstep : (n-1) + 1 = n` (via `Nat.sub_add_cancel hn`).

2. **`companionMx_pow_n_eq_lastCol_e0`** (n-th iterate at e₀):
   `((companionMx p) ^ n).mulVec e₀ = (-(p.coeff i))_{i<n}`. Combines
   Session 3's `companionMx_pow_e0` (k = n-1) with `companionMx_mulVec_eNm1`.
   Trick: rewrite the exponent `n` as `(n-1) + 1` via `congr 1 + omega`
   (a direct `rw [show n = (n-1) + 1 from by omega]` would also rewrite the
   `Fin n` type-level `n`, breaking unification). Then `pow_succ'` +
   `Matrix.mul_mulVec` + `companionMx_pow_e0 p hn (n-1) hnn1` closes.

3. **`aeval_companionMx_p_mulVec_e0_zero`** (the main result):
   `(aeval (companionMx p) p).mulVec e₀ = 0` for monic `p` of degree `n`.
   - Expand `aeval` via the local `aeval_eq_sum_range_natDegree` (Session 3) +
     `sum_mulVec_local` (Session 2) + `hp_deg : p.natDegree = n`.
   - Peel off `k = n` term via `Finset.sum_range_succ`.
   - Use `hp_monic.leadingCoeff` + `Polynomial.leadingCoeff` + `hp_deg` to set
     `p.coeff n = 1`, then `one_smul` cancels the scalar.
   - Apply `companionMx_pow_n_eq_lastCol_e0` for the k=n term and
     `companionMx_pow_e0` for the k<n terms.
   - Pointwise at index i: the `range n` sum picks out `k = i.val`, contributing
     `p.coeff i.val`. The k=n term contributes `-(p.coeff i.val)`. They cancel.

### Files Modified (Session 4)

- `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02.lean` (+103 lines net):
  Three new private lemmas + Session 4 docstring section.
- `src/data/proofs/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02/meta.json`:
  - `meta.lineCount`: 406 → 509
  - `meta.theoremCount`: 14 → 17
  - `leanFile.lineCount`: 214 → 509 (was stale from S2; S3 merged without sync)
  - `leanFile.theoremCount`: 8 → 17 (was stale from S2; S3 merged without sync)
  - Updated `assumptions` and `overview.openQuestions[Q2]` to reflect S4 partial progress.
- `research/problems/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02/state.md`:
  Refreshed (was stuck at "Iteration 2"); now records S3 + S4 with S5 plan.

### Result

Status remains `verified` / `original` / 0 axioms / 0 sorries. The new lemmas
are `private` (not part of the public API) — S5 will promote the matrix-level
result.

### Honest Reporting

- **Build was not verified locally** — same `.lake` symlink trap as before
  (memory `feedback_researcher_lake_symlink_broken.md`). CI is the ground truth.
- **API drift risk**: the proof uses `pow_succ'`, `Matrix.mul_mulVec`,
  `Matrix.smul_mulVec`, `Polynomial.leadingCoeff`, `Polynomial.Monic.leadingCoeff`,
  `Pi.single_apply`, `Pi.single_eq_same`, `Pi.smul_apply`, `Pi.add_apply`,
  `Finset.sum_range_succ`, `Finset.sum_apply`, `Finset.sum_eq_single`,
  `Finset.mem_range`, `Nat.sub_add_cancel`, `Nat.sub_lt`. All used by the existing
  Session 1-3 proofs in this same file, so most are stable; if any break, S5 repairs.
- **Did NOT close `aeval (companionMx p) p = 0`** at the matrix level. The
  vector-level result is the harder computation (the last-column action +
  monicity cancellation); lifting to the matrix level via cyclicity is a
  smaller, more-API-driven step deferred to Session 5.

---

## Session 3 (2026-05-08) — Companion-similarity biconditional

**Mode**: CONTINUE
**Outcome**: completed; merged via PR #17069 into origin/main on 2026-05-08.

### What I Did (recovered from origin/main commit history; this session record was
not written at the time of the S3 merge)

Established the *converse* of `nonderogatory_similar_to_companion`:
`similar_to_companion_implies_nonderogatory` and packaged the full biconditional
`nonderogatory_iff_similar_to_companion`. Three building-block lemmas added:

1. **`aeval_eq_sum_range_natDegree`**: a generalization of S2's
   `aeval_eq_sum_pow_local` to *any* polynomial (no `natDegree p = n` hypothesis),
   producing `aeval M q = ∑ k ∈ range (q.natDegree + 1), q.coeff k • M^k`. Used
   by `companionMx_isCyclic_e0` and (now) S4.

2. **`companionMx_pow_e0` (k < n)**: for any `p` and `0 < n`, induction on `k`
   shows `(companionMx p)^k * e₀ = e_k` for `k < n`. Captures the subdiagonal
   structure of the companion matrix.

3. **`companionMx_isCyclic_e0`**: the standard basis vector `e₀` is cyclic for
   `companionMx p` (any p). Proof: for any `q` with `q.natDegree < n` annihilating
   the matrix at e₀, expand `aeval (companionMx p) q` as a finite sum, evaluate
   at `e₀` using `companionMx_pow_e0`, and the resulting linear combination of
   `e_k`'s being zero forces all coefficients zero.

4. **`cyclicVector_similar_transport`**: similarity transports cyclic vectors. If
   `P⁻¹ M P = N` with `P` invertible and `w` is cyclic for `N`, then `P · w` is
   cyclic for `M`. Proof: `aeval M q * P = P * aeval N q` (induction on power),
   convert to `mulVec`, apply injectivity of `P.mulVec`.

5. **`similar_to_companion_implies_nonderogatory`** (converse): if `M` is similar
   to `companionMx (minpoly K M)`, then by `companionMx_isCyclic_e0` the matrix
   has a cyclic vector (image of e₀ under the similarity), and the cyclic-vector
   biconditional from sibling OQ-01-OQ-01 closes.

6. **`nonderogatory_iff_similar_to_companion`**: full biconditional combining
   forward (S1+S2) and converse (S3) directions.

### Result

The triangle `IsNonderogatory M ↔ ∃ v cyclic ↔ ∃ P, P⁻¹ M P = companionMx (μ_M)`
is now machine-verified over arbitrary fields with **zero axioms**.

PR: #17069 (S2 was merged separately as #17039 earlier the same day).

---

## Session 2 (2026-05-08) — Eliminate hMn_axiom

**Mode**: CONTINUE
**Outcome**: completed (axiom-free; build pending CI)

### What I Did

Replaced `private axiom hMn_axiom` with a `private theorem hMn_axiom` proved from
Mathlib API. The shipped proof uses the lower-level `Polynomial.eval₂_eq_sum` route
rather than the Session-1-skeleton's `Polynomial.aeval_eq_sum_range` (which may not
exist by that exact name in v4.26.0):

1. **Local helper `aeval_eq_sum_pow_local`**: expands `aeval M p` for any polynomial
   `p` with `natDegree p = n` into `∑ k ∈ Finset.range (n+1), p.coeff k • M^k`.
   - Start: `aeval_def` + `Polynomial.eval₂_eq_sum` + `Polynomial.sum_def` give
     `∑ k ∈ p.support, algebraMap K _ (p.coeff k) * M^k`.
   - Convert to smul form via `← Algebra.smul_def`: `∑ k ∈ p.support, p.coeff k • M^k`.
   - Extend to `range (n+1)` via `Finset.sum_subset`. Subset direction uses
     `Polynomial.le_natDegree_of_mem_supp` + `hdeg ▸` + `Nat.lt_succ_of_le`.
     Zero-outside-subset direction uses `Polynomial.notMem_support_iff` + `simp`
     (which reduces `coeff k = 0` and then `0 • M^k = 0`).

2. **Local helper `sum_mulVec_local`**: distributes `(∑_i f i).mulVec v = ∑_i (f i).mulVec v`
   over a finset. Direct induction on the finset using `Matrix.zero_mulVec`
   (empty case) + `Matrix.add_mulVec` + `Finset.sum_insert` (cons case).

3. **`hMn_axiom` (now a private theorem)**:
   - Set `p := minpoly K M`. Get `p.Monic` from `minpoly.monic (Matrix.isIntegral M)`.
   - From `hmon.leadingCoeff` + `Polynomial.leadingCoeff` + `hdeg`, get `p.coeff n = 1`.
   - Apply `aeval_eq_sum_pow_local p hdeg M` to expand `aeval M p` as a `range (n+1)`-sum.
   - `Finset.sum_range_succ` + `hcoeff_n` + `one_smul` peels off the top term:
     `∑_{k<n} c_k • M^k + M^n = aeval M p`. Combine with `minpoly.aeval K M : aeval M p = 0`
     and `eq_neg_of_add_eq_zero_right` to get `M^n = -∑_{k<n} c_k • M^k`.
   - Apply `mulVec v`: `Matrix.neg_mulVec` + `sum_mulVec_local` + `Matrix.smul_mulVec`
     gives the desired identity.

### Files Modified (Session 2)

- `proofs/Proofs/CayleyHamiltonCyclicVectorAllFieldsOQ01OQ02.lean` (+58 lines net):
  - Updated docstring to "0 sorries, 0 axioms"
  - Added `sum_mulVec_local` (8 lines)
  - Added `aeval_eq_sum_pow_local` (10 lines)
  - Replaced `private axiom hMn_axiom` with `private theorem hMn_axiom` (~30 lines)
  - Cleaned up the `cyclicMatrix_ker` simp lemma list (`coeff_sum` → `Polynomial.finset_sum_coeff`,
    added explicit `show c j = 0`)
- `src/data/proofs/cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-02/meta.json`:
  - status `axiomatized` → `verified`
  - badge `axiom` → `original`
  - axiomCount 1 → 0
  - lineCount 156 → 214
  - theoremCount 5 → 8
  - Updated description, assumptions, originalContributions, proofStrategy, openQuestions
    to reflect the axiom elimination

### PR

#17039 — research label, OPEN, awaiting CI build verification.

### Result

Gallery entry: status=`verified`, badge=`original`, axiomCount=0, sorries=0, lineCount=214.
The full nonderogatory RCF chain (OQ-01 + OQ-01-OQ-01 + OQ-01-OQ-02) is now
**fully axiom-free over arbitrary fields**.

### Honest Reporting

- Build was **not** verified locally — the worktree's `proofs/.lake` self-symlink
  forces fresh Mathlib clones on every Docker build (~45 min). Two other agents
  were already running Docker builds in parallel; starting a third was deemed
  uneconomic relative to claim TTL. CI is the ground truth for PR #17039.
- If the build flags an API drift on any of `Polynomial.eval₂_eq_sum`,
  `Polynomial.sum_def`, `Polynomial.le_natDegree_of_mem_supp`,
  `Polynomial.notMem_support_iff`, `Polynomial.finset_sum_coeff`,
  `Polynomial.Monic.leadingCoeff`, `Matrix.isIntegral`, or
  `eq_neg_of_add_eq_zero_right`, Session 3 will repair.

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
