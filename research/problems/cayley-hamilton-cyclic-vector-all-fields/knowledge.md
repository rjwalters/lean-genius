# Knowledge Base: cayley-hamilton-cyclic-vector-all-fields

**Problem**: Cyclic Vector Existence for Nonderogatory Matrices over All Fields
**Status**: COMPLETED (gallery entry created)
**Phase**: COMPLETED

---

## Session 2026-04-26 (Session 1) — Axiomatized Gallery Entry

**Mode**: FRESH
**Outcome**: completed

### What I Did

1. Surveyed landscape: Mathlib v4.26.0 lacks RCF infrastructure (no companion matrix, no Smith NF, no PID structure theorem)
2. Read related files: `CayleyHamiltonReductionOQ02OQ01.lean` (companion matrix, fully proved), `CayleyHamiltonMinpolyOQ05OQ01OQ04.lean` (CyclicVectorArbitrary namespace, 1 sorry for nonderogatory_similar_companion)
3. Chose Route B: axiomatize the RCF similarity theorem, prove main theorem from it
4. Created `proofs/Proofs/CayleyHamiltonCyclicVectorAllFields.lean`:
   - 1 explicit `axiom`: `nonderogatory_similar_companion` (RCF similarity — nonderog M ~ C(minpoly M))
   - 0 sorries: all other lemmas imported/proved
   - Main theorem: `nonderogatory_has_cyclic_vector` (for all fields)
   - Corollaries: finite field version + cyclic characterization
5. Created gallery entry at `src/data/proofs/cayley-hamilton-cyclic-vector-all-fields/`

### Key Findings

- Mathlib v4.26.0 has NO companion matrix or RCF infrastructure — only basic charpoly/minpoly facts
- The `CyclicVectorArbitrary` namespace (OQ04) already proved the supporting lemmas:
  - `companionMatrix_cyclic_e0`: e₀ cyclic for C(p) via orbit argument
  - `cyclic_vector_of_similar`: cyclic vectors transfer under similarity
  - `aeval_conj`: conjugation commutes with polynomial evaluation
- Route B (axiom) is cleaner than sorry: the assumption is named and documented
- The full proof from scratch would require ~800 lines of Smith normal form

### Files Created

- `proofs/Proofs/CayleyHamiltonCyclicVectorAllFields.lean` (213 lines, 1 axiom, 0 sorries)
- `src/data/proofs/cayley-hamilton-cyclic-vector-all-fields/meta.json`
- `src/data/proofs/cayley-hamilton-cyclic-vector-all-fields/annotations.json` (5 annotations)
- `src/data/proofs/cayley-hamilton-cyclic-vector-all-fields/index.ts`

### Result

Gallery entry: status=axiomatized, badge=axiom, axiomCount=1, sorries=0

---

## Dead Ends

- `exists_strongly_cyclic` approach (strong induction on natDegree q): viable but complex (~100 more lines). Route B was simpler.

---

## Session 2026-04-27 (Session 2 — researcher-10) — Audit and Mathlib Re-Survey

**Mode**: AUDIT
**Outcome**: documentation updated; full discharge deferred to next session

### What I Did

Audited the existing axiomatized gallery entries
(cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01 and the parallel
cayley-hamilton-cyclic-vector-all-fields) and re-surveyed Mathlib for
the supposedly-missing PID structure theorem.

### Key Finding (correcting prior session)

The PID structure theorem **is** in Mathlib (verified via direct
inspection of the `.lake` packages):

- `Mathlib.Algebra.Module.PID`:
  - `Module.equiv_directSum_of_isTorsion` — f.g. torsion module over PID
    is direct sum of `R/(p_i^e_i)`.
  - `Module.equiv_free_prod_directSum` — full structure theorem.
  - `Module.exists_ker_toSpanSingleton_eq_annihilator` — for f.g. module
    over PID, ∃ x with ker(toSpanSingleton x) = annihilator. This is
    exactly the cyclic-vector witness once specialized.

- `Mathlib.Algebra.Polynomial.Module.AEval`:
  - `Module.AEval'` — type synonym making `M` into `R[X]`-module via an
    endomorphism / matrix.
  - `Module.AEval.annihilator_top_eq_ker_aeval` — annihilator of AEval
    equals ker(aeval), connecting module annihilator with minimal poly.
  - `Module.AEval.instFinitePolynomial` — AEval inherits Module.Finite.

### Why the Earlier Sessions Missed This

The original problem.md (line 52) explicitly suggested searching Mathlib
for `Matrix.IsCompanion` / `Matrix.RationalCanonicalForm` / similar.
Those are absent. But the PID structure theorem lives at the more
abstract `Module` level (via the AEval bridge), not the matrix level —
and that is what was missed.

### Direct Discharge Path (Route D)

For nonderogatory M ∈ Matrix (Fin n) (Fin n) K:

1. Treat K^n as `Module.AEval' M`. It inherits `Module.Finite K[X]`.
2. Apply `Module.exists_ker_toSpanSingleton_eq_annihilator` →
   ∃ x ∈ Module.AEval' M with ker(p ↦ p • x) = annihilator (top).
3. By `annihilator_top_eq_ker_aeval`, this annihilator is ker(aeval M),
   which is the principal ideal (minpoly K M).
4. For nonderogatory M, deg(minpoly K M) = n. No nonzero polynomial of
   degree < n is in (minpoly).
5. Pull x back through `Module.AEval.of` to get v ∈ K^n. Then for any
   p with deg p < n: if `(aeval M p).mulVec v = 0`, then p ∈ (minpoly),
   so p = 0. That is precisely `IsCyclicVector M v`.

This avoids the companion matrix similarity entirely. The axiom
`nonderogatory_similar_to_companion` becomes a derived theorem:
v cyclic + change-of-basis to {v, Mv, …, M^{n-1}v} produces the
companion-matrix similarity.

### Why Discharge Was Deferred

Disk free at session start: ~750 MiB (95% full). Per project memory,
under 1 GiB free I should not attempt Docker builds. Lean code that
cannot be built locally must not be pushed. So the audit is committed
as documentation; the discharge waits for a session with adequate disk.

### Files Changed (this session)

- `proofs/Proofs/CayleyHamiltonMinpolyOQ05OQ01OQ04WIP01.lean`: axiom
  docstring expanded with the audit and the Route D proof sketch.
- `src/data/proofs/cayley-hamilton-minpoly-oq-05-oq-01-oq-04-wip-01/meta.json`:
  - `assumptions` corrected.
  - `openQuestions` rewritten around the actual gap (bridging code).
  - 3 new `mathlibDependencies` for the PID + AEval lemmas.
- `research/problems/cayley-hamilton-cyclic-vector-all-fields/state.md`:
  REOPENED-FOR-DISCHARGE, Route D documented as next-action.
- `research/problems/cayley-hamilton-cyclic-vector-all-fields/knowledge.md`:
  this entry.

### Anticipated Next-Session Effort

Estimated 50–150 lines of Lean. The bridging code itself is mostly
unfolding definitions; the conceptual content is in the four Mathlib
lemmas above. A future session should attempt to write the new file
and run the Docker build to verify.

