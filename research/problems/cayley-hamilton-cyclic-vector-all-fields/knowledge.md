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

## Session 2026-04-28 (Session 2) — V2 Reconciliation (Axiom Eliminated)

**Mode**: REVISIT
**Outcome**: progress (metadata reconciliation only — no Lean changes this session)

### What I Did

1. Discovered candidate-pool entry stale-`available` for an already-completed problem
2. Read gallery file `proofs/Proofs/CayleyHamiltonCyclicVectorAllFields.lean` (189 lines): now V2 axiom-free (0 axioms, 1 routine sorry on `monic_factored_form`)
3. Confirmed via git log: PR #13041 (2026-04-27) eliminated the V1 RCF axiom by routing through WIP04's `GeneralCyclicVector.nonderogatory_general_has_cyclic_vector` (primary decomposition + Bezout/CRT)
4. Reconciled `src/data/research/problems/cayley-hamilton-cyclic-vector-all-fields.json` to reflect V2 state (was still describing V1 axiom-based approach)
5. No Lean code edits this session — Docker daemon was unresponsive locally; pure-text reconciliation only

### Key Findings

- V2 (PR #13041) replaces a deep mathematical axiom (`nonderogatory_similar_companion`, ~800 lines to prove from PID structure theorem) with a routine UFM API sorry (`monic_factored_form`, ~50 lines). Net: deep axiom → routine sorry.
- V2 proof chain: factor `minpoly K M` via `monic_factored_form` → apply WIP04's `nonderogatory_general_has_cyclic_vector` (axiom-free primary decomposition).
- `monic_factored_form` is Aristotle-suitable: `normalizedFactors μ` → `toFinset/count` for distinct primes with exponents → coprime via `Prime.coprime_iff_not_dvd` → product equality via `Polynomial.normalizedFactors_prod`.
- Per-problem JSON had not been updated since V1; this session brings it into agreement with the actual gallery file and the merged axiom-elimination PR.

### Files Modified

- `src/data/research/problems/cayley-hamilton-cyclic-vector-all-fields.json` — `currentState.{focus,nextAction,iteration}`, `knowledge.{progressSummary,builtItems[3..4],insights+=,mathlibGaps,nextSteps}`
- `research/problems/cayley-hamilton-cyclic-vector-all-fields/knowledge.md` — this session entry

### Next Steps

- Submit `monic_factored_form` to Aristotle (routine UFM API) — would close the file to 0/0.
- After 0/0: optionally upstream `monic_factored_form` to Mathlib as a `Polynomial.UniqueFactorizationMonoid` lemma.

---

## Dead Ends

- `exists_strongly_cyclic` approach (strong induction on natDegree q): viable but complex (~100 more lines). Superseded by WIP04 primary-decomposition route used in V2.
- V1 Route B (axiomatize `nonderogatory_similar_companion`): superseded by V2 axiom elimination (PR #13041).
