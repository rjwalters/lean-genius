# Knowledge Base: lagrange-theorem-oq-02-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-08 (researcher-5) — Verified + gallery re-file

**Mode**: FRESH · **Outcome**: completed

### What I Did
- Discovered the full deliverable already exists: `Proofs/LagrangeTheoremOQ02OQ03.lean`
  (finiteness-free / `Cardinal.mk` orbit–stabilizer; 7 theorems, 167 lines, 0 sorries,
  0 axioms), merged via the recovery queue (#35316) without a Lean build.
- Rebuilt it under Docker to confirm it is genuinely verified: **3058 jobs, EXIT 0**.
- Found the verified proof was galleried under the wrong slug
  `lagrange-theorem-oq-02-oq-02-oq-03` (no matching pool problem), while this problem
  `lagrange-theorem-oq-02-oq-03` was still open. Re-filed the gallery entry
  (dir + `meta.id`/`slug` + `annotations.proofId`) under the correct slug.

### Key Findings
- The Lean content is finiteness-free orbit–stabilizer over `Cardinal.mk`: coset
  characterization, the bijection `orbit ≃ G ⧸ Stab`, `#(orbit) = #(G ⧸ Stab)`, cardinal
  Lagrange `#G = #(G ⧸ H)·#H`, the cardinal product `#(orbit)·#(Stab) = #G`, the `Finite`
  `Nat.card` specialization, and the pretransitive corollary `#X = #(G ⧸ Stab)`.
- Left the auditor's `audit-tracker.json` untouched (a stale `...-oq-02-oq-02-oq-03`
  entry for the deleted slug remains; auditors reconcile deleted-slug entries).

### Files Modified
- `src/data/proofs/lagrange-theorem-oq-02-oq-03/{meta.json,annotations.json}` (re-filed)
- `src/data/research/problems/lagrange-theorem-oq-02-oq-03.json` (knowledge + status)
- `research/problems/lagrange-theorem-oq-02-oq-03/{knowledge.md,state.md}`

### Next Steps
None — completed and verified.
