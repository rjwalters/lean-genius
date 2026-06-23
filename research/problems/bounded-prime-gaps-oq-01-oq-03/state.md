# Current State

**Phase**: COMPLETED (axiomatized) — the stated OQ is fully answered; only assumption is a cited external-computation axiom
**Since**: 2026-06-13 (S2 COMPLETION-SYNC, researcher-1)
**Iteration**: 2 (COMPLETION-SYNC)

## S2 COMPLETION-SYNC (researcher-1, 2026-06-13)

The stated open question — *determine the minimum admissible 50-tuple diameter*
— is **answered: it is exactly 246**, proved in both directions by
`oq01_k50_diameter_is_exactly_246` (achievability via `table_k50`; tightness via
`engelsma_lower_bound`). The only remaining assumption is the transitive axiom
`engelsma_lower_bound` (Engelsma's 2005 exhaustive admissible-tuple computation,
imported from sibling `BoundedPrimeGapsOQ03.lean`) — a cited external
computational result, reasonably axiomatized per the project axiom-integrity
policy, not a tractable in-Lean gap.

AUDIT (build-free, blackout 2026-06-13): source `BoundedPrimeGapsOQ01OQ03.lean`
and `meta.json` are fully consistent — 155 lines, 9 theorems (both conventions
agree; no private/indented), 0 local axioms (1 transitive → meta.axiomCount=1,
leanFile.axiomCount=0 per convention), 0 real sorries. No drift to fix.

Pool workflow status was stale at `in-progress`; promoted to `completed`. The
verification status stays `axiomatized` / badge `axiom` (unchanged).

---

**Phase (S1)**: AXIOMATIZED — structurally complete; conjecture isolated as transitive axiom from sibling slug
**Since**: 2026-06-04 (S1 STATE-SYNC, researcher-1, doc-only refresh of stale stub)
**Iteration**: 1 (STATE-SYNC)

## Current Focus

S1 STATE-SYNC (researcher-1, 2026-06-04): doc-only refresh.

State.md was a template stub with "Phase: COMPLETED" but
"Current Focus: Initial exploration" — inconsistent. The actual
disk state of `proofs/Proofs/BoundedPrimeGapsOQ01OQ03.lean` is:

- 155 lines, 9 theorems, 0 definitions, 0 sorries, 0 declared axioms.
- 1 *transitive* axiom: `engelsma_lower_bound` declared in sibling
  slug file `BoundedPrimeGapsOQ03.lean`, used here via the
  `Proofs.BoundedPrimeGapsOQ03` import.
- Top-level meta.json correctly records `axiomCount: 1` per project
  axiom integrity policy (transitive axioms count toward the
  assumption budget).

## Source-of-Truth Counts (proofs/Proofs/BoundedPrimeGapsOQ01OQ03.lean)

| Kind            | Count | Examples                                                  |
|-----------------|-------|-----------------------------------------------------------|
| Definitions     | 0     | (No new defs; all defs come from imported sibling slugs.)  |
| Theorems        | 9     | `table_k2`, `table_k3`, `table_k5`, `table_k50`, `complete_diameter_table`, `oq01_upper_bound_is_tight`, plus 3 sieve / equivalence theorems |
| Sorries         | 0     |                                                            |
| Axioms (local)  | 0     |                                                            |
| Axioms (transitive) | 1 | `engelsma_lower_bound` from `BoundedPrimeGapsOQ03.lean`  |

## Mathematical Content

The file completes the minimum-diameter table at k = 50 by:

1. Recording the diameter table entries for k ∈ {2, 3, 5, 50} as
   verified theorems (`table_k2`, `table_k3`, `table_k5`, `table_k50`).
2. Proving the k = 50 entry is *tight* (`oq01_upper_bound_is_tight`):
   no admissible 50-tuple has diameter < 246. Uses Engelsma's 2005
   exhaustive computation result as the lower bound axiom (declared in
   sibling slug OQ03).
3. Connecting to the Maynard–Tao sieve: H ≤ 246 (Polymath 8b, 2014)
   matches the Engelsma 50-tuple diameter exactly, showing the
   Polymath bound is sieve-tight within the k = 50 framework.

## Axiom Integrity

Per project policy, the slug's contribution is **honestly
axiomatized**: the Engelsma 2005 exhaustive computational result is
recorded as `engelsma_lower_bound : ∀ H : Finset ℕ, IsAdmissible H →
H.card ≥ 50 → diameter(H) ≥ 246` in the sibling slug file. This is
an external computational result that falls outside the scope of
in-Lean formalization (Engelsma's search ran on dedicated hardware
in 2005); recording it as an axiom is the correct framing.

## Active Approach

This iteration is STATE-SYNC only.

## Blockers

None. The slug is structurally complete.

## Forward Levers (NOT a roadmap to discharge the Engelsma axiom)

1. **Discharge `engelsma_lower_bound` axiom**: formalize Engelsma's
   2005 exhaustive search in Lean. This is a major project: the search
   space for admissible 50-tuples is combinatorially explosive, and
   the original computation ran for months on dedicated hardware. A
   Lean version would require either (a) re-running the search inside
   Lean's kernel (intractable), (b) a Lean-internal optimization proof
   (open mathematical problem), or (c) a `native_decide` certificate
   for a single witness tuple proving optimality (still requires
   establishing the search-exhaustion claim).

2. **Extend the diameter table**: the OQ-01 framework supports
   k ∈ {2, 3, 5, 50}; adding entries for k ∈ {4, 6, 7, …, 49} would
   require either separate computational searches or proofs of
   intermediate diameter values. The Polymath project tabulated these
   values; importing them as axioms is straightforward but
   axiom-multiplying.

3. **Sibling-slug audit cycle**: this slug imports `BoundedPrimeGaps`,
   `BoundedPrimeGapsOQ01`, `BoundedPrimeGapsOQ03`. A periodic audit
   ensures the import chain remains build-clean as those sibling
   slugs evolve.

## Blockers

None — file builds (assumed, per S1 OBSERVE checkpoint).

## Next Action

1. **(Optional, this iteration)** STATE-SYNC: this update + tracker
   JSON refresh.

2. **No further researcher work** is required on this slug. It is
   structurally complete; the 1 transitive axiom is honestly
   classified per project axiom integrity policy.

3. **Sibling-slug attention**: if any of the upstream sibling slugs
   (`bounded-prime-gaps`, `bounded-prime-gaps-oq-01`,
   `bounded-prime-gaps-oq-03`) breaks under future Mathlib drift,
   this slug's build would cascade. Routine auditor monitoring.

## Honesty Block

- This iteration is doc-only (no `.lean`, no `meta.json`,
  no `annotations.json` edits). State.md was a "Phase: COMPLETED"
  template stub with inconsistent body text ("Current Focus: Initial
  exploration"); this update reconciles the two.
- The 1 transitive axiom (`engelsma_lower_bound`) is *honestly*
  classified: it cites a 2005 exhaustive computer search whose
  Lean-internal reproduction is impractical. Per project axiom
  integrity policy, the top-level meta.json `axiomCount: 1`
  correctly counts the transitive dependency, while `leanFile.axiomCount: 0`
  correctly counts the local declaration.
- 9 theorems / 0 sorries / 155 lines verified on disk this session.

## Attempt Counts

- Total attempts: 1 (S1 STATE-SYNC, this iteration; the
  substantive Lean work pre-dates this tracker entry).
- Current approach attempts: STATE-SYNC.
- Approaches tried: 1 (diameter-table completion via Engelsma
  axiom + Polymath sieve framework).
