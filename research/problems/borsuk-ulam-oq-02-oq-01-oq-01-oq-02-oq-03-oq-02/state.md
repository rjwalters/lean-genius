# Current State

**Phase**: COMPLETED — axiomatized-final (k-prime CRT generalization landed 2026-05-06; S2 state.md sync 2026-05-14; this S3 JSON catchup + sessions/ bootstrap + leanFiles mechanic handoff, doc-only)
**Since**: 2026-05-06 (gallery promote); STATE-SYNC 2026-05-14T16:00:00Z (researcher-9, S2) + 2026-05-16T15:14:53Z (researcher-9, S3)
**Last Updated**: 2026-05-16T15:14:53Z (researcher-9, S3 STATE-SYNC)
**Iteration**: 3 (1 ACT + S2 STATE-SYNC + this S3 STATE-SYNC)

## Iteration 3 (researcher-9, 2026-05-16) — S3 STATE-SYNC

**Outcome**: doc-only — absorb the four residual drift items that S2's
narrow "state.md-only" scope left behind, bootstrap the `sessions/`
directory, and package the `leanFiles[].lineCount: 235 → 247` correction
as a ready-to-paste mechanic handoff. The slug remains
`axiomatized-final` (no math change; the 247-LOC leaf .lean file,
13 theorems, 0 sorries, 0 new axioms, 5 inherited parent axioms is
unchanged since the 2026-05-06 S1 ACT).

### Drift absorbed (4 surfaces; see new memo §2 for verification commands)

- JSON `currentState.iteration` `1 → 3` (catches S2 + S3 in one bump)
- JSON `currentState.since` refresh to `2026-05-06T00:00:00Z` (gallery
  promote canonicalisation; not S3 ship time per memo §5.10)
- JSON `currentState.attemptCounts.total` `0 → 3` (never bumped through
  S1 ACT or S2 STATE-SYNC)
- JSON `lastUpdate` (top-level) `2026-05-05T02:57:44.792Z (seeker create)
  → 2026-05-16T15:14:53Z`
- JSON `currentState.focus` minor refresh to reference S3 + S2 STATE-SYNCs
- JSON `currentState.nextAction` adds 1-sentence mechanic handoff pointing
  at memo §3 (leanFiles drift) without self-editing the leanFiles field
- JSON `knowledge.nextSteps` populated from `[]` with 2 items:
  completed-final declaration + 1 mechanic handoff note pointing at memo §3
- `sessions/` directory bootstrapped with this session memo as first entry

### Not done (out of scope per memory feedback)

- No `leanFiles[]` self-edit (mechanic territory; memo §3 packages the
  ready-to-paste correction)
- No `proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean` edit (slug
  is axiomatized-final; Lean unchanged)
- No gallery `meta.json` edit (all fields correct at branch base SHA)
- No `problem.md` creation (curator batch territory for OQ-class slugs)
- No `knowledge.md` edit (math content unchanged)
- No close/comment on the 4 OPEN PRs for the related-but-distinct
  5-segment slug `borsuk-ulam-oq-02-oq-01-oq-03-oq-02` (informational
  audit only — see memo §4)
- No Docker build (doc-only; daemon hung + disk 5.7 Gi marginal in any
  case)

### Files modified (S3, 3 files, doc-only)

- `research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02/sessions/2026-05-16-s3-state-sync-completed-final.md`
  (new, ~220 LOC, 8 sections — bootstraps the `sessions/` directory).
- `research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02/state.md`
  (this entry + header refresh).
- `src/data/research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02.json`
  (5 `currentState` fields + `lastUpdate` top-level + `knowledge.nextSteps`;
  `leanFiles[]` NOT touched per memo §3.5 mechanic-territory rule).

### Next Action

**None — axiomatized-final**. Future cycles on this slug, if any, are
mechanic (the §3 `leanFiles[].lineCount` correction; ready-to-paste
package supplied), curator (`problem.md` bootstrap for OQ-class slugs
lacking one), or champion (PR audit). Researcher claim-random should
skip this slug going forward.

---

## (Historic) Iteration 2 (researcher-9, 2026-05-14) — STATE-SYNC

**Outcome**: doc-only — refresh canonical `state.md` from seeker-init
stub to a consolidated session log reflecting the slug's COMPLETED
status. Per
`feedback_researcher_canonical_vs_flat_research_problems_dir_divergence.md`,
some slugs that completed earlier have canonical state.md still in
seeker-init form (this slug: NEW / Iteration 1 / "Initial exploration").
Counts against the 2-per-session STATE-SYNC cap.

### Drift identified

- `research/problems/.../state.md` (this file, pre-sync): `Phase: NEW`,
  `Iteration: 1`, `Current Focus: Initial exploration of the problem.`
- `src/data/research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02.json`:
  `phase: COMPLETED`, `status: completed`, `iteration: 1`,
  `focus: Completed: proved k-prime CRT generalization with 0 sorries`,
  `knowledge.progressSummary: COMPLETE 2026-05-06: 0 sorries, 0 axioms.
  buDim CRT generalized to squarefree n = p1*...*pk via k-prime
  induction. Gallery entry created.`
- Gallery `src/data/proofs/.../meta.json` `meta`: `status: axiomatized`,
  `badge: axiom`, `sorries: 0`, `axiomCount: 5` (parent imports),
  `lineCount: 247`, `theoremCount: 13`.

Lean file `proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean`
exists at 247 LOC with 13 theorems. Slug is genuinely complete; only
the canonical state.md was never advanced past seeker init.

### Result (consolidated session log)

* **Initial creation (seeker-spawned, 2026-05-05)**: slug NEW, no
  problem/knowledge artefacts beyond JSON metadata.

* **ACT (2026-05-06)**: proved k-prime CRT generalization
  `buDim_eq_sup_primeFactors` for all n ≥ 2 (and the squarefree
  restriction `buDim_squarefree_crt`). New file
  `proofs/Proofs/BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ02.lean` at 247 LOC:
  - `buDim_eq_sup_primeFactors`: `buDim n d = n.primeFactors.sup (buDim · d)`
    for all `n ≥ 2`.
  - `buDim_squarefree_crt`: squarefree restriction (trivially follows).
  - `buDim_le_sup_primeFactors`, `buDim_prime_le_of_dvd`,
    `buDim_le_prod_primes`, `sup_buDim_le_buDim_prod`: the directional
    inequalities and their products-of-primes specialisation.
  - `primeFactors_prod_primes`: `primeFactors (∏ S) = S` for a Finset
    of primes (inductive proof via `Nat.primeFactors_mul` +
    membership). Two cooperative lemmas: `two_le_prod_primes`
    discharges the `2 ≤ n` hypothesis.
  - `buDim_prod_primes_eq`: the CRT formula
    `buDim (∏ S) d = S.sup (buDim · d)` for a `Finset` of distinct
    primes.
  - `crt_recovers_semiprime`: semiprime specialisation
    `buDim (p * q) d = max (buDim p d) (buDim q d)` for distinct
    primes `p ≠ q`.
  - Concrete cases via `native_decide`: `buDim 30 d`, `buDim 210 d`,
    `buDim 2310 d` (the first three primorials).

  Counts: 13 theorems / 0 definitions / 0 sorries / 0 new axioms.
  Reuses 5 parent-file axioms: `buDim`, `buDim_two`, `buDim_prime`,
  `buDim_mono`, `buDim_le_formula` (from BorsukUlamOQ02OQ01 and
  BorsukUlamOQ02OQ01OQ01).

* **Gallery promote (2026-05-06)**: `src/data/proofs/.../meta.json`
  created with `status: axiomatized`, `badge: axiom`, `sorries: 0`,
  `axiomCount: 5`. `JSON.phase` → `COMPLETED`, `status` → `completed`.

### Mathlib v4.26.0 surface notes (from this slug)

* `Nat.primeFactors_prime` was removed in v4.26.0; replaced with
  `Nat.mem_primeFactors` + `Finset.eq_singleton_iff_unique_mem`.
* `Mathlib.Data.Finset.Lattice` was removed; `Finset.sup_*` are
  available via the `Mathlib.Data.Finset.Basic` + `Tactic` imports.

### Files modified (this STATE-SYNC)

- `research/problems/borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02/state.md` —
  this file. Seeker-init stub → consolidated session log.

### Out of scope

- No `.lean` edits.
- No `meta.json` edits — the gallery entry is correctly
  `status: axiomatized` / `badge: axiom`.
- No JSON edits — `src/data/research/problems/.../json` is already
  at `phase: COMPLETED` / `status: completed`.
- No candidate-pool sync (the pool still lists the slug as
  `status: in-progress`; that drift is seeker/auditor scope and is
  blocked because `.lean/state/candidate-pool.json` is gitignored).

### Race-safety note

* Pre-claim probe (2026-05-14 ~16:00 UTC): `gh pr list --search
  "borsuk-ulam-oq-02-oq-01-oq-01-oq-02-oq-03-oq-02 in:title" --state open`
  returns 0 open PRs on the exact slug. (Search returns PRs for the
  related but distinct slug `oq-02-oq-01-oq-03-oq-02` — 4 segments vs
  6 — which is a different slug.)
* Pre-push probe will re-verify before push.

## (Historic) Iteration 1 (2026-05-05/06) — initial ACT [reconstructed]

See the consolidated log above for the ACT details. The canonical
state.md was never updated past seeker init at that time; this
STATE-SYNC retroactively records the work.
