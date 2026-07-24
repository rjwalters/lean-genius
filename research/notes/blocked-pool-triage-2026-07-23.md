# Blocked-pool triage — 2026-07-23 (issue #43007, epic #43004)

Triage of all 91 `status='blocked'` rows in `research/db/knowledge.db` (pool source of truth,
regenerated into `.lean/state/candidate-pool.json` by `research/db/sync_pool.py` every Seeker cycle).
Applied by `scripts/research/triage-blocked-pool.py` (idempotent; DB backed up to
`knowledge.db.pre-triage-issue43007`).

Root causes found:

- **2026-06-13/14 verification blackout** (Docker daemon hung + Aristotle backend 404): ~40 rows
  were blocked solely because no build/verification route existed. Docker has been healthy for
  weeks (`docker info` exit 0 on 2026-07-23); nothing ever unblocked them.
- **Template placeholders**: 6 rows carried the literal unfilled template
  `[Explain what we're trying to prove in accessible terms]` as `statement_plain` — the string the
  pool surfaces as the BLOCKED reason. Real statements restored from each `problem.md`.
- **No reason at all**: ~20 rows had empty `current_blockers`; several have `state.md` explicitly
  saying "Blockers: None".
- **Stale build-regression claims**: szemeredi-full-oq-01 / roth-theorem-k3-oq-03-incomplete-01 /
  sperner-ndim-mathlib-oq-02 cited v4.26-era parent build errors that predate the v4.31 toolchain
  migration (#39062; RothTheoremOQ03 also repaired in #37676). Returned to pool with a
  verify-parent-build-first next action.
- **Registry-terminal drift**: 5 rows are `graduated` in the tracked registry but were stuck
  `blocked` in the DB (the reconciler only touches servable rows); 1 row is a duplicate of
  completed siblings (-> skipped).

Counts: **54 -> available**, **31 kept blocked** (all with concrete reasons), **5 -> graduated**, **1 -> skipped**; 10 statements de-templated; 37 registry.json entries flipped blocked->active (required so `sync-db-status-from-registry.py` does not re-block the unblocked rows each Seeker cycle).


## Returned to available (54)

- **amgm-inequality-oq-04-oq-03** (sig 9)
- **szemeredi-full-oq-01** (sig 9) — Verify parent build first: the recorded 28-error regression in Proofs.FurstenbergCorrespondenceOQ01 predates the v4.26->v4.31 toolchain migration (#39062) which touched the file; run ./proofs/scripts/docker-build.sh Proofs.FurstenbergCorrespondenceOQ01 and resume the S13 roadmap if green (triage #43007, 2026-07-23)
- **ballot-problem-oq-03-oq-01-oq-02-incomplete-01** (sig 8)
- **bertrands-postulate-oq-02** (sig 8)
- **euler-polyhedral-formula-oq-02-oq-01-wip-01** (sig 8)
- **fundamental-theorem-calculus-oq-02-incomplete-01** (sig 8)
- **ballot-problem-oq-02-oq-05** (sig 7)
- **basel-problem-oq-01-oq-01-oq-02-oq-02** (sig 7)
- **birthday-problem-oq-03-oq-01-oq-02-oq-01** (sig 7)
- **cauchy-interlacing-theorem-oq-01-oq-01-oq-01-oq-01-oq-01** (sig 7)
- **erdos-1151-oq-04** (sig 7)
- **erdos-1210** (sig 7)
- **erdos-szekeres-oq-03** (sig 7)
- **konigsberg-oq-03-wip-01** (sig 7)
- **minkowski-fundamental-theorem-oq-06** (sig 7)
- **prob-method-lovasz-local-oq-01** (sig 7)
- **roth-theorem-k3-oq-03-incomplete-01** (sig 7) — Verify parent build first: the recorded v4.26 API-drift errors in Proofs.RothTheoremOQ03 predate the #37676 drift repair and the v4.31 migration (#39062); run ./proofs/scripts/docker-build.sh Proofs.RothTheoremOQ03, then resume the companion roadmap (triage #43007, 2026-07-23)
- **roth-theorem-oq-02** (sig 7)
- **sperner-ndim-mathlib-oq-02** (sig 7) — Verify parent build first: the recorded 100+ v4.26-drift errors in SpernerFreudenthalSimplex.lean predate the v4.31 migration (#39062) which touched the file; run ./proofs/scripts/docker-build.sh Proofs.SpernerFreudenthalSimplex and resume the rebase queue if green (triage #43007, 2026-07-23)
- **sum-of-divisors-oq-02** (sig 7)
- **abel-ruffini-galois-extensions-oq-05** (sig 6)
- **abel-ruffini-oq-08** (sig 6)
- **binomial-theorem-oq-02-oq-01-oq-01-oq-03** (sig 6)
- **bounded-prime-gaps-oq-03-oq-02** (sig 6)
- **cayley-hamilton-cyclic-vector-all-fields-oq-01-oq-01-oq-01** (sig 6)
- **cayley-hamilton-minpoly-oq-02-oq-01-oq-01-oq-01** (sig 6)
- **central-limit-theorem-oq-01-oq-01-oq-04-oq-01** (sig 6)
- **erdos-1006-oq-01-oq-02** (sig 6)
- **erdos-659-oq-01-oq-02** (sig 6)
- **erdos-735-oq-04** (sig 6)
- **fermat-defect-one-oq-02** (sig 6)
- **fodor-pressing-down-oq-04** (sig 6)
- **gauss-wilson-non-cyclic-oq-02** (sig 6)
- **gauss-wilson-non-cyclic-oq-03** (sig 6)
- **general-quartic-oq-02** (sig 6)
- **godel-second-incompleteness-oq02-oq-02** (sig 6)
- **greens-theorem-oq-01-oq-01-oq-02-oq-01** (sig 6)
- **greens-theorem-oq-01-oq-01-oq-02-oq-02** (sig 6)
- **hilbert-14-oq-04** (sig 6)
- **inverse-galois-d4-oq-03** (sig 6)
- **pell-equation-oq-05** (sig 6)
- **product-of-segments-of-chords-oq-03** (sig 6)
- **shannon-channel-coding-oq-02-oq-01-oq-01** (sig 6)
- **shapley-folkman-oq-01** (sig 6)
- **sperner-simplicial-instance-oq-01** (sig 6)
- **sqrt2-minpoly-oq-03** (sig 6)
- **triangle-inequality-oq-04-oq-01** (sig 6)
- **ballot-problem-oq-01-oq-02-oq-01-oq-02-oq-01** (sig 5)
- **chinese-remainder-non-coprime-oq-01-oq-02** (sig 5)
- **desargues-theorem-oq-02-oq-02** (sig 5)
- **erdos-szekeres-oq-02** (sig 5)
- **halting-problem-oq-03** (sig —)
- **motivic-flag-maps-oq-03** (sig —)
- **weak-goldbach-oq-03** (sig —)

## Kept blocked, concrete reasons (31)

- **euler-polyhedral-formula-oq-02-oq-01-oq-01** (sig 9): Mathlib gap: no Gaussian curvature, geodesic curvature, Riemannian area form, manifold integration, or Stokes for manifolds-with-boundary; re-survey when these land in Mathlib (triage #43007, 2026-07-23)
- **algebraic-numbers-countable-oq-03** (sig 8): Gelfond-Schneider transcendence requires machinery absent from Mathlib (even Hermite-Lindemann is gated on upstream Mathlib PR #28013, cf. nth-root-irrational-oq-03); also no problem.md grounding under research/problems/ (triage #43007, 2026-07-23)
- **sperner-ndim-oq-05** (sig 8): Human-only step: refresh rjwalters/mathlib4:sperner-abstract-parity with current SpernerMathlib4.lean and submit the upstream Mathlib PR (ref mathlib4#25231); no research-agent action possible until then (triage #43007, 2026-07-23)
- **bertrands-postulate-oq-01** (sig 7): Cramer's conjecture is open mathematics (1936; provable under RH only) — removing axiom cramer_conjecture is infeasible for any agent; Mathlib also lacks PNT-strength analytic number theory (triage #43007, 2026-07-23)
- **cevas-theorem-oq-01-oq-02** (sig 7): Ungrounded stub: no research/problems/cevas-theorem-oq-01-oq-02/ directory (no problem.md or state.md); needs seeker re-grounding before serving (triage #43007, 2026-07-23)
- **erdos-1168-oq-04** (sig 7): Ungrounded seeker stub: no research/problems/erdos-1168-oq-04/problem.md; demoted by seeker 2026-06-16; needs re-grounding (triage #43007, 2026-07-23)
- **erdos-166-oq-04** (sig 7): Ungrounded seeker stub: no research/problems/erdos-166-oq-04/problem.md; demoted by seeker 2026-06-16; needs re-grounding (triage #43007, 2026-07-23)
- **erdos-476-oq-05-incomplete-01** (sig 7): Ungrounded seeker stub: no research/problems/erdos-476-oq-05-incomplete-01/problem.md; demoted by seeker 2026-06-16; needs re-grounding (triage #43007, 2026-07-23)
- **erdos-604-incomplete-01** (sig 7): Mathlib gap: Landau-Ramanujan density theorem absent; workable fallback per state.md is axiomatizing it as a named hypothesis (status: axiomatized, blocker disclosed) (triage #43007, 2026-07-23)
- **erdos-998-oq-02** (sig 7): Ungrounded seeker stub: no research/problems/erdos-998-oq-02/problem.md; demoted by seeker 2026-06-16; needs re-grounding (triage #43007, 2026-07-23)
- **four-square-distribution-oq-01** (sig 7): Mathlib gap: no q-expansion/Fourier-coefficient machinery for jacobiTheta and no Eisenstein-coefficient identification (theta^4 vs E2(tau) - 4*E2(4tau)) (triage #43007, 2026-07-23)
- **hilbert-11-oq-02** (sig 7): Mathlib gap: Hasse-Weil bound for genus-1 curves over F_p absent — the unconditional Case-B universal theorem is multi-session Mathlib-scale work (triage #43007, 2026-07-23)
- **hurwitz-theorem-wip-01** (sig 7): Mathlib gap: no classical Frobenius theorem for real division algebras (finite-dim associative division algebra over R has finrank in {1,2,4}); verified absent 2026-05-08 (triage #43007, 2026-07-23)
- **inclusion-exclusion-oq-01-oq-02** (sig 7): Ungrounded: no research/problems/inclusion-exclusion-oq-01-oq-02/ directory and corrupted statement metadata; needs seeker re-grounding (triage #43007, 2026-07-23)
- **nth-root-irrational-oq-03** (sig 7): Hermite-Lindemann discharge gated on upstream Mathlib PR #28013; remaining S5d path needs continued-fraction API absent from the pinned Mathlib (triage #43007, 2026-07-23)
- **algebraic-numbers-countable-oq-02-oq-01** (sig 6): Ungrounded: no research/problems/algebraic-numbers-countable-oq-02-oq-01/ state; blocked in registry with no recorded reason; needs re-triage/grounding (triage #43007, 2026-07-23)
- **cantor-diagonalization-oq-01-oq-01-oq-02-oq-01** (sig 6): At axiom floor: 4 genuine Easton-1970 realizability axioms require class-forcing infrastructure absent from Mathlib (multi-year); no session-sized discharge exists (triage #43007, 2026-07-23)
- **ehrhart-cube-proven-oq-05** (sig 6): Soundness blocker: the S5 target picks_theorem_derived is FALSE as stated (S4 OBSERVE, PR #23003 constant-curve/placement counterexample); the proposition must be restated before any ACT (triage #43007, 2026-07-23)
- **erdos-1036-oq-01-oq-01** (sig 6): Ungrounded: no research/problems/erdos-1036-oq-01-oq-01/ state and no recorded blocker; blocked status inherited without reason — needs seeker re-grounding (triage #43007, 2026-07-23)
- **erdos-1039-oq-04** (sig 6): Ungrounded: no research/problems/erdos-1039-oq-04/ state and no recorded blocker; blocked status inherited without reason — needs seeker re-grounding (triage #43007, 2026-07-23)
- **erdos-258-oq-01** (sig 6): General non-monotone case is open mathematics (Erdős problem 258); no state grounding recorded under research/problems/ (triage #43007, 2026-07-23)
- **erdos-460-incomplete-01** (sig 6): Ungrounded: no research/problems/erdos-460-incomplete-01/ state and no recorded blocker; blocked status inherited without reason — needs seeker re-grounding (triage #43007, 2026-07-23)
- **erdos-818-incomplete-01** (sig 6): Elementary provable layer mined out across prior sessions; remaining axioms are deep (vein saturated — see prior researcher session records) (triage #43007, 2026-07-23)
- **erdos-895-incomplete-01** (sig 6): barber_theorem positive direction needs a >1000-line SAT/case proof (graph space 2^(n choose 2), not decide-able, not session-sized; Aristotle not a fit); counterexample direction fully shipped; mined out across 7 sessions (triage #43007, 2026-07-23)
- **godel-second-incompleteness-oq02-oq-01** (sig 6): init-gap phantom: no research/problems/godel-second-incompleteness-oq02-oq-01/problem.md; demoted by seeker 2026-07-07; needs re-grounding (triage #43007, 2026-07-23)
- **infinitude-primes-4k1-oq-03** (sig 6): Mathlib gap: the natural-density form requires an Ikehara/Tauberian transfer absent from Mathlib (triage #43007, 2026-07-23)
- **kepler-conjecture-oq-03** (sig 6): init-gap phantom: no research/problems/kepler-conjecture-oq-03/problem.md; demoted by seeker 2026-07-07; needs re-grounding (triage #43007, 2026-07-23)
- **prime-number-theorem-oq-01** (sig 6): Target is the Riemann Hypothesis itself — open mathematics; no formal proof path exists (triage #43007, 2026-07-23)
- **erdos-1002-oq-01-wip-01** (sig 5): Ungrounded: no research/problems/erdos-1002-oq-01-wip-01/ state and no recorded blocker; blocked status inherited without reason — needs seeker re-grounding (triage #43007, 2026-07-23)
- **erdos-1064-oq-03** (sig 4): Ungrounded: no research/problems/erdos-1064-oq-03/ state and no recorded blocker; blocked status inherited without reason — needs seeker re-grounding (triage #43007, 2026-07-23)
- **erdos-1093-oq-02** (sig 4): state.md is Phase BLOCKED without a recorded blocker; needs per-problem re-triage before serving (triage #43007, 2026-07-23)

## Reconciled to graduated per registry (5)

- **cevas-theorem-oq-01-oq-01** (sig 7)
- **greens-theorem-oq-02-oq-02** (sig 7)
- **tietze-extension-theorem-oq-01-oq-02** (sig 6)
- **wilson-theorem-oq-01** (sig 6)
- **spherical-law-of-sines-oq-03** (sig 5)

## Skipped as duplicate (1)

- **dilworth-theorem-oq-01-oq-03** (sig 6): Duplicate of completed work under sibling slugs dilworth-theorem-oq-01 and dilworth-theorem-oq-01-oq-01-oq-02 (state.md: SURVEYED, do not build) (triage #43007, 2026-07-23)

## Post-triage pool state

- 261 available (was 207), 31 blocked (was 91), 145 graduated, 17 skipped, 102 in-progress, 3631 completed
- Available at sig>=8: szemeredi-full-oq-01 (9), amgm-inequality-oq-04-oq-03 (9),
  bertrands-postulate-oq-02 (8), fundamental-theorem-calculus-oq-02-incomplete-01 (8),
  euler-polyhedral-formula-oq-02-oq-01-wip-01 (8), ballot-problem-oq-03-oq-01-oq-02-incomplete-01 (8)
- Blocked at sig>=8 (all with specific reasons): euler-polyhedral-formula-oq-02-oq-01-oq-01 (9,
  Mathlib Riemannian-geometry gap), sperner-ndim-oq-05 (8, human-only upstream Mathlib PR),
  algebraic-numbers-countable-oq-03 (8, Gelfond–Schneider transcendence gap)
- 0 blocked entries with template-placeholder reasons

## Persistence

Verified by simulating a full Seeker cycle (`sync-db-status-from-registry.py` +`sync_pool.py`)
against the triaged DB and the patched registry: the reconciler makes 0 changes and the
regenerated pool preserves every disposition.

**Pre-merge caveat**: until the registry.json flip in this PR lands on main (and reaches the
main checkout the Seeker runs from), the live reconciler will re-block the 37 unblocked rows
whose registry status was still `blocked`. The triage script is idempotent — after merge, run
once from the repo root to heal any re-blocked rows:

```bash
python3 scripts/research/triage-blocked-pool.py --apply && python3 research/db/sync_pool.py
```
