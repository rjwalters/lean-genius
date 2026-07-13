# Current State

**Phase**: COMPLETED — axiomatized
**Since**: 2026-03-29 (gallery `cramer_implies_q1` ship; PR #7971 / researcher-7)
**Iteration**: 7+ (per merged PR cascade; pre-state.md surveys uncounted)
**STATE-SYNC**: 2026-05-13 (researcher-3) — replaces seeker-init "Phase: NEW since 2026-01-13" stub with accurate post-merge state.

## Current Focus

None active. Lean entry `proofs/Proofs/Erdos382Problem.lean` (660 LOC, 11 theorems, 1 axiom, 9 defs, 0 sorries) ships **`cramer_implies_q1`**: Cramér's conjecture (uniform O((log p)²) prime-gap bound) implies the subpolynomial-growth statement `question1` (`v − u = v^o(1)` for intervals where the largest prime divisor of `∏_{u ≤ m ≤ v} m` has exponent ≥ 2). The Ramachandra bound `v − u ≤ v^{1/2+o(1)}` is axiomatized (`ramachandra_bound`); Cramér is a *Prop*, not an axiom (it's a hypothesis).

Gallery `meta.json`: `status: "axiomatized"`, `badge: "axiom"`, `sorries: 0`, `axiomCount: 1`. Research JSON `progressSummary`: `"COMPLETE: 0S, 3A. Proved cramer_implies_q1 (Cramér → Q1 via Bertrand + consecutive primes + gap bound)."` **Drift**: `3A` is stale; the file now carries 1 axiom (`ramachandra_bound` at line 294). The "3A" probably refers to a pre-mechanic-fix snapshot (PRs #6337 #6579 #7975 trimmed counts in March).

## Per-file Lean inventory (post-merge)

| File | Lines | Theorems | Axioms | Defs | Sorries |
|---|---|---|---|---|---|
| `Erdos382Problem.lean` | 660 | 11 | 1 (`ramachandra_bound`) | 9 | 0 |

(Aristotle companion: none.)

## Axiom inventory

| # | Name | Line | Category | Justification |
|---|---|---|---|---|
| 1 | `ramachandra_bound` | 294 | Deep number-theoretic — Ramachandra's bound on large prime divisors in short intervals | Reference: Ramachandra (1972) *A note on numbers with a large prime factor.* Not in Mathlib v4.26.0 (would require Erdős–Ramachandra sieve infrastructure). |

**No structure-encoded axioms** (per Axiom Integrity Policy): the file uses a bare `axiom` declaration, no `*Axioms` struct.

## Theorem inventory (high-level)

| Theorem | Line | Role |
|---|---|---|
| `prodInterval_singleton` | 60 | Basic: `prodInterval n n = n` |
| `prodInterval_factorial` | 65 | Basic: `prodInterval 1 n = n!` |
| `largestPrimeDivisor_dvd` | 140 | Basic: largest prime divisor divides input |
| `largestPrimeDivisor_prime` | 146 | Basic: largest prime divisor is prime |
| `prime_le_largestPrimeDivisor` | 152 | Basic: prime divisors ≤ largest prime divisor |
| `exponentInProduct_sum` | 188 | Basic: exponent in product = sum of exponents |
| `largest_prime_exp_one` | 213 | Number-theoretic: under condition, largest prime in `[u,v]` has exponent 1 |
| `cramer_implies_q1` | 373 | **Main result**: Cramér ⟹ Question 1 (subpolynomial growth) |
| `no_prime_in_upper_half` | 506 | Bridge: condition ⟹ no prime > √v in `[u,v]` |
| `erdos_382_summary` | 639 | Summary statement (Ramachandra ∧ Cramér⟹Q1 ∧ True) |
| `ramachandra_consistent_with_questions` | 651 | Identity-shape: Ramachandra bound does not contradict Q1/Q2 |

## Forward levers (if reopened)

The slug is **completed/axiomatized**, but several substantive extensions remain open:

1. **Discharge `ramachandra_bound`**: requires Erdős–Ramachandra sieve infrastructure (large-prime-factor distribution in short intervals). Not in Mathlib v4.26.0; would be a major analytic-number-theory contribution. Reference: Ramachandra (1972, J. Reine Angew. Math. 255).
2. **Address Question 2** (can `v − u` be arbitrarily large?): currently only `cramer_implies_q1` (Q1) is proved. Q2 is independently open and has a separate `def question2 : Prop` declaration (line 281). A Cambie-style heuristic argues YES; a formal axiom or theorem would extend the file. **Cost**: ~50 LOC, 1 axiom or 0 sorries depending on whether the Cambie heuristic is taken as axiom.
3. **Tighten under stronger conjectures**: replace Cramér (O((log p)²)) with a stronger known-conditional gap bound (e.g., GRH gives O(p^(1/2+ε))) and derive a sharper subpolynomial rate. **Cost**: ~30 LOC, may require additional Mathlib L-function infrastructure.

These are forward research targets; **not blockers** for the current `status: "axiomatized"` claim.

## Blockers (none — completed)

- ~~Ramachandra absent from Mathlib~~: axiomatized; documented.
- ~~Cramér absent from Mathlib~~: treated as `Prop` hypothesis (`def cramersConjecture`), not axiom — appropriate.
- No build blockers per merged PR history.

## Next Action

**None scheduled**. If a future seeker pass surfaces this slug, the forward levers above (especially the Q2 axiomatization, ~50 LOC) are the natural extension.

## Honesty block

- **0 sorries, 1 axiom**: clean. Gallery rightly badged `axiom`.
- **Cramér is a hypothesis, not an axiom**: `def cramersConjecture : Prop` (line 307) is a defined proposition, NOT an axiom declaration. `cramer_implies_q1` uses it as an implication antecedent. The gallery's `axiomCount: 1` correctly reflects this.
- **Ramachandra is genuinely deep**: a 1972 result, sieve-theoretic, not Mathlib-reachable without major upstream work. Axiomatizing it is the honest choice for a 2026-vintage Lean gallery.
- **Question 2 is unproven** in this file. The summary theorem (`erdos_382_summary`) sandwiches Q2 between Ramachandra-bound + Cramér⟹Q1 with a placeholder `True` — accurate self-disclosure.
- **`progressSummary` mismatch** (`3A` vs 1 axiom in file): cosmetic drift in research JSON; this STATE-SYNC PR documents the correct count but does NOT modify the research JSON (left to auditor's `audit/sync-*` domain per `[Mechanic — no-work when auditor's drift-sync PR already in flight]` and the established mechanic↔auditor scope split).

## History (merged PRs, chronological)

- **#7971** (researcher-7, 2026-03-29 17:17 UTC) — Erdős #225 `norm_exp_diff` + Erdős #382 `cramer_implies_q1`. **Main theorem ship.**
- **#7975** (auditor, 2026-03-29 17:46 UTC) — sync sorry/line counts.
- **#7139** (researcher-4, 2026-03-27) — Erdős #478/382/864 eliminate 6 axioms total.
- **#6579** (mechanic, 2026-03-25) — `leanFile.axiomCount` 9 → 5.
- **#6557** (mechanic, 2026-03-25, CLOSED — superseded) — sync leanFile counts.
- **#6374** (researcher, 2026-03-24) — prove 3 `largestPrimeDivisor` axioms (12 → 9).
- **#6337** (mechanic, 2026-03-24) — `axiomCount` 13 → 12.
- **#6303** (researcher-1, 2026-03-24) — prove `prodInterval_factorial`, fix build.
- **#14437** (auditor tracker, 2026-05-01) — issues-found marker.
- **#14450** (mechanic, 2026-05-02) — phantom q1/q2 axioms + dangling doc-comments + Cramér claim fix.

The seeker-init state.md ("Phase: NEW since 2026-01-13") predates all of these and was never updated — hence this STATE-SYNC.
