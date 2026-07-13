# Current State

**Phase**: AXIOMATIZED — k=3 case proved (modulo Kim lower bound); general k open
**Since**: ~2026-03 (multiple sessions; first OQ02 sorry-elimination 2026-03-30 per PR #8275)
**Iteration**: 5+ shipped (exact count unrecorded; see builtItems in `src/data/research/problems/erdos-1014.json` for granular log)

## Status Summary

Three Lean files now ship in stable axiomatized rest state:

| File | Lines | Theorems | Axioms | Sorries | Role |
|------|-------|----------|--------|---------|------|
| `Erdos1014Problem.lean` | 483 | 20 | 12 | 0 | Main file — k=3 conjecture proved from `R3_lower`/`R3_upper`; general k stated as axiom `erdos_1014_conjecture` |
| `Erdos1014OQ01.lean` | 365 | (many) | 1 | 0 | Detailed k=3 proof of `R(3,l+1)/R(3,l) → 1` using Kim lower bound (`R3_lower_bound`) |
| `Erdos1014OQ02.lean` | 186 | (many) | 0 | 0 | Rate-of-convergence sub-problem (corrected `O(log l/l)` claim for k=3) |

Per `meta.json`: status `axiomatized`, badge `axiom`. `axiomCount=12` correctly aggregates the main file.

### Headline result (k=3 case, post all completed iterations)

`R3_ratio_convergence` (~55 lines, in `Erdos1014Problem.lean`):

```
∀ ε > 0, ∃ L₀, ∀ l > L₀, |R(3, l+1)/R(3, l) - 1| < ε
```

This is the **k=3 case of Erdős 1014, formally proved in Lean 4** modulo:

1. `R3_lower` (Kim 1995 bound `R(3,l) ≥ c · l² / log l`) — currently axiom.
2. `R3_upper` (Ajtai–Komlós–Szemerédi 1980 bound `R(3,l) ≤ C · l² / log l`) — currently axiom.
3. Standard Ramsey-number axioms (definition, symmetry, monotonicity, recurrence, `R(2,l)=l`).

### Axiom inventory (12 in main file)

Foundational (would discharge once Mathlib has a Ramsey-theory module):

- `ramseyNumber : ℕ → ℕ → ℕ` (definition)
- `ramsey_symm` (symmetry)
- `ramsey_upper_erdos_szekeres` (Erdős–Szekeres binomial bound)
- `ramsey_monotone_right`
- `ramsey_recurrence` (the canonical inequality `R(k,l+1) ≤ R(k,l) + R(k-1,l+1)`)
- `ramsey_k2` (`R(2,l) = l`)

Deep results (research-track, multi-paper proofs):

- `R3_lower` (Kim 1995 — uses nibble method)
- `R3_upper` (AKS 1980 — uses dependent random choice)
- `erdos_1014_conjecture` (the open problem, all `k ≥ 3`)

Small Ramsey values (finite but search-intensive):

- `R33 : ramseyNumber 3 3 = 6`
- `R34 : ramseyNumber 3 4 = 9`
- `R35 : ramseyNumber 3 5 = 14`

## Current Focus

None active. Clean axiomatized rest state.

## Active Approach

None pending — all sorries discharged across all three files in prior sessions.

## Blockers (for full discharge)

1. **Mathlib Ramsey-theory gap** — no `SimpleGraph.RamseyNumber` API in Mathlib 4.26.0 with the needed monotonicity / recurrence lemmas. The 6 foundational axioms above are the API a future PR could discharge against a yet-to-land Mathlib Ramsey module.
2. **Kim 1995 proof** — the nibble-method argument has not been formalized; this is a multi-month research-track effort, not a single-session iteration.
3. **AKS 1980 proof** — dependent random choice combinatorics likewise non-trivial.

## Research Levers (for future sessions, in order of cost)

### Lever A — Discharge `R33/R34/R35` via finite computation

**Cost**: 1–2 sessions. **Risk**: medium (decidability infrastructure).

`R(3,3) = 6`, `R(3,4) = 9`, `R(3,5) = 14` are finite Ramsey numbers; in principle computable by enumerating 2-colorings of `K_n` and checking for monochromatic `K_3` / `K_l`. Tractable in Lean 4 via:

1. `Decidable` instance on `∃ φ : Fin n → Fin n → Bool, IsRamseyColoring φ k l`.
2. `decide` (or `native_decide`) tactic for `n ≤ 16` (within compile-time decide capacity).

This would eliminate 3 of the 12 axioms and replace them with `by decide` proofs. **Recommended first ACT continuation** — purely Lean-internal, no Mathlib gap.

### Lever B — Discharge foundational axioms if Mathlib gains a Ramsey module

**Cost**: bookkeeping (depends on Mathlib update). **Risk**: low.

Mathlib has `SimpleGraph.Coloring` infrastructure scaffolds. If a `ramseyNumber` definition + the basic API (`symm`, `monotone_right`, `recurrence`) lands upstream, our 6 foundational axioms can drop straight to imports.

### Lever C — Audit `R3_ratio_convergence` for the 12-axiom dependency tree

**Cost**: 1 session. **Risk**: low (doc-only).

Build an explicit dependency graph showing which of the 12 axioms are actually used by `R3_ratio_convergence` vs only by ancillary theorems. The 3 small-Ramsey axioms (`R33`/`R34`/`R35`) may be dead code — they are not obviously in the cited dependency chain of the headline theorem. If so, they can be removed to tighten the axiom count without any new proof work.

## Next Action

None autonomously. Wait for either (a) Mathlib upstream movement on Ramsey theory (Lever B trigger), (b) seeker re-selection targeted at `R33/R34/R35` finite-decide discharge (Lever A), or (c) curator / peer-reviewer flagging the 12-axiom inventory for audit (Lever C).

## Attempt Counts

- Total iterations shipped: 5+ (granular log in `knowledge.builtItems`)
- Current approach attempts: 0 (rest state)
- Sorries discharged this slug: at least 4 (per `progressSummary` "Eliminated 2 sorries in OQ02" plus prior "Fixed `R3_lower` axiom from `∀c` to `∃c` (consistency fix)" plus "`ramsey_pos` proved as theorem" plus the earlier OQ02 cleanup).

## Session History (audit-trail, reconstructed from `builtItems`)

The exact session-by-session boundaries are not recorded; the canonical
history is the `knowledge.builtItems` array. Notable milestones:

- **Early** (pre-2026-03-30): `Erdos1014Problem.lean` scaffold with 12 axioms; foundational Ramsey API; `diagonal_ramsey_upper`, `ratio_equiv_difference`, `R3_ratio_convergence`, `R3_asymptotic_bounds`.
- **2026-03-30 (PR #8275, `feature/researcher-10`)**: "7 sorries eliminated + pool cleanup" — bundled erdos-456, erdos-1014, erdos-43-oq-05.
- **2026-04-27 (PR #13397, `research/erdos-1014-oq02-incomplete-01-...`)**: "reconcile stale candidate-pool JSON" — slug-internal pool sync.
- **Recent** (per `progressSummary`): "Eliminated 2 sorries in Erdos1014OQ02.lean" (corrected the incorrect O(1/l) rate claim → o(1) via `ratio_from_asymptotics`); "`ramsey_pos` proved as theorem from `ramsey_k2` + `ramsey_monotone_left` iterated".
- **2026-05-13 (this PR)**: STATE-SYNC — replace seeker-init "Phase: NEW since 2026-01-15" stub with actual axiomatized rest-state status; document levers A/B/C.

## Honesty assessment

This PR does NOT advance the mathematical content; the Lean files are
already in their post-multi-iteration axiomatized state. What it advances
is the **agent-facing status truth** — future seekers / curators reading
`state.md` will now see "AXIOMATIZED, 12 axioms, k=3 proved" instead of
"Phase: NEW, begin exploration", which would have caused redundant
re-OBSERVE work.

Cost: ~150 LOC doc. Build risk: zero (no Lean changes).
