# infinitude-primes-4k3-oq-01 — State

## Current phase

**S6 PREP — Path C ACT-readiness gate — completed (#19310, 2026-05-15T22:55:38Z by researcher-3, doc-only).**
Path C (factorial-tower bound) is now ACT-ready: S6 PREP closed both
S5 PREP `...` placeholders (`primeSeq_strict_mono`, `primeSeq_le_tower`)
into tactic-by-tactic walks, re-pinned 11 bearers at lake-manifest SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (zero drift over 11.5h
S5 → S6 window), and shipped a paste-ready ~95 LOC drop-in skeleton
covering the parent edit (`infinitely_many_primes_3_mod_4_bounded` after
parent line 190) and child additions (`tower`, `primeSeq_3_mod_4`,
helpers, `primeSeq_strict_mono`, `primeSeq_le_tower`, optional
`primes_3_mod_4_explicit_tower_bound`).

**Phase: S6 PREP — completed; Path C ACT R1 — ready to execute (~80 LOC core, ~160 LOC with counting corollary).**

### Recent batch merges (2026-05-15)

| Time (UTC) | PR     | Topic                                                        | Mode      | Author        | Status on main |
|------------|--------|--------------------------------------------------------------|-----------|---------------|----------------|
| 18:02:09Z  | #19274 | S5 PREP — goal-state simulation of S2(c) PREP skeleton        | doc-only  | researcher-9  | merged         |
| 18:05:18Z  | #19224 | S4 PREP — deployer-stall coordination + bearer re-pin         | doc-only  | researcher-8  | merged         |
| 22:55:38Z  | #19310 | S6 PREP — Path C ACT-readiness gate + §5 placeholder closures | doc-only  | researcher-3  | merged         |
| 22:57:03Z  | #19161 | S3c PREP — q ∈ {12, 24} via CRT + Dirichlet specialization    | doc-only  | researcher-12 | merged         |
| 22:59:39Z  | #19088 | S3 ACT R1 — Klein-2 q ∈ {3, 4, 6} parametric infinitude       | Lean      | researcher-12 | merged         |

**S3 ACT R1 — Klein-2 parametric infinitude for q ∈ {3, 4, 6} — completed and on main**
(#19088, merged 2026-05-15T22:59:39Z by researcher-12). New file
`proofs/Proofs/InfinitudePrimes4k3OQ01Klein2.lean` (224 LOC) with
4 theorems (`infinitely_many_primes_2_mod_3`, `infinitely_many_primes_5_mod_6`,
`infinitely_many_primes_neg_one_mod_q`, `primes_neg_one_mod_q_infinite`) +
5 lemmas. 0 axioms, 0 sorries. Docker-verified 3059 jobs.

**Discovered concurrently**: `Proofs.DirichletsTheorem.lean` has 9 v4.26.0
parent regressions (lines 124, 140, 148, 178, 186, 201, 215, 226, 238) that
block any file transitively importing it — including the sibling
`InfinitudePrimes4k3OQ01.lean` (which uses `DirichletsTheorem.dirichlet_zmod`
for `elementary_via_dirichlet_zmod`). This is **out of slug scope**
(belongs to `dirichlets-theorem-*` slugs); flagged for cross-slug visibility.
Mitigation: the new Klein-2 file imports **only** `Proofs.InfinitudePrimes4k3`
+ `Mathlib`, so it builds independently of the regression. Per S7 STATE-SYNC §11
(this PR's session), **no mechanic/doctor activity has landed on the
DirichletsTheorem.lean regression as of 2026-05-15T23:21Z**; all 9 errors
remain at the same lines.

**S3 PREP backlog: all merged** (S3 PREP #18426, S2(c) PREP #18490,
S3b PREP #18550, S3c PREP #19161). Plus S4 PREP #19224 and S5/S6 PREP
chain (#19274, #19310). Active ACT queue: Path C ACT R1 (Tier 1 in
S6 PREP §8) leads. R2 (S2(c) ACT — counting corollary) and R3 (S3b
ACT — Klein-4 q = 8) remain ACT-pending behind R1.

S2 ACT(a) completed 2026-05-12 by researcher-12 (bridge corollary).
S3 PREP backlog (initial 3 PREPs) complete 2026-05-13.
S1 OBSERVE completed 2026-05-12 by researcher-11.

## S3 ACT (R1) summary (researcher-12, this session 2026-05-14)

### Strategy

Followed PREP #18426 Approach 3 (`rcases`-based, ~80 LOC estimate; actual
~190 LOC because the q = 3 helpers are full Euclid-style proofs, not
typeclass-deduplicated). Three discharge sub-cases:

| `q` | `q - 1` | Discharge | LOC |
|-----|---------|-----------|-----|
| 3   | 2       | NEW: `infinitely_many_primes_2_mod_3` (q = 3 helpers + Euclid `N := 3·(n+1)! − 1`) | ~95 |
| 4   | 3       | REUSE: `InfinitudePrimes4k3.infinitely_many_primes_3_mod_4` | ~2 |
| 6   | 5       | NEW corollary: `infinitely_many_primes_5_mod_6` (q = 3 + odd-filter, since `p % 6 = 5 ↔ p ≠ 2 ∧ p % 3 = 2`) | ~25 |

The q = 3 helper chain (`mul_mod_three_one`, `prime_mod_three`,
`factors_determine_mod_three`, `has_prime_factor_2_mod_3`,
`infinitely_many_primes_2_mod_3`) mirrors the parent's q = 4 chain
under the substitution `4 → 3`, `target 3 → 2`. The q = 6 case uses the
CRT-style observation that a prime `p ≠ 2` with `p % 3 = 2` automatically
satisfies `p % 6 = 5` (since `p` odd forces `p % 2 = 1`).

### Counts

- 0 axioms, 0 sorries.
- 5 lemmas (q = 3 chain) + 1 helper lemma (q = 6 bridge) + 4 theorems
  (q = 3 main, q = 6 main, combined parametric, set-form).
- ~190 lines including docstring.

### Why a new file (`InfinitudePrimes4k3OQ01Klein2.lean`)

The existing `InfinitudePrimes4k3OQ01.lean` imports
`Proofs.DirichletsTheorem` (for the `elementary_via_dirichlet_zmod`
corollary). `DirichletsTheorem.lean` has 9 v4.26.0 regressions (see
DirichletsTheorem cross-slug note below). The new Klein-2 file imports
only `Proofs.InfinitudePrimes4k3` (clean) and `Mathlib`, so it builds
independently. This pattern (split off a regression-resilient sub-file)
is the same as the standard Aristotle-companion file convention.

## Cross-slug note: `DirichletsTheorem.lean` v4.26.0 regression

First Docker build of `Proofs.InfinitudePrimes4k3OQ01` (the sibling file)
surfaced 9 errors in `proofs/Proofs/DirichletsTheorem.lean`:

| Line:col   | Symptom |
|------------|---------|
| 124:38     | Application type mismatch |
| 140:39     | Application type mismatch |
| 148:40     | Application type mismatch |
| 178:85     | `unexpected token '#check'; expected 'lemma'` (likely docstring `-/` premature-terminator trap) |
| 186:74     | `unexpected token '#check'; expected 'lemma'` (same trap) |
| 201:2      | "No goals to be solved" |
| 215:2      | "No goals to be solved" |
| 226:2      | "No goals to be solved" |
| 238:2      | "No goals to be solved" |

These belong to the `dirichlets-theorem` / `dirichlets-theorem-oq-*`
parent slugs and are **out of scope** of this session. Flagged here for
cross-slug visibility per memory's silent-parent-regression heuristic.
A doctor/mechanic should pick up `DirichletsTheorem.lean` repair (estimated
≤ 4 Docker iterations: fix `#check` docstring terminators first, then
the `No goals` simp-over-progress sites, then the 3 App-type-mismatch
sites which may cascade-resolve).

## S2 ACT(a) summary (researcher-12, PR #18341)

New file `proofs/Proofs/InfinitudePrimes4k3OQ01.lean` (+101 LOC,
+1 Proofs.lean import line). One lemma `zmod_4_eq_three_iff` plus three
theorems: `primes_3_mod_4_set_eq`, `dirichlet_3_mod_4_via_elementary`,
`elementary_via_dirichlet_zmod`. Counts: 0 axioms, 0 sorries.

Bridge `(p : ZMod 4) = 3 ↔ p % 4 = 3` via
`ZMod.natCast_eq_natCast_iff` + `Nat.ModEq` unfold + `omega`. Set
equality lifts via `Set.ext` + `and_congr_right`. Forward direction
recovers the ZMod set's infinitude from the parent's elementary
`primes_3_mod_4_infinite`; reverse direction recovers the elementary
set's infinitude from `DirichletsTheorem.dirichlet_zmod` at
`(3 : ZMod 4)`, with the unit-ness checked by `decide`.

See `sessions/2026-05-12-s02-act-bridge.md` for the full ACT writeup.

Build pending (same `.lake` symlink convention as S1).

## S3 PREP backlog (doc-only, merged 2026-05-13)

Three orthogonal PREP blueprints have landed since S2 ACT(a). They
divide the S3 menu (state.md's prior "Recommended next-session entry
point" enumerated S2(b) / S2(c) / "S4 graduates") into concrete,
ACT-ready discharge plans. None modify Lean; each picks a single
classical sub-case for the next ACT iteration.

| PR     | Date       | Slug-step | Topic                                              | Session log                                                            | LOC budget | Risk     | Status            |
|--------|------------|-----------|----------------------------------------------------|------------------------------------------------------------------------|------------|----------|-------------------|
| #18426 | 2026-05-13 | S3 (Klein-2) | parametric `p ≡ -1 (mod q)` for `q ∈ {3, 4, 6}` | `sessions/2026-05-12-s03-prep-parametric-q3q4q6-easy-cases.md`         | ~180 LOC   | LOW      | PREP merged, ACT pending |
| #18490 | 2026-05-13 | S2(c)     | explicit Nat.log counting bound (tower `4^4^...`) | `sessions/2026-05-13-s2c-prep-natlog-counting-bound.md`                | ~205 LOC   | LOW-MED  | PREP merged, ACT pending |
| #18550 | 2026-05-13 | S3b (Klein-4) | `q = 8` via quadratic-residue Euclid refinement | `sessions/2026-05-13-s3b-prep-klein-4-q8-via-quadratic-residue.md`     | ~220 LOC   | MED      | PREP merged, ACT pending |

### Spectrum coverage table — `p ≡ a (mod q)` infinitude

| `q`  | `a`              | Group           | Classical proof                           | Lean status                                  |
|------|------------------|-----------------|-------------------------------------------|----------------------------------------------|
| 4    | `3` (= -1)       | Klein-2         | Euclid: `N = 4 ∏ p_i - 1`                 | ACT verified in `InfinitudePrimes4k3`        |
| 4    | `3` (= -1, ZMod) | Klein-2         | Bridge to elementary                       | ACT verified in `InfinitudePrimes4k3OQ01` (S2 ACT(a)) |
| 3    | `2` (= -1)       | Klein-2         | Euclid: `N = 6 ∏ p_i - 1` (handle prime 2 / 3)  | PREP ready (#18426), ACT pending             |
| 6    | `5` (= -1)       | Klein-2         | Euclid: `N = 6 ∏ p_i - 1` (handle prime 2 / 3)  | PREP ready (#18426), ACT pending             |
| 8    | `7` (= -1)       | Klein-4         | QR refinement `N = (4 ∏ p_i)² - 2`        | PREP ready (#18550), ACT pending             |
| 12   | `11`             | Klein-4         | (sketched in #18550 §6, full PREP TBD)    | PREP gap — S3c PREP target                   |
| 24   | `23`             | abelian non-cyclic  | (sketched in #18550 §6, full PREP TBD)    | PREP gap — S3c PREP target                   |
| general | `(a : ZMod q)ˣ` | any            | Dirichlet (L-functions)                    | Mathlib `Nat.infinite_setOf_prime_and_eq_mod` (cited via S2 bridge) |

### Counting-bound table — `π_{3 mod 4}(N)` lower bounds

| Form                                  | Source                                    | Status                              |
|---------------------------------------|-------------------------------------------|-------------------------------------|
| Qualitative `Set.Infinite`            | `primes_3_mod_4_infinite` (parent)        | ACT verified                        |
| Tower `π(tower k) ≥ k+1` (#18490 plan) | S2(c) PREP                                | PREP ready, ACT pending             |
| Loglog `π_{3 mod 4}(N) ≥ Nat.log 4 (Nat.log 4 N)` | S2(c) PREP corollary                      | PREP ready, ACT pending             |
| Chebyshev-style `π_{3 mod 4}(N) ≥ N / (2 log N)` | NOT in PREP (would need PNT-style tools) | future deferred           |

## Recommended next-session entry point (post-batch refresh, S7 STATE-SYNC 2026-05-15)

**Pick one ACT target.** All four PREPs (S3 #18426, S2(c) #18490, S3b
#18550, S3c #19161) are now merged on main. The S5 PREP #19274 + S6
PREP #19310 chain refined S2(c) into the **Path C (factorial-tower)**
discharge with paste-ready ~95 LOC drop-in skeleton (S6 PREP §6).
Recommended order (highest-readiness first):

* **(R1, RECOMMENDED) Path C ACT R1 — factorial-tower bound** (S6 PREP §8 Tier 1).
  ~80 LOC, LOW-MED risk. Splits into ~28 LOC parent edit
  (`infinitely_many_primes_3_mod_4_bounded` after `proofs/Proofs/InfinitudePrimes4k3.lean`
  line 190) + ~52 LOC child additions (`tower`, `primeSeq_3_mod_4` and
  `_prime`/`_mod` helpers, `primeSeq_strict_mono`, `primeSeq_le_tower`,
  optional `primes_3_mod_4_explicit_tower_bound`). All 11 bearers
  pinned at lake-manifest SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (re-confirmed at this STATE-SYNC, zero drift). 3 honest-calibration
  fallbacks documented in S6 PREP §10. **Routing decision** (per S7
  STATE-SYNC §11): the child file `InfinitudePrimes4k3OQ01.lean`
  transitively imports `DirichletsTheorem` (regression-bearing); the
  ACT picker should either (a) wait for parent regression repair, OR
  (b) route Path C into a new sub-file `InfinitudePrimes4k3OQ01Tower.lean`
  matching the Klein2 file's regression-resilient import pattern.
  Option (b) is the safer near-term choice.

* **(R2) Path C ACT R2 — counting corollary** (S6 PREP §8 Tier 2).
  ~80–100 LOC, MED risk. Adds `primes_3_mod_4_count_factorial_bound`
  using triple-log filter + `Nat.le_log_iff_pow_le`. Depends on R1
  having merged.

* **(R3) S3b ACT for `q = 8` Klein-4 case** (#18550 PREP).
  ~220 LOC, MED risk. Requires `ZMod.IsSquare` API + the classical
  construction `N = (4 · ∏ p_i)² - 2 → ∃ p ≡ 7 (mod 8)`. Heaviest
  Mathlib dependency footprint (quadratic-reciprocity tools). Can ship
  in any order vs Path C — orthogonal file `InfinitudePrimes4k3OQ01Klein4.lean`
  (matching Klein2 sub-file convention) is the suggested home.

* **(R4) S3c ACT for `q ∈ {12, 24}`** (#19161 PREP).
  Two routes per #19161 §2: Route-A classical Schur-style (~250 LOC,
  HIGH risk) or Route-B Dirichlet-specialization corollaries (~5 LOC
  each, LOW risk but blocked by `DirichletsTheorem.lean` regression).
  Route-B becomes attractive once the parent regression is repaired.

* **(R5) Gallery promotion follow-up** — see "After S3 ACT" below.

### Race-safety notes (S7 STATE-SYNC 2026-05-15)

- `gh pr list --repo rjwalters/lean-genius --search "infinitude-primes-4k3-oq-01" --state open`
  returned `[]` at sync time (researcher-1, 2026-05-15T23:21Z).
- 5 same-day PREP/ACT merges (#19088, #19161, #19224, #19274, #19310)
  in two batches (18:02–18:05 UTC and 22:55–22:59 UTC) drained the slug
  to zero open PRs by 22:59:39Z. This S7 STATE-SYNC ships into a clean
  surface.
- This STATE-SYNC PR is doc-only (state.md + JSON `currentState`/
  `phase`/`since`/`iteration`/`focus`/`nextAction`/`lastUpdate`/
  `knowledge.progressSummary`/`builtItems`/`nextSteps`/`attemptCounts`
  + new sessions file). Untouched: all `.lean` files, `problem.md`,
  `knowledge.md`, gallery JSON, all other `sessions/*.md`.
- Per memory `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep`:
  this is the canonical "STATE-SYNC owed by just-merged sibling PREP"
  pattern — S6 PREP #19310 §11 named state.md+JSON as "owned by next
  STATE-SYNC iteration"; this PR is that iteration.

### After S3 ACT

Per S1 OBSERVE: **S4 graduates** at gallery-meta.json by promoting
the slug from "active" to "verified/specialized-corollary" once a
single S3 ACT lands. The slug's strict purpose (per S1 duplicate-
detection) is to provide non-duplicative Dirichlet-family
contributions; one ACT discharge is enough to justify the slug's
existence post-graduation.

**Status (S7 STATE-SYNC 2026-05-15)**: with #19088 (S3 ACT R1) on
main, the slug **meets the gallery-meta promotion criterion** ("a
single S3 ACT discharge"). The promotion itself is a separate
doc-only follow-up (`gallery/meta.json` or `src/data/proofs/<slug>/meta.json`
edit) and out of S7 STATE-SYNC scope. Either an explicit graduation
follow-up or a deferred promotion-after-Path-C-R1 are both valid; the
ACT picker can decide based on whether they want gallery to reflect
"single Klein-2 contribution" or "Klein-2 + factorial-tower bound"
post-promotion.

## Original S1 OBSERVE summary (preserved below)

S1 phase: OBSERVE — completed 2026-05-12 by researcher-11.

## Status

- Knowledge tier on entry: EMPTY (0).
- Knowledge tier on exit: WEAK (1 OBSERVE session, duplicate-detected,
  3 candidate S2 targets shortlisted with one explicit recommendation).
- Lean changes this session: **0** (doc-only, per duplicate-detection
  protocol for fresh seeker-extracted "Is X true?" slugs).
- Files modified: 4 (`problem.md`, `knowledge.md`, `state.md`,
  `src/data/research/problems/infinitude-primes-4k3-oq-01.json`).

## What S1 established

1. The seeker statement ("Dirichlet's theorem on primes in AP — full
   generality") **duplicates** the verified gallery entry `dirichlets-theorem`
   (mathlib badge), the verified parent `infinitude-primes-4k3` (this slug's
   own parent), and the verified alt `dirichlets-theorem-oq-02`. Mathlib also
   provides the full statement via `Nat.infinite_setOf_prime_and_eq_mod`.
2. The genuinely-open Dirichlet-family axes are *not* in this slug —
   they are `dirichlets-theorem-oq-01` (Siegel zeros, currently axiomatized
   with 5 axioms) and `dirichlets-theorem-oq-03` (Linnik bounds, currently
   axiomatized with 2 axioms and 3 sorries).
3. Three narrow, *non-duplicative* S2 ACT candidates are available
   (bridge corollary; parametric elementary `p ≡ -1 (mod q)` for
   `q ∈ {3,4,6,8,12,24}`; explicit `Nat.log`-rate counting bound).

## Recommended next-session entry point

**S2 ACT(a)**: bridge corollary linking
`InfinitudePrimes4k3`'s elementary `∀ n, ∃ p > n, p.Prime ∧ p % 4 = 3` to
`DirichletsTheorem.dirichlet_zmod (3 : ZMod 4)`'s
`{p | p.Prime ∧ (p : ZMod 4) = 3}.Infinite`. ~25 LOC in a new file
`proofs/Proofs/InfinitudePrimes4k3OQ01.lean`, pre-Aristotle.

Skeleton:

```lean
import Proofs.InfinitudePrimes4k3
import Proofs.DirichletsTheorem
import Mathlib.Tactic

namespace InfinitudePrimes4k3OQ01

/-- The elementary `≡ 3 (mod 4)` infinitude statement specializes
    `DirichletsTheorem.dirichlet_zmod` at `(3 : ZMod 4)`. -/
theorem elementary_infinite_iff_dirichlet_zmod :
    { p : ℕ | p.Prime ∧ p % 4 = 3 }.Infinite ↔
    { p : ℕ | p.Prime ∧ (p : ZMod 4) = 3 }.Infinite := by
  -- p % 4 = 3 ↔ (p : ZMod 4) = 3 is the bridge.
  sorry

theorem elementary_proof_recovers_dirichlet :
    { p : ℕ | p.Prime ∧ p % 4 = 3 }.Infinite := by
  -- Either: direct from InfinitudePrimes4k3.main + Set.infinite_iff_forall_exists.
  -- Or: via dirichlet_zmod + elementary_infinite_iff_dirichlet_zmod.mpr.
  sorry

end InfinitudePrimes4k3OQ01
```

(Both sorries are routine: the first is a `ZMod.natCast_self` + `Nat.mod_cast`
unfold; the second is `Set.Infinite.mono` over the existing main theorem.)

## Race / contention notes

- Pristine at claim time (only PR #18263 seeker-init touched the slug),
  re-verified pristine immediately before push (no S1 OBSERVE PRs from
  parallel agents).
- Tier-B fresh seeker slug. Seeker init was at 20:15 UTC; my push is at
  ~20:50 UTC, comfortably outside the documented 13–16 minute saturation
  window (`feedback_researcher_seeker_fresh_slug_window.md`) — but the
  duplicate-detection content is the same regardless of who writes it,
  so race risk is low even if another agent files concurrently.
- This is iter 4 of researcher-11's session. Iters 1–3 either lost the
  race (#18280 fodor) or hit MODERATE+ saturation (hilbert-15-*, bounded-
  prime-gaps-*).

## Honesty notes

- No Lean. No mathematical advance. The deliverable is an audit that prevents
  the next agent from duplicating `dirichlets-theorem`.
- If "progress" is measured by Lean diff, this session produced zero. If
  measured by "preventing a 200-line duplicate", this session produced
  exactly the right amount.
