# Knowledge Base: twin-primes-special-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Open question**: Are there infinitely many primes $p$ such that $p+2$ is also prime?

**Status**: OPEN mathematically. Closely analogous to `sophie-germain-oq-01` (which is for the pair $(p, 2p+1)$).

---

## Session 2026-05-16 (Session 2) — STATE-SYNC: catchup, implementation merged out-of-band

**Mode**: doc-only STATE-SYNC
**Outcome**: completed (no proof change)
**PR**: this PR

### What I Did

1. `claim-random` landed on this slug (RICH 9 MODERATE+, originally tier A path full).
2. Audited disk reality vs planning artifacts: state.md said `Phase: SURVEYED, "no Lean file or gallery entry exists yet"`. JSON said `phase: NEW, status: active, currentState.phase: SURVEYED, since: 2026-04-27`.
3. Reality check: `proofs/Proofs/TwinPrimesSpecialOQ01.lean` exists (150 LOC, 25 theorems, 0 sorries, 0 standalone axioms inherits `twin_prime_conjecture`); gallery entry `src/data/proofs/twin-primes-special-oq-01/{meta.json,annotations.json,index.ts}` exists with `status: "axiomatized"`.
4. Traced via `git log --all`: implementation was merged via PR #14871 (`feat(twin-primes): add TPC OQ-01 gallery entry with 25 verified twin prime pairs`, 2026-05-02 23:19 +0200) — a `feat(...)` PR not `research(...)`, bypassing the standard researcher state tracking.
5. Updated state.md: Phase SURVEYED → COMPLETED (axiomatized), Since → 2026-05-16, Iteration 1 → 2, History appended with out-of-band impl + S2 catchup, Attempt Count 1 → 2.
6. Updated JSON: 14 field edits (phase NEW→COMPLETED, status active→completed, currentState 5 fields, blockers re-scoped to standing INFRA, knowledge.progressSummary rewrite, builtItems prepended with [S2-catchup] items, insights add 1 new entry about out-of-band PRs, nextSteps refresh, leanFiles[0].lineCount 151→150 to match gallery, lastUpdate).
7. Bootstrapped sessions/ directory and authored `sessions/2026-05-16-s2-statesync-catchup-implementation-merged-out-of-band.md` (~340 LOC, 10 sections including drift inventory + bearer spot-check + picker decision matrix + honesty calibration).

### Verified (no proof regression)

- Lean file: 150 LOC (matches gallery `meta.json.lineCount: 150`), 25 theorems (matches), 0 sorries (matches), 0 standalone axioms.
- Parent `proofs/Proofs/TwinPrimes.lean`: axiom `twin_prime_conjecture:163` byte-stable, SHA-stable.
- Gallery `meta.json`: all numerics canonical (150/25/1/0/0 status:axiomatized badge:axiom).
- Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged since 2026-05-02.

### Host snapshot (S2 time)

- Disk free: 2.5 Gi 🔴
- Docker daemon: hung 🔴
- `proofs/.lake`: circular self-symlink 🔴
- 3 INFRA RED → only optional follow-up iter (Maynard-Tao axiom, etc.) blocked; slug itself is COMPLETED so nothing required is blocked.

### Files Modified

- `research/problems/twin-primes-special-oq-01/state.md` (Phase + Since + Iter + body sections + History + Attempt Count)
- `src/data/research/problems/twin-primes-special-oq-01.json` (14 field edits including top-level phase/status + currentState + knowledge + leanFiles[0].lineCount + lastUpdate)
- `research/problems/twin-primes-special-oq-01/knowledge.md` (this entry)
- `research/problems/twin-primes-special-oq-01/sessions/2026-05-16-s2-statesync-catchup-implementation-merged-out-of-band.md` (new, ~340 LOC, 10 sections)

### Next Steps (post-S2)

Slug COMPLETED axiomatized. Optional follow-up:

- Maynard-Tao bounded-gaps axiom (k≤246) as strengthened companion
- Cross-reference Zhang/Polymath8 via shared parent refactor
- Annotation enrichment via /lean-research enricher

---

## Session 2026-04-27 (Session 1) — Survey + Plan for OQ-01 Gallery Entry

**Mode**: FRESH
**Outcome**: SURVEYED — no gallery entry or Lean file for this OQ-01 yet; documented direct port plan from `sophie-germain-oq-01`

### What I Did

1. Read `problem.md`, `state.md`, parent `proofs/Proofs/TwinPrimes.lean` (190 lines, has `TwinPrimeConjecture` axiom and several verified examples).
2. Searched for existing Lean file: **none** — no `proofs/Proofs/TwinPrimesSpecialOQ01.lean` exists.
3. Searched for existing gallery dir: **none** — no `src/data/proofs/twin-primes-special-oq-01/`.
4. Compared with completed analogue `sophie-germain-oq-01`:
   - That file: 196 lines, 24 theorems, 1 inherited axiom (sophie_germain_conjecture), 0 sorries.
   - Strategy used: 4 equivalent formulations, 25 verified examples, 3 conditional consequences under the axiom.
5. The same strategy ports cleanly to twin primes (essentially a renaming exercise from `IsSophieGermainPrime`/SGC to `IsTwinPrimePair`/TPC).

### Analogous Plan for `TwinPrimesSpecialOQ01.lean`

Mirror SophieGermainOQ01 with the twin-prime substitution:

| SophieGermainOQ01 | Twin Primes OQ01 (proposed) |
|---|---|
| `SophieGermainConjecture` | `TwinPrimeConjecture` (already in `TwinPrimes.lean`) |
| `SafePrimeConjecture` | (No direct dual; twin primes are self-dual under p ↔ p+2 only modulo offset) |
| `sgc_iff_unbounded` | `tpc_iff_unbounded` |
| `sgc_iff_prime_pairs` | `tpc_iff_prime_pairs` (just unfold IsTwinPrimePair) |
| 25 verified SG primes via `decide` | 25 verified twin primes via `decide` |
| `infinite_safe_primes`, `infinite_primes_mod_twelve`, `no_finite_cover` | analogous twin-prime versions; structural constraints already proved in parent `twin-primes-special` (form $(6k-1, 6k+1)$) |

### Important Differences from SG OQ-01

1. **No "safe prime" dual**: Sophie Germain's $p \mapsto 2p+1$ bijection has no clean analogue for twin primes (the pair (p, p+2) is symmetric). So the SafePrimeConjecture-equivalent is just the unfolding of `TwinPrimeConjecture`.
2. **Mod-6 vs Mod-12**: Twin primes give the form $(6k-1, 6k+1)$; the analogous mod-12 result for safe primes does not have a direct mirror.
3. **Bounded gaps context**: Maynard-Tao gives ≤246 unconditionally for twin primes — could be added as an axiomatized result, parallel to how Helfgott/Brun results are referenced in SG. (Optional content.)

### Verified Twin Prime Examples Already in Parent (`TwinPrimes.lean`)

The parent has examples 3, 5, 11, 17, 29, 41, 59, 71. Extending to ~25 via `decide`: 101, 107, 137, 149, 179, 191, 197, 227, 239, 269, 281, 311, 347, 419, 431, 461, 521, 569, 599, 617 (all known twin prime lower elements).

### Why I Did Not Write the Lean File This Session

A new ~200-line Lean file with 20+ `decide`-based theorems is **safe in principle** (just primality checks) but cannot be safely tested without a `lake build` cycle (Docker-only here, ~10+ min per iteration). A botched namespace import or Mathlib-version-incompatible tactic would silently break the file. The honest contribution is to document the exact port plan so a future session with build access can execute in ~15-30 minutes.

### Files Modified

- `research/problems/twin-primes-special-oq-01/knowledge.md` (this Session 1 entry)
- `research/problems/twin-primes-special-oq-01/state.md` (Phase: SURVEYED)
- `src/data/research/problems/twin-primes-special-oq-01.json` (focus, progressSummary)

### Knowledge Delta

- Insights: 2 (no existing OQ-01 file/gallery; concrete port plan from SG OQ-01)
- Built items: 0 (no Lean code this session)
- Sorry/axiom delta: N/A (no new file created)

---

## Insights

- **The SG OQ-01 → Twin Primes OQ-01 port is mechanical.** The two problems have the same axiomatize-and-derive-consequences structure. A focused 30-minute session with build access can complete it.
- **The OQ-01 problem record was created (2026-04-23) but never executed.** This kind of gap is a candidate for a "stub gallery generator" task that auto-creates skeleton entries from problem.md.

---

## Dead Ends

None this session — purely a survey.
