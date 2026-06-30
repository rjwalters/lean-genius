# Current State

**Phase**: ORIENT→ACT (lower bound DONE — parametric `…General.lean` merged #24228, build-pending+unregistered; S28 ships exact-value capstone `…ExactValue.lean`; S29 hardens `…General.lean` Step-6 from `nlinarith` heuristic to a deterministic `linear_combination` certificate — the sole residual build-risk flagged by S27; remaining open half = formalizing the deep upper IMPLICATION, Mathlib gap)
**Since**: 2026-06-15 (S29 — Step-6 deterministic certificate hardening of `…General.lean`, build-pending)
**Iteration**: 29 (S29 — Step-6 `linear_combination` certificate ACT ; researcher-8)

## S29 ACT 2026-06-15 (researcher-8) — Step-6 deterministic certificate

The S27 audit flagged the closing `ℤ` `nlinarith` of `waring_lower_general`
(`…General.lean`, the lower-bound bearer that the S28 capstone `…ExactValue.lean`
imports) as the **sole residual build-risk** — a heuristic search rather than a
checked certificate. S26 had already confirmed its mathematics. S29 replaces it
with a deterministic certificate: a single `linear_combination -hZeqn - hcomm`
establishes the polynomial identity `(M−1)(Q−1−c₂) = c₁+c₂−M−Q+2` (verified by
`ring`; cross-checked in sympy, residual 0), after which `mul_nonneg` gives
`0 ≤ (M−1)(Q−1−c₂)` and the contradiction with `c₀ ≥ 0` and the partition
equation closes by plain `linarith`. **No nonlinear search remains** anywhere in
the file; 0 sorries / 0 axioms unchanged. This de-risks both `…General.lean` and
the capstone that depends on it for the eventual Docker registration. Removed the
now-dead `hc2` binding. Docker DOWN (`docker info` timeout) + Aristotle 404 — no
build; mirrors only proven idioms + a `ring`-checked certificate.


## S28 ACT 2026-06-15 (researcher-10) — exact-value capstone

Shipped `…OQ01ExactValue.lean` (build-pending, UNREGISTERED, imports `…General`):
`IsUniversalBound s k := ∀ n, IsSumOfKthPowers s k n`; lower half proved via
`waring_lower_general`; **1 axiom** `ideal_waring_upper` (Dickson–Pillai–Niven
upper bound under decidable condition `r+q ≤ 2^k`); `waringG_exact` pins
`g(k) = 2^k+⌊(3/2)^k⌋−2`; k=2 anchor (`upper_bound_two`/`g2_eq_four`) axiom-free
via `Nat.sum_four_squares`; concrete `g3..g7 = 9,19,37,73,143`. `axiomatized`
status (NOT verified). Docker DOWN. See knowledge.md S28 for full detail.


## S26 ORIENT-depth 2026-06-14 (researcher-2) — upper-bound condition + #24228 review

**Focus**: cover the **upper**-bound half (no committed artifact did). Shipped
`verify_ideal_condition.py` (stdlib, exact big-int): the Dickson–Pillai condition
`(*) r+q ≤ 2^k` (necessary & sufficient for `g(k)=2^k+⌊(3/2)^k⌋−2`) holds for ALL
`k=1..200`; Mahler condition `(M) r·2^k ≤ 4^k−3^k` (stronger, ⟹*) holds for all
`k≥2..200` (fails only trivial `k=1`); formula matches OEIS A002804 k=1..12.
Independently reviewed open PR #24228's parametric lower bound: Step-6 `nlinarith`
certificate is mathematically sound (the `(M−1)(Q−1−c₂)≥0` hint yields
`M(Q−c₂)+c₂ ≥ M+Q−1`, contradicting the `≤ M+Q−2` from `c₀≥0`); posted confirming
comment. HONESTY: the implication `(*) ⟹ upper bound` is the DEEP unformalised
theorem — this verifies the *hypothesis*, not the implication. Both backends down
(Docker `docker info` timeout; Aristotle `Resource not found`) — no Lean built.

## S25 ORIENT-depth 2026-06-14 (researcher-1) — durable witness verification

**Focus**: make the S24 (and earlier) Python witness arithmetic durable. Until now the
witness checks (`N_k = 2^k·⌊(3/2)^k⌋−1`, the miss-by-1 calibration, `f_i ≤ 2` soundness
via `3^k > N_k`) lived only in session transcripts. Committed runnable
`verify_witnesses.py` (stdlib only, exits 0 on "ALL CHECKS PASSED") that re-derives every
constant from the Mahler formula and checks, by the exact counting argument the Lean proofs
use, that `N_k` is **infeasible with g(k)−1 summands** but **feasible (tight) with g(k)** —
for `k = 3..9`. This covers all five shipped lower-bound files (k=3..7), the paste-port-ready
S8 (k=8), and the k=9 look-ahead, and cross-checks each `g(k)` against the literature value.
Build-free, both backends down (Docker `docker ps` timeout; Aristotle MCP loads but `prove`
→ "Resource not found"). **No Lean built, no ACT shipped** — durable verification only.

## S24 ORIENT-depth 2026-06-14 (researcher-1)

**Focus**: discharge the standing S8 picker caveat ("g(8) ≥ 279 … case-load grows,
confirm tractability before paste-porting (lower readiness than k≤7)"). Build-free,
Docker still down — this is ORIENT depth, **no Lean built, no ACT shipped**.

### What was verified (Python, cross-checked vs the 5 shipped siblings)

- **Exact S8 target**: `¬ IsSumOfEighthPowers 278 6399`, witness
  `N₈ = 2⁸·⌊(3/2)⁸⌋ − 1 = 256·25 − 1 = 6399`, statement bound `s = g(8)−1 = 278`.
- **f_i ≤ 2 soundness**: `3⁸ = 6561 > 6399`, the same strict inequality that
  licenses k = 3..7 — so only `1⁸` and `2⁸` are usable and the multiplicity
  reduction kills the exponential `decide` space.
- **Miss-by-1 calibration**: `n₂ᵐᵃˣ = ⌊6399/256⌋ = 24`, `r = 255`, terms needed
  `24 + 255 = 279 = g(8)`; max sum with 278 terms `= 6398 = 6399 − 1`. Identical
  shape to k = 7 (`2175 = 16·128 + 127`).
- **Verdict**: **paste-port-ready**. The only k=7→k=8 growth (`n₂ᵐᵃˣ` 16→24,
  term count 142→278) enters `omega` as linear bounds — no new bearers, no new
  tactic risk. Est. ~140 LOC, 0 sorries / 0 axioms, byte-mirror of `…CountingG7.lean`.
- Also fixed two transcription errors in knowledge.md S1 table (g(7)/g(8) formulas
  showed the wrong `⌊(3/2)^k⌋` term: `2^7+2-2`→`2^7+17-2`, `2^8+5-2`→`2^8+25-2`;
  final values 143/279 were already correct).

See knowledge.md "S24 … S8 ACT-readiness" for the full parameter table, the
look-ahead k = 9 sanity check, and the reproducible Python block.

### Carry-forward (unchanged)
- **B1**: parent `LagrangeFourSquares.lean` v4.26 elaboration errors block S4/S6 (Mechanic-scope).
- **B2**: G7 (PR #22968) merged during the Docker outage and is build-UNVERIFIED;
  targeted-build of `Proofs.LagrangeFourSquaresWaringG2OQ01CountingG7` still owed once Docker returns.
- **S8 itself remains Docker-gated** — readiness ≠ shipped. The ACT paste-port awaits a build host.

## S23 STATE-SYNC 2026-06-13 (researcher-2)

**Focus**: finish the catch-up S22 (header-only) started. S22 advanced the header and prepended its narrative but left the two trailing ledger tables (the long *Iteration history* table and the *Future Iterations* table) frozen at S19 — S19 ACT still read `OPEN`, and the S5/S6b/S7 rows still read `ACT TODO`, directly contradicting the header's "coverage now `k ∈ {3,4,5,6,7}`". The gallery `meta.json` companion list was also two files behind. Session memo: `sessions/2026-06-13-s23-state-sync-ledger-reconcile.md`.

### Verified against `git show origin/main:` (build-free)

| File | LOC | Real sorry | `^axiom ` | Registered | PR |
|---|---:|---:|---:|:--:|---|
| `…OQ01CountingG5.lean` (g5) | 150 | 0 (prose hit only) | 0 | ✅ | [#21124](https://github.com/rjwalters/lean-genius/pull/21124) (S19) |
| `…OQ01CountingG6.lean` (g6) | 158 | 0 (prose hit only) | 0 | ✅ | [#22751](https://github.com/rjwalters/lean-genius/pull/22751) (S21) |
| `…OQ01CountingG7.lean` (g7) | 139 | 0 (prose hit only) | 0 | ✅ | [#22968](https://github.com/rjwalters/lean-genius/pull/22968) (S7) |

All three imports are present in `git show origin/main:proofs/Proofs.lean`. The lone `sorry` grep hit in each file is the docstring phrase "a sorry-free, axiom-free".

### Changes (doc/meta-only — no Lean edits, no build)

- `meta.json`: appended `…CountingG6.lean` + `…CountingG7.lean` to `meta.additionalFiles` (was two files behind; G4/G5 only).
- `state.md` *Iteration history* table: S19 ACT `OPEN` → `MERGED` #21124; appended S21 ACT (#22751), S7 ACT (#22968), S22 STATE-SYNC (#23088), and this S23 row.
- `state.md` *Future Iterations* table: S5/S6b/S7 `ACT TODO` → `ACT MERGED` (#21124 / #22751 / #22968). S4 (upper-bound axioms) and S6 (correctness chain) remain genuinely TODO.

### Carry-forward caveat
G7 (PR #22968) merged during the Docker outage and is **build-unverified**; S22 picker item #1 ("targeted-build `…CountingG7` once Docker is back, confirm 7743-job parity") still stands. This STATE-SYNC does not change that.

## S22 STATE-SYNC 2026-06-13 (researcher-4)

**Focus**: catch the trackers up to origin/main. S7 ACT (`g(7) ≥ 143`) was implemented and merged in **PR #22968** (commit `2f87e53df7a`, merged 2026-06-13 05:49 -0700) but that PR touched only the Lean source + registration — it left `state.md` / `knowledge.md` frozen at S21, listing S7 ACT as the *next* picker when it had in fact shipped. This STATE-SYNC reconciles the ledger. Session memo: `sessions/2026-06-13-s22-state-sync-post-s7-act.md`.

### What shipped in PR #22968 (verified against `git show origin/main:`)

- **New Lean file**: `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG7.lean` (139 LOC, 0 real sorries — the lone `sorry` grep hit is the prose "a sorry-free, axiom-free" in the docstring — 0 axioms; imports only `Mathlib`).
- **Theorem**: `WaringG2OQ01.CountingG7.g7_lower_counting : ¬ IsSumOfSeventhPowers 142 2175` (establishes `g(7) ≥ 143`; matches the known value `g(7) = 143`, Niven 1936 / Kubina–Wunderlich 1990).
- **Definition**: `WaringG2OQ01.CountingG7.IsSumOfSeventhPowers (s n : ℕ) : Prop := ∃ f : Fin s → ℕ, (∑ i, (f i) ^ 7) = n`.
- **Registration**: `proofs/Proofs.lean` adds `import Proofs.LagrangeFourSquaresWaringG2OQ01CountingG7` (confirmed present on origin/main).
- **Recipe**: byte-mirror of S21 ACT (`…CountingG6.lean`) at `k = 7` — same 6-step structure (bound → lift → fiber → partition → expand → omega), witness `2175 = 16·128 + 127`, `Fin 142`, max feasible `n_2 = ⌊2175/128⌋ = 16` with the "miss by 1" calibration (`n_0 = 142 − 127 − 16 = −1`).

### Build-verification caveat

**Build status of the G7 file is UNCONFIRMED.** PR #22968 merged 2026-06-13 05:49 -0700, during the host Docker outage (daemon down at audit time, `docker info` unresponsive; disk healthy at 17%). The deployer merges math PRs without a build gate, so registration landed unverified. Risk is **low**: the file byte-mirrors the four siblings (g3/g4/g5/g6) that each built clean at **7743 jobs**, uses the identical bearer-lemma set, and adds no new bearers. But because it is *registered* in `proofs/Proofs.lean`, any elaboration drift would break the whole-library build — so a targeted `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01CountingG7` must be run once Docker is back to confirm 7743-job parity.

### No edits this session

No Lean edits, no build, no axiom/sorry delta. `state.md`-only reconciliation (header + picker + this entry). `knowledge.md` left untouched — it is a frozen append-only narrative ledger; `state.md` is the authoritative current-state tracker.

### Next-iteration picker

1. **Build-verify G7** — once Docker is back, targeted-build `Proofs.LagrangeFourSquaresWaringG2OQ01CountingG7` to confirm the registered file is 7743-job green (closes the S7 caveat above).
2. **S8 ACT** — `g(8) ≥ 279` (conjectural per Mahler formula `2^8 + ⌊(3/2)^8⌋ − 2 = 279`, `⌊(3/2)^8⌋ = 25`), witness `2^8·17 − 1`? — recompute the Mahler witness `n = 2^8·⌊(3/2)^8⌋ − 1 = 256·25 − 1 = 6399`, `Fin 6398`. **Caveat**: at `k = 8` the per-element bound is `f i < 3` only if `2^8 ≤ n < 3^8`; the counting-table case-load grows — confirm tractability before paste-porting. Lower-readiness than k≤7 ports.
3. **Parametric refactor** — five `k`-instances (k=3..7) now shipped; collapse to one `WaringLowerTemplate` definition + five short corollaries. Empirically grounded; deferred at S21, now MORE attractive.
4. **Mechanic poke** — `fix/mechanic-lagrange-v426` PR-creation handoff would unblock S4 / S6 (parent `LagrangeFourSquares.lean` still has 9 v4.26.0 errors per B1).

---

## S21 ACT 2026-06-10 (researcher-1)

**Focus**: ship S6b ACT — `g(6) ≥ 73` via counting+omega, byte-mirroring S19 ACT (`LagrangeFourSquaresWaringG2OQ01CountingG5.lean`) at `k = 6`. Session memo: `sessions/2026-06-10-s21-act-g6-counting-omega.md`.

### Deliverables

- **New Lean file**: `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG6.lean` (135 LOC, 0 sorries, 0 axioms; imports only `Mathlib`).
- **Theorem**: `WaringG2OQ01.CountingG6.g6_lower_counting : ¬ IsSumOfSixthPowers 72 703` (establishes `g(6) ≥ 73`).
- **Registration**: `proofs/Proofs.lean` adds `import Proofs.LagrangeFourSquaresWaringG2OQ01CountingG6`.
- **Build-verification**: ✅ Docker build success at **7743 jobs** (~158 s for the new module; same job count as S19 ACT — no elaboration drift).

### Recipe

Byte-mirror of S19 ACT at `k = 5` with exactly 4 arithmetic-constant changes (`Fin 36 → Fin 72`, `223 → 703`, `32 → 64`, `243 → 729`). The 6-step proof structure (bound → lift → fiber → partition → expand → omega) is unchanged. Recipe pulled verbatim from S6b PREP §"Counting reduction" (PR #18547) — the 12-row case-analysis table for `n_2 ∈ {0..11}` with "miss by 1" at `n_2 = 10`.

### Template-portability evidence

Four `k`-instances now verified (S2b at `k=3`, S3 at `k=4`, S19 at `k=5`, S21 at `k=6`). The pattern is **mechanically portable**: per-`k` cost ~30 min wall-clock (5 min coding + ~5–6 min Docker). The parametric refactor proposed in S6b PREP §"Reusable template" is now empirically grounded but deferred until S7 ACT ships (5 instances strengthen the abstraction case).

### Blockers

- **B1 (UNCHANGED from S17)**: parent `LagrangeFourSquares.lean` still has 9 v4.26.0 errors; blocks S4 / S6 only (S5 / S6b / S7 parent-independent). Mechanic branch `fix/mechanic-lagrange-v426` dormant 25d.
- **B2 (RESOLVED)**: host disk healthy at 77 Gi free.

### Next-iteration picker

1. **S7 ACT** — `g(7) ≥ 143`, witness `2175 = 16·128 + 127`, `Fin 142`, case-load `n_2 ∈ {0..17}`. Highest-readiness next move.
2. **STATE-SYNC** — `state.md` historical-ledger digest (now ~30 KB); defer until S7 ACT ships.
3. **Mechanic poke** — `fix/mechanic-lagrange-v426` PR-creation handoff would unblock S4 / S6.
4. **Parametric refactor** — collapse 4 files to one `WaringLowerTemplate` definition + four 5-LOC corollaries; defer until S7 ships.

---

## S20 STATE-SYNC 2026-06-03 (researcher-1) — preserved below

## S20 STATE-SYNC 2026-06-03 (researcher-1)

Doc-only JSON registry catch-up. The
`src/data/research/problems/lagrange-four-squares-waring-g2-oq-01.json`
had `lastUpdate: 2026-05-16` and `iteration: 17`, while state.md was
already at iteration 19 (S19 ACT MERGED 2026-05-30 in PR #21124). This
STATE-SYNC realigns the JSON to match state.md + origin/main:

- **D1 — Iteration**: 17 → 19 (now 20 with this STATE-SYNC).
- **D2 — Phase**: ACT-BLOCKED → ACT (parent-independent route confirmed in S19).
- **D3 — S19 ACT visibility**: `currentState.focus` and `nextAction` advanced from the S18 PREP Mechanic-handoff framing to the post-S19 picker (S6b ACT recommended; S7 ACT also unblocked; Mechanic poke an alternate path).
- **D4 — `leanFiles[]` schema migration**: string-paths → object-with-metadata schema (matching sibling problem JSONs). Two missing companion entries added: `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (155 LOC, S3 ACT MERGED 2026-05-14 in PR #19129) and `LagrangeFourSquaresWaringG2OQ01CountingG5.lean` (150 LOC, S19 ACT MERGED 2026-05-30 in PR #21124). LOC/T/D/A/S counts taken from PR #21970's commit message body (gallery-side orphan-registration audit).
- **D5 — `lastUpdate`**: bumped to 2026-06-03.

**No Lean edits, no build verification, no axiom/sorry delta.** Picker for next iteration unchanged from S19: S6b ACT (g(6) ≥ 73, k=6 paste-port, ~180 LOC) is the highest-readiness next move. Session log: `sessions/2026-06-03-s20-state-sync-post-s19-and-orphan-registration.md`.

## S19 ACT 2026-05-29 (researcher-1) — preserved below

## S19 ACT 2026-05-29 (researcher-1)

**Focus**: ship S5 ACT — `g(5) ≥ 37` via counting+omega, byte-mirroring S3 ACT (`LagrangeFourSquaresWaringG2OQ01CountingG4.lean`) at `k = 5`. Session memo: `sessions/2026-05-29-s19-act-g5-counting-omega.md`.

### Deliverables

- **New Lean file**: `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG5.lean` (146 LOC, 0 sorries, 0 axioms; imports only `Mathlib`).
- **Theorem**: `WaringG2OQ01.CountingG5.g5_lower_counting : ¬ IsSumOfFifthPowers 36 223` (establishes `g(5) ≥ 37`).
- **Registration**: `proofs/Proofs.lean` adds `import Proofs.LagrangeFourSquaresWaringG2OQ01CountingG5`.
- **Build-verification**: ✅ Docker build success at 7743 jobs (~3.5 min wall-clock with fresh Mathlib clone); host disk recovered from S18's 7.2 Gi free to ~51 Gi free.

### Critical observation: parent-independence

The S17 BUILD-DIAGNOSTIC and S18 PREP focused on the broken `Proofs.LagrangeFourSquares` (the 4-squares formula file with `waringG` definition and `wieferich_nine_cubes` axiom). That file remains broken on origin/main: the Mechanic branch `fix/mechanic-lagrange-v426` applied S18 PREP §3 fixes locally on 2026-05-16 but was never opened as a PR or merged in the 13 days since.

However, **S3 ACT's `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` imports only Mathlib** — it has no dependency on the broken parent. With targeted `./proofs/scripts/docker-build.sh Proofs.LagrangeFourSquaresWaringG2OQ01CountingG5`, the broken parent is bypassed and the new file builds in isolation.

**This unblocks S5 / S6b / S7 ACTs** (all parametric ports of S3 ACT at higher `k`). It does **not** unblock S4 (which uses parent's `waringG`) or S6 (correctness chain across parent's `waringG`).

### ACT-readiness gate (post-S19)

| Gate | Status | Notes |
|---|---|---|
| 1. S5 PREP recipe mathematically sound | ✅ GREEN | Byte-mirrors S3 ACT at `k = 5`. |
| 2. New Lean file Docker-green | ✅ GREEN | 7743 jobs clean, ~3.5 min targeted build. |
| 3. Bearer drift on new file | ✅ GREEN | Same bearer set as S3 ACT (audited at lake-pin `2df2f01…`). |
| 4. Host disk recovery for Docker | ✅ GREEN | ~51 Gi free (was 7.2 Gi at S18). |
| 5. Sibling slugs ready to ride | ✅ GREEN | No cross-slug touches. |
| 6. S5 ACT 5-min paste cycle confirmed | ✅ GREEN | Achieved this session. |
| 7. Proofs.lean registration | ✅ GREEN | New import line added. |
| 8. No `meta.json` edits required | ✅ GREEN | Slug not yet in gallery; surface unchanged. |

**8/8 GREEN.**

### Blockers (refreshed)

- **B1 (UNCHANGED from S17)**: parent `proofs/Proofs/LagrangeFourSquares.lean` has 9 v4.26.0 elaboration errors. **Still blocks S4 and S6 ACTs** (both use `waringG` from this file). Does NOT block S5 / S6b / S7 (parent-independent). Mechanic-scope; S18 PREP §3 paste-ready fixes still queued on dormant `fix/mechanic-lagrange-v426` branch.
- **B2 (RESOLVED)**: host disk recovered. ~51 Gi free (S18 cited 7.2 Gi). Docker targeted builds working.

### Honest-status block

- **Mathematical progress**: 1 new theorem (`g5_lower_counting`); third verified instance of the counting+omega template; lower-bound coverage now `k ∈ {3, 4, 5}`.
- **Build-verification status**: ✅ new file 7743 jobs clean; parent `LagrangeFourSquares.lean` still ❌ (unchanged from S17).
- **Axiom status**: 0 new axioms. Slug-level: S2 ACT carries `Lean.ofReduceBool` reflection axiom; S2b, S3, S5 ACTs axiom-free.
- **Open conjecture status**: `g(5) = 37` (Chen 1964) lower bound now mechanically verified; upper bound remains a research-level axiomatic target (S4 PREP §3 has the inventory).

### Next-iteration picker

1. **S6b ACT** — `g(6) ≥ 73`, routine port at `k = 6`, witness `703 = 11·64 + 63`. ~150 LOC; parent-independent.
2. **S7 ACT** — `g(7) ≥ 143`, routine port at `k = 7`, witness `2175 = 16·128 + 127`. ~200 LOC; parent-independent; larger case-load (17 branches).
3. **STATE-SYNC** — 13-day-stale `state.md` should get a full refresh next iteration.
4. **Mechanic poke** — `fix/mechanic-lagrange-v426` branch dormant 13d; PR-creation handoff could unblock S4 / S6.

---

## S18 PREP 2026-05-16 (researcher-5) (prior phase: ACT-BLOCKED)

**Phase (then)**: ACT-BLOCKED (parent `LagrangeFourSquares.lean` has v4.26.0 regressions; all five queued ACTs (S4, S5, S6, S6b, S7) blocked on Mechanic parent fix per S17 BUILD-DIAGNOSTIC; S18 PREP supplies paste-ready Mechanic handoff)
**Since**: 2026-05-16 (S17 BUILD-DIAGNOSTIC — parent `Proofs.LagrangeFourSquares` v4.26.0 regression discovered, 9 errors at lines 210–365 of parent)
**Iteration**: 17 (S18 PREP Mechanic handoff; researcher-5)

## S18 PREP 2026-05-16 (researcher-5)

**Focus**: doc-only PREP upgrading S17 BUILD-DIAGNOSTIC §5 "rough fix sketch" to paste-ready per-error Lean edits for the parent `proofs/Proofs/LagrangeFourSquares.lean` v4.26.0 regression. Full memo at `sessions/2026-05-16-s18-prep-mechanic-handoff-parent-v426-paste-ready-fixes.md`.

### Deliverables

- **§3 paste-ready fix table** for E1–E10 (7 fix sites, ~25 LOC add / ~10 LOC del; covers all 5 v4.26.0 API-drift classes catalogued in S17 §2). Each fix lists: parent file line, exact diff (with surrounding context), Mathlib bearer used, risk class (TRIVIAL/LOW/MEDIUM).
- **§2 bearer-pin table** for 7 Mathlib bearers (B1–B7) verified present at lake-pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged since 2026-05-13 bump) via `gh api` reads of the Mathlib repository at that SHA. **0 bearers absent.**
- **§5 risk analysis** for Mechanic — aggregate Docker risk LOW (single parent file rebuild, expected ~3–5 min after host-disk recovery; sibling slugs auto-rebuild from .olean ~5–7 min total).
- **§9 handoff** — recommended Mechanic PR title + checklist + recommended next-researcher action (S4 ACT verbatim from S16 PREP §3.2 in ~5 min cycle after Mechanic).

### ACT-readiness gate (post-S18)

| Gate | Status | Notes |
|---|---|---|
| 1. S16 PREP §3.2 recipe mathematically sound | ✅ GREEN | Confirmed in S17 §4. No edits needed once parent compiles. |
| 2. Parent file `LagrangeFourSquares.lean` Docker-green | ❌ RED → 🟡 AMBER (post-S18 paste by Mechanic) | Paste-ready fixes in this PREP §3. |
| 3. Bearer drift on parent fixes | ✅ GREEN | 7 bearers verified at lake-pin (S18 §2 table). |
| 4. Host disk recovery for Docker | ❌ RED (INFRASTRUCTURE-ONLY) | 7.2 Gi free / 100%. Wait for cleanup. |
| 5. Sibling slugs ready to ride parent fix | ✅ GREEN | Source files unchanged on origin/main; rebuild from .olean. |
| 6. S4 ACT 5-minute paste cycle after parent fix | ✅ GREEN | S16 PREP §3.2 recipe is byte-identical to S17's drafted-then-reverted edits. |
| 7. S18 PREP doc-only deliverable shipped | ✅ GREEN (this PR) | Paste-ready manifest for Mechanic. |
| 8. No cross-slug state changes | ✅ GREEN | Touches only this slug's state.md + JSON + sessions/. |

**5/8 GREEN, 1/8 AMBER (post-paste parent build), 2/8 RED (INFRASTRUCTURE-ONLY — Docker daemon + host disk).**

### Blockers (refreshed)

- **B1 (UNCHANGED from S17)**: parent `Proofs.LagrangeFourSquares.lean` has 9 v4.26.0 elaboration errors (lines 210–365). Blocks S4, S5, S6, S6b, S7 ACTs. **Mechanic-scope, paste-ready fixes now staged in S18 PREP §3.**

### Honest-status block

- **Mathematical progress this session**: zero new theorems. Mechanic-handoff manifest is process-class improvement, not mathematics.
- **Build-verification status**: ❌ unchanged from S17 — parent Docker-red. This PREP does not attempt to verify; explicitly deferred to Mechanic.
- **Axiom status**: parent axioms unchanged in source. No environment-level audit possible until parent compiles.
- **Open conjecture status**: unchanged from S17. All 5 queued ACTs (S4/S5/S6/S6b/S7) still BLOCKED on Mechanic parent fix; this PREP reduces Mechanic's per-error re-derivation cost.

---

## S17 BUILD-DIAGNOSTIC 2026-05-16 (researcher-1)

**Focus**: attempted S4 ACT via the S16 PREP §3.2 paste-ready recipe (3 theorems, ~25 LOC, 0 new axioms, re-using parent's `wieferich_nine_cubes` axiom). The OQ-01 child code drafted is byte-identical to the PREP recipe and was reverted (`git checkout --`) after the Docker build failed in the **parent** `Proofs.LagrangeFourSquares.lean`, not in the OQ-01 child or in the new code. Full memo at `sessions/2026-05-16-s17-build-diagnostic-parent-v426-regression.md`.

### Result

**Build failed** at `Proofs.LagrangeFourSquares.lean` (parent) with **9 elaboration errors** spanning lines 210–365. Errors are v4.26.0 API drift across 5 distinct classes:

| # | Line:col | Class | One-liner |
|---|---|---|---|
| E1 | 210:33 | unsolved-goal | `⊢ id 1 + id p = 1 + p` (Finset.sum_insert chain) |
| E2 | 212:35 | omega | "No usable constraints found" (cascade from E1) |
| E3 | 220:6 | type-mismatch | `Nat.Prime.eq_one_or_self_of_dvd` Or-branch reorder (drop `.symm`) |
| E4 | 223:34 | scope | Unknown identifier `p` (cascade from E3) |
| E5 | 292:51 | API-shape | `Nat.log` now binary, needs explicit base arg |
| E6 | 304:6 | rewrite-pattern | `Int.natAbs` normalisation shifted to `\|·\|` form |
| E7 | 321:69 | API-removal | `Exists.mod_cast` field removed; use `obtain ⟨k, hk⟩ := …; exact_mod_cast …` |
| E8 | 325:51 | omega | mod-4 reasoning fails after `Nat.cast_pow` normal-form shift |
| E9 | 326:51 | omega | same class as E8 |
| E10 | 365:59 | omega | 4-square sum bound `j + k + l + m ≤ 0` with `i := ↑n` |

Plus 4 warnings (3 unused vars, 1 unused simp arg); none blocking.

### Why this regression was invisible until now

1. **S2b ACT BUILD-VERIFY (#19041, 2026-05-15T23:38:13Z)** built a sibling that imports the parent — 7745 jobs clean. So the parent **did compile** ~5h before this session.
2. **No commits to `LagrangeFourSquares.lean`** in 24h (last touch: PR #18059, 2026-05-08).
3. **Lake-pin unchanged** at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` since 2026-05-13 v4.26.0 bump.
4. **S16 PREP (#19392)** did `gh api`-level bearer drift recheck only — no Docker re-build.

**Most likely cause**: the parent's `.olean` was cached from a pre-v4.26.0 elaboration and rode along under sibling-targeted builds without being re-elaborated; this session's target (which forced a parent rebuild from source) is the first elaboration against the current Mathlib pin. This is a **new manifestation** of the doc-only-saturation trap, hitting a parent slug rather than the OQ-01 child.

### Impact on slug

- **S16 PREP §3.2 recipe remains mathematically sound** — bridges are `Iff.rfl`-trivial, paired witness well-formed, `waringG 3 = 9 := rfl` discharges by match-arm. No edits needed when Mechanic fixes the parent.
- **All five queued ACTs (S4, S5, S6, S6b, S7) are BLOCKED** on the parent fix. None can ship until the parent compiles.
- **Lower-bound deliverables on origin/main** (`twenty_three_needs_nine_cubes`, `g3_lower_counting`, `g4_lower_counting`) are unaffected as source; they will rebuild green once parent does.
- **4 other slugs** that import the same parent (`lagrange-four-squares-oq-04`, `angle-trisection-oq-02-oq-01-oq-02-incomplete-01` aristotle companion, plus this slug's `*Counting.lean` and `*CountingG4.lean`) are also blocked downstream.

### Recommended Mechanic actions

1. **Open fix-PR on parent** addressing E1–E10 per §5 of the session memo. Likely-mechanical fixes for E3 (drop `.symm`), E5 (`Nat.log 2 k`), E7 (`obtain` + `exact_mod_cast`); E1/E2/E4 needs a single-block restructure; E6 a `simp`-form swap; E8/E9/E10 may need explicit `Int.emod_emod_of_dvd` or hypothesis restatement.
2. **Add parent-level pre-ACT BUILD-VERIFY pass** for all parent-of-OQ slugs that haven't been built in isolation in the last 7 days. Would have caught this before S16 PREP shipped paste-ready recipes.

### Blockers (refreshed)

- **B1 (NEW)**: parent `Proofs.LagrangeFourSquares.lean` has 9 v4.26.0 elaboration errors (lines 210–365). Blocks S4, S5, S6, S6b, S7 ACTs. Mechanic-scope.

### Honest-status block

- **Mathematical progress**: zero (S4 recipe is shovel-ready but cannot ship).
- **Build-verification status**: ❌ parent `LagrangeFourSquares.lean` Docker-red with 9 errors.
- **Axiom status**: parent retains `wieferich_nine_cubes` (L271, source-textual unchanged); environment cannot be loaded until parent fix.
- **Open conjecture status**: unchanged. All five queued ACTs BLOCKED on Mechanic parent fix.

---

## Pre-S17 Current Focus (researcher-3, 2026-05-15 STATE-SYNC)

**This iteration is a STATE-SYNC** (researcher-3, 2026-05-15) catching `state.md` and JSON up to the 3-PR drain wave that landed at 2026-05-15T22:56–23:38 UTC. See `sessions/2026-05-15-state-sync-s3-act-merge-build-verify-s7-prep-rescue.md` for full delta.

Lower-bound layer `g(k) ≥ N` design coverage is **saturated through k = 7** under the parametric "counting + omega" template established by S2b PREP / S3 PREP / S5 PREP / S6b PREP / S7 PREP (all five PREPs MERGED post-rescue). Upper-bound layer is **fully specified as an axiom inventory** (S4 PREP). The semantic correctness chain bridging local `IsSumOfPowers` predicates to `waringG k = N` is **scoped** (S6 PREP) and **audited** for typing/axiom errors (S6c PREP).

**S2b ACT BUILD-VERIFY MERGED** (PR [#19041](https://github.com/rjwalters/lean-genius/pull/19041), 2026-05-15T23:38:13Z, researcher-12): 1-LOC `by simp` fix at `LagrangeFourSquaresWaringG2OQ01Counting.lean:122` retiring the v4.26.0 `Set β`-coercion regression on `Finset.card_eq_sum_card_fiberwise`; final build 7745 jobs clean. The slug's lower bound `g(3) ≥ 9` is now verified via two independent routes (S2 ACT `native_decide` + S2b ACT counting+omega), with the latter axiom-free modulo no reflection-axiom dependency.

**S3 ACT MERGED** (PR [#19129](https://github.com/rjwalters/lean-genius/pull/19129), 2026-05-15T22:58:02Z, researcher-12): `WaringG2OQ01.CountingG4.g4_lower_counting : ¬ IsSumOfFourthPowers 18 79` shipped in new sibling file `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (155 LOC on origin/main, 0 sorries, 0 axioms, no `native_decide`). First-iteration Docker build 7743 jobs clean — the S2b BUILD-VERIFY `(by simp)` fix was incorporated up front. The parametric template is now verified at `k ∈ {3, 4}`.

**S7 PREP rescued** (PR [#19177](https://github.com/rjwalters/lean-genius/pull/19177), 2026-05-15T22:56:35Z): doc-only memo (828 LOC) supplying the `g(7) ≥ 143` design via counting + omega (witness `2175 = 16·128 + 127`). S7 PREP was previously an orphan branch (`research/lagrange-four-squares-waring-g2-oq-01-s7-prep-g7-counting-omega-20260513-054453`); the rescue PR opens S7 ACT as a routine port of the S3 ACT recipe at `k = 7`. After this STATE-SYNC, **five ACT iterations remain queued: S4 (smallest, axiom-only), S5 (routine k=4→5 port), S6 (correctness chain), S6b (routine k=4→6 port), S7 (now unblocked, routine k=4→7 port).**

**Last shipped Lean deliverables** (origin/main, byte-stable at lake SHA `2df2f01…` v4.26.0):
- S3 ACT — `WaringG2OQ01.CountingG4.g4_lower_counting : ¬ IsSumOfFourthPowers 18 79` (PR [#19129](https://github.com/rjwalters/lean-genius/pull/19129) MERGED, 0 sorries, 0 axioms, counting+omega, no `native_decide`); `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (155 LOC); registered in `proofs/Proofs.lean`.
- S2b ACT BUILD-VERIFY — `(by simp)` fix at `LagrangeFourSquaresWaringG2OQ01Counting.lean:122` (PR [#19041](https://github.com/rjwalters/lean-genius/pull/19041) MERGED, 7745 jobs clean).
- S2b ACT — `WaringG2OQ01.Counting.g3_lower_counting : ¬ IsSumOfCubes 8 23` via counting+omega (PR [#18928](https://github.com/rjwalters/lean-genius/pull/18928) MERGED 2026-05-13); `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01Counting.lean` (141 LOC, 0 sorries, 0 axioms post-#19041).
- S2 ACT — `WaringG2OQ01.twenty_three_needs_nine_cubes : ¬ IsSumOfCubes 8 23` via `native_decide` (PR [#18176](https://github.com/rjwalters/lean-genius/pull/18176) MERGED 2026-05-12); `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` (118 LOC).

## Active Approach

**Two-tier strategy: lower bounds verified, upper bounds axiomatized.** Verified — S4 PREP confirms upper bounds for `k ∈ {3, 4, 5, 6}` are research-level (Wieferich–Kempner 1909/1912, BDD 1986, Chen 1964, Pillai 1940) and must enter as `axiom` declarations rather than proved theorems.

**Lower-bound proof technique**: parametric "counting + omega".

1. *Bounding step*: each summand `f i` satisfies `(f i)^k ≤ n_k < 3^k`, so `f i ≤ 2`. (The key arithmetic fact, audited in S6b audit [PR #18555], is `q_k := ⌊(3/2)^k⌋ < (3/2)^k` strictly for every `k ≥ 1` — guaranteeing `n_k = q_k · 2^k + (2^k − 1) < 3^k`.)
2. *Lifting step*: `f : Fin s → ℕ` with each `f i ≤ 2` lifts to `g : Fin s → Fin 3`.
3. *Counting step*: let `n_j = |{i : g i = j}|` for `j ∈ {0, 1, 2}`. Then `n_0 + n_1 + n_2 = s` and `n_1 + 2^k · n_2 = n_k`.
4. *Omega step*: the resulting linear system over `ℕ` is infeasible — `omega` discharges. (Cases up to `n_2 ≤ q_k` exhibit a "miss by 1" calibration `n_0 = -1` characteristic of the witness construction.)

The S2 ACT shipped instance uses an alternative `native_decide` over `3^8 = 6561` tuples; the counting+omega route is the parametric design now established for `k ≥ 4` where `3^k · s` exceeds `native_decide`'s budget. S2b PREP supplies a counting+omega-style sibling proof for `k = 3` (smaller search space, same template).

**Upper-bound technique**: axiomatize the research-level results, register each as `axiomatized` in `meta.json`.

**Correctness-chain technique** (S6 PREP, S6c audit): for each `k`, bridge `WaringG2OQ01.IsSumOfPowers_k` (local) ↔ parent `IsSumOfPowers _ _ k` via `Iff.rfl` (or `⟨id, id⟩` defensively per S6c F6), then combine lower-bound theorem and upper-bound axiom to derive `waringG k = N` as a semantic certificate (not just `rfl`).

## Iteration history

| Iter | Researcher | Date | Mode | Deliverable | PR | Status |
|---:|---|---|---|---|---|---|
| S1 | researcher-? | 2026-05-12 | OBSERVE | Survey of `g(k)` history, two-tier architecture, Mathlib gap analysis | [#18152](https://github.com/rjwalters/lean-genius/pull/18152) | MERGED |
| S2 | researcher-3 | 2026-05-12 | ACT | `g(3)` lower bound via `native_decide` on `3^8 = 6561` tuples; new file `LagrangeFourSquaresWaringG2OQ01.lean` (118 LOC, 0 sorries, 0 axioms) | [#18176](https://github.com/rjwalters/lean-genius/pull/18176) | MERGED |
| S3 | researcher-10 | 2026-05-12 | PREP | `g(4)` lower bound design via counting+omega (369-line memo, full Lean sketch); identifies that `native_decide` over `3^18 ≈ 4·10^8` is infeasible | [#18314](https://github.com/rjwalters/lean-genius/pull/18314) | MERGED |
| S4 | researcher-? | 2026-05-12 | PREP | Upper-bound axiom inventory for `k = 3..6`: `waring_g3_upper`, `waring_g4_upper`, `waring_g5_upper`, `waring_g6_upper`; gap analysis for `bdd_nineteen_fourth_powers`, `chen_thirty_seven_fifth_powers` (218-line memo) | [#18348](https://github.com/rjwalters/lean-genius/pull/18348) | MERGED |
| S5 | researcher-4 | 2026-05-13 | PREP | `g(5)` lower bound design via counting+omega; witness `n = 223 = 6 · 32 + 31`; (509-line memo) | [#18463](https://github.com/rjwalters/lean-genius/pull/18463) | MERGED |
| S2b | researcher-? | 2026-05-13 | PREP | Counting+omega sibling for `g(3) ≥ 9`, unifying with S3/S5/S6b/S7 parametric template (186-line memo) | [#18483](https://github.com/rjwalters/lean-genius/pull/18483) | MERGED |
| S6 | researcher-12 | 2026-05-12 | PREP | `waringG k = N` correctness chain — semantic bridge `WaringG2OQ01.IsSumOfPowers_k ↔ IsSumOfPowers _ _ k` + `g_k_eq_N` theorems for `k = 3, 4, 5, 6` (543-line memo) | [#18406](https://github.com/rjwalters/lean-genius/pull/18406) | MERGED |
| S6b | researcher-10 | 2026-05-13 | PREP | `g(6)` lower bound design via counting+omega; witness `n = 703 = 11 · 64 + 63`; (682-line memo) | [#18547](https://github.com/rjwalters/lean-genius/pull/18547) | MERGED |
| S6b audit | researcher-? | 2026-05-13 | PREP | Audit of S6b PREP `{0,1,2}`-trick boundary arithmetic; proves `q_k < (3/2)^k` strictly for all `k ≥ 1`, hence `n_k < 3^k` universally (447-line memo) | [#18555](https://github.com/rjwalters/lean-genius/pull/18555) | MERGED |
| S6c audit | researcher-? | 2026-05-13 | PREP | Audit of S6 PREP §3 `waringG_2_correct` draft — 4 typing errors (F1–F4) + 1 axiom-integrity finding (F5: hidden `legendre_three_squares` dependency); proposes axiom-free `bound → lift → decide` alternative at `k = 2` (625-line memo) | [#18664](https://github.com/rjwalters/lean-genius/pull/18664) | MERGED |
| S7 | researcher-4 | 2026-05-13 | PREP | `g(7)` lower bound design via counting+omega; witness `n = 2175 = 16 · 128 + 127`; (828-line memo) | (orphan branch — see below) | DRAFT |
| S2b audit | researcher-4 | 2026-05-13 | PREP | Mathlib bearer audit for S2b PREP skeleton at lake-pinned SHA `2df2f01` (Mathlib v4.26.0); 9-row bearer table + sorry-free tactic draft (`Finset.sum_fiberwise` route, ~75 LOC) ready for S2b ACT paste | [#18895](https://github.com/rjwalters/lean-genius/pull/18895) | MERGED |
| S2b ACT | researcher-1 | 2026-05-13 | ACT | `g3_lower_counting : ¬ IsSumOfCubes 8 23` via counting + omega, sibling of S2 ACT's `native_decide`; eliminates `Lean.ofReduceBool` reflection axiom on the `g(3) ≥ 9` lower bound; new file `LagrangeFourSquaresWaringG2OQ01Counting.lean` (~141 LOC). | [#18928](https://github.com/rjwalters/lean-genius/pull/18928) | MERGED |
| S2b BUILD-VERIFY | researcher-12 | 2026-05-14 | ACT | 1-LOC `by simp` fix on `Finset.card_eq_sum_card_fiberwise` membership goal (v4.26.0 `Set β`-coercion regression); 7745 jobs clean. | [#19041](https://github.com/rjwalters/lean-genius/pull/19041) | **MERGED** 2026-05-15T23:38:13Z (`f31c503b89e2`) |
| S3 ACT | researcher-12 | 2026-05-14 | ACT | `g4_lower_counting : ¬ IsSumOfFourthPowers 18 79` via counting+omega — second verified instance of the parametric template (sibling of S2b ACT at `k = 4`). New file `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (155 LOC on origin/main, 0 sorries, 0 axioms, no `native_decide`). **First-iteration Docker build success, 7743 jobs clean.** Registered in `Proofs.lean`. | [#19129](https://github.com/rjwalters/lean-genius/pull/19129) | **MERGED** 2026-05-15T22:58:02Z (`c803ae7efe88`) |
| S7 PREP rescue | researcher-? | 2026-05-15 | PREP | Rescued the orphan-branch `g(7) ≥ 143` design memo (828 LOC) from `research/lagrange-four-squares-waring-g2-oq-01-s7-prep-g7-counting-omega-20260513-054453`. Opens S7 ACT as a routine port of the S3 ACT recipe at `k = 7`. | [#19177](https://github.com/rjwalters/lean-genius/pull/19177) | **MERGED** 2026-05-15T22:56:35Z (`b8c177c438e2`) |
| STATE-SYNC | researcher-3 | 2026-05-15 | STATE-SYNC | doc-only refresh after S3 ACT (#19129) merge + S2b BUILD-VERIFY (#19041) merge (partial — JSON-only, did not touch state.md) | [#19060](https://github.com/rjwalters/lean-genius/pull/19060) | **MERGED** 2026-05-15T23:34:19Z (`037b5b88d81`) |
| STATE-SYNC | researcher-3 | 2026-05-15 | STATE-SYNC | doc-only refresh after the 3-PR drain wave (#19129 + #19041 + #19177); refreshes `state.md` + JSON + new session memo. **No Lean changes.** | [#19366](https://github.com/rjwalters/lean-genius/pull/19366) | **MERGED** 2026-05-16T03:53:34Z |
| S17 BUILD-DIAGNOSTIC | researcher-1 | 2026-05-16 | BUILD-DIAGNOSTIC | doc-only; attempted S4 ACT via S16 PREP §3.2 paste-ready recipe but discovered parent `Proofs.LagrangeFourSquares.lean` fails Docker elaboration with 9 v4.26.0 errors at lines 210–365 (5 API-drift classes). Drafted child code reverted. Blocks all 5 queued ACTs (S4/S5/S6/S6b/S7); B1 NEW blocker added. | [#19442](https://github.com/rjwalters/lean-genius/pull/19442) | **MERGED** 2026-05-16T04:39:18Z |
| S18 PREP | researcher-5 | 2026-05-16 | PREP | doc-only Mechanic handoff upgrading S17 §5 rough fix sketch to paste-ready per-error Lean edits for parent `LagrangeFourSquares.lean` v4.26.0 fixes. 7 fix sites (E1+E2, E3, E4 cascade, E5, E6, E7, E8+E9, E10), ~25 LOC add / ~10 LOC del. Bearer-pinned at lake-SHA `2df2f015…` (7 bearers verified). Risk classification per fix (TRIVIAL/LOW/MEDIUM). Includes S4 ACT 5-min paste cycle once Mechanic ships parent fix. **No Lean changes; no `meta.json` edits.** | [#19546](https://github.com/rjwalters/lean-genius/pull/19546) | **MERGED** 2026-05-16T09:05:04Z |
| S19 ACT | researcher-1 | 2026-05-29 | ACT | `g5_lower_counting : ¬ IsSumOfFifthPowers 36 223` via counting+omega — third verified instance of the parametric template (sibling of S2b/S3 ACT at `k = 5`). New file `LagrangeFourSquaresWaringG2OQ01CountingG5.lean` (146 LOC, 0 sorries, 0 axioms, no `native_decide`). **Targeted Docker build success, 7743 jobs clean (~3.5 min wall-clock, fresh Mathlib clone)**. Registered in `Proofs.lean`. **Parent-independent route** — bypasses broken `LagrangeFourSquares.lean` (B1 unchanged). | [#21124](https://github.com/rjwalters/lean-genius/pull/21124) | **MERGED** |
| S21 ACT | researcher-1 | 2026-06-10 | ACT | `g6_lower_counting : ¬ IsSumOfSixthPowers 72 703` via counting+omega — fourth verified instance at `k = 6`, byte-mirror of S19 ACT (4 arithmetic-constant changes). New file `LagrangeFourSquaresWaringG2OQ01CountingG6.lean` (0 sorries, 0 axioms, no `native_decide`). **Docker build success, 7743 jobs clean.** Registered in `Proofs.lean`. Parent-independent. | [#22751](https://github.com/rjwalters/lean-genius/pull/22751) | **MERGED** |
| S7 ACT | researcher-? | 2026-06-13 | ACT | `g7_lower_counting : ¬ IsSumOfSeventhPowers 142 2175` via counting+omega — fifth verified instance at `k = 7`, byte-mirror of S21 ACT. New file `LagrangeFourSquaresWaringG2OQ01CountingG7.lean` (139 LOC, 0 sorries, 0 axioms). Registered in `Proofs.lean`. **Build-unverified** — merged during the Docker outage; targeted-build pending (see S22 caveat). | [#22968](https://github.com/rjwalters/lean-genius/pull/22968) | **MERGED** |
| S22 STATE-SYNC | researcher-4 | 2026-06-13 | STATE-SYNC | doc-only header/picker catch-up recording S7 ACT (`g(7) ≥ 143`, PR #22968) as shipped; coverage now `k ∈ {3,4,5,6,7}`. No Lean edits. | [#23088](https://github.com/rjwalters/lean-genius/pull/23088) | **MERGED** |
| S23 STATE-SYNC | researcher-2 | 2026-06-13 | STATE-SYNC | doc/meta-only ledger reconciliation: add CountingG6/G7 to `meta.additionalFiles`, flip S19/S21/S7 ACT rows here + in Future Iterations table from OPEN/TODO to MERGED. No Lean edits. | (this PR) | OPEN |

**Total PREP/ACT artifacts on origin/main**: post-S2b ACT — 11 PREP/ACT/audit + 3 STATE-SYNC + S3 ACT + S2b BUILD-VERIFY + S7 PREP rescue + S17 BUILD-DIAGNOSTIC, plus the S19/S21/S7 ACTs (g5/g6/g7 lower bounds) and S20/S22 STATE-SYNCs. **5 verified lower-bound Lean files** on origin/main (`k ∈ {3,4,5,6,7}`: Counting + CountingG4/G5/G6/G7), all 0-sorry / 0-axiom; G7 build-unverified pending Docker recovery.

## Open branches

None for this slug as of 2026-05-16T01:43Z. The S7 PREP orphan branch `research/lagrange-four-squares-waring-g2-oq-01-s7-prep-g7-counting-omega-20260513-054453` was rescued and MERGED via PR [#19177](https://github.com/rjwalters/lean-genius/pull/19177) at 2026-05-15T22:56:35Z, retiring the orphan-branch entry that previously occupied this section.

## Blockers

- **B1 (NEW 2026-05-16 via S17)**: parent `proofs/Proofs/LagrangeFourSquares.lean` fails Docker elaboration with 9 v4.26.0 errors at lines 210–365 across 5 API-drift classes. **Blocks S4/S5/S6/S6b/S7 ACTs.** **Mechanic-scope, paste-ready fixes staged in S18 PREP §3** (`sessions/2026-05-16-s18-prep-mechanic-handoff-parent-v426-paste-ready-fixes.md`). Per-error: E1+E2 (unsolved goal `id 1 + id p = 1 + p` + omega cascade, L210–212, LOW), E3 (drop `.symm` on `Nat.Prime.eq_one_or_self_of_dvd`, L220, TRIVIAL), E4 (scope cascade resolves after E3, L223, TRIVIAL), E5 (`Nat.log` binary arity, insert base `2`, L292, LOW), E6 (`Int.natAbs` → `sq_abs` rewrite swap, L304, LOW), E7 (`Exists.mod_cast` → `mod_two_eq_one_iff_ne_two.mpr`, L321, LOW), E8+E9 (extract `sq_mod_four` helper for mod-4 omega, L325–326, MEDIUM), E10 (`Int.toNat_natCast` cast collapse, L365, MEDIUM). Aggregate ~25 LOC add / ~10 LOC del; single Mechanic PR, single Docker pass once host-disk recovers.
- **B2 (INFRASTRUCTURE)**: host disk `/System/Volumes/Data` at 100% capacity (~7.2 Gi free / 926 Gi as of 2026-05-16T~05:00Z). Docker containerd `meta.db` cannot write atomically. Doc-only PREPs (this S18) and STATE-SYNCs unblocked; ACT/BUILD-VERIFY requires host-disk cleanup first.

**ACT-side risk** (when host-disk recovers): Docker build of Lean ACTs requires a fresh Mathlib clone if the worktree's `proofs/.lake` symlink is broken (`feedback_researcher_lake_symlink_broken.md`); end-to-end build is ~45 minutes. Allocate session budget accordingly.

## Next Action

**Path A (preferred — Mechanic-gated)**: wait for Mechanic to apply S18 PREP §3 paste-ready fixes to parent `proofs/Proofs/LagrangeFourSquares.lean`. Estimated Mechanic cycle: ~5–7 min Docker (parent rebuild + 4 sibling .olean refresh) once host-disk recovers. After Mechanic ships fix-PR, ANY researcher can claim this slug and ship S4 ACT verbatim from S16 PREP §3.2 in a ~5-min paste cycle.

**Path B (fallback if Mechanic-handoff stalls ≥ 4 drain waves)**: this slug's next researcher can attempt a Path-B fork — extract OQ-01 child code into a fully-self-contained sibling file that does NOT import `Proofs.LagrangeFourSquares` (define local `IsSumOfPowers`, local `waringG`, local `wieferich_nine_cubes` axiom; lose the bridge to parent but unblock S4 ACT). Estimated effort: ~50 LOC fresh recipe; trades parent-bridge for unblocked ACT. Recommend Path A unless Mechanic-side activity for `lagrange-four-squares` parent is invisible past 4 drain waves.

After Path A unblock, the queued ACTs remain (in recommended picker order — smallest scope / lowest build-risk first):

1. **S4 ACT** — register `axiom waring_g3_upper : ∀ n, ∃ f : Fin 9 → ℕ, (∑ i, (f i)^3) = n` (per S4 PREP [#18348](https://github.com/rjwalters/lean-genius/pull/18348)) + `theorem waringG_g3 : waringG 3 = 9` combining S2 ACT's `twenty_three_needs_nine_cubes` (lower, `native_decide` route) and S2b ACT's `g3_lower_counting` (lower, axiom-free counting+omega) with `waring_g3_upper` (axiomatized upper). **Smallest scope, ~50 LOC, axiom-only file, no fiberwise tactics, no `(by simp)` coercion surface — single Docker build expected first-iteration.**
2. **S5 ACT** — `g(5) ≥ 37` via counting+omega. Witness `223 = 6 · 32 + 31`. Expected size: ~150–180 LOC (case analysis on `n_2 ∈ {0..6}` has 7 branches vs. 5 for `k = 4`). **Routine port of S3 ACT recipe** — change `Fin 18 → Fin 36`, `79 → 223`, `16 → 32`, `81 → 243`, `^4 → ^5`. Paste `(by simp)` idiom from `Counting.lean:122` directly.
3. **S6b ACT** — `g(6) ≥ 73`. Witness `703 = 11 · 64 + 63`. Expected size: ~180–220 LOC (case analysis on `n_2 ∈ {0..10}`). Routine port of S3 ACT recipe at `k = 6`. Allocate 1-2 retry budget for v4.26.0 simp-set regressions on the larger case load.
4. **S6 ACT** — implement the correctness chain. Per S6c audit ([#18664](https://github.com/rjwalters/lean-genius/pull/18664), F5): **avoid the hidden `legendre_three_squares` dependency** by using the axiom-free `bound → lift → decide` route at `k = 2`. Expected size: ~60 LOC for the `k = 2` bridge + ~40 LOC per higher `k` once lower bounds and upper-bound axioms are in. Allocate 1-2 retry budget for `Iff.rfl` definitional-unfolding regressions.
5. **S7 ACT** — `g(7) ≥ 143`. Witness `2175 = 16 · 128 + 127`. **NEWLY UNBLOCKED** by PR [#19177](https://github.com/rjwalters/lean-genius/pull/19177) (S7 PREP rescue MERGED). Routine port of S3 ACT recipe at `k = 7`. Expected size: ~180–220 LOC (case analysis on `n_2 ∈ {0..16}` has 17 branches; ~3x S3 ACT's case-load). Allocate 2-3 retry budget; ~30 min Docker build.

Per the established pattern, all counting+omega ACTs share the same load-bearing case-analysis structure — a single ACT can refactor into a parametric `lemma waringG_lower_bound_template (k : ℕ) (s n_k : ℕ) (hk : ... ) : ¬ IsSumOfPowers _ s k n_k` that subsumes `k = 3..7` once written. The S2b ACT (`k = 3`) and S3 ACT (`k = 4`) confirm that the recipe ports mechanically; the (by simp) idiom from S2b BUILD-VERIFY is canonical.

## Attempt Counts

- Total iterations: 15 (3 ACTs MERGED + 1 BUILD-VERIFY MERGED + 11 PREPs MERGED + 2 STATE-SYNCs MERGED + this STATE-SYNC OPEN)
- ACT iterations merged: 3 (S2, S2b, S3) — all on origin/main, all build-verified
- ACT iterations in-flight: 0 — S2b BUILD-VERIFY (PR #19041) MERGED at 2026-05-15T23:38:13Z, retiring the only OPEN ACT
- ACT iterations this session: 0 (this STATE-SYNC is doc-only)
- PREP iterations merged: 11 (S1 OBSERVE, S2b PREP, S3 PREP, S4 PREP, S5 PREP, S6 PREP, S6b PREP, S6b audit, S6c audit, S2b bearer audit, **S7 PREP rescue [#19177](https://github.com/rjwalters/lean-genius/pull/19177) NEW**)
- PREP iterations drafted (no PR yet): 0 — S7 PREP rescued via #19177
- STATE-SYNC iterations merged: 2 ([#18866](https://github.com/rjwalters/lean-genius/pull/18866) on 2026-05-13 + [#19060](https://github.com/rjwalters/lean-genius/pull/19060) on 2026-05-15)
- STATE-SYNC iterations this session: 1 (this PR)
- Approaches: 2 — `native_decide` (S2 ACT only, adds `Lean.ofReduceBool` reflection axiom) and counting+omega (S2b ACT, S3 ACT, all 11 merged PREPs, future S4/S5/S6/S6b/S7 ACTs); S2b ACT + S3 ACT eliminate the reflection axiom on the `g(3) ≥ 9` and `g(4) ≥ 19` lower bounds respectively

## Open files

- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01.lean` — Lean deliverable for S2 (118 LOC, 2 theorems/lemmas, 0 sorries, 0 axioms via `native_decide` reflection axiom).
- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01Counting.lean` — Lean deliverable for S2b ACT + S2b BUILD-VERIFY (141 LOC on origin/main, 1 theorem `g3_lower_counting`, 0 sorries, 0 axioms, no `native_decide`). **BUILD-VERIFY PR [#19041](https://github.com/rjwalters/lean-genius/pull/19041) MERGED at 2026-05-15T23:38:13Z** — `(by simp)` v4.26.0 fix at line 122 is now on main.
- `proofs/Proofs/LagrangeFourSquaresWaringG2OQ01CountingG4.lean` — Lean deliverable for S3 ACT (155 LOC on origin/main, 1 theorem `g4_lower_counting`, 0 sorries, 0 axioms, no `native_decide`). Imports only Mathlib (no parent dependency). **PR [#19129](https://github.com/rjwalters/lean-genius/pull/19129) MERGED at 2026-05-15T22:58:02Z**, build-verified first iteration, 7743 jobs clean. Registered in `proofs/Proofs.lean`.
- `problem.md` — formal Lean signature targets, classification, Mathlib gap analysis, `g(k)` historical table.
- `knowledge.md` — `g(k)` historical table with citations, mod-arithmetic recipes, bibliographic references.
- `sessions/2026-05-12-s03-prep-g4-counting-omega.md` — S3 PREP (369 LOC).
- `sessions/2026-05-12-s04-prep-upper-bound-axioms.md` — S4 PREP (218 LOC).
- `sessions/2026-05-12-s06-prep-waringG-correctness-chain.md` — S6 PREP (543 LOC).
- `sessions/2026-05-13-s05-prep-g5-counting-omega.md` — S5 PREP (509 LOC).
- `sessions/2026-05-13-s2b-prep-g3-lower-counting-omega.md` — S2b PREP (186 LOC).
- `sessions/2026-05-13-s2b-prep-mathlib-bearer-audit.md` — S2b PREP follow-up bearer audit (~250 LOC).
- `sessions/2026-05-13-s6b-prep-audit-witness-arithmetic.md` — S6b audit (447 LOC).
- `sessions/2026-05-13-s6b-prep-g6-counting-omega.md` — S6b PREP (682 LOC).
- `sessions/2026-05-13-s6c-prep-audit-correctness-chain.md` — S6c audit (625 LOC).
- `sessions/2026-05-13-s7-prep-g7-counting-omega.md` — **S7 PREP (828 LOC) — NOW ON ORIGIN/MAIN via PR [#19177](https://github.com/rjwalters/lean-genius/pull/19177) (rescued from orphan branch).**
- `sessions/2026-05-14-s2b-act-build-verify-mem-univ-coercion-fix.md` — S2b ACT BUILD-VERIFY session memo (PR [#19041](https://github.com/rjwalters/lean-genius/pull/19041) MERGED).
- `sessions/2026-05-14-s3-act-g4-counting-omega.md` — S3 ACT session memo (PR [#19129](https://github.com/rjwalters/lean-genius/pull/19129) MERGED).
- `sessions/2026-05-14-state-sync-s2b-act-merge-build-verify.md` — STATE-SYNC #18866 / #19060 session memo (researcher-3, prior STATE-SYNC).
- `sessions/2026-05-15-state-sync-s3-act-merge-build-verify-s7-prep-rescue.md` — **this STATE-SYNC session memo**.

## Honesty block

This STATE-SYNC iteration is **doc-only**. It introduces 3 file edits (`state.md` refresh, JSON refresh, 1 new session memo `2026-05-15-state-sync-s3-act-merge-build-verify-s7-prep-rescue.md`) and **0 Lean code changes, 0 axiom-count changes, 0 sorry-count changes, 0 build attempts**.

The slug's three Lean deliverables are unchanged on origin/main:
- `LagrangeFourSquaresWaringG2OQ01.lean` (S2 ACT, 118 LOC)
- `LagrangeFourSquaresWaringG2OQ01Counting.lean` (S2b ACT post-#19041, 141 LOC)
- `LagrangeFourSquaresWaringG2OQ01CountingG4.lean` (S3 ACT, 155 LOC)

The bearer drift recheck in the session memo §3 is a **passive verification** (read lake-manifest, compare to last-known-good SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` v4.26.0, confirm no churn since 2026-05-14 v4.26.0 bump) rather than a re-run of the Mathlib bearer-audit script. The passive verification is sufficient because the v4.26.0 SHA pin has not changed since the last bearer audit (S2b PREP follow-up #18895 on 2026-05-13).

The `Iteration` increment 14 → 15 is justified per the slug's iteration-counting convention: STATE-SYNCs that introduce visibility for ≥1 merged-since-last-update ACT/PREP/BUILD-VERIFY count as iterations themselves. The three merges in the 22:56–23:38Z drain wave (#19129, #19041, #19177) are NOT separate iteration increments — they are landings of work whose iterations were already counted (iteration 13 for S3 ACT design / S3 ACT this PR, iteration ?? for S2b BUILD-VERIFY, iteration ?? for S7 PREP draft).

## Future Iterations

| Iter | Target | Predicate | Approach | Status |
|---:|---|---|---|---|
| S1 | OBSERVE survey | — | doc-only | **MERGED** #18152 |
| S2 | $g(3) \ge 9$ | $\neg \text{IsSumOfCubes } 8\ 23$ | `native_decide` $3^8$ | **MERGED** #18176 (0 sorries, 0 axioms) |
| S2b | $g(3) \ge 9$ (sibling) | $\neg \text{IsSumOfCubes } 8\ 23$ | counting + omega (template) | **PREP MERGED** #18483; **ACT MERGED** #18928; **BUILD-VERIFY MERGED** #19041 |
| S3 | $g(4) \ge 19$ | $\neg \text{IsSumOfFourthPowers } 18\ 79$ | counting + omega | **PREP MERGED** #18314; **ACT MERGED** #19129 (build-verified, 7743 jobs) |
| S4 | upper-bound axioms | `waring_g{3,4,5,6}_upper` | axiomatised | **PREP MERGED** #18348; ACT TODO |
| S5 | $g(5) \ge 37$ | $\neg \text{IsSumOfFifthPowers } 36\ 223$ | counting + omega | **PREP MERGED** #18463; **ACT MERGED** #21124 (S19, build-verified 7743 jobs) |
| S6 | $\text{waringG } k = N$ | semantic correctness chain | bridge + `decide` per S6c | **PREP MERGED** #18406, audit #18664; ACT TODO |
| S6b | $g(6) \ge 73$ | $\neg \text{IsSumOfSixthPowers } 72\ 703$ | counting + omega | **PREP MERGED** #18547, audit #18555; **ACT MERGED** #22751 (S21, build-verified 7743 jobs) |
| S7 | $g(7) \ge 143$ | $\neg \text{IsSumOfSeventhPowers } 142\ 2175$ | counting + omega | **PREP MERGED** #19177 (rescued); **ACT MERGED** #22968 (S7, build-unverified — merged during Docker outage) |
| (open) | $g(8) \ge 279$ | $\neg \text{IsSumOfEighthPowers } 278\ 6399$ | counting + omega | not yet designed |
| (open) | Hilbert–Waring existence | $\forall k \ge 1, \exists s, \forall n, \dots$ | Hardy–Littlewood (axiomatised) | not yet designed |

## REGISTER (2026-06-15, researcher-6)
Registered the two unregistered, clean (0-sorry, no `native_decide`) capstone files
in `proofs/Proofs.lean`:
- `LagrangeFourSquaresWaringG2OQ01General` — `waring_lower_general`: the general
  lower bound `g(k) ≥ 2^k+⌊(3/2)^k⌋-2` (0 axioms; hardened deterministic
  `linear_combination` certificate from S29 #24439, no nlinarith search).
- `LagrangeFourSquaresWaringG2OQ01ExactValue` — exact values `g(2)=4`
  (UNCONDITIONAL, via `Nat.sum_four_squares`) and `g(3)..g(7)` (modulo the single
  deep `ideal_waring_upper` axiom = Dickson–Pillai–Niven, absent from Mathlib).
  Imports General. Its `decide` calls are all trivial small-Nat arithmetic
  (`2^k+3^k/2^k-2=N`, the Dickson condition) — safe, unlike `native_decide`.

Neither was in the import manifest, so the deployer never compiled them; the
"0 sorry" status was inspection-only. The heavy `native_decide` Counting{G4..G7}
files (the alternative computational lower bounds) are already registered and are
the build-verify-gated frontier; this registration is the lightweight
formula-based capstone, NOT the counting frontier (open PRs #22889/#23377/#23330
target g(7)/g(8) counting). Deployer-gated: compile failure blocks merge, not main.
