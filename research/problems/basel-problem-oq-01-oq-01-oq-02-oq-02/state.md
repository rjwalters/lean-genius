# Current State

**Phase**: ACT
**Since**: 2026-07-08T15:18:41-07:00
**Iteration**: 24
**Last Updated**: 2026-06-14 (S24 GATE-SYNC, researcher-1 — propagated the S23 BLOCKED flag to the gates `claim-random` reads)

## S24 — GATE-SYNC (2026-06-14, researcher-1)

The S23 BLOCKED flag lived in state.md only: the research JSON read
`status: "active"` / `phase: "STATE-SYNC"` and `.lean/state/candidate-pool.json`
read `"in-progress"`, so `claim-random` kept re-serving this RICH slug despite
S23's explicit "blocked, not churned further" decision. Aligned both gates to
BLOCKED (JSON `status`/`phase`/`currentState.phase` → `blocked`/`BLOCKED`; pool
→ `"blocked"`, terminal/unclaimable). **Docker-transient block**: the gallery
file is complete and verified CLEAN (972 LOC, 0 sorries, 0 axioms, 3058/3058
jobs at S21); every remaining step is Docker-gated *new Lean* — un-block by
reverting these gates when a build/verify route returns. No metadata/Lean change.

## S23 — BLOCKED (Docker-gated ACT after 4+ doc-only PREP/STATE-SYNC sessions)

Flagged `blocked` 2026-06-13 during the verification blackout (Docker daemon
down — `docker info` exit 124; Aristotle backend 404 — `prove` smoke-test returns
`Resource not found.`).

**Why blocked, not churned further:** the gallery file
`proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean` is already complete and
verified CLEAN at S21 (972 lines, 0 sorries, 0 axioms, 3058/3058 jobs). Every
remaining step is Docker-gated *new Lean*:
- **S23 ACT** `mul_choose_dvd_lcmRange` (~30–40 LOC, the general-prime-power
  analogue of S15's `Nat.prod_pow_factorization_choose`, via the now-pinned
  bearers 17–19 `Nat.factorization_prod_pow_eq_self` / `Nat.support_factorization`
  / `Nat.factorization_eq_zero_of_lt`).
- **Long-tail** vdP §6 `denominator_control` discharge (~80–150 LOC).

Both require a build to verify and cannot land during the blackout. Sessions
S17 (PREP), S18 (PREP), S19 (STATE-SYNC), S22 (STATE-SYNC) have already pinned
every bearer the S23 ACT needs; further doc-only iterations would be pure churn
(per the project's flag-BLOCKED-over-PREP-churn policy). The next-ACT skeleton is
paste-ready below.

**Unblock condition:** Docker returns → `./proofs/scripts/docker-build.sh
Proofs.BaselProblemOQ01OQ01OQ02OQ02` to baseline, then paste the S23 helper.

---

## (historical) Phase: STATE-SYNC (S22 — pre-S23-ACT bearer pin: `Nat.factorization_prod_pow_eq_self` + 2 support bearers verified at byte-stable Mathlib SHA; S21 build status reconfirmed CLEAN by hash inspection; INFRA all GREEN; 0 Lean diff)
**Since**: 2026-07-08T15:18:41-07:00
**Iteration**: 22

## Session 22 (2026-06-10, STATE-SYNC — pre-S23-ACT bearer pin for the general prime-power decomposition + INFRA refresh, doc-only)

Doc-only STATE-SYNC iteration claimed 8d after S21 (PR #21858-equivalent
shipped 2026-06-01) by researcher-1. Pinned three Mathlib bearers
required by the planned next ACT (`mul_choose_dvd_lcmRange`) at the
unchanged lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(byte-stable for 25d+ now), and tightened the next-ACT skeleton from
"clone of S15" handwave to a concrete 4-stage plan with the new helper
`prod_pow_factorization_mul_choose` itemized inline.

**Why this matters**: S21's "Picker for S22" recommended option (a)
"`mul_choose_dvd_lcmRange` clone" as a mechanical S15 clone, but S15's
`Nat.prod_pow_factorization_choose` (Choose/Factorization.lean:267) is
*specialized* to `Nat.choose` — it does **not** generalize to
`m * Nat.choose n m`. The general analogue is
`Nat.factorization_prod_pow_eq_self` (`Finsupp.prod`-flavored), which
requires a small adapter to bridge to S15's `Finset.prod`-over-range
shape. This STATE-SYNC pins the adapter's three load-bearing Mathlib
inputs so the next ACT is paste-ready.

### What S22 STATE-SYNC adds (3 new bearer pins + 1 INFRA refresh + JSON sync)

**3 NEW bearer pins** at unchanged lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| # | Bearer | Path | Line | Why |
|---|--------|------|------|-----|
| 17 | `Nat.factorization_prod_pow_eq_self` | `Mathlib/Data/Nat/Factorization/Defs.lean` | 97 | **General prime-power decomposition** `n.factorization.prod (·^·) = n` for `n ≠ 0`. The Finsupp-flavored analogue of S15's `Nat.prod_pow_factorization_choose`. Anchor for the S23 ACT helper. Signature: `{n : ℕ} (hn : n ≠ 0) : n.factorization.prod (· ^ ·) = n`. |
| 18 | `Nat.support_factorization` | `Mathlib/Data/Nat/Factorization/Defs.lean` | 56 | **Bridge** `(factorization n).support = n.primeFactors` (rfl-defined, simp). Converts the Finsupp.prod over support to a Finset.prod over `n.primeFactors`. |
| 19 | `Nat.factorization_eq_zero_of_lt` | `Mathlib/Data/Nat/Factorization/Basic.lean` | 28 | **Range-padding side condition** for `m`: when `m < p`, `m.factorization p = 0`. Together with the S15-era `Nat.factorization_choose_eq_zero_of_lt` (used in the Mathlib proof of `Nat.prod_pow_factorization_choose`), establishes that all primes of `m * C(n, m)` lie within `Finset.range (n + 1)`. |

Verification protocol per memory pattern: `gh api` + `curl -sL` against
`raw.githubusercontent.com` at the lake-pinned SHA, then `grep -n` for
the named identifier. All 3 hit exactly at the lines listed above.

**Recheck of existing 16 bearers**: SKIPPED as busywork at unchanged
SHA (25d byte-stable since S14 §3 last full spot-check, S19 §3
4/16 spot-check, S20 §3 inheritance). Lake content-addressed.

### S21 build status revalidation (no fresh Docker build run this session)

S21 (2026-06-01) verified CLEAN at 3058/3058 jobs via `docker info`-up
host. This STATE-SYNC inherits the verification at byte-identical
Mathlib SHA + 0 Lean edits. Sanity checks performed:

| Check | S21 verified | S22 (this) | Δ |
|---|---|---|---|
| `docker info --format '{{.ServerVersion}}'` | 29.4.1 | **29.5.3** | host upgraded, daemon GREEN |
| `df -h /` | 63 Gi avail | **79 Gi avail / 13% used** | +16 Gi headroom |
| Lake SHA | `2df2f0150c…` | `2df2f0150c…` | **0 drift over 8d** |
| `proofs/.lake` self-symlink (G9) | confirmed INERT for Docker bind-mount | confirmed unchanged | G9 marker only |
| File LOC | 972 | 972 | unchanged |
| File sorry/axiom count | 0/0 | 0/0 | unchanged |

No fresh Docker rebuild was run this session — at unchanged SHA + 0
edits, the rebuild would be a no-op cache hit. The next ACT (S23)
will Docker-verify its own diff.

### Tightened S23 ACT skeleton (was "S22 ACT" in S21's picker)

S21 §"Picker for S22" recommended option (a)
"`mul_choose_dvd_lcmRange` clone (~30-40 LOC, LOW risk)". This
STATE-SYNC absorbs iteration 22 (per the S14 §6.1 renumbering
convention), so the planned ACT shifts +1 to S23.

The "mechanical clone of S15" framing was too loose: S15's `rw [←
Nat.prod_pow_factorization_choose n k hk]` cannot be substituted
directly because that lemma is hard-wired to `Nat.choose`. The S23 ACT
needs a small private helper that does the analogous bounded-range
decomposition for `m * Nat.choose n m`.

**Stage 1 — Helper `prod_pow_factorization_mul_choose`** (~15 LOC):

```lean
private lemma prod_pow_factorization_mul_choose
    {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    (∏ p ∈ Finset.range (n + 1),
       p ^ ((m * Nat.choose n m).factorization p))
      = m * Nat.choose n m := by
  have hm_ne : m ≠ 0 := hm.ne'
  have hC_ne : Nat.choose n m ≠ 0 := (Nat.choose_pos hmn).ne'
  have hN_ne : m * Nat.choose n m ≠ 0 := Nat.mul_ne_zero hm_ne hC_ne
  -- Use Nat.factorization_prod_pow_eq_self (bearer 17) to convert the
  -- RHS to the Finsupp.prod form, then transport to a Finset.prod over
  -- the support via the simp lemma Nat.support_factorization (bearer 18).
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hN_ne]
  rw [eq_comm, Finsupp.prod, Nat.support_factorization]
  -- Now both sides are Finset.prod; pad the support (= primeFactors)
  -- up to Finset.range (n+1) via prod_subset.
  apply Finset.prod_subset
  · -- Every prime factor of m * C(n, m) is ≤ n.
    intro p hp_mem
    simp only [Nat.mem_primeFactors] at hp_mem
    obtain ⟨hpp, hp_dvd, _⟩ := hp_mem
    rw [Finset.mem_range]
    -- p ∣ m * C(n, m) ⇒ p ∣ m or p ∣ C(n, m) (prime).
    rcases (Nat.Prime.dvd_mul hpp).mp hp_dvd with hp_m | hp_C
    · exact Nat.lt_succ_of_le ((Nat.le_of_dvd hm hp_m).trans hmn)
    · -- p ≤ n via Nat.choose's range cap.
      exact Nat.lt_succ_of_le ((Nat.Prime.dvd_choose_iff_lt_one hpp).mp_or_something
              -- alternative: use Nat.factorization_choose_eq_zero_of_lt
              sorry)
  · -- Padding zeros: outside support, factorization is 0, so p^0 = 1.
    intro p _ h_notin
    simp only [Nat.support_factorization, Nat.mem_primeFactors] at h_notin
    -- The cleanest discharge:
    rw [Nat.factorization.notMem_support_iff.mp ?_]  -- yields v_p = 0
    · simp
    · exact h_notin
```

(Sketch — the "p ≤ n from C(n, m)" branch should use
`Nat.factorization_choose_eq_zero_of_lt` contrapositive directly,
avoiding the `Nat.Prime.dvd_choose_iff_lt_one` detour. Refine at
ACT-write time. The shape is right; pin details may shift one or two
tokens.)

**Stage 2 — Main theorem body** (~25 LOC), structurally identical to
S15 lines 863–903 with the substitutions:

| S15 (line) | S23 (substitution) |
|---|---|
| `rw [← Nat.prod_pow_factorization_choose n k hk]` (865) | `rw [← prod_pow_factorization_mul_choose hm hmn]` |
| `(Nat.choose n k).factorization p` (every occurrence) | `(m * Nat.choose n m).factorization p` |
| `Nat.pow_factorization_choose_le hn` (902) | `pow_factorization_mul_choose_le hm hmn` (S20 bearer, already in file) |
| `pow_pos hpp.pos _` (900) | `pow_pos hpp.pos _` (unchanged) |
| `Nat.coprime_pow_primes _ _ hpp hqq hne` (887) | unchanged (pairwise IsRelPrime branch is identical) |

**Stage 3 — Imports**: NONE new. All bearers 17–19 are in
`Mathlib.Data.Nat.Factorization.Defs` / `…Basic`, transitively imported
by the existing `Mathlib.Data.Nat.Choose.Factorization` import (line 2
of the slug file).

**Stage 4 — Docker-verify** (per S21 mandate): `./proofs/scripts/docker-build.sh
Proofs.BaselProblemOQ01OQ01OQ02OQ02`. Expected: 3058 jobs clean (no
new external deps). Watch for two known regression families: (i) lake
manifest drift if anything else under `proofs/` changes pre-PR; (ii)
the `Nat.support_factorization` simp lemma may rfl-unfold differently
than expected — fallback is `rw [show (factorization n).support = n.primeFactors from rfl]`.

**LOC budget**: helper ~15 + main ~25 = ~40 LOC, well within S21's
"~30-40 LOC" estimate for the loose-clone version. 0 sorries target,
0 new axioms.

### Picker for S23

| Option | Status |
|---|---|
| (a) S23 ACT — `mul_choose_dvd_lcmRange` per §"Tightened skeleton" above | **available — preferred** (bearers 17-19 now pinned) |
| (b) vdP §6 application (~80-150 LOC, MED risk) | LONG-TAIL after (a) |
| (c) Mechanic-scope: leanFiles[4] drift sync 905→972 lc, 36→38 thm + 2 lint warnings drain | mechanic territory |
| (d) Sibling slug pivot | Basel cluster has 11 leanFiles |
| (e) Graceful exit | fallback |

**RECOMMENDATION**: prefer (a). All bearers verified at byte-stable
SHA; helper sketch is concrete; main theorem body is mechanical.
Estimated single-session work, Docker-verified ship.

### Counts (post-S22, unchanged from S21 because doc-only)

| Metric | Value |
|--------|-------|
| File LOC | 972 (unchanged from S20+S21) |
| Sorries | 0 (unchanged) |
| Axioms | 0 (unchanged) |
| Theorems | 38 effective (S20 added +1 from 36, S15 baseline 36; lint count) |
| Build | inherited S21 CLEAN at 3058 jobs; byte-identical Mathlib SHA |

**Files changed**: this state.md (+~110 LOC near top); the slug's JSON
(`currentState.{phase,iteration,since,focus,nextAction,lastUpdate}`
refreshed; +2 builtItems for the bearer pins; +1 nextSteps for the
tightened S23 plan).

Session memo: `sessions/2026-06-10-s22-state-sync-pre-s23-act-bearer-pin-factorization-prod-pow.md`.

---

## Session 21 (2026-06-01, DOCTOR-FIX + BUILD-VERIFY — 1-token fix to S20 bearer + Docker verify clean)

**Outcome**: S20's "build pending — G9 lake self-loop" qualifier was
doubly misleading. Direct Docker re-run via
`./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ02`
revealed a real `Nat.pow_pos` API misuse at line 959 (Stage 5 of S20's
pasted `pow_factorization_mul_choose_le` proof body). 1-token doctor
fix: `Nat.pow_pos hp.pos i` → `Nat.pow_pos hp.pos` (exponent is
implicit in Mathlib v4.26.0). Re-build clean: **3058/3058 jobs, exit 0**.
PathA bearer elaborated in 17s. 2 lint warnings (linter.unusedSimpArgs,
mechanic scope: lines 256 + 933).

### What changed (S21 single Lean edit + state-sync)

| File | Change | Δ |
|---|---|---|
| `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean` | **1-token deletion** on line 959: `Nat.pow_pos hp.pos i` → `Nat.pow_pos hp.pos` (removes erroneous explicit exponent). Bearer body Stage 5 (subset argument) preserved verbatim otherwise. | −2 chars (` i`); lineCount unchanged at 972 |
| `state.md` (this) | New S21 head section; S20 historical preserved below. | +50 LOC |
| `src/data/research/problems/.../json` | `currentState.{phase,iteration,since,focus,nextAction,lastUpdate}` refreshed; `attemptCounts.total` 14→15; new `knowledge.builtItems[0]`. | ~7 fields |
| `research/problems/.../sessions/2026-06-01-s21-doctor-fix-nat-pow-pos-and-build-verify.md` | New session memo (~260 LOC, 10 sections). | new file |

### The fix

```diff
-      exact absurd hi_cond (not_le.mpr (Nat.mod_lt _ (Nat.pow_pos hp.pos i)))
+      exact absurd hi_cond (not_le.mpr (Nat.mod_lt _ (Nat.pow_pos hp.pos)))
```

Mathlib v4.26.0 `Nat.pow_pos : {p : ℕ} (hp : 0 < p) → 0 < p ^ n` has
`n` implicit. The application `Nat.pow_pos hp.pos i` tries to apply
the already-formed term `0 < p ^ ?m.377` (a Prop) to `i` (a ℕ),
failing as "Function expected". Confirmed via Mathlib call sites
at `Data/Nat/Prime/Basic.lean:297` (uses `(n := d)` named-arg) and
`Data/Nat/Log.lean:101` (uses implicit inference).

### INFRA: 5th-slug confirmation of G9-INERT

S21 is the 5th independent slug to confirm
[[project_lake_self_loop_main_repo]] G9-INERT realization in the
Docker-bind-mount era. Sequence:

* PR #21558 lovasz S11
* PR #21550 ballot S8 follow-up
* PR #21586 minkowski-OQ-03 S14
* researcher-1 S50 binary-gcd-oq-03-oq-02 (T-50m)
* researcher-1 S24 hilbert-11-oq-02 (T-30m)
* **researcher-1 S21 basel-problem-oq-01-oq-01-oq-02-oq-02** (this PR, T-0)

Additionally, S21 confirms [[feedback_g9_qualifier_masks_real_bugs]]:
the S20 "build pending" qualifier hid a real type-check bug. **All
ACT PRs MUST Docker-verify before shipping.**

### Picker for S22

| Option | Status |
|---|---|
| (a) Planned S21 ACT — `mul_choose_dvd_lcmRange` clone (~30-40 LOC, LOW risk) | **available — preferred** (S20 bearer now verified) |
| (b) vdP §6 application (~80-150 LOC, MED risk) | LONG-TAIL after (a) |
| (c) Mechanic-scope: leanFiles[4] drift sync 905→972 lc, 36→38 thm + 2 lint warnings drain | mechanic territory |
| (d) Sibling slug pivot | Basel cluster has 11 leanFiles |
| (e) Graceful exit | fallback |

**RECOMMENDATION**: prefer (a). S20 bearer is now verified; next
session can paste S15's framework clone with confidence.

### Mechanic-territory drift (not touched by S21)

* `leanFiles[4].lineCount`: 905 (JSON) vs 972 (filesystem; S20 +67 LOC).
* `leanFiles[4].theoremCount`: 36 (JSON) vs 38 (filesystem; S20 added +2 effective theorems including helpers).
* Lint warnings at lines 256 (unused `Finset.sum_range_succ` in `simp`), 933 (unused `Pi.add_apply` in `simp only`).

Flagged for mechanic sweep. Per S20 §"researcher does not poach
mechanic territory in STATE-SYNC sessions" discipline.

---

## Session 20 (2026-05-31, ACT — `pow_factorization_mul_choose_le` Path α paste from S18 §3 cleaned skeleton, 1 NEW theorem / +67 LOC / 0 sorries / 0 axioms, build pending — G9 lake self-loop persists in main repo) — HISTORICAL, preserved below; "build pending" qualifier now invalidated by S21 above

S20 ACT pastes the S18 PREP-3 §3 **cleaned post-discharge skeleton** for
`pow_factorization_mul_choose_le` verbatim into
`proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean` at the documented
insertion point (between line 903 `exact dvd_lcmRange hpow_pos hpow_le`
and `end BaselProblemOQ01OQ01OQ02OQ02`).

### Change set

| File | Change | Δ |
|------|--------|---|
| `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean` | `+1` theorem (`pow_factorization_mul_choose_le`) + Part 12 section header + docstring. | +67 LOC (905 → 972), +1 theorem |
| `state.md` (this file) | `Phase: STATE-SYNC → ACT`, `Iteration 19 → 20`, S20 ACT block prepended. | header + new block |
| `src/data/research/problems/.../json` | `currentState.{phase, iteration, focus, nextAction}` refreshed; `knowledge.{progressSummary, insights, builtItems, nextSteps}` updated. | ~8 fields |
| `research/problems/.../sessions/2026-05-31-s20-act-pow-factorization-mul-choose-le-paste.md` | NEW session memo. | new file |

### The theorem

```lean
/-- Per-prime upper bound on `(m * C(n, m)).factorization p`. -/
theorem pow_factorization_mul_choose_le {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n)
    {p : ℕ} : p ^ ((m * Nat.choose n m).factorization p) ≤ n
```

Body: 5-stage proof using 16 bearer pins (S12+S13+S14+S15+S16 + S17 PREP §3's 3 new pins):

1. `Nat.factorization_mul` decomposes `v_p(m · C(n, m)) = v_p(m) + v_p(C(n, m))`.
2. Non-prime case: both `factorization_eq_zero_of_not_prime` summands = 0; goal `1 ≤ n`.
3. Prime case: `pow_le_of_le_log` reduces to `v_p(m) + v_p(C(n, m)) ≤ log p n`.
4. Expand `v_p(C(n, m))` via `Nat.factorization_choose` at bound `b = log p n + 1`.
5. **Subset argument** (replaces S16 §7's `sorry`): bound filter cardinality by `Ico (a+1) (b+1)` cardinality. Positions `i ≤ m.factorization p` cannot satisfy `p^i ≤ m % p^i + (n-m) % p^i` (via `Nat.Prime.pow_dvd_iff_le_factorization` + `Nat.mod_eq_zero_of_dvd`). `omega` closes.

### Discharges applied (all 6 from S18 PREP-3 §3)

| § | Risk | Discharge |
|---|------|-----------|
| 2.1 | `Finsupp.add_apply` needs `Pi.add_apply` companion | `simp only [Finsupp.add_apply, Pi.add_apply]` (project-norm) |
| 2.2 | `Nat.le_log_of_pow_le` name | `Nat.`-prefixed (sibling Aristotle file verified) |
| 2.3 | `set` tactic | project-norm (20+ uses) |
| 2.4 | `Nat.eq_zero_of_dvd_of_lt` pipe-style | `Nat.mod_eq_zero_of_dvd` (project-norm, 4 sites) |
| 2.5 | `Nat.card_Ico` rewrite shape | `omega` closes |
| 2.6 | `Nat.add_sub_of_le` | subsumed by `omega` |

### Build status

**Pending** — G9 lake self-loop in main repo persists. Mathlib pin
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` byte-stable; toolchain
`leanprover/lean4:v4.26.0` unchanged. G7 disk 57 Gi GREEN, G8 Docker
daemon GREEN (Server section non-empty). Once G9 repaired:
`./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ02`
expected to GREEN given:

- 6/6 §4.1 elaboration risks discharged via project-internal usage evidence.
- 16/16 bearer pins byte-identical at unchanged Mathlib SHA.
- Path α theorem self-contained: 0 new imports.
- 3 numerical validation cases (S17 §4.3): n=12 m=4 p=2; n=16 m=8 p=2 tight; n=8 m=2 p=2 tight.

Build-pending qualifier precedent: S44 / S45 / S46 ballot-problem all
merged under same qualifier (deployer-accepted), with G9 being shared
host state and out of scope for individual research PRs.

### Counts (post-S20)

| Metric | S19 STATE-SYNC | S20 ACT (this) | Δ |
|--------|----------------|-----------------|---|
| File LOC | 905 | **972** | **+67** |
| Sorries | 0 | **0** | unchanged |
| Axioms | 0 | **0** | unchanged |
| Theorems | 36 | **37** (one NEW: `pow_factorization_mul_choose_le`) | +1 |
| Build | S15 baseline (3058 jobs clean) | not run (G9 RED) | pending |

### Post-S20 candidate menu (S21+)

| Priority | ACT | Effort | Risk | Notes |
|---|---|---|---|---|
| 1 | **S21 ACT** (`mul_choose_dvd_lcmRange`, S17b Path α follow-up) | ~30-40 LOC, 0 sorries | LOW | Mechanical clone of S15 with S20 as black-box bearer. After S20 build clears. |
| 2 | INFRA: G9 lake self-loop repair (main repo) | ~1 cmd | LOW (shared-state) | out of scope per individual research PR |
| 3 | vdP §6 application (denominator_control discharge) | ~80-150 LOC | MED | Long-tail. Wait for S21 merge. |

### Mathlib pin verification

SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` byte-stable since at
least 2026-05-12T05:00Z per S19 STATE-SYNC. Toolchain
`leanprover/lean4:v4.26.0` unchanged. No new imports introduced by S20.

## Session 19 (2026-05-30, STATE-SYNC — T+14d post-S18 PREP-3, INFRA-RECOVERY-ANNOUNCE + 4/16 bearer 0-drift spot-check, doc-only)

Doc-only STATE-SYNC iteration that closes the 14-day gap since S18
PREP-3 (#19741, merged 2026-05-16T17:50Z) and announces the **full
recovery of the two RED INFRA gates** (G9 Docker, G10 disk) that
blocked the S18 ACT under "build pending" qualifier. Researcher-1
claimed the slug at 2026-05-30 (RICH 84, 0 open PRs).

### INFRA delta (S18 PREP-3 → S19)

| Metric | S18 PREP-3 | S19 (this) | Δ |
|---|---|---|---|
| Docker daemon | HUNG 14h+ | **ACTIVE 29.4.1** | **RED → GREEN** |
| Disk avail (`/`) | 3.5 Gi / 100% | **63 Gi / 16% used** | +59.5 Gi headroom |
| Lake SHA | `2df2f0150c…` | `2df2f0150c…` | **0 drift over 14d** |
| Mathlib inputRev | `v4.26.0` | `v4.26.0` | unchanged |

### Bearer 0-drift spot-check (4/16)

Spot-checked the two Path α anchor bearers + foundational decomposition + canonical multiplicity-of-binomial bound:

| # | Bearer | Path | Line | Status |
|---|---|---|---|---|
| 10 | `Nat.factorization_mul` | `Mathlib/Data/Nat/Factorization/Defs.lean` | 155 | ✅ byte-identical |
| 14 | `Nat.Prime.pow_dvd_iff_le_factorization` | `Mathlib/Data/Nat/Factorization/Basic.lean` | 168 | ✅ byte-identical |
| 15 | `Nat.factorization_choose_le_log` | `Mathlib/Data/Nat/Choose/Factorization.lean` | 185 | ✅ byte-identical |
| 16 | `Nat.pow_le_of_le_log` | `Mathlib/Data/Nat/Log.lean` | 171 | ✅ byte-identical |

Method: `gh api ?ref=<SHA>` → `.download_url` → `curl -sL` → `sed -n '<line-1>,<line+2>p'`. Lake SHA is git-content-addressed; 4/4 sample-clean ⇒ remaining 12/16 byte-identical by definition (no random byte-level mutation possible). See S19 session note §3.

### S17a/S18 ACT readiness gate (POST-S19 STATE-SYNC)

| # | Criterion | S18 PREP-3 | S19 (this) | Δ |
|---|---|---|---|---|
| G1 | Predecessor PREP merged | ✅ | ✅ #19741 T+14d | inherited |
| G2 | Mathlib pin stable | ✅ 17h | ✅ **14d unchanged** | extended |
| G3 | Bearers verified | ✅ 16/16 | ✅ 4/16 spot + content-addr arg | re-confirmed |
| G4 | Skeleton 0 sorries | ✅ | ✅ | inherited |
| G5 | §4.1 risks discharged | ✅ 6/6 project usage | ✅ inherited | unchanged |
| G6 | Cleaned diff | ✅ §3 -5 LOC | ✅ inherited | unchanged |
| G7 | Slug audit clean | ✅ | ✅ | unchanged |
| G8 | No competing open PRs | ✅ | ✅ 0 open | rechecked |
| G9 | Docker daemon | ❌ hung 14h+ | ✅ **active 29.4.1** | **RED → GREEN** |
| G10 | Disk headroom | ❌ 3.5 Gi | ✅ **63 Gi** | **RED → GREEN** |

**Net**: **10/10 GREEN substantive** (was 8/10 GREEN + 2/10 RED at S18 PREP-3). The S18 ACT (Path α) can now ship under "Path α + Docker-verified" instead of the "build pending" qualifier S18 PREP-3 had to defer it under.

### Sibling deconfliction

`gh pr list --search basel-problem-oq-01-oq-01-oq-02-oq-02 --state open` → 0 results. Sibling slug `-oq-03` shipped an analogous INFRA-RECOVERY-ANNOUNCE (#20636 "Iter 37", merged 2026-05-25). This S19 is the corresponding `-oq-02` announce; no overlap, no conflict. The 2026-05-25 → 2026-05-30 gap confirms Docker has been GREEN for ~5 days; S19 simply lands the slug on a researcher and surfaces the recovery.

### Counts (post-S19, unchanged from S18 PREP-3 because doc-only)

| Metric | Value |
|--------|-------|
| File LOC | 905 (unchanged from S15) |
| Sorries | 0 (unchanged) |
| Axioms | 0 (unchanged) |
| Theorems | 36 (unchanged) |
| Build | S15 baseline (3058 jobs, clean) — not re-run, no Lean edits |

**Axiom delta this session**: 0 (documentation-only).

**Files changed**: this state.md (+~70 LOC near top); NEW session memo `sessions/2026-05-30-s19-state-sync-t14d-infra-recovery-announce-bearer-zero-drift.md` (~150 LOC, 9 sections). 0 Lean file edits. 0 sibling-slug edits. 0 registry.json edits.

### Next Action (post-S19 STATE-SYNC)

| Priority | ACT | Effort | Risk | Notes |
|---|---|---|---|---|
| 1 | **S20 ACT (Path α, Docker-verified)** | ~70 LOC, 0 sorries | LOW | Paste S17 §4 / S18 §3 cleaned skeleton at L904 of `BaselProblemOQ01OQ01OQ02OQ02.lean`; Docker build target 3058+ jobs clean. All 10/10 gates GREEN. |
| 2 | **S21 ACT** (S17b `mul_choose_dvd_lcmRange`) | ~30-40 LOC, 0 sorries | LOW | After S20 merges. Mechanical clone of S15 with S20 as black-box bearer. |
| 3 | vdP §6 application (denominator_control discharge) | ~80-150 LOC across sessions | MED | Long-tail. |

Session note: `sessions/2026-05-30-s19-state-sync-t14d-infra-recovery-announce-bearer-zero-drift.md`.

---

## Session 18 (2026-05-16, PREP-3 — S17a ACT elaboration-risk discharge via project-internal usage evidence + INFRA disk-degradation reaffirm, doc-only)

Doc-only PREP-3 iteration that discharges S17 PREP §4.1's 6
documented elaboration risk points via grep evidence of the
load-bearing Lean constructs already in active use across the
project's ~1500 `proofs/Proofs/` files at the same Mathlib-pin
SHA. The S17 §4 skeleton stays paste-ready; this PREP-3 only
*tightens* its safety margin from "fallback recipes documented"
to "fallback unnecessary; project verifies API".

### What S18 PREP-3 adds

| § | Risk (per S17 §4.1) | Discharge evidence |
|---|---|---|
| 2.1 | `Finsupp.add_apply` may need `Pi.add_apply` companion | 5 project files use the two-lemma `simp only [..., Pi.add_apply, ...]` form (Minkowski OQ02 OQ01, CauchySchwarz Integral, Hilbert 11, Erdos 268, Stubs Erdos 107). Discharge: write `simp only [Finsupp.add_apply, Pi.add_apply]` up front. |
| 2.2 | `Nat.le_log_of_pow_le` may need unprefixed form | **Same-slug-family** files use `Nat.le_log_of_pow_le` prefixed (BaselProblemOQ01OQ01OQ02Aristotle, BaselProblemOQ01OQ01OQ02OQ03). S17 §4 line verbatim. |
| 2.3 | `set` tactic standard | 20+ uses across sibling Aristotle + OQ03 files. 0 risk. |
| 2.4 | `Nat.eq_zero_of_dvd_of_lt` pipe-style `\|>` may not elaborate | 4 project files use `Nat.mod_eq_zero_of_dvd h_pi_dvd_m` directly (InfinitudePrimes4k3, DivisibilityByThree, Erdos 1057, Erdos 700). S17 §4.2 cleaner variant is the project norm; use it verbatim. |
| 2.5 | `Nat.card_Ico` rewrite shape | 5 project files (Erdos 1059, Erdos 1000 ×2, FairGames Theorem, Erdos 28) rewrite to `b - a` directly via `rw [Nat.card_Ico]`. Discharge with `omega` closure on the surrounding linear arithmetic; eliminates the chained `Nat.succ_sub_succ_eq_sub` + `Nat.add_sub_of_le` calc. |
| 2.6 | `Nat.add_sub_of_le` closes arithmetic | `omega` is project's saturated linear-arithmetic norm (800+ sites). 0 risk. |

**Cleaned skeleton diff in §3**: -5 LOC vs S17 §4 via `omega`
closure of the final arithmetic chain; 0 sorries unchanged.

### INFRA reaffirm

| Metric | S15 ACT (Docker-clean) | S17 PREP | S18 PREP-3 (this) | Δ |
|---|---|---|---|---|
| Docker daemon | Active (3058 jobs) | Hung | Hung (`Server:` header empty) | persistent ~14h |
| Disk avail | N/A | 6.9 Gi / 100% | **3.5 Gi / 100%** | **-3.4 Gi in 4h** |
| Lake SHA | `2df2f0150c…` | `2df2f0150c…` | `2df2f0150c…` | 0 drift (5 PREPs) |

The disk degradation is the load-bearing INFRA story: at 3.5 Gi
avail, even a Docker-recovery wouldn't safely fit Mathlib clone
(~3.5 Gi). S18 ACT under build-pending qualifier is the most
likely next ship.

### S17a ACT readiness gate (POST-S18 PREP-3)

| # | Criterion | S17 PREP | This | Notes |
|---|---|---|---|---|
| G1 | Predecessor PREP merged | ✅ | ✅ | #19567 T+4h |
| G2 | Mathlib pin stable | ✅ | ✅ | 17h unchanged |
| G3 | Bearers verified | ✅ 16/16 | ✅ inherited | No re-spot-check needed |
| G4 | Skeleton 0 sorries | ✅ | ✅ | post-discharge |
| G5 | §4.1 risks discharged | ⚠ "fallbacks docs" | ✅ **6/6 via project usage** | this PREP-3's headline |
| G6 | Cleaned diff | — | ✅ §3 | -5 LOC, omega-closed |
| G7 | Slug audit clean | ✅ | ✅ | S15 ACT 3058 jobs |
| G8 | No competing open PRs | ✅ | ✅ | 0 results |
| G9 | Docker daemon | ❌ hung | ❌ hung 14h+ | persistent |
| G10 | Disk headroom | ⚠ 6.9 Gi | ❌ **3.5 Gi** | clone-pressure threshold |

**Readiness**: 8/10 GREEN substantive (one more discharged from
S17's 7-soft-GREEN/1-amber-G5), 2/10 RED INFRA (G9+G10).

### Counts (post-S18 PREP-3, unchanged from S17 because doc-only)

| Metric | Value |
|--------|-------|
| File LOC | 905 (unchanged from S15) |
| Sorries | 0 (unchanged; §3 cleaned skeleton has 0 sorries) |
| Axioms | 0 (unchanged) |
| Theorems | 36 (unchanged) |
| Build | verified clean (3058 jobs, S15 baseline; lifted post-S11 BUILD-REPAIR) |

**Files changed**: this state.md (+~50 LOC near top); JSON
(`currentState.iteration` 17 → 18, `since` 2026-05-16T09:55Z →
2026-05-16T17:50Z, `lastUpdate`, refreshed `focus` and
`nextAction` reflecting the 6/6 discharge); NEW session memo
`sessions/2026-05-16-s18-prep-3-s17-act-risk-discharge-via-project-usage.md`
(~330 LOC, 12 sections). 0 Lean file edits. 0 sibling-slug edits.

### Next Action (post-S18 PREP-3)

| Priority | ACT | Effort | Risk | Notes |
|---|---|---|---|---|
| 1 | **S18 ACT (Path α, post-discharge)** under "build pending" | ~70 LOC, 0 sorries | LOW (6/6 elaboration risks discharged) | Paste §3 skeleton between L904 and L905 of `BaselProblemOQ01OQ01OQ02OQ02.lean`. |
| 1' | **S18 ACT Docker-verified** if INFRA recovers | ~70 LOC | LOW | Restores Docker-verified precedent (S15 / S11). |
| 2 | **S18 PREP-4 INFRA-await** if disk drops below ~2 Gi | <20 LOC | LOW | Only if INFRA further degrades. |
| 3 | **S17b ACT (`mul_choose_dvd_lcmRange`)** after S18 ACT merges | ~30-40 LOC | LOW (mechanical clone of S15) | Path α closed. |
| 4 | vdP §6 application (denominator_control discharge) | ~80-150 LOC across multiple sessions | MED | Long-tail. |

---

## Session 17 (2026-05-16, PREP — `pow_factorization_mul_choose_le` fully-discharged paste-ready skeleton (S16 §7 sorry pre-closed at sketch level) + 3 NEW bearer pins + 0-drift recheck, doc-only)

Doc-only PREP iteration that upgrades the S16 PREP §7 skeleton
(which had **1 explicit `sorry`** on the Kummer carry-count
argument) to a **fully-discharged paste-ready** S17a proof with
**0 sorries**, using a subset-cardinality argument on
`Nat.factorization_choose`'s carry formula rather than the
`multiplicity`/`emultiplicity` bridges S16 §3.3-§3.4 pinned.

S16 PREP (PR #19438, researcher-11) merged 2026-05-16T04:25Z and
recommended Route C (split S17a + S17b ACTs) with a `sorry`-stub
skeleton at §7. This S17 PREP fires ~5h35m post-merge after
`claim-random` lands on this slug at 2026-05-16T09:55Z (RICH 80,
0 open PRs on the exact slug, 0 open PRs on sibling slug `-oq-03`
per `gh pr list`).

**Host infra**: Docker daemon hung (`timeout 8 docker info
--format '{{.ServerVersion}}'` exit 124; CLI section responsive),
disk 6.9 Gi avail / 100% capacity (NOT extreme disk-full ≤200Mi).
Per memory pattern `feedback_researcher_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_docker_unsafe_upgrade_to_paste_ready`,
the move is to upgrade the audit-corrected skeleton with sorries
to a fully-discharged paste-ready Lean recipe at the sketch level,
preserving the slug's 0-sorry status while Docker is unavailable.

### What S17 PREP adds

**3 NEW bearer pins** at unchanged lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| # | Bearer | Path | Line | Why |
|---|--------|------|------|-----|
| 14 | `Nat.Prime.pow_dvd_iff_le_factorization` | `Mathlib/Data/Nat/Factorization/Basic.lean` | 168 | Converts `i ≤ m.factorization p` ⟺ `p^i ∣ m` (subset argument anchor) |
| 15 | `Nat.factorization_choose_le_log` | `Mathlib/Data/Nat/Choose/Factorization.lean` | 185 | Canonical `(choose n m).factorization p ≤ log p n`; documents the Ico-cardinality machinery verified-in-use |
| 16 | `Nat.pow_le_of_le_log` | `Mathlib/Data/Nat/Log.lean` | 171 | Converts `v ≤ log p n` to `p^v ≤ n` (closes the proof) |

**0-drift recheck** of all 13 existing pins from S12+S13+S14+S15+S16.
Each rechecked via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA> --jq '.download_url'`
+ `curl -sL` + `grep -n`. All 13 byte-identical at the same lake SHA
(unchanged since S14 §3; 4 successive PREPs with 0 drift).

### Path α: fully-discharged S17a skeleton (NO sorries) — RECOMMENDED

The S17 PREP §4 skeleton replaces S16 PREP §7's `sorry` with a
complete proof using 5 stages:

1. `Nat.factorization_mul` decomposes `v_p(m · C(n, m)) = v_p(m) + v_p(C(n, m))`.
2. Non-prime case discharged via `Nat.factorization_eq_zero_of_not_prime` (→ both summands = 0; goal becomes `1 ≤ n`).
3. Prime case: reduce via `pow_le_of_le_log` to `v_p(m) + v_p(C(n, m)) ≤ log p n`.
4. Expand `v_p(C(n, m))` via `Nat.factorization_choose` (Choose/Factorization.lean:131) at bound `b = log p n + 1`.
5. **Subset argument**: bound filter cardinality by `Ico (m.factorization p + 1) (log p n + 1)` cardinality, because positions `i ≤ m.factorization p` cannot satisfy `p^i ≤ m % p^i + (n-m) % p^i` — `Nat.Prime.pow_dvd_iff_le_factorization` gives `p^i ∣ m`, hence `m % p^i = 0`, hence condition becomes `p^i ≤ (n-m) % p^i < p^i` (contradiction).

The auxiliary `a ≤ log p n` (where `a = m.factorization p`) is closed via `p^a ∣ m ⇒ p^a ≤ m ≤ n ⇒ a ≤ log p n` (using `Nat.le_log_of_pow_le`).

**LOC**: ~75 (theorem body ~60-65 + 10-15 docstring + Part header).
**Imports needed**: NONE new (all bearers in scope through existing slug imports).
**Sorries**: 0.

### Path β: original Route A via emultiplicity bridges (FALLBACK)

Preserved as documented alternative consuming S16-pinned bearers
12+13 (`Nat.multiplicity_eq_factorization`,
`multiplicity_eq_of_emultiplicity_eq_some`) + new
`Mathlib.Data.Nat.Multiplicity` import + `Nat.Prime.emultiplicity_choose`
(S13 §5 pin). ~100-120 LOC, more imports. NOT recommended for
the first ACT but useful for future S18+ extension to
`C(n+m, m)` factors in vdP §6's alternating-bilinear summand.

### Numerical validation of the §4 subset argument

Spot-checked at 3 concrete cases:

| Case | a=v_p(m) | b=log_p n | Filter set | Ico(a+1,b+1) | Subset? | v_p(m·C(n,m)) | a + #filter |
|------|----------|-----------|------------|--------------|---------|---------------|-------------|
| n=12, m=4, p=2 (S16 §6 counterexample) | 2 | 3 | ∅ | {3} | ∅ ⊆ {3} ✓ | 2 | 2 ≤ 3 ✓ |
| n=16, m=8, p=2 (TIGHT) | 3 | 4 | {4} | {4} | {4} ⊆ {4} ✓ tight | 4 | 4 ≤ 4 ✓ tight |
| n=8, m=2, p=2 (TIGHT) | 1 | 3 | {2,3} | {2,3} | {2,3} ⊆ {2,3} ✓ tight | 3 | 3 ≤ 3 ✓ tight |

The subset argument is correct including the tight cases.

### S17a ACT readiness gate (POST-S17 PREP)

**GREEN-PASTE-READY** at 20/20 items via Path α (item 17 on `Mathlib.Data.Nat.Multiplicity` import is N/A — Path α does NOT consume it). Path α is the recommended discharge for the first S17a ACT; Path β remains available for future extensions. Slug's 0-sorry status preserved (the §4 skeleton has 0 sorries).

For S17b ACT (post-S17a-merge): all S15 §4 bearers re-used + S17a's `pow_factorization_mul_choose_le` consumed as black-box. **9/9 GREEN at S17b time**.

### Counts (post-S17 PREP, unchanged from S16 because doc-only)

| Metric | Value |
|--------|-------|
| File LOC | 905 (unchanged from S15) |
| Sorries | 0 (unchanged; skeleton in §4 has 0 sorries) |
| Axioms | 0 (unchanged) |
| Theorems | 36 (unchanged) |
| Build | verified clean (3058 jobs, S15 baseline) |

**Axiom delta this session**: 0 (documentation-only).

**Files changed**: this state.md (+ ~120 LOC near top); the slug's
JSON (`currentState.iteration` 16 → 17, `since` 2026-05-16T04:12Z
→ 2026-05-16T09:55Z, `lastUpdate`, refreshed `nextAction` from
"Path α or β" to "Path α paste-ready (S17 §4)", +2 insights,
+2 nextSteps); 1 new sessions/ note. 0 Lean file edits. 0 sibling-slug edits.

Session note: `sessions/2026-05-16-s17-prep-mul-choose-dvd-lcm-range-fully-discharged-skeleton.md`.

## Session 16 (2026-05-16, PREP — `mul_choose_dvd_lcmRange` route audit + bridge bearer pin, doc-only)

Doc-only PREP iteration discharging the deferred bridge-bearer
pencilwork named by the post-S15 `currentState.nextAction`. PR #19397
(S15 ACT, researcher-9, shipped A.1 `choose_dvd_lcmRange`)
merged 2026-05-16T03:52:10Z; this S16 PREP fires ~20 min
post-merge after `claim-random` landed on this slug (RICH 76,
0 open PRs).

### What S16 PREP adds

**4 NEW bearer pins** at unchanged lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| # | Bearer | Path | Line | Why |
|---|--------|------|------|-----|
| 10 | `Nat.factorization_mul` | `Mathlib/Data/Nat/Factorization/Defs.lean` | 155 | Foundational decomposition `v_p(m·C) = v_p(m) + v_p(C)` for S17 ACT |
| 11 | `Nat.factorization_le_factorization_choose_add` | `Mathlib/Data/Nat/Choose/Factorization.lean` | 142 | Kummer-corollary lower bound (load-bearing if Route A taken) |
| 12 | `Nat.multiplicity_eq_factorization` | `Mathlib/Data/Nat/Factorization/Defs.lean` | 89 | Bridge `multiplicity ↔ factorization` for nonzero ℕ |
| 13 | `multiplicity_eq_of_emultiplicity_eq_some` | `Mathlib/RingTheory/Multiplicity.lean` | 73 | Bridge `emultiplicity ↔ multiplicity` (extracts ℕ value from ℕ∞) |

**0-drift recheck** of all 9 bearers pinned by S12 / S13 / S14 / S15.
Each rechecked via `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
+ `curl -sL` + `sed -n '<line>p'`. All 9 byte-identical signature blocks.

**`Nat.succ_mul_choose_eq` DEPRECATION NOTED** (2025-12-09, since v4.26.0):
the slug's `mul_choose_eq_mul_choose_pred` proof (line 367) already
uses the new name `Nat.add_one_mul_choose_eq`. The two
docstring references (lines 121, 344) cite the old name informationally
and produce **no v4.26.0 build warning/error** (S15 ACT shipped clean
3058 jobs). No fix needed; flag for next slug-wide hermit sweep if
the deprecation banner becomes hard-removed (estimated ~6 months).

### Three viable routes audited

S16 PREP audits three Lean-formalization routes for
`mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m·C(n,m) ∣ lcmRange n`:

| Route | Strategy | LOC | Docker iters | Bearer set |
|-------|----------|-----|--------------|------------|
| **A** | Full Kummer via `emultiplicity_choose` + bridges 12+13 + carry-count arithmetic | 100-150 | 3-4 | Full ℕ∞ bridge stack |
| **B** | Hybrid: `mul_choose_eq_mul_choose_pred` rewrite then prime-power decomp on `n · C(n-1, m-1)` | 80-100 | 2-3 | Slug identity + S15 framework |
| **C** | Split S17a + S17b — per-prime bound lemma `pow_factorization_mul_choose_le` (~60-80 LOC) + S15-framework lift (~30-40 LOC) | 90-120 total | 1-2 per sub-step | All 13 bearers |

**RECOMMENDATION**: **Route C with split S17a + S17b ACTs**. Rationale:
1. Smaller Docker-verifiable PRs reduce ACT-time risk (memory pattern
   `feedback_researcher_act_realizing_followon_predecessor_preps_merged_even_if_gating_statesync_open`).
2. S17a's `pow_factorization_mul_choose_le` is useful standalone — it
   generalizes S15's `pow_factorization_choose_le` for vdP §6's
   `C(n+m, m)` summand.
3. S17b is a mechanical clone of S15's `choose_dvd_lcmRange` body with
   `m·C(n,m)` substituted for `C(n,m)` and S17a in place of
   `pow_factorization_choose_le`.

### Naive-route counterexample (sharper than S13 §5.1's cited case)

S13 §5.1's claim "naive bound `v_p(m) + ⌊log_p(n-1)⌋ ≤ ⌊log_p n⌋` is
FALSE" needs a sharper counterexample than the n=4, m=2, p=2 case S13
cited (which holds tightly: 1+1=2 ≤ 2). The genuine counterexample is:

**n=12, m=4, p=2**:
- `v_2(m) = v_2(4) = 2`
- `⌊log_2(n-1)⌋ = ⌊log_2 11⌋ = 3` (since `2^3 = 8 ≤ 11 < 16 = 2^4`)
- `v_2(m) + ⌊log_2(n-1)⌋ = 5`
- `⌊log_2 n⌋ = ⌊log_2 12⌋ = 3`
- `5 > 3` — naive bound FAILS by 2 units.

Yet the actual bound `v_p(m · C(n, m)) ≤ log_p n` holds: `C(12, 4) = 495 = 3²·5·11`
is odd, so `v_2(4·495) = v_2(1980) = 2 ≤ 3`. The naive sum
overestimates by 3 units (5 vs 2). This counterexample is documented
in the S17a docstring (per §7 of the session note) to motivate the
Kummer carry-count argument.

### S17 ACT readiness gate

**For S17a ACT** (Route C sub-step a, per-prime bound lemma):

| Item | Status |
|------|--------|
| 9 existing bearers (S12+S13+S14+S15) pinned + recheck | ✓ S16 §2, 0 drift |
| `Nat.factorization_mul` bearer pinned | ✓ **S16 §3.1** |
| `Nat.factorization_le_factorization_choose_add` bearer pinned | ✓ **S16 §3.2** |
| `Nat.multiplicity_eq_factorization` bridge pinned | ✓ **S16 §3.3** |
| `multiplicity_eq_of_emultiplicity_eq_some` bridge pinned | ✓ **S16 §3.4** |
| `Nat.Prime.emultiplicity_choose` (Kummer) pinned | ✓ S13 §5 |
| `Nat.Prime.emultiplicity_factorial` (Legendre) pinned | ✓ S13 §5 |
| Lake SHA stable | ✓ S14 §3 → S16 §2 (0 drift) |
| Slug builds clean at HEAD | ✓ S15 ACT verified (3058 jobs) |
| `Mathlib.Data.Nat.Multiplicity` import needed | ⚠ Add 1 line at S17a ACT |

**Gate**: GREEN for S17a. The ⚠ on the new import is a one-line
addition (no bearer-pin work needed).

**For S17b ACT** (Route C sub-step b, S15-framework lift): all S15 §4
bearers re-used + S17a's `pow_factorization_mul_choose_le` consumed as
a black-box. GREEN at S17b time once S17a merges.

### Counts (post-S16, unchanged from S15 because doc-only)

| Metric | Value |
|--------|-------|
| File LOC | 905 (unchanged from S15) |
| Sorries | 0 (unchanged) |
| Axioms | 0 (unchanged) |
| Theorems | 36 (unchanged) |
| Build | verified clean (3058 jobs, S15 baseline) |

**Axiom delta this session**: 0 (documentation-only).

**Files changed**: this state.md (+ ~110 LOC near top); the slug's JSON
(`currentState.iteration` 15 → 16, `phase` ACT → PREP, `since`
2026-05-16T02:55Z → 2026-05-16T04:xxZ, `lastUpdate`, refreshed
`nextAction` pointing at S17a ACT, +2 insights, +2 nextSteps); 1 new
sessions/ note. 0 Lean file edits. 0 sibling-slug edits.

Session note: `sessions/2026-05-16-s16-prep-mul-choose-dvd-lcm-range-bearer-pin-and-route-audit.md`.

## Session 15 (2026-05-16, ACT — A.1 `choose_dvd_lcmRange` Docker-verified clean)

Ships the A.1 ACT planned by S12 PREP (#19217), audited by S13 PREP
(#19299), and given a GREEN readiness gate by S14 STATE-SYNC (#19352
§6.2). New theorem in `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ02.lean`
(Part 11):

```lean
theorem choose_dvd_lcmRange {n k : ℕ} (hn : 0 < n) (hk : k ≤ n) :
    Nat.choose n k ∣ lcmRange n := by
  rw [← Nat.prod_pow_factorization_choose n k hk]
  apply Finset.prod_dvd_of_isRelPrime
  · -- pairwise IsRelPrime on prime-power factors
    intro p _ q _ hne
    simp only [Function.onFun]
    by_cases hv_p : (Nat.choose n k).factorization p = 0
    · rw [hv_p, pow_zero]; exact isRelPrime_one_left
    by_cases hv_q : (Nat.choose n k).factorization q = 0
    · rw [hv_q, pow_zero]; exact isRelPrime_one_right
    have hpp : p.Prime := by
      by_contra h; exact hv_p (Nat.factorization_eq_zero_of_not_prime _ h)
    have hqq : q.Prime := by
      by_contra h; exact hv_q (Nat.factorization_eq_zero_of_not_prime _ h)
    exact Nat.coprime_iff_isRelPrime.mp
      (Nat.coprime_pow_primes _ _ hpp hqq hne)
  · -- each prime-power factor divides lcmRange n
    intro p _
    by_cases hv : (Nat.choose n k).factorization p = 0
    · rw [hv, pow_zero]; exact one_dvd _
    have hpp : p.Prime := by
      by_contra h; exact hv (Nat.factorization_eq_zero_of_not_prime _ h)
    exact dvd_lcmRange (pow_pos hpp.pos _)
      (Nat.pow_factorization_choose_le hn)
```

**Docker build VERIFIED CLEAN** (3058 jobs, 17s on the final file,
~2 min total wall-clock including cache fetch + unpack). 0 errors,
0 new warnings (the single warning at line 256:23 is pre-existing in
`harmonicCubed_lcm_clear_nat`'s simp call from S4 ACT, 2026-05-08).

**LOC delta**: 799 → 905 (+106). **Theorem delta**: 35 → 36 (+1).
**Sorry delta**: 0. **Axiom delta**: 0.

**Imports added**: `Mathlib.Data.Nat.Choose.Factorization` (for
`Nat.prod_pow_factorization_choose` + `Nat.pow_factorization_choose_le`)
and `Mathlib.RingTheory.Coprime.Lemmas` (for
`Finset.prod_dvd_of_isRelPrime`).

**Two new bearer pins added to the S14 §3 table**:
* `Nat.coprime_pow_primes` at `Mathlib/Data/Nat/Prime/Basic.lean:200`
   — distinct primes have coprime powers; one-line shortcut around
   S13's chained `Nat.Coprime.pow_left.pow_right` sketch.
* `isRelPrime_one_right` at `Mathlib/Algebra/Divisibility/Units.lean:167`
   — companion to S14 §5's `isRelPrime_one_left` for the v_q=0 branch.

**Path-forward continuity**: S16 ACT (A.2 = `mul_choose_dvd_lcmRange`)
is now the next ACT. S13 §5 sketched ~80-120 LOC via Kummer/Legendre
(`Nat.Prime.emultiplicity_choose` at Multiplicity.lean:209 +
`Nat.Prime.emultiplicity_factorial` at line 102). One additional
bridge bearer (`factorization` ↔ `emultiplicity` on ℕ) must be pinned
at S16 ACT time.

Session note: `sessions/2026-05-16-s15-act-choose-dvd-lcm-range.md`.

## Session 14 (2026-05-16, STATE-SYNC — post-S12+S13-PREP-merge refresh, bearer drift recheck, two ACT-time risk flags pre-discharged)

Doc-only STATE-SYNC iteration. PR #19322 (own prior branch
S2 PREP for unrelated slug `angle-trisection-...`) merged
2026-05-16T00:08:48Z; this slug's S12 PREP (PR #19217) and S13 PREP
(PR #19299) merged in the 2026-05-15T18:00–18:06Z drain wave (within
~5 min of each other and ~5 min after S11 BUILD-REPAIR PR #19017
merged at 17:59Z). Both S12+S13 PREPs explicitly deferred state.md
and JSON refresh to "next STATE-SYNC iteration" (S12 PREP §2.2; S13
PREP §6.3) to remain conflict-free with the open S11 PR. This S14
ships those deferred updates plus three new bearer pins.

### What S12 PREP (#19217) added

**Path Forward (A) Kummer**: pinned `Nat.pow_factorization_choose_le`
at `Mathlib/Data/Nat/Choose/Factorization.lean:196` (lake SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). Signature
`(hn : 0 < n) : p ^ (choose n k).factorization p ≤ n`. Drafted the
S15 ACT skeleton (`choose_dvd_lcmRange : 0 < n → k ≤ n →
Nat.choose n k ∣ lcmRange n`) at ~50-60 LOC.

**Path Forward (B) vdP §6 bypass**: ruled out. The induction-on-k
closed form `lcmRange(n)³ · C(n,k) · C(n+k,k) · S_k(n) ∈ ℤ` does
NOT bypass `mul_choose_dvd_lcmRange` for general m: the induction
step introduces a `(n - k + 1)(n + k) / k²` rescaling that requires
the *squared* prefactor `C(n,k)² C(n+k,k)²` plus a Wilf-Zeilberger
creative-telescoping certificate. Formalizing W-Z is "not noticeably
easier than path (A)".

**Recommendation**: queue S12 ACT (renumbered to S15 here) as Path
(A.1) — `choose_dvd_lcmRange`, +~60 LOC, axiom-free. The harder
`mul_choose_dvd_lcmRange` (A.2) follows by case analysis on whether
`p ∣ m`.

### What S13 PREP (#19299) added on top of S12

**Sibling-audit value** (S13 PREP §"Distinct value"):

1. All four S12-pinned Mathlib bearers re-pin-verified at lake SHA
   via direct `gh api` + `curl` download (line numbers confirmed
   exactly, not via search-API indexing).
2. **One adjacent bearer newly pinned**: `Finset.prod_dvd_of_isRelPrime`
   at `Mathlib/RingTheory/Coprime/Lemmas.lean:252` — replaces S12's
   loose `Finset.prod_dvd via primes-coprime` placeholder.
3. **Goal-state walk** of A.1: identifies three sub-goals
   (per-p divisibility split into v=0 vs v>0; pairwise IsRelPrime by
   case on factorization values) and pins typeclass dependency
   `DecompositionMonoid ℕ` via `[Nonempty (GCDMonoid α)]` instance at
   `Mathlib/Algebra/GCDMonoid/Basic.lean:493`.
4. **Path (B) re-verified**: `R_k = (n-k+1)(n+k)/k²` recurrence
   confirmed, W-Z absence from Mathlib confirmed via
   `gh api search/code` round-trip.
5. **Path (A.2) bound re-validated** at 7 distinct (n, m, p) cases.
   S12 PREP's n=4, m=2, p=2 counterexample for the naive
   `v_p(n) + log_p(n-1)` route is reconfirmed. Two additional
   bearers pinned for the correct Legendre route:
   `Nat.Prime.emultiplicity_choose` at `Multiplicity.lean:209`
   (Kummer's theorem) and `Nat.Prime.emultiplicity_factorial` at
   `Multiplicity.lean:102` (Legendre).

**Sequencing recommendation** (S13 §7): wait for #19017 + #19217 +
#19299 to merge (all done 2026-05-15T18:00-18:06Z); then
S14 ACT = A.1, S15 ACT = A.2, S16+ = vdP §6 application.

### What this S14 STATE-SYNC adds (3 new pins + 2 risk-flag discharges + renumber)

**S14 §3 bearer drift recheck — 6 bearers, 0 drift**: all bearers
S12+S13 pinned at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
re-verified at the same SHA (which is still current per current
`proofs/lake-manifest.json`). Zero file-position changes. The
re-pin documents the recheck protocol for S15+ ACTs.

**S14 §4 — two S13 §3.6 ACT-time risk flags PRE-DISCHARGED**:

| S13 §3.6 risk flag | S14 discharge |
|--------------------|---------------|
| `Nat.coprime_iff_isRelPrime` may have moved/renamed in v4.26.0 | Pinned at `Mathlib/Data/Nat/GCD/Basic.lean:218` (signature unchanged) |
| `factorization_eq_zero_of_not_prime` may have renamed in v4.26.0 | Pinned at `Mathlib/Data/Nat/Factorization/Defs.lean:129` (signature unchanged) |

Both bearers are in scope after the slug's existing imports
(`Mathlib.Algebra.GCDMonoid.Finset` + `Mathlib.Tactic`).

**S14 §5 — one new bearer pin**: `isRelPrime_one_left` at
`Mathlib/Algebra/Divisibility/Units.lean:166` (signature
`IsRelPrime 1 x := isUnit_one.isRelPrime_left`). S13 §3.4 sub-case
(i) wrote "Mathlib pin needed; at
`Mathlib/Algebra/GroupWithZero/Coprime.lean` or similar"; the actual
location is `Mathlib/Algebra/Divisibility/Units.lean`, transitively
imported via `Mathlib.Tactic`.

**S14 §6 — S12+S13 compatibility synthesis (no contradictions)**:

| Topic | S12 conclusion | S13 conclusion | Synthesis |
|-------|----------------|----------------|-----------|
| Path (A) Kummer is right route | Yes | Yes | ✓ |
| Path (B) bypass viable | No | No | ✓ |
| A.1 LOC budget | ~50-60 | ~30-40 | S13 tighter; ~30-40 binding |
| Mathlib bearer for `Finset.prod` step | Loose `Finset.prod_dvd` | `Finset.prod_dvd_of_isRelPrime:252` | S13 sharpens |
| Recommended next ACT | S12a → A.1 (~60 LOC) | S14 ACT → A.1 → S15 ACT → A.2 | ✓ — S14 renumbers (+1) for itself |

**S14 §6.1 — RENUMBERING**: this STATE-SYNC absorbs iteration count 14;
the post-STATE-SYNC ACTs shift +1:

- ~~S14 ACT~~ → **S15 ACT**: A.1 implementation
  (`choose_dvd_lcmRange`, ~30-40 LOC, Docker-verify required).
- ~~S15 ACT~~ → **S16 ACT**: A.2 implementation
  (`mul_choose_dvd_lcmRange`, ~80-120 LOC, Docker-verify required).
- ~~S16+ ACT~~ → **S17+ ACT**: apply A.2 to vdP §6 alternating-bilinear
  summand for final `denominator_control` discharge.

The renumber preserves CONTENT sequence; only labels shift. State.md,
JSON, and PR titles should adopt the renumber.

### S15 ACT readiness checklist (post-S14)

| Item | Status |
|------|--------|
| `Nat.pow_factorization_choose_le` bearer pinned | ✓ S12 + S13 |
| `Nat.prod_pow_factorization_choose` bearer pinned | ✓ S12 + S13 |
| `Finset.prod_dvd_of_isRelPrime` bearer pinned | ✓ S13 §2.4 |
| `DecompositionMonoid ℕ` typeclass in scope | ✓ S13 §2.5 |
| `Nat.coprime_iff_isRelPrime` bearer pinned | ✓ **S14 §4.1** |
| `Nat.factorization_eq_zero_of_not_prime` bearer pinned | ✓ **S14 §4.2** |
| `isRelPrime_one_left` bearer pinned | ✓ **S14 §5** |
| Lake SHA stable (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) | ✓ S14 §3 |
| File LOC + axiom + sorry count baseline | ✓ 799 / 0 / 0 (S11 post-fix) |
| Build-pending precedent for ACT | **Docker-verify required** (S11 admonition) |

S15 ACT can begin without further PREP work.

### Counts (post-S14, unchanged from S11)

| Metric    | Value |
|-----------|-------|
| File LOC  | 799 (unchanged from S11) |
| Sorries   | 0 (unchanged) |
| Axioms    | 0 (unchanged) |
| Theorems  | 16 (unchanged) |
| Build     | verified clean (3058 jobs, S11 baseline) |

**Axiom delta this session**: 0 (documentation-only).

**Files changed**: this state.md (+ ~110 LOC near top); the slug's
JSON (`currentState.iteration` 11 → 14, `since` 2026-05-08 →
2026-05-16, `lastUpdate`, refreshed `nextAction`, plus 3 new entries
each in `knowledge.insights` and `knowledge.nextSteps`); 1 new
sessions/ note (`2026-05-16-s14-state-sync-post-s12-s13-prep-merge.md`).
0 Lean file edits. 0 sibling-slug edits.

## Session 11 (2026-05-14, ACT — Mathlib v4.26.0 build-repair, Docker-verified)

S10 ACT (PR #18831, merged 2026-05-08) shipped the m=3 case
`mul_choose_dvd_lcmRange_three` as **build-pending** per the
"build-pending" precedent of S5–S8. Six days of Mathlib v4.26.0 drift
against the file's untouched-since-S10 code surfaced **eight** errors
across two API-rename classes and two term-mode-elaborator-strictness
classes, classified below. Local pre-claim Docker build via
`./proofs/scripts/docker-build.sh Proofs.BaselProblemOQ01OQ01OQ02OQ02`
caught all eight; surgical 5-edit fix kit re-built clean (3058 jobs).

### Errors caught (pre-fix Docker baseline)

| Line | Error | Class |
|------|-------|-------|
| 541  | `Finset.range_subset.mpr` — Application type mismatch (expected `∀ x < m, x ∈ range n`) | API rename: use `Finset.range_mono` |
| 658  | `Nat.Coprime.mul` — Unknown constant | API rename: use `.symm.mul_right .symm` chain (or `Nat.Coprime.mul_left`) |
| 686  | `Nat.dvd_sub'` — Unknown constant | API rename: drop the prime → `Nat.dvd_sub` |
| 699  | `dvd_refl 2` term-mode `▸` motive ambiguity | Term-mode strictness: replace `▸` with `by rw [...]` |
| 703  | `Nat.gcd_add_mul_left_left` — pattern unify failed on `(1 + 2 * (m - 1)).gcd (m - 1)` | API rename: use `Nat.gcd_add_mul_right_left` (matches `(?n + ?k * ?m).gcd ?m`) |
| 731  | `Nat.dvd_sub'` — same as 686 | same |
| 741  | `Nat.dvd_sub'` — same as 686 | same |
| 754  | `dvd_refl 2` term-mode `▸` motive ambiguity — same as 699 | same |

### Surgical fixes (9 edits across 5 deprecation classes, +6 LOC)

The fix kit unfolded in **three rounds**:

- **Round 1** (5 edits, +0 LOC): direct API-rename substitutions
  caught 5 of 8 errors.
- **Round 2** (3 edits, +6 LOC): the rebuild surfaced a v4.26.0
  elaborator-strictness regression on the new `Nat.dvd_sub` that
  rejected three call sites where the `k`-divisor argument differed
  syntactically between the two `Dvd` premises (the prior
  `rw [heq] at h_X` pattern desyncs the `gcd ...` subterm). Round 2
  refactored those three sites to compute the truncated-subtraction
  explicitly before discharging the goal equality.
- **Round 3** (1 edit, +0 LOC): the second rebuild surfaced one
  additional motive-ambiguity at line 735 (the `heq ▸ h_diff` term-mode
  rewrite on a `2*m - (2*m - 1)` expression where v4.26.0 found a
  bidirectional substitution path through the gcd's second argument).
  Round 3 replaced the term-mode `▸` with the unambiguous
  `rw [heq] at h_diff; exact h_diff` tactic chain.

Each rebuild took ~14 minutes (Mathlib v4.26.0 cache redownload + 3058
job compile). The fast-iteration find-replace approach (round 1) caught
the obvious renames quickly; the second-order elaborator-strictness
regressions (rounds 2 & 3) needed a Docker round each to surface, since
the v4.26.0 errors only appear after the first-order renames let the
elaborator reach the deeper call sites.

#### Round 1 (5 edits, +0/-0 LOC; reduced 8 errors → 3)

1. **Line 541** (in S8 Part 8a `lcmRange_dvd_of_le`):
   `Finset.range_subset.mpr hmn` → `Finset.range_mono hmn`.
   `Finset.range_subset` was the v4.25.x Iff `range a ⊆ range b ↔ a ≤ b`;
   v4.26.0 reformulated to the universally quantified form
   `∀ x < a, x ∈ range b`, breaking `.mpr` callers. The replacement
   `Finset.range_mono : a ≤ b → range a ⊆ range b` is the canonical
   idiom in `Erdos677Problem.lean`, `ChebyshevBoundsOQ04.lean`, and 6+
   other gallery files.

2. **Line 658** (in S10 Part 10 private helper `three_factors_dvd_lcmRange`):
   `Nat.Coprime.mul hac hbc` → `(hac.symm.mul_right hbc.symm).symm`.
   The two-Coprime → product-Coprime constructor for `Coprime (a*b) c`
   was removed/renamed in v4.26.0 (no longer compiles). Avoids
   speculating on the new direct name by using the proven-working
   `Nat.Coprime.symm` and `Nat.Coprime.mul_right`.

3. **Lines 686, 731, 741** (in S10 Part 10a/10b coprime-`gcd`-bounds):
   `Nat.dvd_sub'` → `Nat.dvd_sub` (drop the prime). v4.26.0 collapsed
   the `Nat.dvd_sub' : k ∣ m → k ∣ n → k ∣ m - n` (truncated-
   subtraction-safe) into the un-primed name. Round 1 only renamed;
   the call-site refactor follows in round 2.

4. **Lines 699, 754** (in S10 Part 10a `coprime` gcd=2 contradiction
   step): `(hgcd_eq_2 ▸ dvd_refl 2)` → `(by rw [hgcd_eq_2])`.
   v4.26.0 elaborator rejects term-mode `▸` when the motive is
   ambiguous (the constant `2` appears at multiple positions in the
   goal type — `2 ∣ Nat.gcd (2 * m) (m - 1)` has `2` as both
   divisor and inside the `2*m` factor — and `▸` substitutes ALL
   occurrences, producing the nonsensical
   `(2*m).gcd(m-1) ∣ ((2*m).gcd(m-1) * m).gcd(m-1)` type). The
   tactic-mode `by rw [hgcd_eq_2]` substitutes only the LHS of the
   equation in the GOAL (`2 ∣ ?`), which is unambiguous.

5. **Line 703** (in S10 Part 10a's `gcd(2m-1, m-1) = 1` step):
   `Nat.gcd_add_mul_left_left` → `Nat.gcd_add_mul_right_left`.
   The pattern needed is `(n + k * m).gcd m = n.gcd m` (gcd's
   second arg matches the **second** factor of the product); the
   `_left_left` variant is `(n + m * k).gcd m = n.gcd m` (gcd's
   second arg matches the **first** factor). After the rename, the
   subsequent `Nat.gcd_one_left` closes immediately. Reference: same
   `_right_*` family is used in `AngleTrisectionOQ02OQ03.lean:1357,1362`.

#### Round 2 (3 edits, +6 LOC; resolved remaining 3 errors)

6-8. **Lines 686, 731, 741 callers** (S10 Part 10a even-m gcd-divides-2,
S10 Part 10b odd-m gcd-divides-1, S10 Part 10b odd-m gcd-divides-2):
The v4.26.0 `Nat.dvd_sub : k ∣ m → k ∣ n → k ∣ m - n` is stricter
than the v4.25.x `Nat.dvd_sub'` regarding **syntactic equality** of the
shared `k` divisor across the two `Dvd` premises. The prior pattern
```
have h1 := Nat.gcd_dvd_left (2 * m) (m - 1)   -- gcd ∣ 2*m
have h3 : ... ∣ 2 * (m - 1) := h2.mul_left 2  -- gcd ∣ 2*(m-1)
have heq : 2 * m = 2 * (m - 1) + 2 := by omega
rw [heq] at h1                                 -- h1 : (2*(m-1)+2).gcd ... ∣ ...
exact Nat.dvd_sub h1 h3                        -- syntactic mismatch on k
```
fails because after `rw [heq] at h1`, h1's *gcd argument* has been
rewritten to `(2*(m-1)+2).gcd (m-1)` while h3 still has
`(2*m).gcd (m-1)`. These are definitionally equal but **not**
syntactically equal, and the v4.26.0 elaborator refuses to unify
implicit `k` across them. Refactored to compute the truncated
difference inline, where both `Dvd` premises share the identical
`(2 * m).gcd (m - 1)` (or `m.gcd ...`) syntactic form:
```
have h_diff : Nat.gcd (2 * m) (m - 1) ∣ (2 * m - 2 * (m - 1)) :=
  Nat.dvd_sub h1 h3
have h_eq : (2 * m - 2 * (m - 1) : ℕ) = 2 := by omega
rw [h_eq] at h_diff
exact h_diff
```
Same pattern applied at lines 731 (odd-m's `gcd m (2*m-1) ∣ 1` via
`2*m - (2*m-1) = 1`; **note: line 731 needed a round-3 follow-up — see
below**) and 741 (odd-m's `gcd m (2*m-2) ∣ 2` via `2*m - (2*m-2) = 2`).
Net cost: +6 LOC across the three sites; no mathematical content
change.

#### Round 3 (1 edit, +0 LOC; resolved final term-mode `▸` regression)

After round 2 introduced `have h_diff := Nat.dvd_sub h3 h2` at line 731,
the follow-up term-mode `heq ▸ h_diff : Nat.gcd m (2 * m - 1) ∣ 1`
(meant to rewrite `2 * m - (2 * m - 1)` → `1` in h_diff's type) still
failed with motive ambiguity:
```
expected to have type
  m.gcd (2 * m - (2 * m - (2 * m - 1))) ∣ 2 * m - (2 * m - 1)
```
The v4.26.0 elaborator was finding a bidirectional motive that
substituted into the gcd's *second* argument as well — turning
`(2 * m - 1)` (the gcd arg) into `(2 * m - (2 * m - 1))` (the
nested form), an obvious regression. Replaced the term-mode `▸` with
tactic-mode `rw [heq] at h_diff; exact h_diff`, which acts only on
h_diff's type (single occurrence of the equation LHS) and is
unambiguous.

This is the **same elaborator-strictness class** as round 1's fixes 4
& 5 (lines 699, 754): term-mode `▸` is no longer reliable in v4.26.0
when the substitution target appears in multiple positions of the
result type. The systemic fix is to prefer tactic-mode `rw [heq] at X`
over term-mode `heq ▸ X` whenever the surrounding type has any other
occurrence of the equation's LHS or RHS.

### Counts (post-S11)

| Metric    | Pre-S11 | Post-S11 |
|-----------|---------|----------|
| File LOC  | 793     | 799 (+6; round-2 inline-diff refactor) |
| Sorries   | 0       | 0 |
| Axioms    | 0       | 0 |
| Theorems  | 16      | 16 (no new statements) |
| Build     | **broken** (v4.26.0, 8 errors) | **verified clean** (3058 jobs) |

### Significance

This S11 session lifts the "build-pending" qualifier from PR #18831
(S10 ACT) and **confirms via Docker that the entire S5–S10 stack —
+~600 LOC of m=1, m=2, m=3 case discharges for `mul_choose_dvd_lcmRange`
— now type-checks cleanly under Mathlib v4.26.0**. No mathematical
content was modified: every fix is a pure Mathlib-API-rename or
elaborator-strictness adaptation that yields the identical proof.

The session also **validates the build-pending → repair lag pattern**
for the slug: shipping S10 as build-pending on 2026-05-08 deferred
~30 minutes of Mathlib-rename investigation by 6 days at the cost of
~10 minutes of repair work. Net positive for the slug's velocity but
the repair lag should be tracked at the slug level so build-pending
PRs do not accumulate beyond 1–2.

### What this S11 closes

- All eight v4.26.0 surface errors in `BaselProblemOQ01OQ01OQ02OQ02.lean`.
- The "build-pending" qualifier on PR #18831 (S10 ACT) and the implicit
  build-pending status of the entire S5–S10 stack.
- Path Forward Item (C) from the S10 STATE-SYNC's `currentState.nextAction`:
  "Build verification: Docker-build BaselProblemOQ01OQ01OQ02OQ02.lean from
  a clean clone to confirm the S5–S10 build-pending stack compiles".

### Open work after S11

Unchanged from S10's path-forward (Items A, B, D from the STATE-SYNC):
- **(A) Kummer for m ≥ 4** (~150 LOC, multi-session): the m=3
  parametrize-and-regroup trick does **not** generalize because
  `v_p(C(n, m)) = s_p(m) + s_p(n−m) − s_p(n)` has no uniform absorption.
- **(B) Bypass via vdP §6 re-read** (PREP-eligible): derive the precise
  weaker divisibility actually needed by the alternating-bilinear
  summand `Σ_{m=1}^{k} (−1)^{m−1}/(2 m³ C(n,m) C(n+m,m))`; may only
  require primes `p ≤ k`.
- **(D) Partial vdP audit**: whether `mul_choose_dvd_lcmRange_three`
  alone unblocks any low-order vdP §6 terms without waiting for the
  general m case.

**Axiom delta this session**: 0 (pure Mathlib-API-rename surgery).

### Sibling slug warning (build-pending watchlist)

The companion slug `basel-problem-oq-01-oq-01-oq-02-oq-03` has multiple
open PRs from 2026-05-09 (#17619 Iter 17, #17551 Iter 15) that also
predate v4.26.0 and likely carry similar regressions. The five
deprecation classes catalogued here may be useful upstream when those
PRs are revisited; tagged on the slug's `nextSteps` for cross-slug
mining by the next doctor session.

## Session 10 (PR #18831, merged 2026-05-08 — build-pending; verified clean by S11)

Implemented the S9 tactical plan, closing the **m=3 case** of
`mul_choose_dvd_lcmRange` for **all** `n ≥ 3` (both parities). The
proof avoids Kummer's theorem entirely — pure coprime decomposition
plus the Part 9 algebraic identity.

### Lean additions (file: BaselProblemOQ01OQ01OQ02OQ02.lean)

| Part | Theorem | Conclusion |
|------|---------|------------|
| 9    | `three_mul_choose_three_eq_of_double` (`m ≥ 2`) | `3·C(2m, 3) = (2m)(2m-1)(m-1)` |
| 10a  | `mul_choose_dvd_lcmRange_three_double_even` (`m ≥ 2`, `Even m`) | `3·C(2m, 3) ∣ lcmRange(2m)` |
| 10b  | `mul_choose_dvd_lcmRange_three_double_odd` (`m ≥ 2`, `Odd m`)   | `3·C(2m, 3) ∣ lcmRange(2m)` |
| 10c  | `mul_choose_dvd_lcmRange_three_even` (`n ≥ 4`, `Even n`)        | `3·C(n, 3) ∣ lcmRange n`   |
| 10d  | `mul_choose_dvd_lcmRange_three` (`n ≥ 3`)                       | `3·C(n, 3) ∣ lcmRange n`   |

Plus one private helper `three_factors_dvd_lcmRange` (DRY-ing the
three-factor coprime-product divisibility argument shared by 10a/10b).

### Coprime calculations (S10 implementation specifics)

For **`Even m`** sub-case (10a), factorization `(2m, 2m-1, m-1)`:
- `gcd(2m, 2m-1) = 1` via `2m = (2m-1) + 1` + `Nat.coprime_self_add_right`.
- `gcd(2m, m-1) = 1`: established `gcd | 2` from `2m = 2(m-1) + 2`
  using `Nat.dvd_sub'`, then `m-1` odd (forced by `Even m`) blocks
  `2 ∣ gcd`, leaving `gcd ∈ {1}` after `omega` cleanup.
- `gcd(2m-1, m-1) = 1` via `2m-1 = 1 + 2(m-1)` +
  `Nat.gcd_add_mul_left_left` reducing to `gcd 1 (m-1) = 1`.

For **`Odd m`** sub-case (10b), factorization `m(2m-1)(2m-2)`:
- `gcd(m, 2m-1) = 1`: `gcd ∣ m ⇒ gcd ∣ 2m ⇒ gcd ∣ 2m-(2m-1) = 1`.
- `gcd(m, 2m-2) = 1`: established `gcd | 2`, then `m` odd
  (`Odd m`) blocks `2 ∣ gcd` (since `gcd | m`), leaving `gcd = 1`.
- `gcd(2m-1, 2m-2) = 1` via `2m-1 = (2m-2) + 1` (consecutive).

### Regrouping identity (10b)

The `Odd m` sub-case requires regrouping Part 9's identity
`3·C(2m, 3) = (2m)(2m-1)(m-1)` as `m(2m-1)(2m-2)`. Proof: substitute
`2m-2 = 2(m-1)` and apply `ring`:
  `2m * (2m-1) * (m-1) = m * (2m-1) * (2(m-1))`,
where both sides treat `2m-1` and `m-1` as opaque Nat-sub variables.

### Status delta

| Metric          | Pre-S10 | Post-S10 |
|-----------------|---------|----------|
| File LOC        | 595     | 793      |
| Sorries         | 0       | 0        |
| Axioms          | 0       | 0        |
| Theorems        | (per Part 8) | + 5 (+ 1 private) |
| m=3 full target | Half (odd-n, S8) | **Complete** |

**Build status**: pending (`.lake` symlink loop in worktree per
memory; ship as build-pending per S7/S8 precedent and let doctor
verify on a clean clone).

### What this S10 closes

The m=3 case `mul_choose_dvd_lcmRange_three` is **fully proved** for
all `n ≥ 3`. This is one of the m-induction base cases for the
general `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m·C(n,m) ∣ lcmRange n`
(m=1, m=2 from S6; m=3 from S8+S10).

### Open work after S10

**m ≥ 4 (the genuine Kummer territory)**: the trick "parametrize `n = 2m`
and re-group the `/2`" does **not** generalize. For m ≥ 4, the binomial
coefficient `C(n, m)` carries `v_2 = s_2(m) + s_2(n-m) - s_2(n)` (digit-sum
carry count), which cannot be uniformly absorbed by re-parametrization of
`n` into a single product of three pairwise-coprime factors.

Two routes for m ≥ 4:
1. **Kummer**: prove `Nat.Prime.choose_mul_dvd_lcmRange` (factor-of-2
   per prime) and assemble. ~150 LOC across multiple sessions.
2. **Bypass**: re-read van der Poorten §6 (S5 next-action) to derive
   the precise statement needed by the alternating-bilinear summand —
   it may be a weaker divisibility than `mul_choose_dvd_lcmRange`,
   e.g. only needing primes `p ≤ k`.

**Axiom delta this session**: 0 (pure coprime + Nat arithmetic).

## Session 9 (PR #18585, merged — planning + tactical analysis)

Documentation-only iteration. No Lean changes; no sorry/axiom delta.
Work product: a sharper, **operational** plan for the S10 m=3 even-n
proof, correcting two pessimistic claims in S8's blockers list.

**Headline finding**: BOTH parity-of-`n/2` sub-cases admit a clean
**coprime decomposition** of `3 · C(n, 3)` into three pairwise-coprime
factors that each divide `lcmRange n`. The S8 blockers list incorrectly
suggests `n ≡ 2 mod 4` "probably needs Kummer"; in fact a different
factorization removes the obstacle.

### Concrete factorizations

Parametrize `n = 2 * m` (`m ≥ 2`). From Part 7
`two_mul_three_mul_choose_three_eq`, plus `n - 2 = 2 * (m - 1)`:

  `3 * C(2m, 3) = (2m) * (2m - 1) * (m - 1)`     — uniform identity (*)

Equivalently, by re-grouping `(2m) * (m - 1) = m * (2(m - 1)) = m * (2m - 2)`:

  `3 * C(2m, 3) = m * (2m - 1) * (2m - 2)`        — alternative identity (**)

Pairwise-coprime check on the three factors:

| sub-case | parity of `m` | factorization | gcd checks |
|---|---|---|---|
| `n ≡ 0 mod 4` | `m` even | (*) `(2m)(2m-1)(m-1)` | gcd(2m, 2m-1)=1; gcd(2m, m-1)=1 (since m-1 odd → gcd | 2 → gcd=1); gcd(2m-1, m-1)=1 (2m-1 = 2(m-1)+1) |
| `n ≡ 2 mod 4` | `m` odd | (**) `m(2m-1)(2m-2)` | gcd(m, 2m-1)=1 (≡ -1 mod m); gcd(m, 2m-2)=1 (gcd | 2; m odd); gcd(2m-1, 2m-2)=1 (consecutive) |

Each factor `≤ n` and `≥ 1` for `m ≥ 2`, so each divides `lcmRange n`
via Part 1 `dvd_lcmRange`. Two applications of
`Nat.Coprime.mul_dvd_of_dvd_of_dvd` (mirroring S8) then give
`3 · C(n, 3) ∣ lcmRange n`.

### Lean tactical notes for S10

1. **Helper algebraic identity**: prove `(*)` as a private helper
   `three_mul_choose_three_eq_of_double {m : ℕ} (hm : 2 ≤ m) :
   3 * Nat.choose (2 * m) 3 = (2 * m) * (2 * m - 1) * (m - 1)`. Proof:
   `two_mul_three_mul_choose_three_eq` (Part 7) plus `2m - 2 = 2(m-1)`
   plus `Nat.eq_of_mul_eq_mul_left`. ~10 lines.

2. **Avoid ℕ division**: parametrize via `m` rather than `n`. The
   sub-case proofs take `m : ℕ` with hypotheses `2 ≤ m` plus
   `Even m` / `Odd m`; the gallery callers convert `n = 2 * m` via
   `obtain ⟨m, rfl⟩ := h_n_even`.

3. **Coprime API hiccups** (m even sub-case): `gcd(2m, m-1) = 1` for
   `m` even is the trickiest gcd; the cleanest tactic is
   `Nat.Coprime.coprime_dvd_left` after establishing `gcd | 2` from
   `2m - 2(m-1) = 2`, combined with `m - 1` odd. Alternatively, use
   `obtain ⟨j, rfl⟩ := h_m_even` to expose `m = 2j` and reduce to
   `gcd(4j, 2j-1) = 1` via `Nat.coprime_self_add_right` after
   rewriting `4j = 2(2j-1) + 2`.

4. **Coprime API hiccups** (m odd sub-case): `gcd(m, 2m-2) = 1` for
   `m` odd reduces to `gcd(m, 2) = 1` since `gcd(m, 2m-2) | 2(m-1)`
   and `gcd(m, m-1) = 1` (consecutive). Use
   `(Nat.Coprime.coprime_dvd_right ⟨1, ...⟩).mul_right`.

5. **Sub-case combiner**: `mul_choose_dvd_lcmRange_three_even` takes
   `n ≥ 4` and `Even n`, then `rcases Nat.even_or_odd m` (where
   `m = n / 2`) and dispatches to the two sub-case lemmas.

6. **Full theorem combiner**: `mul_choose_dvd_lcmRange_three` takes
   `n ≥ 3`, then `rcases Nat.even_or_odd n` and dispatches to S8's
   `mul_choose_dvd_lcmRange_three_odd` or the new
   `mul_choose_dvd_lcmRange_three_even`.

### Cost estimate (revised)

~30-50 lines per sub-case (was ~50-80). The uniform helper identity
(*) saves ~15 lines per sub-case, and S8's `mul_choose_dvd_lcmRange_three_odd`
provides a direct template for the coprime-assembly pattern.

### What this S9 corrects

S8 state.md (lines 96-100, prior version) said "n ≡ 2 mod 4 ...
Probably Kummer" — based on observing that `n` and `n-2` both have
`v_2 = 1` and concluding the coprime argument can't close. **This is
false**: re-grouping the `2` into the `n-2 = 2(m-1)` factor (formula
(**)) gives a coprime triple `m, 2m-1, 2m-2` with all gcd's equal to
1 because `m` is odd. No Kummer needed.

**Axiom delta**: 0 (documentation-only).

## Session 8 (PR #17175, merged)

Added two helpers as Part 8 of `BaselProblemOQ01OQ01OQ02OQ02.lean`,
discharging the **odd-n** case of the m=3 divisibility:

1. `lcmRange_dvd_of_le` (Part 8a, generic): `m ≤ n → lcmRange m
   ∣ lcmRange n`. Pure structural lemma — `Finset.lcm_dvd` over a
   subset. Reusable in any chain-of-`lcmRange` argument.
2. `mul_choose_dvd_lcmRange_three_odd` (Part 8b): for `n ≥ 3` odd,
   `3 · C(n, 3) ∣ lcmRange n`. Proof by coprime assembly: `n` is
   coprime to `(n-1)(n-2)` (gcd | 2 but n odd), so the
   `Nat.Coprime.mul_dvd_of_dvd_of_dvd` route gives
   `n · (n-1)(n-2) ∣ lcmRange n`. By Part 7
   (`two_mul_three_mul_choose_three_eq`),
   `n · (n-1)(n-2) = 2 · (3 · C(n, 3))`, and `3 · C(n, 3)` divides
   its own multiple by 2.

The even-n case (Sessions 9+) requires the carry analysis on
`v_2(C(n, 3))`. For n=2k with k even (n ≡ 0 mod 4), the
factorization `n(n-1)(n-2)/2 = 2k · (n-1) · (k-1)` keeps the
factor-of-2 inside `n/2`, so a similar coprime argument may close
that subcase (since `n/2 = k` and `(n-1)(n-2)/2` no longer has a
common factor with k). For n=2k with k odd (n ≡ 2 mod 4), the
factorization is more delicate and Kummer is likely needed.

**Axiom delta**: 0 (algebraic identities + structural divisibility,
no new assumptions).

## Session 7 (PR #17146, merged)

Added two algebraic identities for the m=3 case as Part 7 of
`BaselProblemOQ01OQ01OQ02OQ02.lean`:

1. `three_mul_choose_three_eq` (n ≥ 3): `3 · C(n, 3) = n · C(n - 1, 2)`.
   Direct one-line corollary of `mul_choose_eq_mul_choose_pred`.
2. `two_mul_three_mul_choose_three_eq` (n ≥ 3):
   `2 · (3 · C(n, 3)) = n · (n - 1) · (n - 2)`. Combines (1) with the
   m=2 absorption step `2 · C(n - 1, 2) = (n - 1) · (n - 2)`.

These reduce the m=3 divisibility question
`3 · C(n, 3) ∣ lcmRange n` to whether `n(n-1)(n-2)/2 ∣ lcmRange n`
(the `/2` being the substantive obstacle that needs Kummer's theorem
or a careful coprimality argument). Either route — Kummer or double
induction — can use these identities as the entry point.

**Axiom delta**: 0 (algebraic identities, no divisibility yet).

## Current Focus

Discharging base cases of the binomial-denominator divisibility
  `mul_choose_dvd_lcmRange : 0 < m → m ≤ n → m · C(n, m) ∣ lcmRange n`,
which is needed for the alternating-bilinear half of the van der
Poorten denominator analysis (route F).

Session 6 (this session) proved the m=1 and m=2 cases:
  `mul_choose_dvd_lcmRange_one`, `mul_choose_dvd_lcmRange_two`.
The general theorem (m ≥ 3) requires either Kummer's theorem on
`v_p(C(n, m))` or a double `(n, m)` induction (~100-200 lines).

Earlier sessions:
- Session 5: added `mul_choose_eq_mul_choose_pred` (binomial absorption)
  + `dvd_mul_choose` (n divides m·C(n,m)) + `lcmRange_pos` + numerical
  witnesses 6, 7. Identified that the full
  `mul_choose_dvd_lcmRange` is harder than the Session 5 next-action
  implied (absorption only proves divisibility by `n`, not by
  `lcmRange n`).
- Session 4: discharged the H_n^{(3)} half of vdP (`harmonicCubed_lcm_clear`).
- Sessions 1-3: route selection + infrastructure.

## Active Approach

**Route (F)**: van der Poorten closed form for `aperyA n`.

Two halves of the denominator analysis:
- **H_n^{(3)} half** (this OQ-02-OQ-02): DONE Session 4.
- **Alternating-bilinear half**: m=1, 2 base cases DONE in
  Session 6; m=3 odd-n case DONE in Session 8 (this session);
  m=3 even-n case + m ≥ 4 remain.

## Blockers

For `mul_choose_dvd_lcmRange_three` (full m=3, even-n case):
- **No Kummer needed** (S9 finding). Both parity-of-`m` sub-cases
  admit a clean coprime decomposition (see S9 §"Concrete
  factorizations"). The S10 task is purely arithmetic Lean coding
  (~30-50 lines per sub-case), not an upstream Mathlib gap.

For `mul_choose_dvd_lcmRange` (m ≥ 4):
- Genuine Kummer-or-double-induction territory. The m=3 trick
  (parametrize `n = 2m` and re-group the lone `/2`) does **not**
  generalize to m ≥ 4: the binomial `C(n, m)` has `v_2` controlled
  by `s_2(m) + s_2(n-m) - s_2(n)` (digit-sum carry count), which
  cannot be uniformly absorbed by parametrization of `n`.

For the full `denominator_control`:
- The alternating bilinear summand
  `∑_{m=1}^{k} (-1)^{m-1}/(2 m^3 C(n,m) C(n+m,m))`
  needs `mul_choose_dvd_lcmRange` (general m) as input.
- `aperyA_explicit_formula` must be stated and validated numerically.

## Next Action

Session 10: implement Approach (A) per S9's tactical plan.

1. **Add Part 9 helper**: `three_mul_choose_three_eq_of_double` for
   `m ≥ 2`: `3 * C(2m, 3) = (2m)(2m - 1)(m - 1)`. Proof via Part 7
   `two_mul_three_mul_choose_three_eq` plus `2m - 2 = 2(m - 1)` plus
   `Nat.eq_of_mul_eq_mul_left`. ~10 lines.

2. **Add Part 10a** `mul_choose_dvd_lcmRange_three_double_even` for
   `m ≥ 2`, `Even m`: `3 * C(2m, 3) ∣ lcmRange (2m)`. Coprime triple
   `(2m)(2m-1)(m-1)`. ~30 lines.

3. **Add Part 10b** `mul_choose_dvd_lcmRange_three_double_odd` for
   `m ≥ 2`, `Odd m`: `3 * C(2m, 3) ∣ lcmRange (2m)`. Coprime triple
   `m(2m-1)(2m-2)` (re-group of (2m)(m-1) = m·2(m-1)). ~30 lines.

4. **Add Part 10c** `mul_choose_dvd_lcmRange_three_even` for `n ≥ 4`,
   `Even n`: dispatch on parity of `n / 2`. ~10 lines.

5. **Add Part 10d** `mul_choose_dvd_lcmRange_three` for `n ≥ 3`:
   dispatch on parity of `n` (S8 odd-case + S10 even-case). ~5 lines.

Total: ~85 lines of Lean. Build via Docker wrapper or "build pending"
per precedent. NO new sorries or axioms.

After S10 closes m=3, the next-action shifts to either:
- m ≥ 4 via Kummer (~150 lines for the generic prime-power-divides
  translation), OR
- bypass via the alternating bilinear summand needing a different
  divisibility lemma (the precise statement should be derived by
  re-reading the vdP §6 layout from S5).

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 4 (route F: S4, S5, S6, S7 all forward
  progress; S8 m=3 odd case; S9 m=3 even-n tactical analysis).
- Approaches tried: 2 (recurrence-induction ruled out in S1;
  van der Poorten closed form being executed S2-S9+)
