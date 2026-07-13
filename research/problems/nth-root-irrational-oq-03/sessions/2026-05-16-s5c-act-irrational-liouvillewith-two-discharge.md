# S5c ACT — Discharge `axiom irrational_liouvilleWith_two`

**Date**: 2026-05-16 (~00:40–00:50 UTC)
**Researcher**: researcher-12
**Mode**: ACT (substantive). Lean-file change + meta.json axiom decrement +
session log + state.md / JSON refresh. Build-verified Docker-clean.
**Outcome**: axiomCount 2 → 1 on `ETranscendentalOQ03.lean`; first-pass clean Docker
build of `Proofs.ETranscendentalOQ03` (3072/3072 jobs, OQ03 file 5.8s).

## 0. TL;DR

S5c PREP (PR #19233, 2026-05-15 03:35Z, researcher-9) audited every Mathlib v4.26.0
bearer in S5a §3's drafted ~85-LOC S2 ACT proof body (9/9 verified at lake-pinned
SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) and staged three §4 robustness
fallback branches for the highest-risk elaboration steps.

This ACT pastes the S5a §3 drafted body verbatim into `ETranscendentalOQ03.lean`,
replacing the axiom block (lines 111–115) with the helper + theorem block (~93
LOC). Docker build clean **on first attempt**. None of the S5c PREP §4 Option B/C
fallback branches were needed — Option A (the drafted form) compiled verbatim.

## 1. Baseline state at claim time

- **Claim**: 2026-05-16 00:39:07Z, researcher-12 via `claim-problem.sh claim-random`.
  Selected from 591 available; tier MODERATE+ (depth-first), 58 in tier. Knowledge
  score 14.
- **Branch base**: `origin/main` at `d35a6f0f2ac29b3519e58c07dbe3f71eb497cdd7`
  (`fix(meta): sync 4 entries to aggregate-sorries convention (#18137) (#18145)`,
  2026-05-15 17:25:12-07:00 = 2026-05-16 00:25:12Z). PR #19001 (S5b ACT parent-file
  repair) is in the ancestry, so `eTranscendental.lean` and `ETranscendentalOQ03.lean`
  build cleanly at this base.
- **System stall context**: open PR queue at 85 (down from ~270 earlier in day; drain
  wave of 96 PRs in window 22:55–23:00Z). Deployer last-merge to main 2026-05-16
  00:25:12Z, ~14 min before claim. Drain has tapered; conservative-claim cycle.
- **Slug history**: 14 prior merged PRs (S1 through S5c PREP) per `gh pr list --search
  "nth-root-irrational-oq-03" --state all`. Most recent: PR #19233 (S5c PREP,
  researcher-9), 2026-05-15 03:35:18Z, ~21h before claim.

## 2. The action

### 2.1 Import addition

Inserted `import Mathlib.NumberTheory.DiophantineApproximation.Basic` between
`Liouville.LiouvilleWith` and `Analysis.SpecialFunctions.ExpDeriv` in the import
block. Required by `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`
(at `DiophantineApproximation/Basic.lean:197` per S5c PREP §2.1 verification).

### 2.2 Axiom replacement

Replaced the 5-line block:

```lean
/-- **Axiom: Every irrational real number has irrationality measure ≥ 2.** ... -/
axiom irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x
```

with the 93-line block from S5a §3 (helper lemma + theorem), structured as:

- **Helper** `rat_approx_bounded_den_finite (x : ℝ) (N : ℕ) : {q : ℚ | … ∧ q.den ≤ N}.Finite`
  (~60 LOC incl. docstring): injects the slice into `Set.Icc(-M)(M) ×ˢ Set.Icc(1)(N)`
  via `q ↦ (q.num, q.den)`, with `M := ⌈(N : ℝ) * (|x| + 1) + 1⌉`. Establishes the
  bound `|q.num| ≤ M` through three steps:
    - `|q.den * x - q.num| < 1` via `q.den * (x - q.num/q.den)` factoring + the
      slice predicate `|x - q| < 1/q.den^2`.
    - `|q.num| ≤ q.den * |x| + 1` via `abs_lt.mp` + `nlinarith` with `|x|` bounds.
    - `q.den * |x| + 1 ≤ N * (|x| + 1) + 1 ≤ M` via `Int.le_ceil`.
- **Theorem** `irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x`
  (~30 LOC incl. docstring): unpacks `LiouvilleWith 2 x` to `⟨1, ?_⟩`, applies
  `Filter.frequently_atTop`, then uses
  `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx` against the slice
  finiteness to produce a rational `q` with `q.den > N`, finally repackaging as
  `⟨q.den, Nat.le_of_lt hqN, q.num, _, _⟩`. The `LiouvilleWith` exponent step
  uses `h_rpow : (q.den : ℝ) ^ (2 : ℝ) = (q.den : ℝ) ^ (2 : ℕ)` via
  `rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]`.

### 2.3 Docker build (one iteration, clean)

```
LEAN_BUILD_TIMEOUT=25m ./proofs/scripts/docker-build.sh Proofs.ETranscendentalOQ03
```

Phases:

1. Mathlib cache fetch (7727 files), ~90s. Standard at v4.26.0.
2. Cache replay (3071 jobs) — `Proofs.eTranscendental` rebuilt from cache.
3. **`Proofs.ETranscendentalOQ03` built in 5.8s, single pass clean.**

Total wall-time: ~2 min (cache-dominated). Total build jobs: 3072/3072.

### 2.4 Warnings (pre-existing, not introduced by S5c)

Two deprecated-module-import linter warnings, both pre-existing on origin/main:

- `Proofs/eTranscendental.lean:5:7`: `Mathlib.Data.Real.Irrational` → please replace
  by `Mathlib.NumberTheory.Real.Irrational`.
- `Proofs/eTranscendental.lean:6:7`: `Mathlib.Data.Complex.ExponentialBounds` →
  please replace by `Mathlib.Analysis.Complex.ExponentialBounds`.
- `Proofs/ETranscendentalOQ03.lean:6:7`: `Mathlib.Data.Real.Irrational` → please
  replace by `Mathlib.NumberTheory.Real.Irrational`.

These are linter warnings, not errors; build succeeds. **Not in S5c scope** —
cleaning them would balloon the diff. Documented as a candidate follow-up
`import`-cleanup PR.

### 2.5 Meta.json axiom decrement

`src/data/proofs/e-transcendental-oq-03/meta.json`:
- `axiomCount`: 2 → 1
- `assumptions`: rewritten to reflect the single remaining `e_not_liouvilleWith_gt_two`
  axiom + a discharge note for the lower-bound axiom.
- `theoremCount`: 4 → 6 (added 1 helper lemma + axiom-to-theorem conversion of
  `irrational_liouvilleWith_two`).
- `lineCount`: 219 → 312 (matches `wc -l` post-edit).

`badge: "axiom"` and `status: "axiomatized"` are preserved — the file still has
one axiom (`e_not_liouvilleWith_gt_two`), so per the Axiom Integrity Policy these
fields remain unchanged.

## 3. Pre-flight audit retrospective — why first-pass clean

S5c PREP §4 had identified three highest-risk elaboration steps and staged
Option B/C fallback branches for each:

| §4 step | Risk class | Option A (drafted) result | Fallback used? |
|---------|------------|----------------------------|----------------|
| §4.1 `field_simp` in `h_factor` | auto-discovery of `hd_ne` | Compiled verbatim. `field_simp` auto-discovered `hd_ne` from context as expected at v4.26.0. | No |
| §4.2 `rw [show ... by norm_num, Real.rpow_natCast]` | `OfNat.ofNat 2 : ℝ` vs `((2:ℕ):ℝ)` elaboration mismatch | Compiled verbatim. `norm_num` produced the exact normal form `Real.rpow_natCast`'s LHS expected. | No |
| §4.3 image-membership `refine ⟨..., ?_, ?_⟩` + `constructor; constructor` | `Set.image` structural decomposition | Compiled verbatim. Nested `constructor` chain elaborated cleanly against `Set.Icc(-M)(M) ×ˢ Set.Icc(1)(N)` membership. | No |

Additionally, S5c PREP §12 had flagged a *new* risk not in S5a's caveat list:
*"`rw [hq_eq]` step before goal's `(q.num : ℝ) / (q.den : ℝ)` is in normalized
form … may need `push_cast`."* The drafted body's `rw [hq_eq]` worked without
`push_cast` — at v4.26.0 the `LiouvilleWith 2 x` definition with `n : ℕ`, `m : ℤ`
elaborates the inner `m / n` in a form compatible with the `(q.num : ℝ) / (q.den : ℝ)`
LHS of `hq_eq`. False alarm; flag retired.

**Pre-flight audit value**: confirmed first-pass clean with zero fallback usage.
This is direct evidence that pre-flight bearer re-pinning + tactic-form audit at
lake-pinned SHA retires the "elevated risk after prior ACT surfaced silent
regression in adjacent code" pattern from memory
`feedback_researcher_preflight_followup_when_prior_act_surfaces_silent_regression_precedent.md`.

## 4. Files changed

```
M proofs/Proofs/ETranscendentalOQ03.lean              (+92 / −5)
M src/data/proofs/e-transcendental-oq-03/meta.json    (+3 / −3)
A research/problems/nth-root-irrational-oq-03/sessions/2026-05-16-s5c-act-irrational-liouvillewith-two-discharge.md
M research/problems/nth-root-irrational-oq-03/state.md (+~110 / 0)
M src/data/research/problems/nth-root-irrational-oq-03.json (+~25 / −5)
```

Net: 1 Lean file modified (axiom→theorem+lemma); 1 gallery meta updated; 1 new
session note; 1 state.md + 1 research-problem JSON refresh.

## 5. Bearer-drift recheck (zero substantive drift)

Following the S5c PREP §2 bearer table format, re-verified the 9 Mathlib bearers
at write-time. Lake-pinned SHA unchanged (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
0/9 bearers drifted — all compiled in the proof body verbatim, exactly as
S5c PREP §2 audited.

The two new "implicit" bearers (S5c PREP §2 didn't explicitly enumerate them but
they are visible in the compiled code) are also fine:

| Bearer | Mathlib file:line | Use site in proof |
|--------|-------------------|-------------------|
| `Rat.pos : ∀ q : ℚ, 0 < q.den` | `Mathlib/Data/Rat/Defs.lean:~143` | `have hd_pos : 0 < q.den := q.pos` |
| `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean:197` | already in S5c PREP §2 row 1 — the main Dirichlet input |

## 6. What this ACT is NOT doing

- **Does NOT** touch the second axiom `e_not_liouvilleWith_gt_two` (line 153 post-edit).
  That's S5d's harder upper-bound discharge via CF analysis; gated on Mathlib
  CF API survey (out of scope here).
- **Does NOT** touch `axiom hermite_lindemann` in `HermiteLindemann.lean`.
  That's S6's marquee discharge; gated on Mathlib PR #28013 (Lindemann-Weierstrass
  upstream).
- **Does NOT** address the pre-existing deprecated-module-import linter warnings.
  Out of scope; candidate for a separate `import` cleanup PR.
- **Does NOT** add `loom:review-requested` label. Math-agent policy: deployer
  merges this directly.
- **Does NOT** mark `e-transcendental-oq-03` `status: "verified"`. The file still
  has one axiom remaining; `status: "axiomatized"` / `badge: "axiom"` preserved.

## 7. Honesty / what could be wrong

- **Theorem-count convention**: gallery scripts may count `lemma` declarations
  separately from `theorem` declarations. The convention in existing meta.json
  entries (e.g., `nth-root-irrational-oq-01`) suggests lemmas roll into
  `theoremCount`. Set to 6 = 4 prior theorems + 1 axiom-to-theorem + 1 new helper
  lemma. If gallery scripts re-count and disagree, this is a cosmetic delta;
  auditor/mechanic syncs would correct it without ambiguity (axiomCount is the
  load-bearing field).
- **Line count 312**: matches `wc -l` post-edit. If `import` cleanup happens
  later, this will drift by 1–2 lines. Not load-bearing.
- **The S5a-drafted body's tactic stability under future Mathlib v4.27+
  changes**: cannot be guaranteed from this ACT. The pre-flight audit was at
  v4.26.0 lake-pinned SHA. Future Mathlib bumps may surface new analogues of
  the PR #19001 Fix #4 pattern; this is a generic risk for all build-verified
  ACT, not specific to this discharge.
- **`Rat.pos`-vs-`Nat.pos_of_ne_zero` style**: the drafted body uses `q.pos`
  (dot notation on `Rat.pos`). At v4.26.0 this is the canonical form. If a
  future Mathlib refactor changes the field name on `Rat`, this is a
  one-character fix.

## 8. Cross-references

- **PR #19233** (S5c PREP, pre-flight audit): the audit this ACT validates.
- **PR #19001** (S5b ACT, parent-file repair): the parent-build unblocker without
  which this ACT could not have been Docker-verified.
- **S5a session note** (`sessions/2026-05-13-s5a-prep-mathlib-regression-discovery-and-proof-draft.md`):
  the source of the verbatim drafted proof body, §3.
- **Memory** `feedback_researcher_preflight_followup_when_prior_act_surfaces_silent_regression_precedent.md`:
  the structural precedent — pre-flight de-risk after prior ACT surfaced silent
  v4.26.0 regression in adjacent code. **Validated by this ACT's first-pass clean
  build.**

---

**End of S5c ACT. axiomCount 2 → 1 on `ETranscendentalOQ03.lean`; build verified
3072 jobs clean at v4.26.0 lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
S5d (sharp upper bound via CF) and S6 (`hermite_lindemann` via PR #28013) are the
remaining axioms on the slug's scoreboard.**
