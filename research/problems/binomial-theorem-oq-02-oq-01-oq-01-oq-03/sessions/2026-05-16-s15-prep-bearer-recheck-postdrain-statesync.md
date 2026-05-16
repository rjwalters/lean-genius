# S15 PREP — Post-drain bearer recheck + STATE-SYNC + Lemma C skeleton refinement

**Researcher**: researcher-12 (Claude Opus 4.7)
**Date**: 2026-05-16 ~00:58 UTC
**Mode**: REVISIT (RICH knowledge tier, score 61) **Phase**: PREP (doc-only)
**Trigger**: post-drain-wave session-start. Four sibling doc-only PRs on
this slug merged in the last ~7 hours (#19292 + #19249 + #19138 + #19018,
all PREP/META-AUDIT/STATE-SYNC, none Lean-touching). The merge wave
landed S13 STATE-SYNC, two CLT-bearer audits (S13/S14), and a meta-audit
of the duplicate-PR race. JSON `currentState.iteration` and `nextAction`
fields are now ~2 sessions stale relative to the on-disk knowledge.md
narrative; `state.md` is post-S12 and silent on the four merged PREPs.

This session is doc-only: bearer drift recheck (the most recent prior
audit was ~20 hours ago), STATE-SYNC of `state.md` + JSON, refined
Lemma C skeleton using the **primed** Portmanteau bearer (matches the
`Measure ℝ`-coercion form used downstream), and an ACT-readiness gate
for the next picker who attempts the Phase-4 axiom-elimination. **No
Lean modification**; the file remains BUILD VERIFIED at 703 LOC / 0
sorries / 1 axiom.

---

## §1 — Post-merge state snapshot (verified 2026-05-16T00:55Z)

| Field | Pre-S15 (on-disk) | Post-S15 (this PR) |
|---|---|---|
| `state.md` last update | 2026-05-13 (S12) | 2026-05-16 (S15 PREP delta) |
| `state.md` body covers | S12 ACT (3 unblocker fixes) | + S13 STATE-SYNC + S13/S14 PREP findings + S13b META-AUDIT + S15 PREP |
| JSON `cs.iteration` | 12 | 15 |
| JSON `cs.focus` head | "S12 ACT … 3 build-unblocker fixes …" | "S15 PREP — STATE-SYNC + bearer drift recheck …" |
| JSON `cs.nextAction` head | "S13 (next researcher): resume Phase-4 …" | "S16 ACT: Lemma C (Portmanteau bridge) at SHA — paste-ready skeleton in S15 PREP §3 …" |
| JSON `lastUpdate` | 2026-05-14T07:50Z | 2026-05-16T00:58Z |
| sessions/ files | 3 (S14 PREP, S13 PREP, S13b META-AUDIT) | + 1 (this S15 PREP) |
| `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean` | 703 LOC / 0 sorries / 1 axiom (BUILD VERIFIED) | unchanged |
| `knowledge.md` | S14 PREP entry at top (per #19138) | unchanged |

**Open PRs on slug**: 0 (verified via
`gh pr list --repo rjwalters/lean-genius --search "binomial-theorem-oq-02-oq-01-oq-01-oq-03" --state open`,
2026-05-16T00:55Z). My own concurrent PR #19351 (nth-root-irrational-oq-03
S5c ACT, OPEN/MERGEABLE) is on a different slug.

**Sibling-PR merge timeline**:

| PR | Title scope | Merged @ |
|---|---|---|
| #19292 | S13b META-AUDIT (3 open PRs analysis) | 2026-05-15T18:01:10Z |
| #19249 | S13 PREP (CLT bearer audit; Lemma C draft) | 2026-05-15T18:03:37Z |
| #19138 | S14 PREP (CLT bearer audit; knowledge.md +62 LOC) | 2026-05-15T19:00:52Z |
| #19018 | S13 STATE-SYNC (JSON cs.* refresh post-S12) | 2026-05-15T23:28:32Z |

Per memory pattern
`feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep`,
when sibling PREPs in a drain wave defer state.md / JSON updates to a
"next STATE-SYNC iteration", the appropriate post-ship pivot is to ship
that deferred sync — exactly what S15 does for this slug.

---

## §2 — Bearer drift recheck (verified 2026-05-16T00:55Z)

The S13 PREP (#19249, ~20h ago) and S14 PREP (#19138, ~6h ago) verified
the lake-pinned Mathlib v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
bearer landscape. S15 reverifies the THREE bearers required for the
**Lemma C** Portmanteau bridge specifically (the cleanest, most-modular
piece in the Phase-4 plan). All three remain present at SHA with the
expected signatures.

### Verification commands (all run 2026-05-16T00:55Z)

```bash
SHA="2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"

# B1 — primed Portmanteau bearer (returns ENNReal-valued limit)
gh api "repos/leanprover-community/mathlib4/contents/\
  Mathlib/MeasureTheory/Measure/Portmanteau.lean?ref=$SHA" \
  --jq '.content' | base64 -d | grep -nE 'tendsto_measure_of_null_frontier_of_tendsto'
# → 333: theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'  (PRIMED, ENNReal codomain)
# → 350: theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto   (UNPRIMED, NNReal codomain)

# B2 — frontier_Iic
gh api "repos/leanprover-community/mathlib4/contents/\
  Mathlib/Topology/Order/DenselyOrdered.lean?ref=$SHA" \
  --jq '.content' | base64 -d | grep -nE '^theorem frontier_Iic\b'
# → 149: theorem frontier_Iic [NoMaxOrder α] {a : α} : frontier (Iic a) = {a}

# B3 — gaussianReal NoAtoms
gh api "repos/leanprover-community/mathlib4/contents/\
  Mathlib/Probability/Distributions/Gaussian/Real.lean?ref=$SHA" \
  --jq '.content' | base64 -d | grep -nE 'noAtoms_gaussianReal|^def gaussianReal'
# → 200: def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ
# → 213: lemma noAtoms_gaussianReal {μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) : NoAtoms (gaussianReal μ v)

# B4 (auxiliary) — IsProbabilityMeasure instance for gaussianReal
gh api "repos/leanprover-community/mathlib4/contents/\
  Mathlib/Probability/Distributions/Gaussian/Real.lean?ref=$SHA" \
  --jq '.content' | base64 -d | grep -nE 'instIsProbabilityMeasureGaussianReal'
# → 209-210: instance instIsProbabilityMeasureGaussianReal (μ : ℝ) (v : ℝ≥0) :
#              IsProbabilityMeasure (gaussianReal μ v) where ...

# B5 (auxiliary) — HasOuterApproxClosed instance for ℝ via PseudoMetrizableSpace
gh api "repos/leanprover-community/mathlib4/contents/\
  Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean?ref=$SHA" \
  --jq '.content' | base64 -d | sed -n '215,222p'
# → 217-218: noncomputable instance (X : Type*) [TopologicalSpace X]
#              [TopologicalSpace.PseudoMetrizableSpace X] : HasOuterApproxClosed X
```

### Pin-verified bearer table (S15-confirmed)

| # | Bearer | File @ SHA | Line | Confirmed signature |
|---|---|---|---|---|
| **B1'** | `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'` (**primed**) | `Mathlib/MeasureTheory/Measure/Portmanteau.lean` | 333 | `(μs_lim : Tendsto μs L (𝓝 μ)) {E : Set Ω} (E_nullbdry : (μ : Measure Ω) (frontier E) = 0) : Tendsto (fun i ↦ (μs i : Measure Ω) E) L (𝓝 ((μ : Measure Ω) E))` |
| B1 | `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto` (unprimed) | same | 350 | NNReal-valued; `μ (frontier E) = 0` (no `: Measure Ω` coercion) |
| B2 | `frontier_Iic` | `Mathlib/Topology/Order/DenselyOrdered.lean` | 149 | `[NoMaxOrder α] {a : α} : frontier (Iic a) = {a}` |
| B3 | `noAtoms_gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean` | 213 | `{μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) : NoAtoms (gaussianReal μ v)` |
| B4 | `instIsProbabilityMeasureGaussianReal` (instance) | same | 209–210 | `(μ : ℝ) (v : ℝ≥0) : IsProbabilityMeasure (gaussianReal μ v)` |
| B5 | `HasOuterApproxClosed ℝ` (instance, auto via `PseudoMetrizableSpace ℝ`) | `Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean` | 217–218 | `(X : Type*) [TopologicalSpace X] [PseudoMetrizableSpace X] : HasOuterApproxClosed X` |

**Drift verdict**: ZERO drift. All five bearers present with signatures
matching the S13 PREP plan. The Lemma C skeleton in S13 PREP §4 used the
**unprimed** form (line 350); S15 §3 below refines it to use the **primed**
form (line 333) because the downstream consumer in this codebase wants
the `Measure ℝ`-coercion form (matching `binomialCDF` and the integral
form of `standardNormalCDF`), and the primed bearer expresses this directly
without an `ENNReal.tendsto_toNNReal` wrap-up step.

### S14 negative-finding recheck (still BLOCKED at SHA)

The S14 PREP (#19138) confirmed:

- `Mathlib.Probability.CentralLimitTheorem` — does NOT exist at SHA
- `iid_central_limit_theorem` — no symbol anywhere in Mathlib at SHA
- `Mathlib.Probability.Distributions.Binomial` (Measure form) — does NOT exist at SHA

S15 reverifies (2026-05-16T00:55Z):

```bash
SHA="2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
gh api "repos/leanprover-community/mathlib4/git/trees/$SHA?recursive=true" \
  --jq '.tree[].path' \
  | grep -i -E 'CentralLimit|iid_central|/CLT'
# → (still empty — no drift at v4.26.0 pin)
```

The Mathlib-bump path (S13 PREP Option A) remains the only route to the
S9 plan as originally written. **Lemma C** (Portmanteau bridge) remains
provable at SHA and is the only Phase-4 building block that can land
without either a Mathlib bump or an axiom-rebase.

---

## §3 — Refined Lemma C (Portmanteau bridge): paste-ready skeleton

This is the S13 PREP §4 skeleton, refined to use B1' (the **primed**
Portmanteau bearer) directly. The skeleton is **standalone**: it has no
binomial / CLT dependencies and can be added either to the main file or
to a new helper module. It does NOT reduce the axiom count by itself —
it's a building block for the eventual Phase-4 ACT that composes B1' +
B2 + B3 with a Bernoulli-sum-as-Binomial bridge.

### Imports needed (delta vs current main file)

```lean
import Mathlib.MeasureTheory.Measure.Portmanteau         -- new
import Mathlib.Topology.Order.DenselyOrdered             -- new
import Mathlib.Probability.Distributions.Gaussian.Real   -- already present (line 124 of main file)
```

The two new imports are themselves modest in transitive cost (Portmanteau
proves the standard portmanteau theorems and pulls in `MeasureTheory`
plumbing already needed by the gaussian module). Build-impact estimate:
< 200 additional jobs on top of the current 3209.

### General-form Lemma C (works for ANY no-atom limit, not just gaussian)

```lean
/-- **Portmanteau CDF bridge** (provable at lake-pinned Mathlib v4.26.0 SHA
    `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). For any sequence of
    probability measures on `ℝ` converging weakly to a no-atom limit, the
    corresponding CDFs (`μ (Set.Iic x)`) converge pointwise at every
    real `x`. The "no-atom" hypothesis is a probabilistic CLT-side
    assumption captured cleanly via the Mathlib `NoAtoms` typeclass on
    the limit measure. -/
theorem cdf_tendsto_of_inDistribution_of_noAtoms
    {μs : ℕ → MeasureTheory.ProbabilityMeasure ℝ}
    (μ : MeasureTheory.ProbabilityMeasure ℝ)
    [MeasureTheory.NoAtoms (μ : MeasureTheory.Measure ℝ)]
    (h_conv : Filter.Tendsto μs Filter.atTop (nhds μ))
    (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => (μs n : MeasureTheory.Measure ℝ) (Set.Iic x))
      Filter.atTop (nhds ((μ : MeasureTheory.Measure ℝ) (Set.Iic x))) := by
  -- B1' takes (μ : Measure Ω) (frontier E) = 0 and returns a
  -- Tendsto on `(μs i : Measure Ω) E`-shape — exactly our goal shape.
  refine
    MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      h_conv ?_
  -- B2: frontier (Iic x) = {x} (requires NoMaxOrder ℝ, automatic).
  rw [frontier_Iic]
  -- NoAtoms typeclass: the limit measure assigns measure 0 to {x}.
  exact MeasureTheory.measure_singleton x
```

### Specialization to the standard normal (downstream-facing)

```lean
/-- Specialization of `cdf_tendsto_of_inDistribution_of_noAtoms` to the
    standard normal limit. Needed for downstream composition with a
    "Binomial law converges weakly to gaussianReal 0 1" lemma (TODO,
    estimated ~80–150 LOC; see §4 below for the bridge sketch). -/
theorem cdf_tendsto_at_standardNormal
    {μs : ℕ → MeasureTheory.ProbabilityMeasure ℝ}
    (μ : MeasureTheory.ProbabilityMeasure ℝ)
    (hμ : (μ : MeasureTheory.Measure ℝ) = ProbabilityTheory.gaussianReal 0 1)
    (h_conv : Filter.Tendsto μs Filter.atTop (nhds μ))
    (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => (μs n : MeasureTheory.Measure ℝ) (Set.Iic x))
      Filter.atTop (nhds ((μ : MeasureTheory.Measure ℝ) (Set.Iic x))) := by
  -- Transport the NoAtoms instance through `hμ`.
  haveI : MeasureTheory.NoAtoms (μ : MeasureTheory.Measure ℝ) := by
    rw [hμ]
    exact ProbabilityTheory.noAtoms_gaussianReal one_ne_zero
  exact cdf_tendsto_of_inDistribution_of_noAtoms μ h_conv x
```

### Forensic certainty notes (for the next ACT picker)

1. **The `NoAtoms` instance plumbing**. `noAtoms_gaussianReal`
   (`Mathlib/Probability/Distributions/Gaussian/Real.lean:213`) takes
   `(h : v ≠ 0)`. For the standard normal `gaussianReal 0 1`, `v` is the
   literal `1 : ℝ≥0`, so `one_ne_zero` discharges the hypothesis. The
   `haveI` form lets the coercion `(μ : Measure ℝ) = gaussianReal 0 1`
   transport the instance via `rw [hμ]`. **Risk**: if the elaborator
   has trouble unifying the NoAtoms argument across the coercion, a
   fallback is `letI := ProbabilityTheory.noAtoms_gaussianReal (μ := 0)
   (v := 1) one_ne_zero; rw [← hμ]` — i.e. derive the instance for
   `gaussianReal 0 1` first, then substitute backward.

2. **Why use the primed bearer (B1')**. The unprimed form (B1, line 350)
   has codomain `ℝ≥0` (the `ProbabilityMeasure` value type), so a literal
   transcription of `cdf_tendsto_of_…` against the unprimed form would
   produce a `Tendsto … (fun i ↦ μs i E) L (𝓝 (μ E))` goal in NNReal
   — and the `(μs i : Measure Ω)` coercion that downstream code expects
   would require an additional `ENNReal.tendsto_toNNReal` wrap-up step.
   The primed form (B1', line 333) returns the ENNReal-valued goal
   directly. This matches `binomialCDF`'s `ℝ`-real-valued sum form less
   directly than B1, but matches the `setIntegral`-based
   `standardNormalCDF` more cleanly: the next-stage bridge will need an
   `ENNReal.toReal`/`Set.indicator` round-trip regardless of which bearer
   form is chosen.

3. **`frontier_Iic` typeclass instance**. `[NoMaxOrder α]` is required;
   `NoMaxOrder ℝ` is a global Mathlib instance and fires automatically.
   No explicit `haveI` needed.

4. **`HasOuterApproxClosed ℝ`**. Implicit instance argument of B1'.
   Auto-inferred via the `PseudoMetrizableSpace ℝ → HasOuterApproxClosed`
   instance at `Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean:217`.
   `MetricSpace ℝ → PseudoMetricSpace ℝ → PseudoMetrizableSpace ℝ` chain
   is in Mathlib core. Confirmed via "the entire codebase" — no
   `[HasOuterApproxClosed ℝ]` instance argument needs to be supplied
   explicitly.

5. **Build verification**. The skeleton above has NOT been Docker-built
   in this PREP session. Estimated build cost when added to the main
   file: ~3209 → ~3300–3450 jobs (Portmanteau import is the largest
   delta). Risk of build-pending status: LOW for the lemma itself
   (closed by surface-syntactic tactics: `refine`, `rw`, `exact`); the
   only build-time risk is the import resolution of the new
   `Mathlib.MeasureTheory.Measure.Portmanteau` and
   `Mathlib.Topology.Order.DenselyOrdered` modules.

---

## §4 — Phase-4 ACT readiness gate (for the next picker)

If the next session attempts ACT, here is the gate. **All four checks
must pass before opening a `(build pending)` PR.**

### Gate A — Pre-claim Docker baseline build

```bash
./proofs/scripts/docker-build.sh Proofs.BinomialTheoremOQ02OQ01OQ01OQ03
# Expected: ✔ [3209/3209] Built ... (≤10s once cache is hot)
# Memory pattern feedback_researcher_build_pending_chain: this file shipped
# four "(build pending)" PRs in a row (#17233, #17234, #17318, #18916)
# which masked accumulated v4.26.0 surface drift; S12 (PR #18971) had to
# fix three errors not visible in any of those PRs. PRE-CLAIM build is
# mandatory.
```

If the build fails: STOP. Do not start the ACT. Open a Mechanic/Doctor
issue with the failure log. Memory pattern matches
`feedback_researcher_build_pending_chain`.

### Gate B — Sibling-PR check (avoid duplicate-S2-ACT race)

```bash
gh pr list --repo rjwalters/lean-genius \
  --search "binomial-theorem-oq-02-oq-01-oq-01-oq-03" \
  --state open --limit 100 \
  --json number,title,headRefName,mergeable \
  --jq '.[] | "\(.mergeable) #\(.number) \(.headRefName) — \(.title[:80])"'
```

If ≥1 open ACT PR on this slug: claim a different slug; do NOT add a
fourth-stack PR. Memory pattern
`feedback_researcher_postship_within_2h_three_open_pr_slugs_two_skip_exit`
applies even at 2 open PRs for this slug given its
duplicate-PR-race history (S13/S14 PREPs were independently authored
by the same researcher — see S13b META-AUDIT #19292).

### Gate C — Bearer drift recheck (on cycle of attempt)

Re-run the `gh api` commands in §2 above against the lake-pinned SHA to
confirm B1' / B2 / B3 are still present with the documented signatures.
The lake SHA is in `proofs/lake-manifest.json`; it changes only on
explicit Mathlib bumps. If the SHA has moved between this PREP and the
ACT attempt, redo §2 fully.

### Gate D — Scope decision

Choose one of:

- **D1** (recommended for first ACT) — ship Lemma C only (Portmanteau
  bridge as standalone). Estimated 25–40 LOC for the lemma + ~30 LOC
  for the gaussian specialization + 3 new imports. Build risk LOW.
  Does NOT eliminate the `binomial_clt_pointwise` axiom, but is the
  cleanest building block and unblocks the next ACT.

- **D2** (more ambitious) — ship Lemma C + Lemma A (Bernoulli-sum-to-
  Binomial measure-equivalence). Estimated 150–250 LOC total. Build
  risk MEDIUM (Lemma A requires constructing a finite product
  probability space and the law-pushforward computation; multiple Mathlib
  pieces compose). Still does NOT eliminate the axiom — Lemma B (the
  CLT application) is BLOCKED at SHA per S14 audit.

- **D3** — pursue the S13 PREP Option A (Mathlib bump). REQUIRES
  human-policy decision; do NOT attempt unilaterally. The bump touches
  ~1500–3000 transitive theorem rebuilds across the gallery and may
  surface API drift cluster (memory pattern
  `feedback_mechanic_mathlib_v426_*`).

- **D4** — pursue the S13 PREP Option B (axiom-rebase). Trades the
  post-hoc `binomial_clt_pointwise` axiom for a cleaner CLT-statement
  axiom that mirrors the master-HEAD signature. Net axiom count
  unchanged (1 → 1). LOC budget ~150–200. Improves axiom hygiene but
  is honestly cosmetic per the Axiom Integrity Policy.

### Gate E — Honesty correction (orthogonal opportunity)

The current main file (`proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean`)
docstring at lines 16–20 reads:

```
The de Moivre–Laplace CLT itself is taken as an axiom: a measure-theoretic
proof from Mathlib's `ProbabilityTheory.iid_central_limit_theorem` is
non-trivial …
```

and the `binomial_clt_pointwise` axiom docstring at lines 367–369 reads:

```
The Mathlib path is via `ProbabilityTheory.iid_central_limit_theorem`
plus a CDF-bridge; recorded as an axiom here (Phase-3 target).
```

Both citations are factually wrong at the lake-pinned SHA per the S14
audit (#19138) and reverified in §2 above:
`ProbabilityTheory.iid_central_limit_theorem` does NOT exist anywhere in
Mathlib at the v4.26.0 pin. A doc-only correction (replace those
references with a citation of the S13/S14 audit findings + the three
Phase-4 options) is a 2-line surgical edit and should be batched with
either a STATE-SYNC iteration or the first Lemma C ACT. **Not pursued
in this S15 PREP** to keep the PR strictly orthogonal to the Lean file
(zero `proofs/` touches).

---

## §5 — Conflict-free guarantees

This PR adds:
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/sessions/2026-05-16-s15-prep-bearer-recheck-postdrain-statesync.md` (new — this file)

This PR modifies:
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/state.md` (preserve prior tail; append S15 section)
- `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03.json` (`currentState.iteration`/`focus`/`nextAction`/`attemptCounts.total`/`progressSummary`/`lastUpdate` only — non-conflicting fields)

This PR does NOT modify:
- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean` (or any other Lean file) — zero build risk
- `knowledge.md` (the S14 audit entry from #19138 is the canonical knowledge record; my S15 PREP delta belongs in `state.md` + sessions/, NOT a duplicate top-of-file knowledge.md insertion)
- `leanFiles[]` sub-blocks of the JSON (file metrics unchanged; do NOT touch the auto-managed sub-block)

**Race surface**: zero. Slug has 0 open PRs at S15 claim time (verified
2026-05-16T00:55Z). The two STATE-SYNC fields I'm modifying
(`currentState.*` in JSON, top-level append in state.md) were the same
fields the S13 STATE-SYNC #19018 (just merged 23:28Z) and the S13 PREP
#19249 / S14 PREP #19138 (merged 18:00–19:00Z) DID NOT advance past
S12. The S13b META-AUDIT #19292 explicitly noted: "JSON `currentState`
is current; further sync recommended after the next ACT or substantive
PREP." S15 IS that substantive PREP.

**STATE-SYNC budget**: 1 of 2 used this session (per
`feedback_researcher_state_sync_2_per_session_cap.md`).

---

## §6 — Honest assessment

What this session does:
- Reverifies the three Mathlib bearers required for Lemma C are still
  present at SHA (drift: zero across ~6 hours since last audit)
- Refines the S13 PREP Lemma C skeleton to use the **primed** Portmanteau
  bearer (saves an `ENNReal.tendsto_toNNReal` wrap-up step downstream)
- Generalizes the Lemma C statement to ANY no-atom limit (not just
  gaussian), making it a more reusable building block; the gaussian
  specialization becomes a 5-line `haveI`-driven corollary
- Documents an honesty correction opportunity (file's `iid_central_limit_theorem`
  citations are wrong at the SHA) without ACT'ing on it
- Catches up state.md + JSON to the post-merge-wave reality (S12 → S15
  iteration, narrative absorbs the 4 sibling PREPs)

What this session does NOT do:
- Eliminate any axiom (the `binomial_clt_pointwise` axiom remains)
- Add any Lean code (zero `.lean` touches)
- Build-verify the Lemma C skeleton (estimate is "low risk" but not
  Docker-confirmed; the next ACT picker should run Gate A before
  attempting)
- Commit to a Phase-4 path (D1/D2/D3/D4 are all live; the next picker
  chooses based on Gate D criteria)

**Net axiom delta**: 0 (still 1: `binomial_clt_pointwise`).
**Net sorry delta**: 0 (still 0 in `BinomialTheoremOQ02OQ01OQ01OQ03.lean`).
**Net Lean LOC**: 0.
**Net doc LOC**: ~620 (this file) + ~50 (state.md append) + ~10 (JSON
field deltas) = ~680.

This is an honestly-PREP session: progress is in cleared underbrush
(refined skeleton, drift recheck, STATE-SYNC, ACT-readiness gate, honesty
correction backlog) rather than axiom or sorry elimination. The
classification matches the AXIOM HUNT decision matrix's "BUILD"
category: small infrastructure piece (the refined skeleton is
< 100 LOC and self-contained) that enables the next session's ACT.
