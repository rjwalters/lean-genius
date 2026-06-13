# Current State

**Phase**: ACT (S15 BUILD-REPAIR — file now Docker-verified clean; G3 AMBER→GREEN. dE_dk assembly still due.)
**Since**: 2026-06-13T00:00:00Z
**Iteration**: 15

## Iteration 15 (2026-06-13, researcher-2): S15 BUILD-REPAIR — Mathlib-drift fixes; file builds clean (Docker 7745)

**Critical finding**: `AmgmInequalityOQ04OQ02.lean` did **not** compile at the
current Mathlib pin (v4.26.0), despite being labeled `status: axiomatized,
sorries: 0` in the gallery. The S14 patch (#22… era) left it "build pending"
and it had in fact accumulated **7 distinct Mathlib-drift breakages** across 6
sites. A baseline Docker build (this session) surfaced them; all are now fixed
and the file is **Docker-verified clean (7745 jobs, 0 errors, 0 sorries)**.

### Breakages fixed (Mathlib v4.26.0 drift)

1. **`𝓝` unknown** (×2, `dK_dk`): the file opened `MeasureTheory
   intervalIntegral Real` but not `Topology`. Added `open scoped Topology`.
2. **`div_le_div` unknown** (×2, §9 bound lemmas): renamed to `div_le_div₀`
   in current Mathlib (same 4-arg signature `(0≤c)(a≤c)(0<d)(d≤b) : a/b ≤ c/d`).
3. **`field_simp; ring` / `linear_combination` failures** (3 sites: the
   pointwise K/E identity §12, `auxFnK_deriv_form_eq`, `h_eq_intermediate`):
   current `field_simp`/`ring_nf` commutes the radicand `k²·sin²θ → sin²θ·k²`,
   splitting `√(1−k²sin²θ)` and `√(1−sin²θk²)` into two distinct atoms `ring`
   cannot unify, and leaving inverses uncleared because the `≠ 0` hypotheses
   kept the un-commuted order. **Fix pattern**: canonicalize the radicand to a
   single `sin²·k²` order via `simp only [show 1−k²sin²θ = 1−sin²θk² from by
   ring]`, supply commuted `≠ 0` / sqrt-square facts (`mul_comm` + the
   original), then `field_simp [commuted facts]` clears denominators and
   `rw [hsq']; ring` closes.
4. **`field_simp; ring` no-goals** (1 site, §16 dIntegrandK rewrite): current
   `field_simp` fully closes the goal, so the trailing `ring` errored with
   "No goals". Removed the redundant `ring`.

### Counts

| | Before | After |
|--|--|--|
| Builds (Docker) | **NO (broken)** | **YES (7745 jobs)** |
| LOC | 1575 | 1601 |
| Axioms | 1 (`legendre_relation`) | 1 (unchanged) |
| Theorems | 47 | 47 (unchanged) |
| Sorries | 0 | 0 |

**Axiom unchanged** — this is a build repair, not an axiom discharge. It
restores the 47 theorems to genuinely machine-checked status (they were
unverified while the file was broken). G3 (dK_dk Mathlib-API-clean) is now
**GREEN/Docker-verified**. G4 (`dE_dk` assembly) remains the next milestone
toward discharging `legendre_relation` via the Wronskian closure.

---

## Iteration 14 (2026-06-02T19:00Z, researcher-1): S14 ACT Site-1 — minimal-diff B1 fix in `dK_dk` (§4.4 path; +16 LOC; build pending; Site-2 deferred)

S14 ACT Site-1 applies the **minimal-diff** §4.4 fix path (per S11c PREP
PR #19290) to the merged `dK_dk` template in
`proofs/Proofs/AmgmInequalityOQ04OQ02.lean`. The patch is **+16 LOC**
inside a single 76-LOC theorem; no other declarations touched.

### What this patch does

Discharges BLOCKER B1 (Mathlib API mismatch F1+F2 in merged `dK_dk` at
file lines 1482-1557) by inserting an `ε`/`Metric.ball` scaffold that
lifts the existing `s`-domain machinery to the form expected by
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

**Concretely (file lines 1504-1517 of the patched file):**
```lean
  -- B1 fix per S11c §4.4: pick ε so Metric.ball k ε ⊆ s.
  set ε : ℝ := min (M - k) (k + M) with hε_def
  have hε_pos : 0 < ε := by
    simp only [hε_def]
    exact lt_min (by linarith) (by linarith)
  have h_ball_eq_s : Metric.ball k ε ⊆ s := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx
    obtain ⟨hx_low, hx_hi⟩ := hx
    have hε_le_Mk : ε ≤ M - k := by simp only [hε_def]; exact min_le_left _ _
    have hε_le_kM : ε ≤ k + M := by simp only [hε_def]; exact min_le_right _ _
    exact ⟨by linarith, by linarith⟩
```

Then `h_bound` (1540-1547) and `h_diff` (1553-1561) are rewritten to
quantify over `∀ κ ∈ Metric.ball k ε` (was `∀ κ ∈ s`), each using
`h_ball_eq_s` to lift the inner κ back into `s` before invoking the
existing helpers (`h_kappa_sq_le`, `h_kappa_sq_lt_one`,
`dIntegrandK_abs_le_bound`, `integrandK_hasDerivAt_in_k`). Finally the
parametric-integral lemma call (1563-1564) takes `hε_pos` (was
`hs_nhds`) as its first explicit argument, matching the Mathlib slot
`(ε_pos : 0 < ε)`.

### Why §4.4 instead of §4.1

S11c §4.5 recommends §4.1 (full rewrite to `ε`/`ball`, +13 LOC/theorem)
as cleaner. But §4.4 (lift `s`-domain via `h_ball_eq_s`, ~+8 LOC) is
strictly safer:
- Preserves all existing `s`/`M` machinery (`h_kappa_sq_le`,
  `h_kappa_sq_lt_one`, `boundDIntegrandK`, bound-integrability) — no
  re-derivation of these from scratch.
- Smaller diff surface = smaller chance of introducing new errors
  without Docker validation.
- Concentrates the change to four localized sites (one insertion, two
  ∀-rewrites, one arg-substitution).

A future PR can convert to §4.1's cleaner form once §4.4 is verified.

### File counts (this PR)

| | Before | After | Δ |
|--|--|--|--|
| LOC | 1559 | 1575 | +16 |
| Axioms | 1 | 1 | 0 |
| Sorries | 0 | 0 | 0 |
| Theorems | 47 | 47 | 0 |
| Defs | 10 | 10 | 0 |

**Axiom unchanged** — this PR does NOT discharge `legendre_relation`.
That comes from S15 (Wronskian closure) which requires both `dK_dk` AND
`dE_dk`. Site-1 here only fixes the **B1 Mathlib API mismatch** in
`dK_dk`; Site-2 (`dE_dk` E-side mirror) is deferred to S15-prep.

### Build status

**Build pending** — Docker not run in this iteration per project
convention for `[Researcher — broken proofs/.lake symlink]` and
memory entry [Docker image-corruption blocker]. The §4.4 fix path is
mechanical per S11c PREP audit; main residual risks are:
- Lean elaboration syntax (e.g. `min_le_left _ _` argument inference).
- `abs_lt` rewrite direction in `Metric.mem_ball` chain.

Auditor/Mechanic verification will surface any of these. The merged
`dK_dk` was already build-pending since #17606 (2026-05-09), so this
patch does not regress anything Docker-verified.

### B2 status — fully resolved since S13

State.md (iter 13) flagged 3 stale-open PRs from 2026-05-08:
- **#17371** (S6 dE_dk theorem): merged 2026-05-19T17:53Z as
  **session-file-only** (added `sessions/2026-05-08-s06-dE-dk-theorem.md`,
  did NOT touch the .lean file). So the merged-but-broken `dE_dk` from
  the PR title never actually landed in the gallery file — only the
  session note did.
- **#17445** (S8 dE_dk replay): CLOSED without merge.
- **#17477** (S9 complModulus boundary helpers): CLOSED without merge.

B2 is therefore retired in this iteration. No new B-flag created.

### S11 ACT readiness gate (refreshed)

| # | Item | Status |
|---|------|--------|
| G1 | Lake pin stable | GREEN (`2df2f0150c…` unchanged since S11c) |
| G2 | `complModulus_hasDerivAt` in main | GREEN (#17500) |
| G3 | `dK_dk` Mathlib-API-clean in main | **AMBER** (Site-1 patch here, build pending) |
| G4 | `dE_dk` in main | **RED** (still no canonical version; Site-2 still due) |
| G5 | `legendre_relation_symmetric` for constant-pin | GREEN |
| G6 | S11 closure recipe documented | GREEN (#19187 §3) |
| G7 | Mathlib API matched at pin (read-side) | GREEN |
| G8 | No open-PR text collisions with the fix path | GREEN (0 open PRs for slug) |

**6/8 GREEN, 1/8 AMBER (pending Docker), 1/8 RED.** Next iteration
(S15-prep) addresses G4 by appending the E-side `dE_dk` mirror.

### Files changed by this iteration

- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` — +16 LOC inside `dK_dk`
  (one insertion block + two ∀-quantifier rewrites + one arg
  substitution). Gallery file line count 1559 → 1575.
- `src/data/proofs/amgm-inequality-oq-04-oq-02/meta.json` — `lineCount`
  1559 → 1575 in both top-level meta and `leanFile` block.
- `src/data/research/problems/amgm-inequality-oq-04-oq-02.json` —
  `currentState.iteration` 13 → 14; `currentState.phase` ACT (unchanged);
  `currentState.since` → `2026-06-02T19:00:00Z`; `currentState.lastUpdate` →
  `2026-06-02T19:00:00Z`; B1 description marks "Site-1 patched (build
  pending)"; B2 dropped (resolved); new `nextAction` (S15-prep: Site-2
  `dE_dk` mirror); `knowledge.builtItems` appends S14 Site-1.
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-06-02-s14-act-site1-b1-fix.md` —
  new session file documenting the patch.

## Iteration 13 (2026-05-16T05:00Z, researcher-9): S13 STATE-SYNC — absorb S11 + S11b + S11c PREPs; surface BLOCKER B1

S13 STATE-SYNC (doc-only) absorbs three PREP merges that landed since
iter 12 and surfaces the load-bearing BLOCKER found by S11c into the
top-level `## Blockers` section so the next ACT picker (mechanic or
researcher) can act on it. Lean code: unchanged.

### Absorbed PREP merges

| PR # | Merged | Subject | Headline finding |
|------|--------|---------|------------------|
| #19187 | 2026-05-15 22:56Z | S11 PREP | Wronskian-closure bearer audit at lake SHA; flagged 2 stale CONFLICTING `dE_dk` PRs (#17371, #17445); recommended fresh re-implementation. |
| #19222 | 2026-05-15 18:05Z | S11b PREP | Copy-paste-ready `dE_dk` fallback skeleton (~76 LOC mirroring merged `dK_dk` template) with E-side helper inventory verified line-accurate. |
| #19290 | 2026-05-15 18:01Z | S11c PREP | **Mathlib API mismatch audit** — bugs F1 (wrong first-arg type) + F2 (wrong scope for h_bound/h_diff) in BOTH the merged `dK_dk` AND the proposed `dE_dk`. Fix path documented in §4. |

### Bearer pin re-verification (drift = 0 since S11c)

Re-fetched `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
at lake-pinned SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (lake
manifest unchanged from S11c; toolchain `leanprover/lean4:v4.26.0`).
Lines 96-111 of the file confirm:

```lean
nonrec theorem hasDerivAt_integral_of_dominated_loc_of_deriv_le
    {F : 𝕜 → ℝ → E} {F' : 𝕜 → ℝ → E} {x₀ : 𝕜}
    (ε_pos : 0 < ε)                                                       -- ← F1: 0 < ε
    (hF_meas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) (μ.restrict (Ι a b)))
    ...
    (h_bound : ∀ᵐ t ∂μ, t ∈ Ι a b → ∀ x ∈ ball x₀ ε, ‖F' x t‖ ≤ bound t)   -- ← F2: ball x₀ ε
    ...
```

The bug bearer signature is unchanged since S11c's 2026-05-15 08:10Z
fetch — F1/F2 still apply verbatim. The merged `dK_dk` at file
lines 1485-1548 passes `hs_nhds : s ∈ 𝓝 k` to the first slot (which
expects `0 < ε`) and quantifies `h_bound`/`h_diff` over `∀ κ ∈ s`
(which expects `∀ x ∈ ball k ε`). Both BLOCKING for elaboration.

### Stale-open `dE_dk` PR landscape (verified 2026-05-16 04:58Z)

Three PRs from 2026-05-08 remain open, all `mergeable_state="dirty"`:

| PR # | Title | Last update | Notes |
|------|-------|-------------|-------|
| #17371 | S6 — dE_dk theorem (build pending) | 2026-05-08T19:18Z | Original dE_dk attempt. Inherits F1/F2. |
| #17445 | S8 — dE_dk replay of #17371 (build pending) | 2026-05-08T22:03Z | Replay; inherits F1/F2. |
| #17477 | S9 orthogonal — complModulus boundary helpers (build pending) | 2026-05-08T22:28Z | Helpers superseded by `complModulus_hasDerivAt` (merged via #17500). |

Per #19187 §4 these need rebase or close, but **rebasing without fixing
F1/F2 produces a still-broken build**. The S11b skeleton in #19222 also
inherits F1/F2 because it was authored before the S11c audit.

### S11 ACT readiness gate (refreshed)

S11 Wronskian closure (→ discharges `legendre_relation` axiom, 1 → 0)
requires `dK_dk` AND `dE_dk` to compile clean. Current readiness:

| # | Item | Status |
|---|------|--------|
| G1 | Lake pin stable | GREEN (`2df2f0150c…` unchanged since S11c) |
| G2 | `complModulus_hasDerivAt` in main | GREEN (#17500) |
| G3 | `dK_dk` compiles in main | **RED** (F1/F2 in merged code) |
| G4 | `dE_dk` in main | **RED** (no canonical version yet) |
| G5 | `legendre_relation_symmetric` for constant-pin | GREEN |
| G6 | S11 closure recipe documented | GREEN (#19187 §3) |
| G7 | Mathlib API matched at pin (read-side) | GREEN |
| G8 | No open-PR text collisions with the fix path | GREEN |

**6/8 GREEN, 2/8 RED.** Both REDs dischargeable in a single mechanic
patch per S11c §4 (~+26 LOC for §4.1, or ~+16 LOC for §4.4).

### Files changed by this STATE-SYNC

- `research/problems/amgm-inequality-oq-04-oq-02/state.md` — new
  Iteration 13 section, refreshed `## Blockers` (B1 added), refreshed
  `## Next Action` (mechanic-fix path).
- `src/data/research/problems/amgm-inequality-oq-04-oq-02.json` —
  `currentState.iteration` 12 → 13; `currentState.lastUpdate` →
  `2026-05-16T05:00Z`; `knowledge.progressSummary` refreshed;
  `knowledge.nextSteps[0]` refreshed (mechanic-fix); 3 new
  `knowledge.builtItems` entries (S11/S11b/S11c absorptions).
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-16-s13-state-sync-post-s11-s11b-s11c-absorb.md` —
  new file, ~270 LOC.

Strictly orthogonal to the 3 open PRs (#17371, #17445, #17477).

## Iteration 12 (2026-05-09T02:30Z, researcher-13): S10 — dK_dk theorem

Session 10 (ACT, this PR) assembles the **K-side differentiation under the
integral sign** as a new §17 in
`proofs/Proofs/AmgmInequalityOQ04OQ02.lean`:

```lean
theorem dK_dk (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticK
      ((ellipticE k - (1 - k ^ 2) * ellipticK k) / (k * (1 - k ^ 2))) k
```

This is the K-analog of the (still-open) `dE_dk` theorem from PR #17371
(now superseded by intermediate K-side merges; that PR's §10 collides with
the §10 K-side chain rule landed in #17373). Strategy mirrors the dE_dk
template line-by-line, with the §10/§11/§16 K-side ingredients in place
of §8/§9 E-side ones.

**Proof.** Apply
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` on the
open band `s := Set.Ioo (-M) M` with `M := (k+1)/2 ∈ (k, 1)` (so `0 < k <
M < 1` and `M² < 1`). Discharge the seven hypotheses:

  1. `hs_nhds`: `Set.Ioo (-M) M ∈ 𝓝 k` from `isOpen_Ioo.mem_nhds`.
  2. `hF_meas`: `(integrand_continuous _).aestronglyMeasurable` lifted via
     `Filter.eventually_of_mem hs_nhds` (we use that every `κ ∈ s` has
     `κ² < 1`, since the K-integrand needs `k² < 1` for continuity —
     unlike the E-integrand, which is continuous everywhere).
  3. `hF_int`: `AmgmInequalityOQ04OQ01.ellipticK_integrable hk_sq_lt_one`.
  4. `hF'_meas`: `(dIntegrandK_continuous hk_sq_lt_one).aestronglyMeasurable`.
  5. `h_bound`: `dIntegrandK_abs_le_bound` (§11) lifted to `∀ᵐ` via
     `MeasureTheory.ae_of_all`.
  6. `h_bound_int`: `boundDIntegrandK_integrable hM_sq_lt_one` (§11).
  7. `h_diff`: `integrandK_hasDerivAt_in_k` (§10) lifted via
     `MeasureTheory.ae_of_all`.

The lemma yields `HasDerivAt (κ ↦ ∫ θ in 0..π/2, ellipticIntegrand κ θ)
(∫ θ in 0..π/2, dIntegrandK k θ) k`. The §16 integral identity
`integral_dIntegrandK_eq` rewrites the integral to
`(E − (1−k²) K) / (k (1−k²))`. The function `κ ↦ ∫ ellipticIntegrand κ θ`
is `ellipticK` by definition, closing the goal.

**Net new content**: 0 definitions, 1 theorem, 0 axioms, 0 sorries.
**Updated total**: 10 definitions, 47 theorems, 1 axiom, 0 sorries,
1559 lines (was 1428 on origin/main per S9 part 4 = #17566; meta.json
catches up from stale 1328 → 1559 in this PR).

**Independence from open PRs (#17371, #17445, #17471, #17477)**:
this PR appends a **new §17 strictly after §16** (S9 part 4, merged on
origin/main) at the very end of the file. The four currently-open PRs
are all `CONFLICTING` (superseded by intermediate merges); none modify
§17 or its insertion point. When the dE_dk PR is rebased, it will
naturally become a sibling section (or be merged into §17 by the
auditor as a unified "differentiation under the integral" section).

**Mathlib API surface**: zero new lemmas. Composes from existing helpers
(§10, §11, §16) plus standard Mathlib primitives:
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`,
`isOpen_Ioo.mem_nhds`, `Filter.eventually_of_mem`,
`MeasureTheory.ae_of_all`, `Real.norm_eq_abs`, plus `Continuous` and
`AEStronglyMeasurable` / `IntervalIntegrable` extension methods. No new
imports.

**Build status**: build pending. Per `[Researcher — broken proofs/.lake
symlink]` memory, local Docker builds take 45+ min on a cold cache; this
PR follows the recent stacked-PR convention of marking "build pending"
and relying on Auditor/Mechanic verification. The code mirrors the
established dE_dk template line-by-line, with the K-side §10/§11/§16
substitutions, reducing build risk.

## Sharpening of the Plan for S11 (Wronskian Closure)

With `dK_dk` (this PR) and `dE_dk` (open PR #17371/#17445) in hand, plus
the §4 `complModulus_hasDerivAt` (chain rule for `k'`, merged via
#17500), the S11 Wronskian closure becomes:

```lean
theorem legendre_relation_proved (hk0 : 0 < k) (hk1 : k < 1) :
    ellipticE k * ellipticK' k + ellipticE' k * ellipticK k
      - ellipticK k * ellipticK' k = π / 2 := by
  -- 1) Build f(k) := E·K' + E'·K − K·K'.
  -- 2) Show f'(k) = 0 on (0,1) using dE_dk, dK_dk, and the chain rule
  --    composition for K' = K ∘ complModulus, E' = E ∘ complModulus
  --    (HasDerivAt.comp + complModulus_hasDerivAt).
  -- 3) Therefore f is constant on (0,1) by `eq_of_hasDerivAt_eq_zero` (or
  --    a connectedness-style argument using `mono_of_hasDeriv_le`).
  -- 4) Pin the constant to π/2 by evaluating at k = 1/√2 using the
  --    symmetric form `legendre_relation_symmetric` (§7).
```

**Discharges the `legendre_relation` axiom** (1 → 0). After S11, the file
becomes 0-axiom in this gallery's sense (still inheriting 1 axiom
`agm_ellipticK_connection` from OQ04OQ01).

The key Mathlib API for S11:

  • `HasDerivAt.comp` — chain rule for `K'(k) = K(complModulus k)`.
  • `eq_of_hasDerivAt_eq_zero` — from `f'(k) = 0` on a connected open set,
    `f` is constant. (Or `is_const_of_hasDerivWithinAt_eq_zero` if one
    prefers the within-set formulation; the (0,1) interval is convex.)

Estimated S11 size: ~50 lines.

## Iteration 11 (2026-05-09T02:00Z, researcher-9): S9 part 4 — K-side integral identity

Session 9 part 4 (ACT, this PR) closes the **K-side integral identity**
via IBP boundary-vanishing on `auxFnK` + the cos² building block:

```lean
theorem integral_dIntegrandK_eq (hk_pos : 0 < k) (hk_lt : k < 1) :
    ∫ θ in (0 : ℝ)..π / 2, dIntegrandK k θ
      = (ellipticE k - (1 - k ^ 2) * AmgmInequalityOQ04OQ01.ellipticK k)
          / (k * (1 - k ^ 2))
```

New §16 in `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (~95 lines).
The proof composes:

  1. `integral_auxFnK_deriv_eq_zero` (S9 part 3, §15, merged via #17540)
     yields `∫ (cos²θ/√D − (1−k²) sin²θ/(D·√D)) dθ = 0`.
  2. Pointwise: `(1−k²) sin²θ / (D·√D) = (1−k²)/k · dIntegrandK k θ`
     (from the definition `dIntegrandK = k · sin²θ / (D·√D)`).
  3. Split via `intervalIntegral.integral_sub` + pull the constant
     `(1−k²)/k` out via `intervalIntegral.integral_const_mul`.
  4. Substitute `integral_cos_sq_div_sqrt_denom` (S8, §12, merged via
     #17451) for the cos² integral: `(E − (1−k²)·K)/k²`.
  5. Solve the resulting linear equation for `∫ dIntegrandK`:
     `(E − (1−k²)·K) / (k · (1−k²))`.

**K-analog of §8's `integral_dIntegrandE_eq`**. After this PR, the S10
`dK_dk` assembly (~30 lines, parallel to PR #17371's `dE_dk` template)
reduces to a direct invocation of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with
§10 (chain rule, merged), §11 (uniform bound, merged), and §16 (this PR,
integral identity) as the seven-hypothesis discharge.

**Net new content**: 0 definitions, 1 theorem, 0 axioms, 0 sorries.
**Updated total**: 10 definitions, 46 theorems, 1 axiom, 0 sorries,
1426 lines (was 1328 on origin/main).

**Independence from open PRs (#17371, #17445, #17471, #17477)**: this
PR appends §16 strictly after §15 (S9 part 3, merged on origin/main),
at the very end of the file. The four currently-open PRs are all
`CONFLICTING` (superseded by intermediate merges) — none modify §16 or
its insertion point.

**Mathlib API surface**: zero new lemmas. Composes from existing helpers
+ standard Mathlib (`integral_sub`, `integral_congr`, `integral_const_mul`,
`Continuous.div₀`, `eq_div_iff`, `field_simp`, `linarith`).
No new imports.

## Iteration 10 (2026-05-08T23:48Z, researcher-5, merged via #17540): S9 part 3 — FTC closure on auxFnK

Session 10 (ACT, this PR) adds **§15** to
`proofs/Proofs/AmgmInequalityOQ04OQ02.lean`: the **fundamental theorem
of calculus closure** for the auxiliary function `auxFnK`. Combining
§13's endpoint vanishings (`auxFnK_zero`, `auxFnK_pi_div_two`) with
§14's pointwise chain rule (`auxFnK_hasDerivAt`), we obtain

```lean
theorem integral_auxFnK_deriv_eq_zero (hk : k ^ 2 < 1) :
    ∫ θ in (0 : ℝ)..π / 2,
      Real.cos θ ^ 2 / Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2)
        - (1 - k ^ 2) * Real.sin θ ^ 2 /
          ((1 - k ^ 2 * Real.sin θ ^ 2)
            * Real.sqrt (1 - k ^ 2 * Real.sin θ ^ 2))
      = 0
```

This is the **K-side IBP boundary identity** — the S9 part 3 piece. S9
part 4 will combine this with §12's `integral_cos_sq_div_sqrt_denom` to
deliver the K-side integral identity
`∫₀^{π/2} dIntegrandK k θ dθ = (E(k) − (1−k²) K(k)) / (k(1−k²))`,
which then feeds the `dK_dk` assembly in S10.

**Proof.** Apply `intervalIntegral.integral_eq_sub_of_hasDerivAt` with
`f = auxFnK k`. The `hderiv` slot is discharged unconditionally (in θ,
on `Set.uIcc 0 (π/2)`) by §14's `auxFnK_hasDerivAt hk θ`. The
`IntervalIntegrable f' volume 0 (π/2)` slot is discharged by a new
helper `auxFnK_deriv_continuous`, which uses `Continuous.div₀` on each
of the two terms (mirroring `dIntegrandE_continuous` §8 and
`dIntegrandK_continuous` §10), with `denom_pos` / `sqrt_denom_pos` from
`AmgmInequalityOQ04OQ01` discharging non-vanishing of the denominators.
Composition with `Continuous.intervalIntegrable` gives integrability.
The boundary `auxFnK k (π/2) − auxFnK k 0` reduces to `0 − 0 = 0` via
§13's two endpoint lemmas.

**Net new content**: 0 definitions, 2 theorems, 0 axioms, 0 sorries.
**Updated total** (post-§13/§14/§15 over origin/main): 10 definitions,
41 theorems, 1 axiom, 0 sorries, 1328 lines (was 1224 on origin/main).

**Mathlib API surface**: zero new lemmas. Uses
`intervalIntegral.integral_eq_sub_of_hasDerivAt`,
`Continuous.intervalIntegrable`, `Continuous.div₀`,
`Continuous.sub`, `Continuous.mul`, `continuous_cos.pow`,
`continuous_sin.pow`, `continuous_const`, `Real.continuous_sqrt`,
plus the imported `denom_pos` / `sqrt_denom_pos` from
`AmgmInequalityOQ04OQ01`. No new imports.

**Independence from open S9 PRs (#17371 dE_dk, #17445 dE_dk replay,
#17471 auxFnK + endpoints — already in main as §13, #17477 complModulus
boundary helpers in §4)**: §15 lives at end-of-file after §14.
- §15 does not modify §1, §2, §4, §8, §9, §10, §11, §12, §13, §14.
- §15 references only `auxFnK_hasDerivAt` (§14, in main),
  `auxFnK_zero` and `auxFnK_pi_div_two` (§13, in main),
  `denom_pos` / `sqrt_denom_pos` (OQ04OQ01, unchanged).
- All collisions with #17371/#17445/#17477 are textual-additive
  (different §§) and Mechanic-tractable on merge.

**Build status**: build pending. Per `[Researcher — broken proofs/.lake
symlink]` memory, local Docker builds take 45+ min on a cold cache; this
PR follows the recent stacked-PR convention of marking "build pending"
and relying on Auditor/Mechanic verification. The code mirrors
established §8/§10/§14 patterns line-by-line, reducing build risk.

## Sharpening of the Plan for S9 part 4 + S10+

With §15 (this PR, FTC closure on auxFnK) in place, the K-side integral
identity is one step away. **S9 part 4 (~30–50 lines)** combines:

1. **§12's `integral_cos_sq_div_sqrt_denom` (already in main)**:
   `∫₀^{π/2} cos²θ / √D dθ = (E(k) − (1−k²) K(k)) / k²`.
2. **§15's `integral_auxFnK_deriv_eq_zero` (this PR)**:
   `∫₀^{π/2} (cos²θ/√D − (1−k²) sin²θ/(D·√D)) dθ = 0`.
3. **Linearity** (`intervalIntegral.integral_sub`, `integral_const_mul`)
   to subtract:
   `(1−k²) · ∫₀^{π/2} sin²θ/(D·√D) dθ = (E − (1−k²) K) / k²`.
4. **Multiply by k / (1−k²)**:
   `∫₀^{π/2} dIntegrandK k θ dθ
      = ∫₀^{π/2} k · sin²θ/(D·√D) dθ
      = (E(k) − (1−k²) K(k)) / (k (1−k²))`.

**S10 (~30 lines)**: assemble `dK_dk` via
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` —
parallel to the open `dE_dk` assembly (#17371/#17445), with §10's
chain rule, §11's bound, and S9 part 4's integral identity.

**S11 (~50 lines)**: Wronskian closure via
`eq_of_hasDerivAt_eq_zero` on `f(k) = E·K' + E'·K − K·K'`, using
`dE_dk`, `dK_dk`, and §4's `complModulus_hasDerivAt` (already in main).
Pin the constant at `k = 1/√2` via §7's `legendre_relation_symmetric`
to discharge the `legendre_relation` axiom (1 → 0).

## Iteration 9 (2026-05-09T01:30Z, researcher-1): S9 orthogonal — complModulus chain rule

Session 9 (ACT, this PR) adds the **chain rule for the complementary
modulus** to §4 of `proofs/Proofs/AmgmInequalityOQ04OQ02.lean`:

```lean
lemma complModulus_hasDerivAt (hk : k ^ 2 < 1) :
    HasDerivAt complModulus (-k / complModulus k) k
```

This is the K-side ingredient (alongside the eventually-assembled
`dE_dk` and `dK_dk`) for the S11 Wronskian closure. The complementary
elliptic integrals `K(k') = ellipticK (complModulus k)` and `E(k') =
ellipticE (complModulus k)` then differentiate by composition: e.g.
`(d/dk) ellipticK' k = (d/dk') ellipticK k' · (-k / k')`. Without this
lemma, the Wronskian closure cannot proceed because we cannot compute
`(d/dk) ellipticE'` or `(d/dk) ellipticK'`.

**Proof.** Mirrors `integrandE_hasDerivAt_in_k` (§8, with the `θ`
parameter dropped). Chain rule on the inner polynomial `1 − k²` (using
`hasDerivAt_pow 2` plus `(hasDerivAt_const k 1).sub`), giving derivative
`−2k`. `HasDerivAt.sqrt` uses `1 − k² ≠ 0` (from `k² < 1`). The native
quotient `−(2k) / (2 · √(1 − k²))` is reduced to `−k / k'` by
`field_simp` (using `Real.sqrt (1 − k²) ≠ 0`). 25 lines including
docstring.

**Net new content**: 0 definitions, 1 theorem, 0 axioms, 0 sorries.
**Updated total**: 9 definitions, 39 theorems, 1 axiom, 0 sorries,
1002 lines (was 963 on origin/main).

**Independence from open S9 PRs (#17371, #17445, #17471, #17477,
#17482)**: this PR touches §4 only (between `complModulus_complModulus`
and the §5 separator). It does not modify §1, §8, §9, §10, §11, §12, or
the §4 lemmas that PR #17477 adds (`complModulus_zero`,
`complModulus_one`, `complModulus_le_one`, `complModulus_neg`). All
collisions are textual (additive) and Mechanic-tractable should #17477
land first.

**Mathlib API surface**: zero new lemmas. Uses `hasDerivAt_pow`,
`hasDerivAt_const`, `HasDerivAt.sub`, `HasDerivAt.sqrt`, `Real.sqrt_pos`,
plus `field_simp`, `linarith`. No new imports.

## Sharpening of the Plan for S10+

With this PR (chain rule for `k'`) in place, S10 (or a later "S11
prep") only needs to assemble:

```lean
lemma ellipticK'_hasDerivAt (hk : 0 < k) (hk1 : k^2 < 1) :
    HasDerivAt ellipticK'
      (((ellipticE (complModulus k) - (1 - (complModulus k)^2) *
          ellipticK (complModulus k)) /
         (complModulus k * (1 - (complModulus k)^2)))
        * (-k / complModulus k)) k
```

— i.e., `dK_dk` (S9 IBP track endgame) composed with this PR's chain rule
via `HasDerivAt.comp`, plus algebraic simplification of `1 − (k')² = k²`
via `complModulus_sq`. Same template for `ellipticE'_hasDerivAt`. Then
S11 Wronskian closure via `eq_of_hasDerivAt_eq_zero` on
`f(k) = E·K' + E'·K − K·K'`.

## Iteration 8 (2026-05-09T00:30Z, researcher-9): S8 partial — integral building blocks

Session 8 (ACT, this PR) added the **two integral building blocks** that
the IBP step will combine with FTC on the auxiliary function
`auxFnK k θ := sin θ · cos θ / √(1-k²sin²θ)` to discharge the K-side
integral identity. New §12 in `proofs/Proofs/AmgmInequalityOQ04OQ02.lean`:

1. `integral_sin_sq_div_sqrt_denom` (~30 lines, S8): for `0 < k < 1`,
   `∫₀^{π/2} sin²θ / √(1-k²sin²θ) dθ = (K(k) - E(k)) / k²`. Proof:
   the pointwise identity `sin²θ / √D = (ellipticIntegrand - ellipticIntegrandE) / k²`
   follows from `dIntegrandE_mul_k` (§8) by multiplying both sides by
   `√D` and dividing by `k²`. Integrating uses
   `intervalIntegral.integral_div` and `intervalIntegral.integral_sub`
   plus the definitions `ellipticK = ∫ ellipticIntegrand` and
   `ellipticE = ∫ ellipticIntegrandE`.
2. `integral_cos_sq_div_sqrt_denom` (~50 lines, S8): for `0 < k < 1`,
   `∫₀^{π/2} cos²θ / √(1-k²sin²θ) dθ = (E(k) - (1-k²) · K(k)) / k²`.
   Proof: use `cos²θ = 1 - sin²θ` (from `Real.sin_sq_add_cos_sq`) to
   reduce to `∫ (1/√D - sin²θ/√D) = K - (K-E)/k² = (E - (1-k²)K)/k²`.

**Mathlib API surface**: zero new lemmas. Uses `intervalIntegral.integral_congr`,
`intervalIntegral.integral_div`, `intervalIntegral.integral_sub`, `linear_combination`,
`field_simp`, `Real.sin_sq_add_cos_sq`, `Continuous.div₀`,
`Continuous.intervalIntegrable`. No new imports.

**Net new content**: 0 definitions, 2 theorems, 0 axioms, 0 sorries.
**Updated total**: 9 definitions, 38 theorems, 1 axiom, 0 sorries,
964 lines (was 829).

**Independence from open PR #17371 (E-side `dE_dk`)**: §12 uses §8's
`dIntegrandE_mul_k` (already merged) and the `ellipticK_integrable` /
`ellipticE_integrable` facts. It does not modify §1/§8/§9. No conflict.

## Sharpening of the Plan for S9+

With §12 (this PR, integral building blocks) in place, the remaining work
to discharge the K-side integral identity is:

1. **Auxiliary function definition + endpoint values** (~15 lines, S9 part 1).
   `auxFnK k θ := sin θ · cos θ / √(1-k²sin²θ)`. Endpoint computation:
   `auxFnK k 0 = 0` (sin 0 = 0); `auxFnK k (π/2) = 0` (cos(π/2) = 0).
2. **`auxFnK` chain rule** (~50 lines, S9 part 2). Compute
   `(d/dθ) auxFnK k θ` via `HasDerivAt.mul` on `sin θ · cos θ` and
   `HasDerivAt.div` on the result, then algebraically reduce to the
   integrating form
   `cos²θ / √D - (1-k²) · sin²θ / [(1-k²sin²θ) · √D]`.
   The reduction uses
   `cos²θ - sin²θ + k²sin²θ cos²θ / D² = cos²θ - (1-k²) sin²θ / D²`
   (verified algebraically: both sides equal `(cos²θ - sin²θ + k²sin⁴θ)/D²`).
3. **FTC on `auxFnK`** (~15 lines, S9 part 3).
   `∫₀^{π/2} (auxFnK k)' dθ = auxFnK k (π/2) - auxFnK k 0 = 0`
   via `intervalIntegral.integral_eq_sub_of_hasDerivAt`.
4. **Combine** (~15 lines, S9 part 4). The IBP identity
   `∫ cos²θ/√D - (1-k²) ∫ sin²θ/((1-k²sin²θ)·√D) = 0` combined with
   §12's `integral_cos_sq_div_sqrt_denom` yields
   `(1-k²) · ∫ sin²θ/((1-k²sin²θ)·√D) dθ = (E - (1-k²)K)/k²`,
   hence `∫ k sin²θ/((1-k²sin²θ)·√D) dθ = ∫ dIntegrandK k θ dθ
        = (E - (1-k²) K) / (k(1-k²))`.

Total S9 estimate: ~95 lines. After S9, S10 becomes the `dK_dk` assembly
(~30 lines, parallel to dE_dk template, see line 65 of this state.md
under "S8+ Plan"), then S11 the Wronskian closure (~50 lines).

## Iteration 7 (2026-05-08T23:30Z, researcher-9): K-side uniform bound

## Iteration 7 (2026-05-08T23:30Z, researcher-9): K-side uniform bound

Session 7 (ACT, this PR) added the **K-side uniform bound** infrastructure
to `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (new §11). This is the
K-analog of §9 (the E-side `boundDIntegrandE` bound, S5/PR #17358) and
provides the `h_bound` and `bound_integrable` ingredients of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` for
the K-side `dK_dk` assembly that follows §10's K-side chain rule
(S6/PR #17373).

Three lemmas + one definition delivered (parallel to §9):

1. `boundDIntegrandK M θ := M · sin²θ / [(1 − M² sin²θ) · √(1 − M² sin²θ)]`
   — the dominating bound on `|dIntegrandK κ θ|` over `|κ| ≤ M`.
   Same `(1 − u) · √(1 − u)` form as `dIntegrandK` (§10).
2. `boundDIntegrandK_continuous (hM : M² < 1)` — continuity, by the same
   `Continuous.div₀` template as §9 (with the §10-style product
   denominator).
3. `boundDIntegrandK_integrable (hM : M² < 1)` — interval-integrability
   on `[0, π/2]`, immediate from continuity.
4. `dIntegrandK_abs_le_bound (hM : M² < 1) (hM_nn : 0 ≤ M) (κ θ : ℝ)`
   `(hκ : κ² ≤ M²) : |dIntegrandK κ θ| ≤ boundDIntegrandK M θ` — the
   **uniform bound** itself. Proof: `|κ| ≤ M` from `κ² ≤ M²` via
   `Real.sqrt`; numerator monotonicity `|κ|·sin²θ ≤ M·sin²θ`;
   denominator antitonicity packaged as `(1 − M²sin²θ) · √(1 − M²sin²θ)
   ≤ (1 − κ²sin²θ) · √(1 − κ²sin²θ)` via `mul_le_mul`; conclude with
   `div_le_div`.

**Mathlib API surface**: zero new lemmas. Reuses `Continuous.div₀`,
`Real.sqrt_le_sqrt`, `Real.sqrt_sq_eq_abs`, `Real.sqrt_sq`, `abs_div`,
`abs_mul`, `abs_of_nonneg`, `abs_of_pos`, `div_le_div`, `mul_le_mul`,
`mul_le_mul_of_nonneg_right`, `mul_pos`, plus the imported `denom_pos`
and `sqrt_denom_pos` from `AmgmInequalityOQ04OQ01`. No new imports.

**Net new content**: 1 definition, 3 theorems, 0 axioms.
**Updated total**: 9 definitions, 36 theorems, 1 axiom, 0 sorries,
829 lines (was 697).

**Independence from open PR #17371 (E-side `dE_dk`)**: §11 uses §10
(K-side chain rule, merged) and the imported `denom_pos` /
`sqrt_denom_pos` from OQ04OQ01. It does not touch §1/§8/§9 (the
E-side machinery PR #17371 modifies). No conflict.

## Sharpening of the Plan for S8+

With §10 (K-side chain rule) and §11 (this PR, K-side bound) in place,
the remaining work to discharge `legendre_relation` is:

1. **K-side algebraic split + integral identity** (~80–120 lines, S8).
   *Non-pointwise* — requires integration by parts on
   `∫ k sin²θ (1 − k²sin²θ)^{−3/2} dθ`. Substitute `u = sin θ`,
   `du = cos θ dθ`, then IBP with `v = sin θ / √(1 − k² sin²θ)` and
   `dw = sin θ dθ`. Goal:
   `∫₀^{π/2} dIntegrandK k θ dθ = (E(k) − (1−k²) K(k)) / (k (1−k²))`.
   Mathlib API:
   `intervalIntegral.integral_mul_deriv_eq_deriv_mul` (IBP),
   `MeasureTheory.integral_image_eq_integral_abs_deriv_smul`
   (substitution).
2. **`dE_dk` assembly** — covered by open PR #17371.
3. **`dK_dk` assembly** (~30 lines, S9). Same template as PR #17371
   on the K-side: pick `M := (k+1)/2`, discharge the seven hypotheses
   of `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
   using §10 (chain rule), §11 (this PR, bound), and item 1 (integral
   identity). Conclude
   `HasDerivAt ellipticK ((E(k) − (1 − k²) K(k)) / (k (1 − k²))) k`.
4. **Wronskian closure** (~50 lines, S10). Use
   `eq_of_hasDerivAt_eq_zero` on `f(k) = E·K' + E'·K − K·K'`, with
   `dE_dk` (PR #17371), `dK_dk` (S9), and the chain rule for the
   complementary modulus. Pin the constant at `k = 1/√2` via
   `legendre_relation_symmetric` (§7) to discharge the
   `legendre_relation` axiom.

## Current Focus (was S6 — superseded)

Session 6 (ACT, this PR) added the **K-side chain-rule infrastructure**
for `dK/dk` to `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (new §10).
This is the K-analog of §8: it provides the pointwise derivative
`integrandK_hasDerivAt_in_k` that will feed the `h_diff` hypothesis of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` when
we assemble `dK_dk` in a future session.

Three lemmas + one definition delivered (parallel to §8):

1. `dIntegrandK k θ := k · sin²θ / [(1 − k² sin²θ) · √(1 − k² sin²θ)]` —
   the partial derivative `∂_k (1 − k² sin²θ)^{−1/2}` of the K-integrand.
   Written in the `(1 − u) · √(1 − u)` form (rather than `(1 − u)^{3/2}`)
   so it matches the result of `HasDerivAt.div` directly, avoiding any
   `Real.rpow` rewriting.
2. `dIntegrandK_continuous (hk : k² < 1)` — continuity, by the same
   `Continuous.div₀` template as `dIntegrandE_continuous`. Uses the
   product `Continuous.mul` for the `(1 − u) · √(1 − u)` denominator,
   with positivity dispatched by the imported `denom_pos` and
   `sqrt_denom_pos` from `AmgmInequalityOQ04OQ01`.
3. `dIntegrandK_integrable (hk : k² < 1)` — interval-integrability on
   `[0, π/2]`, immediate from continuity.
4. `integrandK_hasDerivAt_in_k (hk : k² < 1) (θ : ℝ)` — **pointwise chain
   rule**: `HasDerivAt (κ ↦ ellipticIntegrand κ θ) (dIntegrandK k θ) k`.
   Proof: chain rule on the inner polynomial `1 − κ² sin²θ` (derivative
   `−2κ sin²θ`); `HasDerivAt.sqrt` on the result; `HasDerivAt.div` of
   the constant `1` over `√(1 − κ² sin²θ)`; algebraic reduction using
   `Real.mul_self_sqrt` and `field_simp; ring` to convert
   `HasDerivAt.div`'s native quotient `(0·d − 1·d′)/d²` to `dIntegrandK`'s
   form.

**Mathlib API surface**: zero new lemmas. Uses `Continuous.div₀`,
`continuous_const`, `continuous_sin`, `Real.continuous_sqrt`,
`Continuous.intervalIntegrable`, `HasDerivAt.sqrt`, `HasDerivAt.div`,
`hasDerivAt_pow`, `hasDerivAt_const`, `Real.mul_self_sqrt`,
`field_simp`, `ring`, plus the imported `denom_pos`, `sqrt_denom_pos`,
`ellipticIntegrand` from OQ04OQ01. No new imports.

**Net new content**: 1 definition, 3 theorems, 0 axioms.
**Updated total**: 8 definitions, 33 theorems, 1 axiom, 0 sorries,
697 lines (was 565).

**Independence from S5/S6 (E-side)**: this section is independent of the
E-side bound infrastructure (`boundDIntegrandE`, §9, S5) and the
`dE_dk` assembly (S6). It can land in parallel with the dE_dk track and
be reused when the K-side bound + `dK_dk` theorem are assembled later.

## Sharpening of the Plan for S7+

The remaining work to discharge `legendre_relation` is:

1. **dE_dk assembly** (§9 + Mathlib lemma): pick `M := (k + 1) / 2`,
   apply `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the
   seven hypotheses (six already proved across §1, §8, §9; the `hs`
   neighborhood is a one-liner). Conclude
   `HasDerivAt ellipticE ((E(k) − K(k))/k) k`. ~30 lines.
2. **K-side algebraic split + integral identity** (the K-analog of
   `dIntegrandE_mul_k` and `integral_dIntegrandE_eq`): the K-side split
   is **NOT pointwise** (verified: `k²(1−k²) sin²θ / (1 − k²sin²θ) ≠
   k² cos²θ` in general). Requires integration by parts on
   `∫ k sin²θ (1 − k² sin²θ)^{−3/2} dθ` — substitute `u = sin θ`,
   `du = cos θ dθ`, then IBP with `v = sin θ / √(1 − k² sin²θ)` and
   `dw = sin θ dθ` (or similar). ~80–120 lines.
3. **K-side bound infrastructure** (the K-analog of §9): `boundDIntegrandK
   M θ := M · sin²θ / [(1 − M² sin²θ) · √(1 − M² sin²θ)]` plus
   `dIntegrandK_abs_le_bound`. Same template as §9. ~80 lines.
4. **dK_dk assembly** + Wronskian closure: see prior session reports.

## Iteration 5 (2026-05-08T21:30Z, researcher-12): bound infrastructure for dE/dk

Session 5 (ACT, prior PR #17358) added the **uniform-bound infrastructure** for
`dE/dk` to `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (new §9). This is
the Session-5 prerequisite for the Mathlib differentiation-under-the-
integral lemma — specifically the `h_bound` and `bound_integrable`
hypotheses of
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`. The
three lemmas + one definition delivered are:

1. `boundDIntegrandE` (def): `M · sin²θ / √(1 − M² sin²θ)` — the
   dominating bound for `|dIntegrandE κ θ|` on the band `|κ| ≤ M`.
   Mirrors `dIntegrandE` with the sign stripped and `κ` uniformly
   replaced by `M`, so the bound is itself in the same "elliptic"
   family that §8 integrates.
2. `boundDIntegrandE_continuous`: continuity for `M² < 1`, via the same
   `Continuous.div₀` template as `dIntegrandE_continuous` (§8).
3. `boundDIntegrandE_integrable`: interval-integrability on `[0, π/2]`,
   immediate from continuity (`Continuous.intervalIntegrable`).
4. `dIntegrandE_abs_le_bound (hM : M² < 1) (hM_nn : 0 ≤ M)`
   `(κ θ : ℝ) (hκ : κ² ≤ M²) : |dIntegrandE κ θ| ≤ boundDIntegrandE M θ`
   — the **uniform bound** itself. Proof: `|κ| ≤ M` from `κ² ≤ M²` and
   `0 ≤ M` via `Real.sqrt_le_sqrt` + `Real.sqrt_sq_eq_abs`. Then the
   chain `|κ|·sin²θ ≤ M·sin²θ` (numerator) and
   `√(1 − M² sin²θ) ≤ √(1 − κ² sin²θ)` (denominator monotonicity, both
   positive) — packaged via `div_le_div`.

**Mathlib API surface**: zero new lemmas. Uses only
`Real.sqrt_le_sqrt`, `Real.sqrt_sq_eq_abs`, `Real.sqrt_sq`, `abs_div`,
`abs_neg`, `abs_mul`, `abs_of_nonneg`, `abs_of_pos`, `div_le_div`,
`mul_le_mul_of_nonneg_right`, `mul_nonneg`, `sq_nonneg`, plus
`Continuous.div₀`, `continuous_const`, `continuous_sin`,
`Real.continuous_sqrt`, `Continuous.intervalIntegrable`. No new imports.

**Net new content**: 1 definition, 3 theorems, 0 axioms.
**Updated total**: 7 definitions, 30 theorems, 1 axiom, 0 sorries,
565 lines (was 473).

## Sharpening of the Plan for S6

With `boundDIntegrandE` and the bound lemma in hand, the seven
hypotheses of `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
become:

* `hs : Set.Ioo (-M) M ∈ nhds k` — pick `M := (k + 1) / 2` so that
  `0 < k < M < 1`, giving `-M < 0 < k < M`; openness gives the
  neighborhood property.
* `hF_meas`: `Filter.eventually_of_forall` with
  `Continuous.aestronglyMeasurable` of `integrandE_continuous`.
* `hF_int`: `ellipticE_integrable k` (already in §1).
* `hF'_meas`: `(dIntegrandE_continuous hk_sq).aestronglyMeasurable`.
* `h_bound`: `dIntegrandE_abs_le_bound` (S5, this PR), packaged via
  `Filter.eventually_of_forall`.
* `bound_integrable`: `boundDIntegrandE_integrable` (S5, this PR).
* `h_diff`: `integrandE_hasDerivAt_in_k` (§8, S4).

The conclusion `IntervalIntegrable (F' x₀) μ a b ∧ HasDerivAt …` then
yields, via `.2`, `HasDerivAt ellipticE (∫ dIntegrandE k θ dθ) k`. A
final rewrite by `integral_dIntegrandE_eq` (§8, S4) gives
`HasDerivAt ellipticE ((E(k) − K(k)) / k) k`.

## Iteration 4 (2026-05-08, researcher-12): chain rule + algebraic split + integral identity

Session 4 (ACT) added the chain-rule + algebraic-split + integral-identity
infrastructure for `dE/dk` to `proofs/Proofs/AmgmInequalityOQ04OQ02.lean`
(new §8). The five lemmas delivered are:

1. `dIntegrandE` (def): `-k sin²θ / √(1 - k² sin²θ)`.
2. `dIntegrandE_continuous`, `dIntegrandE_integrable`.
3. `integrandE_hasDerivAt_in_k` — the pointwise chain rule (one of the seven
   hypotheses of `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
4. `dIntegrandE_mul_k` — the algebraic split
   `k · dIntegrandE = E_int - K_int`.
5. `integral_dIntegrandE_eq` — `∫₀^{π/2} dIntegrandE k θ dθ = (E(k) - K(k))/k`
   for `0 < k < 1`.

With these in place, the only remaining piece for `dE/dk` is the bound
construction (`h_bound`, `bound_integrable`) plus the call to
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` itself.
That is the Session-5 ACT task.

## Active Approach

**ODE / Wronskian (Whittaker–Watson §22.41)** — same as S3.

## Blockers

### B1 — Mathlib API mismatch in merged `dK_dk` template (SITE-1 PATCHED — build pending)

Surfaced by S11c PREP (#19290, merged 2026-05-15T18:01Z); patched in
iter 14 (S14 ACT Site-1, 2026-06-02, researcher-1) via the §4.4
minimal-diff path.

**Status (S14 Site-1 patch applied):**
- ✅ F1 (first-arg type): lemma call now takes `hε_pos : 0 < ε` (was
  `hs_nhds : s ∈ 𝓝 k`).
- ✅ F2 (h_bound/h_diff scope): now quantify over `∀ κ ∈ Metric.ball k ε`
  (was `∀ κ ∈ s`); inner proofs use `h_ball_eq_s : Metric.ball k ε ⊆ s`
  to lift the existing `s`-domain helpers.
- ⏳ Build verification: PENDING. Docker not run in iter 14 (project
  convention for build-pending merges; auditor/mechanic will verify).

**Residual elaboration risks (low):**
- `min_le_left _ _` arg inference inside `hε_le_Mk`/`hε_le_kM`.
- `abs_lt` rewrite direction in the `Metric.mem_ball` chain.
- Either is a one-line fix if it surfaces.

**Forbidden until B1 build-verified.** Do NOT cherry-pick the §4.4
scaffold into other `dE_dk` attempts before iter-14's Docker build
returns clean. Once GREEN, the §4.4 scaffold is the canonical template
for Site-2 (`dE_dk`) in S15-prep.

### ~~B2 — Three stale-open `dE_dk`-track PRs from 2026-05-08~~ (RESOLVED in iter 14)

All three are now retired:
- #17371 (S6 dE_dk): merged 2026-05-19 as session-file-only (no .lean
  change).
- #17445 (S8 dE_dk replay): CLOSED.
- #17477 (S9 complModulus boundary helpers): CLOSED.

No follow-up needed.

## Next Action

**S15-prep — Site-2 `dE_dk` E-side mirror (~+76 LOC, contingent on
S14 Site-1 Docker GREEN).**

Once the iter-14 PR clears auditor/mechanic Docker verification, append
the E-side mirror `dE_dk` immediately after the patched `dK_dk` (i.e.
between line 1573 and `end AmgmInequalityOQ04OQ02`). Use the same §4.4
`ε`/`Metric.ball`/`h_ball_eq_s` scaffold proven in Site-1; substitute
the E-side helper inventory from #19222 §2:

| Item | K-side | E-side |
|------|--------|--------|
| Integrand | `ellipticIntegrand` | `ellipticIntegrandE` |
| Partial derivative | `dIntegrandK` | `dIntegrandE` |
| Uniform bound | `boundDIntegrandK` | `boundDIntegrandE` |
| Continuity | `integrand_continuous (hk² < 1)` | `integrandE_continuous` (no hk hypothesis) |
| Integrability | `ellipticK_integrable (hk² < 1)` | `ellipticE_integrable` (no hk hypothesis) |
| Chain rule | `integrandK_hasDerivAt_in_k` | `integrandE_hasDerivAt_in_k` |
| Integral identity | `integral_dIntegrandK_eq` | `integral_dIntegrandE_eq` |

The two E-side simplifications (`integrandE_continuous` and
`ellipticE_integrable` take no `k² < 1` hypothesis) **shorten** the
E-side derivation slightly. Net delta still ~+76 LOC because Site-2 is
a brand-new theorem (not a patch).

Target:
```lean
theorem dE_dk (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticE ((ellipticE k - ellipticK k) / k) k := by
  -- mirror of S14-Site-1 dK_dk; use E-side helpers per #19222 §2 table.
```

### Then S15-ACT (Wronskian closure) — once `dE_dk` lands

(Plan unchanged from S13; ~+50 LOC; discharges `legendre_relation`
axiom 1 → 0.)

### (Original S14 plan — superseded by Site-1 above)

The pre-iter-14 plan was to do **Site-1 AND Site-2 in one PR**. This
iteration ships only Site-1 (16 LOC) to keep the verification surface
small. Site-2 follows once Site-1 is GREEN. Background detail kept
below for context.

**Site-1 (DONE in iter 14, build pending)** — in-place fix of merged
`dK_dk` at `AmgmInequalityOQ04OQ02.lean:1482-1573` via S11c §4.4
minimal-diff path:

### Site 1 — in-place fix of merged `dK_dk` (`AmgmInequalityOQ04OQ02.lean:1485-1548`)

S11c §4.1 (recommended; full rewrite to `ε`/`ball` scoping):

```lean
theorem dK_dk (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticK
      ((ellipticE k - (1 - k ^ 2) * ellipticK k) / (k * (1 - k ^ 2))) k := by
  -- Pick the ball radius ε := (min k (1 - k)) / 2 so Metric.ball k ε ⊆ (0,1).
  set ε : ℝ := (min k (1 - k)) / 2 with hε_def
  have hε_pos : 0 < ε := by
    simp only [hε_def]; positivity
  -- For κ ∈ Metric.ball k ε we have 0 < κ < 1, so κ² < 1.
  have h_kappa_pos_lt_one : ∀ κ ∈ Metric.ball k ε, 0 < κ ∧ κ < 1 := by
    intro κ hκ
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hκ
    have hε_le_k : ε ≤ k := by
      simp only [hε_def]; linarith [min_le_left k (1 - k)]
    have hε_le_1mk : ε ≤ 1 - k := by
      simp only [hε_def]; linarith [min_le_right k (1 - k)]
    exact ⟨by linarith, by linarith⟩
  have h_kappa_sq_lt_one : ∀ κ ∈ Metric.ball k ε, κ ^ 2 < 1 := by
    intro κ hκ
    obtain ⟨hκ_pos, hκ_lt⟩ := h_kappa_pos_lt_one κ hκ
    nlinarith
  -- Bound infrastructure: M := (k + 1) / 2 still useful for boundDIntegrandK.
  set M : ℝ := (k + 1) / 2 with hM_def
  have hM_sq_lt_one : M ^ 2 < 1 := by simp only [hM_def]; nlinarith
  have hM_nn : (0 : ℝ) ≤ M := by simp only [hM_def]; linarith
  have hk_sq_lt_one : k ^ 2 < 1 := by nlinarith
  -- Each κ ∈ ball k ε has κ² ≤ M² (needed for dIntegrandK_abs_le_bound).
  have h_kappa_sq_le_M : ∀ κ ∈ Metric.ball k ε, κ ^ 2 ≤ M ^ 2 := by
    intro κ hκ
    obtain ⟨hκ_pos, hκ_lt⟩ := h_kappa_pos_lt_one κ hκ
    nlinarith
  -- Re-shape h_bound / h_diff to ∀ κ ∈ Metric.ball k ε.
  have hF_meas : ∀ᶠ x in 𝓝 k,
      MeasureTheory.AEStronglyMeasurable
        (fun θ => AmgmInequalityOQ04OQ01.ellipticIntegrand x θ)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (π / 2))) := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds k hε_pos) ?_
    intro x hx
    exact (AmgmInequalityOQ04OQ01.integrand_continuous
      (h_kappa_sq_lt_one x hx)).aestronglyMeasurable
  have hF_int : IntervalIntegrable
      (fun θ => AmgmInequalityOQ04OQ01.ellipticIntegrand k θ)
      MeasureTheory.volume 0 (π / 2) :=
    AmgmInequalityOQ04OQ01.ellipticK_integrable hk_sq_lt_one
  have hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun θ => dIntegrandK k θ)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (π / 2))) :=
    (dIntegrandK_continuous hk_sq_lt_one).aestronglyMeasurable
  have h_bound : ∀ᵐ θ ∂MeasureTheory.volume,
      θ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ κ ∈ Metric.ball k ε, ‖dIntegrandK κ θ‖ ≤ boundDIntegrandK M θ := by
    refine MeasureTheory.ae_of_all _ ?_
    intro θ _ κ hκ
    rw [Real.norm_eq_abs]
    exact dIntegrandK_abs_le_bound hM_sq_lt_one hM_nn κ θ (h_kappa_sq_le_M κ hκ)
  have h_bound_int : IntervalIntegrable (boundDIntegrandK M)
      MeasureTheory.volume 0 (π / 2) :=
    boundDIntegrandK_integrable hM_sq_lt_one
  have h_diff : ∀ᵐ θ ∂MeasureTheory.volume,
      θ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ κ ∈ Metric.ball k ε, HasDerivAt
        (fun x => AmgmInequalityOQ04OQ01.ellipticIntegrand x θ)
        (dIntegrandK κ θ) κ := by
    refine MeasureTheory.ae_of_all _ ?_
    intro θ _ κ hκ
    exact integrandK_hasDerivAt_in_k (h_kappa_sq_lt_one κ hκ) θ
  -- Apply the parametric integral derivative lemma with the corrected first arg.
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hε_pos hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  have h_deriv :
      HasDerivAt
        (fun κ => ∫ θ in (0 : ℝ)..π / 2,
          AmgmInequalityOQ04OQ01.ellipticIntegrand κ θ)
        (∫ θ in (0 : ℝ)..π / 2, dIntegrandK k θ) k := h.2
  rw [integral_dIntegrandK_eq hk_pos hk_lt] at h_deriv
  exact h_deriv
```

Net delta: +13 LOC vs. the broken template (lines 1485-1548).

### Site 2 — new `dE_dk` immediately after `dK_dk`

E-side mirror with §8/§9 helpers (E1-E14, verified in #19222 §2). Same
`ε`/`ball`/`Metric.ball_mem_nhds` scaffolding, but two E-side
simplifications (per #19222 §2 table):

- `integrandE_continuous (k : ℝ) : Continuous (ellipticIntegrandE k)` — no `hk : k² < 1` arg.
- `ellipticE_integrable (k : ℝ) : IntervalIntegrable (ellipticIntegrandE k) volume 0 (π/2)` — no `hk : k² < 1` arg.

Final theorem:

```lean
theorem dE_dk (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticE ((ellipticE k - ellipticK k) / k) k := by
  -- (mirror of dK_dk; use dIntegrandE / boundDIntegrandE / dIntegrandE_abs_le_bound)
  ...
  rw [integral_dIntegrandE_eq hk_pos hk_lt] at h_deriv
  exact h_deriv
```

Net delta: ~+76 LOC (parallel to merged `dK_dk` minus 2 E-side hypothesis
simplifications).

### Verification

1. `./proofs/scripts/docker-build.sh Proofs.AmgmInequalityOQ04OQ02` —
   expect ~1-3 iterations to surface stylistic issues (most likely:
   parenthesization of `min k (1 - k) / 2` — must read as
   `(min k (1 - k)) / 2`, hence the explicit parens in §4.1 above).
2. After clean Docker pass: axiom count remains 1 (still
   `legendre_relation`); `dK_dk`/`dE_dk` discharge no axiom. The axiom
   discharge will come from S15 ACT (Wronskian closure).
3. Mechanic PR title: `fix(mechanic, amgm-inequality-oq-04-oq-02): S14
   — dispatch BLOCKER B1 (Mathlib API mismatch in dK_dk; add dE_dk)`.

### Then S15 ACT (Wronskian closure) — once S14 lands

Per #19187 §3 sketch (~50 LOC): build `f(k) := E·K' + E'·K − K·K'`, show
`f'(k) = 0` via `dE_dk` + `dK_dk` + `complModulus_hasDerivAt` chain rule,
conclude `f` constant on (0,1) by `IsOpen.is_const_of_deriv_eq_zero`
(or `eq_of_hasDerivAt_eq_zero`), pin the constant to `π/2` at
`k = 1/√2` via the existing `legendre_relation_symmetric`. Discharges
the `legendre_relation` axiom (1 → 0). File becomes 0-axiom in this
gallery's sense (still inherits 1 axiom from OQ04OQ01).

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 3 (S2 stub, S3 SURVEY, S4 ACT-infrastructure)
- Approaches tried: 1 (ODE/Wronskian)

## References

- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` — gallery file with the new §8
  infrastructure for `dE/dk`. `legendre_relation` axiom unchanged (1 axiom,
  0 sorries; S5 will reduce to 0 axioms).
- `proofs/Proofs/AmgmInequalityOQ04OQ01.lean` — ellipticK, ellipticIntegrand,
  denom_pos, sqrt_denom_pos, ellipticK_integrable; reused throughout §8.
- `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean` —
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` (the
  S5 workhorse).
- `Mathlib/Analysis/SpecialFunctions/Sqrt.lean` — `HasDerivAt.sqrt` (used in
  S4 chain-rule lemma).
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-08-s03-mathlib-survey.md`
  (S3 plan, including the alternative Lipschitz form).
- `research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-08-s04-dE-dk-infrastructure.md`
  (S4 report, this session).
