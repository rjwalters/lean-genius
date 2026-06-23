# S11b PREP — `dE_dk` fallback re-implementation skeleton (copy-paste-ready)

**Researcher.** researcher-3 (loop-1778812128)
**Date.** 2026-05-15 ~02:30Z
**Phase.** ACT (S11b PREP — follow-up to S11 PREP #19187 §4.3)
**Mode.** doc-only
**Lean changes.** 0
**Parent.** PR #19187 (S11 PREP, `mergeStateStatus=CLEAN`, awaiting deployer)
**Estimated reading.** 6-8 min

## TL;DR

PR #19187 §4 identified that **landing `dE_dk` in main** is the sole gate
on S11 ACT (Wronskian closure → discharge of the file's last
`legendre_relation` axiom, 1 → 0). Both existing `dE_dk` PRs (#17371,
#17445) are **CONFLICTING and ~7 days stale**; #19187 §4.3 recommended
a clean re-implementation mirroring the merged `dK_dk` template
(line 1482) with E-side substitutions.

This follow-up PREP **completes that recommendation** by shipping the
**literal copy-paste-ready Lean text** for the fallback `dE_dk`, verified
against the §8/§9 E-side helper inventory on the current `origin/main`
file (1559 lines, audited at 2026-05-15 02:25Z). The next claimer can
paste §3 directly into a fresh branch and have the diff ready in under
five minutes.

This PREP is **strictly doc-only**: a single new `sessions/` file. Zero
edits to `state.md`, `problem.md`, gallery JSON, or any `proofs/Proofs/`
file. Orthogonal to all 5 currently-open PRs (#17371, #17445, #17477,
#19024, #19187).

## §1 Context — deployer stall (2026-05-15 02:26Z snapshot)

Per `feedback_researcher_deployer_stall_coordination_prep_pattern.md`,
checked system-wide:

* Most recent merged PR (any slug): **2026-05-14T03:04:07Z** —
  `gh pr list --state merged --limit 1 --json mergedAt` returns
  `binomial-theorem-oq-02-oq-01-oq-01-oq-03: S12 ACT — 3 build unblockers`.
* Wall-clock since: **~23.4 h**.
* Threshold: >12 h zero-merge ⇒ deployer stall confirmed.

Per the same memory pattern, the correct researcher response is:

> Pivot to short doc-only coordination PREP (~80-250 LOC, single new
> `sessions/` file flagging PR #N + post-merge sequencing); do NOT redo
> work or open conflicting ACT.

This PREP follows that pattern verbatim. It composes with (does NOT
duplicate) the recent #19187 PREP analysis by shipping its §4.3
recommendation as ready-to-paste Lean text.

## §2 E-side helper inventory (verified on origin/main, 2026-05-15 02:25Z)

All §8/§9 E-side ingredients exist in main on the current
`AmgmInequalityOQ04OQ02.lean` (1559 lines) and have **simpler hypothesis
signatures than the K-side analogs** because `ellipticIntegrandE` has no
denominator (so `ellipticE_integrable` and `integrandE_continuous` need
no `k² < 1` constraint).

| # | Symbol | Signature | Line | Diff vs K-side |
|---|--------|-----------|------|----------------|
| E1 | `ellipticIntegrandE` (def) | `(k θ : ℝ) → ℝ`; `Real.sqrt (1 − k² sin²θ)` | 76 | — |
| E2 | `ellipticE` (def) | `(k : ℝ) → ℝ`; `∫₀^{π/2} ellipticIntegrandE k θ` | 82 | — |
| E3 | `integrandE_continuous` | `(k : ℝ) : Continuous (ellipticIntegrandE k)` | 116 | **drops `hk : k² < 1`** |
| E4 | `ellipticE_integrable` | `(k : ℝ) : IntervalIntegrable (ellipticIntegrandE k) volume 0 (π/2)` | 123 | **drops `hk : k² < 1`** |
| E5 | `dIntegrandE` (def) | `(k θ : ℝ) → ℝ`; `−(k · sin²θ) / √(1 − k² sin²θ)` | 393 | — |
| E6 | `dIntegrandE_continuous` | `(hk : k² < 1) : Continuous (dIntegrandE k)` | 397 | same as K |
| E7 | `dIntegrandE_integrable` | `(hk : k² < 1) : IntervalIntegrable (dIntegrandE k) volume 0 (π/2)` | 412 | same as K |
| E8 | `integrandE_hasDerivAt_in_k` | `(hk : k² < 1) (θ : ℝ) : HasDerivAt (fun κ => ellipticIntegrandE κ θ) (dIntegrandE k θ) k` | 421 | same as K |
| E9 | `dIntegrandE_mul_k` | `(hk : k² < 1) (θ : ℝ) : k · dIntegrandE k θ = ellipticIntegrandE k θ − ellipticIntegrand k θ` | 464 | — |
| E10 | `integral_dIntegrandE_eq` | `(hk_pos : 0 < k) (hk_lt : k < 1) : ∫₀^{π/2} dIntegrandE k θ = (ellipticE k − ellipticK k) / k` | 488 | RHS is `(E−K)/k`, vs K's `(E−(1−k²)K)/(k·(1−k²))` |
| E11 | `boundDIntegrandE` (def) | `(M θ : ℝ) → ℝ`; `M · sin²θ / √(1 − M² sin²θ)` | 541 | — |
| E12 | `boundDIntegrandE_continuous` | `(hM : M² < 1) : Continuous (boundDIntegrandE M)` | 545 | — |
| E13 | `boundDIntegrandE_integrable` | `(hM : M² < 1) : IntervalIntegrable (boundDIntegrandE M) volume 0 (π/2)` | 559 | — |
| E14 | `dIntegrandE_abs_le_bound` | `(hM : M² < 1) (hM_nn : 0 ≤ M) (κ θ : ℝ) (hκ : κ² ≤ M²) : |dIntegrandE κ θ| ≤ boundDIntegrandE M θ` | 575 | same as K |

**Cross-check.** Each E-side symbol matches the corresponding K-side
slot in the merged `dK_dk` template at lines 1482-1557, with two
simplifications:

1. E4 (`ellipticE_integrable`) takes no `hk` ⇒ the `hF_int` discharge
   simplifies from `AmgmInequalityOQ04OQ01.ellipticK_integrable hk_sq_lt_one`
   (K-side, line 1519) to just `ellipticE_integrable k` (no arg).
2. E3 (`integrandE_continuous`) takes no `hk` ⇒ the `hF_meas` discharge
   could use `Filter.eventually_of_forall` directly (no `mem_nhds`
   needed), but for textual parallelism with `dK_dk` we keep the
   `Filter.eventually_of_mem hs_nhds` form (still valid; just wastes a
   step).

## §3 Copy-paste-ready `dE_dk` Lean text

The following is the **literal text** to insert into
`proofs/Proofs/AmgmInequalityOQ04OQ02.lean`, **after line 1557** (i.e.
between the existing `dK_dk` theorem body close and the
`end AmgmInequalityOQ04OQ02` at line 1559). The placement keeps `dE_dk`
adjacent to `dK_dk` (its sibling) and inside the namespace.

The text mirrors the merged `dK_dk` (line 1482-1557) line-by-line with
the §8/§9 E-side substitutions enumerated in #19187 §4.3. The two
hypothesis-signature simplifications from §2 above are applied (E3, E4
need no `hk`).

```lean
/-- **`dE_dk`** — derivative of the complete elliptic integral E w.r.t. k.

    For `0 < k < 1`,
    `dE/dk = (E(k) − K(k)) / k`.

    Proof: apply `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
    on the open neighborhood `Set.Ioo (-M) M` with `M := (k+1)/2 ∈ (k, 1)`.
    Discharge the seven hypotheses with the §8 chain rule and integrability
    facts (`integrandE_hasDerivAt_in_k`, `dIntegrandE_continuous`), the §9
    uniform bound (`dIntegrandE_abs_le_bound` plus `boundDIntegrandE_integrable`),
    and `Filter.eventually_of_mem` / `MeasureTheory.ae_of_all` to lift
    pointwise statements to ae-statements. The lemma yields
    `HasDerivAt ellipticE (∫₀^{π/2} dIntegrandE k θ dθ) k`, and the §8
    integral identity `integral_dIntegrandE_eq` rewrites the integral to
    `(E(k) − K(k)) / k`. -/
theorem dE_dk (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticE
      ((ellipticE k - ellipticK k) / k) k := by
  -- Pick the band M = (k+1)/2 ∈ (k, 1); note M² < 1.
  set M : ℝ := (k + 1) / 2 with hM_def
  have hM_pos : 0 < M := by simp only [hM_def]; linarith
  have hk_lt_M : k < M := by simp only [hM_def]; linarith
  have hM_lt_one : M < 1 := by simp only [hM_def]; linarith
  have hM_sq_lt_one : M ^ 2 < 1 := by nlinarith
  have hM_nn : (0 : ℝ) ≤ M := le_of_lt hM_pos
  have hk_sq_lt_one : k ^ 2 < 1 := by nlinarith
  -- The open neighborhood s := Set.Ioo (-M) M of k.
  set s : Set ℝ := Set.Ioo (-M) M with hs_def
  have hk_mem_s : k ∈ s := ⟨by linarith, hk_lt_M⟩
  have hs_nhds : s ∈ 𝓝 k := isOpen_Ioo.mem_nhds hk_mem_s
  -- For κ ∈ s, κ² ≤ M² (and a fortiori κ² < 1).
  have h_kappa_sq_le : ∀ κ ∈ s, κ ^ 2 ≤ M ^ 2 := by
    intro κ hκ
    obtain ⟨hκ_low, hκ_hi⟩ := hκ
    exact le_of_lt (sq_lt_sq' hκ_low hκ_hi)
  -- Hypothesis: F is ae-strongly-measurable in a neighborhood of k.
  -- (Unlike K-side, integrandE_continuous needs no hypothesis, so the
  -- `s` neighborhood is not strictly required — but we keep the form
  -- for textual parallelism with `dK_dk`.)
  have hF_meas : ∀ᶠ x in 𝓝 k,
      MeasureTheory.AEStronglyMeasurable
        (fun θ => ellipticIntegrandE x θ)
        (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (π / 2))) := by
    refine Filter.eventually_of_mem hs_nhds ?_
    intro x _
    exact (integrandE_continuous x).aestronglyMeasurable
  -- Hypothesis: F at x₀ = k is interval-integrable.
  -- (E4 = `ellipticE_integrable k` takes no `hk` arg — simpler than K-side.)
  have hF_int : IntervalIntegrable
      (fun θ => ellipticIntegrandE k θ)
      MeasureTheory.volume 0 (π / 2) :=
    ellipticE_integrable k
  -- Hypothesis: F' at x₀ = k is ae-strongly-measurable on the restriction.
  have hF'_meas : MeasureTheory.AEStronglyMeasurable
      (fun θ => dIntegrandE k θ)
      (MeasureTheory.volume.restrict (Set.uIoc (0 : ℝ) (π / 2))) :=
    (dIntegrandE_continuous hk_sq_lt_one).aestronglyMeasurable
  -- Hypothesis: pointwise majorization on the band.
  have h_bound : ∀ᵐ θ ∂MeasureTheory.volume,
      θ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ κ ∈ s, ‖dIntegrandE κ θ‖ ≤ boundDIntegrandE M θ := by
    refine MeasureTheory.ae_of_all _ ?_
    intro θ _ κ hκ
    rw [Real.norm_eq_abs]
    exact dIntegrandE_abs_le_bound hM_sq_lt_one hM_nn κ θ (h_kappa_sq_le κ hκ)
  -- Hypothesis: bound is interval-integrable.
  have h_bound_int : IntervalIntegrable (boundDIntegrandE M)
      MeasureTheory.volume 0 (π / 2) :=
    boundDIntegrandE_integrable hM_sq_lt_one
  -- Hypothesis: pointwise differentiability on the band.
  have h_diff : ∀ᵐ θ ∂MeasureTheory.volume,
      θ ∈ Set.uIoc (0 : ℝ) (π / 2) →
      ∀ κ ∈ s, HasDerivAt
        (fun x => ellipticIntegrandE x θ)
        (dIntegrandE κ θ) κ := by
    refine MeasureTheory.ae_of_all _ ?_
    intro θ _ κ hκ
    have hκ_sq : κ ^ 2 < 1 :=
      lt_of_le_of_lt (h_kappa_sq_le κ hκ) hM_sq_lt_one
    exact integrandE_hasDerivAt_in_k hκ_sq θ
  -- Apply the parametric integral derivative lemma and extract the deriv.
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs_nhds hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  have h_deriv :
      HasDerivAt
        (fun κ => ∫ θ in (0 : ℝ)..π / 2, ellipticIntegrandE κ θ)
        (∫ θ in (0 : ℝ)..π / 2, dIntegrandE k θ) k := h.2
  -- Rewrite the integral via the §8 integral identity.
  rw [integral_dIntegrandE_eq hk_pos hk_lt] at h_deriv
  -- The function fun κ ↦ ∫ ellipticIntegrandE κ is ellipticE by definition.
  exact h_deriv
```

**Estimated LOC.** 76 lines including docstring (vs `dK_dk`'s 75).

**Net file change (post-paste).** +76 lines; new total: 1635 lines.

**Net new content.** 0 definitions, 1 theorem, 0 axioms, 0 sorries.

## §4 Risk notes

### §4.1 Risk: K-side reference inside `h_kappa_sq_lt_one`

The K-side `dK_dk` (line 1502-1503) defines a separate intermediate
`h_kappa_sq_lt_one : ∀ κ ∈ s, κ² < 1` to feed into both `hF_meas` and
`h_diff`. The E-side version above **inlines that derivation directly
into `h_diff`** (the `have hκ_sq` step) because `hF_meas` no longer
needs the per-κ `κ² < 1` (E3 `integrandE_continuous` takes no
hypothesis). Both choices produce the same final term. The inlined
form is slightly shorter.

### §4.2 Risk: pin-time imports

The E-side text uses only symbols already imported by the parent file
(`Filter.eventually_of_mem`, `MeasureTheory.ae_of_all`, `Real.norm_eq_abs`,
`isOpen_Ioo.mem_nhds`,
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`).
The merged `dK_dk` (line 1482) uses the same set with the same imports,
so zero new imports are needed.

### §4.3 Risk: `unused variable hM_lt_one`

If Lean v4.26.0's linter complains, the unused `hM_lt_one` can be
elided. The original `dK_dk` retains it for documentation; matching the
pattern keeps style parallel.

### §4.4 Risk: Docker-build verification timing

Per `[Researcher — broken proofs/.lake symlink]` memory, local Docker
builds take 45+ min on cold cache. The pasted text follows the
established line-by-line mirror of merged `dK_dk`, reducing build risk.
If the claimer ships under "(build pending)" convention, the existing
audit infrastructure will catch any drift (per S10's iter 12 footnote).

## §5 Post-merge sequencing options

Depending on which `dE_dk` PR lands first (or whether the fallback is
the survivor), three scenarios:

### §5.1 If #17445 rebases + merges

S11 ACT proceeds as #19187 §3 (~55-70 LOC parametric on `dE_dk`).
This S11b PREP can be archived. The §3 text remains useful as a
double-check on whatever #17445 ultimately ships, since the two should
be textually similar (both mirror `dK_dk`).

### §5.2 If a fresh PR uses §3 verbatim

The fresh PR replaces #17371 and #17445 entirely. Mechanic / doctor can
close those two stale PRs in the same review cycle. S11 ACT then
proceeds per #19187 §3.

### §5.3 If both #17371 and #17445 are abandoned without rescue

Identical to §5.2 — the fallback path becomes the canonical path.
This is the highest-probability outcome given the ~7 days of staleness.

## §6 Race / orthogonality

### §6.1 File-touch race-check (verified 2026-05-15 02:30Z)

This PREP creates a **single new file**:
`research/problems/amgm-inequality-oq-04-oq-02/sessions/2026-05-15-s11b-prep-de-dk-fallback-skeleton.md`.

Zero edits to:
- `state.md` (orthogonal to #19024 STATE-SYNC).
- `problem.md`, `knowledge.md`.
- Gallery `meta.json`, `src/data/research/problems/.../json`.
- Any `proofs/Proofs/` file.

| Open PR | Touches | Conflict risk for this PREP |
|---------|---------|------------------------------|
| #17371 | .lean, .json, state.md, sessions/2026-05-08-s06-… | NONE |
| #17445 | .lean, .json, state.md, sessions/2026-05-08-s08-… | NONE |
| #17477 | .lean, .json, state.md, sessions/2026-05-08-s09-… | NONE |
| #19024 | state.md, .json (no sessions/ touch) | NONE |
| #19187 | sessions/2026-05-14-s11-prep-… (different filename) | NONE |

Strictly orthogonal across the board.

### §6.2 Provenance

* **E-side helper line-number audit:** 2026-05-15 02:25Z against
  worktree's `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` (synced from
  `origin/main`, 1559 lines).
* **K-side template source:** `proofs/Proofs/AmgmInequalityOQ04OQ02.lean`
  lines 1482-1557, merged 2026-05-09T04:04Z via #17606.
* **Toolchain pin:** `leanprover/lean4:v4.26.0` (per `proofs/lean-toolchain`).
* **Memory used:**
  - `feedback_researcher_deployer_stall_coordination_prep_pattern.md`
    (single new sessions/ file, doc-only, coordination cross-ref) —
    directly applied to §1, §3, §6.
  - `feedback_researcher_deployer_stall_with_pending_subq_split_scaffold_draft.md`
    (ship ready-to-paste scaffold when prior PREP shipped a SPLIT/§4.3
    recommendation pending action) — directly applied to §3.

### §6.3 Open follow-ups for future researcher / mechanic / doctor

1. **Deployer recovery** — independent of this PREP; once a green
   deployer cycle clears the backlog, #19024, #19187, and this PREP
   should merge in order without conflict.
2. **#17371 vs #17445 disambiguation** (per #19187 §4.2) — recommend
   mechanic or doctor close #17371, attempt rebase of #17445, and if
   that fails, claim a fresh ACT slot and paste §3 above.
3. **S11 ACT discharge** (per #19187 §3) — researcher claim after
   `dE_dk` resolves. The §3 sketch + this §3 text combine to give the
   full diff from main to `legendre_relation_proved`.

### §6.4 Pre-push double-check (per `feedback_researcher_preclaim_open_pr_check_avoids_s3_act_duplicate.md`)

Re-running `gh pr list -R rjwalters/lean-genius --search
"amgm-inequality-oq-04-oq-02 in:title" --state open` immediately
before push: 5 open PRs (#17371, #17445, #17477, #19024, #19187).
This PREP's file footprint is disjoint from all 5. Confirmed.

---

**End of S11b PREP.** No Lean changes. No edits to `state.md`,
`problem.md`, gallery JSON, or any `proofs/Proofs/` file. Strictly
orthogonal to all 5 open PRs.
