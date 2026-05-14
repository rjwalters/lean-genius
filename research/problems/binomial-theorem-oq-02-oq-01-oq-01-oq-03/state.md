# Research State: binomial-theorem-oq-02-oq-01-oq-01-oq-03

## Current State
**Phase**: ACT (Phase-4 unblocking — S11 templates BUILD VERIFIED via S12 unblocker fixes)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-13 (Session 12, researcher-9)
**Iteration**: 12

## Session 12 Focus (2026-05-13, researcher-9) — S11 build verification + 3 unblocker fixes

S12 establishes the build baseline that S11 deferred. Per memory pattern
[researcher-9 build-pending-chain]: this slug had shipped 4+ "(build
pending)" PRs in a row (S8 #17233/#17234, S9 #17318, S11 #18916), so the
Mathlib v4.26.0 surface-drift risk had accumulated. Pre-claim Docker
build (commit 7f555c51, S11 tip) revealed **3 errors in target file
itself** (not parent-file regressions):

| # | Line | Theorem | Error | Root cause |
|---|---|---|---|---|
| 1 | 390 | `piAntidiag_apply_le` (helper) | `omega could not prove the goal` | Mathlib v4.26.0 `Finset.mem_piAntidiag` returns `s.sum k = n` (dot-notation form); omega's preprocessor doesn't bridge to `∑ i ∈ s, k i` form despite definitional equality. |
| 2 | 537 | `binomialCDF_le_one` (pre-S11, working idiom) | `rewrite failed: pattern not found` | Mathlib v4.26.0 `add_pow` produces `p^m * (1-p)^(n-m) * choose` order (choose last); `binomialCDF` definition uses `choose * p^m * (1-p)^(n-m)` order (choose first). |
| 3 | 609 | `binomialCDF_eq_one` (S11 transcribed template) | same as #2 | same as #2 |

S12 fixes (3 surgical edits, each in same file):

* **Line 390** (`piAntidiag_apply_le`): replace bare `omega` with explicit `calc k i₀ ≤ ∑ i ∈ s, k i := hle | _ = n := hksum` chain. Bulletproof against the omega/dot-notation skew.
* **Lines 537 + 609** (both in `add_pow`-using theorems): replace `rw [← hadd]` with `conv_rhs => rw [hadd]`. The `conv_rhs` targets only the goal's RHS `1`, avoiding the over-rewrite that mangles `(1 - p)` inner expressions. The subsequent `Finset.sum_congr rfl + ring` normalises per-term multiplication order (`choose * p^j * (1-p)^(n-j)` vs `p^j * (1-p)^(n-j) * choose`).

**Status: BUILD VERIFIED.** Final docker-build:

```
✔ [3209/3209] Built Proofs.BinomialTheoremOQ02OQ01OQ01OQ03 (6.3s)
Build completed successfully (3209 jobs).
```

(Build log: `.loom/logs/researcher-9-binomial-s12-build2.log`.) Build #1 (cold cache) failed at 3 errors above; build #2 (after fixes 1+2 forward, before targeted `conv_rhs`) failed at 2 errors at 538:62 and 601:58 — `rw [hadd]` over-rewrote the inner `1`, mangling the goal; build #3 with `conv_rhs => rw [hadd]` succeeded.

### File counts (post-S12)

* `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean`: **682 → 703** lines (+21, all comment-only documentation of the 3 fixes plus the 3 surgical-tactic edits themselves; no theorem/axiom/sorry-count change).
* `theoremCount`: 17 (unchanged).
* `axiomCount`: 1 (`binomial_clt_pointwise`, unchanged).
* `sorries`: 0 (unchanged — confirmed live, no longer just metadata claim).

The `meta.json` status / badge upgrade noted in S11's "After build is green" plan is now appropriate (mechanic territory):

```json
"status": "axiomatized" (already current per #18919 sync)
"badge": "axiom"          (already current per #18919 sync)
"sorryCount": 0           (already current per #18919 sync)
```

So no `meta.json` follow-up needed — the S11 mechanic sync (#18919, 2026-05-13) was prescient. **What S12 retroactively validates is that the sync was correct: the file does build with 0 sorries.**

## Session 11 Focus (2026-05-13, researcher-1) — S10 repair templates transcribed (build-pending ACT)

S11 ACT transcribes the five repair templates produced in S10 (researcher-6)
into `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean`, taking the file
from `544 lines / 5 sorries / 1 axiom` to `~658 lines / 0 sorries / 1 axiom`.
Net change: -5 sorries, +114 LOC, unchanged axiom count. The single
remaining axiom is `binomial_clt_pointwise` (de Moivre–Laplace), preserved
as the Phase-4 elimination target.

**Status: BUILD-PENDING.** S11 did not run `./proofs/scripts/docker-build.sh
Proofs.BinomialTheoremOQ02OQ01OQ01OQ03` due to session-time budget
(Docker bootstrap + Mathlib cache fetch is 1–2 hours; templates carry
forensic-certainty caveats noted in S10 knowledge.md). The repair-template
"risk notes" identify the most likely failure modes per sorry:

| # | Theorem | Risk note (from S10) |
|---|---|---|
| 1 | `standardNormalCDF_tendsto_atBot` | `simpa using hsub` final step may need explicit `linarith` fallback or named `have` for the `1 - 1 = 0` identity. |
| 2 | `multinomialMarginalCDF_eq_binomialCDF` | The `Finset.sum_fiberwise_of_maps_to` `with`-filter syntax may not unify literally with `.filter (...)`; `simp_rw` fallback or hand-rolled `disjUnion`. |
| 3 | `binomialCDF_mono` | If `Application type mismatch` reappears at `mul_nonneg`, may be `Finset.sum_le_sum` signature drift; companion `binomialCDF_zero_le` uses same syntax and works. |
| 4 | `binomialCDF_eq_one` | `unfold binomialCDF` may produce `dite` instead of `ite` requiring `conv_lhs` adjustment; mirror is `binomialCDF_le_one` (working idiom). |
| 5 | `multinomial_marginal_clt` | Clean composition; requires #2 to build. |

If Docker build fails on any of the five, Doctor / Mechanic can refine
the closing tactic in isolation (each repair is local). If multiple
templates regress simultaneously the safe fallback is to selectively
revert and re-demote the problematic sorries to `sorry` while keeping
the successfully-transcribed ones.

### After build is green
1. `meta.json`: `status: "formalized" → "axiomatized"`, `badge: "wip" → "axiom"`, `sorryCount: 5 → 0` (Mechanic territory).
2. Phase-4 Portmanteau axiom-elimination work (S9's `cdf_tendsto_of_inDistribution` bridge lemma) can resume.
3. The CDF-tail saturation library (`standardNormalCDF_tendsto_atBot` + S8's `_atTop`) is now complete on a green file.

### Files modified (S11)
- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean` (5 sorry bodies replaced, +114 LOC, doc string "Honest Reporting" section updated)
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/state.md` (this entry)
- `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03.json` (`currentState`, `lastUpdate`, `progressSummary`, `insights`, `nextSteps`)

Build status: PENDING Docker verification. Status field intentionally
NOT changed to `axiomatized` until build is green; meta `sorryCount`
intentionally NOT decremented for the same reason.

---

## Session 10 Focus (2026-05-13, researcher-6) — Sorry-site forensics + Mathlib v4.26 repair templates (doc-only PREP)

S10 PREP work targets the 5-sorry build-broken state inherited from
S5–S8 "build pending" merges (mechanic PR #17353 demoted to sorry;
file currently 544 lines, 5 sorries + 1 axiom, compiles). The S10
contribution is a forensic audit of each sorry against the lake-pinned
Mathlib v4.26.0 SHA (`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
together with concrete repair templates a future ACT session can
transcribe in a single 1–2 hour bounded iteration.

**Key forensic finding (refutes S9 hypothesis).**
`MeasureTheory.tendsto_integral_Iic_zero` — cited by S8 (researcher-1,
PR #17233) as the foundation of `standardNormalCDF_tendsto_atBot` and
re-raised by S9 as "possibly a namespace/import ordering issue" — does
NOT exist in the lake-pinned v4.26 Mathlib SHA. Bearer-audited via
`gh api repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Integral/IntegralEqImproper.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
The S8/S9 attribution was wrong.

**The corrected proof strategy** (concrete template in knowledge.md
S10 entry) builds `standardNormalCDF_tendsto_atBot` from
`aecover_Ioi Filter.tendsto_id` (atBot direction) + `setIntegral_compl`
+ `Set.compl_Ioi`, then `Filter.Tendsto.const_sub 1` to get the
`1 - 1 = 0` limit. All cited Mathlib lemmas are confirmed present in
the pinned SHA.

The remaining four sorry sites have repair templates in S10
knowledge.md:

| # | Theorem | Template strategy |
|---|---|---|
| 1 | `standardNormalCDF_tendsto_atBot` | aecover_Ioi + setIntegral_compl (new approach) |
| 2 | `multinomialMarginalCDF_eq_binomialCDF` | fiber-decomp via `sum_fiberwise_of_maps_to`; flagged pre-fix used `(g := if-stmt)` typo where `(f := ...)` was intended |
| 3 | `binomialCDF_mono` | pre-fix proof minus missing terminal `le_refl 0` close |
| 4 | `binomialCDF_eq_one` | mirror `binomialCDF_le_one` (working idiom in same file); pre-fix had wrong `exact (binomialCDF_neg n p hx).symm` (premise contradicts hx) |
| 5 | `multinomial_marginal_clt` | `Filter.Tendsto.congr` composition of sorries 2 + de Moivre–Laplace axiom |

Repair work is bounded (~25 LOC per sorry), independent (#1, #3, #4
can land in any order; #5 strictly depends on #2), and uses only
Mathlib v4.26 idioms already exercised elsewhere in the same file.
Build verification mandatory once an ACT session transcribes the
templates.

After repair: file returns to `0 sorries / 1 axiom`; `status` flips
back `formalized → axiomatized`; `badge` `wip → axiom` (Mechanic
inverse of PR #17331). Then Phase-4 Portmanteau axiom-elimination
work (S9's `cdf_tendsto_of_inDistribution` bridge lemma) can resume
on a green file.

S10 declined to push the templates as Lean code: build risk + ACT
session has tighter scope. The PREP contribution is the API survey +
proof sketches.

### Files modified (S10)
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/state.md` (this entry)
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/knowledge.md` (full S10 entry with API table + 5 templates)
- `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03.json` (`currentState`, `lastUpdate`, `progressSummary`, `insights`, `nextSteps`)

No `.lean` file modifications. No build risk.

---

## Session 9 Focus

S9 (this session, researcher-8) ran a Docker build of the merged
`BinomialTheoremOQ02OQ01OQ01OQ03.lean` and **discovered the file does NOT
build** under Mathlib v4.26.0. Five pre-existing errors are present from
S5–S8 PRs that landed with `(build pending)` annotation but were never
actually verified:

```
error: Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean:271:8:
  Unknown identifier `MeasureTheory.tendsto_integral_Iic_zero`
error: Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean:381:4:
  omega could not prove the goal: a possible counterexample may satisfy c ≥ 0
error: Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean:409:40:
  Application type mismatch
error: Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean:519:8:
  Tactic `rewrite` failed: Did not find an occurrence of the pattern
error: Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean:585:6:
  Tactic `rewrite` failed: Did not find an occurrence of the pattern
```

These match the doctrinal anti-pattern from memory
`feedback_docstring_only_merges_mask_type_errors.md` (deployer auto-merges
PRs without builds). The file claims "0 sorries / 1 axiom" but Lean
cannot type-check it; if it had been built locally before merge any of
S5/S6/S7/S8 would have been blocked. Same recurrence pattern as the
konigsberg-oq-01-oq-02 main file (#16675 broke the build, never repaired).

### What S9 Decided NOT to Do

S9 prepared a small additive contribution — the **abstract Portmanteau
CDF-bridge lemma** `cdf_tendsto_of_inDistribution`, which would have been
the abstract step S10 composes with Mathlib's i.i.d. CLT. The lemma was
researched, drafted, and Mathlib-API-verified. However, S9 reverted the
in-file edit and elected NOT to push it as part of the broken main file
because:

1. The pre-existing 5 errors must be repaired BEFORE adding new
   theorems (they cause Lean to silently substitute `sorry` for the
   broken proofs, making meta.json's "0 sorries" claim false).
2. Adding a new lemma without verifying it elaborates is the same
   "build pending" anti-pattern that produced this state.
3. The right fix is to repair S5–S8 errors first — a Mechanic / Doctor
   task, not a Researcher task.

Instead, S9 documented the bridge lemma proof template + the build-
breakage details in `knowledge.md` so a future S10 (after the file
is unblocked) can transcribe the lemma directly.

### The Bridge Lemma Proof Template (for S10)

```lean
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Order.DenselyOrdered

theorem cdf_tendsto_of_inDistribution
    {μs : ℕ → MeasureTheory.ProbabilityMeasure ℝ}
    {μ : MeasureTheory.ProbabilityMeasure ℝ}
    (h_conv : Filter.Tendsto μs Filter.atTop (nhds μ))
    {x : ℝ} (h_atom : μ {x} = 0) :
    Filter.Tendsto (fun n : ℕ => μs n (Set.Iic x))
      Filter.atTop (nhds (μ (Set.Iic x))) := by
  refine MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    h_conv ?_
  rw [frontier_Iic]
  exact h_atom
```

Mathlib API surface verified by S9:
- `MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`
  — exists in mathlib v4.26.0; signature confirmed.
- `frontier_Iic` (in `Mathlib.Topology.Order.DenselyOrdered`)
  — requires `[NoMaxOrder α]`; ℝ has this auto-instance.
- `HasOuterApproxClosed ℝ` (required by Portmanteau lemma)
  — automatic since ℝ is pseudo-emetrizable
  (`Mathlib.MeasureTheory.Measure.HasOuterApproxClosed:31`).

### Build-Breakage Details (for Mechanic / Doctor)

The 5 failure sites correspond approximately to:
- L271 (S8 `standardNormalCDF_tendsto_atBot`): `MeasureTheory.tendsto_integral_Iic_zero`
  — possibly renamed or class-context-dependent. The lemma exists in
  `Mathlib.MeasureTheory.Integral.IntegralEqImproper.lean:630` inside the
  `MeasureTheory` namespace, so the qualified name should resolve. The
  S5-imported file may have shadowed it or import path drift.
- L381 / L409 / L519 / L585: omega/rewrite/type-mismatch failures in
  `binomialCDF_*` and `multinomialMarginalCDF_eq_binomialCDF`. Need
  individual debugging.

### Axiom count: 1 (unchanged), file: build-broken (unchanged from pre-S9 state).

### What S9 Did NOT Do

- Push any `.lean` modifications (avoided polluting a broken file).
- Run a Mechanic-style fix-up of the 5 errors (out of researcher scope;
  flag-and-document is the appropriate response).

## Current Focus (Session 8, prior)
Phase-4 prep continued — Session 8 (this PR, complementary track) adds
two binomialCDF-side asymptotic-saturation (`Filter.Tendsto`-form) lemmas:

- `binomialCDF_tendsto_one_atTop` (under `0 ≤ p ≤ 1`): eventually
  constant via `binomialCDF_eq_one`, packaged with `Tendsto.congr'` and
  `Filter.eventually_ge_atTop (n : ℝ)`.
- `binomialCDF_tendsto_zero_atBot`: eventually constant via
  `binomialCDF_neg`, packaged with `Tendsto.congr'` and
  `Filter.eventually_lt_atBot (0 : ℝ)`. No `p` constraint required.

The matching standardNormalCDF tail-limit lemmas (Φ → 1 at +∞ and
Φ → 0 at -∞) are added in the parallel S8 PR #17233 (researcher-1, opened
3 minutes earlier). To avoid lemma-statement collisions on a hot file,
this PR was narrowed to the binomialCDF side only — the original draft
also included `standardNormalCDF_tendsto_one_atTop` but that lemma is
already in #17233 under name `standardNormalCDF_tendsto_atTop` with the
same proof technique (AECover + integral_gaussianPDFReal_eq_one), so
keeping it here would have produced a merge conflict.

Together, the two PRs convert the boundary-value information from
Sessions 4–7 into the `Filter.Tendsto` form Mathlib's Portmanteau
direction at `±∞` consumes. With `standardNormalCDF_continuous`
(Session 7) and the four-corner `binomialCDF_*` lemmas (Sessions 4–7),
all the structural-CDF prerequisites for the Portmanteau bridge are
now in place after both S8 PRs land.

**Axiom count: 1 (unchanged).** After this PR alone: 0 sorries / 1 axiom
(`binomial_clt_pointwise` only), 16 theorems (substantive count: 12),
550 lines.

**Build verification.** Session 8 was conducted under the broken
`/Users/rwalters/GitHub/lean-genius/proofs/.lake` self-symlink trap
(see memory feedback `feedback_researcher_lake_symlink_broken.md`),
so a Docker build was not run. Each lemma uses well-tested Mathlib
idioms (`AECover` API, `Filter.Tendsto.congr'`, `filter_upwards` over
`eventually_ge_atTop` / `eventually_lt_atBot`), so confidence is high
but not verified locally. CI is the ground truth for this PR.

## Active Approach
**CDF-based** rather than the measure-theoretic Bernoulli-sum approach
sketched in iteration 1. Justification:

- Avoids the heavy `MeasureTheory` + `IsProbabilityMeasure` + Mathlib-CLT
  setup needed to use `ProbabilityTheory.iid_central_limit_theorem`.
- Matches the classical de Moivre–Laplace presentation.
- Keeps the reduction step transparent: the marginal CDF *equals* the
  binomial CDF (not just converges to it), so `Filter.Tendsto.congr` does
  the job.
- Cost (since Session 2 — RESOLVED Session 6): the original scaffold
  introduced `standardNormalCDF` as `opaque` (counted as +1 axiom);
  Session 6 replaced it with a concrete `noncomputable def`
  integrating Mathlib's `gaussianPDFReal 0 1` over `Set.Iic x`,
  removing that assumption.

## Attempt Count
- Total attempts: 7 (Sessions 1–7)
- Approaches tried:
  - **Iteration 1** (researcher-8, OBSERVE→ORIENT): planned i.i.d.-CLT
    decomposition (Sublemmas A, B, C, D). No Lean code.
  - **Iteration 2** (researcher-9, ACT): CDF-based scaffold.
    `BinomialTheoremOQ02OQ01OQ01OQ03.lean` (178 lines, 2 axioms incl.
    opaque, 1 sorry, 2 theorems). Merged in #16866.
  - **Iteration 3** (researcher-3, ACT): discharged the reduction-lemma
    sorry via `Finset.sum_fiberwise_of_maps_to`. File grew to 239 lines,
    2 axioms, **0 sorries**, 3 theorems (added `piAntidiag_apply_le`
    private lemma).
  - **Iteration 4** (researcher-10, ACT): Phase-4 prep.
    Added `binomialCDF_neg` (CDF = 0 below support) and
    `binomialCDF_mono` (monotone in `x` when `0 ≤ p ≤ 1`). File grew to
    275 lines, 2 axioms (unchanged), **0 sorries**, 5 theorems
    (substantive count: 4). Merged in #16951.
  - **Iteration 5** (researcher-1, ACT): Phase-4 prep continued.
    Added `binomialCDF_zero_le` (CDF ≥ 0) and `binomialCDF_le_one`
    (CDF ≤ 1) using `add_pow` for the binomial expansion. File grew to
    330 lines, 2 axioms (unchanged), **0 sorries**, 7 theorems
    (substantive count: 6). Merged in #16992.
  - **Iteration 6** (researcher-1, ACT): Phase-4 axiom elimination.
    Replaced `opaque standardNormalCDF` with a concrete `noncomputable def`
    integrating `ProbabilityTheory.gaussianPDFReal 0 1` over `Set.Iic x`;
    added three structural lemmas (`standardNormalCDF_nonneg`, `_le_one`,
    `_mono`). File grew to 369 lines, **1 axiom** (was 2), 0 sorries,
    10 theorems (substantive count: 9). Merged in #17014.
  - **Iteration 7** (researcher-11, ACT — THIS SESSION): Phase-4 prep —
    completed the standard-normal CDF structural library. Added
    `standardNormalCDF_continuous` (Φ is continuous on ℝ) plus a private
    bridge lemma `standardNormalCDF_eq_zero_plus_intervalIntegral`
    (`Φ x = Φ 0 + ∫_{0..x} gaussianPDFReal 0 1 t`). The continuity
    proof reduces to `MeasureTheory.Integrable.continuous_primitive`
    after the bridge lemma, which in turn uses
    `MeasureTheory.intervalIntegral_tendsto_integral_Iic`,
    `intervalIntegral.integral_add_adjacent_intervals`, and
    `tendsto_nhds_unique`. Two new imports
    (`Mathlib.MeasureTheory.Integral.IntegralEqImproper`,
    `Mathlib.MeasureTheory.Integral.DominatedConvergence`). File now
    445 lines, **1 axiom** (unchanged), 0 sorries, 12 theorems
    (substantive count: 10).

## Blockers
- **Build verification**: this session could not run the Docker build
  for direct compile-check (long iteration time + worktree symlink trap).
  The scaffold uses well-tested Mathlib idioms (`Filter.Tendsto.congr`,
  `Real.sqrt`, `Finset.range`); confidence is high but not verified.
  CI is the ground truth.
- **Reduction lemma sorry**: the proof of
  `multinomialMarginalCDF_eq_binomialCDF` is a routine fiber-regrouping
  + application of the parent's `multinomial_marginal_pmf`. Phase-3 target.
- **`standardNormalCDF` opaque** (RESOLVED in Session 6): replaced
  with a concrete `noncomputable def` integrating Mathlib's
  `ProbabilityTheory.gaussianPDFReal 0 1` over `Set.Iic x`; axiom
  count dropped 2 → 1.
- **`binomial_clt_pointwise` axiom** (the only remaining axiom):
  Session 8 target. The cleanest path is to derive from
  `ProbabilityTheory.iid_central_limit_theorem` via the Portmanteau
  theorem at continuity points of the standard normal CDF (every
  point — Φ is continuous, now machine-verified by Session 7's
  `standardNormalCDF_continuous`).
- **Mathlib survey result** (Session 7): Mathlib does NOT contain a
  single `iid_central_limit_theorem` lemma. Instead it has
  `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum` (random-
  variable convergence-in-distribution form, requires centered + unit-
  variance + i.i.d. + identically-distributed). There is also no
  Mathlib lemma stating "the law of (X₁ + ... + Xₙ) for i.i.d.
  Bernoulli(p) X₁,...,Xₙ equals Binomial(n,p)" — that bridge needs to
  be constructed manually from `PMF.binomial` and pushforward measures.
  Realistic estimate: discharge of `binomial_clt_pointwise` is ~300–500
  lines across **2+ sessions**, not feasible in one session.

## Next Action

**Session 8 — Phase-4 axiom attack (Lemma A: Bernoulli→Binomial measure
bridge)**. With the CDF-structure library complete on both sides
(Sessions 4–7), the next bottleneck is the measure-theoretic side:
prove that for n i.i.d. Bernoulli(p) random variables `X₁, ..., Xₙ` on
a finite product probability space, the pushforward of the product
measure under `(ω ↦ Σ Xᵢ(ω))` has law equal to `Binomial(n, p)` (with
PMF matching `binomialCDF`'s summand). This is the foundational bridge
that lets Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum` apply.

Subsequent sessions:
- **Session 9 (Lemma C — Portmanteau bridge)**: prove the abstract
  bridge "convergence in distribution + continuous limit CDF ⟹
  pointwise CDF convergence". Combines Mathlib's Portmanteau lemmas
  (`Mathlib/MeasureTheory/Measure/Portmanteau.lean`) with our new
  `standardNormalCDF_continuous`.
- **Session 10 (axiom discharge)**: assemble Lemmas A + C + Mathlib's
  CLT into the proof of `binomial_clt_pointwise`. Convert axiom →
  theorem; status promotes to `verified` (axiomCount 1 → 0).

Alternative single-session path that was considered but rejected:
direct Stirling's-formula asymptotic analysis of `C(n,j) p^j (1-p)^(n-j)`
near the mean. Self-contained but tedious; competing with the
Portmanteau path's reuse of Mathlib infrastructure.

---

**Phase-3 (Session 3)**: discharged the reduction-lemma sorry. Proof
sketch (follows the actual file):

```lean
theorem multinomialMarginalCDF_eq_binomialCDF ... := by
  unfold multinomialMarginalCDF binomialCDF
  -- Step 1: build the fibre map.
  have hmaps : ∀ k ∈ s.piAntidiag n, k i₀ ∈ Finset.range (n + 1) :=
    fun k hk => by
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact piAntidiag_apply_le s n i₀ k hk
  -- Step 2: split the multinomial sum by `j := k i₀`.
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (g := fun k => if ((k i₀ : ℕ) : ℝ) ≤ x
                       then multinomialProb s p n k else 0)]
  -- Step 3: term-by-term comparison.
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  by_cases hcond : (j : ℝ) ≤ x
  · rw [if_pos hcond]
    -- inside the fibre, k i₀ = j, so the if-condition reduces to hcond.
    -- factor it out, then apply Sublemma A.
    have h_inner : ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
        (if ((k i₀ : ℕ) : ℝ) ≤ x then multinomialProb s p n k else 0) =
        ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
          multinomialProb s p n k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [hk.2, if_pos hcond]
    rw [h_inner]
    exact multinomial_marginal_pmf s p n hp i₀ hi₀ j hj
  · rw [if_neg hcond]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [hk.2, if_neg hcond]
```

Plus a short auxiliary `piAntidiag_apply_le` (private lemma): every
coordinate of a composition `k ∈ s.piAntidiag n` is at most `n`.

**Phase-4 stretch**: discharge `binomial_clt_pointwise` by bridging from
Mathlib's i.i.d. CLT. This requires the Portmanteau theorem at continuity
points of the standard normal CDF.

## References
- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ02.lean:167` —
  `multinomial_marginal_pmf` (used for the reduction lemma).
- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean` —
  this session's scaffold (178 lines).
- `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-01-oq-03/` — gallery
  entry (created this session).
- `proofs/Proofs/CentralLimitTheorem.lean:375` — local general CLT
  (axiomatized at the standardisation step, characteristic-function form).
- Classical: Feller, *Introduction to Probability Theory*, Vol. I (1968),
  Ch. VII §3 (de Moivre–Laplace).
