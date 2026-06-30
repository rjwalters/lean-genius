# greens-theorem-oq-02-oq-02

**Question**: Can the Whitney axiom be proved in Lean using Mathlib's existing `BoundedVariation` and `MeasureTheory.Measure.AbsolutelyContinuous` API?

**Source**: open question on `greens-theorem-oq-02` (Green's Theorem: Minimal Regularity — Lipschitz Curves and L¹ Curl)

**Status**: DECIDE — **UPDATE (2026-06-15, S11/researcher-5): Docker recovered; built + verified the Fubini-reduction bridge (`proofs/Proofs/GreensTheoremOQ02FubiniBridge.lean`, Docker-GREEN, 0 sorry/0 axiom) — the step-3 connective `rectDoubleIntegral f = ∫ p in Ioo×ˢIoo, f ∂volume` that every prior plan listed but none had proven. This is the C¹ discharge path's missing piece: composing OQ01's axiom-free `greens_theorem_concrete` with it gives the corrected axiom's C¹ conclusion axiom-free. The L¹ case still needs the FTC-for-AC keystone (Mathlib v4.26→≥4.28 bump, unchanged). The S10 orientation fix is confirmed fully landed (all 7 consumers thread `hLineEq`; gallery meta `axiomatized`/`axiomCount: 1` accurate). See the S11 entry at the end of this file.**

**Prior (2026-06-15, S10/researcher-5)**: the orientation fix is LANDED + Docker-VERIFIED in the registered files. The previously-FALSE `greens_theorem_l1curl` now carries the `hLineEq` orientation hypothesis (and all 7 consumers thread it), so the registered build no longer contains the unsound statement.

**Prior status (2026-06-15, Session 5/researcher-4): the axiom `greens_theorem_l1curl` is FALSE as currently stated, so it cannot be discharged at all — not even after the planned Mathlib bump.** Sessions 1–4/S2 reduced the discharge to one RHS keystone (function-level FTC-for-AC, now upstream from v4.28.0) plus a Fubini reduction, and the S2 blueprint's step 4 assumed the LHS line integral could be assembled from "OQ01's boundary algebra" for free. That assumption is wrong: the ONLY hypothesis linking the abstract curve to the rectangle is `hTraversal` = image-containment in `frontier`, which encodes neither orientation, nor winding, nor non-degeneracy. A degenerate constant curve at a corner satisfies every hypothesis yet has line integral 0 while the curl's double integral is the area ≠ 0. There are therefore **two** gaps, not one: (a) the FTC-for-AC keystone (resolved upstream, needs the bump), AND (b) a curve→boundary orientation reduction that `hTraversal` does not support and that the bump does not address. The axiom's hypotheses must be strengthened before any discharge is possible. Still Docker-gated (blackout continues 2026-06-15). Build-pending counterexample committed: `proofs/Proofs/GreensTheoremOQ02Counterexample.lean` (UNREGISTERED).

## Summary

The target axiom is `greens_theorem_l1curl` (`proofs/Proofs/GreensTheoremOQ02.lean:350`). The OQ asks whether it is dischargeable via Mathlib's `BoundedVariation` + `Measure.AbsolutelyContinuous` API.

**Updated answer (2026-06-14): the keystone now exists upstream.** The survey (Session 1) correctly reduced the whole question to one missing keystone — the **function-level FTC for absolutely continuous functions**: `f` AC on `[a,b]` ⟹ `f b − f a = ∫ x in a..b, deriv f x` with `deriv f` only L¹/a.e.-defined. That keystone was **absent at v4.26.0** but is **present from Mathlib v4.28.0 onward** as:

```
theorem AbsolutelyContinuousOnInterval.integral_deriv_eq_sub
    {f : ℝ → ℝ} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    ∫ (x : ℝ) in a..b, deriv f x = f b - f a
```

in `Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean` (author Yizheng Zhu, PR #29508, part of #29092). The same file also ships integration-by-parts for AC functions (`integral_mul_deriv_eq_deriv_mul`). The function-level AC predicate `AbsolutelyContinuousOnInterval` and its algebra (`add`/`sub`/`mul`/`const_smul`) already existed at v4.26.0 in `Mathlib/MeasureTheory/Function/AbsolutelyContinuous.lean`; only the FTC/IBP theorems were added later.

So the blocker is **no longer "build a ~200–400 line foundational lemma"** — it is now **"bump Mathlib v4.26.0 → ≥ v4.28.0, then wire the rectangle Fubini reduction to the upstream lemma."**

## Key reframing (the main finding)

The axiom's own docstring justifies axiomatization by claiming the proof "requires geometric measure theory machinery (sets of finite perimeter, BV functions, Federer's trace theorem, Gauss-Green formula) not yet assembled in Mathlib." **This is an overstatement for the case actually stated.** The axiom's domain is a **rectangle** `Set.Icc a b ×ˢ Set.Icc c d`, with the curve `C` a Lipschitz parametrization of its frontier (`hTraversal`). The geometric domain is simple; the heavy GMT machinery is needed for general Lipschitz *domains*, not here.

The genuine gap versus the **axiom-free** OQ01 (`GreensTheoremOQ01.lean`, 0 axioms, uses pointwise `HasDerivAt` + `intervalIntegral.integral_eq_sub_of_hasDerivAt`) is precisely the weakening from pointwise-C¹ partials to an **a.e. curl with merely L¹ integrability** (`hCurlAE` + `hL1`). Via Fubini (`MeasureTheory.integral_prod`) the rectangle double integral splits into iterated 1D integrals, each needing FTC for a function whose derivative is only L¹ — i.e. FTC-for-AC.

So the true blocker is a **bounded ~200–400 line local build**, not a 1000+ line foundational GMT project.

## What Mathlib has vs. lacks

| Ingredient | Mathlib status |
|---|---|
| FTC (continuity / `HasDerivAt` everywhere) | ✅ `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` |
| **FTC-for-AC** (`f b − f a = ∫ f'`, L¹ deriv) | ✅ **added v4.28.0** — `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` (was ❌ at the v4.26.0 pin) |
| AC function predicate + algebra (`AbsolutelyContinuousOnInterval`) | ✅ v4.26.0 `Mathlib.MeasureTheory.Function.AbsolutelyContinuous` |
| IBP for AC functions | ✅ v4.28.0 `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul` |
| `IntervalIntegrable f` ⟹ `x ↦ ∫_c^x f` is AC | ✅ v4.28.0 `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral` |
| BoundedVariation (`eVariationOn`, BV ⟹ a.e. diff) | ✅ `Mathlib.Analysis.BoundedVariation` |
| Rademacher (Lipschitz ⟹ a.e. diff) | ✅ `Mathlib.Analysis.Calculus.Rademacher` |
| Measure `AbsolutelyContinuous` + Radon-Nikodym | ✅ `Mathlib.MeasureTheory.Decomposition.RadonNikodym` |
| Fubini (`integral_prod`) | ✅ |

Note: `Measure.AbsolutelyContinuous` is AC of **measures** (μ ≪ ν), not of functions. The OQ's intended route — model the L¹ curl as the RN-derivative of an AC measure and recover boundary values — still bottlenecks on the same function-level FTC bridge.

## Recommended approach (revised 2026-06-14 — keystone is upstream now)

Do **not** build `ftc_of_absolutelyContinuous` by hand any more — it exists upstream. New plan:

1. **Bump Mathlib** from `v4.26.0` to `≥ v4.28.0` in `proofs/lakefile.toml` / `lake-manifest.json` (current stable is v4.30.0; v4.31.0-rc2 exists). This is the gating step and may surface unrelated breakage across the proof corpus, so do it on a dedicated branch and rebuild the full proof set under Docker. **Verify the cross-corpus build before relying on this for OQ02.**
2. `import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun` in `GreensTheoremOQ02.lean`.
3. Discharge `greens_theorem_l1curl` by Fubini (`MeasureTheory.integral_prod`) reduction to two 1D integrals over the rectangle. For each 1D slice `x ↦ Q(x, y)` (resp. `y ↦ P(x, y)`):
   - From the L¹ hypotheses (`hCurlAE` + `hL1`), exhibit the slice as `c + ∫_a^x (∂Q/∂x)`; that integral function is AC by `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`.
   - Apply `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub` to get `f b − f a = ∫ deriv f`, matching the a.e. partial via `hCurlAE`.
   Reuse OQ01's boundary algebra to assemble the line-integral side.
4. Sanity check: the reduction must recover OQ01's conclusion when the curl comes from genuine `HasDerivAt` partials (C¹ ⟹ AC on a compact rectangle), matching the existing `greens_oq1_from_l1curl`.
5. Once discharged, flip `greens_theorem_l1curl` from `axiom` to `theorem ... := by …` and update `axiomCount` in `GreensTheoremOQ02` gallery meta + research JSON.

DONE (2026-06-13, doc-only): the OQ02 axiom docstring already states the accurate narrowed gap (rectangle ⟹ no GMT, only Fubini + FTC-for-AC). A follow-up doc tweak could now name the upstream lemma directly.

## Session log

### Session 2026-06-13 (Session 1) — ORIENT survey

**Mode**: FRESH
**Outcome**: scouted / ORIENT

**What I Did**
- Claimed fresh EMPTY-knowledge available problem.
- Read the `greens_theorem_l1curl` axiom and surrounding consequences in `GreensTheoremOQ02.lean` (origin/main).
- Compared against the axiom-free OQ01 proof to isolate the genuine hypothesis gap.
- Checked Mathlib's FTC / BoundedVariation / Radon-Nikodym coverage (mathlib4_docs + literature).

**Key Findings**
- Axiom domain is a rectangle ⟹ cited GMT requirement is overstated.
- True gap = FTC-for-AC (function level), which Mathlib lacks.
- Buildable in a bounded ~200–400 lines; problem is NOT truly blocked.

**Files Modified**
- `src/data/research/problems/greens-theorem-oq-02-oq-02.json` (added knowledge, status→surveyed, phase→ORIENT)
- `research/problems/greens-theorem-oq-02-oq-02/knowledge.md` (this file)

**Next Steps**
- Build FTC-for-AC bridge lemma; discharge axiom by Fubini once Docker restored.

### Session 2026-06-14 (Session 2) — Docker blackout: family-meta section-realign

**Mode**: BLOCKED (Docker down — `docker info` times out >25s; the FTC-for-AC build path from Session 1 is gated).

**What I Did**
- Re-confirmed the OQ's build path (`ftc_of_absolutelyContinuous`, ~200–400 lines) is gated by the Docker blackout. No Lean committed.
- Pivoted to the build-free vein: scanned the whole `greens-theorem*` gallery family for section/count drift.
- Fixed stale gallery metadata in 4 sibling entries (pure metadata, no Lean changes):
  - `greens-theorem-oq-01-oq-01-oq-03`: added missing **§ VII. Atomless Measure Generalization** section (228–292); 67-line tail was hidden.
  - `greens-theorem-oq-01-oq-02`: re-pinned all 5 Part ranges (file grew ~20 lines, sections never re-synced); synced stale `leanFile` counts (lineCount 227→247, theoremCount 5→6).
  - `greens-theorem-oq-04`: rebuilt sections array 11→12 (split lumped "Parts VIII-IX", fixed shifted ranges and Part IV/V/XI/XII banner titles to match the file).
  - `greens-theorem-oq-02` (parent of this OQ): re-pinned Part IV/V ranges + lineCount 507→518. theoremCount=19 is correct (3 apparent extras were docstring false positives).

**Verified clean (no fix)**: `greens-theorem`, `greens-theorem-oq-01` (gaps = trailing `end`/blank only); `greens-theorem-oq-03` (def 15/ax 3 grep counts were ```lean docstring false positives — real counts 14/2 match meta).

**Next Steps (unchanged from Session 1)**
- When Docker restored: build FTC-for-AC bridge lemma; discharge `greens_theorem_l1curl` by Fubini reduction to two 1D FTC-for-AC applications over the rectangle.

### Session 2026-06-14 (Session 3) — Aristotle attempt + keystone StatementOnly target

**Mode**: BLOCKED (Docker down — `docker info` times out; Aristotle MCP down — `prove()` returns "Resource not found"; worktree Mathlib symlink unreadable). No Lean verified.

**What I Did**
- Tried the one genuinely new avenue vs. Sessions 1–2: server-side proving via Aristotle MCP (bypasses local Docker). Server returned "Resource not found" on two attempts — currently down.
- Refined the keystone to its cleanest **tractable first building block**: FTC for **Lipschitz** functions,
  `LipschitzOnWith K f (Set.Icc a b) → f b - f a = ∫ x in a..b, deriv f x`.
  Rationale: it is statable in plain Mathlib without an `AbsolutelyContinuous`-of-functions predicate (the definitional gap that makes the general AC statement awkward), it captures the hard `AC ⟹ FTC` content, and the rectangle's boundary edges are Lipschitz.
- Localized the true obstruction: `integral_eq_sub_of_hasDeriv_right_of_le` wants an *everywhere* right-derivative on `(a,b)`; Lipschitz/Rademacher supplies it only a.e., so the a.e.-derivative → FTC bridge (the AC theory) is exactly the missing keystone.
- Authored `proofs/Proofs/StatementOnly_GreensOQ02_FTCofLipschitz.lean` — a one-theorem Aristotle batch target (`ftc_of_lipschitzOn`) following the Harmonic StatementOnly format (informal `/-` block, verbatim `set_option` block, Rivin proof-attempt scaffolding).

**Honest status**: This is an incremental artifact, not a discharge of the axiom. The StatementOnly file is **unverified** — it could not be compile-checked (Docker down) and could not be submitted (Aristotle down). The Lipschitz case is strictly weaker than the general-AC version the axiom needs.

**Files Modified**
- `proofs/Proofs/StatementOnly_GreensOQ02_FTCofLipschitz.lean` (new)
- `src/data/research/problems/greens-theorem-oq-02-oq-02.json` (insights, builtItems, progressSummary)
- `research/problems/greens-theorem-oq-02-oq-02/knowledge.md` (this entry)

**Next Steps**
- When Aristotle restored: submit `StatementOnly_GreensOQ02_FTCofLipschitz.lean` via the batch pipeline / `prove()`.
- When Docker restored: compile-check the StatementOnly file; if the Lipschitz FTC goes through, generalize to AC and run the Fubini discharge of `greens_theorem_l1curl`.

### Session 2026-06-14 (Session 4) — keystone found UPSTREAM (Docker down)

**Mode**: BLOCKED for build (Docker blackout continues), but a build-free **upstream-API audit** produced a real ORIENT→DECIDE advance that **supersedes the Session 3 manual-build path**.

**What I Did**
- Re-examined Sessions 1/3's central premise — "Mathlib lacks the function-level FTC for absolutely continuous functions" — against the *current* Mathlib source (the repo pins `v4.26.0`).
- Searched `leanprover-community/mathlib4` and found `Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`, which proves **exactly** the missing keystone.
- Pinned the version boundary precisely via the GitHub API: the file is **absent at v4.26.0** (tag dated 2025-12-13) and **first present at v4.28.0** (2026-02-16). It was introduced by **PR #29508** (author Yizheng Zhu, merged 2026-02-02, "FTC and integration by parts for absolutely continuous functions", part of #29092). Current stable is v4.30.0; v4.31.0-rc2 exists.
- Verified the exact theorem signature and that the supporting API the discharge needs (`AbsolutelyContinuousOnInterval` predicate + algebra, `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral`, `intervalIntegrable_deriv`, `ae_differentiableAt`) is all present at v4.28.0.

**Key Findings**
- The single keystone gap is **now closed upstream**: `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub : ∫ x in a..b, deriv f x = f b - f a` for `f` AC on `uIcc a b`, plus IBP `integral_mul_deriv_eq_deriv_mul`. This is the *general AC* version — strictly stronger than Session 3's Lipschitz-only `ftc_of_lipschitzOn` target.
- The AC-function *definition* + algebra already shipped at v4.26.0; only the FTC/IBP theorems were added in v4.28.0.
- **Supersedes Session 3**: there is no need to prove `ftc_of_lipschitzOn` via Aristotle, nor to hand-build the ~200–400 line bridge. The `StatementOnly_GreensOQ02_FTCofLipschitz.lean` artifact is now only a *fallback* relevant if a Mathlib bump is undesirable.
- Reframes the blocker from "build a foundational lemma" to **"bump Mathlib to ≥ v4.28.0 + wire the rectangle Fubini reduction to the upstream lemma."** Both steps remain Docker-gated for verification.

**Files Modified**
- `research/problems/greens-theorem-oq-02-oq-02/knowledge.md` (this file): status ORIENT→DECIDE, gap table, revised approach, this log entry.
- `src/data/research/problems/greens-theorem-oq-02-oq-02.json`: progressSummary, insights, mathlibGaps (now resolved-upstream), nextSteps, blockedReason, phase→DECIDE.

**Next Steps**
- Bump `proofs/lakefile.toml` Mathlib pin to ≥ v4.28.0 on a dedicated branch; rebuild the full proof corpus under Docker to catch unrelated breakage **before** relying on it.
- Then discharge `greens_theorem_l1curl` per the revised approach above and flip the `axiom` to a proved `theorem`.

---

## Session 2 update (2026-06-15, researcher-3) — upstream signatures VERIFIED

The S1 keystone-existence claim is now **independently confirmed against
Mathlib `master`** (S1 cited PR #29508 but never checked the live names). Both
load-bearing wiring lemmas exist with these exact current signatures:

- `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub (hf) : ∫ x in a..b, deriv f x = f b - f a` (FTC for AC)
- `IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral (h) (hc : c ∈ uIcc a b) : AbsolutelyContinuousOnInterval (fun x ↦ ∫ v in c..x, f v) a b`

**Refinement**: lemma (2) carries `hc : c ∈ uIcc a b`, not recorded in S1.
Wiring discharges it with `left_mem_uIcc` / `right_mem_uIcc` (base-point is an
endpoint).

A pinned 5-step Fubini-reduction blueprint mapping `greens_theorem_l1curl` to
these lemmas (reusing OQ01's boundary algebra) is in
`sessions/2026-06-15-s2-keystone-signature-verification.md`. Blocker unchanged:
the gating Mathlib bump (v4.26.0 → ≥ v4.28.0) is cross-corpus + Docker-gated.

---

## Session 5 (2026-06-15, researcher-4) — the axiom is FALSE as stated (counterexample)

**Mode**: DECIDE → integrity defect found. Dual blackout (Docker `docker info`
times out; Aristotle `prove` returns "Resource not found" on a live `n+0=n`
test). Build-pending Lean, UNREGISTERED.

**The finding (supersedes the "one keystone + bump" framing).** Every prior
session treated the discharge as a single RHS problem (the FTC-for-AC keystone)
and took the S2 blueprint's **step 4** — "reassemble `lipschitzLineIntegral P Q C`
from OQ01's boundary algebra" — as free. It is not free, and the axiom is
**false** under its stated hypotheses.

- The only hypothesis connecting the abstract `C : LipschitzClosedCurve` to the
  rectangle is `hTraversal : ∀ t ∈ Icc 0 C.T, C.γ t ∈ frontier (Icc a b ×ˢ Icc c d)`
  — pure **image containment**. It does **not** encode orientation
  (counterclockwise vs clockwise = a global sign), winding number / single
  traversal, or non-degeneracy.
- OQ01 does NOT relate an abstract curve to the boundary at all: it *defines*
  its line integral as an explicitly oriented four-edge sum
  (`rectLineIntegral`, `GreensTheoremOQ01.lean:76`). So there is no reusable
  "curve ⟹ four edges" lemma to import; that reduction is a genuine **second
  gap**, and it is simply false under the weak `hTraversal`.

**Counterexample (committed, build-pending).** The constant curve `γ ≡ (0,0)` on
the unit square with field `P = 0, Q(x,y) = x` (curl `≡ 1`):
- is a valid `LipschitzClosedCurve` (0-Lipschitz, closed);
- satisfies `hCurlAE` (curl `= 1` everywhere), `hL1` (constant on a compact set),
  and `hTraversal` ((0,0) is a corner ⟹ on the frontier);
- yet `lipschitzLineIntegral P Q C = 0` (zero velocity ⟹ zero integrand) while
  `∫ curl = area = 1`.

So the axiom forces `0 = 1`. File: `proofs/Proofs/GreensTheoremOQ02Counterexample.lean`
(`greens_theorem_l1curl_refuted : (0:ℝ) = 1`, plus the per-hypothesis lemmas).

**Consequence for the OQ verdict.** The answer to "can `greens_theorem_l1curl` be
discharged from Mathlib's BV + AC API?" is now: **No — not as stated, at any
Mathlib version.** The RHS keystone being upstream is necessary but not
sufficient; the LHS curve→boundary reduction is a separate, currently-false step.
The axiom must first be **corrected** — strengthen `hTraversal` to "`C` is a
positively-oriented (counterclockwise) simple parametrization of the rectangle
boundary," most cleanly by adding a hypothesis
`lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d` (OQ01's concrete
integral) and discharging THAT via OQ01 — itself a nontrivial
reparametrization-invariance fact, **not** covered by the Mathlib bump.

**Files Modified**
- `proofs/Proofs/GreensTheoremOQ02Counterexample.lean` (new, UNREGISTERED, build-pending)
- `research/problems/greens-theorem-oq-02-oq-02/knowledge.md` (status correction + this entry)
- `src/data/research/problems/greens-theorem-oq-02-oq-02.json` (insights, progressSummary, nextSteps)

**Next Steps**
1. **Correct the axiom first** (independent of Docker): rewrite
   `greens_theorem_l1curl` to take the orientation/parametrization hypothesis
   (e.g. `hLineEq : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d`),
   or restrict to the concrete four-edge curve.
2. When Docker returns: compile-check `GreensTheoremOQ02Counterexample.lean`
   (a few measure-theory lemma signatures may need v4.26.0 touch-ups — all
   names verified present in Mathlib, only autoparam/`measureReal` forms may
   differ from the newer sibling checkout used to name-check).
3. Then pursue the bump + Fubini discharge of the *corrected* axiom.

---

## Session 6 (2026-06-15, researcher-4) — soundness blast-radius map + build-ready fix spec

**Mode**: REVISIT (post-merge of S5 #24381). **Outcome**: mapped the FULL soundness
blast radius of the false axiom and pinned the exact coordinated correction. Docker
still down (`docker info` timeout); registered files left UNTOUCHED (a blind multi-site
edit to registered files under blackout would silently poison `main` — the deployer
compiles only the website, not Lean, so a break wouldn't surface until a Docker run).

### The defect is now a REGISTERED-CORPUS soundness issue
S5 (#24381, MERGED 11:05) proved `greens_theorem_l1curl` is FALSE (constant-curve
counterexample ⟹ 0=1). That axiom lives in **registered** `GreensTheoremOQ02.lean:361`
(Proofs.lean:2387). The unsoundness has **propagated** to 5 derived theorems across 2
registered files — every one inherits the too-weak `hTraversal` (image-containment only)
and concludes `lipschitzLineIntegral … = ∫∫ curl`, all equally refuted by the S5
constant curve:

| File (registered) | Decl | uses |
|---|---|---|
| GreensTheoremOQ02.lean:361 | `greens_theorem_l1curl` (axiom) | — (root) |
| GreensTheoremOQ02.lean | `lineIntegral_zero_curl` | axiom |
| GreensTheoremOQ02.lean | `lineIntegral_l1curl_smul` | axiom |
| GreensTheoremOQ02.lean | `greens_oq1_from_l1curl` | axiom |
| GreensTheoremOQ02OQ04.lean | `greens_stokes_l1curl` | axiom |
| GreensTheoremOQ02OQ04.lean | `closed_l1form_zero_integral` | `lineIntegral_zero_curl` |

### Build-ready correction spec (one coordinated Docker pass)
`GreensTheoremOQ02.lean` already `import`s `Proofs.GreensTheoremOQ01`, so
`rectLineIntegral` (GreensTheoremOQ01.lean:76) is in scope. Add the orientation
hypothesis to the axiom:

```
(hOrient : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d)
```

This makes the axiom SOUND: its conclusion becomes, after rewriting by `hOrient`,
`rectLineIntegral P Q a b c d = ∫∫ curlF` — the genuine rectangle Green identity (the
oriented four-edge integral equals the double integral of curl), which OQ01 already
proves at the C¹ level (`GreensTheoremOQ01.lean:171`) and which the L¹ case reduces to
via the FTC-for-AC keystone (the still-open Mathlib-bump gap). The S5 constant curve no
longer refutes it: that curve has `lipschitzLineIntegral = 0 ≠ rectLineIntegral` (the
real boundary integral), so it fails `hOrient`.

Each of the 5 consumers must thread one new `hOrient` argument:
- `lineIntegral_zero_curl`, `lineIntegral_l1curl_smul`, `greens_oq1_from_l1curl`,
  `greens_stokes_l1curl`: add `(hOrient : lipschitzLineIntegral P Q C = rectLineIntegral
  P Q a b c d)` (with `ω.P, ω.Q` for the form variants) to the signature and pass it to
  the axiom call.
- `closed_l1form_zero_integral`: add the same `hOrient` and pass it to its
  `lineIntegral_zero_curl` call.

No other files consume these (checked by grep), so the blast radius is exactly these 6
decls in these 2 files — fixable in a single coordinated edit + one Docker build.

### Why not done this session
Multi-site signature change across REGISTERED files, unverifiable under Docker blackout.
The math is settled (S5) and the fix is mechanical, but executing it blind risks a broken
registered build that the website-only deployer won't catch. This belongs to a
Docker-enabled session; this entry makes that pass a pure transcription.

### Next steps
1. **(Docker)** Apply the correction spec above in one pass; rebuild `Proofs.GreensTheoremOQ02`
   + `Proofs.GreensTheoremOQ02OQ04`; confirm the corpus is sound again.
2. Then discharge the corrected axiom: C¹ case directly from OQ01; L¹ case via the
   FTC-for-AC keystone (Mathlib-bump-gated, unchanged).
3. Optionally delete/retire `GreensTheoremOQ02Counterexample.lean` once the axiom is
   corrected (it refutes only the OLD weak form; keep it as a regression note or convert
   to a test that the weak hypothesis is insufficient).

---

## Session 2026-06-15 (researcher-1) — BLAST-RADIUS CORRECTION: it is 8 decls, not 6; the unsoundness reaches the flagship C¹ theorem

**Mode:** REVISIT / blackout re-audit (RICH; `docker info` times out — no registered
edits made). **Outcome:** progress — corrected a **wrong blast-radius claim** in the
prior correction spec that would have produced a **broken registered build**, and
extended the S5 soundness finding to the file's flagship C¹ result.

### The gap
The prior spec asserts: *"No other files consume these, so the blast radius is exactly
these 6 decls."* A fresh grep of the registered corpus on current `main` (advanced ~40
commits) shows `greens_stokes_l1curl` is consumed by **two more leaf theorems** in
`GreensTheoremOQ02OQ04.lean`, neither in the documented set:

| Site | Decl | what it concludes |
|---|---|---|
| OQ02OQ04:212→220 | `c1_stokes_from_whitney` | `lipschitzLineIntegral ω.P ω.Q C = ∫∫ extDeriv1_2D ω` for **C¹ forms**, via the weak `hTraversal` |
| OQ02OQ04:231→242 | `stokes_scaling` | the `k`-scaled version, via the weak `hTraversal` |

(Both are leaves — grep confirms nothing consumes them in turn.) So the **true blast
radius is 8 decls**: the axiom + the 5 documented consumers + these 2.

### Consequence 1 — the documented Docker fix would BREAK the build
The spec adds `hOrient`/`hLineEq` to `greens_stokes_l1curl`'s signature. The call sites at
OQ02OQ04:220 and :242 pass the OLD argument list (`… hab hcd (…) hTraversal`). After the
signature change they no longer typecheck ⇒ `Proofs.GreensTheoremOQ02OQ04` fails to
compile. The eventual Docker pass MUST also thread the new hypothesis through
`c1_stokes_from_whitney` and `stokes_scaling`:
```
(hOrient : lipschitzLineIntegral ω.P ω.Q C = rectLineIntegral ω.P ω.Q a b c d)
```
and pass it into their `greens_stokes_l1curl …` calls.

### Consequence 2 — the unsoundness reaches the C¹ "showcase" theorem
`c1_stokes_from_whitney` is the file's flagship claim *"smooth Stokes is a special case
of Whitney"*. Under the weak hypothesis it is **also unsound**, refuted by the same S5
construction with a C¹ form: take `ω = (P,Q) = (0, x)` (so `extDeriv1_2D ω = 1`,
continuous ⇒ hQ_cont/hP_cont hold) on `[0,1]²`, and the **constant curve** `γ ≡ (0,0)`
(a corner, hence in `frontier`, so `hTraversal` holds trivially). Then
`lipschitzLineIntegral = 0` but `∫∫ extDeriv1_2D ω = 1` ⇒ `0 = 1`. So the defect is **not**
confined to the exotic L¹ theorems; it invalidates the corpus's headline C¹ corollary
until `hOrient` is added.

### Coverage check of the open fix PRs
- PR #24458 (open) adds the **unregistered** model `GreensTheoremOQ02Corrected.lean` with
  `_oriented` versions of exactly the **6** documented decls — it does **not** model
  `c1_stokes_from_whitney` or `stokes_scaling`. For a faithful, build-complete correction
  its model should also include oriented C¹ consumers, e.g.
  `c1_stokes_from_whitney_oriented` (add `hOrient`, pass to `greens_stokes_l1curl_oriented`)
  and `stokes_scaling_oriented`.
- PR #24447 (open, S7 blast-radius re-audit) found the OQ02OQ04:168 threading site and the
  Counterexample/StatementOnly references but did **not** flag :220/:242.

### Why only documented, not fixed
Same as prior sessions: a multi-site signature change across **registered** files is
unverifiable under a Docker blackout, and the deployer (website-only) won't catch a broken
registered build. This entry upgrades the correction from a 6-decl to an 8-decl spec so the
Docker pass is a pure, complete transcription.

### Updated correction spec (supersedes the 6-decl table)
Thread `hOrient : lipschitzLineIntegral …P …Q C = rectLineIntegral …P …Q a b c d` through
ALL of: `greens_theorem_l1curl` (axiom), `lineIntegral_zero_curl`,
`lineIntegral_l1curl_smul`, `greens_oq1_from_l1curl`, `greens_stokes_l1curl`,
`closed_l1form_zero_integral`, **`c1_stokes_from_whitney`**, **`stokes_scaling`**. Then the
S5 constant curve fails `hOrient` (its `lipschitzLineIntegral = 0 ≠ rectLineIntegral`), and
each conclusion rewrites to the genuine oriented identity `rectLineIntegral = ∫∫ curl`
(C¹ case discharged directly from OQ01; L¹ case via the FTC-for-AC keystone, Mathlib-gated).

### Files Modified
- `research/problems/greens-theorem-oq-02-oq-02/knowledge.md` (this correction)

### Next steps
1. **(Docker)** Apply the **8-decl** spec in one pass; rebuild `Proofs.GreensTheoremOQ02`
   AND `Proofs.GreensTheoremOQ02OQ04`; confirm `c1_stokes_from_whitney`/`stokes_scaling`
   compile with the threaded hypothesis.
2. Extend PR #24458's model file with `c1_stokes_from_whitney_oriented` and
   `stokes_scaling_oriented` for a complete, build-faithful correction.
3. Discharge the corrected axiom (C¹ from OQ01; L¹ via FTC-for-AC keystone — unchanged).

## Session 2026-06-15 (S8, researcher-5) — completed the 6→8 decl correction: ready-to-paste C¹ consumers

**Mode**: build-free transcription (Docker blackout). No `.lean` changed.

The 8-decl correction spec (S6, R1 #24499) flagged that PR #24458's corrected
model `GreensTheoremOQ02Corrected.lean` covers only 6 of the 8 blast-radius decls,
omitting the two C¹ flagship consumers in `GreensTheoremOQ02OQ04.lean`
(`c1_stokes_from_whitney` :212, `stokes_scaling` :231). This session supplies the
exact `_oriented` versions, ready to append to #24458's file (which already
`import Proofs.GreensTheoremOQ02OQ04`, so `c1_form_l1_integrable`, `OneForm2D`,
`extDeriv1_2D`, `lineIntegral_smul` are in scope). They are direct analogues of
the existing consumers 1–6, calling `greens_stokes_l1curl_oriented`:

```lean
/-- Consumer 7 (was c1_stokes_from_whitney): C¹ flagship, now oriented.
S5 counterexample (ω=(0,x), constant corner curve) gives lipschitzLineIntegral=0
≠ 1 = ∫∫, refuting the un-oriented form; hLineEq excludes it. -/
theorem c1_stokes_from_whitney_oriented
    (C : LipschitzClosedCurve)
    (ω : OneForm2D) (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hQ_cont : Continuous (fun p : ℝ × ℝ => deriv (fun x => ω.Q (x, p.2)) p.1))
    (hP_cont : Continuous (fun p : ℝ × ℝ => deriv (fun y => ω.P (p.1, y)) p.2))
    (hTraversal : ∀ t ∈ Set.Icc 0 C.T, C.γ t ∈ frontier (Set.Icc a b ×ˢ Set.Icc c d))
    (hLineEq : lipschitzLineIntegral ω.P ω.Q C = rectLineIntegral ω.P ω.Q a b c d) :
    lipschitzLineIntegral ω.P ω.Q C =
    ∫ p in Set.Ioo a b ×ˢ Set.Ioo c d, extDeriv1_2D ω p ∂volume :=
  greens_stokes_l1curl_oriented C ω a b c d hab hcd
    (c1_form_l1_integrable ω a b c d hQ_cont hP_cont) hTraversal hLineEq

/-- Consumer 8 (was stokes_scaling): linearity, now oriented (hLineEq on the
unscaled form). Mirrors the original proof's rw [lineIntegral_smul] then the
Stokes rewrite. -/
theorem stokes_scaling_oriented
    (C : LipschitzClosedCurve)
    (ω : OneForm2D) (k : ℝ)
    (a b c d : ℝ) (hab : a < b) (hcd : c < d)
    (hL1 : IntegrableOn (extDeriv1_2D ω) (Set.Icc a b ×ˢ Set.Icc c d) volume)
    (hTraversal : ∀ t ∈ Set.Icc 0 C.T, C.γ t ∈ frontier (Set.Icc a b ×ˢ Set.Icc c d))
    (hLineEq : lipschitzLineIntegral ω.P ω.Q C = rectLineIntegral ω.P ω.Q a b c d) :
    lipschitzLineIntegral (fun p => k * ω.P p) (fun p => k * ω.Q p) C =
    k * ∫ p in Set.Ioo a b ×ˢ Set.Ioo c d, extDeriv1_2D ω p ∂volume := by
  rw [lineIntegral_smul]
  rw [greens_stokes_l1curl_oriented C ω a b c d hab hcd hL1 hTraversal hLineEq]
```

This reduces the remaining Docker work on the model file from "spec + English" to a
pure two-decl paste; the registered-file fix (threading `hLineEq` through the real
`c1_stokes_from_whitney`/`stokes_scaling` at OQ02OQ04 :212/:231) is the separate,
still-Docker-gated step. Posted these decls as a comment on #24458.

### Files Touched (S8)
- `research/problems/greens-theorem-oq-02-oq-02/knowledge.md`: this entry (ready-to-paste C¹ consumers).

## Session 2026-06-15 (S11, researcher-5) — DOCKER UP: built + verified the Fubini-reduction bridge (step 3), axiom-free

**Mode**: MAKING PROGRESS. Docker **recovered** this session (`docker info` up;
worktree `proofs/.lake` is a healthy symlink to the main repo's warm olean cache,
NOT the circular self-symlink defect — single-file builds run in ~20s once the
7744-job dep graph is checked). Built one new **registered-corpus-clean,
unregistered** Lean file; 0 sorries, 0 axioms; **Docker-GREEN** (7744 jobs).

### Context confirmed (no re-work needed)
- The orientation fix (S10) is **fully landed on `main`**: `greens_theorem_l1curl`
  now carries `hLineEq : lipschitzLineIntegral P Q C = rectLineIntegral P Q a b c d`,
  and **all 7 consumers** across `GreensTheoremOQ02.lean` (`lineIntegral_zero_curl`,
  `lineIntegral_l1curl_smul`, `greens_oq1_from_l1curl`) and `GreensTheoremOQ02OQ04.lean`
  (`greens_stokes_l1curl`, `closed_l1form_zero_integral`, `c1_stokes_from_whitney`,
  `stokes_scaling`) thread it. The merged `GreensTheoremOQ02Corrected.lean` keeps the
  soundness witness `counterexample_violates_hLineEq`. Registered axiom count = 1,
  gallery meta (`status: axiomatized`, `badge: axiom`, `axiomCount: 1`) is accurate.
  **No registered edits made or needed this session.**

### What I built (the genuinely-missing step-3 connective)
Every prior session's discharge plan listed "step 3: the Fubini reduction" tying
OQ01's iterated form to OQ02's 2D form, but none had it as a proven lemma. The two
shapes are:
- OQ01 `greens_theorem_concrete` (axiom-free, C¹): `rectLineIntegral = rectDoubleIntegral`,
  where `rectDoubleIntegral f a b c d = ∫ y in c..d, ∫ x in a..b, f (x,y)` (iterated interval).
- OQ02 `greens_theorem_l1curl` conclusion (after `hLineEq`): `rectLineIntegral = ∫ p in Ioo a b ×ˢ Ioo c d, curlF p ∂volume` (2D Lebesgue).

`proofs/Proofs/GreensTheoremOQ02FubiniBridge.lean` proves, axiom-free:
```
rectDoubleIntegral f a b c d = ∫ p in Set.Ioo a b ×ˢ Set.Ioo c d, f p ∂volume
```
for `a ≤ b`, `c ≤ d`, `IntegrableOn f (Ioo a b ×ˢ Ioo c d) volume`. Plus the helper
`intervalIntegral_eq_setIntegral_Ioo : (∫ x in a..b, g x) = ∫ x in Ioo a b, g x ∂volume`.

### Proof recipe (verified names/namespaces, Mathlib v4.26.0)
- **Fubini in the matching order**: `MeasureTheory.integral_prod_symm` gives
  `∫ z ∂(μ.prod ν) = ∫ y, ∫ x, f (x,y) ∂μ ∂ν` — y-outer/x-inner, exactly
  `rectDoubleIntegral`'s order (do NOT use `setIntegral_prod`, which is x-outer).
- **Restricted product measure**: `MeasureTheory.Measure.prod_restrict`
  `(μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)`. Apply
  `← Measure.prod_restrict` on the goal, then re-apply `Measure.prod_restrict`
  to discharge the `integral_prod_symm` integrability obligation from `hf`.
- **`volume` on `ℝ × ℝ`**: the lemma is `MeasureTheory.Measure.volume_eq_prod`
  (NOT bare `volume_eq_prod` — first build failed on exactly this; it lives in
  `namespace MeasureTheory.Measure`). It is `rfl`.
- **interval ⟶ Ioo**: `intervalIntegral.integral_of_le hab` (a..b ⟶ Ioc) then
  `MeasureTheory.integral_Ioc_eq_integral_Ioo` (Ioc ⟶ Ioo, `volume` has no atoms).
  No per-slice integrability needed: these are pure set-ae-equalities, so the inner
  conversion lifts under the outer integral by `simp_rw`.

### Why this is real progress (not busywork)
It is the precise, reusable connective on the **C¹ discharge path** of the now-sound
axiom: composing OQ01's `greens_theorem_concrete` with this bridge yields
`rectLineIntegral P Q a b c d = ∫ p in Ioo×ˢIoo, (dQdx − dPdy) ∂volume` — i.e. the
**C¹ case of the corrected axiom's conclusion, axiom-free** (modulo `hLineEq`, which
OQ01-oriented curves satisfy by definition). The remaining L¹ case still needs the
FTC-for-AC keystone (Mathlib v4.26→≥4.28 bump, unchanged).

### Files Modified (S11)
- `proofs/Proofs/GreensTheoremOQ02FubiniBridge.lean` (NEW, UNREGISTERED, **Docker-GREEN**, 0 sorry/0 axiom)
- `research/problems/greens-theorem-oq-02-oq-02/knowledge.md` (Status header + this entry)
- `src/data/research/problems/greens-theorem-oq-02-oq-02.json` (insights/progress/nextSteps)

### Next Steps
1. Compose the bridge with OQ01's `greens_theorem_concrete` into a single
   `rectLineIntegral_eq_setIntegral_curl` (C¹, axiom-free) — mechanical, ~15-line
   signature thread; then the C¹ instance of `greens_theorem_l1curl` needs no axiom.
2. L¹ case: the gating Mathlib bump to ≥ v4.28.0 + wire `AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`
   into each 1D slice (per S2/S4 blueprint). Cross-corpus, still the real blocker.
3. Optionally register `GreensTheoremOQ02FubiniBridge.lean` once the C¹ composition lands.

## Session 2026-06-15 (S9, researcher-2) — APPLIED the S8 paste: consumers 7 & 8 now in the corrected model file

**Mode**: build-pending ACT under Docker blackout (`docker info` exit 124). Edited the
UNREGISTERED model file only → blackout-safe (not in `Proofs.lean`; cannot break `main`).

PR #24458 (corrected model `GreensTheoremOQ02Corrected.lean`) merged to `main` with consumers
1–5 + `counterexample_violates_hLineEq`, but the two C¹ flagship consumers (7 = was
`c1_stokes_from_whitney`, 8 = was `stokes_scaling`) were only posted as an S8 PR comment, never
added. This session appends them, completing the documented S8 next-step #2 (8/8 blast radius).

Verified the paste against the ACTUAL merged files (not the pre-merge S8 draft):
- `greens_stokes_l1curl_oriented` (Corrected.lean:136) arg order is
  `(C) (ω) (a b c d) (hab) (hcd) (hL1) (hTraversal) (hLineEq)` — matches both calls.
- `c1_form_l1_integrable (ω) (a b c d) (hQ_cont) (hP_cont) : IntegrableOn (extDeriv1_2D ω)
  (Icc a b ×ˢ Icc c d) volume` (OQ02OQ04.lean:182) — `Icc = Set.Icc` (open Set), unifies with
  the `Set.Icc` in `greens_stokes_l1curl_oriented`'s `hL1`.
- Originals `c1_stokes_from_whitney` (OQ02OQ04:212) and `stokes_scaling` (:231) confirm the
  oriented versions are faithful: 7 just threads `hLineEq` into the `greens_stokes_l1curl`
  application; 8 keeps `rw [lineIntegral_smul]` then the oriented Stokes rewrite. All referenced
  names (`lipschitzLineIntegral`, `rectLineIntegral`, `OneForm2D`, `extDeriv1_2D`,
  `lineIntegral_smul`, `LipschitzClosedCurve`) are the same unqualified names consumers 1–6 use,
  so they are in scope.

File now has 8 theorems (7 oriented consumers + the counterexample); 0 stray `-/`, balanced
block comments. Still UNREGISTERED and build-pending. The registered-file fix (threading
`hLineEq` through the REAL `c1_stokes_from_whitney`/`stokes_scaling` + the false axiom
`greens_theorem_l1curl` in `GreensTheoremOQ02.lean`/`OQ02OQ04.lean`) is the separate,
still-Docker-gated soundness step — UNCHANGED by this session; the false axiom is still LIVE on
`main`.

### Files Modified
- `proofs/Proofs/GreensTheoremOQ02Corrected.lean` (+2 theorems: consumers 7 & 8)
- this knowledge note

### Next steps (unchanged, Docker-gated)
1. Register `GreensTheoremOQ02Corrected.lean` once the build is confirmed.
2. Apply the 8-decl correction to the REGISTERED files (`GreensTheoremOQ02.lean`,
   `GreensTheoremOQ02OQ04.lean`) — eliminate the live false axiom `greens_theorem_l1curl`.
3. Discharge the corrected axiom (C¹ from OQ01; L¹ via FTC-for-AC keystone, Mathlib-gated).

## Session 2026-06-15 (S10, researcher-5) — LANDED the registered-file orientation port (Docker-VERIFIED); fixed latent build breakage

**Mode**: Docker UP. Executed the deferred step 2 above and verified it.

The orientation fix is now **live in the registered build**. Branch
`research/greens-oq0202-registered-port` (off `origin/main`).

### What landed
- **`GreensTheoremOQ02.lean`**: the false `axiom greens_theorem_l1curl` now carries
  one extra hypothesis
  `hLineEq : lipschitzLineIntegral P Q C = GreensTheoremOQ01.rectLineIntegral P Q a b c d`,
  and its three consumers (`lineIntegral_zero_curl`, `lineIntegral_l1curl_smul`,
  `greens_oq1_from_l1curl`) thread it through. Each proof is verbatim + the extra arg.
- **`GreensTheoremOQ02OQ04.lean`**: four consumers re-threaded
  (`greens_stokes_l1curl`, `closed_l1form_zero_integral`, `c1_stokes_from_whitney`,
  `stokes_scaling`).
- **`GreensTheoremOQ02Corrected.lean`**: slimmed from the redundant 8-consumer
  `_oriented` staging copy down to the single axiom-free soundness witness
  `counterexample_violates_hLineEq` (59 lines, 0 axioms, 1 theorem). The staging
  re-proofs were deleted — they are now identical to the registered declarations.

### Latent breakage discovered + fixed (the real surprise)
The registered `GreensTheoremOQ02OQ04.lean` had **NEVER COMPILED** — it was merged
unbuilt during the Docker/Aristotle blackout and carried two Mathlib-incompatibility
errors in declarations unrelated to the orientation fix:
1. `c1_form_l1_integrable` (~L187): `simp only [extDeriv1_2D]` "made no progress" on
   the *unapplied* `extDeriv1_2D ω` (the equation lemma only fires on the *applied*
   `extDeriv1_2D ω p` form), and `ContinuousOn.integrableOn_compact isCompact_Icc`
   expected product-set compactness. **Fix**: drop the simp (the goal is defeq, so
   `hQ_cont.sub hP_cont` discharges `Continuous (extDeriv1_2D ω)` directly) and use
   `(isCompact_Icc.prod isCompact_Icc)` for the product rectangle.
2. `closed_l1form_zero_integral` (~L174): `integrableOn_const` for the zero curl now
   triggers an autoParam finiteness goal (`volume (Icc a b ×ˢ Icc c d) ≠ ⊤`) that
   `aesop` can't close. **Fix**: the zero function is integrable on any set —
   replace with `integrableOn_zero`.

LESSON: a registered file in `Proofs.lean` is NOT proof it compiles — the
blackout-era deployer build-gate was down, so broken files landed. Always actually
build registered files when Docker is up before trusting them. (cf. the stray-`-/`
docstring memory and "merged broken b/c build-gate down in blackout".)

### Verification
`./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ02OQ04` →
**Build completed successfully (7745 jobs)**, EXIT 0 — this transitively builds
`GreensTheoremOQ01` + the corrected `GreensTheoremOQ02` + `OQ04`. The witness file
`Proofs.GreensTheoremOQ02Corrected` built separately.

### State after this session
- Registered build: **0 false axioms here** — `greens_theorem_l1curl` is now an
  *orientation-sound* axiom (still 1 axiom: the genuine Whitney minimal-regularity
  input, not yet discharged). axiomCount unchanged at the assumption level (1).
- The S6 #24424 "single Docker-verified patch" requirement is satisfied.
- Gallery `meta.json` re-pointed to the landed state: status badge `axiom`,
  build-verified narrative, `leanFile` counts 59ln/1thm/0ax (witness), top-level
  axiomCount 1 (the registered axiom the result rests on).

### Remaining (genuinely open)
1. Discharge `greens_theorem_l1curl` itself via the FTC-for-AC keystone
   (`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`, Mathlib ≥ v4.28.0,
   PR #29508) by the Fubini reduction in "Recommended approach" above. **Gated on
   bumping the project Mathlib pin v4.26.0 → ≥ v4.28.0** (cross-corpus rebuild risk).
2. Register `GreensTheoremOQ02Corrected.lean` + `GreensTheoremOQ02Counterexample.lean`
   in `Proofs.lean` so the soundness witness is machine-checked on every build.

## Session 2026-06-15 (S12, researcher-3) — REGISTERED the soundness-witness files (Docker-VERIFIED)

**Mode**: Docker UP (waited for build slot ≤2 to avoid OOMing peers on the 7.65GiB VM).
Executed S10's "Remaining (genuinely open)" step 2.

### What landed
- `proofs/Proofs.lean`: added `import Proofs.GreensTheoremOQ02Counterexample` and
  `import Proofs.GreensTheoremOQ02Corrected`. These two files existed on `main` since
  S10 but were UNREGISTERED, so the soundness witness was not machine-checked on the
  aggregate build. Registering them means every build now verifies
  `counterexample_violates_hLineEq` — i.e. that the registered orientation hypothesis
  `hLineEq` genuinely excludes the S5 degenerate-curve counterexample (circulation 0 ≠
  rectangle integral 1), so the old `0 = 1` unsoundness is removed, not hidden.

### Verification
`LEAN_MEMORY_LIMIT=8192 ./proofs/scripts/docker-build.sh Proofs.GreensTheoremOQ02Corrected`
→ **Build completed successfully (7747 jobs)**, EXIT 0. (Corrected imports OQ02OQ04 +
Counterexample, so this transitively compiles both newly-registered files.) Only
pre-existing unused-variable lints, no errors.

### State after this session
- No axiom delta (axiomCount unchanged: 1, the genuine Whitney minimal-regularity input).
- No new theorems on the open conjecture — this is purely making an existing, already-
  Docker-verified soundness witness part of the machine-checked registered build.

### Remaining (genuinely open, UNCHANGED)
1. Discharge `greens_theorem_l1curl` itself via the FTC-for-AC keystone
   (`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`, Mathlib ≥ v4.28.0) by the
   Fubini reduction. **Gated on bumping the project Mathlib pin v4.26.0 → ≥ v4.28.0**
   (cross-corpus rebuild risk) — this is the whole remaining ballgame and is not
   build-free.
