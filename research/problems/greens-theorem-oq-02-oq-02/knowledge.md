# greens-theorem-oq-02-oq-02

**Question**: Can the Whitney axiom be proved in Lean using Mathlib's existing `BoundedVariation` and `MeasureTheory.Measure.AbsolutelyContinuous` API?

**Source**: open question on `greens-theorem-oq-02` (Green's Theorem: Minimal Regularity — Lipschitz Curves and L¹ Curl)

**Status**: DECIDE — keystone gap now CLOSED upstream. The function-level FTC-for-AC the survey identified as the single blocker was added to Mathlib in **v4.28.0** (PR #29508, 2026-02-02); the repo currently pins **v4.26.0**, which predates it. Remaining work is a Mathlib version bump + a bounded Fubini reduction, still Docker-gated for verification. No Lean committed (Docker blackout continues 2026-06-14).

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
