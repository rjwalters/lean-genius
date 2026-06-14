# greens-theorem-oq-02-oq-02

**Question**: Can the Whitney axiom be proved in Lean using Mathlib's existing `BoundedVariation` and `MeasureTheory.Measure.AbsolutelyContinuous` API?

**Source**: open question on `greens-theorem-oq-02` (Green's Theorem: Minimal Regularity — Lipschitz Curves and L¹ Curl)

**Status**: surveyed (ORIENT) — feasibility analyzed, blocker narrowed and corrected, bounded build path identified. No Lean committed (Docker blackout 2026-06-13).

## Summary

The target axiom is `greens_theorem_l1curl` (`proofs/Proofs/GreensTheoremOQ02.lean:350`). The OQ asks whether it is dischargeable via Mathlib's `BoundedVariation` + `Measure.AbsolutelyContinuous` API.

**Answer: those APIs are necessary but not sufficient.** The whole question reduces to one missing keystone — the **function-level FTC for absolutely continuous functions**: `f` AC on `[a,b]` ⟹ `f b − f a = ∫ x in a..b, deriv f x` with `deriv f` only L¹/a.e.-defined. Mathlib's `FundThmCalculus` provides only continuity / `HasDerivAt`-everywhere versions and does **not** have this Lebesgue/AC direction.

## Key reframing (the main finding)

The axiom's own docstring justifies axiomatization by claiming the proof "requires geometric measure theory machinery (sets of finite perimeter, BV functions, Federer's trace theorem, Gauss-Green formula) not yet assembled in Mathlib." **This is an overstatement for the case actually stated.** The axiom's domain is a **rectangle** `Set.Icc a b ×ˢ Set.Icc c d`, with the curve `C` a Lipschitz parametrization of its frontier (`hTraversal`). The geometric domain is simple; the heavy GMT machinery is needed for general Lipschitz *domains*, not here.

The genuine gap versus the **axiom-free** OQ01 (`GreensTheoremOQ01.lean`, 0 axioms, uses pointwise `HasDerivAt` + `intervalIntegral.integral_eq_sub_of_hasDerivAt`) is precisely the weakening from pointwise-C¹ partials to an **a.e. curl with merely L¹ integrability** (`hCurlAE` + `hL1`). Via Fubini (`MeasureTheory.integral_prod`) the rectangle double integral splits into iterated 1D integrals, each needing FTC for a function whose derivative is only L¹ — i.e. FTC-for-AC.

So the true blocker is a **bounded ~200–400 line local build**, not a 1000+ line foundational GMT project.

## What Mathlib has vs. lacks

| Ingredient | Mathlib status |
|---|---|
| FTC (continuity / `HasDerivAt` everywhere) | ✅ `Mathlib.MeasureTheory.Integral.FundThmCalculus` |
| **FTC-for-AC** (`f b − f a = ∫ f'`, L¹ deriv) | ❌ **missing — the keystone** |
| BoundedVariation (`eVariationOn`, BV ⟹ a.e. diff) | ✅ `Mathlib.Analysis.BoundedVariation` |
| Rademacher (Lipschitz ⟹ a.e. diff) | ✅ `Mathlib.Analysis.Calculus.Rademacher` |
| Measure `AbsolutelyContinuous` + Radon-Nikodym | ✅ `Mathlib.MeasureTheory.Decomposition.RadonNikodym` |
| Fubini (`integral_prod`) | ✅ |

Note: `Measure.AbsolutelyContinuous` is AC of **measures** (μ ≪ ν), not of functions. The OQ's intended route — model the L¹ curl as the RN-derivative of an AC measure and recover boundary values — still bottlenecks on the same function-level FTC bridge.

## Recommended approach (when Docker restored)

1. Build a self-contained `ftc_of_absolutelyContinuous` lemma (≤400 lines). Likely route: `f` AC ⟹ its Lebesgue-Stieltjes signed measure `≪ volume` ⟹ `deriv f` is its Radon-Nikodym derivative ⟹ integrate (`withDensity` / RN lemmas).
2. Discharge `greens_theorem_l1curl` by Fubini reduction to two 1D FTC-for-AC applications over the rectangle, reusing OQ01's boundary algebra.
3. Amend the OQ02 axiom docstring to state the accurate narrowed gap (doc-only follow-up).
4. Sanity check: must recover OQ01's conclusion when the curl comes from genuine `HasDerivAt` partials (matches existing `greens_oq1_from_l1curl`).

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
