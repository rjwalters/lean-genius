# prob-method-second-moment-oq-02 — S1c OBSERVE: Paley-Zygmund Mathlib-gap correction

**Date**: 2026-05-12 (UTC night → 2026-05-13)
**Author**: researcher-11
**Scope**: doc-only sub-step of S1b OBSERVE (PR #18429). The S1b audit claimed "search for `paleyZygmund` in Mathlib" as a load-bearing reduction for §9 of the S2 ACT plan (`triangle_supercritical` Paley-Zygmund). Direct `gh api search/code` confirms **`paleyZygmund` does NOT exist in Mathlib** (0 hits). This correction reframes the S2 ACT scope and identifies alternative routes.

**No Lean source changes**, no `meta.json` / `problem.md` / `knowledge.md` / `state.md` / gallery-JSON edits. The only file added is this sessions/* document.

## Audit finding 1 — Paley-Zygmund inequality is missing from Mathlib

The S1b OBSERVE (PR #18429, lines 184–186 in the merged session note) states:

> Paley-Zygmund (search for `paleyZygmund` in Mathlib).

This was unverified at the time. Direct verification via `gh api search/code -f q='repo:leanprover-community/mathlib4 "paleyZygmund"'` returns **0 hits**. Mathlib v4.26.0 has **no implementation of the Paley-Zygmund inequality**. The names `paleyZygmund`, `paley_zygmund`, `PaleyZygmund`, and `Paley_Zygmund` were all spot-checked; none appear.

This contradicts the S1b table's "~50 LOC, -30 LOC savings via Paley-Zygmund + cliqueFinset" projection for `triangle_supercritical` (§ 9 of the revised S2 plan).

## Audit finding 2 — Other Mathlib API claims from S1b confirmed

For honesty, the following S1b claims **were verified**:

| S1b claim | Verification | Status |
|---|---|---|
| `PMF.bernoulli` at `Constructions.lean` | `def bernoulli` found in `Mathlib/Probability/ProbabilityMassFunction/Constructions.lean` | ✅ |
| `PMF.bind`, `PMF.toMeasure_bind_apply` at `Monad.lean` | `def bind` found in `Mathlib/Probability/ProbabilityMassFunction/Monad.lean` | ✅ |
| `ProbabilityTheory.variance` at `Moments/Variance.lean` | `def variance` found in `Mathlib/Probability/Moments/Variance.lean` | ✅ |
| `SimpleGraph.cliqueFinset` at `Clique.lean` | `def cliqueFinset` found in `Mathlib/Combinatorics/SimpleGraph/Clique.lean` | ✅ |
| `PMF.binomial` (S1b implicit; verified independently) | `def binomial` at `Mathlib/Probability/ProbabilityMassFunction/Binomial.lean:25` | ✅ (bonus finding — see below) |
| **Paley-Zygmund inequality** | 0 hits in Mathlib v4.26.0 | ❌ |

So 5 of 6 spot-checked claims hold; the one that fails is the load-bearing one for § 9 of the S2 plan.

## Audit finding 3 — `PMF.binomial` does exist (bonus)

`Mathlib/Probability/ProbabilityMassFunction/Binomial.lean` (Joachim Breitner, 2023) provides:

```lean
namespace PMF

def binomial (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : PMF (Fin (n + 1)) :=
  .ofFintype (fun i =>
    ↑(p ^ (i : ℕ) * (1 - p) ^ ((Fin.last n - i) : ℕ) * (n.choose i : ℕ))) (by …)

theorem binomial_one_eq_bernoulli (p : ℝ≥0) (h : p ≤ 1) :
    binomial p h 1 = (bernoulli p h).map (cond · 1 0) := by …

end PMF
```

This is the **head-count distribution** of `n` independent Bernoulli trials, not the joint subset distribution. **It does NOT directly give G(n, p) over `Finset (EdgeIdx n)`** — which is the goal of S1b § 3.4. To get the joint subset PMF from the binomial head-count, one would need an extra "uniform over `(n choose k)`-subsets given k heads" step:

$$\Pr[\mathrm{edges} = E] = \Pr[|\mathrm{edges}| = |E|] \cdot \frac{1}{\binom{n}{|E|}}.$$

This is two PMF compositions: one binomial (for the count) and one uniform (over equal-count subsets). Each is in Mathlib (`PMF.binomial` + `PMF.uniformOfFinset`), so this route is well-formed but slightly more involved than the S1b sketch (~10 extra LOC for the uniform step).

## Audit finding 4 — `Finset.foldr` + PMF requires `LeftCommutative`

The S1b § 3.4 sketch uses:

```lean
noncomputable def gnp_edges (p : ℝ≥0) (hp : p ≤ 1) :
    PMF (Finset (EdgeIdx n)) :=
  Finset.univ.foldr
    (fun e q => (PMF.bernoulli p hp).bind (fun b =>
      q.map (if b then Finset.insert e else id)))
    (PMF.pure ∅)
```

Mathlib's `Finset.foldr` (in `Mathlib/Data/Finset/Fold.lean`) requires a `LeftCommutative` instance for the folding function — i.e., `f a (f b x) = f b (f a x)` for all `a, b, x`. A `LeftCommutative` instance is **not free** for the PMF-bind composition: it must be proved manually as a `PMF`-equality, which reduces to the independence + commutativity of `PMF.bernoulli` instances. The proof is non-trivial (the standard "product measure is commutative" result, but in PMF/monad form).

`gh api search/code` returns **0 hits** for `LeftCommutative` under `path:Probability` in Mathlib, suggesting no off-the-shelf `LeftCommutative` instance exists for PMF-bind. The S2 ACT will need to either:

- (a) **Prove the `LeftCommutative` instance** locally (~20-40 LOC; uses `PMF.bind_bind` and Bernoulli independence).
- (b) **Use a different construction**: e.g., `PMF.ofFintype` directly with the joint probability `p ^ |E| * (1 - p) ^ (N - |E|)` for `E : Finset (EdgeIdx n)` (where `N = Fintype.card (EdgeIdx n)`). This requires a `sum = 1` proof, which reduces to `(p + (1 - p)) ^ N = 1` via `Finset.sum_pow_mul_pow` or the binomial theorem.
- (c) **Drop to Measure-level** and use `MeasureTheory.Measure.pi` for the product measure construction; then the entire framework lives in `Mathlib.MeasureTheory` without PMF intermediate steps.

Route (b) is the cleanest. Estimated ~15 LOC including the `sum = 1` proof, using `Finset.sum_pow_mul_pow_eq_pow_card` or hand-rolling via `Finset.binomial_sum`.

## Audit finding 5 — Revised S2 ACT scope (S1c update)

The S1b "~250 LOC, 0 sorries" estimate (down from S1's ~350) banks on Paley-Zygmund in Mathlib. With Paley-Zygmund **absent**, the corrected estimate:

| Component | S1 (no audit) | S1b (Paley-Zygmund OK) | **S1c (this PR)** | Note |
|---|---|---|---|---|
| `indicatorSum_variance` (generic) | ~80 | ~50 | ~50 | unchanged from S1b |
| `subgraphCount_variance` (triangle) | ~80 | ~50 | ~50 | unchanged from S1b |
| `gnp` PMF definition | ~30 | ~25 | **~30** | +5 (LeftCommutative proof OR PMF.ofFintype detour) |
| `triangle_subcritical` (Markov) | ~50 | ~50 | ~50 | unchanged |
| `triangle_supercritical` | ~80 | ~50 | **~120** | **+70**: prove Paley-Zygmund inline OR axiomatize it |
| Glue, namespaces | ~30 | ~25 | ~25 | unchanged |
| **Total** | ~350 | ~250 | **~325** | -25 vs S1, +75 vs S1b |

Net: the S1b "~29% reduction" claim collapses to "~7% reduction" once the Paley-Zygmund Mathlib gap is reckoned with. The cliqueFinset + variance API savings are real (~60 LOC), but they are partially offset by the Paley-Zygmund inline proof (~70 LOC if proved; or a +1 axiom if axiomatized).

## Audit finding 6 — Paley-Zygmund inline proof strategy

If S2 ACT proves Paley-Zygmund inline (avoiding the +1 axiom), the standard route is:

> **Paley-Zygmund**: For a non-negative random variable `X` with finite second moment and `0 ≤ θ ≤ 1`:
> $$P(X > \theta \cdot E[X]) \ge (1 - \theta)^2 \cdot \frac{(E[X])^2}{E[X^2]}.$$

Proof: Cauchy-Schwarz applied to `X · 1_{X > θE[X]}` and the second moment. Mathlib has:
- `MeasureTheory.integral_mul_le_Lp_mul_Lq` (Cauchy-Schwarz / Hölder for integrals) — verified location: `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean` (was at `Mathlib/Analysis/MeanInequalities.lean` in older revs).
- `ProbabilityTheory.integral_eq_*` for the expectation manipulations.

Estimated inline proof: ~70 LOC. The bottleneck is the Cauchy-Schwarz step in PMF/measure form.

Alternative — **axiomatize Paley-Zygmund** as a +1 axiom:

```lean
/-- Paley-Zygmund inequality (axiomatized; standard textbook result, not in Mathlib). -/
axiom paley_zygmund_pmf (q : PMF Ω) (X : Ω → ℝ) (hX : ∀ ω, 0 ≤ X ω) (θ : ℝ) (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (h2 : ∫ ω, X ω ^ 2 ∂q.toMeasure < ⊤) :
    q.toMeasure {ω | X ω > θ * ∫ ω', X ω' ∂q.toMeasure}
      ≥ ENNReal.ofReal ((1 - θ) ^ 2 * (∫ ω, X ω ∂q.toMeasure) ^ 2 / ∫ ω, X ω ^ 2 ∂q.toMeasure)
```

Adds +1 axiom but saves ~70 LOC. Tradeoff: the `status` becomes `"axiomatized"` (per CLAUDE.md axiom integrity policy) and the parent's `prob-method-second-moment.meta.json:axiomCount` increments. Acceptable if explicitly declared.

**Recommendation**: S2 ACT should axiomatize Paley-Zygmund for the first PR (faster to land), then a future "axiom-elimination" S3 PR can prove it from `MeasureTheory.integral_mul_le_Lp_mul_Lq`. This mirrors the project's pattern with `conic_implies_pascal_constraint` in `pascals-hexagon` (axiomatized first, eliminated later).

## Implications for the S2 plan

The S1b plan in `2026-05-12-s1b-mathlib-clique-pmf-audit.md` § 6 outlines 10 sections. S1c updates two of them:

- § 3: `gnp` PMF — switch from `Finset.foldr` to `PMF.ofFintype` to avoid the `LeftCommutative` proof obligation (saves ~10-20 LOC, removes one technical gap).
- § 9: `triangle_supercritical` — choose between (a) inline Paley-Zygmund proof (~70 LOC, 0 axioms) or (b) axiomatized Paley-Zygmund (~20 LOC, +1 axiom). Both routes are viable.

Net effect: the S2 ACT is **still tractable in a single PR** (~325 LOC, 0-1 axioms), but the LOC and axiom budgets need to reflect the actual Mathlib state, not the S1b's unverified projection.

## Race awareness

At session time:
- `gh pr list --repo rjwalters/lean-genius --state open --search "prob-method-second-moment-oq-02"`: 0 hits.
- `gh pr list --repo rjwalters/lean-genius --state merged --search "prob-method-second-moment-oq-02"` (most recent): PR #18295 (S1, 2026-05-12T23:51 UTC), PR #18429 (S1b, 2026-05-13T02:07 UTC).
- This S1c is approximately 30 minutes post the S1b merge — fits the "30-min-post-merge MODERATE+/RICH PREP" pattern (memory: researcher-6 quadruple-PREP and post-S1/S1b cluster).

## Sorry / axiom delta projection

- This PR (S1c): **0 sorries, 0 axioms, 0 Lean lines.**
- Recommended S2 ACT (axiomatized Paley-Zygmund route): 0 sorries, **+1 axiom** (`paley_zygmund_pmf`), ~325 LOC.
- Alternative S2 ACT (inline Paley-Zygmund route): 0 sorries, 0 axioms, ~395 LOC.

## Anti-targets

This PR does NOT:
- Modify any Lean source file (no `proofs/Proofs/ProbMethodSecondMomentOQ02.lean` exists yet — S2 ACT is still pending).
- Modify `problem.md`, `knowledge.md`, `state.md`, `meta.json`, or the gallery JSON.
- Touch the parent file `proofs/Proofs/ProbMethodSecondMoment.lean` or its meta.
- Touch the S1b sessions/* file (`2026-05-12-s1b-mathlib-clique-pmf-audit.md`) — that document stands as the merged record; this S1c is an additive correction in a new file.

## Honest scope guarantee

The audit findings 1–6 are based on:
- (1) `gh api search/code -f q='repo:leanprover-community/mathlib4 "paleyZygmund"'` (and variant spellings) returning 0 hits. Verified at session time (2026-05-13 ~02:25 UTC, before GitHub API rate-limiting kicked in).
- (2) Spot-checks of the other 5 S1b claims via `gh api search/code`. All confirmed.
- (3) Direct read of `Mathlib/Probability/ProbabilityMassFunction/Binomial.lean` via `gh api repos/leanprover-community/mathlib4/contents/...` (full source decoded from base64).
- (4) Cross-reference between `Finset.foldr` requirements and the absence of `LeftCommutative` instances under `path:Probability`.
- (5) LOC estimates updated to reflect the Paley-Zygmund gap quantitatively.
- (6) Standard Cauchy-Schwarz proof outline; estimated LOC drawn from analogous PMF/measure-level proofs in Mathlib.

No Lean build was attempted. No code changes were made.

## Differentiation from PR #18429 (S1b OBSERVE)

| Aspect | S1b (#18429) | S1c (this PR) |
|---|---|---|
| Paley-Zygmund in Mathlib | "search for `paleyZygmund` in Mathlib" (unverified) | **Verified absent (0 hits)** |
| `PMF.bernoulli`, `variance`, `cliqueFinset` | Audited | Re-verified ✅ |
| `Finset.foldr` + `LeftCommutative` for `gnp_edges` | Unaddressed | Flagged; alternative `PMF.ofFintype` route proposed |
| `PMF.binomial` (Joachim Breitner 2023) | Not mentioned | Cataloged as bonus (head-count only; not joint subset) |
| S2 LOC budget | ~250 (29% reduction) | **~325 (7% reduction)** — Paley-Zygmund eats most of the savings |
| Axiom count | 0 | 0 or 1 (Paley-Zygmund axiomatization choice) |
| File changes | 1 new sessions/* | 1 new sessions/* (this PR) |

This S1c is **orthogonal by construction** to S1b: different file path, no overlapping content. The corrections are additive — the S1b record stands; this S1c quantifies its corrections in a follow-up document.

## What this PR provides for the next researcher

The next agent picking up `prob-method-second-moment-oq-02` should:

1. Read PR #18295 (S1 OBSERVE) for the framing.
2. Read PR #18429 (S1b) for the Mathlib `cliqueFinset` + `variance` + `PMF.bernoulli` infrastructure.
3. Read this S1c for the **Paley-Zygmund gap correction** (the critical-load-bearing one).
4. Choose between:
   - **S2-A** (axiomatize Paley-Zygmund): ~250 LOC + 1 axiom. Faster.
   - **S2-B** (inline Paley-Zygmund from Cauchy-Schwarz): ~320 LOC + 0 axioms. Stronger.
5. For § 3 (the `gnp` PMF), use `PMF.ofFintype` with binomial-coefficient formula, not `Finset.foldr` — avoids the `LeftCommutative` instance burden.
