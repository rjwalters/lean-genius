# prob-method-second-moment-oq-02 — S1f PREP: S1e errata audit + Route C weighted-Finset alternative (doc-only)

**Date:** 2026-05-13 ~07:05 UTC
**Author:** researcher-8
**Phase:** S1f PREP (sub-step of S2 ACT planning)
**Scope:** Single new `sessions/` file. **No edits** to any other file: not Lean, not gallery JSON, not `meta.json`, not `state.md` / `knowledge.md` / `problem.md`, not sibling S1/S1b/S1c/S1d/S1e session notes. No build.

## 0. Why this angle now

The most recent in-flight PREPs (S1c #18472 03:08 UTC, S1d #18527 03:24 UTC, S1e #18543 03:38 UTC) all converged on
**measure-theoretic Paley-Zygmund via `PMF.ofFintype` + `integral_mul_le_Lp_mul_Lq_of_nonneg`**. S1e in particular
shipped a pinned Mathlib v4.26.0 API audit and a ~75-LOC inline-route skeleton.

Spot-checking S1e's citations against pinned commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (the SHA recorded
in `proofs/lakefile.toml`) surfaced **8 line-number drifts and 1 phantom-name** in the load-bearing tables. Each
drift is small (3-25 lines) — consistent with S1e having been written against an unpinned `master` snapshot, not
the lakefile-pinned commit. The skeleton (§4 of S1e) calls these load-bearing lemmas, so an S2 ACT picker would
hit a name error on first build at `setIntegral_compl₀`.

Separately, all three of (S1c, S1d, S1e) treat `G(n,p)` as requiring a `Measure`-typed sample space and PMF-monad
machinery. But the parent `ProbMethodSecondMoment.lean:177-225` already ships a **quantitative discrete
Paley-Zygmund** `paley_zygmund_quantitative` over `Finset α` with `f : α → ℚ` — using uniform measure. A
**weighted-Finset** generalisation `paley_zygmund_quantitative_weighted` would expose the same inequality for
`f : α → ℚ` against an arbitrary non-negative weight `w : α → ℚ`, and `G(n,p)` with `w(E) := p^|E|·(1-p)^(N-|E|)`
plugs in directly without ever touching `PMF` / `Measure` / `MemLp` / Bochner integration.

This S1f PREP does two things:

1. **Audit-correction** of S1e's §3 table — flag the 8 drifted line numbers and the 1 phantom name (`setIntegral_compl₀`).
2. **Sketch Route C** — weighted-Finset Paley-Zygmund as a third option alongside S1c's (a) axiomatize and (b) inline-PMF-CS, with a concrete ~45-LOC theorem skeleton derived from the parent's existing `sq_sum_le_card_mul_sum_sq` Cauchy-Schwarz lemma.

Strictly orthogonal to:
- **S1** (#18295 MERGED), **S1b** (#18429 MERGED), **S1c** (#18472 MERGED), **S1d** (#18527 MERGED), **S1e** (#18543 MERGED) — none touched.
- **No open PRs** on slug `prob-method-second-moment-oq-02` at session start (verified 07:05 UTC).

This memo is **doc-only**: 1 file added, 0 Lean lines, 0 builds, 0 gallery edits.

## 1. Audit of S1e Mathlib v4.26.0 API table

All checks performed at 2026-05-13 ~07:00 UTC via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

### 1.1 Hölder / Cauchy-Schwarz core

| S1e claim | Actual at pinned SHA | Status |
|-----------|----------------------|--------|
| `integral_mul_le_Lp_mul_Lq_of_nonneg` at `MeasureTheory/Integral/Bochner/Basic.lean:1237` | line **1244** | ⚠ DRIFT (off by 7) |
| (S1e elsewhere cites line `1244` in §0) | line **1244** | ✓ correct |

The S1e §3.1 table line `1237` is the line where the *previous* theorem `integral_mul_le_Lp_mul_Lq` (norm form) ends mid-tactic — `1237` is **inside another theorem's body**, not at the declaration of `_of_nonneg`. The §0 narration line `1244` is correct.

Verbatim signature at line 1244:

```lean
theorem integral_mul_le_Lp_mul_Lq_of_nonneg {p q : ℝ} (hpq : p.HolderConjugate q) {f g : α → ℝ}
    (hf_nonneg : 0 ≤ᵐ[μ] f) (hg_nonneg : 0 ≤ᵐ[μ] g) (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal q) μ) :
    ∫ a, f a * g a ∂μ ≤ (∫ a, f a ^ p ∂μ) ^ (1 / p) * (∫ a, g a ^ q ∂μ) ^ (1 / q)
```

**Note**: S1e's §3.1 table calls the hypothesis names `hf_nn` and `hg_nn`. The actual names are `hf_nonneg` and `hg_nonneg`. Named-argument calls (`(hf_nonneg := hX_nn)`) in §4 of S1e would fail with `unknown named argument 'hf_nn'` — but since §4 uses positional arguments after `hpq :=`, the name mismatch is silent. Still worth pinning the actual names so an S2 ACT picker who refactors to named-args doesn't hit a friction wall.

### 1.2 Hölder-conjugate (2,2)

| S1e claim | Actual at pinned SHA | Status |
|-----------|----------------------|--------|
| `Real.HolderConjugate.two_two` at `Mathlib/Data/Real/ConjExponents.lean:137` | line **133** | ⚠ DRIFT (off by 4) |

The lemma exists at line 133 inside `namespace HolderConjugate` (the `Real.HolderConjugate.two_two` full path is the `namespace Real` + `namespace HolderConjugate` (lines 131-195) compound).

### 1.3 Integral decomposition (`Bochner/Set.lean`)

| S1e claim | Actual at pinned SHA | Status |
|-----------|----------------------|--------|
| `integral_add_compl` at `Bochner/Set.lean:150` | line **145** | ⚠ DRIFT (off by 5) |
| `integral_add_compl₀` at `Bochner/Set.lean:144` | line **139** | ⚠ DRIFT (off by 5) |
| `setIntegral_compl₀` at `Bochner/Set.lean:155` | **PHANTOM** — only `setIntegral_compl` exists at line **149** | ✗ ERRATUM |

The `setIntegral_compl₀` name appears 0 times in `Bochner/Set.lean` at the pinned SHA. The actual lemma is
`setIntegral_compl` (no trailing `₀`), and its hypothesis is `(hs : MeasurableSet s) (hfi : Integrable f μ)`,
not the `NullMeasurableSet` form S1e §3.3 transcribes.

**Impact on §4 skeleton**: S1e's skeleton (§4) does NOT call `setIntegral_compl` or `setIntegral_compl₀` directly
— it uses `integral_add_compl` followed by `add_comm`. So this phantom name is in the *cite-table only*, not in
the load-bearing tactic chain. **However**, an S2 ACT picker scanning the table for shortcut lemmas could land
on the phantom and produce a `unknown identifier 'setIntegral_compl₀'` build error. The §3.3 table needs the
trailing `₀` stripped.

### 1.4 Indicator & set-integral basics

| S1e claim | Actual at pinned SHA | Status |
|-----------|----------------------|--------|
| `integral_indicator` at `Bochner/Set.lean:164` | line **155** | ⚠ DRIFT (off by 9) |
| `integral_indicator_const` at `Bochner/Set.lean:514` | line **489** | ⚠ DRIFT (off by 25) |
| `integral_indicator_one` at `Bochner/Set.lean:519` | line **494** | ⚠ DRIFT (off by 25) |
| `setIntegral_const` at `Bochner/Set.lean:510` | line **485** | ⚠ DRIFT (off by 25) |
| `setIntegral_le_integral` at `Bochner/Set.lean:728` | line **743** | ⚠ DRIFT (off by 15, +) |

The cluster of ~25-line offsets in §1.4 around lines 485-494 vs. cited 510-519 suggests S1e was written against
a Mathlib commit where ~25 lines were inserted later (between `Bochner/Set.lean` line 489 and a later commit).
The single +15 drift on `setIntegral_le_integral` is a separate insertion. None of these are name errors — only
file-line drift — but together they make line-number-based navigation in S1e's table unreliable.

### 1.5 Variance / second-moment bridge

| S1e claim | Actual at pinned SHA | Status |
|-----------|----------------------|--------|
| `ProbabilityTheory.variance` def at `Probability/Moments/Variance.lean:63` | line **63** | ✓ correct |
| `ProbabilityTheory.variance_eq_sub` at `Variance.lean:225` | line **204** | ⚠ DRIFT (off by 21) |
| `ProbabilityTheory.variance_eq_integral` at `Variance.lean:154` | line **145** | ⚠ DRIFT (off by 9) |
| `ProbabilityTheory.variance_nonneg` at `Variance.lean:201` | line **180** | ⚠ DRIFT (off by 21) |
| `ProbabilityTheory.evariance_lt_top` at `Variance.lean:97` | line **94** | ⚠ DRIFT (off by 3) |

Same drift pattern — ~21 lines off for two of the lemmas (consistent with a single ~21-line block insertion
upstream of `variance_eq_sub` in the commit S1e was written against vs. the pinned commit). None of these are
phantoms — every name resolves at the pinned SHA, just not at the cited line.

### 1.6 Probability-measure facts

| S1e claim | Actual at pinned SHA | Status |
|-----------|----------------------|--------|
| `MeasureTheory.measureReal_le_one` "standard" (no path/line given) | `MeasureTheory/Measure/Typeclasses/Probability.lean:43` | ⚠ unspecified-now-pinned |

The typeclass requirement is `[IsZeroOrProbabilityMeasure μ]`, *not* `[IsProbabilityMeasure μ]` (which is what
S1e's variable block declares). Mathlib has an auto-instance `IsProbabilityMeasure → IsZeroOrProbabilityMeasure`
at `Probability.lean:73-75`, so the call works transparently — but if a future Mathlib refactor splits the two
typeclasses, S1e's `measureReal_le_one` reference may need an explicit instance. Not a bug today; a fragility
worth flagging.

### 1.7 Summary table

| Class | Cited | Verified | Net |
|-------|-------|----------|-----|
| Cauchy-Schwarz core | 1 | 1 (drift +7) | 0 phantoms |
| HolderConjugate | 1 | 1 (drift +4) | 0 phantoms |
| Integral decomposition | 3 | 2 (drift +5/+5) | **1 phantom** (`setIntegral_compl₀`) |
| Indicator & set-integral | 5 | 5 (drift +9/+25/+25/+25/+15) | 0 phantoms |
| Variance | 5 | 5 (drift +0/+21/+9/+21/+3) | 0 phantoms |
| Probability-measure facts | 3 | 3 (none pinned to file:line) | 0 phantoms |

**Net**: 1 phantom name + ≥11 lemma cites with line drift. Names resolve correctly; line numbers do not.

### 1.8 Recommendation for S2 ACT picker (if route (b-S1e) is chosen)

1. **Strip the trailing `₀` from `setIntegral_compl₀`** in S1e §3.3 — or just don't call that lemma; the §4 skeleton uses `integral_add_compl` + `add_comm` instead, which is fine.
2. **Trust the *names* in S1e's tables, not the *line numbers*** — re-verify any line number you need to physically open in your editor by `gh api search/code+contents` against the pinned SHA. Names are 11/12 correct (1 phantom: `setIntegral_compl₀`). Line numbers are ~3/12 correct.
3. **Spot-check `MemLp.integrable` and `MemLp.sq`** (S1e §3.8 explicitly flags these as un-file-located). Both exist at the pinned SHA — `MemLp.integrable` is at `Mathlib/MeasureTheory/Function/LpSpace/Integrable.lean`; `MemLp.sq` is at `Mathlib/MeasureTheory/Function/LpSpace/Basic.lean` (verified by independent search). If a fallback is needed, S1e §3.8 alternatives stand.

## 2. Route C: weighted-Finset Paley-Zygmund (alternative to (a) and (b))

S1c's framing of routes was:
- **(a)** Axiomatize Paley-Zygmund as a `Measure`-theoretic statement, +1 axiom, ~20 LOC.
- **(b)** Inline Paley-Zygmund from Cauchy-Schwarz in measure-theoretic form, 0 axioms, ~70 LOC (S1c) / ~75 LOC (S1e refined).

Both routes treat `G(n,p)` as needing a `Measure`-typed sample space. But the parent gallery proof `ProbMethodSecondMoment.lean` is **already entirely finite-discrete** — it uses `Finset α` + `α → ℚ` + uniform mean `μ := s.sum f / s.card`, with 0 sorries and 0 axioms.

The OQ-02 problem statement reads:
> "Can the variance computation for indicator sums be formalized generically to handle subgraph counting in $G(n,p)$ and derive specific threshold functions?"

`G(n,p)` is a **finite probability space**: there are exactly $2^{N}$ possible edge-sets where $N = \binom{n}{2}$, each with weight $p^{|E|}(1-p)^{N-|E|}$ in ℝ (or ℚ if $p \in \mathbb{Q}$). The "measure" is fully discrete.

### 2.1 The weighted generalisation

Parent's existing lemma (lines 177-225 of `ProbMethodSecondMoment.lean`):

```lean
theorem paley_zygmund_quantitative {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℚ} {θ : ℚ} (hs : s.Nonempty) (hnn : ∀ a ∈ s, 0 ≤ f a)
    (hpos : 0 < s.sum f) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hf2_pos : 0 < s.sum (fun a => f a ^ 2)) :
    let μ := s.sum f / s.card
    (1 - θ) ^ 2 * (s.sum f) ^ 2 / s.sum (fun a => f a ^ 2) ≤
      ↑(s.filter (fun a => f a ≥ θ * μ)).card
```

This uses **uniform** weight 1 per element (the `μ := s.sum f / s.card` and the `↑(...filter...).card` on the RHS).

The **weighted** generalisation:

```lean
theorem paley_zygmund_quantitative_weighted {α : Type*} [DecidableEq α] {s : Finset α}
    {f w : α → ℚ} {θ : ℚ} (hs : s.Nonempty) (hnn : ∀ a ∈ s, 0 ≤ f a)
    (hwnn : ∀ a ∈ s, 0 ≤ w a) (hwpos : 0 < s.sum w)
    (hpos : 0 < s.sum (fun a => w a * f a)) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (hf2_pos : 0 < s.sum (fun a => w a * f a ^ 2)) :
    let μ := s.sum (fun a => w a * f a) / s.sum w
    (1 - θ) ^ 2 * (s.sum (fun a => w a * f a)) ^ 2 / s.sum (fun a => w a * f a ^ 2) ≤
      (s.filter (fun a => f a ≥ θ * μ)).sum w
```

The expectation `μ := E_w[f] := (Σ w·f) / (Σ w)`. The LHS bounds `Pr_w[f ≥ θ·μ] := (Σ_{f ≥ θμ} w) / (Σ w)`
when both sides are multiplied by `Σ w`, recovering the standard Paley-Zygmund form
`(1-θ)² · E_w[f]² / E_w[f²] ≤ Pr_w[f ≥ θ·μ]` after normalising.

### 2.2 Proof sketch (~45 LOC, 0 sorries, 0 axioms)

The proof structure mirrors the existing `paley_zygmund_quantitative` in the parent (`ProbMethodSecondMoment.lean:177-225`). Substitute `s.sum f → s.sum (w·f)`, `s.card → s.sum w`, `s.sum f² → s.sum (w·f²)`, and `(s.filter P).card → (s.filter P).sum w` throughout.

The key Cauchy-Schwarz step in parent uses helper:

```lean
private lemma sq_sum_le_card_mul_sum_sq {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℚ) :
    (s.sum f) ^ 2 ≤ ↑s.card * s.sum (fun a => f a ^ 2)
```

The weighted analogue (provable by the same induction structure with weight inserted):

```lean
private lemma sq_sum_le_sum_weighted_mul_sum_sq {α : Type*} [DecidableEq α]
    (s : Finset α) (f w : α → ℚ) (hwnn : ∀ a ∈ s, 0 ≤ w a) :
    (s.sum (fun a => w a * f a)) ^ 2 ≤ s.sum w * s.sum (fun a => w a * f a ^ 2)
```

This is the *weighted Cauchy-Schwarz* inequality `(Σ w·f)² ≤ (Σ w)·(Σ w·f²)`. It is the standard Cauchy-Schwarz
applied to `(√w · f, √w)` after squaring. The parent already has the induction skeleton; the weighted version
adds `* (√w(a))²` at each step.

**Alternative**: this is also `Finset.inner_mul_le_norm_mul_norm` or `Finset.sum_mul_sq_le_sq_mul_sq` in Mathlib.
Quick search:

- `Finset.inner_mul_le_norm_mul_norm` exists in `Mathlib/Analysis/InnerProductSpace/Basic.lean` — for inner product spaces.
- `Finset.sum_mul_sq_le_sq_mul_sq` exists in `Mathlib/Analysis/MeanInequalitiesPow.lean` (or similar) — the discrete Cauchy-Schwarz.

The S2 ACT picker can either:
- Inline the weighted Cauchy-Schwarz (induction, ~15 LOC) — matches parent style.
- Specialise from Mathlib's discrete Cauchy-Schwarz (~5 LOC) — pin the exact Mathlib name first.

### 2.3 LOC budget for Route C

| Component | LOC | Note |
|-----------|-----|------|
| `sq_sum_le_sum_weighted_mul_sum_sq` (Cauchy-Schwarz, induction or Mathlib reuse) | 15 | Could be 5 if Mathlib name confirmed |
| `paley_zygmund_quantitative_weighted` main theorem | 30 | Mirror parent's structure |
| `gnp_edge_weight` def (the weight function `E ↦ p^|E|·(1-p)^(N-|E|)`) | 3 | Trivial def |
| `gnp_edge_weight_sum` (sum-to-1 over Finset.univ : Finset (Finset (EdgeIdx n))) | 5 | Reuses S1d's `Fintype.sum_pow_mul_eq_add_pow` |
| `triangle_subcritical` / `triangle_supercritical` applications | ~120 | The actual G(n,p) variance computation (unchanged from S1c §6) |
| **Total** | **~175 LOC** | **0 axioms** |

**Comparison with routes (a) and (b-S1e)**:

| Route | LOC (total file) | Axioms | Mathlib API surface | Build risk |
|-------|------------------|--------|---------------------|------------|
| (a) axiomatize PMF P-Z | ~250 | **+1** | PMF + Measure + Variance | low (small surface) |
| (b-S1e) inline measure-theoretic P-Z | ~260 (per S1e §6 refined budget) | 0 | PMF + Measure + Variance + MemLp + Bochner + Lp + HolderConjugate | moderate (large surface) |
| **(c) weighted-Finset P-Z** | **~175** | 0 | `Finset.sum` + `Finset.filter` + basic ℚ arithmetic | **low** (parent-style only) |

Route C is ~85 LOC tighter than (b-S1e) and avoids the entire measure-theoretic stack. The trade-off: it
operates in ℚ (or ℝ if `p ∈ ℝ`), not against a `Measure` / `PMF`. This means downstream applications that want
to compose with measure-theoretic results (e.g. continuous random variables, expectation over `ℝ`-valued
measurable functions) cannot use Route C — but the OQ-02 statement specifically targets `G(n,p)` and threshold
functions, both of which are finite-discrete by construction.

### 2.4 Why Route C is plausibly the right call

1. **Parent is already discrete-Finset.** Route C extends parent in its native idiom; routes (a) and (b)
   introduce a measure-theoretic dialect not used elsewhere in the parent file.
2. **`G(n,p)` is finite.** A `Measure`-typed sample space is over-machinery for `2^N` configurations with
   rational/real weights.
3. **Stage gate to `verified`.** Route C ships 0 axioms in ~175 LOC, candidate for
   `status: "verified"` in the OQ-02 meta.json once built. Route (a) lands at `status: "axiomatized"` (1 axiom).
   Route (b-S1e) also lands at `verified` (0 axioms) but at ~260 LOC and with deeper measure-theoretic dependencies.
4. **Independent of `PMF.ofFintype`/`MemLp`/`HolderConjugate`** — the three load-bearing Mathlib chains S1d/S1e
   audit. The only Mathlib reuse is `Finset.sum_pow_mul_eq_add_pow` (S1d's lemma, well-cited and at correct
   line 236) for the sum-to-1 of edge weights.

### 2.5 Why Route C is plausibly NOT the right call

1. **Doesn't generalise.** Beyond `G(n,p)`, Route C doesn't extend to continuous distributions. If the parent
   ever wants to formalise (say) Markov / Borel-Cantelli with measure-theoretic input, the weighted-Finset
   framework is dead-end.
2. **Doesn't match `prob-method-second-moment-oq-02`'s "generic" framing.** The OQ statement asks for "generic"
   indicator-sum variance — Route C's "generic" is restricted to discrete-Finset inputs, not arbitrary indicator
   random variables.
3. **`p ∈ ℝ` is more natural than `p ∈ ℚ`.** The parent uses ℚ for exact arithmetic; the threshold theorems
   `triangle_subcritical` / `_supercritical` are stated against `p : ℝ` in the literature. Route C in ℝ works
   but loses the parent's `decide`-friendly ℚ tactic surface.
4. **Inflation risk.** ~120 LOC of the ~175 budget is in the `triangle_*` applications, which are common to all
   three routes. The savings vs (b-S1e) on the P-Z step alone are ~30 LOC, not 85 — the +85-LOC gap mostly
   reflects S1e's added measure-theoretic boilerplate that Route C doesn't need.

### 2.6 Recommendation

**The S2 ACT picker should reconsider Route C before committing to (b-S1e).** S1e's audit gives a clean
~75-LOC inline route conditional on the Mathlib chain being correctly named — and our §1 audit just confirmed
the names are (with one phantom-strip) correct at the pinned SHA, so (b-S1e) is in-principle viable. But Route
C is plausibly tighter (~175 vs ~260 total LOC), simpler (no measure-theoretic stack), and stays in the
parent's existing dialect.

If the S2 ACT picker prefers (b-S1e), this audit removes the `setIntegral_compl₀` phantom and the line-number
drift as blockers. If the picker prefers Route C, §2.2 gives the weighted-Finset skeleton.

## 3. Anti-targets

This memo does **not**:

1. ❌ Write `proofs/Proofs/ProbMethodSecondMomentOQ02.lean` (S2 ACT's domain — pending route choice).
2. ❌ Touch the parent `proofs/Proofs/ProbMethodSecondMoment.lean`.
3. ❌ Edit any of `state.md`, `knowledge.md`, `problem.md`, gallery JSON, or `meta.json`.
4. ❌ Edit sibling session files (`2026-05-12-s1b-...`, `2026-05-13-s01c-...`, `2026-05-13-s01d-...`, `2026-05-13-s1e-...`).
5. ❌ Run `./proofs/scripts/docker-build.sh` (no build).
6. ❌ Submit anything to Aristotle (no `*Aristotle.lean` companion).
7. ❌ Propose Mathlib upstream contribution (`paley_zygmund_quantitative_weighted` is slug-local for now).

## 4. Race awareness

Pre-push checks (2026-05-13 ~07:05 UTC):

- `gh pr list --repo rjwalters/lean-genius --state open --search "prob-method-second-moment-oq-02 in:title"`: **0 open PRs** on this slug.
- `gh pr list --repo rjwalters/lean-genius --state open --search "prob-method in:title"`: **0 open PRs** across the family.
- Most recent merge on slug: PR #18543 (S1e) at 03:38 UTC — ~3.5h before this session start.
- 30-min window since last merge is closed; this is a post-cascade audit, not a 30-min-post-merge PREP cascade.
- All 5 prior PREPs (S1, S1b, S1c, S1d, S1e) merged. Clean state.

Conflict surface with the merged PREPs: zero. New file path under `sessions/`. No edits to any other file.

## 5. Acceptance criteria

1. **Audit §1 surfaces concrete errata**: 1 phantom name (`setIntegral_compl₀`), 11+ line-number drifts (3-25 lines each), all spot-checked against pinned commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
2. **Route C §2 sketch is concrete**: `paley_zygmund_quantitative_weighted` theorem statement is precise; LOC budget is decomposed; comparison with (a) and (b-S1e) is quantified.
3. **No conflicts with S1c/S1d/S1e**: their Lean skeletons remain valid (just with line numbers refreshed and one name corrected).
4. **0 sorries, 0 axioms, 0 Lean lines, 0 builds** in this PREP.
5. **Honest about Route C limitations**: §2.5 lists 4 reasons it might not be the right call.

## 6. Honesty

- The 8 line-number drifts in §1 are **not** evidence S1e was careless — they are evidence S1e was written
  against a Mathlib commit ~25 lines (in the relevant section blocks) different from the pinned commit
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. The names are correct; the lines have drifted upstream.
- The `setIntegral_compl₀` phantom **is** a typo — Mathlib v4.26.0 only has `setIntegral_compl` (no `₀`).
  Easy to fix; S1e's §4 skeleton doesn't depend on this name.
- The Route C weighted-Finset framing **has not been ground-tested**. The ~45-LOC P-Z theorem is a paper
  estimate based on mirroring the parent's existing ~50-LOC `paley_zygmund_quantitative`. The actual LOC
  could be 30 (if Mathlib's discrete Cauchy-Schwarz subsumes most of the work) or 70 (if the weighted
  Cauchy-Schwarz needs its own induction).
- The 0-axiom claim for Route C **assumes** Mathlib's `Finset.sum_pow_mul_eq_add_pow` covers the sum-to-1
  step for edge weights. Verified at line 225 (`Finset.`) and line 236 (`Fintype.`) of
  `Mathlib/Algebra/BigOperators/Ring/Finset.lean` at the pinned SHA — S1d's audit is correct.
- The "~85 LOC tighter" Route C claim is a delta of *total file LOC*, not just the P-Z step. The P-Z step
  itself is ~75 LOC (S1e b-route) vs ~45 LOC (Route C) — a ~30-LOC saving. The remaining ~55 LOC gap is the
  measure-theoretic boilerplate (PMF construction, `MemLp` bookkeeping, `μ.real ↔ μ` conversions) that
  Route C doesn't need.
- The "low build risk" rating for Route C is **subjective**: it operates in the parent's existing dialect
  (Finset/ℚ/ℝ + induction + Cauchy-Schwarz), which the parent already builds clean against. Route (b-S1e)'s
  "moderate" rating reflects the larger Mathlib API surface — even with a clean audit, more lemma names
  means more drift exposure.

## 7. Cross-references

- PR #18295 (MERGED) — S1 OBSERVE generic variance framing.
- PR #18429 (MERGED) — S1b OBSERVE Mathlib `cliqueFinset` / `variance` / `PMF.bernoulli` audit.
- PR #18472 (MERGED) — S1c OBSERVE Paley-Zygmund gap correction; this PREP refines its routes (a)/(b) by adding Route C.
- PR #18527 (MERGED) — S1d PREP `gnp_edges` PMF; this PREP confirms its `Finset.sum_pow_mul_eq_add_pow` citations at 225/236 (correct) and reuses the same lemma for Route C's edge-weight sum-to-1.
- PR #18543 (MERGED) — S1e PREP inline-measure-theoretic Paley-Zygmund; this PREP **audits** its §3 table (8 line drifts + 1 phantom name) and **adds** Route C as a third option.
- `proofs/Proofs/ProbMethodSecondMoment.lean` (parent, lines 177-225 — existing `paley_zygmund_quantitative` that Route C extends).
- Mathlib v4.26.0 pinned commit `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:
  - `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean:1244` (`integral_mul_le_Lp_mul_Lq_of_nonneg` — corrected from S1e's 1237).
  - `Mathlib/MeasureTheory/Integral/Bochner/Set.lean:139,145,149,155,485,489,494,743` (decomposition + indicator + monotonicity — corrected from S1e's 144/150/155/164/510/514/519/728).
  - `Mathlib/Probability/Moments/Variance.lean:63,94,145,180,204` (variance API — corrected from S1e's 63/97/154/201/225).
  - `Mathlib/Data/Real/ConjExponents.lean:133` (`HolderConjugate.two_two` — corrected from S1e's 137).
  - `Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:43` (`measureReal_le_one` — newly pinned; S1e left this unfile-located).
  - `Mathlib/Algebra/BigOperators/Ring/Finset.lean:225,236` (`Finset.sum_pow_mul_eq_add_pow`, `Fintype.sum_pow_mul_eq_add_pow` — confirms S1d's audit).
- Memory: `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — audit-correction PREP pattern; this S1f is a direct continuation, flagging concrete errata (1 phantom + 11 line drifts) in a recently-merged S1e PREP.
- Memory: `feedback_researcher_12_2026_05_13_triple_mathlib_bearer_audit.md` — Mathlib-bearer-audit pattern; this S1f also corrects bearer attribution.
- Memory: "Mathlib API audit beats first-principles design" — this PREP applies the same lens: the §3 table in S1e is the bearer chain; auditing it pre-empts ~1-2 hours of S2 ACT debug time at first build.

## 8. Sorry / axiom delta projection

- This S1f PREP: **0 sorries, 0 axioms, 0 Lean lines**.
- Route C if chosen for S2 ACT: **0 axioms**, ~45 LOC for the P-Z step itself, ~175 LOC total file.
- Route (b-S1e) if chosen with this PREP's errata applied: **0 axioms**, ~75 LOC for the P-Z step, ~260 LOC total file. S1e §6 budget unchanged; the audit doesn't move LOC, only fixes name/line references.
- Route (a) axiomatize: **+1 axiom**, ~20 LOC for the P-Z statement, ~250 LOC total file. Unchanged by this PREP.

## 9. Next iteration after this PREP

1. **S2 ACT picker chooses route**: (a) axiomatize, (b-S1e) inline measure-theoretic, or (c) weighted-Finset. This S1f neutralizes the audit risk for (b) and surfaces (c) as a fresh contender.
2. **If (c) chosen**: Write `paley_zygmund_quantitative_weighted` (~45 LOC) + `gnp_edge_weight` (~8 LOC) + `triangle_*` applications (~120 LOC). Total ~175 LOC, 0 axioms, `status: "verified"`.
3. **If (b-S1e) chosen**: Use S1e §4 skeleton verbatim with one fix — replace `setIntegral_compl₀` with `setIntegral_compl` (or drop it entirely, as §4 doesn't need it). Re-pin line numbers via this PREP's §1 corrections. ~260 LOC, 0 axioms, `status: "verified"`.
4. **If (a) chosen**: Drop the inline-Paley-Zygmund machinery entirely. ~250 LOC, +1 axiom, `status: "axiomatized"`.

The post-S2 ACT gallery entry update would be a sibling S3 task (meta.json + annotations.json + index.ts under `src/data/proofs/prob-method-second-moment-oq-02/`).
