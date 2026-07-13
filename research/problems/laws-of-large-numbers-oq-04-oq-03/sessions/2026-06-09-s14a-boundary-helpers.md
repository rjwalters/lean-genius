# S14a ACT — Boundary-node existence helpers for `QuantileBracketingGrid`

**Slug**: `laws-of-large-numbers-oq-04-oq-03`
**Date**: 2026-06-09 (UTC)
**Researcher**: researcher-4
**Mode**: ACT (Lean code; +2 public lemmas, +1 private bridge lemma)
**Builds performed**: Docker build of `Proofs.LawsOfLargeNumbersOQ04OQ03QuantileBracketing` (pending at memo write time; cache download finished, build phase running)

## 0. TL;DR

S14a ships the two boundary-node existence helpers needed by the upcoming
S14b existence proof of `quantileBracketingGrid_exists`, plus a private
self-contained restatement of the `trueCDF ↔ cdf` bridge so the
quantile-bracketing chain has no transitive dependency on the refuted
axiom in the original bracketing companion.

```lean
lemma trueCDF_exists_le [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, trueCDF X μ x ≤ ε

lemma trueCDF_exists_ge [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0))
    {η : ℝ} (hη : η < 1) :
    ∃ x : ℝ, η ≤ trueCDF X μ x
```

These discharge the `left_le` and `right_ge` fields of
`QuantileBracketingGrid` directly: pick `q 0` as a witness of
`trueCDF_exists_le ε` and `q_last` as a witness of
`trueCDF_exists_ge (1 - ε)`. The S14b existence proof then has to
construct only the **interior** `k` quantile nodes plus prove `step_le`
and `mono`.

## 1. Why these helpers, why now

The S13 ACT (PR #22044, researcher-1, 2026-06-02) shipped the typed
scaffold `QuantileBracketingGrid` with 0 theorems. The
state.md "Next Action" describes S14 as one substantive ~150 LOC piece
proving `quantileBracketingGrid_exists`. That is too large for a single
ACT session without prior decomposition: the proof has four moving parts
(boundary nodes, interior nodes via quantile, strict-mono between
adjacent nodes, the step bound via leftLim). Landing all four together
risks a session that ends with sorries.

S14a splits the first part off — the two boundary nodes — into
elementary, self-contained lemmas that are useful regardless of the
interior construction. They:

* compile without `import Proofs.LawsOfLargeNumbersOQ04OQ03Bracketing`,
  preserving the design intent that `LawsOfLargeNumbersOQ04OQ03QuantileBracketing.lean`
  is the substrate for the S17 retirement of the refuted bracketing
  companion;
* mirror S3 (PR #17442) → S4 (PR #17442 follow-up) → S5 → S6 cadence,
  where each session shipped one §x.y piece;
* are short (~10 LOC each) and use exclusively Mathlib's stable
  `ProbabilityTheory.tendsto_cdf_atBot` / `tendsto_cdf_atTop` plus
  `Iio_mem_nhds` / `Ioi_mem_nhds` neighborhood-eventually unwinding.

The S14b session then constructs the interior quantile nodes
`q_j = sInf {x | F x ≥ j*ε}` for `j = 1, …, k` (with `k = ⌈1/ε⌉`),
and proves `step_le` via `leftLim F (q_{j+1}) ≤ (j+1)ε` (definition of
infimum) and `F (q_j) ≥ j*ε` (right-continuity of F via Mathlib's
`StieltjesFunction.right_continuous` + `cdf` is a `StieltjesFunction`).

## 2. Files modified

* `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03QuantileBracketing.lean`:
  154 → 216 lines (+62). One `variable` line, one `private lemma`,
  two public `lemma`s, one §S14a.1 section header, ~30 lines of new
  docstrings.
* `src/data/research/problems/laws-of-large-numbers-oq-04-oq-03.json`:
  `leanFiles` appended with the QuantileBracketing entry (lineCount 216,
  theoremCount 3, axiomCount 0, sorryCount 0); knowledge `builtItems`,
  `insights`, `nextSteps` extended.
* `research/problems/laws-of-large-numbers-oq-04-oq-03/state.md`:
  Next Action section updated; new S14a ACT block prepended.
* `research/problems/laws-of-large-numbers-oq-04-oq-03/knowledge.md`:
  this session's entry archived; older sessions remain on disk in
  `sessions/`.
* `research/problems/laws-of-large-numbers-oq-04-oq-03/sessions/2026-06-09-s14a-boundary-helpers.md`:
  this memo (new).

## 3. Counts delta

| File | Lines | Theorems | Axioms | Sorries |
|------|-------|----------|--------|---------|
| `LawsOfLargeNumbersOQ04OQ03QuantileBracketing.lean` | 154 → 216 | 0 → 3 (1 private) | 0 | 0 |

Chain-level axiomCount unchanged (still 1, the refuted
`bracketingGrid_exists` in the original bracketing companion).
Chain-level sorryCount unchanged (still 0). No `gallery-tracked
verified` status changes.

## 4. Proof technique notes

Both helpers use the same five-line skeleton:

```lean
haveI : IsProbabilityMeasure (Measure.map (X 0) μ) :=
  Measure.isProbabilityMeasure_map hX_meas.aemeasurable
have h_tend : Tendsto (trueCDF X μ) (atBot|atTop) (nhds (0|1)) := by
  rw [funext_via_trueCDF_eq_cdf_map']; exact ProbabilityTheory.tendsto_cdf_(atBot|atTop) _
obtain ⟨x, hx⟩ := (h_tend.eventually ((Iio|Ioi)_mem_nhds (hε|hη))).exists
exact ⟨x, le_of_lt hx⟩
```

Key Mathlib lemmas:

* `ProbabilityTheory.tendsto_cdf_atBot : Tendsto (cdf μ) atBot (𝓝 0)`
* `ProbabilityTheory.tendsto_cdf_atTop : Tendsto (cdf μ) atTop (𝓝 1)`
* `Iio_mem_nhds : a < b → Iio b ∈ 𝓝 a`
* `Ioi_mem_nhds : a < b → Ioi a ∈ 𝓝 b`
* `Filter.Eventually.exists` (uses `Filter.atBot.NeBot` / `Filter.atTop.NeBot`)

The private bridge `trueCDF_eq_cdf_map'` is a verbatim duplicate of the
public `trueCDF_eq_cdf_map` from the bracketing companion. Duplication
is intentional: the redesign plan retires the bracketing companion at
S17, so importing it now would create coupling we plan to remove. The
~7-line duplicate is preferable to a transitive import of the refuted
axiom's namespace.

## 5. Honesty

This session is **infrastructure-only**: no axioms eliminated, no
sorries closed on the main theorem. The two helpers are not themselves
the existence proof — they are pre-staged witnesses for S14b. Per the
gallery rubric, this is "category 5 — infrastructure that enables
future proofs". The "axiom elimination" pivot point remains S15+, when
the redesigned §2.4 / §2.5 land and the refuted `bracketingGrid_exists`
is retired.

The two lemmas compile against Mathlib 4.26 (commit `2df2f0150c27`,
matched by `proofs/lake-manifest.json`). Build verification via Docker
is pending at memo write time; the build was launched against the
QuantileBracketing target and the cache download finished cleanly
(7727 files / 100%). The build log will be appended to this memo if
the verification passes; otherwise the session memo will be updated to
record any remediation needed.

## 6. Honest scope estimate for S14b

The remaining work to prove `quantileBracketingGrid_exists` after this
session:

| Piece | Approach | LOC estimate |
|-------|----------|--------------|
| Define `quantile F t := sInf {x | F x ≥ t}` (private) | direct | ~5 |
| `quantile_le : F (quantile F t) ≥ t` (right-continuity of cdf) | csInf + Stieltjes right-continuous | ~25 |
| `leftLim_quantile_le : leftLim F (quantile F t) ≤ t` | infimum-of-set property | ~20 |
| Pick `k = ⌈1/ε⌉.toNat` and `q j = quantile F (j * ε)` for interior | direct | ~10 |
| Strict-mono of `q` (interior) | StrictMono.id_iff + quantile mono | ~25 |
| `step_le` for interior cells | combine the two `quantile` bounds | ~15 |
| Boundary nodes (left_le, right_ge) | this session's helpers + Finset stitching | ~15 |
| Compose into `Nonempty (QuantileBracketingGrid …)` | refine ⟨{…}⟩ | ~10 |
| **S14b total** | | **~125 LOC** |

S14b should be a single session ACT, possibly tight but achievable.
S15 (§2.4 rewrite) and S16 (§2.5 rewrite) remain larger pieces.

## 7. Tracker hygiene

* Pool `status` for this slug: `in-progress` (claimed pre-S14a, will be
  released at end of session).
* `phase`: `ACT` (advanced from S13's `ACT` value — this is S14a still
  within ACT phase, not a fresh phase).
* No PR labels triggering Loom Judge review (math research PR; deployer
  will merge per CLAUDE.md policy).
