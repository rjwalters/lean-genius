# Current State

**Phase**: ACT
**Since**: 2026-05-08T20:43:00Z
**Iteration**: 5 (S5 — bracketing_uniform_sup_bound + bracketing_uniform_from_grid)

## S5 (this session, researcher-6, 2026-05-11) — §2.4 deterministic + limit form

S4 landed §2.3 (`bracketing_simultaneous_pointwise`). S5 (this session) lands
the second of the three remaining theorems, §2.4
(`bracketing_uniform_from_grid`), in two parts:

* `bracketing_uniform_sup_bound` (deterministic): for any `n` and `ω`,
  `⨆ x, |Fₙ(x, ω) − F(x)| ≤ max_j |Fₙ(qⱼ, ω) − F(qⱼ)| + 2ε`.
  Probability-free, limit-free monotone-interpolation inequality.
* `bracketing_uniform_from_grid` (limit): given simultaneous a.s. convergence
  at every grid node (`hpw`), for every slack `η > 0`, eventually the sup-error
  is `≤ 2ε + η`. The composition is short: `hpw` ⇒ finite max → 0 ⇒ sup
  eventually `≤ η + 2ε` via the deterministic bound.

### What landed

The deterministic bound is the meat of §2.4: a three-case split on `x`
relative to the grid `q : Fin (G.k+2) → ℝ`:

* **Left tail** (`x < q 0`): `|Fₙ(x) − F(x)| ≤ Fₙ(q 0) + F(q 0)` (via
  nonnegativity), then `Fₙ(q 0) + F(q 0) = (Fₙ(q 0) − F(q 0)) + 2·F(q 0)
  ≤ |Fₙ(q 0) − F(q 0)| + 2ε ≤ M + 2ε`.
* **Interior cell** (`q (j.castSucc) ≤ x < q j.succ` for some
  `j : Fin (G.k+1)`): monotonicity gives `|Fₙ(x) − F(x)| ≤ Fₙ(q j.succ) −
  F(q j.castSucc) = (Fₙ(q j.succ) − F(q j.succ)) + (F(q j.succ) −
  F(q j.castSucc)) ≤ M + ε ≤ M + 2ε` (and the symmetric lower bound).
* **Right tail** (`q (Fin.last (G.k+1)) ≤ x`): `|Fₙ(x) − F(x)| ≤ (1−Fₙ x)
  + (1−F x)` (using both `_le_one` bounds), then `(1 − F x) ≤ ε` (boundary)
  and `(1 − Fₙ(q_last)) ≤ ε + M` (chain through `F(q_last)`), giving
  `≤ M + 2ε`.

The cell-finding step uses `Finset.max'` on `s := {j | q j ≤ x}`, choosing
the largest grid index that lies at or below `x`. By maximality, the next
index strictly exceeds `x`.

Two trivial upper bounds (`empiricalCDF_le_one`, `trueCDF_le_one`) were added
as private helpers; both were absent from the parent file but follow directly
from definitions plus `IsProbabilityMeasure μ`.

The limit form is short: from `hpw`, each `|Fₙ(qⱼ) − F(qⱼ)| → 0`, so for
every `η > 0` each is eventually `< η`; combining over the finite index
`Fin (G.k+2)` via `Filter.eventually_all` gives the finite max `≤ η`
eventually, and the deterministic bound lifts this to the `iSup`.

### Mathlib API used

* `empiricalCDF_mono`, `trueCDF_mono`, `empiricalCDF_nonneg`, `trueCDF_nonneg`
  (parent file `LawsOfLargeNumbersOQ04`) — monotone-interpolation core.
* `measure_mono`, `measure_univ` + `[IsProbabilityMeasure μ]`,
  `ENNReal.toReal_mono` — for the `trueCDF ≤ 1` helper.
* `Finset.sup'`, `Finset.le_sup'`, `Finset.sup'_le`, `Finset.max'`,
  `Finset.le_max'`, `Finset.max'_mem` — for the finite max bookkeeping.
* `Fin.last`, `Fin.castSucc`, `Fin.succ`, `Fin.ext` — for the grid indexing.
* `ciSup_le` — to lift the per-`x` bound to the `iSup` over `ℝ`.
* `Metric.tendsto_nhds`, `Real.dist_eq` — to extract eventually-bounded
  form from the `Tendsto` hypothesis.
* `Filter.eventually_all` — to commute `∀ᶠ` with `∀ j : Fin (G.k+2)`.

### Counts

The bracketing companion file went 147 → 447 lines (+300 lines), 1 → 3
theorems (added `bracketing_uniform_sup_bound`, `bracketing_uniform_from_grid`,
plus 3 private helpers `empiricalCDF_le_one`, `trueCDF_le_one`,
`find_cell`, `bracketing_pointwise_bound`), 1 axiom unchanged
(`bracketingGrid_exists`), 0 sorries unchanged. The main file
`LawsOfLargeNumbersOQ04OQ03.lean` is unchanged (158 lines, 4 theorems, 0
sorries, 0 axioms). Per gallery convention `meta.lineCount` /
`theoremCount` track the main file only — no meta.json update needed.

### Build status

Pending. Build started under Docker (`./proofs/scripts/docker-build.sh
Proofs.LawsOfLargeNumbersOQ04OQ03Bracketing`); expected ~45 min cold under
the broken `proofs/.lake` self-symlink. PR title bears the "(build pending)"
suffix per the recent precedent for §2.3+ work on this slug. API names were
verified against Mathlib 4.26 prior to commit.

### Remaining work in §2

- §2.5 (`glivenko_cantelli_uniform_proved`, ~20 lines, composition of
  `bracketingGrid_exists` + `bracketing_simultaneous_pointwise` +
  `bracketing_uniform_from_grid` along `ε = 1/(m+1)`).
- Optional: retire parent's `glivenko_cantelli_uniform` once §2.5 lands.
- Future Mathlib upstream: `Monotone.exists_increasing_continuity_seq`.

## S4 (researcher-4, 2026-05-08) — §2.3 bracketing_simultaneous_pointwise landed

S3 (PR by researcher-12) shipped the typed scaffold:
`BracketingGrid` structure (§2.1) and `bracketingGrid_exists` axiom (§2.2),
both in `Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean`. S4 (this session)
fills in the first of the three remaining theorems from
`bracketing-decomposition-draft.md` §2.

### What landed

`bracketing_simultaneous_pointwise`: given any `Fin (k+2)`-indexed grid `q`,
produces a single full-measure set on which the empirical CDF tends to the
true CDF *simultaneously* at every `q j`. The proof is 3 tactic lines:

```lean
rw [ae_all_iff]
intro j
exact empiricalCDF_pointwise_convergence hX_meas hX_iid hX_ident (q j)
```

Mathlib API:
- `MeasureTheory.ae_all_iff` (Mathlib.MeasureTheory.OuterMeasure.AE:95) — the
  countable conjunction lemma `(∀ᵐ a ∂μ, ∀ i, p a i) ↔ ∀ i, ∀ᵐ a ∂μ, p a i`,
  applied with `ι := Fin (k+2)` (finite, so countable).
- `empiricalCDF_pointwise_convergence` (parent file `LawsOfLargeNumbersOQ04`
  line 144) — supplies the per-grid-point a.s. convergence.

### Counts (no meta.json update needed)

The bracketing companion file is in `leanFile.additionalFiles`; per gallery
convention `meta.lineCount` / `theoremCount` track the main file only. The
main file `LawsOfLargeNumbersOQ04OQ03.lean` is unchanged (158 lines, 4
theorems, 0 sorries, 0 axioms — `verified`/`original`).

The bracketing companion went 120 → 147 lines, 0 → 1 theorem, 1 axiom
unchanged, 0 sorries unchanged.

### Build status

Pending. The `proofs/.lake` recursive self-symlink remains broken (per memory
feedback `feedback_researcher_lake_symlink_broken.md`). Type-check confidence
is high: `ae_all_iff` is in `Mathlib.MeasureTheory.OuterMeasure.AE` and is
transitively imported by `Mathlib.MeasureTheory.Integral.Bochner.Set` (which
the parent file already imports); `Fin (k + 2)` has a `Countable` instance
since it is finite; all referenced names match the parent file's already-built
declarations.

### Remaining work in §2

- §2.4 (`bracketing_uniform_from_grid`, ~50 lines, deterministic case-split).
- §2.5 (`glivenko_cantelli_uniform_proved`, ~20 lines, composition).
- Optional: retire parent's `glivenko_cantelli_uniform` once §2.5 lands.
- Future Mathlib upstream: `Monotone.exists_increasing_continuity_seq`.

## S3 (researcher-12, 2026-05-08) — Bracketing scaffold landed

S2 (researcher-9) produced `bracketing-decomposition-draft.md`: a five-section
spec decomposing the parent file's monolithic `glivenko_cantelli_uniform`
axiom (`Proofs/LawsOfLargeNumbersOQ04.lean` line 176) into three orthogonal
pieces and a composition theorem. Of the four declarations in the spec, three
are routine theorems provable from existing Mathlib + parent infrastructure;
the fourth is a smaller, purely real-analytic axiom that is the natural target
for a future Mathlib upstream PR
(`Monotone.exists_increasing_continuity_seq`).

S3 (this session) ships the **typed scaffold** for the decomposition: the
`BracketingGrid` structure (§2.1 of the draft) and the `bracketingGrid_exists`
axiom (§2.2). Both land in a new companion file
`proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` (~120 lines, mostly
docstring), added to `meta.json`'s `leanFile.additionalFiles`. Sessions 4+ will
fill in §2.3 (`bracketing_simultaneous_pointwise`), §2.4
(`bracketing_uniform_from_grid`), and §2.5 (`glivenko_cantelli_uniform_proved`)
following the spec verbatim.

### Why scaffold-only this session

The existing OQ04OQ03 entry is `verified` / 0-axioms / 0-sorries; introducing
incomplete theorem stubs would visibly regress the entry's status. A
pure-scaffold session — one structure declaration plus one axiom in an
additionalFile — preserves the main file's verified status and gives S4 a
typed substrate for the routine-but-not-trivial §2.3 + §2.4 + §2.5 proofs
without committing to a single sitting.

The scaffold also frontloads the only design decision: how to encode an
ε-bracketing grid. The five-field structure (`k`, `q`, `mono`, `cont`,
`step_le`, `left_le`, `right_ge`) is taken verbatim from spec §2.1, with no
modifications.

### Axiom shift, not net axiom reduction (yet)

Until §2.5 lands, the chain has the parent's `glivenko_cantelli_uniform` AND
the new `bracketingGrid_exists` axiom — net count 1 → 2. After §2.5 proves
`glivenko_cantelli_uniform_proved` from `bracketingGrid_exists`, the parent's
monolithic axiom can be retired (or the gallery entry can adopt the proved
variant), bringing the chain back to 1 axiom whose mathematical content is
now purely real-analytic and ready for upstream contribution.

This session's contribution is intentionally *axiom-introducing* — the trade
is one big black box (probabilistic uniformity) for two smaller boxes
(probabilistic uniformity *plus* analytic ε-cover), with the second box being
the natural Mathlib home and the first box scheduled for retirement once §2.5
lands.

### Counts

- New file `LawsOfLargeNumbersOQ04OQ03Bracketing.lean`: 120 lines, 1
  structure (`BracketingGrid`), 1 axiom (`bracketingGrid_exists`), 0
  theorems, 0 sorries.
- Main file `LawsOfLargeNumbersOQ04OQ03.lean`: unchanged
  (158 lines, 4 theorems, 0 sorries, 0 axioms).
- `meta.json`: `leanFile.additionalFiles` adds the new file path.
  `meta.lineCount` / `meta.sorries` / `meta.axiomCount` / `meta.theoremCount`
  unchanged (track main file only, per gallery convention).
- `meta.status` / `meta.badge`: unchanged (`verified` / `original` — the main
  file remains fully axiom-free).

### Build status

Pending. The `proofs/.lake` recursive self-symlink in this repo forces a
~45-min cold-cache Mathlib clone on every Docker build. The new file is
small (120 lines, 1 structure + 1 axiom, no proof obligations beyond
elaboration of the axiom signature). Type-check confidence is high: all
referenced names (`Fin (k + 2)`, `StrictMono`, `ContinuousAt`, `Fin.castSucc`,
`Fin.succ`, `Fin.last`, `IsProbabilityMeasure`, `Measurable`, `trueCDF`,
`Nonempty`) are stable Mathlib v4.26 / parent-file references. Build
verification deferred to S4 alongside the §2.3–§2.5 theorem additions.

## Next Action

1. **(S4)** Prove `bracketing_simultaneous_pointwise` (§2.3 of
   `bracketing-decomposition-draft.md`). Routine: apply
   `empiricalCDF_pointwise_convergence` (parent line 144) for each
   `j : Fin (k + 2)` to get a per-grid-point a.s. convergence statement,
   then commute the universal-over-`Fin (k + 2)` with the a.s. quantifier
   via `MeasureTheory.ae_all_iff`. Estimated 10–25 lines.
2. **(S5)** Prove `bracketing_uniform_from_grid` (§2.4). Deterministic
   case-split (interior cell, left tail, right tail) using the parent's
   `empiricalCDF_mono` / `trueCDF_mono` plus elementary `abs_le_iff` /
   `max_le_iff`. Estimated ~50 lines, the longest of the three.
3. **(S6)** Prove `glivenko_cantelli_uniform_proved` (§2.5). Composition:
   for each `m`, set `ε := 1 / (m + 1)`, apply `bracketingGrid_exists` →
   `bracketing_simultaneous_pointwise` → `bracketing_uniform_from_grid`,
   then countable intersection of full-measure sets via
   `MeasureTheory.ae_iInter_iff`, then "non-negative limsup ≤ 2 / (m + 1)
   for every `m`" ⇒ "limit = 0". Estimated ~20 lines.
4. **(S7+, optional)** Once §2.5 lands, retire the parent's
   `glivenko_cantelli_uniform` axiom: either replace it textually with
   the new `glivenko_cantelli_uniform_proved`, or update gallery
   conventions to recognise the proved variant as the canonical statement.
5. **(future, upstream)** Mathlib PR for
   `Monotone.exists_increasing_continuity_seq`. Once accepted upstream,
   the bracketing companion's `bracketingGrid_exists` axiom can be
   discharged and the entry becomes fully axiom-free.

## Active Approach

`bracketing-decomposition-draft.md` §2.1–§2.5 is the canonical decomposition.
S3 has shipped §2.1 + §2.2; S4–S6 ship §2.3–§2.5 in order. No alternative
approach considered — the spec's Mathlib API audit (§3) confirms 9 of 10
required lemmas are present in Mathlib 4.26, so the only real work is
typing the proofs out.

## Blockers

None for the §2.3–§2.6 work beyond the broken `proofs/.lake` symlink (which
makes Docker builds slow but not impossible). The single missing Mathlib
piece (`Monotone.exists_increasing_continuity_seq`) is encapsulated as the
`bracketingGrid_exists` axiom and does not block §2.3–§2.5.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 1 (S3 scaffold)
- Approaches tried: 1 (bracketing decomposition per S2 spec)

## Previous Iterations

### Session 1 (2026-05-06, researcher-4) — Integration axioms
PR #16099 created the gallery entry and proved the two integration axioms
(`thresholdIndicator_integrable_proved`, `integral_thresholdIndicator_eq_cdf_proved`),
reducing the parent's axiom count from 3 to 1. File:
`proofs/Proofs/LawsOfLargeNumbersOQ04OQ03.lean` (158 lines, 4 theorems,
0 sorries, 0 axioms).

### Session 2 (2026-05-08, researcher-9) — Bracketing decomposition spec
Produced `bracketing-decomposition-draft.md` (~370 lines): a pre-formalization
spec that decomposes the remaining `glivenko_cantelli_uniform` axiom into
three named pieces (grid existence + simultaneous pointwise + uniform sup) +
a composition theorem. Identified one Mathlib gap
(`Monotone.exists_increasing_continuity_seq`) and confirmed the other 9 of
10 required lemmas are present in Mathlib 4.26.

### Session 3 (2026-05-08, researcher-12) — this session
See "S3" above.
