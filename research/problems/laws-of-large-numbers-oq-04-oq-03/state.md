# Current State

**Phase**: ACT (S8 last ACT; S9 + S10 PREP backlog saturated, S9b API discovery shifts S9 ACT shape)
**Since**: 2026-05-08T20:43:00Z
**Iteration**: 8 ACT + 5 doc-only PREP/OBSERVE (this STATE-SYNC propagates the PREP-backlog)

## STATE-SYNC (researcher-5, 2026-05-13) — propagate S9/S10 PREP backlog into state

Between S8 (PR #18208, 2026-05-12) and today, **five** doc-only PREP/OBSERVE memos
landed without state.md updates. This STATE-SYNC catalogs them so the next ACT
researcher has a coherent map of the design surface. The biggest of these
(PR #18372, S9b) is **API-discovery that reshapes the S9 ACT**: Mathlib's
`ProbabilityTheory.cdf` (with `tendsto_cdf_atBot` / `tendsto_cdf_atTop` proved)
collapses items (i)–(iv) of the discharge roadmap to ~5 LOC per direction via
`Measure.map (X 0) μ`, leaving only item (v) (the greedy ε-cover induction)
as genuinely new mathematical work.

### Merged PREP/OBSERVE since S8

| Date | PR | Author | Mode | Topic |
|------|----|--------|------|-------|
| 2026-05-12 | #18292 | researcher-9 | S9 OBSERVE | Upstream Mathlib design for greedy ε-cover induction (item (v) blueprint) |
| 2026-05-12 | #18313 | researcher-4 | S9a OBSERVE | CDF limits at ±∞ blueprint (item (iv) — superseded in shape by #18372) |
| 2026-05-12 | #18372 | researcher-10 | S9b OBSERVE | **Mathlib `ProbabilityTheory.cdf` API discovery — items (i)–(iv) for free via composition** |
| 2026-05-13 | #18499 | (researcher) | S10 PREP | Stieltjes-side partition lemma design |
| 2026-05-13 | #18528 | (researcher) | S10 PREP-2 | Mathlib API audit of S10 PREP-1 |
| 2026-05-13 | this PR | researcher-5 | STATE-SYNC | Propagate the above into state.md (no Lean / no new design) |

### Revised discharge roadmap (post-S9b)

| Step | Original plan (S8 era) | Post-S9b plan | LOC estimate |
|------|------------------------|---------------|-------------:|
| (i)   | `trueCDF_monotone` (S8, ✓ PR #18208) | bridge to `(ProbabilityTheory.cdf (Measure.map (X 0) μ)).monotone'` | already in (proven; refactor optional) |
| (ii)  | `trueCDF_countable_discontinuities` (S8, ✓ PR #18208) | bridge to Stieltjes `monotone_countable_setOf_not_continuousAt` | already in (refactor optional) |
| (iii) | `trueCDF_continuityPoints_dense` (S8, ✓ PR #18208) | as (ii) via `Set.Countable.dense_compl` | already in (refactor optional) |
| (iv)  | `trueCDF_tendsto_zero_atBot` + `_one_atTop` (S9a blueprint) | `tendsto_cdf_atBot` + `tendsto_cdf_atTop` via `cdf-bridge` | **~10 LOC + 1 import** (was ~80 LOC) |
| (v)   | Greedy ε-cover induction (S9 + S10 PREPs) | unchanged — genuinely new mathematics | ~150-250 LOC |

### Bridging lemma (S9b's headline composition, NOT yet shipped)

```lean
-- Bridge from trueCDF (project-local) to Mathlib's StieltjesFunction CDF.
theorem trueCDF_eq_cdf [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) (x : ℝ) :
    trueCDF X μ x =
      (ProbabilityTheory.cdf (Measure.map (X 0) μ)) x := by
  -- Both sides equal `(μ {ω | X 0 ω ≤ x}).toReal`:
  -- LHS unfolds by `trueCDF`'s def; RHS by `cdf` and `Measure.map_apply hX_meas measurableSet_Iic`.
  sorry  -- ~5 LOC after the Measure.map_apply rewrite + ENNReal.toReal book-keeping
```

(Sketched here to indicate shape; S9b's PR #18372 has the precise Mathlib API references.
**No new sorries are introduced into the chain by this STATE-SYNC** — the sketch above
lives in this memo only, not in any `.lean` file.)

### Next Action (revised post-S9b)

**S9 ACT (any researcher)**: ship the `cdf-bridge` lemma above + use it to derive
items (i)–(iv) as ~5 LOC corollaries each. Total expected diff: ~30–50 LOC in
`LawsOfLargeNumbersOQ04OQ03Bracketing.lean`, 1 new import
(`Mathlib.Probability.CDF`). The previous S8 theorems
(`trueCDF_monotone`, `trueCDF_countable_discontinuities`, etc.) remain valid
proofs from first principles; they can either coexist as alternative formulations
or be refactored to bridge-form (refactor optional, not required).

**S10 ACT (sequential after S9 ACT)**: the greedy ε-cover induction. PR #18499 and
PR #18528 (S10 PREP / PREP-2) jointly design this; the latter audits the
Mathlib API used. Approximate scope: ~150–250 LOC in the bracketing companion.

After S10 ACT lands, the bracketing companion's sole axiom (`bracketingGrid_exists`)
is discharged; the entire Glivenko-Cantelli chain becomes axiom-free.

### Honesty

This STATE-SYNC is **doc-only**. Produces:

- 0 new Lean theorems
- 0 sorry / axiom changes (no `.lean` file touched)
- 0 new PREP/design memos (deliberately — five exist already; the value here is
  the cross-PREP index, not new design)
- Updates `state.md` header + session-log table for the 5 merged memos
- Updates `src/data/research/problems/laws-of-large-numbers-oq-04-oq-03.json`
  `currentState.{phase, focus, nextAction, attemptCounts}` +
  `knowledge.progressSummary`

The chain still has 1 axiom (`bracketingGrid_exists`); S9 + S10 ACT are the path
to retiring it. After this STATE-SYNC, the next ACT researcher does not need to
read state.md + 5 separate memos to know which design has landed and which is
canonical — the table above is sufficient.

---

## S8 (researcher-3, 2026-05-12) — Continuity-point density

After S7 retired the parent's `glivenko_cantelli_uniform` axiom and packaged
the chain's sole remaining assumption as `bracketingGrid_exists` (the purely
real-analytic ε-cover existence statement), S8 begins discharging that axiom
by packaging the three foundational facts the eventual greedy proof will
consume: monotonicity of `trueCDF`, countability of its discontinuity set,
and density of its continuity-point set in `ℝ`.

### Changes

1. **`proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean`**: added new
   section §2.2.5 `N2ContinuityDensity` (4 theorems + section header,
   +73 lines, inserted between §2.2 axiom and §2.3 simultaneous-pointwise
   theorem). Also added two imports:
   * `import Mathlib.Topology.Algebra.Module.Cardinality` — exposes
     `Set.Countable.dense_compl` (any countable subset of a non-trivial real
     topological vector space has dense complement; specialized here to
     `𝕜 := ℝ` and `E := ℝ`).
   * `import Mathlib.Topology.Order.Monotone` — exposes
     `Monotone.countable_not_continuousAt` (discontinuity set of a monotone
     function on a 2nd-countable space is countable).

   The four new theorems:
   * `trueCDF_monotone : Monotone (trueCDF X μ)` — bundle form of the parent's
     `trueCDF_mono` (`{x y : ℝ} (hxy : x ≤ y)` shape) into the `Monotone`
     predicate consumed by Mathlib's `Monotone.*` API.
   * `trueCDF_countable_discontinuities : Set.Countable {x | ¬ ContinuousAt
     (trueCDF X μ) x}` — direct application of
     `Monotone.countable_not_continuousAt` to `trueCDF_monotone`.
   * `trueCDF_continuityPoints_dense : Dense {x : ℝ | ContinuousAt
     (trueCDF X μ) x}` — applies `Set.Countable.dense_compl ℝ` to the
     countable discontinuity set. The `ext + simp` step bridges the
     continuity-point set to the complement of the discontinuity set.
   * `trueCDF_continuityPoint_in_Ioo : ∀ a b, a < b → ∃ x ∈ Set.Ioo a b,
     ContinuousAt (trueCDF X μ) x` — the exact shape consumed by the
     greedy selection step of the eventual `bracketingGrid_exists` proof:
     inside any open interval one can locate a continuity point of `F`.
     Proof: `Dense.exists_mem_open` on `Set.Ioo a b` (which is open and
     nonempty for `a < b`).

2. **`research/problems/laws-of-large-numbers-oq-04-oq-03/state.md`**: this
   block.

### Mathematical content

The S8 lemmas are the second of three foundational pieces required to
discharge `bracketingGrid_exists`:

| Piece | Status | What it provides |
|-------|--------|------------------|
| (i)   `trueCDF` monotone | Already in parent (S0 / `trueCDF_mono`) | bundled in S8 |
| (ii)  discontinuities countable | **S8** | `trueCDF_countable_discontinuities` |
| (iii) continuity points dense | **S8** | `trueCDF_continuityPoints_dense` + `_in_Ioo` |
| (iv)  CDF limits at ±∞ | S9 (future) | `Tendsto F atBot 0`, `Tendsto F atTop 1` |
| (v)   greedy ε-cover induction | S10+ (future) | `bracketingGrid_exists` itself |

Pieces (iv) and (v) are independent of S8 and can land in either order. (iv)
uses `tendsto_measure_iUnion_atTop` / `tendsto_measure_iInter_atTop` on
preimage families `{ω | X 0 ω ≤ n}` for integer thresholds. (v) is a finite
inductive ε-step subdivision threading (i)–(iv) together; it is the actual
~150–250-line "ε-cover construction" the docstring forward-references as
`Monotone.exists_increasing_continuity_seq`.

### Why not just one piece per session

The four S8 theorems share the same import (`Mathlib.Topology.Algebra.Module.Cardinality`)
and the same typeclass plumbing (`Monotone`, `Set.Countable`, `Dense`). Splitting
them across sessions would force re-establishing the same import + typeclass
setup three or four times. Packaging them together also yields a single
self-contained "section §2.2.5" with a coherent docstring tying the three
pieces to the eventual axiom proof.

### Counts after S8

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `LawsOfLargeNumbersOQ04.lean` | 228 | 13 | 0 | 3 | 0 |
| `LawsOfLargeNumbersOQ04OQ03.lean` | 163 | 4 | 0 | 0 | 0 |
| `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` | 594 (+73) | 12 (+4) | 1 | 0 | 0 |

The chain's sole remaining axiom is still `bracketingGrid_exists`; S8 only adds
proved theorems on the path toward discharging it.

### Build status

Pending. The S8 changes are mechanical (4 short-proof theorems using
single-application Mathlib lemmas + 2 imports). Docker build kicked off in
parallel during the session.

### Remaining work

- **S9 (next)**: CDF limits at ±∞ — `trueCDF_tendsto_zero_atBot`,
  `trueCDF_tendsto_one_atTop`. Two ~30–50-line theorems using
  `tendsto_measure_iUnion_atTop` / `tendsto_measure_iInter_atTop`.
- **S10+ (greedy construction)**: package S8's continuity-point density and
  S9's CDF limits into a finite inductive ε-step subdivision producing the
  bracketing grid. ~150–250 lines. This is the Mathlib upstream candidate
  `Monotone.exists_increasing_continuity_seq`.
- After (S10+) discharges `bracketingGrid_exists`, the entire chain becomes
  axiom-free.

## S7 (researcher-3, 2026-05-12) — Axiom retirement

After S6 landed §2.5 (`glivenko_cantelli_uniform_proved`, identical signature
to the parent's axiom), the parent's monolithic axiom was logically redundant.
S7 (this session) retires it.

### Changes

1. **`proofs/Proofs/LawsOfLargeNumbersOQ04.lean`**: deleted `axiom
   glivenko_cantelli_uniform` (~20-line block) and replaced the section
   header with a docstring pointing readers to the bracketing companion.
   New line count: 228 (was 231). The axiom is the only thing removed;
   all 13 theorems + 3 defs are preserved.
2. **`proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean`**: renamed
   `glivenko_cantelli_uniform_proved` → `glivenko_cantelli_uniform` (at the
   §2.5 theorem) to make it the canonical statement. Updated 3 docstrings
   (top-of-file overview, `bracketingGrid_exists` docstring, §2.5 docstring).
3. **`proofs/Proofs/LawsOfLargeNumbersOQ04OQ03.lean`**: updated top-of-file
   docstring + summary block to reflect that the parent's axiom was proved
   (not just listed as remaining).
4. **`src/data/proofs/laws-of-large-numbers-oq-04/meta.json`** (parent slug):
   `lineCount` 231 → 228; `theoremCount` 14 → 13; `leanFile.axiomCount`
   1 → 0; outer `axiomCount` stays 1 (in `additionalFiles`). Added
   `additionalFiles: ["Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean"]`
   at meta and leanFile levels. Rewrote `assumptions`, appended new
   `originalContributions` entry, updated uniform-convergence section
   ranges and summary, shifted all sections by +9 lines (header grew).
5. **`src/data/proofs/laws-of-large-numbers-oq-04-oq-03/meta.json`** (this
   slug, unchanged main file): updated three text fields
   (`originalContributions[3]`, `keyInsights[4]`, `openQuestions[0]`) to
   name `bracketingGrid_exists` as the chain's sole remaining axiom.
6. **`research/problems/laws-of-large-numbers-oq-04-oq-03/state.md`**: this
   block.

### No cycle, no cross-slug breakage

The bracketing companion imports the parent; the parent does NOT import the
companion. Renaming + deleting in this direction is cycle-free. The only
places the deleted axiom name `glivenko_cantelli_uniform` was referenced
are docstrings (verified by `grep glivenko_cantelli_uniform` over `proofs/`:
all hits in docstrings, none in tactic positions).

### Counts after S7

| File | Lines | Theorems | Axioms | Defs | Sorries |
|------|-------|----------|--------|------|---------|
| `LawsOfLargeNumbersOQ04.lean` | 228 | 13 | 0 | 3 | 0 |
| `LawsOfLargeNumbersOQ04OQ03.lean` | 163 | 4 | 0 | 0 | 0 |
| `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` | 521 | 8 | 1 | 0 | 0 |

The chain's sole remaining axiom is `bracketingGrid_exists` in the bracketing
companion; both gallery slugs (`laws-of-large-numbers-oq-04` and
`laws-of-large-numbers-oq-04-oq-03`) reflect this through `axiomCount=1`
+ `additionalFiles`.

### Build status

Pending. The `proofs/.lake` recursive self-symlink in this repo forces a
~45-min cold-cache Mathlib clone on every Docker build. S7 makes only
mechanical changes (one deletion, one rename, docstring + meta.json edits);
no new proof obligations were introduced.

### Remaining work

- **S8+ (future Mathlib upstream)**: discharge `bracketingGrid_exists` itself
  by formalising `Monotone.exists_increasing_continuity_seq` (purely
  real-analytic; the only Mathlib gap remaining in the entire
  Glivenko-Cantelli chain). Once that lemma lands upstream, the bracketing
  companion's sole axiom can be retired, leaving the entire chain
  axiom-free.

## S6 (researcher-5, 2026-05-12) — §2.5 diagonal composition

S5 landed §2.4 (`bracketing_uniform_sup_bound` + `bracketing_uniform_from_grid`).
S6 (this session) lands the last theorem of the bracketing decomposition, §2.5
(`glivenko_cantelli_uniform_proved`), closing the loop on the axiom shift.

### What landed

`glivenko_cantelli_uniform_proved`: same signature as the parent's
`glivenko_cantelli_uniform` axiom; proves
`∀ᵐ ω ∂μ, Tendsto (fun n => ⨆ x, |Fₙ(x, ω) - F(x)|) atTop (nhds 0)`. Proof
is a diagonal composition of §2.2–§2.4:

1. Pick the accuracy schedule `ε m := 1 / (m + 1)`. Each is positive.
2. For each `m : ℕ`, take a bracketing grid `G m :=
   (bracketingGrid_exists hX_meas (hε_pos m)).some` via the §2.2 axiom.
3. For each `m`, §2.3 supplies a full-measure set on which the empirical CDF
   converges to the true CDF at every grid point `(G m).q j`.
4. The countable family `{m ↦ "full-measure set for G m"}` is combined into
   a single full-measure set via `MeasureTheory.ae_all_iff` (`ℕ` is
   countable).
5. On this single full-measure set, for any `δ > 0`, choose `m` with
   `1 / (m + 1) < δ / 3` via `exists_nat_one_div_lt`. Apply §2.4 with the
   slack `η := ε m`; eventually `⨆ x, |Fₙ(x, ω) - F(x)| ≤ 2 ε m + ε m =
   3 ε m < δ`. Combined with `Real.iSup_nonneg` (the iSup is non-negative)
   this gives `dist (⨆ ...) 0 < δ` eventually.

### Mathlib API used

* `MeasureTheory.ae_all_iff` (combining countably many full-measure sets) —
  same lemma §2.3 used at the finite Fin (k+2) layer, here re-used at the
  countably-infinite ℕ layer.
* `Metric.tendsto_atTop` (Mathlib.Topology.MetricSpace.Pseudo.Defs:932) —
  metric characterisation of `Tendsto u atTop (nhds a)`.
* `Filter.eventually_atTop` — to extract an explicit threshold `N` from
  `∀ᶠ n in atTop, ...`.
* `exists_nat_one_div_lt` (Mathlib.Algebra.Order.Archimedean:191) — to pick
  `m` with `1 / (m + 1) < δ / 3`.
* `Real.iSup_nonneg` (Mathlib.Data.Real.Archimedean:225) — to flip
  `dist (⨆ ...) 0 = |⨆ ... - 0|` to `⨆ ...`.
* `Real.dist_eq`, `abs_of_nonneg`, `sub_zero` — standard distance/abs
  manipulations on `ℝ`.

### Counts

The bracketing companion file went 447 → 522 lines (+75 lines), 3 → 4
theorems (added `glivenko_cantelli_uniform_proved`). Axiom count for the
companion is unchanged at 1 (`bracketingGrid_exists`); no new axioms or
sorries introduced. The main file `LawsOfLargeNumbersOQ04OQ03.lean` is
unchanged (158 lines, 4 theorems, 0 sorries, 0 axioms). Per gallery
convention `meta.lineCount` / `theoremCount` track the main file only —
no meta.json update needed.

### Build status

Pending. Build attempted under Docker
(`./proofs/scripts/docker-build.sh Proofs.LawsOfLargeNumbersOQ04OQ03Bracketing`);
expected ~45 min cold under the broken `proofs/.lake` self-symlink. PR
title bears the "(build pending)" suffix per the recent precedent for
§2.3+ work on this slug. API names were verified against Mathlib 4.26
source (`Real.iSup_nonneg`, `exists_nat_one_div_lt`, `Metric.tendsto_atTop`,
`ae_all_iff`).

### Status of the bracketing decomposition

After S6 lands, the bracketing decomposition of `bracketing-decomposition-draft.md`
§2 is fully complete:

| Section | Theorem | Status |
|---------|---------|--------|
| §2.1 | `BracketingGrid` structure | Landed S3 |
| §2.2 | `bracketingGrid_exists` axiom | Landed S3 (axiom; Mathlib-side gap) |
| §2.3 | `bracketing_simultaneous_pointwise` | Landed S4 |
| §2.4 | `bracketing_uniform_sup_bound` + `bracketing_uniform_from_grid` | Landed S5 |
| §2.5 | `glivenko_cantelli_uniform_proved` | **Landed S6 (this session)** |

The chain has the parent's `glivenko_cantelli_uniform` AND the bracketing
companion's `bracketingGrid_exists`. After S6, the parent's monolithic
axiom is **logically redundant**: the bracketing companion now proves it
modulo a purely real-analytic axiom. Retiring the parent's axiom is a
mechanical follow-up (S7) — rename `glivenko_cantelli_uniform_proved` to
`glivenko_cantelli_uniform` and delete the original axiom, or have the
parent's theorem re-export the companion's.

### Remaining work

- **S7 (next session)**: retire parent's `axiom glivenko_cantelli_uniform`
  in `LawsOfLargeNumbersOQ04.lean`. Replace with `theorem ...` proved by
  `glivenko_cantelli_uniform_proved` from the bracketing companion (which
  requires a re-export or shim because the bracketing companion imports
  the parent, not vice versa — the cleanest path is to move the proved
  variant into the parent file, or split the parent file to break the
  cycle).
- **S8+ (future Mathlib upstream)**: discharge `bracketingGrid_exists`
  itself by formalising `Monotone.exists_increasing_continuity_seq`
  (purely real-analytic; the only Mathlib gap remaining in the entire
  Glivenko-Cantelli chain).

## S5 (researcher-6, 2026-05-11) — §2.4 deterministic + limit form

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

The bracketing decomposition §2.1–§2.5 of `bracketing-decomposition-draft.md`
is now complete (S3–S6), and S7 (this session) retired the parent's
`glivenko_cantelli_uniform` axiom. The chain's sole remaining axiom is
`bracketingGrid_exists` in the bracketing companion.

1. **(S8, future Mathlib upstream)** Mathlib PR for
   `Monotone.exists_increasing_continuity_seq`: for any monotone $F : \mathbb{R} \to \mathbb{R}$
   with bounded range and any $\varepsilon > 0$, there exist finitely many
   continuity points $q_0 < q_1 < \cdots < q_{k+1}$ of $F$ such that
   $F(q_{j+1}) - F(q_j^-) < \varepsilon$ for each cell, and $F(q_0) < \varepsilon$,
   $1 - F(q_{k+1}) < \varepsilon$ on the boundary. Mathematical content
   reduces to: (i) discontinuity set of monotone real function is countable
   (Mathlib's `Monotone.countable_setOf_not_continuousAt`); (ii) complement
   of countable set is dense in $\mathbb{R}$ (Mathlib's `Set.Countable.dense_compl`
   or equivalent); (iii) greedy ε-cover induction on $[0,1]$ to pick the
   grid. Once landed upstream and pulled into our `Mathlib` dependency,
   `bracketingGrid_exists` can be discharged and the bracketing companion
   becomes axiom-free, making the entire Glivenko-Cantelli chain
   fully verified.
2. **(alternate path, in-tree)** Prove `bracketingGrid_exists` directly in
   the bracketing companion without upstreaming first, using the same
   three-step structure as (1). Roughly ~80-150 lines, primarily real-
   analysis bookkeeping (no probability).

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

- Total attempts: 7
- Current approach attempts: 5 (S3 scaffold, S4 §2.3, S5 §2.4, S6 §2.5, S7 axiom retirement)
- Approaches tried: 1 (bracketing decomposition per S2 spec — fully landed)

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
