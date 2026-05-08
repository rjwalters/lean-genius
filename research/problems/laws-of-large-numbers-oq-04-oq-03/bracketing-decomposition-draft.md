# Bracketing Decomposition: Discharging `glivenko_cantelli_uniform`

**Session**: 2 (researcher-9, 2026-05-08)
**Parent**: `LawsOfLargeNumbersOQ04.lean` (Glivenko–Cantelli, 1 axiom)
**Sibling completed**: `LawsOfLargeNumbersOQ04OQ03.lean` (2 of 3 axioms eliminated)
**Status**: Pre-formalization specification — no Lean code committed to gallery, no
PR opened upstream yet.

This document specifies a decomposition of the remaining axiom

```
axiom glivenko_cantelli_uniform [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iid : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => ⨆ x : ℝ, |empiricalCDF X n x ω - trueCDF X μ x|)
        Filter.atTop (nhds 0)
```

into three named pieces. Two of the three are routine and provable from what
Mathlib 4.26 already has; the third is the genuine Mathlib gap that should be
filled (separately) to retire the last GC axiom. The aim of this note is to
isolate the gap so that future work (in this entry or upstream Mathlib) has a
concrete, well-typed target instead of a monolithic uniformity statement.

---

## 1. Why this decomposition

The classical bracketing argument has three independent ingredients:

1. **Grid existence (analytic, on F)**. For each ε > 0 there exist finitely many
   continuity points `q₀ < q₁ < ⋯ < q_{k+1}` of `F` such that
   `F(q_{j+1}) − F(q_j) < ε` for every `j ∈ {0, …, k}`,
   `F(q_0) < ε`, `F(q_{k+1}) > 1 − ε`. Equivalently, the partial range
   `F(q_0), F(q_1), …, F(q_{k+1}) ∈ [0,1]` is an ε-cover of `[0,1]` whose nodes
   are continuity points of `F`. **This is the genuinely missing piece in
   Mathlib 4.26.**
2. **Simultaneous pointwise convergence (probabilistic, finite intersection)**.
   Given a finite grid, the SLLN-derived a.s. pointwise convergence
   `Fₙ(qⱼ) → F(qⱼ)` upgrades to *simultaneous* a.s. convergence at all `k+2`
   grid points by countable (in fact finite) intersection of full-measure sets.
   **This is routine using `MeasureTheory.ae_all_iff`** (or its finite specialisation),
   already available in Mathlib.
3. **Uniform sup-bound from the grid (deterministic, monotone interpolation)**.
   Given that `Fₙ` and `F` are non-decreasing and that `Fₙ(qⱼ) → F(qⱼ)`
   simultaneously at the `k+2` grid points, on the deterministic side
   `sup_{x∈ℝ} |Fₙ(x) − F(x)| ≤ max_{j} |Fₙ(qⱼ) − F(qⱼ)| + ε`, hence
   `lim sup_n sup_x |Fₙ(x) − F(x)| ≤ ε` a.s., and ε ↓ 0 finishes via a
   countable union of null sets along ε = 1/m. **This is provable from the
   parent file's existing `empiricalCDF_mono` and `trueCDF_mono` plus elementary
   real analysis.**

Decomposing into (1), (2), (3) makes the Mathlib gap localised to (1) — a
purely real-analytic statement about monotone functions — and turns the
remaining axiom into a clean one-line `theorem` from three building blocks.

---

## 2. Targeted Lean signatures

The decomposition reorganises `glivenko_cantelli_uniform` as three
named declarations plus a one-line composition theorem. All four belong in
a new file `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` (sibling of the existing
file, importing it). The opens and `variable`s are inherited from
`LawsOfLargeNumbersOQ04`.

### 2.1 The bracketing-grid predicate

```lean
/-- An ε-bracketing grid for the CDF F is a finite increasing sequence of
    continuity points whose F-images cover [0,1] in steps of size ≤ ε. -/
structure BracketingGrid (F : ℝ → ℝ) (ε : ℝ) where
  k        : ℕ
  q        : Fin (k + 2) → ℝ
  mono     : StrictMono q
  cont     : ∀ j, ContinuousAt F (q j)
  step_le  : ∀ j : Fin (k + 1), F (q j.succ) - F (q j.castSucc) ≤ ε
  left_le  : F (q 0) ≤ ε
  right_ge : F (q (Fin.last (k + 1))) ≥ 1 - ε
```

Notes:
- `Fin (k + 2)` indexes the grid points `q₀, …, q_{k+1}`. `Fin.castSucc` /
  `Fin.succ` give consecutive pairs, indexed by `Fin (k + 1)`.
- `cont` requires *F-continuity* at each grid point — this is the dispensable
  but useful side condition that makes the right-continuous CDF agree with the
  pointwise convergence at the node, removing the need to distinguish
  `F(qⱼ⁻)` from `F(qⱼ)`.
- For a CDF derived from a probability measure, `F` is right-continuous and
  bounded in `[0, 1]`. The two boundary inequalities `left_le` and `right_ge`
  encode that the grid effectively covers `(-∞, ∞)` modulo ε mass at each end.

### 2.2 Grid existence (the one piece that remains an axiom)

```lean
/-- **Mathlib gap.** For any CDF derived from a probability measure on ℝ and
    any ε > 0, an ε-bracketing grid exists. Reduces to: the discontinuity set
    of a monotone function ℝ → ℝ is countable, hence its complement is dense;
    pick continuity points one at a time so each F-step is ≤ ε. -/
axiom bracketingGrid_exists [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (BracketingGrid (trueCDF X μ) ε)
```

**Why this is the only genuinely missing piece.** The Mathlib facts that would
discharge this axiom are:

| Mathlib fact (target) | Status |
|----------------------|--------|
| Monotone real functions have at most countably many points of discontinuity | known mathematically, present in Mathlib as `Monotone.countable_setOf_not_continuousAt` |
| Countable subsets of ℝ have dense complement | derivable from `Set.Countable.dense_compl` (or via metric-space density of complements of countable sets) |
| `trueCDF` derived from a probability measure is monotone, right-continuous, with limits 0 at −∞ and 1 at +∞ | partial: `trueCDF_mono` is in the parent file; the right-continuity + endpoint-limit properties are not yet stated for `trueCDF` |
| Constructive ε-cover by continuity points: `∀ ε > 0, ∃ k, q : Fin (k+2) → ℝ, …` | **missing** — needs an induction over `[0,1]` partitioning by F-mass, choosing each `q_{j+1}` as the smallest continuity point with `F(q_{j+1}) > F(q_j) + ε/2` (say) |

Concretely, an upstream Mathlib contribution that proves
`bracketingGrid_exists` would look like (sketch):

```lean
theorem Monotone.exists_increasing_continuity_seq
    {F : ℝ → ℝ} (hF_mono : Monotone F)
    (hF_bounded : ∀ x, F x ∈ Set.Icc 0 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (k : ℕ) (q : Fin (k + 2) → ℝ),
      StrictMono q ∧ (∀ j, ContinuousAt F (q j)) ∧
      (∀ j : Fin (k + 1), F (q j.succ) - F (q j.castSucc) ≤ ε) ∧
      F (q 0) ≤ ε ∧ F (q (Fin.last (k + 1))) ≥ 1 - ε
```

This is a *purely real-analytic* statement, free of probability theory, and is
the natural Mathlib home for the bracketing scaffolding.

### 2.3 Simultaneous pointwise convergence (provable, routine)

```lean
/-- **Provable** in this file. Given a finite (Fin (k+2)-indexed) grid, the
    a.s. pointwise convergence `Fₙ(qⱼ) → F(qⱼ)` from the SLLN holds
    *simultaneously* at all grid points a.s. Routine application of
    `MeasureTheory.ae_all_iff` (countable specialisation to `Fin (k+2)`). -/
theorem bracketing_simultaneous_pointwise [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iid : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {k : ℕ} (q : Fin (k + 2) → ℝ) :
    ∀ᵐ ω ∂μ, ∀ j : Fin (k + 2),
      Filter.Tendsto (fun n => empiricalCDF X n (q j) ω)
        Filter.atTop (nhds (trueCDF X μ (q j)))
```

**Proof sketch (10–20 lines).**
- Apply `empiricalCDF_pointwise_convergence hX_meas hX_iid hX_ident (q j)` for
  each `j : Fin (k + 2)` to get a full-measure set `S j` on which
  `Fₙ(qⱼ) → F(qⱼ)`.
- Use `MeasureTheory.ae_all_iff` (or `ae_ball_iff`) to commute the universal
  over `Fin (k + 2)` with the a.s. quantifier. `Fin (k + 2)` is countable
  (in fact finite), so the intersection of full-measure sets remains full
  measure.
- Conclude: `∀ᵐ ω ∂μ, ∀ j, Tendsto (Fₙ(qⱼ)·) atTop (nhds (F(qⱼ)))`.

Mathlib references:
- `MeasureTheory.ae_all_iff` (countable conjunction of a.s. statements).
- `empiricalCDF_pointwise_convergence` (parent file, line 144).

### 2.4 Uniform sup-bound from grid + simultaneous (provable, routine)

```lean
/-- **Provable** in this file (deterministic, no probability). Given a
    BracketingGrid and a sample point `ω` at which `Fₙ(qⱼ) → F(qⱼ)`
    simultaneously at every grid node, the sup-error of `Fₙ(·, ω)` against
    `F` is asymptotically bounded by `2ε`. -/
theorem bracketing_uniform_from_grid [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (G : BracketingGrid (trueCDF X μ) ε)
    {ω : Ω}
    (hpw : ∀ j : Fin (G.k + 2),
        Filter.Tendsto (fun n => empiricalCDF X n (G.q j) ω)
          Filter.atTop (nhds (trueCDF X μ (G.q j)))) :
    Filter.Tendsto
      (fun n => ⨆ x : ℝ, |empiricalCDF X n x ω - trueCDF X μ x|)
      Filter.atTop (nhds_le_of (· ≤ 2 * ε))
```

**Proof sketch (~50 lines).**
For brevity write `Fₙ := empiricalCDF X n · ω` and `F := trueCDF X μ`. Both are
non-decreasing.

Step 1 (one-sided bracketing). For any `x ∈ ℝ` we either have `x < q₀`,
`x ≥ q_{k+1}`, or `q_j ≤ x ≤ q_{j+1}` for some `j ∈ Fin (k+1)`. In each case
monotonicity yields:

- If `q_j ≤ x ≤ q_{j+1}`:
  ```
  Fₙ(x) − F(x) ≤ Fₙ(q_{j+1}) − F(q_j)
              = (Fₙ(q_{j+1}) − F(q_{j+1})) + (F(q_{j+1}) − F(q_j))
              ≤ |Fₙ(q_{j+1}) − F(q_{j+1})| + ε,         [by step_le]
  Fₙ(x) − F(x) ≥ Fₙ(q_j) − F(q_{j+1})
              = (Fₙ(q_j) − F(q_j)) + (F(q_j) − F(q_{j+1}))
              ≥ −|Fₙ(q_j) − F(q_j)| − ε.
  ```
  Hence `|Fₙ(x) − F(x)| ≤ max{|Fₙ(q_j) − F(q_j)|, |Fₙ(q_{j+1}) − F(q_{j+1})|} + ε`.

- If `x < q_0`: monotonicity gives `0 ≤ F(x) ≤ F(q_0) ≤ ε` (the boundary
  inequality `left_le`) and `0 ≤ Fₙ(x) ≤ Fₙ(q_0)`. Combine to get
  `|Fₙ(x) − F(x)| ≤ Fₙ(q_0) + ε ≤ |Fₙ(q_0) − F(q_0)| + 2ε`.

- If `x ≥ q_{k+1}`: similarly using `right_ge`,
  `|Fₙ(x) − F(x)| ≤ |Fₙ(q_{k+1}) − F(q_{k+1})| + 2ε`.

Step 2 (sup-bound). Taking `sup_x` of the case-split bound gives
`sup_x |Fₙ(x) − F(x)| ≤ max_{j ∈ Fin (k+2)} |Fₙ(q_j) − F(q_j)| + 2ε`.

Step 3 (limsup → 2ε). Apply `hpw` to each `j`: each `|Fₙ(q_j) − F(q_j)| → 0`,
so the finite max → 0. Hence
`lim sup_n sup_x |Fₙ(x) − F(x)| ≤ 2ε`, which is what the theorem states.

Mathlib references:
- `empiricalCDF_mono`, `trueCDF_mono` (parent file).
- `Finset.sup_le_iff`, `abs_le_iff` (elementary).
- `Filter.Tendsto.sup_max` or the explicit ε-N argument for finite max of
  null sequences.

(The `nhds_le_of (· ≤ 2 * ε)` in the conclusion is informal notation; the
precise Lean form uses `Filter.limsup` or an `eventually` upper bound. See §3.)

### 2.5 Composition: deriving the original axiom

```lean
/-- **Provable** in this file once §2.2–§2.4 are in place. The original
    bracketing axiom follows by combining grid existence (§2.2) with
    simultaneous pointwise convergence (§2.3) and the deterministic uniform
    bound (§2.4), then a countable union of null sets along ε = 1/m. -/
theorem glivenko_cantelli_uniform_proved [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iid : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => ⨆ x : ℝ, |empiricalCDF X n x ω - trueCDF X μ x|)
        Filter.atTop (nhds 0)
```

**Proof sketch.** For every `m : ℕ`, set `ε_m := 1/(m+1)`. Apply
`bracketingGrid_exists hX_meas (1/(m+1) > 0)` to get `G_m`. Apply
`bracketing_simultaneous_pointwise` to `G_m.q` to get the full-measure set
`A_m ⊆ Ω` on which simultaneous pointwise convergence at `G_m`'s grid holds.
On `⋂ m, A_m` (countable intersection of full-measure sets, hence full measure),
apply `bracketing_uniform_from_grid` for each `m` to get
`lim sup_n sup_x |Fₙ(x) − F(x)| ≤ 2/(m+1)` for every `m`, hence
`lim sup_n sup_x |Fₙ(x) − F(x)| = 0`, equivalently
`Tendsto (sup_x |Fₙ − F|·) atTop (nhds 0)`.

Mathlib references:
- `MeasureTheory.measure_iInter_eq_one_iff` / `ae_iInter_iff` (countable
  intersection of full-measure sets).
- `Tendsto.le_const_of_limsup_le` or the elementary "`lim sup ≤ c` for every
  `c > 0` ⇒ `lim = 0`" (for nonneg sequences).

---

## 3. Mathlib API audit (Mathlib 4.26)

The decomposition is *closed* — no further axioms — once one Mathlib lemma is
imported and one is proved. Here is the full audit.

| Used by | Mathlib name | Status | Notes |
|--------|-------------|--------|-------|
| §2.3 | `MeasureTheory.ae_all_iff` | present | also `MeasureTheory.ae_ball_iff` for `Fin n`-indexed |
| §2.3 | `Filter.Tendsto.sub` etc. | present | basic limit lemmas |
| §2.4 | `Finset.sup_le_iff`, `abs_le_iff`, `max_le_iff` | present | elementary order |
| §2.4 | parent's `empiricalCDF_mono`, `trueCDF_mono`, `empiricalCDF_nonneg` | present | already proved in `LawsOfLargeNumbersOQ04` |
| §2.4 | `iSup_le` / `Real.iSup_le_iff` | present | sup as iSup over ℝ; care needed for the codomain bound |
| §2.5 | `MeasureTheory.ae_iInter_iff` (or sequential `ae_all_iff`) | present | countable intersection of a.s. sets |
| §2.5 | `Tendsto_of_le_const_for_all_pos` / `Tendsto_zero_iff_isLittleO` | present | nonneg sequence ≤ c for every c > 0 ⇒ tends to 0 |
| §2.2 | `Monotone.countable_setOf_not_continuousAt` | present | discontinuity set of monotone ℝ → ℝ is countable |
| §2.2 | `Set.Countable.dense_compl` (or eqv. via `denseRange_compl_of_countable`) | present (or trivial) | complement of countable in ℝ is dense |
| §2.2 | constructive ε-cover by continuity points: `Monotone.exists_increasing_continuity_seq` (proposed) | **MISSING** | one Mathlib PR's worth of work |

Out of ten lemmas required by the decomposition, **nine are already in
Mathlib 4.26**. The tenth — a constructive ε-cover induction over `[0,1]` for
a monotone real function, choosing continuity points — is the entire
remaining gap.

---

## 4. Forward research path

**Short term (this entry).**
Promote §2.3 and §2.4 from this draft into a real Lean file
`proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` *that compiles*,
with `bracketingGrid_exists` left as the sole `axiom` in that file. This:

- replaces the existing single `glivenko_cantelli_uniform` axiom (one big
  axiom over a complex probabilistic statement) with a single `bracketingGrid_exists`
  axiom (a smaller, purely analytic statement) plus three `theorem`s;
- precisely localises the Mathlib gap in `meta.json` (axiom remains 1, but
  the *content* of the axiom shrinks to the analytic ε-cover);
- gives a future researcher a build-tested platform from which to attempt
  upstream Mathlib `Monotone.exists_increasing_continuity_seq`.

**Medium term (Mathlib upstream).**
File a Mathlib PR proving `Monotone.exists_increasing_continuity_seq`
(signature in §2.2), in
`Mathlib/Analysis/SpecialFunctions/Monotone/Bracketing.lean` (or wherever the
existing `Monotone.countable_setOf_not_continuousAt` lives). On Mathlib bump,
import and discharge `bracketingGrid_exists`; the axiom count of
`LawsOfLargeNumbersOQ04` drops from 1 to 0, and `LawsOfLargeNumbersOQ04OQ03`
becomes a fully axiom-free formalization of the *full* Glivenko–Cantelli
theorem (uniformity included).

**Longer term (VC-class generalisation).**
The reformulated open question for this slug is "What is the minimal Mathlib
infrastructure for VC-class Glivenko–Cantelli." The decomposition above is a
*sufficient* infrastructure for the threshold class
`{1_{· ≤ x} : x ∈ ℝ}`. A VC-class generalisation would replace §2.2 (the
specific ε-cover by continuity points) with a Vapnik–Chervonenkis
symmetrization + Sauer–Shelah finite-shattering argument, plus a
Talagrand-style empirical-process maximal inequality. Both are Mathlib gaps
and are independent of §2.2; the threshold-class case (this file) does not
need them.

---

## 5. Honesty & scope notes

- Nothing in this draft has been compiled. The Lean signatures in §2 are
  intended as *targets* for the next session; type-correctness has been
  hand-checked against the parent file's namespacing/imports but not by the
  Lean elaborator.
- The four theorems §2.3, §2.4, §2.5 plus the §2.2 axiom-replacement are
  expected to total ~150 lines once realised in Lean. The hardest piece by
  far is §2.4's case analysis (~50 lines) — for VC-class generalisation, this
  becomes the symmetrization/Sauer–Shelah step instead.
- This draft does **not** modify the gallery entry's `verified` status.
  `LawsOfLargeNumbersOQ04OQ03.lean` continues to be `verified`/0 axioms;
  the decomposition lives entirely outside that file in (a future)
  `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` that consumes the parent's
  `glivenko_cantelli_uniform` axiom and decomposes it.
- The §2.5 composition is a strict refinement: it would let the parent file
  `LawsOfLargeNumbersOQ04` re-export `glivenko_cantelli_uniform` as a
  `theorem` (modulo the smaller `bracketingGrid_exists` axiom in the
  bracketing file).

---

## 6. Next-action checklist (for the session that promotes this to Lean)

1. Create `proofs/Proofs/LawsOfLargeNumbersOQ04OQ03Bracketing.lean` with imports
   `Proofs.LawsOfLargeNumbersOQ04OQ03`, `Mathlib.MeasureTheory.Measure.AEMeasurable`,
   `Mathlib.Analysis.SpecialFunctions.MonotoneContinuity` (or whatever houses
   `Monotone.countable_setOf_not_continuousAt`).
2. Define `BracketingGrid` (§2.1).
3. State `bracketingGrid_exists` as an `axiom` (§2.2).
4. Prove `bracketing_simultaneous_pointwise` (§2.3) — short.
5. Prove `bracketing_uniform_from_grid` (§2.4) — case analysis, ~50 lines.
6. Prove `glivenko_cantelli_uniform_proved` (§2.5) — composition, ~20 lines.
7. Build via `./proofs/scripts/docker-build.sh Proofs.LawsOfLargeNumbersOQ04OQ03Bracketing`
   (allow 45 min for the first build; broken `proofs/.lake` symlink forces a
   fresh Mathlib clone).
8. Add a one-line companion file
   `LawsOfLargeNumbersOQ04OQ03BracketingAristotle.lean` if any §2.4 sublemma
   ends up as a `sorry` (e.g., the explicit `max_j |Fₙ(qⱼ) − F(qⱼ)| → 0`
   step) for Aristotle to discharge.
