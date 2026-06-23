/-
# Glivenko-Cantelli: Bracketing Decomposition Scaffold
(laws-of-large-numbers-oq-04-oq-03 — Session 3)

The parent file `LawsOfLargeNumbersOQ04` previously discharged the uniform
Glivenko-Cantelli theorem with one axiom, `glivenko_cantelli_uniform`, that
bundled the entire finite-bracketing argument as a single black box. Session 2's
`bracketing-decomposition-draft.md` decomposed that axiom orthogonally into
three pieces:

  1. **Grid existence** (analytic, on F): for every ε > 0 there exist finitely
     many continuity points q₀ < ⋯ < q_{k+1} of F covering [0,1] in F-jumps ≤ ε.
     This is the only piece missing from Mathlib 4.26.
  2. **Simultaneous pointwise convergence**: provable from `MeasureTheory.ae_all_iff`
     + parent's `empiricalCDF_pointwise_convergence`. ~10–20 lines.
  3. **Uniform sup-bound from grid**: deterministic monotone interpolation,
     provable from parent's `empiricalCDF_mono`/`trueCDF_mono`. ~50 lines.

Session 3 (this file) ships pieces (1) and a typed scaffold:

  * `BracketingGrid F ε` (§2.1): structure encoding an ε-bracketing grid for a
    CDF F. Five fields: a strict-monotone Fin (k+2)-indexed sequence of
    continuity points, with an interior step bound and two boundary bounds.
  * `bracketingGrid_exists` (§2.2): the sole new axiom. Asserts existence of a
    grid for any CDF derived from a probability measure on ℝ. Replaces the
    parent's monolithic `glivenko_cantelli_uniform` once §2.3–§2.5 land.

Sessions 4–6 filled in §2.3 (`bracketing_simultaneous_pointwise`),
§2.4 (`bracketing_uniform_from_grid`), and §2.5 (`glivenko_cantelli_uniform`,
which proves the parent's uniform-convergence statement from the smaller
real-analytic `bracketingGrid_exists`).

## Axiom retirement (S7)

After §2.3–§2.5 landed, the parent's monolithic `glivenko_cantelli_uniform`
axiom became logically redundant. S7 retired it: the axiom was deleted from
`LawsOfLargeNumbersOQ04.lean`, and §2.5's proved variant was renamed from
`glivenko_cantelli_uniform_proved` to `glivenko_cantelli_uniform` to become
the canonical statement. The chain now has a single axiom
(`bracketingGrid_exists`), whose mathematical content is purely real-analytic
(no probability) and is the natural Mathlib home for upstream contribution as
`Monotone.exists_increasing_continuity_seq`.

## Build status

Build pending. The `proofs/.lake` recursive self-symlink in this repo forces a
~45-min cold-cache Mathlib clone on every build (per memory feedback). The
file is small (~50 lines, 1 structure + 1 axiom), uses standard Mathlib API
already exercised in the parent (`ContinuousAt`, `Fin (k+2)`, `StrictMono`),
and has no novel proof obligations. Confidence the file type-checks is high;
build verification deferred to S4 alongside the §2.3–§2.5 theorem additions.
-/

import Proofs.LawsOfLargeNumbersOQ04OQ03
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.Topology.Order.Monotone
import Mathlib.Probability.CDF

namespace GlivenkoCantelli

open MeasureTheory ProbabilityTheory Set

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

-- ============================================================================
-- §2.1: The bracketing-grid predicate
-- ============================================================================

/-- An **ε-bracketing grid** for a CDF `F : ℝ → ℝ` is a finite increasing
    sequence of `F`-continuity points whose `F`-images cover `[0, 1]` in steps
    of size at most `ε`.

    The five fields capture:
    * `k`        — number of interior cells (so the grid has `k + 2` nodes);
    * `q`        — the strictly increasing sequence of nodes,
                   indexed by `Fin (k + 2)`;
    * `mono`     — strict monotonicity of `q`;
    * `cont`     — `F` is continuous at each grid node;
    * `step_le`  — interior `F`-jump bound: `F(qⱼ₊₁) − F(qⱼ) ≤ ε` for each
                   adjacent pair, indexed by `Fin (k + 1)` via
                   `Fin.castSucc`/`Fin.succ`;
    * `left_le`  — left boundary mass bound: `F(q₀) ≤ ε`;
    * `right_ge` — right boundary mass bound: `F(q_{k+1}) ≥ 1 − ε`.

    The `cont` side condition makes the right-continuous CDF agree with
    pointwise convergence at each node and removes the need to distinguish
    `F(qⱼ⁻)` from `F(qⱼ)` in the deterministic uniform-bound argument
    (§2.4 of `bracketing-decomposition-draft.md`). -/
structure BracketingGrid (F : ℝ → ℝ) (ε : ℝ) where
  k        : ℕ
  q        : Fin (k + 2) → ℝ
  mono     : StrictMono q
  cont     : ∀ j, ContinuousAt F (q j)
  step_le  : ∀ j : Fin (k + 1), F (q j.succ) - F (q j.castSucc) ≤ ε
  left_le  : F (q 0) ≤ ε
  right_ge : F (q (Fin.last (k + 1))) ≥ 1 - ε

-- ============================================================================
-- §2.2: Grid existence (the one axiom that remains)
-- ============================================================================

/-- **Mathlib gap** (axiomatized). For any CDF derived from a probability
    measure on ℝ and any `ε > 0`, an ε-bracketing grid for the CDF exists.

    The mathematical content reduces to: the discontinuity set of a monotone
    function `ℝ → ℝ` is countable
    (`Monotone.countable_setOf_not_continuousAt`), hence its complement is
    dense; pick continuity points greedily so that each `F`-step is at most
    `ε`. The endpoints are handled by the bounded-range property of CDFs.

    This is the natural Mathlib home for the upstream lemma
    `Monotone.exists_increasing_continuity_seq`
    (`bracketing-decomposition-draft.md` §2.2 sketch).

    After S7 retired the parent's monolithic `glivenko_cantelli_uniform`,
    this single axiom is the chain's sole remaining assumption — narrowing
    the open mathematical content from a probabilistic uniformity statement
    to a purely real-analytic ε-cover induction. -/
axiom bracketingGrid_exists [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i))
    {ε : ℝ} (hε : 0 < ε) :
    Nonempty (BracketingGrid (trueCDF X μ) ε)

-- ============================================================================
-- §2.2.5: Continuity-point density (foundation for `bracketingGrid_exists`)
-- ============================================================================

/-! ### Continuity-point density (S8)

The mathematical content of `bracketingGrid_exists` reduces to three real-analytic
facts about a CDF `F = trueCDF X μ`:

  (i)   `F` is monotone non-decreasing (already in the parent as `trueCDF_mono`);
  (ii)  the discontinuity set of a monotone function `ℝ → ℝ` is countable
        (Mathlib's `Monotone.countable_not_continuousAt`);
  (iii) the complement of a countable subset of ℝ is dense
        (Mathlib's `Set.Countable.dense_compl`, applied with `𝕜 := ℝ`).

S8 packages these three facts as named lemmas so the eventual greedy
construction discharging `bracketingGrid_exists` (S9+) can quote them without
re-deriving the typeclass plumbing each time. None of the three pieces is novel
mathematics; the value is in pre-packaging the exact shape consumed by the
boundary/interior cell selection (`ContinuousAt F (q j)` for each grid node). -/

/-- `trueCDF X μ` packaged as a `Monotone` function `ℝ → ℝ`.
    Bundle form of the parent's `trueCDF_mono`; consumed by
    `Monotone.countable_not_continuousAt` below. -/
theorem trueCDF_monotone [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) :
    Monotone (trueCDF X μ) :=
  fun _ _ hxy => trueCDF_mono X hxy

/-- The set of discontinuity points of `trueCDF X μ` is countable.
    Direct application of `Monotone.countable_not_continuousAt` to
    `trueCDF_monotone`. -/
theorem trueCDF_countable_discontinuities [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) :
    Set.Countable {x : ℝ | ¬ ContinuousAt (trueCDF X μ) x} :=
  (trueCDF_monotone X).countable_not_continuousAt

/-- The set of continuity points of `trueCDF X μ` is dense in `ℝ`.
    Follows from `trueCDF_countable_discontinuities` via
    `Set.Countable.dense_compl` (𝕜 := ℝ): any countable subset of a
    non-trivial real topological vector space has dense complement.

    This is the exact shape the eventual greedy construction will consume:
    inside any open interval `(a, b)` containing a candidate grid node, a
    continuity point of `F` exists, so the `cont` field of `BracketingGrid`
    can always be discharged. -/
theorem trueCDF_continuityPoints_dense [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) :
    Dense {x : ℝ | ContinuousAt (trueCDF X μ) x} := by
  -- Continuity-points = complement of discontinuity set.
  have h_eq : {x : ℝ | ContinuousAt (trueCDF X μ) x} =
      {x : ℝ | ¬ ContinuousAt (trueCDF X μ) x}ᶜ := by
    ext x; simp
  rw [h_eq]
  -- Apply `Set.Countable.dense_compl` with 𝕜 = ℝ (the ambient field is ℝ
  -- and the module is `ℝ` over itself; all topology / module typeclasses
  -- are stdlib).
  exact (trueCDF_countable_discontinuities X).dense_compl ℝ

/-- Inside any open interval `(a, b)` with `a < b`, a continuity point of
    `trueCDF X μ` exists. This is the form consumed in the greedy
    selection step of the eventual `bracketingGrid_exists` proof. -/
theorem trueCDF_continuityPoint_in_Ioo [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) {a b : ℝ} (hab : a < b) :
    ∃ x ∈ Set.Ioo a b, ContinuousAt (trueCDF X μ) x := by
  -- v4.26.0 elaborator no longer defers typeclass resolution on bare `have`;
  -- annotate the `Dense` set to fix `μ` for `IsProbabilityMeasure μ`.
  have h_dense : Dense {x : ℝ | ContinuousAt (trueCDF X μ) x} :=
    trueCDF_continuityPoints_dense X
  -- `Dense` + nonempty open set ⇒ nonempty intersection.
  have h_open : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have h_ne : (Set.Ioo a b).Nonempty := Set.nonempty_Ioo.mpr hab
  obtain ⟨x, hx_cont, hx_in⟩ := h_dense.exists_mem_open h_open h_ne
  exact ⟨x, hx_in, hx_cont⟩

-- ============================================================================
-- §2.2.6: CDF tails — item (iv) on the discharge roadmap of
-- `bracketingGrid_exists`. Routed through Mathlib's `ProbabilityTheory.cdf`
-- to avoid duplicating the work of `tendsto_cdf_atBot`/`atTop`.
--
-- Ships the S9b OBSERVE (#18372) drop-in patch §3.2 verbatim. Builds the
-- bridge `trueCDF X μ = ProbabilityTheory.cdf (Measure.map (X 0) μ)` and
-- derives the two `Tendsto` results as one-line compositions.
-- ============================================================================

/-! ### CDF tails (S9 ACT, via Mathlib `ProbabilityTheory.cdf` bridge)

Item (iv) on the discharge roadmap of `bracketingGrid_exists`: the true CDF
tends to 0 at -∞ and 1 at +∞.

Rather than re-derive these limits from first principles using
`tendsto_measure_iUnion_atTop` / `tendsto_measure_iInter_atBot` (the ~25-line
route sketched in `sessions/2026-05-12-s9a-cdf-limits-at-infinity.md`),
this block uses Mathlib's `ProbabilityTheory.cdf : Measure ℝ →
StieltjesFunction ℝ` (in `Mathlib/Probability/CDF.lean`). That construction
already packages the limits as `ProbabilityTheory.tendsto_cdf_atBot` and
`ProbabilityTheory.tendsto_cdf_atTop`.

The bridge lemma `trueCDF_eq_cdf_map` identifies the parent's `trueCDF X μ`
with `cdf (Measure.map (X 0) μ)`. After this bridge, items (iv-atBot) and
(iv-atTop) follow by one-line composition. -/

/-- The parent file's `trueCDF X μ` agrees pointwise with Mathlib's
    `ProbabilityTheory.cdf` applied to the pushforward `Measure.map (X 0) μ`. -/
theorem trueCDF_eq_cdf_map [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) (x : ℝ) :
    trueCDF X μ x = ProbabilityTheory.cdf (Measure.map (X 0) μ) x := by
  haveI : IsProbabilityMeasure (Measure.map (X 0) μ) :=
    Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real]
  show (μ {ω | X 0 ω ≤ x}).toReal =
       ((Measure.map (X 0) μ) (Set.Iic x)).toReal
  rw [Measure.map_apply hX_meas measurableSet_Iic]
  rfl

/-- **Item (iv) — atBot direction.** The true CDF tends to 0 at -∞.
    One-line composition: identify `trueCDF X μ` with
    `cdf (Measure.map (X 0) μ)` via `trueCDF_eq_cdf_map`, then quote
    Mathlib's `ProbabilityTheory.tendsto_cdf_atBot`. -/
theorem trueCDF_atBot [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) :
    Filter.Tendsto (trueCDF X μ) Filter.atBot (nhds 0) := by
  haveI : IsProbabilityMeasure (Measure.map (X 0) μ) :=
    Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  have h_eq : trueCDF X μ = ProbabilityTheory.cdf (Measure.map (X 0) μ) := by
    funext x; exact trueCDF_eq_cdf_map hX_meas x
  rw [h_eq]
  exact ProbabilityTheory.tendsto_cdf_atBot _

/-- **Item (iv) — atTop direction.** The true CDF tends to 1 at +∞.
    Mirror of `trueCDF_atBot`, using `ProbabilityTheory.tendsto_cdf_atTop`. -/
theorem trueCDF_atTop [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) :
    Filter.Tendsto (trueCDF X μ) Filter.atTop (nhds 1) := by
  haveI : IsProbabilityMeasure (Measure.map (X 0) μ) :=
    Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  have h_eq : trueCDF X μ = ProbabilityTheory.cdf (Measure.map (X 0) μ) := by
    funext x; exact trueCDF_eq_cdf_map hX_meas x
  rw [h_eq]
  exact ProbabilityTheory.tendsto_cdf_atTop _

-- ============================================================================
-- §2.3: Simultaneous pointwise convergence at all grid points
-- ============================================================================

/-- **Provable** in this file. Given a finite (`Fin (k+2)`-indexed) sequence of
    threshold values `q`, the a.s. pointwise convergence
    `Fₙ(qⱼ, ω) → F(qⱼ)` from the parent's `empiricalCDF_pointwise_convergence`
    holds *simultaneously* at all `q j` on a single full-measure set.

    The proof commutes the universal `∀ j : Fin (k+2)` with the a.s. quantifier
    via `MeasureTheory.ae_all_iff` (countable conjunction of a.s. statements;
    `Fin (k+2)` is finite, hence countable). For each individual `j`, the parent
    file's `empiricalCDF_pointwise_convergence` (line 144) supplies the
    a.s. tendsto. -/
theorem bracketing_simultaneous_pointwise [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iid : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    {k : ℕ} (q : Fin (k + 2) → ℝ) :
    ∀ᵐ ω ∂μ, ∀ j : Fin (k + 2),
      Filter.Tendsto (fun n => empiricalCDF X n (q j) ω)
        Filter.atTop (nhds (trueCDF X μ (q j))) := by
  rw [ae_all_iff]
  intro j
  exact empiricalCDF_pointwise_convergence hX_meas hX_iid hX_ident (q j)

-- ============================================================================
-- §2.4: Uniform sup-bound from grid + simultaneous pointwise convergence
-- ============================================================================

/-! ### Helpers: trivial upper bounds on the empirical and true CDF

Both `empiricalCDF` and `trueCDF` take values in `[0, 1]`. The lower bounds
`empiricalCDF_nonneg`, `trueCDF_nonneg` are already in the parent file. The
upper bounds are routine but were not previously needed; the §2.4 uniform
bound uses them in the boundary (left tail / right tail) cases. -/

private lemma empiricalCDF_le_one (X : ℕ → Ω → ℝ) (n : ℕ) (x : ℝ) (ω : Ω) :
    empiricalCDF X n x ω ≤ 1 := by
  simp only [empiricalCDF]
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0; simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hsum_le : ∑ i ∈ Finset.range n,
        Set.indicator (Set.Iic x) (fun _ => (1 : ℝ)) (X i ω) ≤ (n : ℝ) := by
      calc ∑ i ∈ Finset.range n,
              Set.indicator (Set.Iic x) (fun _ => (1 : ℝ)) (X i ω)
          ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro i _
            simp only [Set.indicator]
            split_ifs <;> norm_num
        _ = (n : ℝ) := by simp
    have : (1 / (n : ℝ)) * ∑ i ∈ Finset.range n,
        Set.indicator (Set.Iic x) (fun _ => (1 : ℝ)) (X i ω) ≤ (1 / (n : ℝ)) * n := by
      apply mul_le_mul_of_nonneg_left hsum_le
      positivity
    calc (1 / (n : ℝ)) * ∑ i ∈ Finset.range n,
            Set.indicator (Set.Iic x) (fun _ => (1 : ℝ)) (X i ω)
        ≤ (1 / (n : ℝ)) * (n : ℝ) := this
      _ = 1 := by rw [one_div, inv_mul_cancel₀ hn'.ne']

private lemma trueCDF_le_one [IsProbabilityMeasure μ] (X : ℕ → Ω → ℝ) (x : ℝ) :
    trueCDF X μ x ≤ 1 := by
  simp only [trueCDF]
  have h : μ {ω | X 0 ω ≤ x} ≤ μ Set.univ := measure_mono (Set.subset_univ _)
  rw [measure_univ] at h
  have h1 : (μ {ω | X 0 ω ≤ x}).toReal ≤ (1 : ENNReal).toReal :=
    ENNReal.toReal_mono ENNReal.one_ne_top h
  simpa using h1

/-! ### Cell-finding helper: locate `x` in a grid

Given a strictly increasing grid `q : Fin (k+2) → ℝ`, any `x` with
`q 0 ≤ x < q (Fin.last (k+1))` lies in a unique grid cell `[q.castSucc, q.succ)`
indexed by some `j : Fin (k+1)`. This is the elementary trichotomy that the
§2.4 case split uses for the deterministic uniform bound. -/

private lemma find_cell {k : ℕ} (q : Fin (k + 2) → ℝ) (_hq : StrictMono q)
    {x : ℝ} (h0 : q 0 ≤ x) (hk : x < q (Fin.last (k + 1))) :
    ∃ j : Fin (k + 1), q j.castSucc ≤ x ∧ x < q j.succ := by
  classical
  let s : Finset (Fin (k + 2)) := Finset.univ.filter (fun j => q j ≤ x)
  have hne : s.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h0⟩⟩
  set jmax := s.max' hne with hjmax_def
  have hjmax_mem : jmax ∈ s := s.max'_mem hne
  have hjmax_le : q jmax ≤ x := (Finset.mem_filter.mp hjmax_mem).2
  have hjmax_ne_last : jmax ≠ Fin.last (k + 1) := by
    intro h
    rw [h] at hjmax_le
    linarith
  have hjmax_val_lt : jmax.val < k + 1 := by
    have h_le : jmax.val ≤ k + 1 := Nat.lt_succ_iff.mp jmax.isLt
    have h_ne : jmax.val ≠ k + 1 := fun heq => hjmax_ne_last (Fin.ext (by simp [heq]))
    omega
  refine ⟨⟨jmax.val, hjmax_val_lt⟩, ?_, ?_⟩
  · -- `castSucc` preserves the underlying value, so the cell's left endpoint
    -- is exactly `q jmax`, which is `≤ x` by maximality membership.
    have hcs : (⟨jmax.val, hjmax_val_lt⟩ : Fin (k + 1)).castSucc = jmax :=
      Fin.ext rfl
    rw [hcs]
    exact hjmax_le
  · -- The right endpoint `q jmax.succ` must exceed `x`, else `jmax.succ` would
    -- belong to `s`, contradicting the maximality of `jmax`.
    by_contra h
    push_neg at h
    have hsucc_in_s : (⟨jmax.val, hjmax_val_lt⟩ : Fin (k + 1)).succ ∈ s :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
    have h_le : (⟨jmax.val, hjmax_val_lt⟩ : Fin (k + 1)).succ ≤ jmax :=
      s.le_max' _ hsucc_in_s
    have h_succ_val : ((⟨jmax.val, hjmax_val_lt⟩ : Fin (k + 1)).succ).val
        = jmax.val + 1 := rfl
    have h_le_val : ((⟨jmax.val, hjmax_val_lt⟩ : Fin (k + 1)).succ).val ≤ jmax.val := h_le
    rw [h_succ_val] at h_le_val
    omega

/-! ### Per-`x` deterministic bound

The core deterministic inequality: for any `x : ℝ`, the pointwise error
`|Fₙ(x) − F(x)|` is bounded by the finite maximum of the grid-point errors
plus `2ε`. The three cases — left tail, right tail, and an interior cell —
follow the spec's §2.4 step-by-step reasoning verbatim. No probability or
limits are used; this is a clean monotone-interpolation argument relying on
the parent file's `empiricalCDF_mono` / `trueCDF_mono` and the boundary
inequalities `left_le` / `right_ge` from the `BracketingGrid` structure. -/

private lemma bracketing_pointwise_bound [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {ε : ℝ} (_hε : 0 < ε)
    (G : BracketingGrid (trueCDF X μ) ε)
    (n : ℕ) (ω : Ω) (x : ℝ) :
    |empiricalCDF X n x ω - trueCDF X μ x| ≤
      (Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (G.k + 2) => |empiricalCDF X n (G.q j) ω - trueCDF X μ (G.q j)|))
      + 2 * ε := by
  -- v4.26.0: `set F := trueCDF X μ` rebinds the parameter `G` from
  -- `BracketingGrid (trueCDF X μ) ε` to `BracketingGrid F ε`, leaving the
  -- original as `G✝`. The outer-goal Finset.sup' then mentions `G✝.q j`
  -- while inner hypotheses mention `G.q j`, and `linarith` cannot bridge
  -- the two. `let` (no goal substitution) avoids the rebinding; the body
  -- still reads in terms of `Fn`/`F` via let-zeta.
  let F : ℝ → ℝ := trueCDF X μ
  let Fn : ℝ → ℝ := fun y => empiricalCDF X n y ω
  set M : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun j : Fin (G.k + 2) => |empiricalCDF X n (G.q j) ω - trueCDF X μ (G.q j)|)
    with hM_def
  -- Bound at any specific grid point: `|Fn(q j) - F(q j)| ≤ M`.
  have hM_at : ∀ j : Fin (G.k + 2), |Fn (G.q j) - F (G.q j)| ≤ M := by
    intro j
    exact Finset.le_sup'
      (f := fun j : Fin (G.k + 2) =>
        |empiricalCDF X n (G.q j) ω - trueCDF X μ (G.q j)|)
      (Finset.mem_univ j)
  by_cases hA : x < G.q 0
  · -- Case A: x in the left tail
    have hFnx_nn : 0 ≤ Fn x := empiricalCDF_nonneg X n x ω
    have hFx_nn : 0 ≤ F x := trueCDF_nonneg X x
    have hFnx_le : Fn x ≤ Fn (G.q 0) := empiricalCDF_mono X n ω hA.le
    have hFx_le : F x ≤ F (G.q 0) := trueCDF_mono X hA.le
    have hF0_le_ε : F (G.q 0) ≤ ε := G.left_le
    have hM0 : |Fn (G.q 0) - F (G.q 0)| ≤ M := hM_at 0
    -- F(q 0) - Fn(q 0) ≤ |Fn(q 0) - F(q 0)| ≤ M (use abs_sub_comm-equivalent).
    have hFmnFn : F (G.q 0) - Fn (G.q 0) ≤ M := by
      have h1 : F (G.q 0) - Fn (G.q 0) = -(Fn (G.q 0) - F (G.q 0)) := by ring
      rw [h1]
      have := neg_abs_le (Fn (G.q 0) - F (G.q 0))
      linarith
    have hFnmF : Fn (G.q 0) - F (G.q 0) ≤ M := by
      have := le_abs_self (Fn (G.q 0) - F (G.q 0))
      linarith
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · -- -(M + 2ε) ≤ Fn x - F x
      have : F x - Fn x ≤ M + 2 * ε := by
        calc F x - Fn x ≤ F x := by linarith
          _ ≤ ε := by linarith
          _ ≤ M + 2 * ε := by
              have hM_nn : 0 ≤ M := by
                have := abs_nonneg (Fn (G.q 0) - F (G.q 0))
                linarith
              linarith
      linarith
    · -- Fn x - F x ≤ M + 2ε
      calc Fn x - F x ≤ Fn x := by linarith
        _ ≤ Fn (G.q 0) := hFnx_le
        _ = (Fn (G.q 0) - F (G.q 0)) + F (G.q 0) := by ring
        _ ≤ M + ε := by linarith
        _ ≤ M + 2 * ε := by linarith
  · push_neg at hA  -- hA : G.q 0 ≤ x
    by_cases hB : x < G.q (Fin.last (G.k + 1))
    · -- Case C: interior cell
      obtain ⟨j, hj_lower, hj_upper⟩ := find_cell G.q G.mono hA hB
      have hFnx_lower : Fn (G.q j.castSucc) ≤ Fn x := empiricalCDF_mono X n ω hj_lower
      have hFnx_upper : Fn x ≤ Fn (G.q j.succ) := empiricalCDF_mono X n ω hj_upper.le
      have hFx_lower : F (G.q j.castSucc) ≤ F x := trueCDF_mono X hj_lower
      have hFx_upper : F x ≤ F (G.q j.succ) := trueCDF_mono X hj_upper.le
      have hStep : F (G.q j.succ) - F (G.q j.castSucc) ≤ ε := G.step_le j
      have hM_succ : |Fn (G.q j.succ) - F (G.q j.succ)| ≤ M := hM_at j.succ
      have hM_cast : |Fn (G.q j.castSucc) - F (G.q j.castSucc)| ≤ M := hM_at j.castSucc
      have hFnmF_succ : Fn (G.q j.succ) - F (G.q j.succ) ≤ M :=
        le_trans (le_abs_self _) hM_succ
      have hFmnFn_cast : F (G.q j.castSucc) - Fn (G.q j.castSucc) ≤ M := by
        have h := neg_abs_le (Fn (G.q j.castSucc) - F (G.q j.castSucc))
        linarith
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · -- -(M + 2ε) ≤ Fn x - F x; equivalently, F x - Fn x ≤ M + 2ε.
        have : F x - Fn x ≤ M + 2 * ε := by
          calc F x - Fn x
              ≤ F (G.q j.succ) - Fn (G.q j.castSucc) := by linarith
            _ = (F (G.q j.castSucc) - Fn (G.q j.castSucc))
                  + (F (G.q j.succ) - F (G.q j.castSucc)) := by ring
            _ ≤ M + ε := by linarith
            _ ≤ M + 2 * ε := by linarith
        linarith
      · -- Fn x - F x ≤ M + 2ε
        calc Fn x - F x
            ≤ Fn (G.q j.succ) - F (G.q j.castSucc) := by linarith
          _ = (Fn (G.q j.succ) - F (G.q j.succ))
                + (F (G.q j.succ) - F (G.q j.castSucc)) := by ring
          _ ≤ M + ε := by linarith
          _ ≤ M + 2 * ε := by linarith
    · -- Case B: right tail, x ≥ G.q (Fin.last)
      push_neg at hB  -- hB : G.q (Fin.last (G.k + 1)) ≤ x
      have hFnx_lower : Fn (G.q (Fin.last (G.k + 1))) ≤ Fn x :=
        empiricalCDF_mono X n ω hB
      have hFx_lower : F (G.q (Fin.last (G.k + 1))) ≤ F x := trueCDF_mono X hB
      have hFnx_le_one : Fn x ≤ 1 := empiricalCDF_le_one X n x ω
      have hFx_le_one : F x ≤ 1 := trueCDF_le_one X x
      have hFlast_ge : F (G.q (Fin.last (G.k + 1))) ≥ 1 - ε := G.right_ge
      have hM_last : |Fn (G.q (Fin.last (G.k + 1))) - F (G.q (Fin.last (G.k + 1)))| ≤ M :=
        hM_at (Fin.last (G.k + 1))
      have hFmnFn_last : F (G.q (Fin.last (G.k + 1))) - Fn (G.q (Fin.last (G.k + 1))) ≤ M := by
        have h := neg_abs_le
          (Fn (G.q (Fin.last (G.k + 1))) - F (G.q (Fin.last (G.k + 1))))
        linarith
      have hFnmF_last : Fn (G.q (Fin.last (G.k + 1))) - F (G.q (Fin.last (G.k + 1))) ≤ M :=
        le_trans (le_abs_self _) hM_last
      have hM_nn : 0 ≤ M := by
        have := abs_nonneg
          (Fn (G.q (Fin.last (G.k + 1))) - F (G.q (Fin.last (G.k + 1))))
        linarith
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · -- -(M + 2ε) ≤ Fn x - F x; equivalently, F x - Fn x ≤ M + 2ε.
        have : F x - Fn x ≤ M + 2 * ε := by
          calc F x - Fn x
              ≤ 1 - Fn x := by linarith
            _ ≤ 1 - Fn (G.q (Fin.last (G.k + 1))) := by linarith
            _ = (1 - F (G.q (Fin.last (G.k + 1))))
                  + (F (G.q (Fin.last (G.k + 1))) - Fn (G.q (Fin.last (G.k + 1)))) := by ring
            _ ≤ ε + M := by linarith
            _ ≤ M + 2 * ε := by linarith
        linarith
      · -- Fn x - F x ≤ M + 2ε
        calc Fn x - F x
            ≤ 1 - F x := by linarith
          _ ≤ 1 - F (G.q (Fin.last (G.k + 1))) := by linarith
          _ ≤ ε := by linarith
          _ ≤ M + 2 * ε := by linarith

/-! ### Deterministic uniform sup-bound

`bracketing_uniform_sup_bound`: a probability-free, limit-free statement.
For any sample `ω` and any `n`, the `⨆` over `x : ℝ` of `|Fₙ(x, ω) - F(x)|` is
bounded by the finite maximum of grid-point errors plus `2ε`. This is the
clean target of §2.4 in the bracketing spec; pairing it with the limit
hypothesis on grid-point convergence (next theorem) yields the
`asymptotic 2ε` statement informally written in
`bracketing-decomposition-draft.md` §2.4. -/

theorem bracketing_uniform_sup_bound [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (G : BracketingGrid (trueCDF X μ) ε)
    (n : ℕ) (ω : Ω) :
    (⨆ x : ℝ, |empiricalCDF X n x ω - trueCDF X μ x|) ≤
      (Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (G.k + 2) => |empiricalCDF X n (G.q j) ω - trueCDF X μ (G.q j)|))
      + 2 * ε := by
  apply ciSup_le
  intro x
  exact bracketing_pointwise_bound hε G n ω x

/-! ### §2.4 limit form: eventually `≤ 2ε + η`

Combined statement matching `bracketing-decomposition-draft.md` §2.4. Given
the simultaneous pointwise convergence hypothesis `hpw`, for every slack
`η > 0`, eventually the sup-error of `Fₙ(·, ω)` against `F` is at most
`2ε + η`. This is the precise (well-typed) Lean form of the spec's informal
`Tendsto … (nhds_le_of (· ≤ 2 * ε))` notation: each `|Fₙ(qⱼ) − F(qⱼ)|` is
eventually `< η`, so their finite maximum is eventually `≤ η`, and the
deterministic bound `bracketing_uniform_sup_bound` lifts this to the `iSup`. -/

theorem bracketing_uniform_from_grid [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} {ε : ℝ} (hε : 0 < ε)
    (G : BracketingGrid (trueCDF X μ) ε)
    {ω : Ω}
    (hpw : ∀ j : Fin (G.k + 2),
        Filter.Tendsto (fun n => empiricalCDF X n (G.q j) ω)
          Filter.atTop (nhds (trueCDF X μ (G.q j)))) :
    ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop,
      (⨆ x : ℝ, |empiricalCDF X n x ω - trueCDF X μ x|) ≤ 2 * ε + η := by
  intro η hη
  -- For each grid index `j`, eventually `|Fₙ(qⱼ) − F(qⱼ)| ≤ η`.
  have h_each : ∀ j : Fin (G.k + 2), ∀ᶠ n in Filter.atTop,
      |empiricalCDF X n (G.q j) ω - trueCDF X μ (G.q j)| ≤ η := by
    intro j
    have h_dist : ∀ᶠ n in Filter.atTop,
        dist (empiricalCDF X n (G.q j) ω) (trueCDF X μ (G.q j)) < η :=
      (Metric.tendsto_nhds.mp (hpw j)) η hη
    filter_upwards [h_dist] with n hn
    have := hn
    rw [Real.dist_eq] at this
    linarith [this]
  -- Combine over the finite index set `Fin (G.k + 2)` via `Filter.eventually_all`.
  have h_combined : ∀ᶠ n in Filter.atTop, ∀ j : Fin (G.k + 2),
      |empiricalCDF X n (G.q j) ω - trueCDF X μ (G.q j)| ≤ η := by
    rw [Filter.eventually_all]
    exact h_each
  filter_upwards [h_combined] with n hn
  -- Bound the finite sup' by `η`.
  have hM_le : (Finset.univ.sup' Finset.univ_nonempty
        (fun j : Fin (G.k + 2) => |empiricalCDF X n (G.q j) ω - trueCDF X μ (G.q j)|))
      ≤ η := by
    apply Finset.sup'_le
    intro j _
    exact hn j
  -- Chain with the deterministic bound.
  calc (⨆ x : ℝ, |empiricalCDF X n x ω - trueCDF X μ x|)
      ≤ (Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin (G.k + 2) => |empiricalCDF X n (G.q j) ω - trueCDF X μ (G.q j)|))
        + 2 * ε := bracketing_uniform_sup_bound hε G n ω
    _ ≤ η + 2 * ε := by linarith
    _ = 2 * ε + η := by ring

-- ============================================================================
-- §2.5: Uniform convergence (proved modulo `bracketingGrid_exists`)
-- ============================================================================

/-! ### §2.5 Glivenko–Cantelli uniform convergence

Composes §2.2 (`bracketingGrid_exists`), §2.3 (`bracketing_simultaneous_pointwise`)
and §2.4 (`bracketing_uniform_from_grid`) along the diagonal `ε := 1 / (m+1)`,
`m : ℕ`. The countably many simultaneous-pointwise full-measure sets are
combined via `MeasureTheory.ae_all_iff` into a single full-measure set on
which, for every accuracy `δ > 0`, picking `m` with `1/(m+1) < δ/3` and
applying §2.4 with `η := 1/(m+1)` gives `⨆x |Fₙ − F| ≤ 3/(m+1) < δ` eventually.

This is the canonical statement of uniform Glivenko-Cantelli. It replaces
the parent's `glivenko_cantelli_uniform` axiom (retired in S7), leaving
`bracketingGrid_exists` as the sole remaining axiom in the chain. -/
theorem glivenko_cantelli_uniform [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ}
    (hX_meas : ∀ i, Measurable (X i))
    (hX_iid : iIndepFun X μ)
    (hX_ident : ∀ i, IdentDistrib (X i) (X 0) μ μ) :
    ∀ᵐ ω ∂μ,
      Filter.Tendsto
        (fun n => ⨆ x : ℝ, |empiricalCDF X n x ω - trueCDF X μ x|)
        Filter.atTop (nhds 0) := by
  -- Diagonal accuracy schedule: ε m := 1 / (m + 1)
  let ε : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 1)
  have hε_pos : ∀ m : ℕ, 0 < ε m := fun m => by
    show (0 : ℝ) < 1 / ((m : ℝ) + 1)
    positivity
  -- Pick a bracketing grid for each accuracy ε m
  let G : (m : ℕ) → BracketingGrid (trueCDF X μ) (ε m) := fun m =>
    (bracketingGrid_exists hX_meas (hε_pos m)).some
  -- Per-m simultaneous pointwise convergence at grid points
  have h_per_m : ∀ m : ℕ, ∀ᵐ ω ∂μ, ∀ j : Fin ((G m).k + 2),
      Filter.Tendsto (fun n => empiricalCDF X n ((G m).q j) ω)
        Filter.atTop (nhds (trueCDF X μ ((G m).q j))) := by
    intro m
    exact bracketing_simultaneous_pointwise hX_meas hX_iid hX_ident (G m).q
  -- Combine the countably many full-measure sets via `ae_all_iff`
  have h_all : ∀ᵐ ω ∂μ, ∀ m : ℕ, ∀ j : Fin ((G m).k + 2),
      Filter.Tendsto (fun n => empiricalCDF X n ((G m).q j) ω)
        Filter.atTop (nhds (trueCDF X μ ((G m).q j))) := by
    rw [ae_all_iff]
    exact h_per_m
  filter_upwards [h_all] with ω h_pw_all
  -- Show `Tendsto (⨆x ...) atTop (nhds 0)` via the metric characterisation
  rw [Metric.tendsto_atTop]
  intro δ hδ
  -- Choose `m : ℕ` with `1 / (m + 1) < δ / 3` (so `3 · ε m < δ`)
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt
    (div_pos hδ (by norm_num : (0 : ℝ) < 3))
  -- Apply §2.4 with this `m` and slack `η := ε m`
  have h_event :=
    bracketing_uniform_from_grid (hε_pos m) (G m) (h_pw_all m) (ε m) (hε_pos m)
  -- Extract the eventual index from `∀ᶠ n, ...`
  rw [Filter.eventually_atTop] at h_event
  obtain ⟨N, hN⟩ := h_event
  refine ⟨N, fun n hn => ?_⟩
  -- Bound the sup-error: ⨆ ≤ 2 ε m + ε m = 3 ε m
  have hUle :
      (⨆ x : ℝ, |empiricalCDF X n x ω - trueCDF X μ x|) ≤ 2 * ε m + ε m :=
    hN n hn
  -- ⨆ ≥ 0 since the integrand is a pointwise absolute value
  have hUnn : 0 ≤ ⨆ x : ℝ, |empiricalCDF X n x ω - trueCDF X μ x| :=
    Real.iSup_nonneg (fun _ => abs_nonneg _)
  -- 3 · ε m < δ
  have h3εm : 3 * ε m < δ := by
    have hεlt : ε m < δ / 3 := hm
    linarith
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hUnn]
  linarith

end GlivenkoCantelli
