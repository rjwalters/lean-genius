/-
  DRAFT SCAFFOLD — Shapley–Folkman–Starr quantitative metric bound (OQ-02)

  STATUS: UNVERIFIED DRAFT. This file lives under `research/` (NOT `proofs/Proofs/`)
  on purpose — it is NOT part of the gallery build and must NOT be added to
  `proofs/Proofs.lean` until it compiles. The verification backends were both down
  when this was written (Docker daemon flapping + containerd "unexpected EOF" crash;
  Aristotle MCP returning 404). Every `sorry` below is an ACT target to discharge
  (manually or via Aristotle) the moment a backend returns. The statements are
  name-checked against the parent file and Mathlib v4.26.0 source; the proofs are NOT.

  GOAL (Starr 1969 / Cassels 1975):
    d_H( Σ_{i∈t} S_i , conv Σ_{i∈t} S_i )  ≤  √(min |t| n) · maxᵢ rad(S_i),   n = finrank ℝ E.
  The headline feature is that the bound is INDEPENDENT of the number of summands |t|
  (it saturates at √n). Numerically de-risked in `verify_starr_bound.py` (0 violations,
  m-independence confirmed sharp; see knowledge.md).

  WHAT THE PARENT ALREADY GIVES (proofs/Proofs/ShapleyFolkman.lean, in `main`):
    theorem sum_close_to_convexHull [FiniteDimensional ℝ E]
        {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
        (hne : ∀ i ∈ t, (S i).Nonempty)
        {x : E} (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
        ∃ (f : ι → E),
          (∀ i ∈ t, f i ∈ convexHull ℝ (S i)) ∧
          ∑ i ∈ t, f i = x ∧
          (t.filter (fun i => f i ∉ S i)).card ≤ Module.finrank ℝ E
  i.e. the COMBINATORIAL content: x = Σ fᵢ with each fᵢ ∈ conv(Sᵢ) and at most
  n = finrank summands convexified. The METRIC upgrade below is the new work.

  KEY API CORRECTION (this session, vs prior ORIENT notes):
   * The parent file's ambient context is `variable {E : Type*} [AddCommGroup E] [Module ℝ E]`
     — module-only, NO norm. The metric bound MUST add `[NormedAddCommGroup E]
     [InnerProductSpace ℝ E]`. So OQ-02 cannot live in the parent's namespace context
     unchanged; it re-states `sum_close_to_convexHull`'s conclusion under the richer
     structure (the parent theorem still applies, since a normed ℝ-space is an ℝ-module).
   * Mathlib v4.26.0 has NO general circumradius / minimal-enclosing-ball API for
     arbitrary bounded sets (only `Affine.Simplex.circumradius` for simplices). So `rad`
     must be defined here. The diam-based surrogate `‖f − s‖ ≤ Metric.diam (S i)` gives a
     correct but non-sharp first pass; the sharp constant needs the min-enclosing-ball
     radius `rad`.
-/

import Mathlib

open Set Finset Pointwise Metric Real

namespace ShapleyFolkmanOQ02

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### 1. A radius for an arbitrary set

`rad S` = the infimum over centers `c` of the smallest radius enclosing `S`
(the Chebyshev / minimal-enclosing-ball radius). For the *bound* it is enough to
have, for the nearest point, `‖f − s‖ ≤ rad (S i)` whenever `f ∈ conv (S i)`.
A correct-but-loose first pass replaces `rad` by `Metric.diam`. -/

/-- Minimal enclosing-ball radius of a set: `sInf` over centers `c` of `sSup_{x∈S} ‖x−c‖`.
    (DRAFT: the exact `iInf/iSup` packaging and junk-value handling for unbounded `S`
    need to be pinned down against `Metric` API; `Metric.diam` is the available fallback.) -/
noncomputable def rad (S : Set E) : ℝ :=
  ⨅ c : E, ⨆ x : S, ‖(x : E) - c‖
  -- TODO(ACT): confirm `⨆ x : S, _` typechecks (bddAbove for bounded S); else use
  -- `sInf {r | ∃ c, ∀ x ∈ S, ‖x - c‖ ≤ r}`. Prove `rad_le_diam : rad S ≤ Metric.diam S`
  -- and `rad_nonneg`.

theorem rad_nonneg (S : Set E) : 0 ≤ rad S := by sorry

/-- The min-enclosing-ball radius is bounded by the diameter (so the diam-based first
    pass is a relaxation of the sharp `rad` bound). -/
theorem rad_le_diam (S : Set E) (hb : IsBounded S) : rad S ≤ Metric.diam S := by sorry

/-! ### 2. Per-summand displacement

For a hull point `f ∈ conv (S i)` there is an actual point `s ∈ S i` within `rad (S i)`.
Via Carathéodory (`eq_pos_convex_span_of_mem_convexHull`) `f` is a convex combination of
points of `S i`; the nearest such point is within the enclosing radius. -/
theorem exists_nearby_point {S : Set E} (hne : S.Nonempty) (hb : IsBounded S)
    {f : E} (hf : f ∈ convexHull ℝ S) :
    ∃ s ∈ S, ‖f - s‖ ≤ rad S := by
  -- ACT sketch: `eq_pos_convex_span_of_mem_convexHull hf` gives f = Σ wⱼ • zⱼ, zⱼ ∈ S,
  -- wⱼ > 0, Σwⱼ = 1. With c the enclosing center, ‖f − c‖ = ‖Σ wⱼ(zⱼ−c)‖ ≤ Σ wⱼ‖zⱼ−c‖ ≤ rad.
  -- Then the nearest zⱼ to f satisfies ‖f − zⱼ‖ ≤ ‖f − c‖ + ‖c − zⱼ‖ ... refine to ≤ rad.
  sorry

/-! ### 3. THE CRUX — ℓ² aggregation (source of the √n, NOT triangle/CS-on-norms)

This is the one genuinely non-routine lemma and the open core of OQ-02. Over the
`≤ n` convexified ("excess") indices, the deviation vectors `vᵢ = fᵢ − sᵢ` satisfy
the Cassels–Starr estimate

    ‖∑_{i ∈ excess} vᵢ‖  ≤  √(excess.card) · maxᵢ ‖vᵢ‖.

NOTE (honest): this does NOT follow from the triangle inequality (`norm_sum_le`,
which only gives `excess.card · max`), NOR from Cauchy–Schwarz applied to `∑‖vᵢ‖`
(that also only reaches `excess.card · max`). The √-improvement is Cassels' lemma:
it uses that each `vᵢ` is a deviation of a point of `conv Sᵢ` from a point of `Sᵢ`,
i.e. a genuine convex-geometry fact, NOT a generic inner-product identity. Porting
Cassels' argument (or an equivalent) is the substantial remaining work. -/
theorem cassels_starr_aggregation {ι : Type*} (excess : Finset ι) (v : ι → E) (L : ℝ)
    (hL : ∀ i ∈ excess, ‖v i‖ ≤ L) (hL0 : 0 ≤ L)
    -- Cassels' structural hypothesis: each vᵢ = fᵢ − sᵢ with fᵢ ∈ conv(Sᵢ), sᵢ ∈ Sᵢ a
    -- nearest point; encode precisely during ACT. WITHOUT such a hypothesis the bound is
    -- FALSE (aligned vectors give excess.card · L), so this signature is a PLACEHOLDER.
    :
    ‖∑ i ∈ excess, v i‖ ≤ Real.sqrt (excess.card) * L := by
  sorry

/-! ### 4. One-sided Hausdorff bound — TRIANGLE version (routine, correct, non-sharp)

The honestly-provable fallback that does NOT need Cassels: replace each convexified
`fᵢ` by a nearby `sᵢ ∈ Sᵢ` and bound by the triangle inequality. Constant is `n` (or
`|t|`), not `√n`. This is a complete correct theorem and a good first ACT target. -/
theorem hausdorff_bound_linear {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty) (hb : ∀ i ∈ t, IsBounded (S i))
    {x : E} (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
    ∃ y ∈ (∑ i ∈ t, S i), ‖x - y‖ ≤ (Module.finrank ℝ E) * (⨆ i : t, rad (S i)) := by
  -- ACT sketch: apply `sum_close_to_convexHull hne hx` → f with excess.card ≤ finrank.
  -- On non-excess i, fᵢ ∈ Sᵢ already; on excess i, `exists_nearby_point` gives sᵢ ∈ Sᵢ
  -- with ‖fᵢ − sᵢ‖ ≤ rad(Sᵢ). Set y = Σ sᵢ ∈ Σ Sᵢ. Then
  -- ‖x − y‖ = ‖Σ_{excess}(fᵢ − sᵢ)‖ ≤ Σ_{excess} rad ≤ excess.card · max rad ≤ finrank · max rad.
  sorry

/-! ### 5. One-sided Hausdorff bound — STARR version (the headline target)

Same construction, but bound the excess deviation sum via `cassels_starr_aggregation`,
yielding the sharp `√(min |t| finrank)` constant — independent of |t|. -/
theorem hausdorff_bound_starr {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty) (hb : ∀ i ∈ t, IsBounded (S i))
    {x : E} (hx : x ∈ convexHull ℝ (∑ i ∈ t, S i)) :
    ∃ y ∈ (∑ i ∈ t, S i),
      ‖x - y‖ ≤ Real.sqrt (min t.card (Module.finrank ℝ E)) * (⨆ i : t, rad (S i)) := by
  -- ACT sketch: as in `hausdorff_bound_linear`, but apply `cassels_starr_aggregation`
  -- to the excess deviations (card ≤ finrank, and ≤ t.card), giving the √ factor.
  sorry

/-! ### 6. Full two-sided Hausdorff-distance corollary

`Σ Sᵢ ⊆ conv Σ Sᵢ` makes the reverse direction trivial (dist 0), so the one-sided
bound upgrades to `Metric.hausdorffDist` via `hausdorffDist_le_of_mem_dist`. -/
theorem shapley_folkman_starr {ι : Type*} [DecidableEq ι] {S : ι → Set E} {t : Finset ι}
    (hne : ∀ i ∈ t, (S i).Nonempty) (hb : ∀ i ∈ t, IsBounded (S i)) :
    Metric.hausdorffDist (∑ i ∈ t, S i) (convexHull ℝ (∑ i ∈ t, S i))
      ≤ Real.sqrt (min t.card (Module.finrank ℝ E)) * (⨆ i : t, rad (S i)) := by
  -- ACT sketch: `hausdorffDist_le_of_mem_dist` with r = √(min ..)·max rad ≥ 0.
  -- Forward (x ∈ conv): `hausdorff_bound_starr`. Reverse (x ∈ Σ Sᵢ ⊆ conv): dist 0
  -- via `subset_convexHull` and `self_mem` ⇒ choose y = x.
  sorry

end ShapleyFolkmanOQ02
