import Mathlib

/-
# Heine–Cantor via the Lebesgue Number of the Preimage Cover

## What This Proves

**Heine–Cantor.** A continuous map `f : X → Y` from a compact metric space to a
metric space is *uniformly* continuous: one radius `δ > 0` works simultaneously
at every point.

The proof follows the route singled out by the parent entry
(`compactness-finite-subcover-oq-02`): rather than invoking Mathlib's packaged
`CompactSpace.uniformContinuous_of_continuous`, we *reprove* uniform continuity
directly from the **Lebesgue number lemma**, exactly as the parent's subordinate
ε-net machinery anticipates.  Fix `ε > 0` and cover `X` by the open sets
`U z = f⁻¹(ball (f z) (ε/2))` (one per point `z`, open because `f` is continuous;
covering because `z ∈ U z`).  The Lebesgue number lemma hands back a single
`δ > 0` such that **every** `δ`-ball lies inside some `U z`.  If
`dist x y < δ` then both `x` and `y` lie in one common `ball x δ ⊆ U z`, so
`f x` and `f y` are each within `ε/2` of `f z`; the triangle inequality closes
`dist (f x) (f y) < ε`.

This is the concrete payoff promised by the parent: the Lebesgue radius read off
the preimage cover *is* a global modulus of continuity.

## Results

* `heine_cantor_dist` — the explicit ε–δ engine: for every `ε > 0` there is a
  single `δ > 0` that controls `dist (f x) (f y)` at every pair of points.
* `heine_cantor` — the headline, packaged as `UniformContinuous f`.
* `continuous_iff_uniformContinuous` — on a compact metric domain the two
  notions of continuity coincide (the reverse is the general
  `UniformContinuous.continuous`).
* `cauchySeq_comp_of_continuous` — a downstream corollary: a continuous map on a
  compact metric space preserves Cauchy sequences, since it is uniformly
  continuous.

## Provenance

The single non-trivial ingredient, `lebesgue_number_lemma_of_metric`, is
Mathlib's, and Mathlib also packages Heine–Cantor directly
(`CompactSpace.uniformContinuous_of_continuous`); the formalized content here is
the *self-contained derivation along the Lebesgue-number route*, turning the
parent's subordinate-net philosophy into the uniform modulus, plus the
equivalence and Cauchy-preservation corollaries read off it.  Hence the
`mathlib` badge.
-/

open Set Metric

namespace CompactnessFiniteSubcoverOq02Oq01

variable {X : Type*} [MetricSpace X] [CompactSpace X]
variable {Y : Type*} [MetricSpace Y]

/-- **Heine–Cantor, ε–δ form.** For a continuous `f` on a compact metric space and
any `ε > 0`, there is a single `δ > 0` such that `dist x y < δ` forces
`dist (f x) (f y) < ε` at every pair of points.  The `δ` is the Lebesgue number
of the cover of `X` by the `f`-preimages of the `ε/2`-balls. -/
theorem heine_cantor_dist {f : X → Y} (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x y, dist x y < δ → dist (f x) (f y) < ε := by
  -- Open cover of `X` by preimages of `ε/2`-balls, one centered at each `f z`.
  set U : X → Set X := fun z => f ⁻¹' ball (f z) (ε / 2) with hUdef
  have hU : ∀ z, IsOpen (U z) := fun z => isOpen_ball.preimage hf
  have hsub : (univ : Set X) ⊆ ⋃ z, U z := fun x _ =>
    mem_iUnion.mpr ⟨x, mem_preimage.mpr (mem_ball_self (by positivity))⟩
  -- A Lebesgue number: every `δ`-ball is subordinate to some cover member.
  obtain ⟨δ, hδ, hlb⟩ := lebesgue_number_lemma_of_metric isCompact_univ hU hsub
  refine ⟨δ, hδ, fun x y hxy => ?_⟩
  obtain ⟨z, hz⟩ := hlb x (mem_univ x)
  -- Both `x` and `y` lie in `ball x δ`, hence in `U z = f⁻¹(ball (f z) (ε/2))`.
  have hfx : dist (f x) (f z) < ε / 2 := by
    have := hz (mem_ball_self hδ); rwa [hUdef, mem_preimage, mem_ball] at this
  have hfy : dist (f y) (f z) < ε / 2 := by
    have hyb : y ∈ ball x δ := by rw [mem_ball, dist_comm]; exact hxy
    have := hz hyb; rwa [hUdef, mem_preimage, mem_ball] at this
  calc
    dist (f x) (f y) ≤ dist (f x) (f z) + dist (f z) (f y) := dist_triangle _ _ _
    _ = dist (f x) (f z) + dist (f y) (f z) := by rw [dist_comm (f z) (f y)]
    _ < ε / 2 + ε / 2 := by linarith
    _ = ε := by ring

/-- **Heine–Cantor.** A continuous map from a compact metric space to a metric
space is uniformly continuous. -/
theorem heine_cantor {f : X → Y} (hf : Continuous f) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := heine_cantor_dist hf hε
  exact ⟨δ, hδ, h⟩

/-- **Continuity ⇔ uniform continuity on a compact metric domain.** The forward
direction is Heine–Cantor; the reverse holds for any uniformly continuous map. -/
theorem continuous_iff_uniformContinuous {f : X → Y} :
    Continuous f ↔ UniformContinuous f :=
  ⟨heine_cantor, UniformContinuous.continuous⟩

/-- **Cauchy preservation.** A continuous map on a compact metric space sends
Cauchy sequences to Cauchy sequences — an immediate consequence of Heine–Cantor,
since uniformly continuous maps preserve the Cauchy property. -/
theorem cauchySeq_comp_of_continuous {f : X → Y} (hf : Continuous f)
    {u : ℕ → X} (hu : CauchySeq u) : CauchySeq (f ∘ u) :=
  (heine_cantor hf).comp_cauchySeq hu

end CompactnessFiniteSubcoverOq02Oq01
