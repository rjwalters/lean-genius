/-
# The Banach–Steinhaus Theorem (Uniform Boundedness Principle)

Mathlib proves the Banach–Steinhaus theorem (`banach_steinhaus`) and its
supremum-of-norms reformulation (`banach_steinhaus_iSup_nnnorm`), and constructs the
pointwise limit of a convergent family of continuous linear maps
(`continuousLinearMapOfTendsto`). The proof gallery, however, has no dedicated entry
for the uniform boundedness principle — one of the three pillars of linear functional
analysis (alongside the open mapping and Hahn–Banach theorems), all flowing from the
Baire category theorem.

This entry packages the theorem with its two characteristic consequences, which
Mathlib does not state in this form:

* `uniform_boundedness` — the main theorem: a pointwise-bounded family of continuous
  linear maps out of a complete (Banach) space is uniformly bounded in operator norm;
* `uniform_boundedness_iSup` — the supremum-of-norms form;
* `resonance` — the **condensation of singularities** consequence (the contrapositive):
  if the operator norms are unbounded, then there is a *single* point `x` at which the
  values `‖g i x‖` are unbounded — one resonance point witnesses the failure;
* `pointwise_limit_isClm` — the **closure-under-pointwise-limits** corollary: a
  pointwise limit of continuous linear maps is itself a continuous linear map;
* `pointwise_limit_map_add` — a concrete consequence of the previous: the limit map
  is additive.

All results are verified with no axioms and no `sorry`.
-/
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Tactic

open Filter Topology
open scoped ENNReal NNReal

namespace BanachSteinhausTheorem

variable {𝕜 𝕜₂ : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  {ι : Type*}

/-- **Banach–Steinhaus theorem (Uniform Boundedness Principle).**
A family `g : ι → E →SL[σ₁₂] F` of continuous linear maps out of a complete (Banach)
space `E` that is *pointwise bounded* (for every `x` the norms `‖g i x‖` are bounded by
some constant depending only on `x`) is *uniformly bounded*: a single constant bounds
all of the operator norms `‖g i‖`. -/
theorem uniform_boundedness [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) : ∃ C', ∀ i, ‖g i‖ ≤ C' :=
  banach_steinhaus h

/-- The supremum form of the uniform boundedness principle, phrased with `ℝ≥0∞`:
if the pointwise suprema `⨆ i, ‖g i x‖₊` are all finite, then so is the supremum of the
operator norms `⨆ i, ‖g i‖₊`. -/
theorem uniform_boundedness_iSup [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ x, (⨆ i, (‖g i x‖₊ : ENNReal)) < ∞) : (⨆ i, (‖g i‖₊ : ENNReal)) < ∞ :=
  banach_steinhaus_iSup_nnnorm h

/-- **Condensation of singularities / resonance.**
The contrapositive of the uniform boundedness principle: if the operator norms of a
family of continuous linear maps out of a Banach space are *unbounded* (for every `C`
some `g i` has norm exceeding `C`), then there is a *single* point `x` — a resonance
point — at which the values `‖g i x‖` are unbounded. Failure of uniform boundedness is
always witnessed at one point. -/
theorem resonance [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ C : ℝ, ∃ i, C < ‖g i‖) : ∃ x : E, ∀ C : ℝ, ∃ i, C < ‖g i x‖ := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨C', hC'⟩ := uniform_boundedness hcon
  obtain ⟨i, hi⟩ := h C'
  exact absurd (hC' i) (not_le.mpr hi)

/-- **Pointwise limits of continuous linear maps are continuous linear maps.**
If a family `g : α → E →SL[σ₁₂] F` (indexed by any countably generated, nontrivial
filter `l` — in particular a sequence with `l = atTop`) out of a Banach space `E`
converges *pointwise* to a function `f`, then `f` is itself (the coercion of) a
continuous linear map. This is the standard corollary of Banach–Steinhaus: pointwise
boundedness of the convergent family gives equicontinuity, which makes the limit
continuous. -/
theorem pointwise_limit_isClm [CompleteSpace E] [T2Space F] {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] [l.NeBot] (g : α → E →SL[σ₁₂] F) {f : E → F}
    (h : Tendsto (fun n x ↦ g n x) l (𝓝 f)) :
    ∃ F' : E →SL[σ₁₂] F, ∀ x, F' x = f x :=
  ⟨continuousLinearMapOfTendsto g h, fun _ ↦ rfl⟩

/-- A concrete consequence of `pointwise_limit_isClm`: the pointwise limit of a
convergent family of continuous linear maps is additive. -/
theorem pointwise_limit_map_add [CompleteSpace E] [T2Space F] {α : Type*} {l : Filter α}
    [l.IsCountablyGenerated] [l.NeBot] (g : α → E →SL[σ₁₂] F) {f : E → F}
    (h : Tendsto (fun n x ↦ g n x) l (𝓝 f)) (x y : E) :
    f (x + y) = f x + f y := by
  obtain ⟨F', hF'⟩ := pointwise_limit_isClm g h
  rw [← hF', ← hF', ← hF', map_add]

end BanachSteinhausTheorem
