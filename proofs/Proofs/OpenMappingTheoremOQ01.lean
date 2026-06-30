import Mathlib

/-
# The Open Mapping Theorem and its Banach-space Consequences

The Banach open mapping theorem is one of the three cornerstones of linear
functional analysis (alongside Hahn–Banach and Banach–Steinhaus). It says that a
*surjective* bounded linear map between Banach spaces is an open map. From this one
single fact — itself a consequence of the Baire category theorem — flow several of
the most-used structural results of the subject:

* the surjection is automatically a **quotient map**;
* a continuous linear **bijection** has a continuous (bounded) inverse — the
  *bounded inverse theorem*;
* consequently the two norms `‖x‖` and `‖f x‖` on the domain are **equivalent**;
* a linear map between Banach spaces whose **graph is closed** is automatically
  continuous — the *closed graph theorem*.

Mathlib proves all of these (in `Mathlib/Analysis/Normed/Operator/Banach.lean`).
This entry packages the family of consequences under uniform, textbook-faithful
names, derives the norm-equivalence corollary explicitly (a form not stated as a
single named lemma in Mathlib), and records concrete instances confirming the
hypotheses are not vacuous.

All results are over a pair of Banach spaces `E`, `F` over a nontrivially normed
field `𝕜`.  No axioms, no sorries.
-/

namespace OpenMappingTheoremOQ01

open Function Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-! ## The open mapping theorem -/

/-- **Banach open mapping theorem.** A surjective bounded linear map between Banach
spaces is an open map: it sends open sets to open sets. -/
theorem open_mapping (f : E →L[𝕜] F) (hf : Surjective f) : IsOpenMap f :=
  f.isOpenMap hf

/-- The image of an open set under a surjective bounded linear map is open — the
pointwise form of `open_mapping`, the version one actually applies in practice. -/
theorem isOpen_image_of_surjective (f : E →L[𝕜] F) (hf : Surjective f)
    {s : Set E} (hs : IsOpen s) : IsOpen (f '' s) :=
  f.isOpenMap hf s hs

/-- A surjective bounded linear map between Banach spaces is a **quotient map**: the
topology on the target is exactly the quotient topology induced by `f`. -/
theorem quotient_map (f : E →L[𝕜] F) (hf : Surjective f) : IsQuotientMap f :=
  f.isQuotientMap hf

/-! ## The bounded inverse theorem -/

/-- **Bounded inverse theorem**, packaged as a continuous linear equivalence: a
continuous linear bijection between Banach spaces *is* a linear homeomorphism. This
is the statement that distinguishes Banach spaces — a continuous linear bijection
need *not* have continuous inverse without completeness. -/
noncomputable def equivOfBijective (f : E →L[𝕜] F) (hf : Bijective f) : E ≃L[𝕜] F :=
  (LinearEquiv.ofBijective (f : E →ₗ[𝕜] F) hf).toContinuousLinearEquivOfContinuous f.continuous

@[simp]
theorem equivOfBijective_apply (f : E →L[𝕜] F) (hf : Bijective f) (x : E) :
    equivOfBijective f hf x = f x := rfl

/-- **Bounded inverse theorem.** A continuous linear bijection between Banach spaces
has a continuous (bounded) linear two-sided inverse `g : F →L[𝕜] E`. -/
theorem exists_bounded_inverse (f : E →L[𝕜] F) (hf : Bijective f) :
    ∃ g : F →L[𝕜] E, (∀ x, g (f x) = x) ∧ (∀ y, f (g y) = y) := by
  refine ⟨((equivOfBijective f hf).symm : F →L[𝕜] E), fun x => ?_, fun y => ?_⟩
  · simp only [ContinuousLinearEquiv.coe_coe]
    rw [← equivOfBijective_apply f hf x, ContinuousLinearEquiv.symm_apply_apply]
  · simp only [ContinuousLinearEquiv.coe_coe]
    rw [← equivOfBijective_apply f hf ((equivOfBijective f hf).symm y),
      ContinuousLinearEquiv.apply_symm_apply]

/-! ## Norm equivalence -/

/-- **Norm equivalence from a continuous linear bijection.** If `f : E →L[𝕜] F` is a
bijection between Banach spaces, then `‖f x‖` is comparable to `‖x‖` from both
sides: there are constants `0 < c` and `0 < C` with `c ‖x‖ ≤ ‖f x‖ ≤ C ‖x‖` for all
`x`.

The upper bound is just continuity of `f`; the lower bound is the genuine content,
coming from continuity of the inverse furnished by the bounded inverse theorem. In
particular the "graph norm" `x ↦ ‖f x‖` is equivalent to the original norm. -/
theorem norm_equiv_of_bijective (f : E →L[𝕜] F) (hf : Bijective f) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x : E, c * ‖x‖ ≤ ‖f x‖ ∧ ‖f x‖ ≤ C * ‖x‖ := by
  obtain ⟨g, hg1, _hg2⟩ := exists_bounded_inverse f hf
  refine ⟨1 / (‖g‖ + 1), ‖f‖ + 1, by positivity, by positivity, fun x => ?_⟩
  refine ⟨?_, ?_⟩
  · -- lower bound:  (1/(‖g‖+1)) ‖x‖ ≤ ‖f x‖
    have h1 : ‖x‖ ≤ ‖g‖ * ‖f x‖ := by
      have := g.le_opNorm (f x)
      rwa [hg1 x] at this
    have hpos : (0 : ℝ) < ‖g‖ + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos, one_mul]
    nlinarith [norm_nonneg (f x), h1]
  · -- upper bound:  ‖f x‖ ≤ (‖f‖+1) ‖x‖
    calc ‖f x‖ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
      _ ≤ (‖f‖ + 1) * ‖x‖ := by nlinarith [norm_nonneg x, norm_nonneg f]

/-! ## The closed graph theorem -/

/-- **Closed graph theorem.** A linear map between Banach spaces whose graph is a
closed subset of the product is automatically continuous. -/
theorem closed_graph (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) : Continuous g :=
  g.continuous_of_isClosed_graph hg

/-- Sequential form of the closed graph theorem: to prove a linear map between
Banach spaces is continuous it suffices that whenever `uₙ → x` and `g uₙ → y` one
has `y = g x`. -/
theorem closed_graph_seq (g : E →ₗ[𝕜] F)
    (hg : ∀ (u : ℕ → E) (x y), Filter.Tendsto u Filter.atTop (nhds x) →
      Filter.Tendsto (g ∘ u) Filter.atTop (nhds y) → y = g x) :
    Continuous g :=
  g.continuous_of_seq_closed_graph hg

/-- The closed graph theorem, packaged: a linear map with closed graph is upgraded
to a bundled bounded linear map agreeing with it. -/
noncomputable def toContinuousOfClosedGraph (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) : E →L[𝕜] F :=
  ContinuousLinearMap.ofIsClosedGraph hg

@[simp]
theorem toContinuousOfClosedGraph_apply (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) (x : E) :
    toContinuousOfClosedGraph g hg x = g x := rfl

/-! ## Concrete instances

The hypotheses above are not vacuous: here are explicit witnesses. -/

/-- The identity map of a Banach space is open (the trivial but non-vacuous instance
of the open mapping theorem). -/
example : IsOpenMap (id : E → E) :=
  open_mapping (ContinuousLinearMap.id 𝕜 E) surjective_id

/-- A concrete surjection that is not injective: the first coordinate projection
`ℝ² → ℝ` is an open map by the open mapping theorem. -/
example : IsOpenMap (Prod.fst : ℝ × ℝ → ℝ) :=
  open_mapping (ContinuousLinearMap.fst ℝ ℝ ℝ) Prod.fst_surjective

/-- A concrete bijection: doubling on the real line `x ↦ 2x` is a continuous linear
bijection, so by the norm-equivalence corollary its norm is equivalent to the
standard one. -/
example : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ x : ℝ, c * ‖x‖ ≤ ‖(2 : ℝ) * x‖ ∧ ‖(2 : ℝ) * x‖ ≤ C * ‖x‖ := by
  have hbij : Bijective ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) := by
    constructor
    · intro a b hab
      have h2 : (2 : ℝ) * a = 2 * b := by simpa using hab
      linarith
    · intro y
      refine ⟨y / 2, ?_⟩
      simp only [ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_id',
        Pi.smul_apply, id_eq, smul_eq_mul]
      ring
  obtain ⟨c, C, hc, hC, hbound⟩ := norm_equiv_of_bijective ((2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) hbij
  exact ⟨c, C, hc, hC, fun x => by simpa using hbound x⟩

end OpenMappingTheoremOQ01
