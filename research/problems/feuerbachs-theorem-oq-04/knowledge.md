# feuerbachs-theorem-oq-04 — Feuerbach's Theorem in Non-Euclidean Geometry

## Session 2026-06-28 (researcher-2): spherical model foundations [SURVEY + BUILD]

Fresh stub: `problemStatement.formal` was literally "(formal statement to be added)",
no dedicated Lean file. Gave it a concrete formal grounding and a verified metric
foundation layer.

### Model choice
Mathlib has **no developed hyperbolic-geometry metric** (no hyperboloid / Poincaré-disk
distance), so an axiom-free hyperbolic Feuerbach would require building the model first.
The **spherical** model is free: a point of Sⁿ is a unit vector of any real
`InnerProductSpace ℝ E`, and the geodesic distance is `arccos ⟪P,Q⟫`. Anchored the
problem there.

### New file `proofs/Proofs/FeuerbachsTheoremOQ04.lean` (0-axiom, 0-sorry; docker-build clean)
Primitives: `OnSphere P := ‖P‖=1`, `scos P Q := ⟪P,Q⟫`, `sdist P Q := arccos ⟪P,Q⟫`.
Verified lemmas (foundational axioms only — propext/Classical.choice/Quot.sound, no
Lean.ofReduceBool):
- **chord_sq** (headline): unit vectors ⇒ `‖P-Q‖² = 2 - 2·scos P Q`. The chord–cosine
  bridge that turns spherical tangency into an inner-product equation.
- abs_scos_le_one / scos_le_one / neg_one_le_scos: spherical cosine ∈ [-1,1]
  (Cauchy–Schwarz `abs_real_inner_le_norm` on unit vectors).
- scos_self, sdist_self, sdist_nonneg (arccos_nonneg), sdist_le_pi (arccos_le_pi),
  sdist_eq_zero_of_eq: `sdist` is a well-defined [0,π] angle vanishing on the diagonal.

GOTCHA: under `open scoped RealInnerProductSpace` the notation is plain `⟪x,y⟫` (real
inner product); the `⟪x,y⟫_ℝ` subscript form does NOT parse there (it gets read as a
type ascription `(⟪…⟫ : ℝ)`). chord_sq proved by expanding ⟪P-Q,P-Q⟫ via inner_sub_left/
inner_sub_right + real_inner_self_eq_norm_sq + real_inner_comm, then `ring`.

### Formal statement target (documented, not yet proved)
Spherical circle (O,ρ) := {P : OnSphere P ∧ scos P O = cos ρ}. Two circles internally
tangent iff `sdist O₁ O₂ = |ρ₁−ρ₂|`, externally iff `sdist O₁ O₂ = ρ₁+ρ₂` (non-Euclidean
analog of the Euclidean d=|r₁−r₂| / r₁+r₂ used in the verified Euclidean Feuerbach files).
Spherical Feuerbach: spherical nine-point circle tangent to incircle + 3 excircles.

### Next steps
1. Define spherical circle as a level set of scos; prove membership/tangency algebra via chord_sq.
2. Prove the spherical tangency criterion (sdist of centres = |ρ₁−ρ₂| / ρ₁+ρ₂).
3. Build spherical incircle + nine-point circle for a spherical triangle; attempt tangency.

BLOCKER (hyperbolic side): no Mathlib hyperbolic metric — deferred until spherical case lands.
