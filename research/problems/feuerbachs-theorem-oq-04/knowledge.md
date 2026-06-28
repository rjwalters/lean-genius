# feuerbachs-theorem-oq-04 — Feuerbach's Theorem in Non-Euclidean Geometry

## Session 2026-06-28 (researcher-4): point separation — sdist is a genuine metric [BUILD]

**Mode**: ACT (CONTINUE). The metric foundations + spherical-circle/tangency layers were
already verified on `main`; the one property still missing for `sdist` to be a genuine
metric (besides the hard spherical triangle inequality) was **point separation** — that
`sdist P Q = 0` forces `P = Q`. `main` only had the trivial forward direction
(`sdist_eq_zero_of_eq`). **Outcome**: PROGRESS — added 3 verified declarations
(~30 L). **Docker build VERIFIED** (`docker-build.sh Proofs.FeuerbachsTheoremOQ04`,
`✔ [7743/7743]`); **0-sorry, 0-axiom**, no native_decide.

### What was delivered (appended after `sdist_comm` in `FeuerbachsTheoremOQ04.lean`)
- **`scos_eq_one_iff`** (algebraic core) : for unit `P,Q`, `scos P Q = 1 ↔ P = Q`. Forward
  via `chord_sq` — `‖P−Q‖² = 2 − 2·scos P Q = 0`, so `‖P−Q‖ = 0` (norm nonneg + `nlinarith`)
  and `sub_eq_zero`; backward is `scos_self`.
- **`sdist_eq_zero_iff`** (headline) : for unit `P,Q`, `sdist P Q = 0 ↔ P = Q`. Uses
  `Real.arccos_eq_zero` (`arccos x = 0 ↔ 1 ≤ x`); for unit vectors `scos P Q ≤ 1`, so
  `1 ≤ scos P Q` forces `scos P Q = 1`, then `scos_eq_one_iff`.
- **`sdist_pos`** : distinct model points are at strictly positive spherical distance
  (`lt_of_le_of_ne` on `sdist_nonneg` + `sdist_eq_zero_iff`).

Together with `sdist_self`, `sdist_nonneg`, and `sdist_comm` (all already on `main`), this
makes `sdist` **separate points** — so `(Sⁿ, sdist)` is a genuine metric on the spherical
model *modulo* the spherical triangle inequality (the only remaining axiom of a metric).

GOTCHA: `Real.arccos_eq_zero` is stated as `arccos x = 0 ↔ 1 ≤ x` (a one-sided bound, not
`x = 1`); the `scos P Q ≤ 1` bound is what upgrades `1 ≤ scos` to the equality. For
`‖P−Q‖² = 0 ⇒ ‖P−Q‖ = 0`, `le_antisymm` of a `nlinarith`-proved `≤ 0` with `norm_nonneg`
is robust (avoids guessing the exact `pow_eq_zero_iff` argument form).

### Next steps (unchanged direction)
1. **Spherical triangle inequality** `sdist P R ≤ sdist P Q + sdist Q R` would complete
   `(Sⁿ, sdist)` as a `MetricSpace`. This is the genuinely hard analytic step (arccos
   subadditivity / spherical law of cosines); check `InnerProductGeometry.angle` lemmas
   in Mathlib first — for unit vectors `sdist = InnerProductGeometry.angle`.
2. **Tangent-point existence** for tangent circles (construction-heavy slerp midpoint).
3. Spherical incircle + nine-point circle; attempt the spherical Feuerbach tangency.

BLOCKER (hyperbolic side, unchanged): no Mathlib hyperbolic metric — spherical model only.

## Session 2026-06-28 (researcher-1): spherical circles + tangency layer [BUILD]

**Mode**: ACT (CONTINUE — executed researcher-2's next-steps 1 & 2: "define spherical
circle as level set of scos" and "spherical tangency relations"). **Outcome**: PROGRESS
— extended `FeuerbachsTheoremOQ04.lean` (+8 decls, ~70 L) with the spherical-circle and
tangency layer on top of the existing metric foundations. **Docker build VERIFIED**
(`docker-build.sh Proofs.FeuerbachsTheoremOQ04`); **0-sorry, 0-axiom**, no native_decide
(only `Real.cos_arccos`/`Real.arccos_cos`, `real_inner_comm`, `abs_sub_comm` etc.).

### What was delivered (appended to `FeuerbachsTheoremOQ04.lean`)
- **`sdist_comm`** : `sdist P Q = sdist Q P` (via `real_inner_comm`).
- **`cos_sdist`** : `Real.cos (sdist P Q) = scos P Q` for unit `P,Q` — the bridge between
  the metric (`sdist`) and algebraic (`scos`/inner product) descriptions, from
  `Real.cos_arccos` + the `[-1,1]` bounds.
- **`def sCircle (O ρ) := {P | OnSphere P ∧ scos P O = Real.cos ρ}`** — spherical circle
  as a level set of the spherical cosine.
- **`mem_sCircle_iff_sdist`** (headline) : for `O` on the sphere and `ρ ∈ [0,π]`,
  `P ∈ sCircle O ρ ↔ (OnSphere P ∧ sdist P O = ρ)`. Identifies the algebraic level-set
  circle with the metric "points at spherical distance ρ", so tangency calculations can
  switch freely between the two views. Proof: `Real.arccos_cos` (fwd) / `cos_sdist` (bwd).
- **`def InternallyTangent`** (`sdist O₁ O₂ = |ρ₁−ρ₂|`) and **`def ExternallyTangent`**
  (`sdist O₁ O₂ = ρ₁+ρ₂`) — the non-Euclidean tangency relations.
- **`internallyTangent_comm`**, **`externallyTangent_comm`** : both tangency relations are
  symmetric in the two circles (via `sdist_comm` + `abs_sub_comm`/`add_comm`).

### Next steps (unchanged direction)
1. **Tangent-point existence**: for externally/internally tangent circles, exhibit the
   unique common point on the geodesic between centres (spherical slerp
   `P = cos ρ₁ · O₁ + …`) and prove it lies on both `sCircle`s — this is the genuinely
   harder, construction-heavy step (needs unit-norm + level-set verification).
2. Build the spherical incircle and nine-point circle for a spherical triangle.
3. Attempt the spherical Feuerbach tangency itself.

BLOCKER (hyperbolic side, unchanged): no Mathlib hyperbolic metric — spherical model only.

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
