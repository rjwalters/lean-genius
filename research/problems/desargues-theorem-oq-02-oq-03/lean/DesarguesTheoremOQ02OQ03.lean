/-
# Desargues' Theorem over Free Modules on (Non-Commutative) Division Rings (OQ-02-OQ-03)

Research Question: Over a free rank-3 module `M = R^3` on a possibly
non-commutative ring `R`, under what conditions does Desargues' theorem hold,
and precisely where does the division-ring hypothesis enter?

Answer (forward direction, formalized here): Desargues' theorem holds whenever
`R` is a division ring, and **commutativity is never used** (that governs Pappus,
not Desargues). We isolate the linear-algebra heart of the theorem:

  * `nucleus_sum` — the three "cross" vectors telescope to `0`. This is the
    entire geometric content and holds in ANY module: no division, no
    commutativity.
  * `cross_dep` — hence the three intersection points are collinear.
  * `cross_eq` — under normalized central perspectivity the unprimed cross
    vector `a - b` equals the primed cross vector `b' - a'`, so `a - b` is the
    genuine intersection of lines `AB` and `A'B'`.
  * `desargues` — the assembled theorem: two triangles centrally perspective
    (in normalized form) from `O` are axially perspective (their three side
    intersections are collinear and each lies on both relevant lines).
  * `normalize_perspective` / `smul_ne_zero'` — the ONLY place invertibility is
    used: rescaling a raw perspectivity `o = α•a + β•a'` to the normalized
    `o = ã + ã'` requires `α, β` invertible and the *absence of zero divisors*
    (so the rescaled representatives stay nonzero). Commutativity is not used
    here either.
  * `smul_preserves_nonzero_iff_no_zero_divisors` — the algebraic converse hinge:
    the `smul_ne_zero'` fact the forward proof relies on is *equivalent* to `R`
    having no zero divisors, and `zero_divisor_breaks_normalization` exhibits the
    failure otherwise. This pins down exactly which ring-theoretic property the
    coordinatization mechanism demands (the full geometric converse, Hilbert's
    coordinatization theorem, is not attempted).

This complements the gallery's Moulton-plane counterexample
(`desargues-theorem-oq-02`), which realizes the failure direction. Together they
frame the classical equivalence: Desargues holds in `P(R^3)` iff `R` is a
division ring.

Reference: Artin, *Geometric Algebra* (Desargues ⇔ division ring);
Hartshorne, *Foundations of Projective Geometry*.

BUILD STATUS: UNVERIFIED. Written during a Docker + Aristotle blackout
(containerd `meta.db` I/O error on image build; Aristotle MCP returns 404), so
this file has NOT been machine-checked. It is deliberately placed under
`research/problems/.../lean/` (outside the `proofs/Proofs/` glob) so it cannot
break the gallery build. Parts I–II (`nucleus_sum`, `cross_dep`, `cross_eq`,
`desargues`, `normalize_perspective`) and Part III (`zero_divisor_breaks_-`
`normalization`, `smul_preserves_nonzero_iff_no_zero_divisors`) are the reviewed
mathematical core; the Part IV quaternion `example` is an instance-resolution
demonstration, and the Part V `ZMod 4` `example`s are concrete `decide`-checked
witnesses that the zero-divisor obstruction is inhabited (necessity is non-vacuous).

Tags: projective-geometry, desargues, division-ring, non-commutative, modules
-/

import Mathlib

namespace DesarguesTheoremOQ02OQ03

variable {R : Type*} {M : Type*}

/-! ## Part I — The nucleus identity (holds in any module) -/

section Nucleus
variable [Ring R] [AddCommGroup M] [Module R M]

/-- Projective collinearity of three representative vectors: they satisfy a
    nontrivial vanishing linear combination (linear dependence). For pairwise
    independent vectors over a division ring this is exactly the statement that
    the three projective points lie on a common line. -/
def Dep (u v w : M) : Prop :=
  ∃ a b c : R, (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ a • u + b • v + c • w = 0

/-- **Nucleus identity.** The three cross vectors telescope to zero.
    No division ring, no commutativity — pure `AddCommGroup` arithmetic. -/
theorem nucleus_sum (a b c : M) : (a - b) + (b - c) + (c - a) = 0 := by
  abel

/-- The three cross vectors are linearly dependent, with the canonical witness
    `(1, 1, 1)`. Geometrically: the three side-intersection points are always
    collinear. Needs only `Nontrivial R` (so `1 ≠ 0`). -/
theorem cross_dep [Nontrivial R] (a b c : M) : Dep (a - b) (b - c) (c - a) := by
  refine ⟨1, 1, 1, Or.inl one_ne_zero, ?_⟩
  simp only [one_smul]
  exact nucleus_sum a b c

/-- Membership helper: `x - y` lies in the span of any set containing `x, y`. -/
theorem sub_mem_span {x y : M} {s : Set M} (hx : x ∈ s) (hy : y ∈ s) :
    x - y ∈ Submodule.span R s :=
  Submodule.sub_mem _ (Submodule.subset_span hx) (Submodule.subset_span hy)

/-- **Cross-vector coincidence.** Under normalized central perspectivity
    `o = a + a' = b + b'`, the unprimed cross vector equals the primed one.
    This is exactly what makes `a - b` a point of BOTH line `AB` and line
    `A'B'`, i.e. their intersection. Pure group arithmetic. -/
theorem cross_eq (o a a' b b' : M) (ha : o = a + a') (hb : o = b + b') :
    a - b = b' - a' := by
  have h : a + a' = b + b' := by rw [← ha]; exact hb
  calc a - b = (a + a') - (b + a') := by abel
    _ = (b + b') - (b + a') := by rw [h]
    _ = b' - a' := by abel

end Nucleus

/-! ## Part II — Desargues' theorem over a division ring -/

section Desargues
variable [DivisionRing R] [AddCommGroup M] [Module R M]

/-- Two triangles `A B C` and `A' B' C'` are *centrally perspective in
    normalized form* from `O` when representative vectors satisfy
    `o = a + a' = b + b' = c + c'`. Over a division ring any central
    perspectivity can be put in this form — see `normalize_perspective`. -/
structure NormPersp (o a a' b b' c c' : M) : Prop where
  ha : o = a + a'
  hb : o = b + b'
  hc : o = c + c'

/-- **Desargues' theorem (linear form).** If triangles `ABC` and `A'B'C'` are
    centrally perspective (normalized) from `O`, then the three intersection
    points of corresponding sides are collinear (`Dep`), and each cross vector
    lies on both of the lines it is meant to intersect. Commutativity of `R`
    is never used. -/
theorem desargues (o a a' b b' c c' : M) (h : NormPersp o a a' b b' c c') :
    Dep (a - b) (b - c) (c - a) ∧
    (a - b ∈ Submodule.span R ({a, b} : Set M) ∧
     a - b ∈ Submodule.span R ({a', b'} : Set M)) ∧
    (b - c ∈ Submodule.span R ({b, c} : Set M) ∧
     b - c ∈ Submodule.span R ({b', c'} : Set M)) ∧
    (c - a ∈ Submodule.span R ({c, a} : Set M) ∧
     c - a ∈ Submodule.span R ({c', a'} : Set M)) := by
  refine ⟨cross_dep a b c, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  -- a - b on line AB
  · exact sub_mem_span (by simp) (by simp)
  -- a - b = b' - a' on line A'B'
  · rw [cross_eq o a a' b b' h.ha h.hb]
    exact sub_mem_span (by simp) (by simp)
  -- b - c on line BC
  · exact sub_mem_span (by simp) (by simp)
  -- b - c = c' - b' on line B'C'
  · rw [cross_eq o b b' c c' h.hb h.hc]
    exact sub_mem_span (by simp) (by simp)
  -- c - a on line CA
  · exact sub_mem_span (by simp) (by simp)
  -- c - a = a' - c' on line C'A'
  · rw [cross_eq o c c' a a' h.hc h.ha]
    exact sub_mem_span (by simp) (by simp)

/-- Nonzero scalars scale nonzero vectors to nonzero vectors — the "no zero
    divisors" fact that a division ring supplies. This is the crux the
    forward direction needs and a general ring lacks. -/
theorem smul_ne_zero' (α : R) (a : M) (hα : α ≠ 0) (ha : a ≠ 0) : α • a ≠ 0 := by
  intro h
  apply ha
  have h2 : α⁻¹ • (α • a) = α⁻¹ • (0 : M) := by rw [h]
  rwa [smul_smul, inv_mul_cancel₀ hα, one_smul, smul_zero] at h2

/-- **Where the division-ring hypothesis enters.** A raw central perspectivity
    presents `o` as a linear combination `o = α • a + β • a'` of the two vertex
    representatives. When `α, β ≠ 0` (forced by `O ≠ A'` and `O ≠ A`), the
    rescaled vectors `α • a`, `β • a'` still represent the *same* projective
    points `A`, `A'` (they are nonzero, because a division ring has no zero
    divisors) and satisfy the normalized equation `o = (α•a) + (β•a')`.

    This is the ONLY step requiring invertibility; it uses no commutativity. -/
theorem normalize_perspective
    (o a a' : M) (α β : R) (ho : o = α • a + β • a')
    (ha : a ≠ 0) (ha' : a' ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) :
    ∃ ã ã' : M, ã ≠ 0 ∧ ã' ≠ 0 ∧
      (∃ u : Rˣ, ã = (u : R) • a) ∧ (∃ v : Rˣ, ã' = (v : R) • a') ∧
      o = ã + ã' :=
  ⟨α • a, β • a', smul_ne_zero' α a hα ha, smul_ne_zero' β a' hβ ha',
    ⟨Units.mk0 α hα, rfl⟩, ⟨Units.mk0 β hβ, rfl⟩, ho⟩

end Desargues

/-! ## Part III — Necessity of the no-zero-divisors hypothesis (converse hinge)

The forward direction used invertibility in exactly one spot: `smul_ne_zero'`,
the fact that a nonzero scalar scales a nonzero vector to a nonzero vector. We now
show this fact is *not free* — it is **equivalent** to `R` having no zero divisors,
and it genuinely fails otherwise. This is the algebraic half of the converse: it
pins down precisely which ring-theoretic property the coordinatization mechanism
demands. (The full geometric converse — that a Desarguesian plane is coordinatized
by a division ring — is Hilbert's coordinatization theorem and is not attempted
here.) We read `R` as a module over itself, which is the coordinate line of
`P(R^n)`. -/

section Necessity
variable [Ring R]

/-- **Zero-divisor obstruction.** If `R` has a zero divisor — nonzero `α, d` with
    `α * d = 0` — then the normalization mechanism of the forward direction breaks:
    the nonzero coordinate `d` is sent by the nonzero scalar `α` to `0`, which
    represents no projective point. So `smul_ne_zero'` genuinely fails once `R`
    leaves the class of domains. -/
theorem zero_divisor_breaks_normalization
    (α d : R) (hα : α ≠ 0) (hd : d ≠ 0) (hzd : α * d = 0) :
    α • d = (0 : R) ∧ d ≠ 0 ∧ α ≠ 0 := by
  refine ⟨?_, hd, hα⟩
  simpa [smul_eq_mul] using hzd

/-- **The forward crux is equivalent to being a domain.** For the regular module
    `M = R`, the `smul_ne_zero'` property (nonzero scalar · nonzero vector ≠ 0,
    for all scalars and vectors) holds **iff** `R` has no zero divisors. Combined
    with `normalize_perspective`, this shows the division-ring hypothesis of the
    forward direction is exactly as strong as it needs to be at the rescaling
    step — no weaker hypothesis on `R` supports the normalization. -/
theorem smul_preserves_nonzero_iff_no_zero_divisors :
    (∀ α a : R, α ≠ 0 → a ≠ 0 → α • a ≠ (0 : R)) ↔
    (∀ α a : R, α * a = 0 → α = 0 ∨ a = 0) := by
  constructor
  · intro h α a hmul
    by_contra hcon
    push_neg at hcon
    exact h α a hcon.1 hcon.2 (by simpa [smul_eq_mul] using hmul)
  · intro h α a hα ha hcon
    rcases h α a (by simpa [smul_eq_mul] using hcon) with h0 | h0
    · exact hα h0
    · exact ha h0

end Necessity

/-! ## Part IV — The non-commutative case is genuinely covered -/

/-- The real quaternions `ℍ` form a non-commutative division ring, so Desargues
    applies verbatim to modules over `ℍ`. This witnesses that the theorem is not
    secretly using commutativity. -/
example (o a a' b b' c c' : Fin 3 → Quaternion ℝ)
    (h : NormPersp o a a' b b' c c') :
    Dep (R := Quaternion ℝ) (a - b) (b - c) (c - a) :=
  (desargues (R := Quaternion ℝ) o a a' b b' c c' h).1

/-! ## Part V — The zero-divisor obstruction is concretely inhabited

Part III shows the forward crux `smul_ne_zero'` is *equivalent* to `R` having no
zero divisors. Part IV exhibits a genuine non-commutative division ring where the
theorem applies (positive witness). We close the loop with a concrete *negative*
witness: a ring where the obstruction actually fires, so the necessity direction
of the iff is not vacuous. -/

/-- **Concrete negative witness.** `ZMod 4` is not a domain — the nonzero scalar
    `2` sends the nonzero coordinate `2` to `0`. So `smul_ne_zero'` genuinely fails
    here and the normalization mechanism of the forward direction collapses,
    matching `zero_divisor_breaks_normalization`. This is the counterpart to the
    quaternion positive witness: together they show the division-ring hypothesis is
    both sufficient (Parts I–IV) and, at the rescaling step, necessary (Part III). -/
example : (2 : ZMod 4) • (2 : ZMod 4) = 0 ∧ (2 : ZMod 4) ≠ 0 ∧ (2 : ZMod 4) ≠ 0 :=
  zero_divisor_breaks_normalization (2 : ZMod 4) 2 (by decide) (by decide) (by decide)

/-- The obstruction defeats the crux `smul_preserves_nonzero_iff_no_zero_divisors`
    from the failing side: `ZMod 4` does not satisfy the nonzero-preservation
    property, exactly because it has the zero divisor `2 * 2 = 0`. -/
example : ¬ (∀ α a : ZMod 4, α ≠ 0 → a ≠ 0 → α • a ≠ (0 : ZMod 4)) := by
  rw [smul_preserves_nonzero_iff_no_zero_divisors]
  decide

end DesarguesTheoremOQ02OQ03
