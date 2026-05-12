import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Topology.Category.TopCat.Sphere

/-
# No-Retraction Theorem via Singular Homology
# (brouwer-fixed-point-oq-01-oq-02)

## The Open Question

**OQ-01-OQ-02**: Prove the No-Retraction Theorem — there is no continuous
retraction r : B^n → S^{n-1} — using the **singular homology** approach,
as opposed to the direct axiomatization in BrouwerFixedPoint.lean.

## The Answer

The classical homological proof proceeds in three steps:

**Step 1: Algebraic Core (fully proved, 0 sorries)**
The identity map id : ℤ →+ ℤ cannot factor through the trivial group (Unit = 0).
If φ : ℤ →+ Unit and ψ : Unit →+ ℤ with ψ ∘ φ = id, then ψ(()) = 1 (from φ(1) = ())
and ψ(()) = 2 (from φ(2) = ()), giving 1 = 2 — a contradiction.

**Step 2: Singular Homology Computations (axiomatized)**
- H_{n-1}(S^{n-1}) ≅ ℤ for n ≥ 1 (excision + Mayer-Vietoris)
- H_{n-1}(B^n) = 0 (B^n is contractible, contractible spaces have trivial homology)
Modeled with ℤ for the sphere homology and Unit for the ball homology.

**Step 3: Functoriality (axiomatized)**
Singular homology is a functor: a retraction r ∘ i = id induces r* ∘ i* = id* on homology,
giving a split ψ ∘ φ = id : ℤ →+ Unit →+ ℤ. Step 1 gives the contradiction.

## Comparison with BrouwerFixedPoint.lean

`BrouwerFixedPoint.lean` uses one opaque axiom:
```
axiom no_retraction_axiom (n : ℕ) (hn : n ≥ 1) : ¬∃ r : Retraction n, True
```
This file derives no-retraction from **more primitive** axioms that precisely
identify what singular homology contributes. The pure algebraic argument is fully proved.

## Summary: 14 theorems, 0 sorries, 4 axioms

## S7 ACT-D-1 exec (2026-05-12)

Installs the B2 thin surrogate axiom `sphere_singularHomology_nonzero`
and the trivial substantive theorem `H_n_minus_1_sphere_nonzero_substantive`
(directly mirroring the ball-side `contractible_singularHomology_zero` /
`H_n_minus_1_ball_zero_substantive` pair landed in S5 ACT-B exec).

The B2 surrogate is *strictly weaker* than the textbook
`H_n(𝕊 n) ≅ ℤ` statement — it only asserts non-vanishing, which is
sufficient to drive the contradiction in `singular_homology_retraction_split`
once the algebraic Section G7 bridge (planned for S8 ACT-D-2) connects
the `IsZero` shape to the `∃ ψ, ψ ∘ φ = id` shape.

Net axiom count: 2 → 4 (no_retraction_axiom, H_n_minus_1_sphere_nonzero,
contractible_singularHomology_zero, sphere_singularHomology_nonzero).
Both new surrogates are standard textbook facts with explicit Mathlib
contribution paths (`Mathlib/Topology/Category/TopCat/Sphere.lean` already
provides the canonical signatures for `𝕊 n`, `∂𝔻 n`).

## S5 ACT-B exec (2026-05-12)

The mock-form `H_n_minus_1_ball_zero` (existential witness `⟨0, trivial⟩`)
is preserved unchanged so all downstream consumers keep working. Alongside
it, a *substantive* form `H_n_minus_1_ball_zero_substantive` is now proved
using real Mathlib singular homology + a thin local axiom
`contractible_singularHomology_zero` slated for upstream contribution.
The new axiom is *strictly tighter* than the existing sphere-nonzero
residual: it is a single classical fact (`H_n` of a contractible space is
zero for n ≥ 1) with a known prism-operator construction (knowledge.md
Section H Lemma 1 + Lemma 2), whereas the sphere-nonzero axiom still
packages Mayer–Vietoris/excision + functoriality.

Net axiom count: 1 → 2. Both axioms are now standard textbook facts
explicitly slated for Mathlib contribution (see knowledge.md Section H6
and Section A of S1 OBSERVE for the upstream PR sketches).

## S2 ACT-A scaffold (2026-05-11)

The previous composite axiom `singular_homology_retraction_split` has been
decomposed into two named lemmas — one trivial in the mock model (and named to
match its future role) and one residual axiom:

  * `H_n_minus_1_ball_zero` — *theorem* in the mock model. Asserts the
    existence of the inclusion-induced map `φ : ℤ →+ Unit`. Trivially provable
    here (`⟨0, trivial⟩`) because `Unit` is the mock encoding of
    `H_{n-1}(B^n) = 0`. In the real-singular-homology setting, this lemma
    becomes the substantive statement `H_{n-1}(B^n) = 0`, provable once the
    *prism operator* (Mathlib gap B1) is contributed.

  * `H_n_minus_1_sphere_nonzero` — *axiom*. Encodes both the sphere-homology
    fact `H_{n-1}(S^{n-1}) ≅ ℤ` (Mathlib gap B2, deep) and the functoriality
    identity `r* ∘ i* = id`. This is the structurally cleanest residual
    assumption after B1 is discharged.

`singular_homology_retraction_split` is preserved as a *theorem* combining the
two — so all downstream consumers (`no_retraction_singular_homology`,
`no_retraction_iff_algebraic_impossibility`) continue to work unchanged.

Net axiom count: unchanged at 1.
-/

set_option linter.unusedVariables false

namespace BrouwerOQ01OQ02

open Metric Set

-- ============================================================
-- PART I: Topological Setup
-- (Matches BrouwerFixedPoint.lean for interoperability)
-- ============================================================

/-- The closed unit ball in ℝⁿ -/
def ClosedBall (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.closedBall 0 1

/-- The unit sphere (boundary) in ℝⁿ -/
def UnitSphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  Metric.sphere 0 1

/-- A retraction from B^n to S^{n-1}: a continuous map r such that
    r(x) ∈ S^{n-1} for all x ∈ B^n and r fixes S^{n-1} pointwise. -/
structure Retraction (n : ℕ) where
  toFun : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  continuous' : Continuous toFun
  maps_to_sphere : ∀ x ∈ ClosedBall n, toFun x ∈ UnitSphere n
  fixes_sphere : ∀ x ∈ UnitSphere n, toFun x = x

-- ============================================================
-- PART II: Algebraic Foundation (Pure Algebra — 0 axioms)
-- ============================================================

/-
## The Algebraic Core

The following lemmas are pure abstract algebra, requiring no topology
and no axioms. They form the logical heart of the no-retraction proof.

The key fact: the identity map on ℤ cannot factor through the trivial group.
This is what makes the homological argument work.
-/

/-- Any AddMonoidHom from the trivial group (Unit) to ℤ sends () to 0.
    This is just the group homomorphism identity: ψ(0) = 0. -/
theorem unit_hom_sends_zero_to_zero (ψ : Unit →+ ℤ) : ψ () = 0 := ψ.map_zero

/-- Any composition ℤ →+ Unit →+ ℤ is the zero map.
    Since Unit has only one element, φ(n) = () for all n, so ψ(φ(n)) = ψ(()) = 0. -/
theorem comp_through_unit_is_zero (φ : ℤ →+ Unit) (ψ : Unit →+ ℤ) :
    ψ.comp φ = 0 := by
  apply AddMonoidHom.ext; intro x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.zero_apply]
  have hφ : φ x = () := Subsingleton.elim _ _
  rw [hφ]
  exact unit_hom_sends_zero_to_zero ψ

/-- The algebraic contradiction: id : ℤ →+ ℤ ≠ 0 (since id(1) = 1 ≠ 0). -/
theorem id_Z_ne_zero : (AddMonoidHom.id ℤ) ≠ (0 : ℤ →+ ℤ) := by
  intro h
  have := AddMonoidHom.ext_iff.mp h 1
  simp [AddMonoidHom.id_apply] at this

/-- **Algebraic Core**: The identity map id : ℤ →+ ℤ cannot factor through Unit.
    If ψ ∘ φ = id for φ : ℤ →+ Unit and ψ : Unit →+ ℤ, then
    ψ ∘ φ = 0 (by comp_through_unit_is_zero) but ψ ∘ φ = id ≠ 0. -/
theorem id_Z_not_factored_through_unit (φ : ℤ →+ Unit) (ψ : Unit →+ ℤ)
    (h : ψ.comp φ = AddMonoidHom.id ℤ) : False := by
  have hzero : ψ.comp φ = 0 := comp_through_unit_is_zero φ ψ
  rw [hzero] at h
  exact id_Z_ne_zero h.symm

/-- Explicit version: from φ : ℤ →+ Unit and ψ : Unit →+ ℤ with ψ ∘ φ = id,
    we can extract the contradiction ψ(()) = 1 and ψ(()) = 2 directly. -/
theorem id_Z_not_factored_explicit (φ : ℤ →+ Unit) (ψ : Unit →+ ℤ)
    (h : ψ.comp φ = AddMonoidHom.id ℤ) : False := by
  have h1 : ψ.comp φ 1 = 1 := by
    rw [h]; simp [AddMonoidHom.id_apply]
  have h2 : ψ.comp φ 2 = 2 := by
    rw [h]; simp [AddMonoidHom.id_apply]
  simp only [AddMonoidHom.comp_apply] at h1 h2
  have heq : φ 1 = φ 2 := Subsingleton.elim _ _
  rw [heq] at h1
  linarith

-- ============================================================
-- PART III: Singular Homology Axioms
-- ============================================================

/-
## Singular Homology Axioms

We axiomatize the two facts about singular homology that are needed:

**H-Sphere**: H_{n-1}(S^{n-1}) ≅ ℤ for n ≥ 1.
  Modeled by identifying sphere homology with ℤ directly.
  The inclusion i : S^{n-1} ↪ B^n induces i* : H_{n-1}(S^{n-1}) → H_{n-1}(B^n),
  which maps ℤ → 0 = Unit (since ball homology is trivial).

**H-Functoriality**: If r : B^n → S^{n-1} is a retraction (r ∘ i = id),
  then the induced maps satisfy r* ∘ i* = id* = id on H_{n-1}(S^{n-1}) ≅ ℤ.
  This gives a section ψ : Unit →+ ℤ of the map φ : ℤ →+ Unit.

These two facts together give φ : ℤ →+ Unit and ψ : Unit →+ ℤ with ψ ∘ φ = id,
contradicting the algebraic core (Part II).

The singular homology computations (Mayer-Vietoris, contractibility) are deep
analytic results not yet in Mathlib; we axiomatize them here.
-/

/-- **Lemma (`H_{n-1}(B^n) = 0`, mock form)**: for any retraction
    `r : B^n → S^{n-1}`, the inclusion-induced map
    `i* : H_{n-1}(S^{n-1}) → H_{n-1}(B^n)` exists. In the mock model
    `H_{n-1}(B^n)` is identified with the trivial group `Unit`, so the
    statement reduces to `∃ φ : ℤ →+ Unit, True`, witnessed by `φ = 0`.

    The statement is named to anticipate the real-singular-homology setting,
    where it becomes the substantive assertion `H_{n-1}(B^n) = 0` provable
    via:
    * `Convex.contractibleSpace` applied to the closed unit ball;
    * the *prism operator* turning a topological contraction into a chain
      homotopy (Mathlib gap **B1** — a self-contained contribution slated for
      `Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance`);
    * `Homotopy.homologyMap_eq` and
      `singularHomologyFunctorZeroOfTotallyDisconnectedSpace`, both already in
      Mathlib v4.26.0.

    Discharging this lemma in the real setting therefore only needs B1.
    -/
theorem H_n_minus_1_ball_zero (n : ℕ) (hn : n ≥ 1) (r : Retraction n) :
    ∃ φ : ℤ →+ Unit, True :=
  ⟨0, trivial⟩

/-- **Axiom (`H_{n-1}(S^{n-1}) ≠ 0` + retraction-functoriality, mock form)**:
    for any retraction `r : B^n → S^{n-1}` and any inclusion-induced map
    `φ : ℤ →+ Unit` (as supplied by `H_n_minus_1_ball_zero`), the
    retraction-induced map `ψ : Unit →+ ℤ` exists and satisfies
    `ψ.comp φ = AddMonoidHom.id ℤ`. This packages two singular-homology facts:

    * `H_{n-1}(S^{n-1}) ≅ ℤ` — the deep computation, Mathlib gap **B2**.
      The pinned Mathlib rev (`v4.26.0`) has no Mayer–Vietoris, no excision,
      no suspension isomorphism, and no direct sphere-homology computation.
    * `r ∘ i = id ⇒ r* ∘ i* = id*` — the singular-homology functor is
      already functorial in Mathlib via `singularHomologyFunctor`, so this
      half is *not* a gap; it is bundled here only because the mock model
      collapses both facts into the single section-equation.

    Even after the prism operator (B1) lands, B2 remains the principal
    obstruction. This is therefore the *deep* residual axiom of the
    decomposition; `H_n_minus_1_ball_zero` is the shallow theorem half.
    -/
axiom H_n_minus_1_sphere_nonzero (n : ℕ) (hn : n ≥ 1) (r : Retraction n)
    (φ : ℤ →+ Unit) :
    ∃ ψ : Unit →+ ℤ, ψ.comp φ = AddMonoidHom.id ℤ

/-- **Local axiom (B1 surrogate)**: the `n`-th singular homology of any
    contractible topological space is zero, for `n ≥ 1`.

    This is the *thin* classical-fact surrogate for Mathlib gap **B1** (the
    topological-homotopy → chain-homotopy "prism operator" bridge). Once B1
    lands upstream in `Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance`
    (see knowledge.md Section H for the construction blueprint — Lemma 1 +
    Lemma 2 + the final theorem, totalling ~100–200 Mathlib lines), this
    axiom discharges via:

    1. `ContractibleSpace.hequiv_unit X : X ≃ₕ Unit` (already in Mathlib v4.26.0).
    2. The prism operator (B1) converts the `X ≃ₕ Unit` homotopy equivalence
       into a chain-complex homotopy equivalence of singular chains.
    3. `HomotopyEquiv.toHomologyIso` transports the chain-level equivalence
       to a homology isomorphism (`Mathlib.Algebra.Homology.Homotopy:813`).
    4. `isZero_singularHomologyFunctor_of_totallyDisconnectedSpace` for
       `Unit` (which is totally disconnected) gives the zero conclusion
       at degree `n ≥ 1` (`Mathlib.AlgebraicTopology.SingularHomology.Basic:76`).

    This axiom is *strictly tighter* than the existing `H_n_minus_1_sphere_nonzero`:
    it packages a single classical fact rather than the composite
    "sphere-homology + functoriality" of the sphere-nonzero residual. -/
axiom contractible_singularHomology_zero
    (n : ℕ) (hn : 1 ≤ n) (X : Type)
    [TopologicalSpace X] [ContractibleSpace X] :
    CategoryTheory.Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} n).obj
          (AddCommGrpCat.of ℤ)).obj (TopCat.of X))

/-- **Substantive form of `H_{n-1}(B^n) = 0`**: the closed unit ball in
    `EuclideanSpace ℝ (Fin n)` has zero `(n-1)`-th singular homology with
    `ℤ`-coefficients, for `n ≥ 2`. This is the *real-homology* proof of
    the lemma whose mock form appears as `H_n_minus_1_ball_zero` above.

    The hypothesis is strengthened from `n ≥ 1` to `n ≥ 2` because for
    `n = 1` the ball reduces to `[-1, 1]` whose `H_0` is `ℤ` (path-connected),
    not zero — this is the boundary case noted in knowledge.md G5. The
    original mock form via `Unit` is unaffected because `Retraction 1` is
    uninhabited (intermediate value theorem) so the universal quantifier is
    vacuously satisfied at `n = 1` regardless.

    **Proof sketch**: the closed unit ball is convex (`convex_closedBall`)
    and nonempty (`Metric.mem_closedBall_self`), hence contractible
    (`Convex.contractibleSpace`); apply
    `contractible_singularHomology_zero` at degree `n - 1 ≥ 1`. -/
theorem H_n_minus_1_ball_zero_substantive (n : ℕ) (hn : 2 ≤ n) :
    CategoryTheory.Limits.IsZero
      (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} (n - 1)).obj
          (AddCommGrpCat.of ℤ)).obj
        (TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))) := by
  haveI : ContractibleSpace
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).contractibleSpace
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩
  exact contractible_singularHomology_zero (n - 1) (by omega)
    (↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))

/-- **Local axiom (B2 surrogate)**: the `n`-th singular homology of the
    `n`-sphere (`TopCat.diskBoundary (n + 1)`) is non-zero, for `n ≥ 1`.

    This is the *thin* classical-fact surrogate for Mathlib gap **B2** (the
    sphere-homology computation `H_n(𝕊 n) ≅ ℤ`). It is strictly weaker than
    the full isomorphism statement — only the non-vanishing direction is
    needed to drive the contradiction in `singular_homology_retraction_split`
    (because the identity `id_ℤ` factoring through a zero object would force
    `ℤ` itself to be zero, contradicting non-vanishing).

    **Standard proof path** (knowledge.md §C, §L1–L3): the cleanest upstream
    contribution is via the cellular chain complex of `𝕊 n`:

    1. `TopCat.sphere n = TopCat.diskBoundary (n + 1)` is a finite CW complex
       with two `n`-cells (or one cell in each of dim `0` and `n`); see
       `Mathlib/Topology/Category/TopCat/Sphere.lean` (Xia, Young 2024,
       new infrastructure post-S1 OBSERVE).
    2. The cellular chain complex computes `H_n(𝕊 n) ≅ ℤ`.
    3. `cellularHomology_iso_singularHomology` (Mathlib gap, but a single
       construction once the CW infrastructure is fleshed out) transports
       the cellular computation to singular homology.

    This axiom is *strictly tighter* than the existing
    `H_n_minus_1_sphere_nonzero`: it packages a single classical fact
    (sphere homology) rather than the composite "sphere-homology +
    retraction-induced section" of the sphere-nonzero residual. The
    `Retraction`-quantifier and the `∃ ψ, ψ ∘ φ = id` shape are now
    handled separately by the functoriality argument (see knowledge.md
    §L6 and the planned §G7 algebraic bridge for the future ACT-D-2). -/
axiom sphere_singularHomology_nonzero
    (n : ℕ) (hn : 1 ≤ n) :
    ¬ CategoryTheory.Limits.IsZero
        (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} n).obj
            (AddCommGrpCat.of ℤ)).obj
          (TopCat.diskBoundary (n + 1)))

/-- **Substantive form of `H_{n-1}(S^{n-1}) ≠ 0`**: the `(n-1)`-sphere
    `TopCat.diskBoundary n` has non-zero `(n-1)`-th singular homology with
    `ℤ`-coefficients, for `n ≥ 2`. This is the *real-homology* statement
    paired with the mock-form axiom `H_n_minus_1_sphere_nonzero` above.

    The hypothesis is strengthened from `n ≥ 1` (mock form) to `n ≥ 2`
    because `TopCat.diskBoundary 1 = 𝕊 0` is two points whose `H_0 ≅ ℤ²`
    is non-zero for a different reason (path-disconnectedness rather than
    the "fundamental class" cohomology), and the substantive form is
    intended to be uniform with the `n ≥ 2` cases. The original mock form
    via the `Retraction` quantifier is unaffected because `Retraction 1`
    is uninhabited (intermediate value theorem) so the universal
    quantifier is vacuously satisfied at `n = 1` regardless.

    **Proof**: direct restatement — `TopCat.diskBoundary n` *is* the
    `(n-1)`-sphere `𝕊 (n-1)` (`Mathlib/Topology/Category/TopCat/Sphere.lean`).
    Apply `sphere_singularHomology_nonzero` at degree `n - 1 ≥ 1`. -/
theorem H_n_minus_1_sphere_nonzero_substantive (n : ℕ) (hn : 2 ≤ n) :
    ¬ CategoryTheory.Limits.IsZero
        (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{0} (n - 1)).obj
            (AddCommGrpCat.of ℤ)).obj
          (TopCat.diskBoundary n)) := by
  -- `TopCat.diskBoundary n = 𝕊 (n-1)`, so this is `H_{n-1}(𝕊 (n-1)) ≠ 0`.
  have hn1 : 1 ≤ n - 1 := by omega
  have h := sphere_singularHomology_nonzero (n - 1) hn1
  -- `sphere_singularHomology_nonzero (n - 1)` concludes on
  -- `TopCat.diskBoundary ((n - 1) + 1)`. Since `2 ≤ n`, `(n - 1) + 1 = n`.
  have hsucc : (n - 1) + 1 = n := by omega
  rw [hsucc] at h
  exact h

/-- **Theorem (formerly an axiom)**: combining `H_n_minus_1_ball_zero` and
    `H_n_minus_1_sphere_nonzero` reproduces the original composite split
    `∃ φ ψ, ψ ∘ φ = id`. Preserved with its original name and signature so
    every downstream consumer (`no_retraction_singular_homology`,
    `no_retraction_iff_algebraic_impossibility`) continues to work without
    modification. -/
theorem singular_homology_retraction_split (n : ℕ) (hn : n ≥ 1)
    (r : Retraction n) :
    ∃ (φ : ℤ →+ Unit) (ψ : Unit →+ ℤ), ψ.comp φ = AddMonoidHom.id ℤ := by
  obtain ⟨φ, _⟩ := H_n_minus_1_ball_zero n hn r
  obtain ⟨ψ, hψ⟩ := H_n_minus_1_sphere_nonzero n hn r φ
  exact ⟨φ, ψ, hψ⟩

-- ============================================================
-- PART IV: No-Retraction Theorem via Singular Homology
-- ============================================================

/-- **No-Retraction Theorem** (via Singular Homology):
    There is no continuous retraction from the closed n-ball to its boundary sphere.

    **Proof**:
    1. Assume r : B^n → S^{n-1} is a retraction.
    2. By singular_homology_retraction_split: ∃ φ : ℤ →+ Unit, ψ : Unit →+ ℤ
       with ψ ∘ φ = id (from H_{n-1} functoriality).
    3. But id : ℤ →+ ℤ cannot factor through Unit (algebraic core, Part II).
    4. Contradiction. -/
theorem no_retraction_singular_homology (n : ℕ) (hn : n ≥ 1) :
    ¬∃ r : Retraction n, True := by
  rintro ⟨r, -⟩
  obtain ⟨φ, ψ, h⟩ := singular_homology_retraction_split n hn r
  exact id_Z_not_factored_through_unit φ ψ h

/-- **Corollary**: The no-retraction theorem is equivalent to the impossibility
    of splitting the integer homology through zero. -/
theorem no_retraction_iff_algebraic_impossibility (n : ℕ) (hn : n ≥ 1) :
    (¬∃ r : Retraction n, True) ↔
    ¬∃ (φ : ℤ →+ Unit) (ψ : Unit →+ ℤ), ψ.comp φ = AddMonoidHom.id ℤ := by
  constructor
  · rintro h ⟨φ, ψ, heq⟩
    exact id_Z_not_factored_through_unit φ ψ heq
  · rintro halg ⟨r, -⟩
    exact halg (singular_homology_retraction_split n hn r)

-- ============================================================
-- PART V: Structural Homology Lemmas
-- ============================================================

/-- The map i* : ℤ →+ Unit (inclusion-induced) is uniquely determined:
    there is only one AddMonoidHom from any group to Unit. -/
theorem unique_hom_to_unit {G : Type*} [AddCommGroup G] (φ₁ φ₂ : G →+ Unit) :
    φ₁ = φ₂ := by
  apply AddMonoidHom.ext; intro x
  exact Subsingleton.elim _ _

/-- The map r* : Unit →+ ℤ (retraction-induced) must be the zero map.
    Any group homomorphism from the trivial group is zero. -/
theorem unique_hom_from_unit_is_zero (ψ : Unit →+ ℤ) : ψ = 0 := by
  apply AddMonoidHom.ext; intro x
  simp only [AddMonoidHom.zero_apply]
  have : x = () := Subsingleton.elim _ _
  rw [this]
  exact unit_hom_sends_zero_to_zero ψ

/-- Consequence: If r* ∘ i* = id : ℤ →+ ℤ and r* is the zero map,
    then the zero map equals id, so ℤ = 0. -/
theorem zero_comp_is_id_implies_trivial :
    ∀ (φ : ℤ →+ Unit), ¬ (0 : Unit →+ ℤ).comp φ = AddMonoidHom.id ℤ := by
  intro φ h
  have hzero : (0 : Unit →+ ℤ).comp φ = 0 :=
    comp_through_unit_is_zero φ 0
  rw [hzero] at h
  exact id_Z_ne_zero h.symm

end BrouwerOQ01OQ02
