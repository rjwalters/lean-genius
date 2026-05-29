/-
# Kakutani from Brouwer via Approximate Selections

This file outlines the proof of Kakutani's fixed point theorem from
Brouwer's fixed point theorem using approximate continuous selections.

**Proof Strategy**:
1. For each n, construct a continuous 1/n-approximate selection f_n of F
2. Apply Brouwer's FPT: ∃ x_n with f_n(x_n) = x_n
3. By compactness of S: extract convergent subsequence x_{n_k} → x*
4. Use upper hemicontinuity to show x* ∈ F(x*)

**Status**: AXIOMATIZED (2 axioms)
- Axiom 1: Brouwer's FPT in Euclidean space
- Axiom 2: Cellina–Browder graph-approximate selections exist for UHC
  maps with convex values
- Proved: Sequential compactness (from Mathlib's IsCompact.isSeqCompact)
- Proved: The combination argument (Kakutani from the two axioms via the helper)
- Proved: The limit-argument helper (approx_fixedpoint_implies_fixedpoint)

**Why graph-approximate selections (vs pointwise / simplicial approximation)?**
The simplicial approach avoids approximate selections altogether but
requires triangulation infrastructure not currently in Mathlib. The
selection approach requires only `Mathlib.Topology.PartitionOfUnity`,
but a subtle point (made precise in S6) is that under USC + convex
values one obtains only the *graph* approximate selection (Cellina 1969,
Browder 1968), NOT the pointwise selection: the strictly stronger
pointwise form is mathematically false in general. This file therefore
states the axiom in graph form and threads a triangle-inequality step
through `kakutani_from_brouwer` to recover the diagonal-distance
witness expected by `approx_fixedpoint_implies_fixedpoint`.

**References**:
- Kakutani, S. (1941). A generalization of Brouwer's fixed point theorem.
  Duke Math. J. 8, 457-459.
- Cellina, A. (1969). Approximation of set valued functions and fixed
  point theorems. Ann. Mat. Pura Appl. 82, 17-24.

Parent: SchauderFixedPointOQ03.lean (Kakutani framework)
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Sequences
import Mathlib.Tactic

noncomputable section

open Set Filter Topology Metric

-- The `⟪x, y⟫_ℝ` real-inner-product notation moved to `scoped[InnerProductSpace]`
-- under Mathlib v4.26.0; the deprecated `Mathlib.Analysis.InnerProductSpace.Projection`
-- monolith used to bring it in transitively. Open the scope explicitly here so the
-- nearest-point retraction proof (`exists_continuous_proj_convex`, lines 211–) and
-- the §4.b Hilbert-projection helper (S19 ACT, lines 859–) keep parsing.
open scoped InnerProductSpace

namespace KakutaniFromBrouwer

-- ============================================================
-- Part I: Definitions (imported from parent)
-- ============================================================

/-- A set-valued map (correspondence). -/
def SetValuedMap (X Y : Type*) := X → Set Y

/-- Fixed point of a set-valued map: x ∈ F(x). -/
def IsFixedPoint {X : Type*} (F : SetValuedMap X X) (x : X) : Prop :=
  x ∈ F x

/-- Upper hemicontinuity: {x | F(x) ⊆ V} is open for every open V. -/
def IsUpperHemicontinuous {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (F : SetValuedMap X Y) : Prop :=
  ∀ V : Set Y, IsOpen V → IsOpen {x | F x ⊆ V}

/-- **S17 scaffold helper for `approx_selection_exists` (Cellina–Browder
    Step 1):** For any upper-hemicontinuous set-valued map `F : X → 2^Y`
    with `Y` a pseudo-metric space, at every basepoint `x₀ : X` and every
    `ε > 0` there is an open neighborhood `U ∋ x₀` on which `F` is contained
    in the `ε`-thickening of `F(x₀)`.

    This unpacks the abstract UHC definition (`{x | F x ⊆ V}` open for
    every open `V`) into the metric form used in the cover-by-thickening
    step of the PartitionOfUnity proof outlined in the
    `approx_selection_exists` docstring (Axiom 2 below). It introduces no
    new axioms and no new definitions; the proof is a one-line application
    of UHC at `V = Metric.thickening ε (F x₀)` together with the standard
    `Metric.self_subset_thickening`. Building this scaffold helper up
    front lets the eventual S12+ Cellina–Browder construction reuse a
    typechecked Step-1 lemma instead of re-deriving it inline.

    **Cellina–Browder construction outline** (for reference; Steps 2–5
    are the unrealized S12+ work):

    1. ✓ (this lemma) — for each `x ∈ S`, pick `y_x ∈ F(x)` and obtain an
       open `U_x ∋ x` with `F(U_x) ⊆ ε`-thickening of `F(x)`.
    2. Compactness extracts a finite subcover `U_{x_1}, …, U_{x_k}`.
    3. Subordinate partition of unity `{φ_i}` with `supp φ_i ⊆ U_{x_i}`.
    4. Define `f(x) := Σ φ_i(x) · y_{x_i}`. Convexity of `S` gives `f x ∈ S`.
    5. Graph bound: at any `x`, pick `i` with `φ_i(x) > 0`; then
       `x ∈ U_{x_i}` and `(x_i, y_{x_i})` witnesses graph-distance `< ε`. -/
lemma uhc_local_thickening {X Y : Type*} [TopologicalSpace X]
    [PseudoMetricSpace Y]
    {F : SetValuedMap X Y} (hF : IsUpperHemicontinuous F)
    (x₀ : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
      ∀ x ∈ U, F x ⊆ Metric.thickening ε (F x₀) := by
  refine ⟨{x | F x ⊆ Metric.thickening ε (F x₀)},
          hF _ Metric.isOpen_thickening,
          ?_, fun _ hx => hx⟩
  exact Metric.self_subset_thickening hε _

/-- **S18f scaffold (input-diameter refinement of S17 `uhc_local_thickening`):**

    Sharpens `uhc_local_thickening` (S17 helper, line 101 above) by
    additionally bounding the input-ball diameter: at every basepoint
    `x₀ : X` and every `ε > 0` there is an open neighborhood `U ∋ x₀`
    contained in `Metric.ball x₀ ε` (input-side diameter `< ε` on
    `↥S`-distances) on which `F` is contained in the `ε`-thickening of
    `F(x₀)` (output-side bound).

    **Why both bounds are needed:** the eventual `IsGraphApproxSelection`
    predicate (line 471) requires `∃ x' y, dist x x' < ε ∧ y ∈ F x' ∧
    dist (f x) y < ε`. The Cellina–Browder construction picks
    `x' := i ∈ ρ.finsupport x` (a partition center) and uses
    `x ∈ tsupport (ρ i) ⊆ U i` (the subordinate-partition clause from
    S18d) together with the open-cover from this helper. To certify
    `dist x i < ε` we need the input-side bound `U i ⊆ Metric.ball i ε`,
    which the S17 helper does **not** provide — the S17 survey
    (`s17-cellina-mathlib-api-survey.md`, Step 5 footnote) explicitly
    flagged this as a load-bearing missing clause for the final graph
    bound. This iteration closes that gap.

    **Proof:** intersect the `U₀` produced by `uhc_local_thickening` with
    `Metric.ball x₀ ε`. Both are open (`IsOpen.inter` + `Metric.isOpen_ball`)
    and both contain `x₀` (`hx_U₀` + `Metric.mem_ball_self hε`); the
    thickening clause restricts to the intersection trivially via
    `Set.inter_subset_left`, and the new input-ball clause is
    `Set.inter_subset_right`.

    No new axiom is introduced; `axiom approx_selection_exists` (Axiom 2
    below) remains in the file unchanged. -/
lemma uhc_local_thickening_with_input_diameter
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {F : SetValuedMap X Y} (hF : IsUpperHemicontinuous F)
    (x₀ : X) (ε : ℝ) (hε : 0 < ε) :
    ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧ U ⊆ Metric.ball x₀ ε ∧
      ∀ x ∈ U, F x ⊆ Metric.thickening ε (F x₀) := by
  obtain ⟨U₀, hU₀_open, hx_U₀, hU₀_thick⟩ :=
    uhc_local_thickening hF x₀ ε hε
  refine ⟨U₀ ∩ Metric.ball x₀ ε,
          hU₀_open.inter Metric.isOpen_ball,
          ⟨hx_U₀, Metric.mem_ball_self hε⟩,
          Set.inter_subset_right,
          fun x hx => hU₀_thick x hx.1⟩

-- ============================================================
-- Part II: Key Axioms
-- ============================================================

/-- **Axiom 1: Brouwer's Fixed Point Theorem on the Closed Unit Ball**

    Every continuous self-map of the closed unit ball in
    `EuclideanSpace ℝ (Fin n)` has a fixed point.

    **S11.A strict-weakening (2026-05-09):** This axiom replaces the
    previous `axiom brouwer_fpt` (which asserted the FPT for *any*
    nonempty compact convex `S`). Following S10's reconnaissance
    (Brouwer FPT is absent from Mathlib4 — neither unit-ball nor
    general-compact-convex form is present at the pinned rev or on
    master; see `s10-mathlib-v426-lookup3-resolved.md`), this
    iteration adopts S10's recommended **Option A**:

    * Strict-weakening on the Brouwer side: assume only the unit-ball
      form (a smaller mathematical commitment, identical axiom
      *count*).
    * The general-compact-convex form is recovered in-house as
      `theorem brouwer_fpt` via the nearest-point retraction reduction
      (S8 design + S11.B helper), pulling the obstruction to a single
      Mathlib API surface (`exists_norm_eq_iInf_of_complete_convex` plus
      its variational-inequality continuity refinement).

    **Mathlib status (S10):** Absent. `docs/100.yaml` entry for
    "Brouwer Fixed Point Theorem" points to an external Lean 3
    implementation; `docs/1000.yaml` flags it as `comment: "in Lean 3"`.
    No Lean file in `Mathlib/Topology/...` or `Mathlib/Analysis/...` at
    the pinned rev contains the topological Brouwer FPT (the three
    `Brouwer` hits across all `.lean` files are in
    `Mathlib/Order/Heyting/...` — Heyting-algebra Brouwer, not the FPT). -/
axiom brouwer_unit_ball {n : ℕ}
    (f : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
       → ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
    (hf : Continuous f) :
    ∃ x, f x = x

/-- **LOOKUP-2 helper (S11.B work item, landed in S14):**
    Nearest-point retraction onto a nonempty compact convex set in
    `EuclideanSpace ℝ (Fin n)`, packaged as a continuous map that is the
    identity on the set.

    **Proof structure (landed in S14, researcher-3, 2026-05-09;
    Mathlib API drift fixed in S15, PR #17654):** existence and
    uniqueness of the nearest point come from
    `exists_norm_eq_iInf_of_complete_convex`
    (`Mathlib.Analysis.InnerProductSpace.Projection`) combined with
    strict convexity of the Euclidean norm; continuity is derived from
    1-Lipschitz, obtained from the variational inequality
    (`norm_eq_iInf_iff_real_inner_le_zero`) plus the Cauchy–Schwarz
    bound on the inner product; idempotency on `↥S` follows from
    `dist_self` and `norm_eq_zero`. With this helper, `theorem
    brouwer_fpt` below is end-to-end sorry-free. -/
lemma exists_continuous_proj_convex {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S) :
    ∃ r : EuclideanSpace ℝ (Fin n) → ↥S,
      Continuous r ∧ ∀ x : ↥S, r (x : EuclideanSpace ℝ (Fin n)) = x := by
  -- S14 (researcher-3, 2026-05-09): full nearest-point retraction proof.
  -- The Hilbert projection theorem (`exists_norm_eq_iInf_of_complete_convex`)
  -- gives existence of the nearest point on a complete convex set.
  -- Continuity follows from 1-Lipschitz, derived from the variational
  -- inequality (`norm_eq_iInf_iff_real_inner_le_zero`) and Cauchy–Schwarz.
  -- Idempotency on `↥S` follows from the infimum being 0 when `x ∈ S`.
  classical
  -- v4.26.0: `le_ciInf` / `ciInf_le` now require an explicit `[Nonempty ↥S]`
  -- instance rather than auto-deriving it from `S.Nonempty` in the proof body.
  haveI : Nonempty ↥S := hS_ne.to_subtype
  have hS_complete : IsComplete S := hS_compact.isComplete
  have hexists : ∀ u : EuclideanSpace ℝ (Fin n),
      ∃ v ∈ S, ‖u - v‖ = ⨅ w : S, ‖u - w‖ :=
    exists_norm_eq_iInf_of_complete_convex hS_ne hS_complete hS_convex
  -- Define the retraction via Classical.choose.
  let r : EuclideanSpace ℝ (Fin n) → ↥S := fun u =>
    ⟨Classical.choose (hexists u), (Classical.choose_spec (hexists u)).1⟩
  have hr_min : ∀ u, ‖u - (r u : EuclideanSpace ℝ (Fin n))‖ = ⨅ w : S, ‖u - w‖ :=
    fun u => (Classical.choose_spec (hexists u)).2
  have hr_mem : ∀ u, (r u : EuclideanSpace ℝ (Fin n)) ∈ S := fun u => (r u).2
  -- Variational inequality (characterization of the projection).
  have hVI : ∀ u : EuclideanSpace ℝ (Fin n),
      ∀ w ∈ S, ⟪u - (r u : EuclideanSpace ℝ (Fin n)),
                  w - (r u : EuclideanSpace ℝ (Fin n))⟫_ℝ ≤ 0 := by
    intro u
    rw [← norm_eq_iInf_iff_real_inner_le_zero hS_convex (hr_mem u)]
    exact hr_min u
  -- Lower-bound zero of `‖u - ·‖` is shared by every `u`; needed for ciInf bounds.
  have hbdd : ∀ u : EuclideanSpace ℝ (Fin n),
      BddBelow (Set.range fun w : S => ‖u - (w : EuclideanSpace ℝ (Fin n))‖) := by
    intro u
    refine ⟨0, ?_⟩
    rintro y ⟨z, rfl⟩
    exact norm_nonneg _
  refine ⟨r, ?_, ?_⟩
  · -- Continuity: prove r is 1-Lipschitz.
    have hLip : ∀ u₁ u₂ : EuclideanSpace ℝ (Fin n),
        ‖(r u₁ : EuclideanSpace ℝ (Fin n)) - (r u₂ : EuclideanSpace ℝ (Fin n))‖
          ≤ ‖u₁ - u₂‖ := by
      intro u₁ u₂
      -- v4.26.0: explicit `↑` is required for the `↥S → EuclideanSpace ℝ (Fin n)`
      -- coercion in `set`'s RHS — bare `(r u₁ : _)` no longer auto-coerces.
      set v₁ : EuclideanSpace ℝ (Fin n) := (↑(r u₁) : EuclideanSpace ℝ (Fin n)) with hv₁
      set v₂ : EuclideanSpace ℝ (Fin n) := (↑(r u₂) : EuclideanSpace ℝ (Fin n)) with hv₂
      have h1 : ⟪u₁ - v₁, v₂ - v₁⟫_ℝ ≤ 0 := hVI u₁ v₂ (hr_mem u₂)
      have h2 : ⟪u₂ - v₂, v₁ - v₂⟫_ℝ ≤ 0 := hVI u₂ v₁ (hr_mem u₁)
      -- Algebraic identity: the sum of the two variational quantities equals
      --   ‖v₁ - v₂‖² - ⟪u₁ - u₂, v₁ - v₂⟫.
      have hexp : ⟪u₁ - v₁, v₂ - v₁⟫_ℝ + ⟪u₂ - v₂, v₁ - v₂⟫_ℝ
                = ‖v₁ - v₂‖ ^ 2 - ⟪u₁ - u₂, v₁ - v₂⟫_ℝ := by
        have hself : ⟪v₁ - v₂, v₁ - v₂⟫_ℝ = ‖v₁ - v₂‖ ^ 2 :=
          real_inner_self_eq_norm_sq _
        -- v4.26.0: `real_inner_comm x y : ⟪y, x⟫ = ⟪x, y⟫` (the convention flipped
        -- relative to the old call); swap arguments to recover the same equation.
        have hcomm : ⟪v₂, v₁⟫_ℝ = ⟪v₁, v₂⟫_ℝ := real_inner_comm v₁ v₂
        simp only [inner_sub_left, inner_sub_right, hcomm] at hself
        simp only [inner_sub_left, inner_sub_right, hcomm]
        linarith [hself]
      have hsum : ‖v₁ - v₂‖ ^ 2 ≤ ⟪u₁ - u₂, v₁ - v₂⟫_ℝ := by
        have := add_le_add h1 h2
        linarith [hexp]
      -- Cauchy–Schwarz upper bound on the right.
      have hcs : ⟪u₁ - u₂, v₁ - v₂⟫_ℝ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ :=
        real_inner_le_norm _ _
      have hsq : ‖v₁ - v₂‖ ^ 2 ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := hsum.trans hcs
      -- Conclude ‖v₁ - v₂‖ ≤ ‖u₁ - u₂‖ via case-split on whether v₁ = v₂.
      rcases eq_or_lt_of_le (norm_nonneg (v₁ - v₂)) with heq | hpos
      · rw [← heq]; exact norm_nonneg _
      · have hsq' : ‖v₁ - v₂‖ * ‖v₁ - v₂‖ ≤ ‖u₁ - u₂‖ * ‖v₁ - v₂‖ := by
          have h := hsq; rw [sq] at h; exact h
        exact le_of_mul_le_mul_right hsq' hpos
    -- Convert Lipschitz on the underlying value to continuity into ↥S.
    refine continuous_induced_rng.mpr ?_
    -- v4.26.0: the original `dist (f u₁) (f u₂) ≤ ((1 : ℝ≥0) : ℝ) * dist u₁ u₂`
    -- formulation triggers a `Type`-kind metavariable in the `≤` / `OfNat 0`
    -- elaboration. Refactor: name the underlying function `f` and use
    -- `LipschitzWith.mk_one` (the `K = 1` specialization of `of_dist_le_mul`)
    -- which sidesteps the `ℝ≥0 → ℝ` cast entirely.
    let f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun u => Subtype.val (r u)
    have hf_dist : ∀ u₁ u₂ : EuclideanSpace ℝ (Fin n),
        dist (f u₁) (f u₂) ≤ dist u₁ u₂ := by
      intro u₁ u₂
      rw [dist_eq_norm, dist_eq_norm]
      exact hLip u₁ u₂
    have hLipWith : LipschitzWith 1 f := LipschitzWith.mk_one hf_dist
    exact hLipWith.continuous
  · -- Idempotency: `x ∈ S ⇒ r x = x`.
    intro x
    apply Subtype.ext
    -- The infimum of `‖x - ·‖` over `S` is 0, attained at `x ∈ S`.
    have hinf_zero : (⨅ w : S, ‖(x : EuclideanSpace ℝ (Fin n)) - w‖) = 0 := by
      apply le_antisymm
      · have hle :
            (⨅ w : S, ‖(x : EuclideanSpace ℝ (Fin n)) - w‖)
              ≤ ‖(x : EuclideanSpace ℝ (Fin n)) - (x : EuclideanSpace ℝ (Fin n))‖ :=
          ciInf_le (hbdd (x : EuclideanSpace ℝ (Fin n))) x
        simpa using hle
      · exact le_ciInf (fun _ => norm_nonneg _)
    have hzero : ‖(x : EuclideanSpace ℝ (Fin n))
                  - (r (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n))‖ = 0 :=
      (hr_min (x : EuclideanSpace ℝ (Fin n))).trans hinf_zero
    have hsub : (x : EuclideanSpace ℝ (Fin n))
              - (r (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n)) = 0 :=
      (norm_eq_zero).mp hzero
    exact (sub_eq_zero.mp hsub).symm

/-- **Theorem 1 (was Axiom 1): Brouwer's FPT on a compact convex subset.**

    Derived from `axiom brouwer_unit_ball` via the nearest-point
    retraction reduction. Net axiom dependence on the Brouwer side is
    strictly weakened from "general compact convex `S`" to "closed unit
    ball only" (S11.A, 2026-05-09; see
    `s10-mathlib-v426-lookup3-resolved.md` Option A).

    **S11.A.body landed (S13, researcher-10, 2026-05-09; see
    `s11-strict-weakening-spec.md` and `s12-s11a-body-step6-refinement.md`).
    S11.B helper (`exists_continuous_proj_convex`) landed in S14
    (researcher-3, PR #17601), with Mathlib API drift fixes in S15
    (PR #17654).** The theorem is now end-to-end sorry-free; the file's
    only remaining assumption on the Brouwer side is the closed-unit-ball
    axiom (`brouwer_unit_ball`).

    **Proof structure:**

    1. Since `S` is compact, it is bounded
       (`IsCompact.isBounded`); pick `R > 0` with
       `S ⊆ Metric.closedBall 0 R` via `Bornology.IsBounded.subset_closedBall_lt`.
    2. Build the nearest-point retraction `r : E → ↥S` from
       `exists_continuous_proj_convex` (LOOKUP-2 helper, S11.B; landed
       in S14).
    3. Compose `F : ↥(closedBall 0 R) → ↥(closedBall 0 R)` via
       `b ↦ ⟨f (r b), …⟩`, well-defined since `f (r b) ∈ ↥S ⊆ closedBall 0 R`;
       continuity from `continuous_subtype_val`/`Continuous.subtype_mk`.
    4. Rescale closed balls *elementwise* (Option b: no `Homeomorph` needed):
       `σ x := R • x` carries `closedBall 0 1` to `closedBall 0 R`, with
       inverse `τ b := R⁻¹ • b`; both are continuous via
       `continuous_const_smul`. Apply `brouwer_unit_ball` to
       `G := τ ∘ F ∘ σ` to get `y` with `G y = y`. Multiplying by `R`
       and using `mul_inv_cancel₀ + one_smul` yields the coordinate
       identity `(F (σ y) : E) = (σ y : E)`.
    5. (S12 refinement.) Lift `σ y` from `↥(closedBall 0 R)` to `↥S` by
       observing `(σ y : E) = (F (σ y) : E) = (f (r (σ y : E)) : E) ∈ S`,
       then invoking the helper's idempotency clause to identify
       `r (σ y : E) = ⟨(σ y : E), …⟩` in `↥S`. The `↥S` candidate
       fixed point is `r (σ y : E)`; the equation `f (r (σ y : E)) =
       r (σ y : E)` follows from the coord chain
       `(F (σ y) : E) = (σ y : E) = (r (σ y : E) : E)` and `Subtype.ext`. -/
theorem brouwer_fpt {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (f : ↥S → ↥S) (hf : Continuous f) :
    ∃ x : ↥S, f x = x := by
  -- S11.A.body (researcher-10, S13, 2026-05-09): retraction reduction body
  -- per s11-strict-weakening-spec.md + s12-s11a-body-step6-refinement.md.
  -- Step 1: bound S by closedBall 0 R for some R > 0 (LOOKUP-1, S9-confirmed).
  have hS_bounded : Bornology.IsBounded S := hS_compact.isBounded
  obtain ⟨R, hR_pos, hSR⟩ :=
    hS_bounded.subset_closedBall_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  have hR_ne : R ≠ 0 := hR_pos.ne'
  have hRinv_pos : 0 < R⁻¹ := inv_pos.mpr hR_pos
  -- Step 2: continuous nearest-point retraction r : E → ↥S (LOOKUP-2 helper, S11.B).
  obtain ⟨r, hr_cont, hr_id⟩ :=
    exists_continuous_proj_convex S hS_ne hS_compact hS_convex
  -- Step 3: F : ↥(closedBall 0 R) → ↥(closedBall 0 R), b ↦ ⟨f (r b), _⟩.
  have hF_coord_cont :
      Continuous fun b : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) =>
        (f (r ((b : EuclideanSpace ℝ (Fin n)))) : EuclideanSpace ℝ (Fin n)) :=
    continuous_subtype_val.comp
      (hf.comp (hr_cont.comp continuous_subtype_val))
  have hF_in_B : ∀ b : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R),
      (f (r ((b : EuclideanSpace ℝ (Fin n)))) : EuclideanSpace ℝ (Fin n))
        ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R :=
    fun b => hSR (f (r ((b : EuclideanSpace ℝ (Fin n))))).property
  let F : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) →
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :=
    fun b => ⟨(f (r ((b : EuclideanSpace ℝ (Fin n)))) : EuclideanSpace ℝ (Fin n)),
              hF_in_B b⟩
  have hF_cont : Continuous F := hF_coord_cont.subtype_mk hF_in_B
  -- Step 4: rescale closedBall 0 R ↔ closedBall 0 1 elementwise (Option b).
  -- σ : ↥(closedBall 0 1) → ↥(closedBall 0 R), x ↦ R • x.
  have hσ_in_B : ∀ x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1),
      R • ((x : EuclideanSpace ℝ (Fin n)))
        ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    intro x
    rw [mem_closedBall_zero_iff, norm_smul,
        Real.norm_of_nonneg hR_pos.le]
    have hx_le : ‖(x : EuclideanSpace ℝ (Fin n))‖ ≤ 1 := by
      have hx := x.property
      rwa [mem_closedBall_zero_iff] at hx
    calc R * ‖(x : EuclideanSpace ℝ (Fin n))‖
        ≤ R * 1 := mul_le_mul_of_nonneg_left hx_le hR_pos.le
      _ = R := by ring
  let σ : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) →
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :=
    fun x => ⟨R • (x : EuclideanSpace ℝ (Fin n)), hσ_in_B x⟩
  have hσ_cont : Continuous σ :=
    ((continuous_const_smul R).comp continuous_subtype_val).subtype_mk hσ_in_B
  -- τ : ↥(closedBall 0 R) → ↥(closedBall 0 1), b ↦ R⁻¹ • b.
  have hτ_in_U : ∀ b : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R),
      R⁻¹ • ((b : EuclideanSpace ℝ (Fin n)))
        ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
    intro b
    rw [mem_closedBall_zero_iff, norm_smul,
        Real.norm_of_nonneg hRinv_pos.le]
    have hb_le : ‖(b : EuclideanSpace ℝ (Fin n))‖ ≤ R := by
      have hb := b.property
      rwa [mem_closedBall_zero_iff] at hb
    calc R⁻¹ * ‖(b : EuclideanSpace ℝ (Fin n))‖
        ≤ R⁻¹ * R := mul_le_mul_of_nonneg_left hb_le hRinv_pos.le
      _ = 1 := inv_mul_cancel₀ hR_ne
  let τ : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) →
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    fun b => ⟨R⁻¹ • (b : EuclideanSpace ℝ (Fin n)), hτ_in_U b⟩
  have hτ_cont : Continuous τ :=
    ((continuous_const_smul R⁻¹).comp continuous_subtype_val).subtype_mk hτ_in_U
  -- G := τ ∘ F ∘ σ : ↥(closedBall 0 1) → ↥(closedBall 0 1).
  let G : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) →
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := τ ∘ F ∘ σ
  have hG_cont : Continuous G := hτ_cont.comp (hF_cont.comp hσ_cont)
  -- Apply the unit-ball axiom.
  obtain ⟨y, hy⟩ := brouwer_unit_ball G hG_cont
  -- Step 5: extract (F (σ y) : E) = (σ y : E) from G y = y.
  -- hy : G y = y, so (G y : E) = (y : E), and (G y : E) = R⁻¹ • (F (σ y) : E).
  have hτFσy_coord :
      R⁻¹ • ((F (σ y) :
          ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n)) =
      ((y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
          EuclideanSpace ℝ (Fin n)) :=
    congrArg Subtype.val hy
  -- Multiply by R: (F (σ y) : E) = R • (y : E) = (σ y : E).
  have hFσy_eq_σy :
      ((F (σ y) :
          ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n)) =
      ((σ y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n)) := by
    have step1 : R • R⁻¹ •
        ((F (σ y) :
            ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
              EuclideanSpace ℝ (Fin n)) =
        R • ((y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
              EuclideanSpace ℝ (Fin n)) := by
      rw [hτFσy_coord]
    rw [smul_smul, mul_inv_cancel₀ hR_ne, one_smul] at step1
    -- step1 : (F (σ y) : E) = R • (y : E); (σ y : E) = R • (y : E) by `let σ`.
    exact step1
  -- Step 6: lift `σ y` from ↥B to ↥S, then derive the ↥S fixed point.
  -- (σ y : E) ∈ S because (σ y : E) = (F (σ y) : E) = (f (r (σ y : E)) : E),
  -- and f's codomain is ↥S.
  have hσy_in_S :
      ((σ y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n)) ∈ S := by
    rw [← hFσy_eq_σy]
    show (f (r (((σ y :
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n)))) : EuclideanSpace ℝ (Fin n)) ∈ S
    exact (f (r (((σ y :
        ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
            EuclideanSpace ℝ (Fin n))))).property
  -- Lift σ y to ↥S and use idempotency r ((x : E)) = x for x : ↥S.
  let x' : ↥S :=
    ⟨((σ y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
          EuclideanSpace ℝ (Fin n)), hσy_in_S⟩
  have hx'_coord : ((x' : ↥S) : EuclideanSpace ℝ (Fin n)) =
      ((σ y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
          EuclideanSpace ℝ (Fin n)) := rfl
  have hr_x' : r ((x' : EuclideanSpace ℝ (Fin n))) = x' := hr_id x'
  have hr_σy : r (((σ y :
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
        EuclideanSpace ℝ (Fin n))) = x' := by
    rw [← hx'_coord]; exact hr_x'
  -- Candidate fixed point: r (σ y : E) ∈ ↥S.
  refine ⟨r (((σ y :
      ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
        EuclideanSpace ℝ (Fin n))), ?_⟩
  -- Reduce to coord equality, then chain through hFσy_eq_σy + hr_σy + hx'_coord.
  apply Subtype.ext
  -- Goal: (f (r (σ y : E)) : E) = (r (σ y : E) : E)
  -- LHS = (F (σ y) : E) by `let F`-unfolding; = (σ y : E) by hFσy_eq_σy.
  -- RHS = (x' : E) via hr_σy; = (σ y : E) by hx'_coord.
  calc (f (r (((σ y :
              ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
                EuclideanSpace ℝ (Fin n)))) : EuclideanSpace ℝ (Fin n))
      = ((F (σ y) : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
              EuclideanSpace ℝ (Fin n)) := rfl
    _ = ((σ y : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
              EuclideanSpace ℝ (Fin n)) := hFσy_eq_σy
    _ = ((x' : ↥S) : EuclideanSpace ℝ (Fin n)) := hx'_coord.symm
    _ = (r (((σ y :
              ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :
                EuclideanSpace ℝ (Fin n))) : EuclideanSpace ℝ (Fin n)) := by
              rw [hr_σy]

/-- A continuous `f : S → S` is an ε-graph-approximate selection of `F`
    if for every `x` there is a nearby point `x'` (within `ε`) and a point
    `y ∈ F(x')` with `dist (f x) y < ε` — i.e. the graph of `f` lies inside
    the `ε`-fattening of the graph of `F`.

    This is the Cellina–Browder form of approximate selection: it is the
    strongest form provable for upper-hemicontinuous maps with nonempty
    convex values (S6 analysis: the strictly stronger pointwise form
    `∀ x, ∃ y ∈ F x, dist (f x) y < ε` is FALSE under USC + convex values
    alone — a 1-D counterexample with `F(0) = [0,1]`, `F(t>0) = {0}`,
    `F(t<0) = {1}` admits no continuous pointwise (1/3)-selection by
    continuity at `0`). -/
def IsGraphApproxSelection {X : Type*} [PseudoMetricSpace X]
    (F : SetValuedMap X X) (f : X → X) (ε : ℝ) : Prop :=
  ∀ x, ∃ x' y, dist x x' < ε ∧ y ∈ F x' ∧ dist (f x) y < ε

/-- **Axiom 2: Cellina–Browder Graph-Approximate Continuous Selections**

    For a compact convex `S`, an UHC map `F : S → 2^S` with nonempty
    convex values, and any `ε > 0`, there exists a continuous
    `f : S → S` whose graph lies in the `ε`-fattening of `graph(F)`.

    **Why the graph form (not the pointwise form):** S6 mathematical
    analysis (`s6-axiom-counterexample.md`) shows the pointwise form
    `IsApproxSelection F f ε` is FALSE under USC + convex values alone.
    The graph form is the standard Cellina–Browder selection theorem
    (Cellina 1969; Browder 1968; Aubin–Frankowska, *Set-Valued Analysis*
    §9.2) and suffices to derive Kakutani's theorem (see
    `kakutani_from_brouwer` below; the helper passes a `2ε`-bound
    through `approx_fixedpoint_implies_fixedpoint`).

    **Proof sketch (PartitionOfUnity construction):**
    1. For each `x ∈ S`, pick `y_x ∈ F(x)` and use UHC to choose an open
       `U_x ∋ x` with `F(U_x) ⊆ ε`-thickening of `F(x)`.
    2. Compactness extracts a finite subcover `U_{x_1}, …, U_{x_k}`.
    3. Subordinate partition of unity `{φ_i}` with `supp φ_i ⊆ U_{x_i}`.
    4. Define `f(x) := Σ φ_i(x) · y_{x_i}`. Convexity of `S` gives `f x ∈ S`.
    5. Graph bound: at any `x`, pick `i` with `φ_i(x) > 0`; then
       `x ∈ U_{x_i}` and `(x_i, y_{x_i})` lies in the graph of `F`,
       certifying graph-distance `< ε`. (The pointwise form would require
       step 5 to bound `dist(f(x), F(x))` directly, which fails — see S6.)

    Formalizing this in Lean requires `Mathlib.Topology.PartitionOfUnity`
    plus the Cellina averaging argument; it is a standard but non-trivial
    Mathlib-level task and is not yet in scope here. -/
axiom approx_selection_exists {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_convex : ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : ↥S → ↥S, Continuous f ∧ IsGraphApproxSelection F (fun x => (f x : ↥S)) ε

/-- **S18a helper for `approx_selection_exists` axiom elimination
    (Step 4: convex combinations weighted by a partition of unity stay
    in the convex set):**

    For a convex set `K ⊆ E` in any real vector space `E` and a partition
    of unity `ρ : PartitionOfUnity ι X s` on a topological space `X`, the
    weighted sum `∑ i ∈ ρ.finsupport x₀, ρ i x₀ • y i` of points
    `y i ∈ K` (for every `i` in the local finite support at `x₀`)
    lies in `K`, provided `x₀ ∈ s`.

    The lemma packages three facts:
    * `PartitionOfUnity.nonneg` — each partition value is `≥ 0`;
    * `PartitionOfUnity.sum_finsupport` — the values sum to `1` at every
      `x₀ ∈ s`;
    * `Convex.sum_mem` — finite convex combinations of points in a convex
      set stay in the set.
    These three are exactly the hypotheses `Convex.sum_mem` requires from
    a partition of unity, in a single call.

    **Use site (S18e+).** Step 4 of the Cellina–Browder PartitionOfUnity
    proof of `axiom approx_selection_exists` (line 465 above) defines the
    candidate continuous selection
    `f x := ∑ i ∈ ρ.finsupport x, ρ i x • y_{x_i}` where the `y_{x_i}`
    are chosen at the subcover centers from Steps 1–2 (S17 survey, Steps
    1–2). This lemma certifies `f x ∈ S` at every `x ∈ ↥S` (taking
    `X = ↥S`, `E = EuclideanSpace ℝ (Fin n)`, `K = S` for the ambient
    convex set, and using the axiom's `hS_convex` hypothesis).

    The statement is intentionally generic in the index, base, and target
    types (no `Fin n`-specific or `↥S`-specific assumptions) so it can be
    reused beyond the immediate Schauder-FP context if the in-file
    Cellina–Browder construction is later upstreamed.

    Reference: S17 Mathlib API survey
    (`research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/s17-cellina-mathlib-api-survey.md`),
    Step 4 (`PartitionOfUnity` API row). -/
private lemma convex_combination_of_partition_in_S
    {ι X E : Type*} [TopologicalSpace X]
    [AddCommGroup E] [Module ℝ E]
    {s : Set X} {K : Set E}
    (ρ : PartitionOfUnity ι X s) (hK : Convex ℝ K)
    {x₀ : X} (hx₀ : x₀ ∈ s)
    {y : ι → E} (hy : ∀ i ∈ ρ.finsupport x₀, y i ∈ K) :
    (∑ i ∈ ρ.finsupport x₀, ρ i x₀ • y i) ∈ K :=
  hK.sum_mem (fun i _ => ρ.nonneg i x₀) (ρ.sum_finsupport hx₀) hy

/-- **S18b scaffold (typeclass instance plumbing for `approx_selection_exists_proof`):**

    The Cellina–Browder construction (S17 survey, S18a–f decomposition) for
    a compact convex `S ⊆ EuclideanSpace ℝ (Fin n)` requires four typeclass
    instances on `↥S`:

    1. `CompactSpace ↥S` — constructed from the `IsCompact S` hypothesis via
       `isCompact_iff_compactSpace.mp` (`Mathlib/Topology/Compactness/Compact.lean`
       line 989 at pinned rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
    2. `T2Space ↥S` — inherited automatically from the ambient
       `EuclideanSpace ℝ (Fin n)` (which is `T2` via its metric structure)
       through the subtype instance `Subtype.t2Space`
       (`Mathlib/Topology/Separation/Hausdorff.lean` line 351).
    3. `NormalSpace ↥S` — derived from `CompactSpace + R1Space` via
       `NormalSpace.of_compactSpace_r1Space`
       (`Mathlib/Topology/Separation/Regular.lean` line 489). The required
       `R1Space ↥S` is itself an automatic consequence of `T2Space ↥S` via
       `T2Space.r1Space` (`.../Hausdorff.lean` line 120).
    4. `ParacompactSpace ↥S` — derived from `CompactSpace ↥S` alone via
       `paracompact_of_compact`
       (`Mathlib/Topology/Compactness/Paracompact.lean` line 180).

    Only (1) requires explicit construction; (2)–(4) are obtained by
    typeclass inference once (1) is in scope. This lemma confirms the
    four-fold derivation typechecks at the pinned rev and isolates the
    single `haveI` step that materializes (1). The S18c–f Cellina–Browder
    construction will reproduce this `haveI` line inside the eventual
    `theorem approx_selection_exists_proof` so that every Mathlib
    partition-of-unity, normal-space-Urysohn, and locally-finite-cover
    lemma has its typeclass prerequisites available without further
    setup.

    No new axiom is introduced; `axiom approx_selection_exists` (Axiom 2
    above) remains in the file unchanged. -/
private lemma typeclass_witnesses_compact_subset {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS_compact : IsCompact S) :
    CompactSpace ↥S ∧ T2Space ↥S ∧ NormalSpace ↥S ∧ ParacompactSpace ↥S := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  -- T2Space ↥S    : inferred from Subtype.t2Space (ambient EuclideanSpace is T2).
  -- NormalSpace ↥S: inferred from CompactSpace + (R1Space ← T2Space).
  -- ParacompactSpace ↥S: inferred from CompactSpace (paracompact_of_compact).
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- **S18c scaffold (Cellina–Browder Steps 1–2 packaged together):**

    For an upper-hemicontinuous set-valued map `F : ↥S → 2^↥S` on a
    compact `S ⊆ EuclideanSpace ℝ (Fin n)` and any `ε > 0`, produce:

    * a function `U : ↥S → Set ↥S` of subtype-relative open
      neighborhoods (one per base point), each contained in the inverse
      image (in the UHC sense) of the `ε`-thickening of `F(x)`;
    * a finite `s : Finset ↥S` of cover centers whose open
      neighborhoods exhaust all of `↥S`.

    The construction chains `uhc_local_thickening` (S17 scaffold, PR
    #17708) pointwise over `↥S`, then invokes
    `CompactSpace.elim_nhds_subcover` once `[CompactSpace ↥S]` is
    materialised from `hS_compact` (the same `haveI` line as in
    `typeclass_witnesses_compact_subset`, S18b PR #17802). The
    quantifier-signature gating question on `IsUpperHemicontinuous` was
    resolved doc-only in PR #17800: `uhc_local_thickening` applies
    directly at `Y = ↥S` with no preimage pull-back step.

    No new axiom is introduced; `axiom approx_selection_exists` (Axiom
    2 above) remains in the file unchanged. The full ↥S-indexed family
    `U` is returned alongside the finite cover `s` so that the
    downstream S18d invocation of
    `PartitionOfUnity.exists_isSubordinate` (subordinate partition of
    unity, Cellina Step 3) can choose either the full family `U` or
    the finite subfamily `{U x : x ∈ s}` as its index set.

    Reference: S17 Mathlib API survey
    (`research/problems/schauder-fixed-point-oq-03-oq-01-incomplete-01/s17-cellina-mathlib-api-survey.md`),
    Steps 1–2; S17-followup quantifier resolution PR #17800. -/
private lemma exists_finite_subcover_for_uhc {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS_compact : IsCompact S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : ↥S → Set ↥S, ∃ s : Finset ↥S,
      (∀ x : ↥S, IsOpen (U x)) ∧
      (∀ x : ↥S, x ∈ U x) ∧
      (∀ x : ↥S, U x ⊆ Metric.ball x ε) ∧
      (∀ x z : ↥S, z ∈ U x → F z ⊆ Metric.thickening ε (F x)) ∧
      (⋃ x ∈ s, U x = (⊤ : Set ↥S)) := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  -- Step 1: pointwise local thickening from UHC with the S18f input-ball
  -- diameter bound `U x ⊆ ball x ε` (replaces the S17 `uhc_local_thickening`,
  -- which lacked the input-side clause needed for the `dist x x' < ε` half of
  -- the eventual `IsGraphApproxSelection` graph bound).
  choose U hU_open hU_mem hU_ball hU_sub using
    fun x : ↥S => uhc_local_thickening_with_input_diameter hF_uhc x ε hε
  -- Step 2: compactness extracts a finite subcover (CompactSpace API).
  obtain ⟨s, hs⟩ :=
    CompactSpace.elim_nhds_subcover U fun x => (hU_open x).mem_nhds (hU_mem x)
  exact ⟨U, s, hU_open, hU_mem, hU_ball, hU_sub, hs⟩

/-- **S18d scaffold (Cellina–Browder Step 3, subordinate partition of unity):**

    Given an upper-hemicontinuous set-valued map `F : ↥S → 2^↥S` on a
    compact `S ⊆ EuclideanSpace ℝ (Fin n)` and any `ε > 0`, package the
    S18c open cover `U : ↥S → Set ↥S` together with a *partition of unity
    subordinate to it*. The subordinate partition `ρ : PartitionOfUnity
    (↥S) (↥S) Set.univ` is the centerpiece of the Cellina–Browder
    construction: in S18e the continuous selection
    `f x := ∑ᶠ i, ρ i x • y_i` (with `y_i ∈ F i`) inherits its
    continuity from `ρ`'s smoothness and its `ε`-graph-approximation
    property from `ρ.IsSubordinate U` plus S18c's
    `F z ⊆ Metric.thickening ε (F x)` clause.

    The proof chains `exists_finite_subcover_for_uhc` (S18c, PR #17910)
    to obtain the open family `U`, derives the universal cover hypothesis
    `Set.univ ⊆ ⋃ x : ↥S, U x` from the basepoint condition `x ∈ U x`,
    and feeds the resulting open cover to
    `PartitionOfUnity.exists_isSubordinate`
    (`Mathlib.Topology.PartitionOfUnity` line 629 at pinned rev
    `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). The required
    `[NormalSpace ↥S]` and `[ParacompactSpace ↥S]` instances are
    supplied automatically by the `haveI : CompactSpace ↥S` line plus
    Mathlib's typeclass derivation chain documented in
    `typeclass_witnesses_compact_subset` (S18b, PR #17802). The closed
    target set is taken to be `Set.univ`, with `IsClosed Set.univ`
    discharged by `isClosed_univ`.

    The full ↥S-indexed family `U` is retained (rather than restricted
    to the finite subcover `s` of S18c) so that the partition of unity
    is indexed over `↥S` itself; the `ρ`'s local-finiteness clause
    inherited from `BumpCovering.exists_isSubordinate` ensures only
    finitely many `ρ i x` are nonzero at any point, recovering the
    finite-sum behavior needed for S18e's continuous selection.

    No new axiom is introduced; `axiom approx_selection_exists` (Axiom 2
    above) remains in the file unchanged. -/
private lemma exists_partition_subordinate_to_uhc_cover {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS_compact : IsCompact S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : ↥S → Set ↥S,
      ∃ ρ : PartitionOfUnity (↥S) (↥S) (Set.univ : Set ↥S),
        (∀ x : ↥S, IsOpen (U x)) ∧
        (∀ x : ↥S, x ∈ U x) ∧
        (∀ x : ↥S, U x ⊆ Metric.ball x ε) ∧
        (∀ x z : ↥S, z ∈ U x → F z ⊆ Metric.thickening ε (F x)) ∧
        ρ.IsSubordinate U := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  obtain ⟨U, _s, hU_open, hU_mem, hU_ball, hU_sub, _hs_cover⟩ :=
    exists_finite_subcover_for_uhc S hS_compact F hF_uhc ε hε
  have hU_cover : (Set.univ : Set ↥S) ⊆ ⋃ x : ↥S, U x := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x, hU_mem x⟩
  obtain ⟨ρ, hρ_sub⟩ :=
    PartitionOfUnity.exists_isSubordinate (s := (Set.univ : Set ↥S))
      isClosed_univ U hU_open hU_cover
  exact ⟨U, ρ, hU_open, hU_mem, hU_ball, hU_sub, hρ_sub⟩

/-- **S18e scaffold (Cellina–Browder Step 4, continuous selection from
    subordinate partition of unity):**

    Given a compact convex `S ⊆ EuclideanSpace ℝ (Fin n)` and an
    upper-hemicontinuous set-valued map `F : ↥S → 2^↥S` with nonempty
    values, package the candidate continuous selection of Step 4 of the
    Cellina–Browder construction together with all witness data needed
    by the eventual S18f graph-bound proof.

    Concretely, for any `ε > 0`, this lemma produces a continuous map
    `f : C(↥S, ↥S)` together with the four S18d outputs
    (`U`, `ρ`, the three open-cover/subordinate-partition clauses) and a
    pointwise selector `ysel : ↥S → ↥S` with `ysel x ∈ F x`. The
    final clause certifies the explicit formula
    `(f x : EuclideanSpace ℝ (Fin n)) = ∑ᶠ i, ρ i x • (ysel i)` so the
    S18f graph-bound argument can compute `dist (f x) (ysel i)` at any
    `i ∈ ρ.finsupport x` directly from this representation.

    **Proof structure** (mirrors Cellina–Browder Step 4):
    1. `choose ysel hysel_in_F using hF_ne` selects one `ysel x ∈ F x`
       per `x : ↥S` (axiom of choice; the selector need not be
       continuous — continuity comes from averaging via `ρ`).
    2. `exists_partition_subordinate_to_uhc_cover` (S18d, PR #17993)
       supplies the open cover `U : ↥S → Set ↥S` and the subordinate
       partition `ρ : PartitionOfUnity (↥S) (↥S) Set.univ`.
    3. The candidate selection in `EuclideanSpace ℝ (Fin n)` is
       `f0 x := ∑ᶠ i, ρ i x • (ysel i : EuclideanSpace ℝ (Fin n))`.
       Continuity of `f0` is `ρ.IsSubordinate.continuous_finsum_smul`
       (`Mathlib.Topology.PartitionOfUnity` line 313 at pinned rev
       `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`) applied to the
       constant-in-`x` family `g i _ := (ysel i : EuclideanSpace ℝ (Fin n))`,
       which is `continuousOn_const` on every `U i`.
    4. Membership `f0 x ∈ S` follows from
       `convex_combination_of_partition_in_S` (S18a, PR #17755) at
       `K = S`, using `(ysel i).property : (ysel i : ...) ∈ S` for the
       point-in-K hypothesis and `ρ.sum_finsupport_smul_eq_finsum`
       (`PartitionOfUnity.lean` line 212 at pinned rev) to bridge the
       finsum form to the `Finset`-sum form expected by the helper.
    5. Lift `f0` to `f : C(↥S, ↥S)` via
       `Continuous.subtype_mk` (the membership witnesses `f0 x ∈ S`
       come from the previous step).

    The full witness bundle (including `ysel`, `ρ`, the cover `U`, and
    the explicit formula) is intentionally exposed in the result type
    so that the eventual S18f graph-bound proof can extract any `i ∈
    ρ.finsupport x` (with `ρ i x > 0`), conclude `x ∈ U i` from the
    `tsupport ⊆ U i` clause of `hρ_sub`, then invoke S18d's
    `F z ⊆ Metric.thickening ε (F i)` clause at `z = x` to bound
    `dist (f x) (ysel i)` via `ysel i ∈ F i ⊆ ε`-thickening of `F x`.

    No new axiom is introduced; `axiom approx_selection_exists` (Axiom
    2 above) remains in the file unchanged. The remaining work to
    fully discharge the axiom is the S18f graph-bound proof, which
    consumes the witnesses produced here. -/
private lemma exists_continuous_selection_with_witnesses {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty) (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ f : C(↥S, ↥S),
      ∃ U : ↥S → Set ↥S,
      ∃ ρ : PartitionOfUnity (↥S) (↥S) (Set.univ : Set ↥S),
      ∃ ysel : ↥S → ↥S,
        (∀ x : ↥S, IsOpen (U x)) ∧
        (∀ x : ↥S, x ∈ U x) ∧
        (∀ x : ↥S, U x ⊆ Metric.ball x ε) ∧
        (∀ x z : ↥S, z ∈ U x → F z ⊆ Metric.thickening ε (F x)) ∧
        ρ.IsSubordinate U ∧
        (∀ x, ysel x ∈ F x) ∧
        (∀ x : ↥S, (f x : EuclideanSpace ℝ (Fin n))
            = ∑ᶠ i, ρ i x • (ysel i : EuclideanSpace ℝ (Fin n))) := by
  -- Step 4a: pointwise selector ysel : ↥S → ↥S with ysel x ∈ F x.
  choose ysel hysel_in_F using hF_ne
  -- Step 4b: open cover U (with the S18f input-ball clause) and subordinate
  -- partition ρ from S18d.
  obtain ⟨U, ρ, hU_open, hU_mem, hU_ball, hU_sub, hρ_sub⟩ :=
    exists_partition_subordinate_to_uhc_cover S hS_compact F hF_uhc ε hε
  -- Step 4c: candidate selection in EuclideanSpace ℝ (Fin n) and its continuity.
  let f0 : ↥S → EuclideanSpace ℝ (Fin n) :=
    fun x => ∑ᶠ i, ρ i x • (ysel i : EuclideanSpace ℝ (Fin n))
  have hf0_cont : Continuous f0 :=
    hρ_sub.continuous_finsum_smul (g := fun i _ => (ysel i : EuclideanSpace ℝ (Fin n)))
      hU_open (fun _ => continuousOn_const)
  -- Step 4d: f0 x ∈ S via convex combination of partition values (S18a helper).
  have hf0_in_S : ∀ x : ↥S, f0 x ∈ S := by
    intro x
    have hysel_in_S :
        ∀ i ∈ ρ.finsupport x, (ysel i : EuclideanSpace ℝ (Fin n)) ∈ S :=
      fun i _ => (ysel i).property
    have hsum_mem :
        (∑ i ∈ ρ.finsupport x, ρ i x • (ysel i : EuclideanSpace ℝ (Fin n))) ∈ S :=
      convex_combination_of_partition_in_S ρ hS_convex (Set.mem_univ x) hysel_in_S
    have hsum_eq :
        (∑ i ∈ ρ.finsupport x, ρ i x • (ysel i : EuclideanSpace ℝ (Fin n)))
        = ∑ᶠ i, ρ i x • (ysel i : EuclideanSpace ℝ (Fin n)) :=
      ρ.sum_finsupport_smul_eq_finsum
        (fun (i : ↥S) (_ : ↥S) => (ysel i : EuclideanSpace ℝ (Fin n)))
    show (∑ᶠ i, ρ i x • (ysel i : EuclideanSpace ℝ (Fin n))) ∈ S
    rw [← hsum_eq]; exact hsum_mem
  -- Step 4e: lift f0 to f : C(↥S, ↥S).
  refine ⟨⟨fun x => ⟨f0 x, hf0_in_S x⟩, hf0_cont.subtype_mk hf0_in_S⟩,
          U, ρ, ysel, hU_open, hU_mem, hU_ball, hU_sub, hρ_sub, hysel_in_F, ?_⟩
  intro _
  rfl

/-- **S23 step (input-side graph-distance bound, `dist x x' < ε` half):**

    Given the open cover `U` carrying the S18f input-ball clause
    `U x ⊆ Metric.ball x ε` (now propagated through the S18c→S18d→S18e
    bundle) and a partition of unity `ρ` subordinate to it, every center
    `i` in the local finite support `ρ.finsupport x` lies within `ε` of `x`
    (in the subtype metric of `↥S`).

    This discharges the first of the three conjuncts of
    `IsGraphApproxSelection F f ε` (`dist x x' < ε`, line 532 above) with
    the witness `x' := i`: the eventual `approx_selection_exists_proof`
    picks any `i ∈ ρ.finsupport x` (nonempty because `ρ` sums to `1` at
    `x ∈ Set.univ`), supplies `y := ysel i ∈ F i` for the second conjunct,
    and is left with only the harder output-side bound
    `dist (f x) (ysel i) < ε` for the third.

    **Proof.** `i ∈ ρ.finsupport x` unfolds (`PartitionOfUnity.mem_finsupport`)
    to `ρ i x ≠ 0`, i.e. `x ∈ Function.support (ρ i)`. Then
    `subset_tsupport` gives `x ∈ tsupport (ρ i)`, `ρ.IsSubordinate U` gives
    `x ∈ U i`, and the input-ball clause `U i ⊆ Metric.ball i ε` gives
    `x ∈ Metric.ball i ε`, i.e. `dist x i < ε`.

    The statement takes `U`, `ρ` and their clauses as explicit hypotheses
    (rather than the full S18e bundle) so it is reusable from any cover
    satisfying the input-ball and subordinate-partition conditions.

    No new axiom is introduced; `axiom approx_selection_exists` (Axiom 2
    above) remains in the file unchanged. The output-side bound
    `dist (f x) (ysel i) < ε` is **not** discharged here: the existing
    thickening clause runs the wrong way (`x ∈ U i` gives
    `F x ⊆ thickening ε (F i)`, controlling `F x`, not the selected values
    `ysel j ∈ F j` for the other `j ∈ ρ.finsupport x`), so that half needs
    a uniform refinement and is left to a subsequent iteration. -/
private lemma finsupport_center_within_input_ball {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ)
    (U : ↥S → Set ↥S) (hU_ball : ∀ x : ↥S, U x ⊆ Metric.ball x ε)
    (ρ : PartitionOfUnity (↥S) (↥S) (Set.univ : Set ↥S))
    (hρ_sub : ρ.IsSubordinate U)
    {x i : ↥S} (hi : i ∈ ρ.finsupport x) :
    dist x i < ε := by
  have hne : ρ i x ≠ 0 := by
    have h := (ρ.mem_finsupport x).mp hi
    simpa using h
  have hx_tsupp : x ∈ tsupport (ρ i) :=
    subset_tsupport (ρ i) (Function.mem_support.mpr hne)
  exact Metric.mem_ball.mp (hU_ball i (hρ_sub i hx_tsupp))

/-- **S23 step (local finite support is nonempty):**

    For a partition of unity `ρ` on `↥S` over `Set.univ`, the local finite
    support `ρ.finsupport x` is nonempty at every `x : ↥S`.

    This supplies the center-existence step the eventual
    `approx_selection_exists_proof` needs: to discharge
    `IsGraphApproxSelection F f ε` at a point `x` the construction must pick
    some `i ∈ ρ.finsupport x` to serve as the witness `x'` (via
    `finsupport_center_within_input_ball` for the `dist x x' < ε` conjunct
    and `ysel i ∈ F i` for the membership conjunct). That choice is only
    possible because the support is nonempty.

    **Proof.** If `ρ.finsupport x` were empty, the partition-of-unity sum
    `∑ i ∈ ρ.finsupport x, ρ i x` would be the empty sum `0`; but
    `PartitionOfUnity.sum_finsupport` (using `x ∈ Set.univ`) forces that sum
    to equal `1`, contradicting `0 ≠ 1`.

    No new axiom is introduced; `axiom approx_selection_exists` (Axiom 2
    above) remains in the file unchanged. -/
private lemma finsupport_nonempty {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (ρ : PartitionOfUnity (↥S) (↥S) (Set.univ : Set ↥S))
    (x : ↥S) :
    (ρ.finsupport x).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  have hsum : ∑ i ∈ ρ.finsupport x, ρ i x = 1 := ρ.sum_finsupport (Set.mem_univ x)
  rw [hempty, Finset.sum_empty] at hsum
  exact one_ne_zero hsum.symm

/-- **S19 scaffold (closed-image helper for the ambient-space projection):**

    Given a Hausdorff ambient space `α`, a compact subset `S ⊆ α`, and a
    set `T ⊆ ↥S` closed in the subtype topology, the image
    `Subtype.val '' T` is closed in `α`. This is the load-bearing
    closed-image step required by the §4.b Hilbert projection chain of
    the eventual `theorem approx_selection_exists_proof`: in that
    construction, the Hilbert projection theorem
    `exists_norm_eq_iInf_of_complete_convex`
    (`Mathlib.Analysis.InnerProductSpace.Projection`, S14-used at line
    226 above) requires the target set to be closed in the *ambient*
    inner-product space `EuclideanSpace ℝ (Fin n)`, while the axiom
    hypothesis `hF_closed : ∀ x, IsClosed (F x)` (S19a signature update;
    matches the existing `kakutani_from_brouwer` caller's hypothesis at
    line 1030) provides closedness of `F x` only in the *subtype*
    `↥S`. This helper bridges the two via `Continuous.isClosedMap`
    (`Mathlib/Topology/Separation/Hausdorff.lean:664` at pinned rev
    `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`): a continuous map from a
    compact space to a Hausdorff space is closed, so `Subtype.val :
    ↥S → α` carries closed sets to closed sets once `↥S` is endowed
    with `CompactSpace` via `isCompact_iff_compactSpace.mp hS_compact`
    (same construction line used by S18b/S18d/S18e at
    `SchauderFixedPointOQ03OQ01.lean:641,744,829`).

    The lemma is **generic** in the ambient `α` (only `TopologicalSpace`
    and `T2Space` typeclasses; no `EuclideanSpace`-specific or
    `Fin n`-specific assumptions) so it is directly reusable beyond the
    immediate Schauder-FP context.

    **Use site (S19+):** the §4.b nearest-point projection in
    `approx_selection_exists_proof` calls this helper with
    `α := EuclideanSpace ℝ (Fin n)` (whose `T2Space` instance is
    automatic from its metric structure, exactly as audited by
    `typeclass_witnesses_compact_subset` (S18b, PR #17802)) and
    `T := F i` (closed in `↥S` via the new `hF_closed` hypothesis) to
    obtain `IsClosed (Subtype.val '' F i)` — the missing precondition
    for `exists_norm_eq_iInf_of_complete_convex`.

    Reference: S19a PREP `2026-05-12-s19a-prep-closed-image-and-signature-alignment.md`
    §3.a Path A draft; S19b PREP `2026-05-13-s19b-prep-mathlib-api-audit-closed-image-and-projection.md`
    confirmed bearer file/line; S19d PREP `2026-05-13-s19d-prep-path-a-bearer-audit-cleared.md`
    §3 provides the verbatim Path A drop-in used here (4-LOC body, no
    new imports beyond the existing `Mathlib.Topology.MetricSpace.Basic`
    transitive closure).

    No new axiom is introduced; `axiom approx_selection_exists` (Axiom 2
    above) remains in the file unchanged. -/
private lemma image_subtype_isClosed_of_isClosed_of_compact
    {α : Type*} [TopologicalSpace α] [T2Space α]
    {S : Set α} (hS_compact : IsCompact S)
    {T : Set ↥S} (hT_closed : IsClosed T) :
    IsClosed ((Subtype.val '' T : Set α)) := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  exact continuous_subtype_val.isClosedMap T hT_closed

/-- **S19 step (b) helper (nearest-point in the ambient image of `F i`):**

    For a compact `S ⊆ EuclideanSpace ℝ (Fin n)`, a set-valued map
    `F : SetValuedMap (↥S) (↥S)` with nonempty closed values (in the
    subtype `↥S`) whose ambient image is convex, and any base point
    `i : ↥S` and target `u : EuclideanSpace ℝ (Fin n)`, the Hilbert
    projection theorem produces a nearest point of
    `Subtype.val '' F i` to `u`.

    The proof chains:
    * `IsClosed.isCompact` (`F i` closed in compact `↥S`)
    * `IsCompact.image` (push compactness through `Subtype.val`)
    * `IsCompact.isComplete` (compact → complete, no `[CompleteSpace α]`)
    * `Set.Nonempty.image` (push nonemptyness through `Subtype.val`)
    * `exists_norm_eq_iInf_of_complete_convex` (the Hilbert projection).

    All five Mathlib bearers verified at pinned Mathlib rev
    `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` by S22 PREP
    (`sessions/2026-05-14-s22-prep-step-b-helper-and-completeness-route.md`),
    which selected this tighter "compact → complete" route over the
    S19b "closed-then-complete-with-CompleteSpace" route to avoid the
    `[CompleteSpace α]` typeclass synthesis (same `IsCompact.isComplete`
    dot-notation as the S14 site at file line 223).

    **Use site (S19 step (c)–(d)).** Inside the eventual
    `approx_selection_exists_proof`, applied at any
    `i ∈ ρ.finsupport x` (from the S18e bundle) and
    `u := (fC x : EuclideanSpace ℝ (Fin n))`, this lemma supplies the
    witness `y ∈ F i` together with the minimal-norm certificate that
    drives the §4.b graph-distance bound (S19 PREP §6 Step 6c). -/
private lemma exists_nearest_in_image_F {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_compact : IsCompact S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_closed : ∀ x, IsClosed (F x))
    (hF_convex :
      ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (i : ↥S) (u : EuclideanSpace ℝ (Fin n)) :
    ∃ y ∈ ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))),
      ‖u - y‖ = ⨅ w : ((Subtype.val '' F i) : Set _), ‖u - w‖ := by
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  have hFi_ne_img :
      ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))).Nonempty :=
    (hF_ne i).image _
  have hFi_complete :
      IsComplete ((Subtype.val '' F i) : Set (EuclideanSpace ℝ (Fin n))) :=
    (((hF_closed i).isCompact).image continuous_subtype_val).isComplete
  exact exists_norm_eq_iInf_of_complete_convex hFi_ne_img hFi_complete
          (hF_convex i) u

/-- **Sequential Compactness in Metric Spaces**

    In a compact metric space, every sequence has a convergent subsequence.
    Proved from Mathlib's `IsCompact.isSeqCompact` (PseudoMetricSpace is
    first-countable). Was previously stated as an axiom; now derived. -/
theorem seq_compact_of_compact {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (hS : IsCompact S) (x : ℕ → X) (hx : ∀ n, x n ∈ S) :
    ∃ (a : X) (φ : ℕ → ℕ), a ∈ S ∧ StrictMono φ ∧
      Tendsto (x ∘ φ) atTop (𝓝 a) := by
  obtain ⟨a, ha, φ, hφ_mono, hφ_tend⟩ := hS.isSeqCompact hx
  exact ⟨a, φ, ha, hφ_mono, hφ_tend⟩

-- ============================================================
-- Part III: Limit Argument (Helper Lemma)
-- ============================================================

/-- A continuous function with ε-approximate fixed point property
    for all ε > 0 has a true fixed point (when the target is closed).

    This captures the limit argument: if we can get "almost" fixed points
    for any precision, compactness gives a real one.

    **Proof outline**:
    1. Build sequences `xₙ ∈ S`, `yₙ ∈ F(xₙ)` with `dist(xₙ, yₙ) < 1/(n+1)`
       via choice on `happrox`.
    2. Compactness of `S` yields a subsequence `x_{φ(n)} → x*` with `x* ∈ S`.
    3. Since `dist(x_{φ(n)}, y_{φ(n)}) → 0`, the subsequence
       `y_{φ(n)} → x*` as well (triangle inequality).
    4. Suppose `x* ∉ F(x*)`. Case split on `(F x*).Nonempty`:
       - **Empty case**: take `V := ∅` (open superset of empty F(x*));
         UHC gives an open `U ∋ x*` with `F(U) ⊆ ∅`, hence eventually
         `F(x_{φ(n)}) = ∅`, contradicting `y_{φ(n)} ∈ F(x_{φ(n)})`.
       - **Nonempty case**: `δ := infDist x* (F x*) > 0` since `F(x*)` is
         closed and `x* ∉ F(x*)`. Take `V := Metric.thickening (δ/2) (F x*)`,
         an open superset of `F(x*)`. UHC gives an open `U ∋ x*` with
         `F(U) ⊆ V`. Eventually `x_{φ(n)} ∈ U`, hence `y_{φ(n)} ∈ V`, so
         `infDist y_{φ(n)} (F x*) < δ/2`. Triangle inequality:
         `infDist x* (F x*) ≤ dist x* y_{φ(n)} + infDist y_{φ(n)} (F x*) < δ`
         for `n` large, contradicting `δ = infDist x* (F x*)`. -/
theorem approx_fixedpoint_implies_fixedpoint
    {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (hS : IsCompact S)
    (F : SetValuedMap X X) (hF_closed : ∀ x ∈ S, IsClosed (F x))
    (hF_uhc : IsUpperHemicontinuous F)
    (happrox : ∀ ε > 0, ∃ x ∈ S, ∃ y ∈ F x, dist x y < ε) :
    ∃ x ∈ S, IsFixedPoint F x := by
  -- Step 1: build sequences via choice
  choose xseq hxseq_S yseq hyseq_F hxy_dist using
    fun n : ℕ => happrox (1 / ((n : ℝ) + 1)) (by positivity)
  -- Step 2: extract convergent subsequence
  obtain ⟨x_star, φ, hx_star_S, hφ_mono, hφ_tend⟩ :=
    seq_compact_of_compact S hS xseq hxseq_S
  refine ⟨x_star, hx_star_S, ?_⟩
  -- Step 3: yseq ∘ φ → x_star
  have h_one_div_to_zero : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
      atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h_xy_to_zero :
      Tendsto (fun n => dist (xseq n) (yseq n)) atTop (𝓝 0) :=
    squeeze_zero (fun _ => dist_nonneg)
      (fun n => le_of_lt (hxy_dist n)) h_one_div_to_zero
  have h_xy_phi_to_zero :
      Tendsto (fun n => dist (xseq (φ n)) (yseq (φ n))) atTop (𝓝 0) :=
    h_xy_to_zero.comp hφ_mono.tendsto_atTop
  have h_x_phi_dist_to_zero :
      Tendsto (fun n => dist (xseq (φ n)) x_star) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hφ_tend
  have hyφ_tend : Tendsto (fun n => yseq (φ n)) atTop (𝓝 x_star) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have h_yx_phi : Tendsto (fun n => dist (yseq (φ n)) (xseq (φ n)))
        atTop (𝓝 0) := by
      simpa [dist_comm] using h_xy_phi_to_zero
    have h_sum :
        Tendsto (fun n => dist (yseq (φ n)) (xseq (φ n)) +
            dist (xseq (φ n)) x_star) atTop (𝓝 0) := by
      simpa using h_yx_phi.add h_x_phi_dist_to_zero
    exact squeeze_zero (fun _ => dist_nonneg)
      (fun n => dist_triangle (yseq (φ n)) (xseq (φ n)) x_star) h_sum
  -- Step 4: derive contradiction from x_star ∉ F x_star
  by_contra hne
  have hF_closed_xstar : IsClosed (F x_star) := hF_closed _ hx_star_S
  by_cases hF_xstar_ne : (F x_star).Nonempty
  · -- Nonempty case: thickening contradiction
    set δ : ℝ := Metric.infDist x_star (F x_star) with hδ_def
    have hδ_pos : 0 < δ := by
      have h_not_mem_closure : x_star ∉ closure (F x_star) := by
        rwa [hF_closed_xstar.closure_eq]
      have h_ne_zero : Metric.infDist x_star (F x_star) ≠ 0 := by
        intro h
        exact h_not_mem_closure
          ((Metric.mem_closure_iff_infDist_zero hF_xstar_ne).mpr h)
      exact lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm h_ne_zero)
    have hδ_half_pos : 0 < δ / 2 := by linarith
    -- Define V as the union of (δ/2)-balls around F x_star (open neighborhood of F x_star)
    let V : Set X := ⋃ y ∈ F x_star, Metric.ball y (δ / 2)
    have hV_open : IsOpen V := isOpen_biUnion (fun _ _ => Metric.isOpen_ball)
    have hF_in_V : F x_star ⊆ V := by
      intro y hy
      exact Set.mem_biUnion hy (Metric.mem_ball_self hδ_half_pos)
    let U : Set X := {z | F z ⊆ V}
    have hU_open : IsOpen U := hF_uhc V hV_open
    have hxstar_U : x_star ∈ U := hF_in_V
    -- Eventually xseq (φ n) ∈ U
    have h_eventually_U : ∀ᶠ n in atTop, xseq (φ n) ∈ U :=
      hφ_tend.eventually (hU_open.mem_nhds hxstar_U)
    -- Eventually dist x_star (yseq (φ n)) < δ/2
    have h_dist_yφ : Tendsto (fun n => dist x_star (yseq (φ n)))
        atTop (𝓝 0) := by
      have h := tendsto_iff_dist_tendsto_zero.mp hyφ_tend
      simpa [dist_comm] using h
    have h_eventually_dist :
        ∀ᶠ n in atTop, dist x_star (yseq (φ n)) < δ / 2 :=
      h_dist_yφ.eventually (Iio_mem_nhds hδ_half_pos)
    -- Combine to get the contradiction
    obtain ⟨n, hn_U, hn_dist⟩ :=
      (h_eventually_U.and h_eventually_dist).exists
    -- yseq (φ n) ∈ V, so ∃ z ∈ F x_star, dist (yseq (φ n)) z < δ/2
    have h_yseq_in_V : yseq (φ n) ∈ V := hn_U (hyseq_F (φ n))
    obtain ⟨z, hz_F, hz_ball⟩ := Set.mem_iUnion₂.mp h_yseq_in_V
    rw [Metric.mem_ball] at hz_ball
    -- δ = infDist x_star (F x_star) ≤ dist x_star z (since z ∈ F x_star)
    have h_delta_le_dist : δ ≤ dist x_star z := by
      have hi := Metric.infDist_le_dist_of_mem (x := x_star) hz_F
      linarith [hδ_def]
    -- triangle inequality on dist x_star z
    have h_tri : dist x_star z ≤ dist x_star (yseq (φ n)) + dist (yseq (φ n)) z :=
      dist_triangle _ _ _
    have hcontra : δ < δ := by
      calc δ ≤ dist x_star z := h_delta_le_dist
        _ ≤ dist x_star (yseq (φ n)) + dist (yseq (φ n)) z := h_tri
        _ < δ / 2 + δ / 2 := by linarith
        _ = δ := by ring
    exact lt_irrefl _ hcontra
  · -- Empty case
    rw [Set.not_nonempty_iff_eq_empty] at hF_xstar_ne
    let U : Set X := {z | F z ⊆ (∅ : Set X)}
    have hU_open : IsOpen U := hF_uhc ∅ isOpen_empty
    have hxstar_U : x_star ∈ U := by
      show F x_star ⊆ ∅
      rw [hF_xstar_ne]
    have h_eventually_U : ∀ᶠ n in atTop, xseq (φ n) ∈ U :=
      hφ_tend.eventually (hU_open.mem_nhds hxstar_U)
    obtain ⟨n, hn⟩ := h_eventually_U.exists
    -- F (xseq (φ n)) ⊆ ∅, but yseq (φ n) ∈ F (xseq (φ n))
    exact (hn (hyseq_F (φ n))).elim

-- ============================================================
-- Part IV: The Proof of Kakutani from Brouwer
-- ============================================================

/-- **Kakutani's FPT from Brouwer + Cellina–Browder Graph Selections**

    Proof sketch (filled body below):
    1. For each `ε > 0`, call `approx_selection_exists` with `ε/2` to get
       a continuous `(ε/2)`-graph-approximate selection `f` of `F`.
    2. Apply `brouwer_fpt` to `f` on `S` to get `x₀` with `f(x₀) = x₀`.
    3. The graph-form property at `x₀` gives `(x', y)` with
       `dist(x₀, x') < ε/2`, `y ∈ F(x')`, `dist(f(x₀), y) < ε/2`.
       Since `f(x₀) = x₀`, the triangle inequality
       `dist(x', y) ≤ dist(x', x₀) + dist(x₀, f x₀) + dist(f x₀, y)
                    < ε/2 + 0 + ε/2 = ε`
       provides the diagonal-distance witness.
    4. Hand the family of `ε`-witnesses to
       `approx_fixedpoint_implies_fixedpoint`, which uses sequential
       compactness + closedness + UHC of `F` to extract a genuine fixed
       point. -/
theorem kakutani_from_brouwer {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n)))
    (hS_ne : S.Nonempty) (hS_compact : IsCompact S) (hS_convex : Convex ℝ S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_ne : ∀ x, (F x).Nonempty)
    (hF_closed : ∀ x, IsClosed (F x))
    (hF_convex : ∀ x, Convex ℝ ((Subtype.val '' F x) : Set (EuclideanSpace ℝ (Fin n))))
    (hF_uhc : IsUpperHemicontinuous F) :
    ∃ x : ↥S, IsFixedPoint F x := by
  -- The subtype ↥S inherits a PseudoMetricSpace from EuclideanSpace.
  -- Compactness of ↥S follows from compactness of S in the ambient space.
  haveI : CompactSpace ↥S := isCompact_iff_compactSpace.mp hS_compact
  have hUniv : IsCompact (Set.univ : Set ↥S) := isCompact_univ
  have hF_closed' : ∀ x ∈ (Set.univ : Set ↥S), IsClosed (F x) :=
    fun x _ => hF_closed x
  have happrox_total :
      ∀ ε > 0, ∃ x ∈ (Set.univ : Set ↥S), ∃ y ∈ F x, dist x y < ε := by
    intro ε hε
    -- Call the graph-selection axiom with ε/2; the triangle-inequality step
    -- below converts the (ε/2, ε/2) graph witness into an ε-diagonal witness.
    have hε_half : 0 < ε / 2 := by linarith
    obtain ⟨f, hf_cont, hf_approx⟩ :=
      approx_selection_exists S hS_ne hS_compact hS_convex F
        hF_ne hF_convex hF_uhc (ε / 2) hε_half
    obtain ⟨x0, hx0⟩ := brouwer_fpt S hS_ne hS_compact hS_convex f hf_cont
    -- Graph-form witness at `x = x0`:
    --   dist x0 x' < ε/2,  y ∈ F x',  dist (f x0) y < ε/2.
    obtain ⟨x', y, hxx', hy_F, hy_dist⟩ := hf_approx x0
    -- Beta-reduce the `(fun x => (f x : ↥S)) x0` form sitting inside `hy_dist`.
    have hy_dist' : dist (f x0) y < ε / 2 := hy_dist
    refine ⟨x', Set.mem_univ _, y, hy_F, ?_⟩
    -- Triangle: dist x' y ≤ dist x' x0 + dist x0 (f x0) + dist (f x0) y.
    -- f x0 = x0 forces dist x0 (f x0) = 0, so the bound is < ε/2 + ε/2 = ε.
    have hxx0 : dist x' x0 < ε / 2 := by
      rw [dist_comm]; exact hxx'
    have h_tri1 : dist x' y ≤ dist x' x0 + dist x0 y := dist_triangle _ _ _
    have h_tri2 : dist x0 y ≤ dist x0 (f x0) + dist (f x0) y := dist_triangle _ _ _
    have h_zero : dist x0 (f x0) = 0 := by rw [hx0]; exact dist_self _
    linarith
  obtain ⟨x_star, _, hfp⟩ :=
    approx_fixedpoint_implies_fixedpoint (Set.univ : Set ↥S) hUniv F
      hF_closed' hF_uhc happrox_total
  exact ⟨x_star, hfp⟩

/-
## Part V: Why This Matters

The proof of Kakutani from Brouwer via graph-approximate selections
demonstrates the power of three fundamental principles:
1. **Brouwer's FPT** (topological): continuous self-maps of compact convex sets have fixed points
2. **Cellina–Browder graph selections** (geometric): UHC maps with convex
   values admit continuous functions whose graph lies in any prescribed
   neighborhood of the graph of `F`
3. **Compactness** (analytical): bounded sequences have convergent subsequences

The combination yields fixed points for set-valued maps — the cornerstone
of Nash equilibrium existence in game theory.

### Infrastructure Needed in Mathlib
- Brouwer's FPT for general compact convex sets (currently only for closed balls)
- Partition of unity construction for finite open covers in Euclidean space
  (powering the Cellina–Browder construction)

### Alternative Proof Paths
1. **Simplicial approximation**: Triangulate S, define PL approximations. Avoids
   partition of unity but needs triangulation machinery.
2. **Michael's selection theorem**: Stronger than needed here (gives exact continuous
   selections for lower hemicontinuous maps with convex values).

### Why not a pointwise approximate selection?
Under USC + convex values, the pointwise form
`∀ x, ∃ y ∈ F x, dist (f x) y < ε` is provably false in general (S6
analysis: 1-D counterexample with `F(0) = [0,1]`, `F(t > 0) = {0}`,
`F(t < 0) = {1}` admits no continuous pointwise (1/3)-selection by an
IVT argument at `0`). The graph form is the strongest selection
provable from USC alone, and is what Mathlib's `PartitionOfUnity`
infrastructure can produce via the Cellina averaging argument.

## Summary

### Axioms (2)
1. `brouwer_unit_ball` — Brouwer's FPT on the closed unit ball in
   `EuclideanSpace ℝ (Fin n)` (S11.A strict-weakening, 2026-05-09).
   Strictly weaker than the previous `axiom brouwer_fpt` (general
   compact convex `S`); the general form is now derived as
   `theorem brouwer_fpt` via in-house retraction reduction.
2. `approx_selection_exists` — UHC + convex values → continuous
   `ε`-graph-approximate selections (Cellina–Browder form).

### Theorems (proved + transitional)
- `seq_compact_of_compact` — Sequential compactness in compact metric
  spaces (was an axiom; now derived from Mathlib).
- `approx_fixedpoint_implies_fixedpoint` — Limit argument for
  approximate fixed points.
- `kakutani_from_brouwer` — The main reduction: Kakutani from the two
  axioms (uses the graph form via a triangle-inequality
  `ε ↦ 2·(ε/2) = ε` step).
- `brouwer_fpt` — Brouwer's FPT for general compact convex `S`,
  derived from `axiom brouwer_unit_ball` via the elementwise rescaling
  retraction reduction (S11.A.body landed S13, researcher-10,
  2026-05-09; S11.B helper landed S14, researcher-3, 2026-05-09;
  Mathlib API drift fix in S15, PR #17654). End-to-end sorry-free.
- `exists_continuous_proj_convex` — Continuous nearest-point retraction
  onto a compact convex set, used by the `brouwer_fpt` body. Landed
  in S14 (~100 Lean lines via `exists_norm_eq_iInf_of_complete_convex`
  + variational inequality + Cauchy–Schwarz 1-Lipschitz argument).

### Path to Axiom Elimination
1. **(S12+, prerequisite work)**: prove `approx_selection_exists`
   (graph form, Cellina–Browder) using
   `Mathlib.Topology.PartitionOfUnity` plus the averaging argument.
   Estimated 200–500 Lean lines; the construction is standard
   (cover-by-UHC-neighborhoods + subordinate partition of unity +
   convex average; graph bound from neighborhood membership). Reduces
   axiom count from 2 to 1.
2. **(Optional, far future)**: in-house Brouwer FPT proof to eliminate
   `brouwer_unit_ball` (Option B from S10's note). Standard routes are
   (a) simplicial approximation + Sperner (the gallery has a Sperner
   formalization), or (b) degree theory in `Mathlib.Topology.Algebra.
   Module.Multilinear`. Either route is several thousand Lean lines.
   Reduces axiom count from 1 to 0.

### Current Status (S16, 2026-05-11)

- 0 sorries (entire file).
- 2 axioms (`brouwer_unit_ball`, `approx_selection_exists`).
- 5 theorems + 1 lemma, all axiom-dependent only via the 2 axioms above.
- End-to-end formalization of Kakutani-from-Brouwer-via-graph-form-
  approximate-selections is complete modulo the 2 axioms.
-/

#check @brouwer_unit_ball
#check @brouwer_fpt
#check @exists_continuous_proj_convex
#check @approx_selection_exists
#check @approx_fixedpoint_implies_fixedpoint
#check @kakutani_from_brouwer

end KakutaniFromBrouwer
