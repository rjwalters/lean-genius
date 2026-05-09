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
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Sequences
import Mathlib.Tactic

noncomputable section

open Set Filter Topology Metric

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

/-- **LOOKUP-2 helper (S11.B work item, currently `sorry`-stubbed):**
    Nearest-point retraction onto a nonempty compact convex set in
    `EuclideanSpace ℝ (Fin n)`, packaged as a continuous map that is the
    identity on the set.

    **Proof outline (deferred to S11.B):** existence and uniqueness of
    the nearest point come from
    `exists_norm_eq_iInf_of_complete_convex`
    (`Mathlib.Analysis.InnerProductSpace.Projection`) combined with
    strict convexity of the Euclidean norm; continuity comes from the
    variational inequality (`norm_eq_iInf_iff_real_inner_le_zero`
    family); idempotency on `↥S` follows from `dist_self` plus the
    uniqueness clause. The full proof is ~30–80 Lean lines and is the
    isolated dependency of the S11.A retraction reduction below. -/
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
      set v₁ : EuclideanSpace ℝ (Fin n) := (r u₁ : _) with hv₁
      set v₂ : EuclideanSpace ℝ (Fin n) := (r u₂ : _) with hv₂
      have h1 : ⟪u₁ - v₁, v₂ - v₁⟫_ℝ ≤ 0 := hVI u₁ v₂ (hr_mem u₂)
      have h2 : ⟪u₂ - v₂, v₁ - v₂⟫_ℝ ≤ 0 := hVI u₂ v₁ (hr_mem u₁)
      -- Algebraic identity: the sum of the two variational quantities equals
      --   ‖v₁ - v₂‖² - ⟪u₁ - u₂, v₁ - v₂⟫.
      have hexp : ⟪u₁ - v₁, v₂ - v₁⟫_ℝ + ⟪u₂ - v₂, v₁ - v₂⟫_ℝ
                = ‖v₁ - v₂‖ ^ 2 - ⟪u₁ - u₂, v₁ - v₂⟫_ℝ := by
        have hself : ⟪v₁ - v₂, v₁ - v₂⟫_ℝ = ‖v₁ - v₂‖ ^ 2 :=
          real_inner_self_eq_norm_sq _
        have hcomm : ⟪v₂, v₁⟫_ℝ = ⟪v₁, v₂⟫_ℝ := real_inner_comm v₂ v₁
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
    have hg_dist : ∀ u₁ u₂ : EuclideanSpace ℝ (Fin n),
        dist ((r u₁ : EuclideanSpace ℝ (Fin n)))
             ((r u₂ : EuclideanSpace ℝ (Fin n)))
          ≤ ((1 : ℝ≥0) : ℝ) * dist u₁ u₂ := by
      intro u₁ u₂
      rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
      exact hLip u₁ u₂
    have hLipWith :
        LipschitzWith 1 (fun u : EuclideanSpace ℝ (Fin n) =>
                          ((r u : EuclideanSpace ℝ (Fin n)) :
                            EuclideanSpace ℝ (Fin n))) :=
      LipschitzWith.of_dist_le_mul hg_dist
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
    `s11-strict-weakening-spec.md` and `s12-s11a-body-step6-refinement.md`).**
    The body still depends on the `sorry`-stubbed
    `exists_continuous_proj_convex` helper (S11.B work item), so this
    theorem is not yet end-to-end sorry-free; once S11.B lands, the
    file's only remaining assumption on the Brouwer side will be the
    closed-unit-ball axiom.

    **Proof structure:**

    1. Since `S` is compact, it is bounded
       (`IsCompact.isBounded`); pick `R > 0` with
       `S ⊆ Metric.closedBall 0 R` via `Bornology.IsBounded.subset_closedBall_lt`.
    2. Build the nearest-point retraction `r : E → ↥S` from
       `exists_continuous_proj_convex` (LOOKUP-2 helper, S11.B; currently
       `sorry`-stubbed).
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
  2026-05-09). The body still depends on the `sorry`-stubbed helper
  `exists_continuous_proj_convex`, so it is not yet end-to-end
  sorry-free.
- `exists_continuous_proj_convex` — Continuous nearest-point retraction
  onto a compact convex set, used by the `brouwer_fpt` body.
  **Currently `sorry`-stubbed** (S11.B work item, ~30–80 Lean lines via
  `exists_norm_eq_iInf_of_complete_convex` + variational inequality).

### Path to Full Verification
1. **S11.B (next)**: prove `exists_continuous_proj_convex` from
   `Mathlib.Analysis.InnerProductSpace.Projection` API. After this
   lands, `theorem brouwer_fpt` is end-to-end sorry-free and the file's
   only remaining axiom on the Brouwer side is the closed-unit-ball
   form.
2. **S12+**: prove `approx_selection_exists` (graph form) using
   `PartitionOfUnity` plus the Cellina averaging argument.
3. **(Optional, far future)**: in-house Brouwer FPT proof to eliminate
   `brouwer_unit_ball` (Option B from S10's note).
-/

#check @brouwer_unit_ball
#check @brouwer_fpt
#check @exists_continuous_proj_convex
#check @approx_selection_exists
#check @approx_fixedpoint_implies_fixedpoint
#check @kakutani_from_brouwer

end KakutaniFromBrouwer
