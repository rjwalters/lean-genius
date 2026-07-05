/-
# Ballot Problem OQ-01-OQ-02-OQ-01-OQ-02-OQ-01: Uniform Fiber Transfer via `Measure.map`

Open Question from `ballot-problem-oq-01-oq-02-oq-01-oq-02`
("General Uniform Fiber Transfer"):

  "Can the event-wise uniform fiber transfer be lifted to the clean, structural
   statement about `MeasureTheory.Measure.map`? Rather than checking each event,
   express the whole transfer as a single pushforward identity for `Measure.count`
   restricted to `A` and `T`."

## The Answer

YES. If `f : α → β` maps `A` into `T` (`MapsTo f A T`) with every fiber
`A ∩ f⁻¹'{t}` of the same cardinality `c` over the finite set `T`, then the
pushforward of the restricted counting measure scales by `c`:

  `(Measure.count.restrict A).map f = c • Measure.count.restrict T`.

As a corollary, the uniform probability measure `uniformOn A` pushes forward to
`uniformOn T` — recovering the parent's event-wise transfer as a single
normalization step.

## Why the `MapsTo` hypothesis (a mathematical subtlety)

The parent theorem `uniformOn_fiber_transfer_all` used only `SurjOn f A T`
(`T ⊆ f '' A`) because it evaluated on events `P ⊆ T`, where points outside `T`
are irrelevant. The *global* pushforward identity, however, is tested on ALL
measurable `S ⊆ β`. If some element of `A` were sent outside `T`, that mass
would land at a point where the right-hand side `c • count.restrict T` is zero,
breaking the equality. `MapsTo f A T` (equivalently `f '' A ⊆ T`) is exactly the
condition that no mass escapes `T`. Together with the uniform-fiber hypothesis
(which forces every `t ∈ T` to have a nonempty preimage when `c > 0`), this gives
`f '' A = T`.

## Proof Strategy

Prove equality of measures with `Measure.ext`: it suffices to agree on every
measurable `S ⊆ β`.

  LHS S = ((count.restrict A).map f) S
        = (count.restrict A) (f⁻¹' S)          -- `Measure.map_apply`
        = count (f⁻¹' S ∩ A)                    -- `Measure.restrict_apply`
        = count (A ∩ f⁻¹'(S ∩ T))               -- `MapsTo` set rewrite
        = ((A ∩ f⁻¹'(S ∩ T)).ncard : ℝ≥0∞)      -- finite: `count = ncard`
        = (c * (S ∩ T).ncard : ℝ≥0∞)            -- parent `uniform_fiber_count`
        = c * count (S ∩ T)                      -- finite: `ncard = count`

  RHS S = (c • count.restrict T) S
        = c * (count.restrict T) S               -- `smul_apply`, `nsmul_eq_mul`
        = c * count (S ∩ T)                       -- `Measure.restrict_apply`

The factor `c` and the intersection `S ∩ T` match on both sides, so the whole
identity collapses onto the already-verified counting lemma
`BallotGeneralFiberTransfer.uniform_fiber_count`.

## Status

UNVERIFIED / build-pending. The Docker build wrapper and the Aristotle proof
service were both unavailable during this session, so this file has NOT been
machine-checked. The proof reduces to the verified parent lemma
`uniform_fiber_count` via standard Mathlib measure-theory API
(`Measure.map_apply`, `Measure.restrict_apply`, `Measure.count_apply_finite`,
`Set.ncard_eq_toFinset_card`, `Measure.map_smul`). It must be built before being
marked `verified`.
-/

import Proofs.BallotProblemOQ01OQ02OQ01OQ02
import Mathlib.Tactic

open ProbabilityTheory Set MeasureTheory

namespace BallotCountMapTransfer

/-
══════════════════════════════════════════════════════════════
PART I: count ↔ ncard BRIDGE
══════════════════════════════════════════════════════════════ -/

/-- On a finite set, the counting measure equals the natural-number cardinality
    (`ncard`), cast into `ℝ≥0∞`. This is the bridge that lets the purely
    combinatorial parent lemma `uniform_fiber_count` (stated in `ncard`) discharge
    a measure-theoretic goal. -/
theorem count_eq_ncard {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    (s : Set α) (hs : s.Finite) :
    Measure.count s = (s.ncard : ℝ≥0∞) := by
  rw [Measure.count_apply_finite s hs, Set.ncard_eq_toFinset_card s hs]

/-
══════════════════════════════════════════════════════════════
PART II: THE MapsTo SET REWRITE
══════════════════════════════════════════════════════════════ -/

/-- When `f` maps `A` into `T`, testing the preimage of an arbitrary `S` against
    `A` is the same as testing the preimage of `S ∩ T`: elements of `A` already
    land in `T`, so intersecting the target with `T` changes nothing. -/
theorem preimage_inter_of_mapsTo {α β : Type*} (f : α → β) (A : Set α) (T : Set β)
    (hmaps : MapsTo f A T) (S : Set β) :
    f ⁻¹' S ∩ A = A ∩ f ⁻¹' (S ∩ T) := by
  ext x
  simp only [mem_inter_iff, mem_preimage]
  constructor
  · rintro ⟨hS, hA⟩
    exact ⟨hA, hS, hmaps hA⟩
  · rintro ⟨hA, hS, _⟩
    exact ⟨hS, hA⟩

/-
══════════════════════════════════════════════════════════════
PART III: MAIN THEOREM — the `Measure.map` pushforward identity
══════════════════════════════════════════════════════════════ -/

/-- **Uniform Fiber Transfer as a `Measure.map` identity.**

    Let `f : α → β` be measurable, mapping `A` into the finite set `T`, with every
    fiber `A ∩ f⁻¹'{t}` of the same cardinality `c` over `T`. Then the pushforward
    of the restricted counting measure scales by `c`:

      `(Measure.count.restrict A).map f = c • Measure.count.restrict T`.

    This is the structural (event-free) form of the parent's
    `uniformOn_fiber_transfer_all`. -/
theorem count_restrict_map_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (f : α → β) (hf : Measurable f)
    (A : Set α) (T : Set β) (hA : A.Finite) (hT : T.Finite)
    (hmaps : MapsTo f A T)
    (c : ℕ) (hc : ∀ t ∈ T, (A ∩ f ⁻¹' {t}).ncard = c) :
    (Measure.count.restrict A).map f = c • Measure.count.restrict T := by
  -- Agree on every measurable set `S`.
  refine Measure.ext (fun S hS => ?_)
  -- LHS: unfold the pushforward and the restriction.
  rw [Measure.map_apply hf hS, Measure.restrict_apply (hf hS),
      preimage_inter_of_mapsTo f A T hmaps S]
  -- The two relevant sets are finite.
  have hST : (S ∩ T).Finite := hT.subset inter_subset_right
  have hAfib : (A ∩ f ⁻¹' (S ∩ T)).Finite := hA.subset inter_subset_left
  -- LHS = count(A ∩ f⁻¹'(S∩T)) = ncard(...) = c * ncard(S∩T).
  rw [count_eq_ncard _ hAfib,
      BallotGeneralFiberTransfer.uniform_fiber_count f A hA T hT c hc (S ∩ T)
        inter_subset_right]
  -- RHS: `c •` a restricted count, unfolded on `S`.
  rw [Measure.smul_apply, Measure.restrict_apply hS, count_eq_ncard _ hST,
      nsmul_eq_mul]
  -- Both sides are `(c : ℝ≥0∞) * (S ∩ T).ncard`.
  push_cast
  ring

/-
══════════════════════════════════════════════════════════════
PART IV: COROLLARY — `uniformOn` pushforward
══════════════════════════════════════════════════════════════ -/

/-- **`uniformOn` transfer, structural form.**

    Under the same hypotheses (with `c > 0` and `T` nonempty, so both uniform
    measures are genuine probability measures), the uniform distribution on `A`
    pushes forward to the uniform distribution on `T`:

      `(uniformOn A).map f = uniformOn T`.

    This recovers the parent's event-wise `uniformOn_fiber_transfer_all` in one
    normalization step from the counting identity `count_restrict_map_eq`. -/
theorem uniformOn_map_eq
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (f : α → β) (hf : Measurable f)
    (A : Set α) (T : Set β) (hA : A.Finite) (hT : T.Finite)
    (hT_ne : T.Nonempty)
    (hmaps : MapsTo f A T)
    (c : ℕ) (hc_pos : 0 < c) (hc : ∀ t ∈ T, (A ∩ f ⁻¹' {t}).ncard = c) :
    (uniformOn A).map f = uniformOn T := by
  -- `uniformOn s = (count s)⁻¹ • count.restrict s` (definition via `cond`).
  -- Surjectivity from the fibers: every `t ∈ T` has `c > 0` preimages in `A`.
  have hf_surj : SurjOn f A T := fun t ht => by
    obtain ⟨x, hx⟩ := Set.nonempty_of_ncard_ne_zero (s := A ∩ f ⁻¹' {t})
      (by rw [hc t ht]; exact hc_pos.ne')
    exact ⟨x, hx.1, hx.2⟩
  -- Counting relation `count A = c * count T` from the surjective fiber decomposition.
  have hA_ncard : A.ncard = c * T.ncard := by
    rw [BallotGeneralFiberTransfer.surjOn_fiber_decomp f A T hf_surj]
    exact BallotFiberTransfer.ncard_biUnion_eq_of_uniform
      (fun t => A ∩ f ⁻¹' {t}) T hT
      (fun t _ => hA.subset inter_subset_left)
      (fun t₁ _ t₂ _ hne => BallotGeneralFiberTransfer.singleton_fiber_disjoint f A t₁ t₂ hne)
      c hc
  -- Positivity / finiteness facts for the ℝ≥0∞ arithmetic.
  have hT_pos : 0 < T.ncard := Set.ncard_pos hT |>.mpr hT_ne
  have hcountT : Measure.count (T : Set β) = (T.ncard : ℝ≥0∞) := count_eq_ncard T hT
  have hcountA : Measure.count (A : Set α) = (A.ncard : ℝ≥0∞) := count_eq_ncard A hA
  -- Expand `uniformOn` as a scalar multiple of the restricted count, then push
  -- the map through the scalar (`Measure.map_smul`) and apply the main identity.
  unfold uniformOn ProbabilityTheory.cond
  rw [Measure.map_smul, count_restrict_map_eq f hf A T hA hT hmaps c hc]
  -- Goal: `(count A)⁻¹ • (c • count.restrict T) = (count T)⁻¹ • count.restrict T`.
  rw [smul_smul, hcountA, hcountT, hA_ncard]
  -- `(c * T.ncard)⁻¹ * c = (T.ncard)⁻¹` in ℝ≥0∞ (c ≠ 0, T.ncard ≠ 0, both finite).
  congr 1
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc_pos.ne'
  have hcT : ((c * T.ncard : ℕ) : ℝ≥0∞) = (c : ℝ≥0∞) * (T.ncard : ℝ≥0∞) := by push_cast; ring
  rw [hcT, ENNReal.mul_inv (Or.inl hc0) (Or.inl (by exact_mod_cast (by omega : c * T.ncard ≠ 0))),
      mul_comm, mul_assoc, ENNReal.inv_mul_cancel hc0 (ENNReal.natCast_ne_top c), mul_one]

end BallotCountMapTransfer
