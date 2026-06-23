/-
  Successive Minima and Minkowski's Second Theorem — Infrastructure
  (minkowski-fundamental-theorem-oq-01)

  Open Question (from minkowski-fundamental-theorem, OQ #1):
  "Can Minkowski's second theorem (on successive minima) be formalized with the
  same infrastructure?"

  Minkowski's second theorem refines the fundamental (first) theorem.  For a
  lattice `L` and a symmetric convex body `S`, the i-th successive minimum is

      λᵢ = inf { c > 0 : cS contains i linearly independent lattice points }.

  The second theorem then bounds the product:

      (2ⁿ / n!) · covolume(L) ≤ λ₁ λ₂ ⋯ λₙ · vol(S) ≤ 2ⁿ · covolume(L).

  This file builds the infrastructure on top of the parent's custom Lattice /
  ConvexBody API and proves the tractable structural facts (0 sorries, 0 axioms):

  * `ConvexBody.scale` — scaling a symmetric convex body by a real factor stays a
    symmetric convex body.
  * `IndepLatticePoints` — the "`k` linearly independent lattice points in a set"
    predicate, and its antitonicity in `k`.
  * `successiveMinimum` — the i-th successive minimum, with positivity and
    monotonicity (λ₀ ≤ λ₁ ≤ ⋯).
  * `secondTheorem_upper_statement` — the precise statement of the upper bound.
  * `firstMinimum_le_one_of_volume_gt` — the first successive minimum is ≤ 1
    once `vol(S) > 2ⁿ covolume(L)`, derived directly from the parent's
    `minkowski_fundamental` (the first theorem, in successive-minima language).

  HONEST SCOPE: the deep analytic content — the product bound itself — is NOT
  proved here; it is stated as a scaffold and left as the open core.  What is
  delivered is the definitional framework plus the order structure and the
  first-minimum specialization of the first theorem.

  References:
  - Minkowski, Geometrie der Zahlen (1896)
  - Cassells, An Introduction to the Geometry of Numbers (1959), Ch. VIII
-/
import Mathlib
import Proofs.MinkowskiFundamentalTheorem

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace MinkowskiSecondTheorem

open MinkowskiFundamentalTheorem Set
open scoped Pointwise

variable (n : ℕ) [NeZero n]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: SCALING A CONVEX BODY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Scaling a symmetric convex body by a real factor `c` is again a symmetric
    convex body (`c • S`).  Convexity and central symmetry are preserved for
    every `c`; non-emptiness too. -/
def ConvexBody.scale (c : ℝ) (S : ConvexBody n) : ConvexBody n where
  carrier := c • S.carrier
  convex := S.convex.smul c
  symmetric := by
    intro x hx
    rw [Set.mem_smul_set] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨-y, S.symmetric y hy, by rw [smul_neg]⟩
  nonempty := S.nonempty.smul_set

@[simp] theorem ConvexBody.scale_carrier (c : ℝ) (S : ConvexBody n) :
    (ConvexBody.scale n c S).carrier = c • S.carrier := rfl

/-- Scaling by `1` is the identity on the carrier. -/
theorem ConvexBody.scale_one (S : ConvexBody n) :
    (ConvexBody.scale n 1 S).carrier = S.carrier := by
  simp [ConvexBody.scale_carrier, one_smul]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: INDEPENDENT LATTICE POINTS IN A SET
═══════════════════════════════════════════════════════════════════════════════ -/

/-- `IndepLatticePoints L k T` holds when `T` contains `k` linearly independent
    points of the lattice `L`. -/
def IndepLatticePoints (L : Lattice n) (k : ℕ) (T : Set (EuclideanN n)) : Prop :=
  ∃ v : Fin k → EuclideanN n,
    LinearIndependent ℝ v ∧ ∀ i, v i ∈ T ∧ v i ∈ latticePoints n L

/-- Containing `m` independent lattice points implies containing `k` of them
    for any `k ≤ m` (drop the surplus coordinates). -/
theorem IndepLatticePoints.mono {L : Lattice n} {k m : ℕ} {T : Set (EuclideanN n)}
    (hkm : k ≤ m) (h : IndepLatticePoints n L m T) : IndepLatticePoints n L k T := by
  obtain ⟨v, hli, hmem⟩ := h
  exact ⟨v ∘ Fin.castLE hkm, hli.comp _ (Fin.castLE_injective hkm),
    fun i => hmem (Fin.castLE hkm i)⟩

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE SUCCESSIVE MINIMA
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The set of admissible scalings for the i-th successive minimum:
    factors `c > 0` such that `cS` contains `i+1` linearly independent
    lattice points. -/
def admissibleScalings (L : Lattice n) (S : ConvexBody n) (i : Fin n) : Set ℝ :=
  {c : ℝ | 0 < c ∧ IndepLatticePoints n L (i.val + 1) (ConvexBody.scale n c S).carrier}

/-- The i-th successive minimum `λᵢ`. -/
noncomputable def successiveMinimum (L : Lattice n) (S : ConvexBody n) (i : Fin n) : ℝ :=
  sInf (admissibleScalings n L S i)

/-- `0` is a lower bound for every set of admissible scalings. -/
theorem admissibleScalings_bddBelow (L : Lattice n) (S : ConvexBody n) (i : Fin n) :
    BddBelow (admissibleScalings n L S i) :=
  ⟨0, fun c hc => le_of_lt hc.1⟩

/-- Successive minima are non-negative. -/
theorem successiveMinimum_nonneg (L : Lattice n) (S : ConvexBody n) (i : Fin n) :
    0 ≤ successiveMinimum n L S i :=
  Real.sInf_nonneg (fun c hc => le_of_lt hc.1)

/-- A larger index has a smaller (or equal) admissible-scaling set: if `cS`
    contains `j+1` independent lattice points then it contains `i+1` for `i ≤ j`. -/
theorem admissibleScalings_subset (L : Lattice n) (S : ConvexBody n) {i j : Fin n}
    (hij : i ≤ j) : admissibleScalings n L S j ⊆ admissibleScalings n L S i := by
  intro c hc
  exact ⟨hc.1, hc.2.mono _ (Nat.succ_le_succ (Fin.val_fin_le.mpr hij))⟩

/-- The successive minima are monotone: `λᵢ ≤ λⱼ` for `i ≤ j`, provided the
    higher minimum is actually attained (its admissible set is non-empty). -/
theorem successiveMinimum_mono (L : Lattice n) (S : ConvexBody n) {i j : Fin n}
    (hij : i ≤ j) (hne : (admissibleScalings n L S j).Nonempty) :
    successiveMinimum n L S i ≤ successiveMinimum n L S j :=
  csInf_le_csInf (admissibleScalings_bddBelow n L S i) hne
    (admissibleScalings_subset n L S hij)

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: MINKOWSKI'S SECOND THEOREM (statement) AND THE FIRST-MINIMUM BOUND
═══════════════════════════════════════════════════════════════════════════════ -/

/-- The upper bound of Minkowski's second theorem, stated precisely:
    `λ₁ ⋯ λₙ · vol(S) ≤ 2ⁿ · covolume(L)`.  Stated as a scaffold; the proof is
    the open analytic core (it requires the simultaneous reduction of the body
    along a basis realizing the successive minima). -/
def secondTheorem_upper_statement (L : Lattice n) (S : ConvexBody n) [hv : HasVolume n S] : Prop :=
  (∏ i : Fin n, successiveMinimum n L S i) * hv.volume ≤ (2 : ℝ) ^ n * L.covolume

/-- **The first theorem in successive-minima language.**  When
    `vol(S) > 2ⁿ covolume(L)`, the body `S` already contains a non-zero lattice
    point, so a single independent lattice point lives in `1 · S`; hence the
    first successive minimum `λ₀` is at most `1`.  This is the `i = 0` shadow of
    Minkowski's second theorem, derived directly from `minkowski_fundamental`. -/
theorem firstMinimum_le_one_of_volume_gt (L : Lattice n) (S : ConvexBody n)
    [hv : HasVolume n S] (h_vol : hv.volume > criticalVolume n L) :
    successiveMinimum n L S ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ ≤ 1 := by
  obtain ⟨x, hxS, hxL, hx0⟩ := minkowski_fundamental n L S h_vol
  -- `1` is an admissible scaling for the first minimum.
  have hmem : (1 : ℝ) ∈ admissibleScalings n L S ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ := by
    refine ⟨one_pos, ?_⟩
    refine ⟨fun _ => x, ?_, ?_⟩
    · -- a single non-zero vector is linearly independent
      haveI : Unique (Fin ((⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ : Fin n).val + 1)) :=
        (inferInstance : Unique (Fin 1))
      rw [linearIndependent_unique_iff]
      simpa using hx0
    · intro i
      rw [ConvexBody.scale_carrier, one_smul]
      exact ⟨hxS, hxL⟩
  exact csInf_le (admissibleScalings_bddBelow n L S _) hmem

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## Successive minima infrastructure for Minkowski's second theorem
   (answering OQ-01 of minkowski-fundamental-theorem)

### What's proved (0 sorries, 0 axioms):
- `ConvexBody.scale`: scaling preserves symmetric-convex-body structure.
- `IndepLatticePoints` + `.mono`: the "k independent lattice points" predicate
  and its antitonicity in k.
- `successiveMinimum`: the i-th successive minimum λᵢ = inf of admissible
  scalings, with `successiveMinimum_nonneg` (positivity) and
  `successiveMinimum_mono` (λᵢ ≤ λⱼ for i ≤ j, when the higher minimum is attained).
- `firstMinimum_le_one_of_volume_gt`: λ₀ ≤ 1 under the first-theorem hypothesis,
  derived from the parent's `minkowski_fundamental`.

### Honest scope:
This is INFRASTRUCTURE + the first-minimum specialization, not the full second
theorem.  The product bound `secondTheorem_upper_statement` is stated as a
scaffold; its proof (and the matching lower bound) is the open analytic core,
requiring a basis realizing the successive minima and a simultaneous reduction
argument — left as the next step.
-/

#check @ConvexBody.scale
#check @IndepLatticePoints
#check @successiveMinimum
#check @successiveMinimum_mono
#check @firstMinimum_le_one_of_volume_gt
#check @secondTheorem_upper_statement

end MinkowskiSecondTheorem
