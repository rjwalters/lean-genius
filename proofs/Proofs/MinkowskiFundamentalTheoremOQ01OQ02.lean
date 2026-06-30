/-
  Homogeneity (Scaling Law) of the Successive Minima
  (minkowski-fundamental-theorem-oq-01-oq-02)

  Next step of `minkowski-fundamental-theorem-oq-01`, which built the successive
  minima infrastructure (the i-th successive minimum

      λᵢ(L, S) = inf { c > 0 : cS contains i+1 linearly independent lattice points })

  and stated, but left open, Minkowski's second theorem product bound.  The
  sibling file oq-01-oq-01 turned the order structure λ₀ ≤ ⋯ ≤ λₙ₋₁ into a
  bracketing of the *product*.

  Here we prove the most basic STRUCTURAL law that any honest treatment of the
  successive minima must establish: their behaviour under rescaling of the convex
  body.  Replacing `S` by `cS` (a `c`-fold dilation, `c > 0`) inverts every
  successive minimum:

      λᵢ(L, cS) = λᵢ(L, S) / c.

  This is the geometric statement that "making the body `c` times bigger makes
  every threshold `c` times smaller".  It is exactly the homogeneity property that
  makes the product `λ₀ ⋯ λₙ₋₁ · vol(S)` of Minkowski's second theorem a *scaling
  invariant*: under `S ↦ cS` the product of minima divides by `cⁿ` while the
  volume multiplies by `cⁿ`, so the second-theorem quantity is unchanged.  We make
  the minima half of that statement precise:

      ∏ᵢ λᵢ(L, cS)  =  (∏ᵢ λᵢ(L, S)) / cⁿ.

  Everything is proved with 0 sorries and 0 axioms, on top of the parent's custom
  `Lattice`/`ConvexBody` API.  No attainment / non-emptiness hypothesis is needed:
  the law holds verbatim even when a minimum is unattained, because in that case
  both sides are `0` (the infimum of the empty set is `0` in ℝ, and `0 / c = 0`).

  The engine is a self-contained scaling lemma for infima on ℝ,
  `sInf_preimage_mul_right`, proved by elementary `csInf` antisymmetry — no measure
  theory, no analysis.

  References:
  - Minkowski, Geometrie der Zahlen (1896)
  - Cassels, An Introduction to the Geometry of Numbers (1959), Ch. VIII
-/
import Mathlib
import Proofs.MinkowskiFundamentalTheorem
import Proofs.MinkowskiFundamentalTheoremOQ01

set_option maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace MinkowskiSecondTheoremHomogeneity

open MinkowskiFundamentalTheorem MinkowskiSecondTheorem Set
open scoped Pointwise

variable (n : ℕ) [NeZero n]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I:  A SCALING LAW FOR INFIMA ON ℝ
═══════════════════════════════════════════════════════════════════════════════

The whole homogeneity statement reduces to the following purely real-analytic
fact: for a positive constant `c` and a set `A ⊆ ℝ` of non-negative reals, the
infimum of the "stretched preimage" `{ d | d·c ∈ A }` is `sInf A / c`.  Because
the admissible-scaling sets are exactly such non-negative sets, this single lemma
drives every successive minimum.
-/

/-- **Scaling law for infima.**  For `c > 0` and a set `A` of non-negative reals,
    `sInf { d | d * c ∈ A } = sInf A / c`.  The non-negativity hypothesis makes
    `0` a common lower bound, and the empty case is covered automatically
    (`sInf ∅ = 0 = 0 / c`). -/
theorem sInf_preimage_mul_right {c : ℝ} (hc : 0 < c) (A : Set ℝ)
    (hA0 : ∀ a ∈ A, 0 ≤ a) :
    sInf {d : ℝ | d * c ∈ A} = sInf A / c := by
  set B : Set ℝ := {d : ℝ | d * c ∈ A} with hB
  have hAbdd : BddBelow A := ⟨0, hA0⟩
  have hBbdd : BddBelow B := by
    refine ⟨0, fun d hd => ?_⟩
    have hdc : 0 ≤ d * c := hA0 _ hd
    -- `0 ≤ d * c` and `0 < c` give `0 ≤ d`
    exact le_of_mul_le_mul_right (by simpa using hdc) hc
  by_cases hAne : A.Nonempty
  · have hAne' : A.Nonempty := hAne
    obtain ⟨a₀, ha₀⟩ := hAne
    have hBne : B.Nonempty :=
      ⟨a₀ / c, by simp only [hB, Set.mem_setOf_eq, div_mul_cancel₀ a₀ hc.ne']; exact ha₀⟩
    apply le_antisymm
    · -- `sInf B ≤ sInf A / c`
      rw [le_div_iff₀ hc]
      apply le_csInf hAne'
      intro a ha
      have hmem : a / c ∈ B := by
        simp only [hB, Set.mem_setOf_eq, div_mul_cancel₀ a hc.ne']; exact ha
      have hle : sInf B ≤ a / c := csInf_le hBbdd hmem
      calc sInf B * c ≤ (a / c) * c := mul_le_mul_of_nonneg_right hle hc.le
        _ = a := by field_simp
    · -- `sInf A / c ≤ sInf B`
      apply le_csInf hBne
      intro d hd
      rw [div_le_iff₀ hc]
      exact csInf_le hAbdd hd
  · -- `A` empty ⟹ `B` empty ⟹ both sides `0`
    have hBempty : B = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      exact fun d hd => hAne ⟨d * c, hd⟩
    rw [Set.not_nonempty_iff_eq_empty] at hAne
    rw [hBempty, hAne]
    simp [Real.sInf_empty]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II:  SCALING THE CONVEX BODY COMPOSES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Dilating twice composes the factors: `d • (c • S) = (d·c) • S`. -/
theorem ConvexBody.scale_scale (c d : ℝ) (S : ConvexBody n) :
    (ConvexBody.scale n d (ConvexBody.scale n c S)).carrier
      = (ConvexBody.scale n (d * c) S).carrier := by
  simp only [ConvexBody.scale_carrier, smul_smul]

/-- **The admissible-scaling set transforms by a stretch.**  Scaling the body by
    `c > 0` pulls the admissible-scaling set back by `· * c`:

      admissibleScalings (cS) i = { d | d·c ∈ admissibleScalings S i }. -/
theorem admissibleScalings_scale (L : Lattice n) (S : ConvexBody n) {c : ℝ}
    (hc : 0 < c) (i : Fin n) :
    admissibleScalings n L (ConvexBody.scale n c S) i
      = {d : ℝ | d * c ∈ admissibleScalings n L S i} := by
  ext d
  simp only [admissibleScalings, Set.mem_setOf_eq, ConvexBody.scale_scale,
    mul_pos_iff_of_pos_right hc]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III:  HOMOGENEITY OF EACH SUCCESSIVE MINIMUM
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Homogeneity of the successive minima.**  For every dilation factor `c > 0`,

      λᵢ(L, cS) = λᵢ(L, S) / c.

    No attainment hypothesis is required: if `λᵢ(L, S)` is unattained (its
    admissible set is empty) then so is `λᵢ(L, cS)`, and the identity reads
    `0 = 0 / c`. -/
theorem successiveMinimum_scale (L : Lattice n) (S : ConvexBody n) {c : ℝ} (hc : 0 < c)
    (i : Fin n) :
    successiveMinimum n L (ConvexBody.scale n c S) i = successiveMinimum n L S i / c := by
  unfold successiveMinimum
  rw [admissibleScalings_scale n L S hc i]
  exact sInf_preimage_mul_right hc (admissibleScalings n L S i) (fun a ha => le_of_lt ha.1)

/-- **Doubling the body halves every successive minimum:** `λᵢ(L, 2S) = λᵢ(L, S) / 2`. -/
theorem successiveMinimum_scale_two (L : Lattice n) (S : ConvexBody n) (i : Fin n) :
    successiveMinimum n L (ConvexBody.scale n 2 S) i = successiveMinimum n L S i / 2 :=
  successiveMinimum_scale n L S (by norm_num) i

/-- **Monotone-down in the body.**  Enlarging the body (`c ≥ 1`) does not increase
    any successive minimum: `λᵢ(L, cS) ≤ λᵢ(L, S)`.  (Bigger body ⟹ smaller — or
    equal — thresholds.) -/
theorem successiveMinimum_scale_le (L : Lattice n) (S : ConvexBody n) {c : ℝ}
    (hc : 1 ≤ c) (i : Fin n) :
    successiveMinimum n L (ConvexBody.scale n c S) i ≤ successiveMinimum n L S i := by
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  rw [successiveMinimum_scale n L S hc0 i]
  rw [div_le_iff₀ hc0]
  -- `λᵢ(S) ≤ λᵢ(S) * c`, since `λᵢ(S) ≥ 0` and `c ≥ 1`
  nlinarith [successiveMinimum_nonneg n L S i]

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV:  HOMOGENEITY OF THE PRODUCT — THE SCALING INVARIANT
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Homogeneity of the product of successive minima.**

      ∏ᵢ λᵢ(L, cS)  =  (∏ᵢ λᵢ(L, S)) / cⁿ.

    Combined with the dilation law `vol(cS) = cⁿ vol(S)` for the volume, this is
    precisely why the Minkowski second-theorem quantity `∏ᵢ λᵢ · vol(S)` is a
    scaling invariant: the product of minima divides by `cⁿ` while the volume
    multiplies by `cⁿ`. -/
theorem prod_successiveMinimum_scale (L : Lattice n) (S : ConvexBody n) {c : ℝ}
    (hc : 0 < c) :
    ∏ i : Fin n, successiveMinimum n L (ConvexBody.scale n c S) i
      = (∏ i : Fin n, successiveMinimum n L S i) / c ^ n := by
  simp only [successiveMinimum_scale n L S hc, div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]

/-- **The second-theorem product is scale-invariant.**  Granting only the volume
    dilation law `vol(cS) = cⁿ vol(S)` (supplied here as a hypothesis, since the
    parent's `HasVolume` is an abstract field), the quantity `∏ᵢ λᵢ · vol` that
    appears on the left of Minkowski's second theorem is unchanged when the body is
    rescaled:

      (∏ᵢ λᵢ(L, cS)) · vol(cS) = (∏ᵢ λᵢ(L, S)) · vol(S). -/
theorem secondTheorem_product_scale_invariant (L : Lattice n) (S : ConvexBody n) {c : ℝ}
    (hc : 0 < c) (volS volcS : ℝ) (hvol : volcS = c ^ n * volS) :
    (∏ i : Fin n, successiveMinimum n L (ConvexBody.scale n c S) i) * volcS
      = (∏ i : Fin n, successiveMinimum n L S i) * volS := by
  rw [prod_successiveMinimum_scale n L S hc, hvol]
  have hcn : (c : ℝ) ^ n ≠ 0 := pow_ne_zero n hc.ne'
  field_simp

/-
═══════════════════════════════════════════════════════════════════════════════
Summary
═══════════════════════════════════════════════════════════════════════════════

## Homogeneity (scaling law) of the successive minima  (oq-01-oq-02)

### What's proved (0 sorries, 0 axioms):
- `sInf_preimage_mul_right`: the real-analysis engine — for `c > 0` and a set of
  non-negative reals, `sInf {d | d·c ∈ A} = sInf A / c` (empty case included).
- `ConvexBody.scale_scale`: dilations compose, `d • (c • S) = (d·c) • S`.
- `admissibleScalings_scale`: scaling the body by `c` pulls back the admissible
  set by `· * c`.
- `successiveMinimum_scale`: **`λᵢ(L, cS) = λᵢ(L, S) / c`** — the homogeneity law,
  no attainment hypothesis needed.
- `successiveMinimum_scale_two`: the `c = 2` specialisation `λᵢ(L, 2S) = λᵢ(L,S)/2`.
- `successiveMinimum_scale_le`: enlarging the body (`c ≥ 1`) lowers every minimum.
- `prod_successiveMinimum_scale`: **`∏ᵢ λᵢ(L, cS) = (∏ᵢ λᵢ(L,S)) / cⁿ`**.
- `secondTheorem_product_scale_invariant`: granting `vol(cS) = cⁿ vol(S)`, the
  Minkowski-second-theorem quantity `∏ᵢ λᵢ · vol` is a scaling invariant.

### Honest scope:
This is the structural homogeneity of the successive minima and of the
second-theorem product — the basic scaling covariance that any treatment must
have.  The second theorem's product *bound* itself remains the open analytic core
(unchanged from the parent files); here we only show that the quantity it bounds
behaves correctly under rescaling of the body.
-/

#check @sInf_preimage_mul_right
#check @ConvexBody.scale_scale
#check @admissibleScalings_scale
#check @successiveMinimum_scale
#check @prod_successiveMinimum_scale
#check @secondTheorem_product_scale_invariant

end MinkowskiSecondTheoremHomogeneity
