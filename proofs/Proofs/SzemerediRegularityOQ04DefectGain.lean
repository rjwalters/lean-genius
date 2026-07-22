/-
  Szemerédi Regularity Lemma — OQ-04: the one-sided defect energy gain (S18).

  `StepThree.lean` (S17) packaged the degenerate side of the sharp `2×2`
  dichotomy into the asymmetric 3-piece step `IsWitnessedSharpStep3`: only `B`
  splits, and the deviating piece `B₁` carries an `eps`-mass floor together with
  an `eps`-density gap *against the parent pair* `(A, B)`.  The symmetric energy
  engine (`pairEnergy_split_gain`, Energy.lean) cannot consume this witness: its
  deviation hypothesis compares the two halves, `|d(A₁,B) − d(A₂,B)| ≥ δ`, while
  the 3-piece step only controls the deviation of ONE half from the PARENT — and
  `energy_excess_A_split` (SzemerediCoreOQ01.lean) needs BOTH halves nonempty.

  This file supplies the missing one-sided (defect) form of the Cauchy–Schwarz
  energy boost, the residual obligation recorded in the header of
  `StepThree.lean`:

  * `defect_energy_bound` — the two-cell weighted-mean defect inequality:
    if `μ` is the size-weighted mean of `d₁, d₂` and `δ ≤ |d₁ − μ|`, then
    `(w₁+w₂)·μ² + w₁·δ² ≤ w₁·d₁² + w₂·d₂²`.  Of the two variance terms in
    `Σ wᵢ(dᵢ−μ)²`, keeping only the deviating cell already yields the gain — so
    NO positivity of `w₂` is needed (the parent-mean pins `μ` even when the
    complementary cell is empty).
  * `pairEnergy_split_gain_defect` — the pair-energy form for an `A`-side split:
    a `δ`-deviation of `d(A₁,B)` from the parent density `d(A₁∪A₂,B)` gains
    `(|A₁||B|/n²)·δ²` of normalized energy.
  * `pairEnergy_split_gain_defect_right` — the `B`-side transport via
    `pairEnergy_comm`/`edgeDensity_symm`: the exact shape the 3-piece step needs.
  * `pairEnergy_step3_gain` — the `eps³` form: with the mass floor
    `eps·|B| ≤ |B₁|` and the `eps`-gap, splitting `B` gains
    `≥ eps³·|A||B|/n²` — the increment the outer AFKS budget consumes
    (`eps³ ≥ eps⁴` covers both dichotomy branches).
  * `pairEnergy_gain_of_isWitnessedSharpStep3` — capstone: every witnessed
    3-piece step carries the `eps³` pair-energy gain at its refined pair.

  0 axioms, 0 sorries.

  Reference: Alon–Fischer–Krivelevich–Szegedy, "Efficient testing of large
  graphs", Combinatorica 20 (2000).
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04Bridge
import Proofs.SzemerediRegularityOQ04StepThree

namespace Szemeredi.RegularityOQ04DefectGain

open Szemeredi.Core Szemeredi.EnergyIncrement Szemeredi.RegularityOQ04Energy
  Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04StepThree

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: THE TWO-CELL DEFECT INEQUALITY (PURE ARITHMETIC)
-- ═══════════════════════════════════════════════════════════════════

/-- **Weighted-mean defect inequality.**  If `μ` is the `w`-weighted mean of
    `d₁, d₂` (stated multiplicatively, so no division and no positivity of the
    total weight is needed) and the FIRST cell deviates from the mean by at
    least `δ`, then the second moment exceeds the squared mean by at least
    `w₁·δ²`:

    `(w₁+w₂)·μ² + w₁·δ² ≤ w₁·d₁² + w₂·d₂²`.

    This is the one-sided (defect) half of the variance identity
    `Σ wᵢdᵢ² − (Σwᵢ)μ² = Σ wᵢ(dᵢ−μ)²`: dropping the nonnegative term
    `w₂(d₂−μ)²` and bounding `w₁(d₁−μ)² ≥ w₁δ².  Unlike
    `split_energy_excess_bound`, the complementary weight `w₂` may be zero. -/
theorem defect_energy_bound (w₁ w₂ d₁ d₂ μ δ : ℚ) (h₁ : 0 ≤ w₁) (h₂ : 0 ≤ w₂)
    (hμ : (w₁ + w₂) * μ = w₁ * d₁ + w₂ * d₂) (hδ : 0 ≤ δ)
    (hdev : δ ≤ |d₁ - μ|) :
    (w₁ + w₂) * μ ^ 2 + w₁ * δ ^ 2 ≤ w₁ * d₁ ^ 2 + w₂ * d₂ ^ 2 := by
  have hsq : δ ^ 2 ≤ (d₁ - μ) ^ 2 := by
    have habs : δ * δ ≤ |d₁ - μ| * |d₁ - μ| := mul_self_le_mul_self hδ hdev
    rw [abs_mul_abs_self] at habs
    nlinarith [habs]
  have hμμ : ((w₁ + w₂) * μ) * μ = (w₁ * d₁ + w₂ * d₂) * μ := by rw [hμ]
  nlinarith [mul_le_mul_of_nonneg_left hsq h₁,
    mul_nonneg h₂ (sq_nonneg (d₂ - μ)), hμμ]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE ONE-SIDED PAIR-ENERGY GAIN (DEVIATION FROM THE PARENT)
-- ═══════════════════════════════════════════════════════════════════

/-- **One-sided (defect) energy increment, `A`-side split.**  If the piece `A₁`
    of a disjoint split deviates from the PARENT density by at least `δ` —
    `δ ≤ |d(A₁,B) − d(A₁∪A₂,B)|` — then refining the pair raises its normalized
    energy contribution by at least `(|A₁|·|B|/n²)·δ²`.

    Compare `pairEnergy_split_gain`, whose hypothesis is the deviation BETWEEN
    the two halves and which needs both halves nonempty; here only the deviating
    piece `A₁` must be nonempty, because the parent mean pins the average even
    when `A₂ = ∅`. -/
theorem pairEnergy_split_gain_defect (G : SimpleGraph V) [DecidableRel G.Adj]
    (A₁ A₂ B : Finset V) (hA : Disjoint A₁ A₂)
    (hn₁ : 0 < (A₁.card : ℚ)) (hB : 0 < (B.card : ℚ))
    (δ : ℚ) (hδ : 0 ≤ δ)
    (hdev : δ ≤ |edgeDensity G A₁ B - edgeDensity G (A₁ ∪ A₂) B|) :
    pairEnergy G (A₁ ∪ A₂) B +
        (A₁.card : ℚ) * B.card / (Fintype.card V : ℚ) ^ 2 * δ ^ 2 ≤
      pairEnergy G A₁ B + pairEnergy G A₂ B := by
  have hcard : ((A₁ ∪ A₂).card : ℚ) = (A₁.card : ℚ) + A₂.card := by
    rw [Finset.card_union_of_disjoint hA]; push_cast; ring
  -- the parent density is the size-weighted mean of the sub-densities
  have hmul := edgeDensity_union_mul G A₁ A₂ B hA
  rw [hcard] at hmul
  have hBne : (B.card : ℚ) ≠ 0 := ne_of_gt hB
  have havg : ((A₁.card : ℚ) + A₂.card) * edgeDensity G (A₁ ∪ A₂) B =
      (A₁.card : ℚ) * edgeDensity G A₁ B + (A₂.card : ℚ) * edgeDensity G A₂ B :=
    mul_left_cancel₀ hBne (by linear_combination hmul)
  -- the unnormalized defect bound at the deviating cell
  have hkey := defect_energy_bound (A₁.card : ℚ) (A₂.card : ℚ)
    (edgeDensity G A₁ B) (edgeDensity G A₂ B) (edgeDensity G (A₁ ∪ A₂) B) δ
    hn₁.le (by positivity) havg hδ hdev
  -- normalize by the common weight |B|/n² ≥ 0
  have hw : (0 : ℚ) ≤ (B.card : ℚ) / (Fintype.card V : ℚ) ^ 2 := by positivity
  unfold pairEnergy
  rw [hcard]
  have hgL :
      (↑A₁.card + ↑A₂.card : ℚ) * ↑B.card / (Fintype.card V : ℚ) ^ 2 *
          (edgeDensity G (A₁ ∪ A₂) B) ^ 2 +
        (A₁.card : ℚ) * ↑B.card / (Fintype.card V : ℚ) ^ 2 * δ ^ 2 =
      (B.card : ℚ) / (Fintype.card V : ℚ) ^ 2 *
        (((A₁.card : ℚ) + A₂.card) * (edgeDensity G (A₁ ∪ A₂) B) ^ 2 +
          (A₁.card : ℚ) * δ ^ 2) := by
    ring
  have hgR :
      (A₁.card : ℚ) * ↑B.card / (Fintype.card V : ℚ) ^ 2 *
          (edgeDensity G A₁ B) ^ 2 +
        (A₂.card : ℚ) * ↑B.card / (Fintype.card V : ℚ) ^ 2 *
          (edgeDensity G A₂ B) ^ 2 =
      (B.card : ℚ) / (Fintype.card V : ℚ) ^ 2 *
        ((A₁.card : ℚ) * (edgeDensity G A₁ B) ^ 2 +
          (A₂.card : ℚ) * (edgeDensity G A₂ B) ^ 2) := by
    ring
  rw [hgL, hgR]
  exact mul_le_mul_of_nonneg_left hkey hw

/-- **One-sided (defect) energy increment, `B`-side split.**  The transport of
    `pairEnergy_split_gain_defect` through `pairEnergy_comm`/`edgeDensity_symm`:
    splitting only the SECOND block of a pair, with the deviating piece `B₁`
    `δ`-far from the parent density `d(A, B₁∪B₂)`, gains `(|A|·|B₁|/n²)·δ²`.
    This is exactly the split shape of the asymmetric 3-piece step
    (`IsWitnessedSharpStep3`, StepThree.lean). -/
theorem pairEnergy_split_gain_defect_right (G : SimpleGraph V)
    [DecidableRel G.Adj] (A B₁ B₂ : Finset V) (hB : Disjoint B₁ B₂)
    (hn₁ : 0 < (B₁.card : ℚ)) (hA : 0 < (A.card : ℚ))
    (δ : ℚ) (hδ : 0 ≤ δ)
    (hdev : δ ≤ |edgeDensity G A B₁ - edgeDensity G A (B₁ ∪ B₂)|) :
    pairEnergy G A (B₁ ∪ B₂) +
        (A.card : ℚ) * B₁.card / (Fintype.card V : ℚ) ^ 2 * δ ^ 2 ≤
      pairEnergy G A B₁ + pairEnergy G A B₂ := by
  rw [pairEnergy_comm G A (B₁ ∪ B₂), pairEnergy_comm G A B₁,
    pairEnergy_comm G A B₂]
  have hdev' : δ ≤ |edgeDensity G B₁ A - edgeDensity G (B₁ ∪ B₂) A| := by
    rwa [edgeDensity_symm G A B₁, edgeDensity_symm G A (B₁ ∪ B₂)] at hdev
  have h := pairEnergy_split_gain_defect G B₁ B₂ A hB hn₁ hA δ hδ hdev'
  have hswap : (A.card : ℚ) * B₁.card / (Fintype.card V : ℚ) ^ 2 * δ ^ 2 =
      (B₁.card : ℚ) * A.card / (Fintype.card V : ℚ) ^ 2 * δ ^ 2 := by
    ring
  rw [hswap]
  exact h

-- ═══════════════════════════════════════════════════════════════════
-- PART III: THE eps³ GAIN OF THE 3-PIECE STEP
-- ═══════════════════════════════════════════════════════════════════

/-- **The `eps³` energy gain of the 3-piece split data.**  With the `eps`-mass
    floor `eps·|B| ≤ |B₁|` on the deviating piece and the `eps`-density gap
    against the parent, splitting `B = B₁ ∪ B₂` (with `A` kept intact) raises
    the pair energy by at least `eps³·|A||B|/n²`:

    `pairEnergy G A B + eps³·|A||B|/n² ≤ pairEnergy G A B₁ + pairEnergy G A B₂`.

    The floor converts the raw defect gain `eps²·|A||B₁|/n²` into the quotable
    `eps³·|A||B|/n²` — one power of `eps` is the price of the mass floor.  This
    is the energy content of `IsWitnessedSharpStep3` recorded as the residual
    obligation in the header of `StepThree.lean`. -/
theorem pairEnergy_step3_gain (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B B₁ B₂ : Finset V) (hunion : B₁ ∪ B₂ = B) (hdisj : Disjoint B₁ B₂)
    (eps : ℚ) (heps : 0 < eps)
    (hApos : 0 < (A.card : ℚ)) (hBpos : 0 < (B.card : ℚ))
    (hfloor : eps * B.card ≤ (B₁.card : ℚ))
    (hdev : eps ≤ |edgeDensity G A B₁ - edgeDensity G A B|) :
    pairEnergy G A B +
        eps ^ 3 * ((A.card : ℚ) * B.card) / (Fintype.card V : ℚ) ^ 2 ≤
      pairEnergy G A B₁ + pairEnergy G A B₂ := by
  subst hunion
  -- the mass floor makes the deviating piece nonempty
  have hn₁ : 0 < (B₁.card : ℚ) := lt_of_lt_of_le (mul_pos heps hBpos) hfloor
  have h := pairEnergy_split_gain_defect_right G A B₁ B₂ hdisj hn₁ hApos
    eps heps.le hdev
  -- eps³·|A||B| ≤ eps²·|A||B₁| via the floor (one power of eps pays for it)
  have hstep : eps ^ 3 * ((A.card : ℚ) * ((B₁ ∪ B₂).card : ℚ)) ≤
      (A.card : ℚ) * (B₁.card : ℚ) * eps ^ 2 := by
    have hmono := mul_le_mul_of_nonneg_left hfloor
      (mul_nonneg (sq_nonneg eps) hApos.le)
    nlinarith [hmono]
  have hinv : (0 : ℚ) ≤ ((Fintype.card V : ℚ) ^ 2)⁻¹ := by positivity
  have h2 := mul_le_mul_of_nonneg_right hstep hinv
  have hgain : eps ^ 3 * ((A.card : ℚ) * ((B₁ ∪ B₂).card : ℚ)) /
        (Fintype.card V : ℚ) ^ 2 ≤
      (A.card : ℚ) * (B₁.card : ℚ) / (Fintype.card V : ℚ) ^ 2 * eps ^ 2 := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    nlinarith [h2]
  linarith [h, hgain]

/-- **Capstone: every witnessed 3-piece step carries the `eps³` pair-energy
    gain.**  Unpacking `IsWitnessedSharpStep3` (for positive `eps` and coarse
    floor `m`) returns the step data together with the energy increment at the
    refined pair — the quantitative input the outer AFKS chain construction
    consumes on the degenerate branch of the dichotomy. -/
theorem pairEnergy_gain_of_isWitnessedSharpStep3 (G : SimpleGraph V)
    [DecidableRel G.Adj] (parts : ℕ → Finset (Finset V)) (n : ℕ) (eps m : ℚ)
    (heps : 0 < eps) (hm : 0 < m)
    (h : IsWitnessedSharpStep3 G parts n eps m) :
    ∃ R : Finset (Finset V), ∃ A B B₁ B₂ : Finset V,
      parts n = insert A (insert B R) ∧
      parts (n + 1) = insert A (insert B₁ (insert B₂ R)) ∧
      B₁ ∪ B₂ = B ∧ Disjoint B₁ B₂ ∧
      pairEnergy G A B +
          eps ^ 3 * ((A.card : ℚ) * B.card) / (Fintype.card V : ℚ) ^ 2 ≤
        pairEnergy G A B₁ + pairEnergy G A B₂ := by
  obtain ⟨R, A, B, B₁, B₂, hpn, hpn1, hunion, hdisj, -, -, -, -, -,
    hmA, hmB, hfloor, hdev⟩ := h
  exact ⟨R, A, B, B₁, B₂, hpn, hpn1, hunion, hdisj,
    pairEnergy_step3_gain G A B B₁ B₂ hunion hdisj eps heps
      (lt_of_lt_of_le hm hmA) (lt_of_lt_of_le hm hmB) hfloor hdev⟩

end Szemeredi.RegularityOQ04DefectGain
