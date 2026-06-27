/-
  Entropic Uncertainty — Finite Shannon-Entropy Infrastructure
  (toward Erdős/Cauchy–Schwarz OQ chain `cauchy-schwarz-oq-01-oq-03-oq-02`)

  Source question (parent `cauchy-schwarz-oq-01-oq-03`, "Heisenberg Uncertainty from
  Complex Cauchy–Schwarz"): can the **entropic uncertainty principle** (Maassen–Uffink
  1988) — `H(p) + H(q) ≥ -2 ln c` for the outcome distributions of two orthonormal bases
  with maximal overlap `c` — be formalized in Lean 4?

  STATUS OF THE FULL THEOREM: BLOCKED on Mathlib. The sharp Maassen–Uffink constant
  follows from the Hausdorff–Young inequality, equivalently a Riesz–Thorin interpolation
  argument; as of Mathlib v4.26.0 there is **no** interpolation theory and **no** Lp→Lp'
  Fourier bound. (Deutsch's interpolation-free precursor `≥ -2 ln((1+c)/2)` is tractable
  in principle but still a substantial standalone development.)

  WHAT IS PROVABLE NOW, and is built here (0 axioms, 0 sorries): the finite-dimensional
  Shannon-entropy framework that any version of the entropic uncertainty relation needs —
  Shannon entropy of a probability vector via Mathlib's `Real.negMulLog`, its
  nonnegativity, and the **maximum-entropy bound** `H(p) ≤ log n` (Jensen on the concavity
  of `negMulLog`; equality at the uniform distribution). This is the "entropy half" of an
  entropic uncertainty relation, and a reusable building block for the eventual proof.

  This revision adds the **equality case** of the maximum-entropy bound:
  `H(p) = log n ↔ p` uniform, the strict-concavity refinement of the Jensen inequality.
-/

import Mathlib

open Finset

namespace CauchySchwarzOQ01OQ03OQ02

variable {ι : Type*} [Fintype ι]

/-- Shannon entropy of a finite probability vector `p` (in nats):
`H(p) = ∑ᵢ negMulLog(pᵢ) = -∑ᵢ pᵢ log pᵢ`, using Mathlib's `Real.negMulLog`. -/
noncomputable def shannonEntropy (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

/-- Entropy of a vector with entries in `[0,1]` is nonnegative (each `negMulLog` term is). -/
theorem shannonEntropy_nonneg {p : ι → ℝ} (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) :
    0 ≤ shannonEntropy p := by
  refine Finset.sum_nonneg fun i _ => ?_
  exact Real.negMulLog_nonneg (h0 i) (h1 i)

/-- **Maximum-entropy bound.** A probability vector on `n = card ι` outcomes has
`H(p) ≤ log n`, with equality for the uniform distribution. Proof: Jensen's inequality
applied to the concave function `negMulLog` with uniform weights `1/n`.

This is the entropy ceiling that bounds either marginal in an entropic uncertainty
relation; the genuinely hard content of Maassen–Uffink is the *lower* bound on the sum
`H(p) + H(q)`, which is interpolation-gated and not yet available in Mathlib. -/
theorem shannonEntropy_le_log_card [Nonempty ι] {p : ι → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    shannonEntropy p ≤ Real.log (Fintype.card ι) := by
  set n : ℕ := Fintype.card ι with hn
  have hnpos : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  -- Jensen for the concave `negMulLog` with uniform weights `1/n`.
  have hjensen :
      (∑ i : ι, ((n : ℝ)⁻¹) • Real.negMulLog (p i))
        ≤ Real.negMulLog (∑ i : ι, ((n : ℝ)⁻¹) • p i) := by
    refine Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := fun _ => (n : ℝ)⁻¹) (p := p) ?_ ?_ ?_
    · intro i _; positivity
    · -- weights sum to 1
      rw [Finset.sum_const, Finset.card_univ, ← hn, nsmul_eq_mul]
      field_simp
    · intro i _; exact Set.mem_Ici.mpr (h0 i)
  -- Evaluate the weighted mean: `∑ (1/n)•pᵢ = 1/n`.
  have hmean : (∑ i : ι, ((n : ℝ)⁻¹) • p i) = (n : ℝ)⁻¹ := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one]
  -- `negMulLog (1/n) = (1/n) * log n`.
  have hval : Real.negMulLog ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ * Real.log n := by
    rw [Real.negMulLog, Real.log_inv]; ring
  -- The LHS of Jensen is `(1/n) * H(p)`.
  have hlhs : (∑ i : ι, ((n : ℝ)⁻¹) • Real.negMulLog (p i))
      = (n : ℝ)⁻¹ * shannonEntropy p := by
    simp only [smul_eq_mul, shannonEntropy, Finset.mul_sum]
  rw [hlhs, hmean, hval] at hjensen
  -- Cancel the common positive factor `1/n`.
  exact le_of_mul_le_mul_left hjensen (by positivity)

/-- The uniform distribution attains the maximum-entropy bound: `H(uniform) = log n`. -/
theorem shannonEntropy_uniform [Nonempty ι] :
    shannonEntropy (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) = Real.log (Fintype.card ι) := by
  set n : ℕ := Fintype.card ι with hn
  have hnpos : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  simp only [shannonEntropy, Real.negMulLog, Real.log_inv, Finset.sum_const,
    Finset.card_univ, ← hn, nsmul_eq_mul]
  field_simp

/-- **Equality case of the maximum-entropy bound.** For a probability vector on
`n = card ι` outcomes, `H(p) = log n` *if and only if* `p` is the uniform distribution.

The reverse implication is `shannonEntropy_uniform`. The forward implication is the
strict-concavity (uniqueness) refinement of Jensen's inequality: because `negMulLog` is
*strictly* concave on `[0,∞)`, equality in the maximum-entropy bound forces all the
weighted points to coincide (`Real.strictConcaveOn_negMulLog.eq_of_map_sum_eq`), and the
normalization `∑ pᵢ = 1` then pins each entry to `1/n`. This upgrades the inequality
`shannonEntropy_le_log_card` to a full characterization of the maximizer (and, with it,
the equality case in any entropic uncertainty relation built on this infrastructure). -/
theorem shannonEntropy_eq_log_card_iff [Nonempty ι] {p : ι → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    shannonEntropy p = Real.log (Fintype.card ι)
      ↔ ∀ i, p i = (Fintype.card ι : ℝ)⁻¹ := by
  set n : ℕ := Fintype.card ι with hn
  have hnpos : 0 < n := Fintype.card_pos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  constructor
  · intro hH
    -- Uniform weights `1/n` sum to `1`.
    have hwsum : (∑ _i : ι, ((n : ℝ)⁻¹)) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, ← hn, nsmul_eq_mul]
      field_simp
    -- The weighted mean of `p` is `1/n` (since `∑ pᵢ = 1`).
    have hmean : (∑ i : ι, ((n : ℝ)⁻¹) • p i) = (n : ℝ)⁻¹ := by
      simp only [smul_eq_mul, ← Finset.mul_sum, hsum, mul_one]
    -- `negMulLog (1/n) = (1/n) * log n`.
    have hval : Real.negMulLog ((n : ℝ)⁻¹) = (n : ℝ)⁻¹ * Real.log n := by
      rw [Real.negMulLog, Real.log_inv]; ring
    -- Equality in Jensen: `negMulLog(mean) = ∑ (1/n)·negMulLog(pᵢ)`.
    have h_eq : Real.negMulLog (∑ i : ι, ((n : ℝ)⁻¹) • p i)
        = ∑ i : ι, ((n : ℝ)⁻¹) • Real.negMulLog (p i) := by
      have hlhs : (∑ i : ι, ((n : ℝ)⁻¹) • Real.negMulLog (p i))
          = (n : ℝ)⁻¹ * shannonEntropy p := by
        simp only [smul_eq_mul, shannonEntropy, Finset.mul_sum]
      rw [hmean, hval, hlhs, hH]
    -- Strict concavity ⇒ all entries of `p` are equal.
    have hall : ∀ ⦃j⦄, j ∈ (Finset.univ : Finset ι) → ∀ ⦃k⦄,
        k ∈ (Finset.univ : Finset ι) → p j = p k :=
      Real.strictConcaveOn_negMulLog.eq_of_map_sum_eq
        (t := Finset.univ) (w := fun _ => (n : ℝ)⁻¹) (p := p)
        (fun i _ => by positivity) hwsum
        (fun i _ => Set.mem_Ici.mpr (h0 i)) h_eq.le
    -- All entries equal + normalization ⇒ each equals `1/n`.
    intro i
    have hconst : ∀ j, p j = p i := fun j =>
      hall (Finset.mem_univ j) (Finset.mem_univ i)
    have hni : (n : ℝ) * p i = 1 := by
      calc (n : ℝ) * p i = ∑ _j : ι, p i := by
              rw [Finset.sum_const, Finset.card_univ, ← hn, nsmul_eq_mul]
        _ = ∑ j : ι, p j := Finset.sum_congr rfl (fun j _ => (hconst j).symm)
        _ = 1 := hsum
    exact eq_inv_of_mul_eq_one_right hni
  · intro hp
    have hpu : p = (fun _ : ι => (Fintype.card ι : ℝ)⁻¹) := funext hp
    rw [hpu, hn]
    exact shannonEntropy_uniform

/-- Relative entropy (Kullback–Leibler divergence) of two finite probability vectors,
`D(p ‖ q) = ∑ᵢ pᵢ (log pᵢ − log qᵢ)`. This is the discrete counterpart of the continuous
KL divergence; it measures the information lost when `q` is used to approximate `p`. -/
noncomputable def klDivergence (p q : ι → ℝ) : ℝ :=
  ∑ i, p i * (Real.log (p i) - Real.log (q i))

/-- **Gibbs' inequality** (discrete relative-entropy nonnegativity). For probability
vectors `p, q` with `q` absolutely continuous with respect to `p` (`qᵢ > 0` whenever
`pᵢ > 0`), the Kullback–Leibler divergence is nonnegative: `D(p ‖ q) ≥ 0`.

Proof: it suffices to bound `−D(p ‖ q) = ∑ᵢ pᵢ (log qᵢ − log pᵢ)` above by `0`. Termwise,
`pᵢ log(qᵢ/pᵢ) ≤ pᵢ (qᵢ/pᵢ − 1) = qᵢ − pᵢ` using the elementary inequality
`log x ≤ x − 1` (`Real.log_le_sub_one_of_pos`); the degenerate terms `pᵢ = 0` give
`0 ≤ qᵢ`. Summing, `−D ≤ ∑ᵢ (qᵢ − pᵢ) = 1 − 1 = 0`.

Gibbs' inequality is the engine behind the maximum-entropy bound (`q` uniform recovers
`H(p) ≤ log n`) and is the foundational positivity statement underlying any
information-theoretic uncertainty relation. -/
theorem klDivergence_nonneg {p q : ι → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hq0 : ∀ i, 0 ≤ q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1)
    (hac : ∀ i, 0 < p i → 0 < q i) :
    0 ≤ klDivergence p q := by
  -- Termwise bound on the *negated* summand: `pᵢ (log qᵢ − log pᵢ) ≤ qᵢ − pᵢ`.
  have hkey : ∀ i, p i * (Real.log (q i) - Real.log (p i)) ≤ q i - p i := by
    intro i
    rcases eq_or_lt_of_le (hp0 i) with hpi | hpi
    · -- `pᵢ = 0`: the summand is `0`, and `qᵢ − 0 = qᵢ ≥ 0`.
      rw [← hpi]; simpa using hq0 i
    · -- `0 < pᵢ`, hence `0 < qᵢ` by absolute continuity.
      have hqi : 0 < q i := hac i hpi
      have hlog : Real.log (q i) - Real.log (p i) = Real.log (q i / p i) := by
        rw [Real.log_div (ne_of_gt hqi) (ne_of_gt hpi)]
      rw [hlog]
      have hbound : Real.log (q i / p i) ≤ q i / p i - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hqi hpi)
      calc p i * Real.log (q i / p i)
          ≤ p i * (q i / p i - 1) := mul_le_mul_of_nonneg_left hbound (le_of_lt hpi)
        _ = q i - p i := by field_simp
  -- Sum the bound: `∑ pᵢ (log qᵢ − log pᵢ) ≤ ∑ (qᵢ − pᵢ) = 0`.
  have hsum_le : (∑ i, p i * (Real.log (q i) - Real.log (p i))) ≤ ∑ i, (q i - p i) :=
    Finset.sum_le_sum (fun i _ => hkey i)
  have hsum_zero : (∑ i, (q i - p i)) = 0 := by
    rw [Finset.sum_sub_distrib, hqsum, hpsum, sub_self]
  -- The negated sum and `D(p ‖ q)` cancel termwise.
  have hcancel :
      klDivergence p q + (∑ i, p i * (Real.log (q i) - Real.log (p i))) = 0 := by
    unfold klDivergence
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero (fun i _ => by ring)
  linarith [hsum_le.trans hsum_zero.le]

/-- `D(p ‖ p) = 0`: the relative entropy of a probability vector with itself vanishes
(no information is lost). Combined with `klDivergence_nonneg`, `p` is the unique
minimizer of `D(· ‖ p)`. -/
theorem klDivergence_self (p : ι → ℝ) : klDivergence p p = 0 := by
  unfold klDivergence
  exact Finset.sum_eq_zero (fun i _ => by ring)

end CauchySchwarzOQ01OQ03OQ02
