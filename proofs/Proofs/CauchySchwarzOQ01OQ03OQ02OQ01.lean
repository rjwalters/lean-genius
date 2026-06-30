/-
  Entropic Uncertainty — OQ-01-OQ-03-OQ-02-OQ-01:
  The min-entropy lower bound and the EIGENSTATE case of Maassen–Uffink.

  ## Question
  The parent entry (`cauchy-schwarz-oq-01-oq-03-oq-02`) builds the finite Shannon-
  entropy infrastructure for the entropic uncertainty principle (Maassen–Uffink
  1988): for outcome distributions `p, q` of measuring a state in two orthonormal
  bases of maximal overlap `c`, `H(p) + H(q) ≥ -2 ln c`. It proves the entropy
  *ceiling* `H ≤ log n` but notes the *lower* bound on `H(p) + H(q)` is gated on
  Riesz–Thorin / Hausdorff–Young interpolation, absent from Mathlib.

  This file supplies what IS provable elementarily: the **min-entropy lower bound**
  `H(p) ≥ -log(max_i p_i)` (equivalently `H(p) ≥ -log M` whenever every `p_i ≤ M`),
  and the resulting **eigenstate case** of the Maassen–Uffink relation. When the
  measured state is a basis vector of the first basis, `H(p) = 0` and every outcome
  probability in the second basis is bounded by the squared overlap `q_k ≤ c²`,
  so `H(p) + H(q) ≥ 0 + (-log c²) = -2 log c`. This is a genuine special case of
  the full theorem, proved with no interpolation theory.

  ## What this file delivers (0 axioms, 0 sorries)
  * `negMulLog_ge_mul_neg_log` — pointwise: `x·(-log M) ≤ negMulLog x` for `0 ≤ x ≤ M`.
  * `shannonEntropy_ge_neg_log_of_max` — the min-entropy bound: if every `p_i ≤ M`
    (`M > 0`) and `∑ p_i = 1`, then `H(p) ≥ -log M`.
  * `shannonEntropy_point_mass` — a deterministic distribution has `H = 0`.
  * `maassen_uffink_eigenstate` — the EUP lower bound `-2 log c ≤ H(p) + H(q)` in the
    eigenstate case (`p` a point mass, `q_k ≤ c²`).

  ## References
  - H. Maassen, J. Uffink, *Generalized entropic uncertainty relations*,
    Phys. Rev. Lett. 60 (1988).
  - D. Deutsch, *Uncertainty in quantum measurements*, Phys. Rev. Lett. 50 (1983).

  Tags: information-theory, entropy, uncertainty-principle, quantum-information, cauchy-schwarz
-/

import Mathlib

open Finset

namespace CauchySchwarzOQ01OQ03OQ02OQ01

variable {ι : Type*} [Fintype ι]

/-- Shannon entropy of a finite probability vector `p` (in nats):
`H(p) = ∑ᵢ negMulLog(pᵢ) = -∑ᵢ pᵢ log pᵢ`, via Mathlib's `Real.negMulLog`. -/
noncomputable def shannonEntropy (p : ι → ℝ) : ℝ :=
  ∑ i, Real.negMulLog (p i)

-- ============================================================
-- SECTION I: The pointwise min-entropy inequality
-- ============================================================

/-- **Pointwise bound.** For `0 ≤ x ≤ M` with `0 < M`, `x·(-log M) ≤ negMulLog x`.
This is the term that, summed against a probability vector, yields the min-entropy
bound `H(p) ≥ -log M`. -/
theorem negMulLog_ge_mul_neg_log (M x : ℝ) (_hM : 0 < M) (hx0 : 0 ≤ x) (hxM : x ≤ M) :
    x * (-Real.log M) ≤ Real.negMulLog x := by
  rcases eq_or_lt_of_le hx0 with hx | hpos
  · simp [← hx, Real.negMulLog]
  · have hlog : Real.log x ≤ Real.log M := Real.log_le_log hpos hxM
    rw [Real.negMulLog]
    nlinarith [mul_le_mul_of_nonneg_left hlog hx0]

-- ============================================================
-- SECTION II: The min-entropy lower bound on Shannon entropy
-- ============================================================

/-- **Min-entropy bound.** If every outcome probability satisfies `p_i ≤ M` for some
`M > 0` and `∑ p_i = 1`, then `H(p) ≥ -log M`. Instantiated with `M = max_i p_i`
this is the standard fact `H(p) ≥ H_∞(p) = -log(max_i p_i)`: Shannon entropy is at
least the min-entropy. -/
theorem shannonEntropy_ge_neg_log_of_max {p : ι → ℝ} (M : ℝ) (hM : 0 < M)
    (h0 : ∀ i, 0 ≤ p i) (hub : ∀ i, p i ≤ M) (hsum : ∑ i, p i = 1) :
    -Real.log M ≤ shannonEntropy p := by
  have hterm : ∑ i, p i * (-Real.log M) ≤ ∑ i, Real.negMulLog (p i) :=
    Finset.sum_le_sum (fun i _ => negMulLog_ge_mul_neg_log M (p i) hM (h0 i) (hub i))
  calc -Real.log M = (∑ i, p i) * (-Real.log M) := by rw [hsum]; ring
    _ = ∑ i, p i * (-Real.log M) := by rw [Finset.sum_mul]
    _ ≤ shannonEntropy p := hterm

-- ============================================================
-- SECTION III: Deterministic distributions have zero entropy
-- ============================================================

/-- **Point mass.** A deterministic distribution (each entry `0` or `1`) has zero
Shannon entropy: `negMulLog 0 = negMulLog 1 = 0`. -/
theorem shannonEntropy_point_mass {p : ι → ℝ} (h : ∀ i, p i = 0 ∨ p i = 1) :
    shannonEntropy p = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rcases h i with h0 | h1
  · rw [h0]; simp [Real.negMulLog]
  · rw [h1]; simp [Real.negMulLog]

-- ============================================================
-- SECTION IV: The eigenstate case of Maassen–Uffink
-- ============================================================

/-- **Eigenstate Maassen–Uffink.** Measuring a basis vector of the first basis gives
a deterministic distribution `p` (`H(p) = 0`); in the second basis every outcome
probability is bounded by the squared maximal overlap, `q_k ≤ c²`. Then the entropic
uncertainty lower bound holds: `-2 log c ≤ H(p) + H(q)`.

This is the genuine `H(p) = 0` special case of the full Maassen–Uffink relation,
proved from the min-entropy bound alone — no Hausdorff–Young / Riesz–Thorin
interpolation, which the general case requires and Mathlib lacks. -/
theorem maassen_uffink_eigenstate {p q : ι → ℝ} (c : ℝ) (hc0 : 0 < c)
    (hp : ∀ i, p i = 0 ∨ p i = 1)
    (hq0 : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = 1) (hqub : ∀ i, q i ≤ c ^ 2) :
    -2 * Real.log c ≤ shannonEntropy p + shannonEntropy q := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hHq : -Real.log (c ^ 2) ≤ shannonEntropy q :=
    shannonEntropy_ge_neg_log_of_max (c ^ 2) hc2 hq0 hqub hqsum
  have hlog : Real.log (c ^ 2) = 2 * Real.log c := by
    rw [Real.log_pow]; push_cast; ring
  rw [hlog] at hHq
  rw [shannonEntropy_point_mass hp]
  linarith [hHq]

#check @negMulLog_ge_mul_neg_log
#check @shannonEntropy_ge_neg_log_of_max
#check @shannonEntropy_point_mass
#check @maassen_uffink_eigenstate

end CauchySchwarzOQ01OQ03OQ02OQ01
