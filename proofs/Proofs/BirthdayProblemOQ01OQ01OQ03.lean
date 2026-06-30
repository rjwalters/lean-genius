/-
  Birthday Problem — OQ01/OQ01/OQ03: Non-uniform collision count.

  Open question (from the parent `BirthdayProblemOQ01OQ01`): does the
  collision-count analysis generalize to *non-uniform* day probabilities,
  the setting relevant to hash-collision analysis in cryptography?

  The parent file formalizes the **uniform** model (assignments
  `f : Fin n → Fin d` under the counting measure, per-pair collision
  probability `1/d`, `E[X] = C(n,2)/d`). Here we record the non-uniform
  generalization at the same definitional rigor: a probability vector
  `p : Fin d → ℝ` with `∑ p k = 1` replaces the uniform weights, the
  per-pair collision probability becomes the **coincidence index**
  `∑ k, (p k)²`, and the expected collision count is `C(n,2) · ∑ (p k)²`.

  Main results:
  * `collisionProb_uniform` — uniform `p ≡ 1/d` recovers `∑ (p k)² = 1/d`.
  * `collisionProb_ge`      — `∑ (p k)² ≥ 1/d` for any distribution
                              (uniform MINIMIZES expected collisions).
  * `collisionProb_eq_iff_uniform` — equality holds iff `p` is uniform.
  * `expectedCollisions_ge` / `expectedCollisions_uniform` — the
                              corresponding statements for the expected
                              collision count `C(n,2) · ∑ (p k)²`.

  The single sum-of-squares identity `sos_identity`
  (`∑ (p k − 1/d)² = ∑ (p k)² − 1/d`) supplies both the sharp lower bound
  and its equality case, so no Cauchy–Schwarz infrastructure is required.

  See `BirthdayProblemOQ01OQ01.lean` for the uniform model this builds on.
-/
import Mathlib
import Proofs.BirthdayProblemOQ01OQ01

open BigOperators

namespace BirthdayDistributionNonUniform

variable {d : ℕ} (p : Fin d → ℝ)

/-- Per-pair collision probability for a day-distribution `p`: the
    probability that two independent items land on the same day,
    `∑ k, (p k)²` (the cryptographic "coincidence index"). -/
noncomputable def collisionProb : ℝ := ∑ k, (p k) ^ 2

/-- Expected collision count among `n` items: `C(n,2) · ∑ (p k)²`, by
    linearity of expectation over the `C(n,2)` pair indicators. -/
noncomputable def expectedCollisions (n : ℕ) : ℝ :=
  (n.choose 2 : ℝ) * collisionProb p

/-- (T1) Recovery of the parent uniform model: with `p ≡ 1/d` the
    coincidence index is `∑ (1/d)² = d · 1/d² = 1/d`. -/
theorem collisionProb_uniform (hd : 0 < d) :
    collisionProb (fun _ => (1 : ℝ) / d) = 1 / d := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  simp only [collisionProb, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

/-- The exact sum-of-squares identity: the squared deviation of `p` from
    uniform equals the excess of the coincidence index over `1/d`.  This
    is the engine for both the lower bound and its equality case. -/
theorem sos_identity (hsum : ∑ k, p k = 1) (hd : 0 < d) :
    ∑ k, (p k - 1 / (d : ℝ)) ^ 2 = collisionProb p - 1 / (d : ℝ) := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  unfold collisionProb
  have step : ∀ k, (p k - 1 / (d : ℝ)) ^ 2
      = (p k) ^ 2 + ((-2 / (d : ℝ)) * p k + (1 / (d : ℝ)) ^ 2) := by
    intro k; ring
  rw [Finset.sum_congr rfl (fun k _ => step k)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsum,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hconst : (-2 / (d : ℝ)) * 1 + (d : ℝ) * (1 / (d : ℝ)) ^ 2 = -(1 / (d : ℝ)) := by
    field_simp
    ring
  rw [hconst]
  ring

/-- (T2) Cauchy–Schwarz lower bound, sum-of-squares form: the uniform
    distribution MINIMIZES the expected number of collisions.  Any
    distribution has coincidence index at least `1/d`. -/
theorem collisionProb_ge (hsum : ∑ k, p k = 1) (hd : 0 < d) :
    1 / (d : ℝ) ≤ collisionProb p := by
  have h := sos_identity p hsum hd
  have hnn : 0 ≤ ∑ k, (p k - 1 / (d : ℝ)) ^ 2 :=
    Finset.sum_nonneg (fun k _ => sq_nonneg _)
  linarith

/-- (T3) Equality characterization: the coincidence index attains its
    minimum `1/d` exactly when `p` is the uniform distribution. -/
theorem collisionProb_eq_iff_uniform (hsum : ∑ k, p k = 1) (hd : 0 < d) :
    collisionProb p = 1 / (d : ℝ) ↔ ∀ k, p k = 1 / (d : ℝ) := by
  constructor
  · intro heq
    have h := sos_identity p hsum hd
    rw [heq] at h
    have hzero : ∑ k, (p k - 1 / (d : ℝ)) ^ 2 = 0 := by linarith
    intro k
    have hk : (p k - 1 / (d : ℝ)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg _)).mp hzero k
        (Finset.mem_univ k)
    have : p k - 1 / (d : ℝ) = 0 := by
      exact sq_eq_zero_iff.mp hk
    linarith
  · intro hunif
    have hp : p = (fun _ => (1 : ℝ) / d) := funext hunif
    rw [hp, collisionProb_uniform hd]

/-- (T4) Expected-collision consequence: non-uniformity never decreases the
    expected number of collisions below the uniform value `C(n,2)/d`. -/
theorem expectedCollisions_ge (n : ℕ) (hsum : ∑ k, p k = 1) (hd : 0 < d) :
    (n.choose 2 : ℝ) * (1 / (d : ℝ)) ≤ expectedCollisions p n := by
  unfold expectedCollisions
  apply mul_le_mul_of_nonneg_left (collisionProb_ge p hsum hd)
  positivity

/-- The uniform expected collision count is the parent's `C(n,2)/d`. -/
theorem expectedCollisions_uniform (n : ℕ) (hd : 0 < d) :
    expectedCollisions (fun _ => (1 : ℝ) / d) n = (n.choose 2 : ℝ) / (d : ℝ) := by
  unfold expectedCollisions
  rw [collisionProb_uniform hd, mul_one_div]

end BirthdayDistributionNonUniform
