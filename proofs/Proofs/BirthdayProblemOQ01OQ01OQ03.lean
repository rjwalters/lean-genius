/-
  Birthday Problem OQ-01-OQ-01-OQ-03: Non-Uniform Collision-Count Distribution

  Open Question (from parent `birthday-problem-oq-01-oq-01`): does the formal
  collision-count analysis generalize to *non-uniform* day distributions
  (unequal day probabilities) — the setting relevant to hash-collision analysis
  in cryptography?

  **Answer: Yes.** Model the days by a probability vector `p : Fin d → ℝ` with
  `0 ≤ p k` and `∑ k, p k = 1`. Each of the `n` items independently lands on day
  `k` with probability `p k`. The per-pair collision probability is then
  `collisionProb p = ∑ k, (p k)^2` (replacing the uniform `1/d`), so by linearity
  of expectation over the `C(n,2)` pair indicators,

      E[X] = expectedCollisions n p = C(n,2) · ∑ k, (p k)^2.

  The cryptographically meaningful statement is that **uniform minimizes
  expected collisions**: by Cauchy–Schwarz applied to `p` and the all-ones
  vector,

      1 = (∑ k, p k)^2 ≤ d · ∑ k, (p k)^2   ⟹   ∑ k, (p k)^2 ≥ 1/d,

  with equality iff `p` is uniform. Hence any non-uniformity strictly increases
  the expected collision count.

  This file matches the parent's *definitional* rigor (the parent defines
  `expectedPairs` as a closed formula rather than constructing a measure space),
  giving T1 (uniform recovery), T2 (Cauchy–Schwarz lower bound), T3 (equality
  characterization, forward direction), and T4 (monotone consequence). The
  Cauchy–Schwarz step is a verbatim port over ℝ of the induction proof in
  `ProbMethodSecondMoment.lean`.

  BUILD STATUS: not yet machine-checked — written during the 2026-06-13 Docker /
  `lake build` verification outage. Shipped as a draft pending a Docker build via
  `./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ01OQ03`.
-/
import Mathlib

namespace BirthdayDistributionNonUniform

open Finset

/-- Cauchy–Schwarz for finite sums over ℝ: `(∑ f)² ≤ |S| · ∑ f²`.
    Verbatim port of `ProbMethodSecondMoment.sq_sum_le_card_mul_sum_sq` from ℚ to ℝ
    (induction + `sub_sq` expansion + sum of squares ≥ 0). -/
private lemma sq_sum_le_card_mul_sum_sq {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → ℝ) :
    (s.sum f) ^ 2 ≤ ↑s.card * s.sum (fun a => f a ^ 2) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have hsq : 0 ≤ s.sum (fun b => (f a - f b) ^ 2) :=
      Finset.sum_nonneg (fun b _ => sq_nonneg _)
    have hexpand : s.sum (fun b => (f a - f b) ^ 2) =
        ↑s.card * (f a) ^ 2 - 2 * f a * s.sum f + s.sum (fun b => (f b) ^ 2) := by
      simp only [sub_sq, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.mul_sum]
      ring
    push_cast [Nat.cast_add, Nat.cast_one]
    nlinarith

variable {d : ℕ} (p : Fin d → ℝ)

/-- Per-pair collision probability for a day-distribution `p`: `∑ k, (p k)²`. -/
def collisionProb : ℝ := ∑ k, (p k) ^ 2

/-- Expected collision count among `n` items: `C(n,2) · ∑ k, (p k)²`. -/
def expectedCollisions (n : ℕ) : ℝ := (n.choose 2 : ℝ) * collisionProb p

theorem collisionProb_def : collisionProb p = ∑ k, (p k) ^ 2 := rfl

theorem expectedCollisions_def (n : ℕ) :
    expectedCollisions p n = (n.choose 2 : ℝ) * collisionProb p := rfl

/-- collisionProb is nonnegative. -/
theorem collisionProb_nonneg : 0 ≤ collisionProb p := by
  unfold collisionProb
  exact Finset.sum_nonneg (fun k _ => sq_nonneg (p k))

/-- (T1) Recovery of the parent: the uniform distribution `p ≡ 1/d` gives
    `collisionProb = 1/d`. -/
theorem collisionProb_uniform (hd : 0 < d) :
    collisionProb (fun _ : Fin d => (1 : ℝ) / d) = 1 / d := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold collisionProb
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- (T1') Expected-collision recovery: uniform `p ≡ 1/d` gives `C(n,2)/d`. -/
theorem expectedCollisions_uniform (hd : 0 < d) (n : ℕ) :
    expectedCollisions (fun _ : Fin d => (1 : ℝ) / d) n = (n.choose 2 : ℝ) / d := by
  unfold expectedCollisions
  rw [collisionProb_uniform hd]
  ring

/-- (T2) Cauchy–Schwarz lower bound: any probability vector has collision
    probability at least `1/d`, so uniform minimizes expected collisions. -/
theorem collisionProb_ge (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1) (hd : 0 < d) :
    1 / d ≤ collisionProb p := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hcs := sq_sum_le_card_mul_sum_sq (Finset.univ : Finset (Fin d)) p
  rw [Finset.card_univ, Fintype.card_fin] at hcs
  -- hcs : (univ.sum p) ^ 2 ≤ ↑d * univ.sum (fun a => p a ^ 2)
  have hsum' : (Finset.univ : Finset (Fin d)).sum p = 1 := hsum
  rw [hsum'] at hcs
  -- hcs : (1 : ℝ) ^ 2 ≤ ↑d * univ.sum (fun a => p a ^ 2)
  have hcp : (1 : ℝ) ≤ (d : ℝ) * collisionProb p := by
    have hcoll : collisionProb p = (Finset.univ : Finset (Fin d)).sum (fun a => p a ^ 2) := rfl
    rw [hcoll]
    nlinarith [hcs]
  rw [div_le_iff₀ hd']
  nlinarith [hcp]

/-- (T4) Monotone consequence: for any probability vector, the expected
    collision count is at least the uniform value `C(n,2)/d`. -/
theorem expectedCollisions_ge (hp : ∀ k, 0 ≤ p k) (hsum : ∑ k, p k = 1) (hd : 0 < d)
    (n : ℕ) : (n.choose 2 : ℝ) / d ≤ expectedCollisions p n := by
  unfold expectedCollisions
  have hcard : (0 : ℝ) ≤ (n.choose 2 : ℝ) := by positivity
  have hcp : 1 / d ≤ collisionProb p := collisionProb_ge p hp hsum hd
  have hstep : (n.choose 2 : ℝ) * (1 / d) ≤ (n.choose 2 : ℝ) * collisionProb p :=
    mul_le_mul_of_nonneg_left hcp hcard
  calc (n.choose 2 : ℝ) / d = (n.choose 2 : ℝ) * (1 / d) := by ring
    _ ≤ (n.choose 2 : ℝ) * collisionProb p := hstep

/-- (T3) Equality characterization (forward direction): if `p` is uniform then
    `collisionProb p = 1/d`. The converse (equality ⟹ uniform) follows from the
    Cauchy–Schwarz equality case; deferred per the ACT plan. -/
theorem collisionProb_eq_of_uniform (hd : 0 < d) :
    collisionProb (fun _ : Fin d => (1 : ℝ) / d) = 1 / d :=
  collisionProb_uniform hd

end BirthdayDistributionNonUniform
