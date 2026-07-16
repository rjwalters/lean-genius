/-
  Newton's log-concavity inductive step: alternative proof via quadratic_nonneg.
  Proves newton_cleared_denom_inductive_step by expressing LHS-RHS as a quadratic
  in t and showing α≥0, γ≥0, 4αγ≥β² using absorption identities.
-/
import Proofs.NewtonInductiveStep

open Finset Real

namespace NewtonIndStep2

/-- The inductive step of Newton's cleared-denominator inequality.
    After Pascal expansion, we must show:
    (ek + t·ekm1)² · (b+a)(d+c) ≥ (ekm1+t·ekm2)(ekp1+t·ek) · (c+b)²
    where a=C(m,k-2), b=C(m,k-1), c=C(m,k), d=C(m,k+1).

    Proof: express LHS-RHS as quadratic αt²+βt+γ. α ≥ 0 and γ ≥ 0 follow by chaining
    the "inductive hypothesis" bounds `h_ih_k`/`h_ih_km1` with the dual binomial
    inequalities `binom_ineq_dual`/`binom_ineq` (both proved in `NewtonInductiveStep`
    via the absorption identities) and dividing out `b² > 0` / `c² > 0`. When β ≤ 0
    the discriminant condition `4αγ ≥ β²` is exactly `newton_disc_of_beta_nonpos`
    from `NewtonInductiveStep`; when β > 0 the quadratic is trivially non-negative
    for `t ≥ 0` since α, γ, β, t are all non-negative. -/
theorem newton_ind_step (m k : ℕ) (hk : 2 ≤ k) (hkm : k + 1 ≤ m)
    (ek ekm1 ekp1 ekm2 t : ℝ)
    (ht : 0 ≤ t) (hek : 0 ≤ ek) (hekm1 : 0 ≤ ekm1)
    (hekp1 : 0 ≤ ekp1) (hekm2 : 0 ≤ ekm2)
    (h_unn_k : ek ^ 2 ≥ ekm1 * ekp1)
    (h_unn_km1 : ekm1 ^ 2 ≥ ekm2 * ek)
    (h_cross : ek * ekm1 ≥ ekm2 * ekp1)
    (a b c d : ℝ)
    (ha : a = (Nat.choose m (k - 2) : ℝ))
    (hb : b = (Nat.choose m (k - 1) : ℝ))
    (hc : c = (Nat.choose m k : ℝ))
    (hd : d = (Nat.choose m (k + 1) : ℝ))
    (h_ih_k : ek ^ 2 * (b * d) ≥ ekm1 * ekp1 * c ^ 2)
    (h_ih_km1 : ekm1 ^ 2 * (a * c) ≥ ekm2 * ek * b ^ 2)
    -- Absorption identities
    (abs1 : (k : ℝ) * c = ((m : ℝ) - k + 1) * b)
    (abs2 : ((k : ℝ) + 1) * d = ((m : ℝ) - k) * c)
    (abs3 : ((k : ℝ) - 1) * b = ((m : ℝ) - k + 2) * a)
    -- Binomial non-negativity
    (ha_nn : 0 ≤ a) (hb_nn : 0 ≤ b) (hc_nn : 0 ≤ c) (hd_nn : 0 ≤ d)
    -- Binomial log-concavity
    (h_binom_k : c ^ 2 ≥ b * d)
    (h_binom_km1 : b ^ 2 ≥ a * c) :
    (ek + t * ekm1) ^ 2 * ((b + a) * (d + c)) ≥
    (ekm1 + t * ekm2) * (ekp1 + t * ek) * (c + b) ^ 2 := by
  -- Strict positivity of the four binomial coefficients (needed by NewtonInductiveStep
  -- lemmas, which require `0 < a` etc. rather than merely `0 ≤ a`).
  have ha_pos : 0 < a := by rw [ha]; exact_mod_cast Nat.choose_pos (show k - 2 ≤ m by omega)
  have hb_pos : 0 < b := by rw [hb]; exact_mod_cast Nat.choose_pos (show k - 1 ≤ m by omega)
  have hc_pos : 0 < c := by rw [hc]; exact_mod_cast Nat.choose_pos (show k ≤ m by omega)
  have hd_pos : 0 < d := by rw [hd]; exact_mod_cast Nat.choose_pos (show k + 1 ≤ m by omega)
  -- Dual binomial inequalities, proved exactly (via `linear_combination` against the
  -- absorption identities) in `NewtonInductiveStep`.
  have hdualb : b ^ 2 * ((b + a) * (d + c)) ≥ a * c * (c + b) ^ 2 := by
    rw [ha, hb, hc, hd]; exact binom_ineq_dual m k hk hkm
  have hccbd : c ^ 2 * ((b + a) * (d + c)) ≥ b * d * (c + b) ^ 2 := by
    have hbi : b * c ^ 3 + a * d * c ^ 2 + a * c ^ 3 ≥ 2 * b ^ 2 * c * d + b ^ 3 * d := by
      rw [ha, hb, hc, hd]; exact binom_ineq m k hk hkm
    nlinarith [hbi]
  -- α ≥ 0: chain h_ih_km1 with hdualb (each multiplied by a nonneg factor), then
  -- divide out b² > 0.
  have hα : 0 ≤ ekm1 ^ 2 * ((b + a) * (d + c)) - ekm2 * ek * (c + b) ^ 2 := by
    have hb2 : 0 < b ^ 2 := pow_pos hb_pos 2
    have t1 : 0 ≤ ekm1 ^ 2 * (b ^ 2 * ((b + a) * (d + c)) - a * c * (c + b) ^ 2) :=
      mul_nonneg (sq_nonneg ekm1) (by linarith [hdualb])
    have t2 : 0 ≤ (ekm1 ^ 2 * (a * c) - ekm2 * ek * b ^ 2) * (c + b) ^ 2 :=
      mul_nonneg (by linarith [h_ih_km1]) (sq_nonneg (c + b))
    have heq : ekm1 ^ 2 * (b ^ 2 * ((b + a) * (d + c)) - a * c * (c + b) ^ 2) +
        (ekm1 ^ 2 * (a * c) - ekm2 * ek * b ^ 2) * (c + b) ^ 2 =
        b ^ 2 * (ekm1 ^ 2 * ((b + a) * (d + c)) - ekm2 * ek * (c + b) ^ 2) := by ring
    have key : 0 ≤ b ^ 2 * (ekm1 ^ 2 * ((b + a) * (d + c)) - ekm2 * ek * (c + b) ^ 2) := by
      rw [← heq]; linarith [t1, t2]
    by_contra hcon
    push_neg at hcon
    exact absurd key (by linarith [mul_neg_of_pos_of_neg hb2 hcon])
  -- γ ≥ 0: chain h_ih_k with hccbd, then divide out c² > 0.
  have hγ : 0 ≤ ek ^ 2 * ((b + a) * (d + c)) - ekm1 * ekp1 * (c + b) ^ 2 := by
    have hc2 : 0 < c ^ 2 := pow_pos hc_pos 2
    have t1 : 0 ≤ ek ^ 2 * (c ^ 2 * ((b + a) * (d + c)) - b * d * (c + b) ^ 2) :=
      mul_nonneg (sq_nonneg ek) (by linarith [hccbd])
    have t2 : 0 ≤ (ek ^ 2 * (b * d) - ekm1 * ekp1 * c ^ 2) * (c + b) ^ 2 :=
      mul_nonneg (by linarith [h_ih_k]) (sq_nonneg (c + b))
    have heq : ek ^ 2 * (c ^ 2 * ((b + a) * (d + c)) - b * d * (c + b) ^ 2) +
        (ek ^ 2 * (b * d) - ekm1 * ekp1 * c ^ 2) * (c + b) ^ 2 =
        c ^ 2 * (ek ^ 2 * ((b + a) * (d + c)) - ekm1 * ekp1 * (c + b) ^ 2) := by ring
    have key : 0 ≤ c ^ 2 * (ek ^ 2 * ((b + a) * (d + c)) - ekm1 * ekp1 * (c + b) ^ 2) := by
      rw [← heq]; linarith [t1, t2]
    by_contra hcon
    push_neg at hcon
    exact absurd key (by linarith [mul_neg_of_pos_of_neg hc2 hcon])
  suffices hsuff :
      (ekm1 ^ 2 * ((b + a) * (d + c)) - ekm2 * ek * (c + b) ^ 2) * t ^ 2 +
      (2 * ek * ekm1 * ((b + a) * (d + c)) -
        (ek * ekm1 + ekm2 * ekp1) * (c + b) ^ 2) * t +
      (ek ^ 2 * ((b + a) * (d + c)) - ekm1 * ekp1 * (c + b) ^ 2) ≥ 0 by
    nlinarith [hsuff]
  by_cases hβ :
      2 * ek * ekm1 * ((b + a) * (d + c)) - (ek * ekm1 + ekm2 * ekp1) * (c + b) ^ 2 ≤ 0
  · -- β ≤ 0: the discriminant condition 4αγ ≥ β² is exactly
    -- `newton_disc_of_beta_nonpos` after transporting the absorption identities
    -- to the normalized `r = m - k + 1` form it expects.
    have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have hkm' : (k : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hkm
    set r : ℝ := (m : ℝ) - (k : ℝ) + 1 with hr_def
    have hr' : (2 : ℝ) ≤ r := by rw [hr_def]; linarith
    have h1 : (k : ℝ) * c = r * b := by rw [hr_def]; linear_combination abs1
    have h2 : ((k : ℝ) + 1) * d = (r - 1) * c := by rw [hr_def]; linear_combination abs2
    have h3 : (r + 1) * a = ((k : ℝ) - 1) * b := by rw [hr_def]; linear_combination -abs3
    have hbeta : 2 * ek * ekm1 * ((b + a) * (d + c)) ≤
        (ek * ekm1 + ekm2 * ekp1) * (c + b) ^ 2 := by linarith [hβ]
    have hdisc := newton_disc_of_beta_nonpos
      (k : ℝ) r a b c d hk' hr' ha_pos hb_pos hc_pos hd_pos h1 h2 h3
      ekm2 ekm1 ek ekp1 hekm2 hekm1 hek hekp1 h_ih_k h_ih_km1 h_cross hbeta
    have := quadratic_nonneg
      (ekm1 ^ 2 * ((b + a) * (d + c)) - ekm2 * ek * (c + b) ^ 2)
      (2 * ek * ekm1 * ((b + a) * (d + c)) - (ek * ekm1 + ekm2 * ekp1) * (c + b) ^ 2)
      (ek ^ 2 * ((b + a) * (d + c)) - ekm1 * ekp1 * (c + b) ^ 2)
      t ht hα hγ hdisc
    linarith [this]
  · -- β > 0: the quadratic is trivially non-negative for t ≥ 0, without needing
    -- the discriminant at all.
    push_neg at hβ
    have e1 : 0 ≤
        (ekm1 ^ 2 * ((b + a) * (d + c)) - ekm2 * ek * (c + b) ^ 2) * t ^ 2 :=
      mul_nonneg hα (sq_nonneg t)
    have e2 : 0 ≤
        (2 * ek * ekm1 * ((b + a) * (d + c)) -
          (ek * ekm1 + ekm2 * ekp1) * (c + b) ^ 2) * t :=
      mul_nonneg hβ.le ht
    linarith [e1, e2, hγ]

end NewtonIndStep2
