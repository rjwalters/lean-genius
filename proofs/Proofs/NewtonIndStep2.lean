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

    Proof: express LHS-RHS as quadratic αt²+βt+γ and apply quadratic_nonneg. -/
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
  -- Define the quadratic coefficients
  set γ := ek ^ 2 * ((b + a) * (d + c)) - ekm1 * ekp1 * (c + b) ^ 2
  set α := ekm1 ^ 2 * ((b + a) * (d + c)) - ekm2 * ek * (c + b) ^ 2
  set β := 2 * ek * ekm1 * ((b + a) * (d + c)) - (ek * ekm1 + ekm2 * ekp1) * (c + b) ^ 2
  -- The goal is equivalent to α*t² + β*t + γ ≥ 0
  suffices hsuff : α * t ^ 2 + β * t + γ ≥ 0 by nlinarith [hsuff]
  apply quadratic_nonneg α β γ t ht
  · -- α ≥ 0: ekm1²*(b+a)(d+c) ≥ ekm2*ek*(c+b)²
    -- Use h_ih_km1 (ekm1²*ac ≥ ekm2*ek*b²) and binom coefficient structure
    -- Key: (b+a)(d+c) = bd+bc+ad+ac and (c+b)² = c²+2bc+b²
    -- α = ekm1²*(bd+bc+ad+ac) - ekm2*ek*(c²+2bc+b²)
    --   = (ekm1²*ac - ekm2*ek*b²) + ekm1²*bd + ekm1²*bc + ekm1²*ad
    --     - ekm2*ek*c² - 2*ekm2*ek*bc
    --   ≥ 0 + ekm1²*bd + bc*(ekm1²-2*ekm2*ek) + ekm1²*ad - ekm2*ek*c²
    -- From h_unn_km1: ekm1² ≥ ekm2*ek, so ekm1²-2*ekm2*ek could be negative.
    -- Better: use (ekm1²-ekm2*ek)*bd ≥ 0 and (ekm1²-ekm2*ek)*bc ≥ 0
    -- Then: α = (ekm1²*ac-ekm2*ek*b²) + (ekm1²-ekm2*ek)*(bd+bc)
    --          + ekm1²*ad - ekm2*ek*(c²+bc)
    -- Still messy. Try nlinarith with products.
    nlinarith [h_ih_km1, h_unn_km1,
               mul_nonneg hekm1 hekm1,
               mul_nonneg hekm2 hek,
               mul_nonneg hb_nn hd_nn,
               mul_nonneg ha_nn hd_nn,
               mul_nonneg hb_nn hc_nn,
               mul_nonneg ha_nn hc_nn,
               sq_nonneg ekm1,
               sq_nonneg (ekm1 * c - ekm2 * b),
               sq_nonneg (ekm1 * d),
               mul_self_nonneg (ekm1 * b - ek * a),
               mul_nonneg (mul_nonneg hekm1 hekm1) (mul_nonneg hb_nn hd_nn),
               mul_nonneg (mul_nonneg hekm1 hekm1) (mul_nonneg ha_nn hd_nn)]
  · -- γ ≥ 0: ek²*(b+a)(d+c) ≥ ekm1*ekp1*(c+b)²
    -- Analogous to α using h_ih_k
    nlinarith [h_ih_k, h_unn_k,
               mul_nonneg hek hek,
               mul_nonneg hekm1 hekp1,
               mul_nonneg hb_nn hc_nn,
               mul_nonneg ha_nn hd_nn,
               mul_nonneg ha_nn hc_nn,
               sq_nonneg (ek * c - ekm1 * b),
               sq_nonneg (ek * b - ekp1 * a),
               sq_nonneg (ek * d),
               mul_nonneg (mul_nonneg hek hek) (mul_nonneg ha_nn hd_nn),
               mul_nonneg (mul_nonneg hek hek) (mul_nonneg hb_nn hc_nn),
               mul_nonneg (mul_nonneg hek hek) (mul_nonneg ha_nn hc_nn)]
  · -- 4αγ ≥ β²: the discriminant condition
    -- This is the hardest part. Use Cauchy-Schwarz style argument.
    -- 4αγ = 4*(ekm1²*(b+a)(d+c) - ekm2*ek*(c+b)²)*(ek²*(b+a)(d+c) - ekm1*ekp1*(c+b)²)
    -- β² = (2*ek*ekm1*(b+a)(d+c) - (ek*ekm1+ekm2*ekp1)*(c+b)²)²
    -- Let P = (b+a)(d+c), Q = (c+b)²
    -- 4αγ = 4*(ekm1²*P - ekm2*ek*Q)*(ek²*P - ekm1*ekp1*Q)
    -- β = 2*ek*ekm1*P - (ek*ekm1+ekm2*ekp1)*Q = ek*ekm1*(2P-Q) - ekm2*ekp1*Q
    -- β² ≤ ... need Cauchy-Schwarz on the "mixed" term
    --
    -- Alternative: 4αγ - β² after expansion. This is degree 4 in elem symms × degree 2 in binom coeffs.
    -- Try nlinarith with many hints.
    nlinarith [h_ih_k, h_ih_km1, h_unn_k, h_unn_km1, h_cross,
               h_binom_k, h_binom_km1,
               sq_nonneg (ek * ekm1 * (b + a) * (d + c) - ekm2 * ekp1 * (c + b) ^ 2),
               sq_nonneg (ek ^ 2 * ekm1 * d - ekm1 * ekp1 * ek * b),
               sq_nonneg (ekm1 ^ 2 * ek * c - ekm2 * ek ^ 2 * b),
               sq_nonneg (ek * ekm1 * c - ekm1 * ekp1 * b),
               sq_nonneg (ekm1 ^ 2 * c - ekm2 * ek * b),
               sq_nonneg (ek * c - ekm1 * b),
               sq_nonneg (ekm1 * c - ekm2 * b),
               mul_nonneg (sub_nonneg.mpr h_unn_k) (sub_nonneg.mpr h_unn_km1),
               mul_nonneg (sub_nonneg.mpr h_unn_k) (mul_nonneg hb_nn hd_nn),
               mul_nonneg (sub_nonneg.mpr h_unn_km1) (mul_nonneg ha_nn hc_nn),
               mul_nonneg (sub_nonneg.mpr h_cross) (sub_nonneg.mpr h_cross),
               mul_nonneg (sub_nonneg.mpr h_ih_k) (sub_nonneg.mpr h_ih_km1),
               mul_self_nonneg (ek * ekm1 * b * d - ekm2 * ekp1 * b * c),
               mul_self_nonneg (ek * ekm1 * a * c - ekm2 * ekp1 * a * b)]

end NewtonIndStep2
