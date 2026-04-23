import Mathlib
import Proofs.SolutionOfCubic
import Proofs.GeneralQuartic

open Polynomial Complex SolutionOfCubic GeneralQuartic

set_option maxHeartbeats 800000

/-!
# Solution of the Cubic: Connection to Quartic via Resolvent Cubic

**Open Question (from solution-of-cubic-oq-05)**:

How does Cardano's cubic formula (Wiedijk #37) connect to Ferrari's quartic
method (Wiedijk #46) through the resolvent cubic?

## Mathematical Content

Ferrari's method for the depressed quartic y⁴ + py² + qy + r = 0 introduces
the **resolvent cubic**:

  8m³ + 20pm² + (16p² − 8r)m + (4p³ − 4pr − q²) = 0

To apply Cardano's formula, we apply the **Tschirnhaus substitution**
  m = t − 5p/6   (subtracting b/(3a) = 20p/(3·8) = 5p/6)

which eliminates the quadratic term and produces the **depressed resolvent cubic**:

  t³ + P_r · t + Q_r = 0

where:
  P_r = −p²/12 − r
  Q_r =  pr/3 − p³/108 − q²/8

**Key identity**: (resolventCubic p q r).eval(t − 5p/6) = 8 · (depressedCubic P_r Q_r).eval(t)

Cardano's formula from `SolutionOfCubic.lean` gives an explicit root t₀ of the depressed form,
and m₀ = t₀ − 5p/6 is the required root of the resolvent cubic.

## Arithmetic Derivation of P_r and Q_r

Substituting m = t − 5p/6 into 8m³ + 20pm² + (16p²−8r)m + (4p³−4pr−q²) and collecting:
- Coefficient of t²: 8·(−3·5p/6) + 20p = −20p + 20p = 0  ✓ (quadratic term eliminated)
- Coefficient of t: 8·3·(5p/6)² − 20p·2·(5p/6) + (16p²−8r)
  = 50p²/3 − 100p²/3 + 16p² − 8r = −2p²/3 − 8r = 8·(−p²/12 − r) = 8·P_r  ✓
- Constant: (full expansion) = −2p³/27 + 8pr/3 − q² = 8·(pr/3 − p³/108 − q²/8) = 8·Q_r  ✓

## Status: 0 sorries, 0 axioms
-/

namespace SolutionOfCubicOQ05

/-! ## Part I: Tschirnhaus Parameters for the Resolvent Cubic -/

/-- The linear coefficient of the Tschirnhaus-reduced (depressed) resolvent cubic.

    After substituting m = t − 5p/6, the coefficient of t is:
    (25p²/12 − 50p²/12 + 24p²/12) − r = −p²/12 − r. -/
noncomputable def resolventP (p r : ℂ) : ℂ := -p ^ 2 / 12 - r

/-- The constant term of the Tschirnhaus-reduced (depressed) resolvent cubic.

    After the Tschirnhaus substitution, the constant term is:
    (−125p³/216 + 375p³/216 − 360p³/216 + 108p³/216) + (180pr/216 − 108pr/216) − q²/8
    = −2p³/27 + 8pr/3 − q²/8 = 8·(pr/3 − p³/108 − q²/8). -/
noncomputable def resolventQ (p q r : ℂ) : ℂ := p * r / 3 - p ^ 3 / 108 - q ^ 2 / 8

/-- The Tschirnhaus shift: b/(3a) = 20p/(3·8) = 5p/6, applied to go from resolvent to depressed. -/
noncomputable def tschirnhausShift (p : ℂ) : ℂ := 5 * p / 6

/-! ## Part II: Key Algebraic Identity — Tschirnhaus Reduction -/

/-- **Tschirnhaus Reduction Identity**: Evaluating the resolvent cubic at (t − 5p/6) gives
    exactly 8 times the Tschirnhaus-reduced depressed cubic evaluated at t.

    This is the algebraic heart of the connection between Cardano and Ferrari: it shows that
    solving the depressed cubic t³ + P_r·t + Q_r = 0 is equivalent to solving Ferrari's
    resolvent cubic (up to the shift m = t − 5p/6).

    Proof: direct ring computation — polynomial identity over ℂ. -/
theorem resolvent_tschirnhaus_identity (p q r t : ℂ) :
    (resolventCubic p q r).eval (t - tschirnhausShift p) =
    8 * (SolutionOfCubic.depressedCubic (resolventP p r) (resolventQ p q r)).eval t := by
  simp only [resolventCubic, SolutionOfCubic.depressedCubic,
             resolventP, resolventQ, tschirnhausShift,
             eval_add, eval_mul, eval_pow, eval_X, eval_C]
  ring

/-! ## Part III: Connection to Cardano's Formula -/

/-- **Main Theorem**: If u, v are Cardano cube roots satisfying
      u³ + v³ = −Q_r   and   u·v = −P_r/3
    (the conditions for `SolutionOfCubic.cardano_formula` applied to the depressed resolvent),
    then m₀ = (u + v) − 5p/6 is a root of Ferrari's resolvent cubic.

    This is the precise bridge between Wiedijk #37 (Cardano's cubic) and Wiedijk #46 (Ferrari's
    quartic): solving the resolvent cubic reduces to applying Cardano's formula to its
    Tschirnhaus reduction, then inverting the shift m = t − 5p/6. -/
theorem resolvent_root_via_cardano (p q r u v : ℂ)
    (h_sum : u ^ 3 + v ^ 3 = -(resolventQ p q r))
    (h_prod : u * v = -(resolventP p r) / 3) :
    (resolventCubic p q r).eval ((u + v) - tschirnhausShift p) = 0 := by
  rw [resolvent_tschirnhaus_identity]
  have hcard := SolutionOfCubic.cardano_formula u v (resolventP p r) (resolventQ p q r)
    h_sum h_prod
  rw [hcard, mul_zero]

/-! ## Part IV: Existence Results via FTA -/

/-- The depressed resolvent cubic always has a root over ℂ (Fundamental Theorem of Algebra). -/
theorem depressed_resolvent_has_root (p q r : ℂ) :
    ∃ t : ℂ,
      (SolutionOfCubic.depressedCubic (resolventP p r) (resolventQ p q r)).eval t = 0 := by
  have hcoeff :
      (SolutionOfCubic.depressedCubic (resolventP p r) (resolventQ p q r)).coeff 3 ≠ 0 := by
    simp only [SolutionOfCubic.depressedCubic, coeff_add, coeff_X_pow, coeff_C_mul,
               coeff_C, coeff_X]
    norm_num
  suffices hdeg :
      (SolutionOfCubic.depressedCubic (resolventP p r) (resolventQ p q r)).degree ≠ 0 from
    IsAlgClosed.exists_root _ hdeg
  intro h0
  exact hcoeff (by
    rw [Polynomial.eq_C_of_degree_le_zero (le_of_eq h0)]
    simp)

/-- **Alternative root existence**: every root of the depressed cubic lifts to a root of the
    resolvent cubic via the shift m = t − 5p/6. In particular, a root always exists. -/
theorem resolvent_has_root_via_tschirnhaus (p q r : ℂ) :
    ∃ m : ℂ, (resolventCubic p q r).eval m = 0 := by
  obtain ⟨t, ht⟩ := depressed_resolvent_has_root p q r
  exact ⟨t - tschirnhausShift p, by rw [resolvent_tschirnhaus_identity, ht, mul_zero]⟩

/-! ## Part V: Lifting Roots from Depressed to Resolvent Form -/

/-- **Corollary**: Every root of the depressed resolvent cubic, shifted by −5p/6,
    gives a root of the original resolvent cubic. -/
theorem depressed_root_lifts (p q r t : ℂ)
    (ht : (SolutionOfCubic.depressedCubic (resolventP p r) (resolventQ p q r)).eval t = 0) :
    (resolventCubic p q r).eval (t - tschirnhausShift p) = 0 := by
  rw [resolvent_tschirnhaus_identity, ht, mul_zero]

/-! ## Part VI: Numerical Parameter Verification -/

/-- **Parameter check (p=0, q=2, r=0)**:
    Resolvent cubic: 8m³ + 0 + 0 + (0 − 0 − 4) = 8m³ − 4 = 0, so m³ = 1/2.
    Depressed form: P_r = 0 − 0 = 0, Q_r = 0 − 0 − 4/8 = −1/2.
    No Tschirnhaus shift (p = 0), so t³ − 1/2 = 0, i.e., t = ∛(1/2). -/
theorem params_p0_q2_r0 :
    resolventP 0 0 = 0 ∧ resolventQ 0 2 0 = -(1 / 2) ∧ tschirnhausShift 0 = 0 := by
  refine ⟨by simp [resolventP], by simp [resolventQ]; norm_num, by simp [tschirnhausShift]⟩

/-- **Parameter check (p=−1, q=0, r=0)**:
    Resolvent cubic: 8m³ − 20m² + 16m + (−4) = 0.
    P_r = −(1)/12 − 0 = −1/12. Q_r = 0 − (−1)/108 − 0 = 1/108.
    Tschirnhaus shift: 5·(−1)/6 = −5/6. -/
theorem params_p_neg1_q0_r0 :
    resolventP (-1) 0 = -(1 / 12) ∧
    resolventQ (-1) 0 0 = 1 / 108 ∧
    tschirnhausShift (-1) = -(5 / 6) := by
  refine ⟨by simp [resolventP]; ring,
          by simp [resolventQ]; norm_num,
          by simp [tschirnhausShift]; ring⟩

/-- **Identity at t=1, p=0, q=2, r=0**: Both sides equal 4.
    LHS: resolventCubic 0 2 0 at 1 − 0 = 1: eval = 8·1³ + 0 + 0 − 4 = 4.
    RHS: 8 · depressedCubic 0 (−1/2) at 1: 8·(1³ + 0·1 − 1/2) = 8·(1/2) = 4. -/
theorem identity_at_t1_p0 :
    (resolventCubic 0 2 0).eval (1 - tschirnhausShift 0) =
    8 * (SolutionOfCubic.depressedCubic (resolventP 0 0) (resolventQ 0 2 0)).eval 1 := by
  exact resolvent_tschirnhaus_identity 0 2 0 1

/-- **Identity at t=2, p=0, q=−60, r=0**: Both sides equal 8·(8 − 450) = −3536.
    Resolvent cubic: 8m³ + 0 + 0 + (0 − 0 − 3600) = 8m³ − 3600.
    At m = t − 0 = 2: 8·8 − 3600 = 64 − 3600 = −3536.
    Depressed cubic: P_r = 0, Q_r = −3600/8 = −450. At t=2: 8 + 0 − 450 = −442.
    8 · (−442) = −3536. -/
theorem identity_at_t2_p0_q60 :
    (resolventCubic 0 60 0).eval (2 - tschirnhausShift 0) =
    8 * (SolutionOfCubic.depressedCubic (resolventP 0 0) (resolventQ 0 60 0)).eval 2 := by
  exact resolvent_tschirnhaus_identity 0 60 0 2

end SolutionOfCubicOQ05
