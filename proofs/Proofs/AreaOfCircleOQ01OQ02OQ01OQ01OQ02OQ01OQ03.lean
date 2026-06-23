/-
  Log-Concavity of the Unit-Ball Volume Sequence ω_n
  Open Question: area-of-circle-oq-01-oq-02-oq-01-oq-01-oq-02-oq-01-oq-03

  The ancestors study the *unimodality profile* of the unit n-ball volume
  ω_n = π^(n/2) / Γ(n/2 + 1): the parent (…-oq-02-oq-01) proves strict
  unimodality — ω rises strictly to a single peak at n = 5 and falls strictly
  thereafter within each parity class.  Unimodality is a statement about the
  *direction* of the increments; it says nothing about how the increments
  themselves evolve.

  This file proves the sharper *second-order* shape property: **log-concavity**
  of the sequence,

      ω_{n+1}² ≥ ω_n · ω_{n+2}      for every n,

  equivalently, the ratios ω_{n+1}/ω_n are non-increasing.  Log-concavity is a
  strictly stronger structural fact than unimodality (every log-concave positive
  sequence is unimodal, but not conversely), and it is exactly the discrete
  shadow of the analytic engine behind ω.

  ## The mathematical content: π drops out, Γ log-convexity does the work

  Writing x = n/2, the three relevant volumes are
      ω_n     = π^x       / Γ(x+1),
      ω_{n+1} = π^(x+1/2) / Γ(x+3/2),
      ω_{n+2} = π^(x+1)   / Γ(x+2).
  Then
      ω_n · ω_{n+2} = π^(2x+1) / (Γ(x+1) Γ(x+2)),
      ω_{n+1}²      = π^(2x+1) / Γ(x+3/2)².
  The powers of π are *identical*, so log-concavity is equivalent to the pure
  Gamma inequality

      Γ(x + 3/2)² ≤ Γ(x+1) · Γ(x+2).

  This is precisely midpoint log-convexity of Γ: with x+3/2 the midpoint of
  x+1 and x+2, Mathlib's `Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma`
  (Hölder/Bohr–Mollerup) gives
      Γ((x+1)/2 + (x+2)/2) ≤ Γ(x+1)^(1/2) · Γ(x+2)^(1/2),
  and squaring yields the claim.  So the convexity that singles out Γ among all
  interpolations of the factorial is exactly what makes the ball-volume sequence
  log-concave.

  Content (all 0 sorries, 0 axioms beyond Mathlib's foundational triple):
  * `gamma_sq_le_mul`     — the engine: Γ(x+3/2)² ≤ Γ(x+1)·Γ(x+2) for x ≥ 0.
  * `omega_log_concave`   — the headline: ω_n · ω_{n+2} ≤ ω_{n+1}² (all n).
  * `omega_sq_ge`         — index form: ω_{n-1}·ω_{n+1} ≤ ω_n² for n ≥ 1.
  * `omega_ratio_antitone`— the ratios ω_{n+1}/ω_n are non-increasing.

  A *strict* log-concavity (ω_{n+1}² > ω_n·ω_{n+2}) would follow from strict
  log-convexity of Γ, which Mathlib does not currently expose in midpoint form;
  we record the non-strict statement, which is the standard "log-concave"
  property and already implies unimodality.

  References:
  - AreaOfCircleOQ01OQ02OQ01OQ01OQ02OQ01.lean (parent: strict unimodality)
  - Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup (log-convexity of Γ)
  - https://en.wikipedia.org/wiki/Volume_of_an_n-ball
-/
import Proofs.AreaOfCircleOQ01OQ02OQ01OQ01OQ02OQ01

open Real

noncomputable section

namespace MaxBallVolume

/- ## The Gamma engine: midpoint log-convexity in squared form -/

/-- **Midpoint log-convexity of Γ (squared form).**  For `x ≥ 0`,

        Γ(x + 3/2)² ≤ Γ(x+1) · Γ(x+2).

    Since `x + 3/2 = ½(x+1) + ½(x+2)` is the midpoint of `x+1` and `x+2`, this is
    Mathlib's multiplicative log-convexity bound
    `Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma` at weights `½, ½`, squared. -/
theorem gamma_sq_le_mul {x : ℝ} (hx : 0 ≤ x) :
    Gamma (x + 3 / 2) ^ 2 ≤ Gamma (x + 1) * Gamma (x + 2) := by
  have hs : (0 : ℝ) < x + 1 := by linarith
  have ht : (0 : ℝ) < x + 2 := by linarith
  have hA : (0 : ℝ) < Gamma (x + 1) := Gamma_pos_of_pos hs
  have hB : (0 : ℝ) < Gamma (x + 2) := Gamma_pos_of_pos ht
  have hmid := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma hs ht
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 : ℝ) / 2 + 1 / 2 = 1)
  -- normalise the midpoint argument `½(x+1) + ½(x+2) = x + 3/2`
  rw [show (1 : ℝ) / 2 * (x + 1) + 1 / 2 * (x + 2) = x + 3 / 2 by ring] at hmid
  -- square the inequality `Γ(x+3/2) ≤ Γ(x+1)^½ · Γ(x+2)^½`
  have hmidpos : 0 ≤ Gamma (x + 3 / 2) := (Gamma_pos_of_pos (by linarith)).le
  have hsq := mul_self_le_mul_self hmidpos hmid
  -- expand the right-hand square: (A^½ B^½)² = A · B
  have e1 : Gamma (x + 1) ^ (1 / 2 : ℝ) * Gamma (x + 1) ^ (1 / 2 : ℝ) = Gamma (x + 1) := by
    rw [← Real.rpow_add hA, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one]
  have e2 : Gamma (x + 2) ^ (1 / 2 : ℝ) * Gamma (x + 2) ^ (1 / 2 : ℝ) = Gamma (x + 2) := by
    rw [← Real.rpow_add hB, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, Real.rpow_one]
  have hexpand :
      (Gamma (x + 1) ^ (1 / 2 : ℝ) * Gamma (x + 2) ^ (1 / 2 : ℝ)) *
        (Gamma (x + 1) ^ (1 / 2 : ℝ) * Gamma (x + 2) ^ (1 / 2 : ℝ))
        = Gamma (x + 1) * Gamma (x + 2) := by
    rw [show (Gamma (x + 1) ^ (1 / 2 : ℝ) * Gamma (x + 2) ^ (1 / 2 : ℝ)) *
          (Gamma (x + 1) ^ (1 / 2 : ℝ) * Gamma (x + 2) ^ (1 / 2 : ℝ))
        = (Gamma (x + 1) ^ (1 / 2 : ℝ) * Gamma (x + 1) ^ (1 / 2 : ℝ)) *
          (Gamma (x + 2) ^ (1 / 2 : ℝ) * Gamma (x + 2) ^ (1 / 2 : ℝ)) by ring,
      e1, e2]
  rw [pow_two, ← hexpand]
  exact hsq

/- ## Log-concavity of the volume sequence -/

/-- **Log-concavity of the unit-ball volume sequence.**  For every `n`,

        ω_n · ω_{n+2} ≤ ω_{n+1}².

    The shared power `π^(2·(n/2)+1)` cancels between the two sides, reducing the
    statement to `gamma_sq_le_mul` at `x = n/2`. -/
theorem omega_log_concave (n : ℕ) : ω n * ω (n + 2) ≤ ω (n + 1) ^ 2 := by
  have hpi : (0 : ℝ) < π := pi_pos
  -- the shared π-power: π^(n/2) · π^(n/2+1) = (π^(n/2+1/2))²
  have hP : π ^ ((n : ℝ) / 2) * π ^ ((n : ℝ) / 2 + 1)
      = (π ^ ((n : ℝ) / 2 + 1 / 2)) ^ 2 := by
    rw [pow_two, ← Real.rpow_add hpi, ← Real.rpow_add hpi]; congr 1; ring
  have key := gamma_sq_le_mul (x := (n : ℝ) / 2) (by positivity)
  unfold ω
  -- rewrite the (n+1)- and (n+2)-arguments in terms of x = n/2
  rw [show ((n + 2 : ℕ) : ℝ) / 2 + 1 = (n : ℝ) / 2 + 2 by push_cast; ring,
      show ((n + 2 : ℕ) : ℝ) / 2 = (n : ℝ) / 2 + 1 by push_cast; ring,
      show ((n + 1 : ℕ) : ℝ) / 2 + 1 = (n : ℝ) / 2 + 3 / 2 by push_cast; ring,
      show ((n + 1 : ℕ) : ℝ) / 2 = (n : ℝ) / 2 + 1 / 2 by push_cast; ring]
  rw [div_mul_div_comm, div_pow,
      div_le_div_iff₀ (by positivity) (by positivity), hP]
  exact mul_le_mul_of_nonneg_left key (by positivity)

/-- **Log-concavity, index form.**  For `n ≥ 1`,

        ω_{n-1} · ω_{n+1} ≤ ω_n².

    The shift of `omega_log_concave` to a centred index. -/
theorem omega_sq_ge {n : ℕ} (hn : 1 ≤ n) : ω (n - 1) * ω (n + 1) ≤ ω n ^ 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hn).symm⟩
  simpa using omega_log_concave m

/-- **Antitone volume ratios.**  Log-concavity expressed as monotonicity of the
    successive ratios: for every `n`,

        ω_{n+2} / ω_{n+1} ≤ ω_{n+1} / ω_n.

    Each `ω` is positive, so this is `omega_log_concave` cross-multiplied. -/
theorem omega_ratio_antitone (n : ℕ) : ω (n + 2) / ω (n + 1) ≤ ω (n + 1) / ω n := by
  rw [div_le_div_iff₀ (omega_pos _) (omega_pos _)]
  have h := omega_log_concave n
  nlinarith [h, omega_pos n, omega_pos (n + 1), omega_pos (n + 2)]

end MaxBallVolume

end

#check @MaxBallVolume.gamma_sq_le_mul
#check @MaxBallVolume.omega_log_concave
#check @MaxBallVolume.omega_sq_ge
#check @MaxBallVolume.omega_ratio_antitone
