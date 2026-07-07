/-
  Newton's log-concavity: inductive step proof.
  Key binomial inequality: bc³+adc²+ac³ ≥ 2b²cd+b³d
  proved via absorption identities and the identity
  k³(k+1)(m-k+2)·(LHS-RHS) = (m-k+1)(m+1)²·b⁴
-/

import Mathlib

/-- Quadratic αt² + βt + γ ≥ 0 for t ≥ 0 when α,γ ≥ 0 and 4αγ ≥ β². -/
theorem quadratic_nonneg (α β γ t : ℝ) (_ht : 0 ≤ t) (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hdisc : 4 * α * γ ≥ β ^ 2) : α * t ^ 2 + β * t + γ ≥ 0 := by
  by_cases hα0 : α = 0
  · subst hα0; simp at hdisc ⊢
    have : β = 0 := by nlinarith [sq_nonneg β]
    rw [this]; simp; exact hγ
  · have hα' : 0 < α := lt_of_le_of_ne hα (Ne.symm hα0)
    nlinarith [sq_nonneg (2 * α * t + β)]

/-- Key binomial inequality via absorption identities.
    After multiplying by k³(k+1)(m-k+2) > 0 and substituting the
    absorption identities, the expression equals (m-k+1)(m+1)²b⁴ ≥ 0. -/
theorem binom_ineq (m k : ℕ) (hk : 2 ≤ k) (hkm : k + 1 ≤ m) :
    let a := (Nat.choose m (k - 2) : ℝ)
    let b := (Nat.choose m (k - 1) : ℝ)
    let c := (Nat.choose m k : ℝ)
    let d := (Nat.choose m (k + 1) : ℝ)
    b * c ^ 3 + a * d * c ^ 2 + a * c ^ 3 ≥ 2 * b ^ 2 * c * d + b ^ 3 * d := by
  intro a b c d
  -- Absorption identities in ℝ
  have h1 : (k : ℝ) * c = ((m : ℝ) - k + 1) * b := by
    have := Nat.choose_succ_right_eq m (k - 1)
    rw [show k - 1 + 1 = k from by omega, show m - (k - 1) = m - k + 1 from by omega] at this
    have := congr_arg (Nat.cast : ℕ → ℝ) this; push_cast at this ⊢
    rw [Nat.cast_sub (show k ≤ m by omega)] at this; linarith
  have h2 : ((k : ℝ) + 1) * d = ((m : ℝ) - k) * c := by
    have := Nat.choose_succ_right_eq m k
    have := congr_arg (Nat.cast : ℕ → ℝ) this; push_cast at this ⊢
    rw [Nat.cast_sub (show k ≤ m by omega)] at this; linarith
  have h3 : ((k : ℝ) - 1) * b = ((m : ℝ) - k + 2) * a := by
    have := Nat.choose_succ_right_eq m (k - 2)
    rw [show k - 2 + 1 = k - 1 from by omega, show m - (k - 2) = m - k + 2 from by omega] at this
    have := congr_arg (Nat.cast : ℕ → ℝ) this; push_cast at this ⊢
    rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show k ≤ m by omega),
        Nat.cast_one] at this
    linarith
  -- Positivity
  set r := (m : ℝ) - k + 1 with hr_def
  have hk_pos : (0 : ℝ) < k := by positivity
  have hr_pos : (0 : ℝ) < r := by simp [hr_def]; linarith [show (k : ℝ) ≤ m from by exact_mod_cast (by omega : k ≤ m)]
  have hb_nn : 0 ≤ b := Nat.cast_nonneg _
  -- Rewrite h1 using r
  have h1' : (k : ℝ) * c = r * b := by linarith [h1]
  -- Derived: k²c² = r²b²
  have h1_sq : (k : ℝ) ^ 2 * c ^ 2 = r ^ 2 * b ^ 2 := by
    linear_combination ((k : ℝ) * c + r * b) * h1'
  -- Derived: k³c³ = r³b³
  have h1_cube : (k : ℝ) ^ 3 * c ^ 3 = r ^ 3 * b ^ 3 := by
    linear_combination ((k : ℝ) ^ 2 * c ^ 2 + (k : ℝ) * r * b * c + r ^ 2 * b ^ 2) * h1'
  -- Derived: k(k+1)d = r(r-1)b  [combining h1 and h2]
  have h12 : (k : ℝ) * ((k : ℝ) + 1) * d = r * (r - 1) * b := by
    -- From h2: (k+1)d = (m-k)c = (r-1)c. Then k(k+1)d = k(r-1)c = (r-1)·kc = (r-1)·rb = r(r-1)b.
    linear_combination (r - 1) * h1' + (k : ℝ) * h2
  -- Derived: (r+1)a = (k-1)b  [from h3]
  have h3' : (r + 1) * a = ((k : ℝ) - 1) * b := by
    linarith [h3]
  -- Now prove: D * target = r(k+r)²b⁴ where D = k³(k+1)(r+1) > 0
  -- Instead of proving the identity, we prove D * target ≥ 0.
  -- D * (bc³+adc²+ac³-2b²cd-b³d) = r(k+r)²b⁴
  -- We compute each term of D*(target):
  -- Term 1: k³(k+1)(r+1)·bc³ = (k+1)(r+1)·k³bc³ = (k+1)(r+1)·r³b⁴  [using k³c³=r³b³]
  -- Term 2: k³(k+1)(r+1)·adc² = k³·(k+1)d·(r+1)a·c² = k³·(r-1)c·(k-1)b·c²
  --        = (k-1)(r-1)k³bc³ = (k-1)(r-1)r³b⁴
  -- Term 3: k³(k+1)(r+1)·ac³ = k³(k+1)·(r+1)a·c³ = k³(k+1)(k-1)bc³ = (k²-1)r³b⁴
  -- Term 4: 2k³(k+1)(r+1)·b²cd = 2(r+1)·k³·b²c·(k+1)d = 2(r+1)k³b²c·(r-1)c
  --        = 2(r²-1)k³b²c² = 2(r²-1)kr²b⁴  [using k²c²=r²b²]
  -- Term 5: k³(k+1)(r+1)·b³d = (r+1)k²b³·k(k+1)d = (r+1)k²b³·r(r-1)b = (r+1)r(r-1)k²b⁴
  --
  -- Sum: b⁴[r³((k+1)(r+1)+(k-1)(r-1)+(k²-1)) - 2(r²-1)kr² - (r+1)r(r-1)k²]
  --    = b⁴[r³(k²+2kr+1) - kr(r²-1)(2r+k)]
  --    = b⁴·r·(k+r)²
  --
  -- So D*(target) = r(k+r)²b⁴ ≥ 0.
  -- We prove this by providing the identity as a linear_combination.
  --
  -- Sufficient: show k³(k+1)(r+1)*(target) ≥ 0
  have hD_pos : 0 < (k : ℝ) ^ 3 * ((k : ℝ) + 1) * (r + 1) := by positivity
  suffices h : (k : ℝ) ^ 3 * ((k : ℝ) + 1) * (r + 1) *
      (b * c ^ 3 + a * d * c ^ 2 + a * c ^ 3 - 2 * b ^ 2 * c * d - b ^ 3 * d) ≥ 0 by
    by_contra hlt; push_neg at hlt
    have : (k : ℝ) ^ 3 * ((k : ℝ) + 1) * (r + 1) *
        (b * c ^ 3 + a * d * c ^ 2 + a * c ^ 3 - 2 * b ^ 2 * c * d - b ^ 3 * d) < 0 :=
      mul_neg_of_pos_of_neg hD_pos (by linarith)
    linarith
  -- Now prove the multiplied version ≥ 0.
  -- We show it equals r * (k + r)^2 * b^4 using linear_combination with derived identities.
  -- Instead, use nlinarith with the derived identities as hints.
  -- The key products nlinarith needs:
  -- h1_cube * b: k³·b·c³ = r³·b⁴
  -- h12 * b³: k(k+1)·b³·d = r(r-1)·b⁴
  -- h3' * ... for the a terms
  -- h1_sq * b²: k²·b²·c² = r²·b⁴
  have key1 : (k : ℝ) ^ 3 * b * c ^ 3 = r ^ 3 * b ^ 4 := by
    linear_combination b * h1_cube
  have key2 : (k : ℝ) * ((k : ℝ) + 1) * b ^ 3 * d = r * (r - 1) * b ^ 4 := by
    linear_combination b ^ 3 * h12
  have key3 : (k : ℝ) ^ 2 * b ^ 2 * c ^ 2 = r ^ 2 * b ^ 4 := by
    linear_combination b ^ 2 * h1_sq
  -- For the a·d·c² and a·c³ terms, we need (r+1)a = (k-1)b
  -- (k+1)d = (r-1)c  [from h2, since m-k = r-1]
  have h2' : ((k : ℝ) + 1) * d = (r - 1) * c := by linarith
  -- k³(k+1)(r+1)·adc² = k³ · [(k+1)d] · [(r+1)a] · c²
  -- = k³ · (r-1)c · (k-1)b · c² = (k-1)(r-1) · k³bc³ = (k-1)(r-1)r³b⁴
  have key4 : (k : ℝ) ^ 3 * ((k : ℝ) + 1) * (r + 1) * (a * d * c ^ 2) =
      ((k : ℝ) - 1) * (r - 1) * r ^ 3 * b ^ 4 := by
    -- Multiply the two absorption identities: (k+1)d·(r+1)a = (r-1)c·(k-1)b
    have step1 : ((k : ℝ) + 1) * d * ((r + 1) * a) = (r - 1) * ((k : ℝ) - 1) * b * c := by
      -- From h2': (k+1)*d = (r-1)*c and h3': (r+1)*a = (k-1)*b
      linear_combination (r + 1) * a * h2' + (r - 1) * c * h3'
    -- k³ * [(k+1)d·(r+1)a] * c² = k³ * (k-1)(r-1)bc * c² = (k-1)(r-1) * k³bc³
    -- And k³bc³ = r³b⁴ (from key1)
    linear_combination (k - 1) * (r - 1) * key1 + (k : ℝ) ^ 3 * c ^ 2 * step1
  -- k³(k+1)(r+1)·ac³ = k³(k+1) · (k-1)b · c³ = (k²-1)(k) · k²bc³ = (k²-1)r³b⁴
  -- Actually: k³(k+1)(r+1)ac³ = k³ · (r+1)a · (k+1) · c³ = k³ · (k-1)b · (k+1) · c³
  have key5 : (k : ℝ) ^ 3 * ((k : ℝ) + 1) * (r + 1) * (a * c ^ 3) =
      ((k : ℝ) ^ 2 - 1) * r ^ 3 * b ^ 4 := by
    -- (r+1)*a = (k-1)*b, so (k+1)*(r+1)*a = (k+1)*(k-1)*b = (k²-1)*b
    -- k³(k+1)(r+1)ac³ = k³ · (k²-1) · b · c³ = (k²-1) · k³bc³ = (k²-1) · r³b⁴
    linear_combination ((k : ℝ) ^ 2 - 1) * key1 + (k : ℝ) ^ 3 * (k + 1) * c ^ 3 * h3'
  -- The key identity:
  -- D * (bc³+adc²+ac³-2b²cd-b³d) = r*(k+r)²*b⁴ ≥ 0
  -- where D = k³(k+1)(r+1)
  --
  -- Proof: Express each term of D*target via absorption identities:
  -- D*bc³     = (k+1)(r+1)*r³b⁴   [via key1]
  -- D*adc²    = (k-1)(r-1)*r³b⁴   [via key4]
  -- D*ac³     = (k²-1)*r³b⁴       [via key5]
  -- D*2b²cd   = 2kr²(r²-1)b⁴      [via h2' and key3]
  -- D*b³d     = k²r(r²-1)b⁴       [via key2]
  -- Sum: [(k+1)(r+1)+(k-1)(r-1)+(k²-1)]r³ - [2kr²+k²r](r²-1) = r(k+r)²
  suffices h_ident : (k : ℝ) ^ 3 * ((k : ℝ) + 1) * (r + 1) *
      (b * c ^ 3 + a * d * c ^ 2 + a * c ^ 3 - 2 * b ^ 2 * c * d - b ^ 3 * d) =
      r * ((k : ℝ) + r) ^ 2 * b ^ 4 by
    rw [h_ident]; positivity
  -- Prove the identity using all absorption identities via linear_combination.
  -- Each key_i is an equation; we provide polynomial coefficients for the combination.
  linear_combination
    ((k : ℝ) + 1) * (r + 1) * key1 +
    key4 + key5 -
    2 * (k : ℝ) ^ 3 * (r + 1) * b ^ 2 * c * h2' -
    2 * (k : ℝ) * (r ^ 2 - 1) * key3 -
    (k : ℝ) ^ 2 * (r + 1) * key2

set_option maxHeartbeats 800000 in
/-- **Core discriminant inequality (normalized form)** for the normalized-Newton
    inductive step, valid whenever the linear coefficient
    `β̂ = (kr−k−r−1)·e₂e₃ − (k+1)(r+1)·e₁e₄` is non-positive (which is the only
    case in which the discriminant is needed: for `β ≥ 0` the quadratic
    `α·t² + β·t + γ` is trivially non-negative for `t ≥ 0`).

    Here `e1 e2 e3 e4` stand for `e_{k−2}(y), …, e_{k+1}(y)` and the binomial
    structure has been normalized away via the absorption identities (with
    `r = m−k+1`): `hP1`/`hP2` are the two normalized-Newton inductive hypotheses
    and `hcross` the cross-product inequality.

    The proof is the exact algebraic certificate (verified by `ring`): with
    `α̂ = kr·e₂² − (k+1)(r+1)e₁e₃`, `γ̂ = kr·e₃² − (k+1)(r+1)e₂e₄`,
    `P̂₁ = k(r−1)e₃² − r(k+1)e₂e₄`, `P̂₂ = (k−1)r·e₂² − k(r+1)e₁e₃`,
    `Ŝ = (r−1)P̂₂e₃² + (r+1)P̂₁e₁e₃`,

    `kr·e₂²e₃²·(4α̂γ̂ − β̂²)
       = 2k(2k+r+1)·P̂₂·e₂²e₃⁴ + 2r(k+2r+1)·P̂₁·e₂⁴e₃²
       + 2(2kr+2k+2r+1)·P̂₁P̂₂·e₂²e₃² + k·Ŝ·e₂e₃·(−β̂)`,

    in which every summand is visibly non-negative (the last one because
    `β̂ ≤ 0`). Equality holds exactly at geometric data (all inputs equal), which
    is why no slack-based `nlinarith` hint list could close this goal, and the
    inequality is genuinely FALSE without the `β̂ ≤ 0` restriction. -/
theorem newton_disc_hat (k r : ℝ) (hk : 2 ≤ k) (hr : 2 ≤ r)
    (e1 e2 e3 e4 : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3) (he4 : 0 ≤ e4)
    (hP1 : 0 ≤ k * (r - 1) * e3 ^ 2 - r * (k + 1) * (e2 * e4))
    (hP2 : 0 ≤ (k - 1) * r * e2 ^ 2 - k * (r + 1) * (e1 * e3))
    (hcross : e1 * e4 ≤ e3 * e2)
    (hbeta : (k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4) ≤ 0) :
    ((k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4)) ^ 2 ≤
      4 * (k * r * e2 ^ 2 - (k + 1) * (r + 1) * (e1 * e3)) *
        (k * r * e3 ^ 2 - (k + 1) * (r + 1) * (e2 * e4)) := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  have hr1 : (0 : ℝ) < r + 1 := by linarith
  -- Degenerate case: e2·e3 = 0 forces both sides to vanish.
  rcases eq_or_lt_of_le (mul_nonneg he2 he3) with h23 | h23
  · have h14 : e1 * e4 = 0 :=
      le_antisymm (by linarith [hcross]) (mul_nonneg he1 he4)
    rcases mul_eq_zero.mp h23.symm with h20 | h30
    · -- e2 = 0: hP2 forces e1·e3 = 0, so both sides vanish
      have h22 : (k - 1) * r * e2 ^ 2 = 0 := by rw [h20]; ring
      have h13 : e1 * e3 = 0 := by
        rcases eq_or_lt_of_le (mul_nonneg he1 he3) with h | h
        · exact h.symm
        · exfalso
          have := mul_pos (mul_pos hk0 hr1) h
          linarith [hP2, h22]
      have hL : ((k * r - k - r - 1) * (e2 * e3) -
          (k + 1) * (r + 1) * (e1 * e4)) ^ 2 = 0 := by
        rw [h20, h14]; ring
      have hR : (k * r * e2 ^ 2 - (k + 1) * (r + 1) * (e1 * e3)) = 0 := by
        rw [h20, h13]; ring
      have hR0 : 0 ≤ 4 * (k * r * e2 ^ 2 - (k + 1) * (r + 1) * (e1 * e3)) *
          (k * r * e3 ^ 2 - (k + 1) * (r + 1) * (e2 * e4)) := by
        rw [hR]; simp
      linarith [hL, hR0]
    · -- e3 = 0: hP1 forces e2·e4 = 0, so both sides vanish
      have h33 : k * (r - 1) * e3 ^ 2 = 0 := by rw [h30]; ring
      have h24 : e2 * e4 = 0 := by
        rcases eq_or_lt_of_le (mul_nonneg he2 he4) with h | h
        · exact h.symm
        · exfalso
          have := mul_pos (mul_pos hr0 hk1) h
          linarith [hP1, h33]
      have hL : ((k * r - k - r - 1) * (e2 * e3) -
          (k + 1) * (r + 1) * (e1 * e4)) ^ 2 = 0 := by
        rw [h30, h14]; ring
      have hR : (k * r * e3 ^ 2 - (k + 1) * (r + 1) * (e2 * e4)) = 0 := by
        rw [h30, h24]; ring
      have hR0 : 0 ≤ 4 * (k * r * e2 ^ 2 - (k + 1) * (r + 1) * (e1 * e3)) *
          (k * r * e3 ^ 2 - (k + 1) * (r + 1) * (e2 * e4)) := by
        rw [hR]; simp
      linarith [hL, hR0]
  · -- Main case: e2, e3 > 0.
    have he2' : 0 < e2 := by
      rcases eq_or_lt_of_le he2 with h | h
      · exfalso; nlinarith [h23]
      · exact h
    have he3' : 0 < e3 := by
      rcases eq_or_lt_of_le he3 with h | h
      · exfalso; nlinarith [h23]
      · exact h
    -- The exact certificate.
    have master : k * r * (e2 ^ 2 * e3 ^ 2) *
        (4 * (k * r * e2 ^ 2 - (k + 1) * (r + 1) * (e1 * e3)) *
            (k * r * e3 ^ 2 - (k + 1) * (r + 1) * (e2 * e4)) -
          ((k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4)) ^ 2) =
        2 * k * (2 * k + r + 1) *
            ((k - 1) * r * e2 ^ 2 - k * (r + 1) * (e1 * e3)) * (e2 ^ 2 * e3 ^ 4) +
          2 * r * (k + 2 * r + 1) *
            (k * (r - 1) * e3 ^ 2 - r * (k + 1) * (e2 * e4)) * (e2 ^ 4 * e3 ^ 2) +
          2 * (2 * k * r + 2 * k + 2 * r + 1) *
            ((k * (r - 1) * e3 ^ 2 - r * (k + 1) * (e2 * e4)) *
              ((k - 1) * r * e2 ^ 2 - k * (r + 1) * (e1 * e3))) * (e2 ^ 2 * e3 ^ 2) +
          k * ((r - 1) * ((k - 1) * r * e2 ^ 2 - k * (r + 1) * (e1 * e3)) * e3 ^ 2 +
              (r + 1) * (k * (r - 1) * e3 ^ 2 - r * (k + 1) * (e2 * e4)) * (e1 * e3)) *
            (e2 * e3) *
            (-((k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4))) := by
      ring
    -- Every right-hand summand is non-negative.
    have hT1 : 0 ≤ 2 * k * (2 * k + r + 1) *
        ((k - 1) * r * e2 ^ 2 - k * (r + 1) * (e1 * e3)) * (e2 ^ 2 * e3 ^ 4) :=
      mul_nonneg (mul_nonneg (by positivity) hP2) (by positivity)
    have hT2 : 0 ≤ 2 * r * (k + 2 * r + 1) *
        (k * (r - 1) * e3 ^ 2 - r * (k + 1) * (e2 * e4)) * (e2 ^ 4 * e3 ^ 2) :=
      mul_nonneg (mul_nonneg (by positivity) hP1) (by positivity)
    have hT3 : 0 ≤ 2 * (2 * k * r + 2 * k + 2 * r + 1) *
        ((k * (r - 1) * e3 ^ 2 - r * (k + 1) * (e2 * e4)) *
          ((k - 1) * r * e2 ^ 2 - k * (r + 1) * (e1 * e3))) * (e2 ^ 2 * e3 ^ 2) :=
      mul_nonneg (mul_nonneg (by positivity) (mul_nonneg hP1 hP2)) (by positivity)
    have hS : 0 ≤ (r - 1) * ((k - 1) * r * e2 ^ 2 - k * (r + 1) * (e1 * e3)) * e3 ^ 2 +
        (r + 1) * (k * (r - 1) * e3 ^ 2 - r * (k + 1) * (e2 * e4)) * (e1 * e3) :=
      add_nonneg
        (mul_nonneg (mul_nonneg (by linarith) hP2) (sq_nonneg e3))
        (mul_nonneg (mul_nonneg (by linarith) hP1) (mul_nonneg he1 he3))
    have hT4 : 0 ≤ k * ((r - 1) * ((k - 1) * r * e2 ^ 2 - k * (r + 1) * (e1 * e3)) * e3 ^ 2 +
          (r + 1) * (k * (r - 1) * e3 ^ 2 - r * (k + 1) * (e2 * e4)) * (e1 * e3)) *
        (e2 * e3) *
        (-((k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4))) :=
      mul_nonneg (mul_nonneg (mul_nonneg hk0.le hS) (mul_nonneg he2 he3))
        (neg_nonneg.mpr hbeta)
    have hkey : 0 ≤ k * r * (e2 ^ 2 * e3 ^ 2) *
        (4 * (k * r * e2 ^ 2 - (k + 1) * (r + 1) * (e1 * e3)) *
            (k * r * e3 ^ 2 - (k + 1) * (r + 1) * (e2 * e4)) -
          ((k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4)) ^ 2) := by
      rw [master]
      linarith [hT1, hT2, hT3, hT4]
    have hpref : 0 < k * r * (e2 ^ 2 * e3 ^ 2) := by positivity
    by_contra hcon
    push_neg at hcon
    have hneg : 4 * (k * r * e2 ^ 2 - (k + 1) * (r + 1) * (e1 * e3)) *
        (k * r * e3 ^ 2 - (k + 1) * (r + 1) * (e2 * e4)) -
        ((k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4)) ^ 2 < 0 := by
      linarith
    have := mul_neg_of_pos_of_neg hpref hneg
    linarith [hkey]

/-- Discriminant inequality `4·α·γ ≥ β²` for the normalized-Newton inductive
    step at the cleared-denominator (binomial) level, valid when
    `β = 2·e₃e₂·AD − (e₃e₂+e₁e₄)·B2 ≤ 0` (with `AD = (b+a)(d+c)`,
    `B2 = (c+b)²`). Reduces to `newton_disc_hat` via the absorption identities
    `h1, h2, h3` (where `a b c d` are the binomial coefficients
    `C(m,k−2), …, C(m,k+1)` and `r = m−k+1`), using the exact ratio identity
    `(k+1)(r+1)·AD = kr·B2` for the Pascal-combined level-(m+1) coefficients. -/
set_option maxHeartbeats 800000 in
theorem newton_disc_of_beta_nonpos
    (k r a b c d : ℝ) (hk : 2 ≤ k) (hr : 2 ≤ r)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : k * c = r * b) (h2 : (k + 1) * d = (r - 1) * c) (h3 : (r + 1) * a = (k - 1) * b)
    (e1 e2 e3 e4 : ℝ) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) (he3 : 0 ≤ e3) (he4 : 0 ≤ e4)
    (hd1 : e3 ^ 2 * (b * d) ≥ e2 * e4 * c ^ 2)
    (hd2 : e2 ^ 2 * (a * c) ≥ e1 * e3 * b ^ 2)
    (hcross : e3 * e2 ≥ e1 * e4)
    (hbeta : 2 * e3 * e2 * ((b + a) * (d + c)) ≤ (e3 * e2 + e1 * e4) * (c + b) ^ 2) :
    4 * (e2 ^ 2 * ((b + a) * (d + c)) - e1 * e3 * (c + b) ^ 2) *
      (e3 ^ 2 * ((b + a) * (d + c)) - e2 * e4 * (c + b) ^ 2) ≥
    (2 * e3 * e2 * ((b + a) * (d + c)) - (e3 * e2 + e1 * e4) * (c + b) ^ 2) ^ 2 := by
  have hk0 : (0 : ℝ) < k := by linarith
  have hr0 : (0 : ℝ) < r := by linarith
  have hk1 : (0 : ℝ) < k + 1 := by linarith
  have hr1 : (0 : ℝ) < r + 1 := by linarith
  have hb2 : (0 : ℝ) < b ^ 2 := by positivity
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  have hB2 : (0 : ℝ) < (c + b) ^ 2 := by positivity
  -- Conversion identities from the absorption relations.
  have hbd : k * (r - 1) * c ^ 2 = r * (k + 1) * (b * d) := by
    linear_combination (r - 1) * c * h1 - r * b * h2
  have hac : (k - 1) * r * b ^ 2 = k * (r + 1) * (a * c) := by
    linear_combination (-((k - 1) * b)) * h1 - k * c * h3
  have hAD : (k + 1) * (r + 1) * ((b + a) * (d + c)) = k * r * ((c + b) ^ 2) := by
    linear_combination (a * r + a + b - c * r) * h1 + ((a + b) * (r + 1)) * h2 +
      (r * (b + c)) * h3
  -- Hypothesis conversions to the normalized form.
  have hP1c : (k * (r - 1) * e3 ^ 2 - r * (k + 1) * (e2 * e4)) * c ^ 2 =
      r * (k + 1) * (e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) := by
    linear_combination e3 ^ 2 * hbd
  have hP1 : 0 ≤ k * (r - 1) * e3 ^ 2 - r * (k + 1) * (e2 * e4) := by
    by_contra hcon
    push_neg at hcon
    have hlt := mul_neg_of_neg_of_pos hcon hc2
    rw [hP1c] at hlt
    have h0 : 0 ≤ r * (k + 1) * (e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) :=
      mul_nonneg (by positivity) (by linarith [hd1])
    linarith
  have hP2b : ((k - 1) * r * e2 ^ 2 - k * (r + 1) * (e1 * e3)) * b ^ 2 =
      k * (r + 1) * (e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2) := by
    linear_combination e2 ^ 2 * hac
  have hP2 : 0 ≤ (k - 1) * r * e2 ^ 2 - k * (r + 1) * (e1 * e3) := by
    by_contra hcon
    push_neg at hcon
    have hlt := mul_neg_of_neg_of_pos hcon hb2
    rw [hP2b] at hlt
    have h0 : 0 ≤ k * (r + 1) * (e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2) :=
      mul_nonneg (by positivity) (by linarith [hd2])
    linarith
  -- β conversion.
  have hbe : ((k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4)) *
      (c + b) ^ 2 =
      (k + 1) * (r + 1) *
        (2 * e3 * e2 * ((b + a) * (d + c)) - (e3 * e2 + e1 * e4) * (c + b) ^ 2) := by
    linear_combination (-(2 * (e2 * e3))) * hAD
  have hbehat : (k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4) ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have hgt := mul_pos hcon hB2
    rw [hbe] at hgt
    have h0 : 0 ≤ (k + 1) * (r + 1) *
        ((e3 * e2 + e1 * e4) * (c + b) ^ 2 - 2 * e3 * e2 * ((b + a) * (d + c))) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  -- Core inequality in normalized form.
  have hat := newton_disc_hat k r hk hr e1 e2 e3 e4 he1 he2 he3 he4 hP1 hP2 hcross hbehat
  -- Convert the conclusion back.
  have hal : (k * r * e2 ^ 2 - (k + 1) * (r + 1) * (e1 * e3)) * (c + b) ^ 2 =
      (k + 1) * (r + 1) * (e2 ^ 2 * ((b + a) * (d + c)) - e1 * e3 * (c + b) ^ 2) := by
    linear_combination (-(e2 ^ 2)) * hAD
  have hga : (k * r * e3 ^ 2 - (k + 1) * (r + 1) * (e2 * e4)) * (c + b) ^ 2 =
      (k + 1) * (r + 1) * (e3 ^ 2 * ((b + a) * (d + c)) - e2 * e4 * (c + b) ^ 2) := by
    linear_combination (-(e3 ^ 2)) * hAD
  have hconv : ((c + b) ^ 2) ^ 2 *
      (4 * (k * r * e2 ^ 2 - (k + 1) * (r + 1) * (e1 * e3)) *
          (k * r * e3 ^ 2 - (k + 1) * (r + 1) * (e2 * e4)) -
        ((k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4)) ^ 2) =
      ((k + 1) * (r + 1)) ^ 2 *
      (4 * (e2 ^ 2 * ((b + a) * (d + c)) - e1 * e3 * (c + b) ^ 2) *
          (e3 ^ 2 * ((b + a) * (d + c)) - e2 * e4 * (c + b) ^ 2) -
        (2 * e3 * e2 * ((b + a) * (d + c)) - (e3 * e2 + e1 * e4) * (c + b) ^ 2) ^ 2) := by
    linear_combination
      (4 * (k * r * e3 ^ 2 - (k + 1) * (r + 1) * (e2 * e4)) * (c + b) ^ 2) * hal +
      (4 * ((k + 1) * (r + 1)) *
        (e2 ^ 2 * ((b + a) * (d + c)) - e1 * e3 * (c + b) ^ 2)) * hga +
      (-(((k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4)) * (c + b) ^ 2 +
        (k + 1) * (r + 1) *
          (2 * e3 * e2 * ((b + a) * (d + c)) -
            (e3 * e2 + e1 * e4) * (c + b) ^ 2))) * hbe
  have hhatpos : 0 ≤ 4 * (k * r * e2 ^ 2 - (k + 1) * (r + 1) * (e1 * e3)) *
      (k * r * e3 ^ 2 - (k + 1) * (r + 1) * (e2 * e4)) -
      ((k * r - k - r - 1) * (e2 * e3) - (k + 1) * (r + 1) * (e1 * e4)) ^ 2 := by
    linarith [hat]
  have hfin : 0 ≤ ((k + 1) * (r + 1)) ^ 2 *
      (4 * (e2 ^ 2 * ((b + a) * (d + c)) - e1 * e3 * (c + b) ^ 2) *
          (e3 ^ 2 * ((b + a) * (d + c)) - e2 * e4 * (c + b) ^ 2) -
        (2 * e3 * e2 * ((b + a) * (d + c)) - (e3 * e2 + e1 * e4) * (c + b) ^ 2) ^ 2) := by
    rw [← hconv]
    exact mul_nonneg (sq_nonneg _) hhatpos
  have hD2 : (0 : ℝ) < ((k + 1) * (r + 1)) ^ 2 := by positivity
  by_contra hcon
  push_neg at hcon
  have hneg : 4 * (e2 ^ 2 * ((b + a) * (d + c)) - e1 * e3 * (c + b) ^ 2) *
      (e3 ^ 2 * ((b + a) * (d + c)) - e2 * e4 * (c + b) ^ 2) -
      (2 * e3 * e2 * ((b + a) * (d + c)) - (e3 * e2 + e1 * e4) * (c + b) ^ 2) ^ 2 < 0 := by
    linarith
  have := mul_neg_of_pos_of_neg hD2 hneg
  linarith [hfin]


/-- Dual binomial inequality: b²·(b+a)·(d+c) ≥ a·c·(c+b)².
    Companion to `binom_ineq`, needed for the `α ≥ 0` branch of the
    normalized-Newton inductive step. Proved by the same absorption technique:
    after multiplying by k³(k+1)(r+1) > 0 (where r = m-k+1) and substituting the
    absorption identities k·c = r·b, (k+1)·d = (r-1)·c, (r+1)·a = (k-1)·b,
    the cleared expression equals r·(k+r)²·b⁴ ≥ 0.
    (The single non-trivial factor is k² - (k-1)(k+1) = 1.) -/
theorem binom_ineq_dual (m k : ℕ) (hk : 2 ≤ k) (hkm : k + 1 ≤ m) :
    let a := (Nat.choose m (k - 2) : ℝ)
    let b := (Nat.choose m (k - 1) : ℝ)
    let c := (Nat.choose m k : ℝ)
    let d := (Nat.choose m (k + 1) : ℝ)
    b ^ 2 * ((b + a) * (d + c)) ≥ a * c * (c + b) ^ 2 := by
  intro a b c d
  -- Absorption identities in ℝ (identical to binom_ineq)
  have h1 : (k : ℝ) * c = ((m : ℝ) - k + 1) * b := by
    have := Nat.choose_succ_right_eq m (k - 1)
    rw [show k - 1 + 1 = k from by omega, show m - (k - 1) = m - k + 1 from by omega] at this
    have := congr_arg (Nat.cast : ℕ → ℝ) this; push_cast at this ⊢
    rw [Nat.cast_sub (show k ≤ m by omega)] at this; linarith
  have h2 : ((k : ℝ) + 1) * d = ((m : ℝ) - k) * c := by
    have := Nat.choose_succ_right_eq m k
    have := congr_arg (Nat.cast : ℕ → ℝ) this; push_cast at this ⊢
    rw [Nat.cast_sub (show k ≤ m by omega)] at this; linarith
  have h3 : ((k : ℝ) - 1) * b = ((m : ℝ) - k + 2) * a := by
    have := Nat.choose_succ_right_eq m (k - 2)
    rw [show k - 2 + 1 = k - 1 from by omega, show m - (k - 2) = m - k + 2 from by omega] at this
    have := congr_arg (Nat.cast : ℕ → ℝ) this; push_cast at this ⊢
    rw [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show k ≤ m by omega),
        Nat.cast_one] at this
    linarith
  -- Positivity setup
  set r := (m : ℝ) - k + 1 with hr_def
  have hk_pos : (0 : ℝ) < k := by positivity
  have hr_pos : (0 : ℝ) < r := by
    simp only [hr_def]; linarith [show (k : ℝ) ≤ m from by exact_mod_cast (by omega : k ≤ m)]
  -- Primitive absorption identities in terms of r
  have h1' : (k : ℝ) * c = r * b := by linarith [h1]
  have h2' : ((k : ℝ) + 1) * d = (r - 1) * c := by
    have : ((m : ℝ) - k) = r - 1 := by simp only [hr_def]; ring
    rw [this] at h2; linarith [h2]
  have h3' : (r + 1) * a = ((k : ℝ) - 1) * b := by
    have : ((m : ℝ) - k + 2) = r + 1 := by simp only [hr_def]; ring
    rw [this] at h3; linarith [h3]
  -- Multiply by D = k³(k+1)(r+1) > 0 and reduce to a nonneg identity.
  have hD_pos : 0 < (k : ℝ) ^ 3 * ((k : ℝ) + 1) * (r + 1) := by positivity
  suffices h : (k : ℝ) ^ 3 * ((k : ℝ) + 1) * (r + 1) *
      (b ^ 2 * ((b + a) * (d + c)) - a * c * (c + b) ^ 2) ≥ 0 by
    by_contra hlt; push_neg at hlt
    have : (k : ℝ) ^ 3 * ((k : ℝ) + 1) * (r + 1) *
        (b ^ 2 * ((b + a) * (d + c)) - a * c * (c + b) ^ 2) < 0 :=
      mul_neg_of_pos_of_neg hD_pos (by linarith)
    linarith
  -- D * target = r·(k+r)²·b⁴ ≥ 0.
  suffices h_ident : (k : ℝ) ^ 3 * ((k : ℝ) + 1) * (r + 1) *
      (b ^ 2 * ((b + a) * (d + c)) - a * c * (c + b) ^ 2) =
      r * ((k : ℝ) + r) ^ 2 * b ^ 4 by
    rw [h_ident]; positivity
  -- Single linear_combination against the three primitive absorption identities.
  linear_combination
    (-a * b ^ 2 * (k : ℝ) ^ 2 * r ^ 2 - 2 * a * b ^ 2 * (k : ℝ) ^ 2 * r - a * b ^ 2 * (k : ℝ) ^ 2
      - a * b ^ 2 * (k : ℝ) * r ^ 3 - 3 * a * b ^ 2 * (k : ℝ) * r ^ 2 - 2 * a * b ^ 2 * (k : ℝ) * r
      - a * b ^ 2 * r ^ 3 - a * b ^ 2 * r ^ 2
      - 2 * a * b * c * (k : ℝ) ^ 3 * r - 2 * a * b * c * (k : ℝ) ^ 3
      - a * b * c * (k : ℝ) ^ 2 * r ^ 2 - 3 * a * b * c * (k : ℝ) ^ 2 * r - 2 * a * b * c * (k : ℝ) ^ 2
      - a * b * c * (k : ℝ) * r ^ 2 - a * b * c * (k : ℝ) * r
      - a * c ^ 2 * (k : ℝ) ^ 3 * r - a * c ^ 2 * (k : ℝ) ^ 3
      - a * c ^ 2 * (k : ℝ) ^ 2 * r - a * c ^ 2 * (k : ℝ) ^ 2
      + b ^ 3 * (k : ℝ) ^ 3 * r + b ^ 3 * (k : ℝ) ^ 3
      + b ^ 3 * (k : ℝ) ^ 2 * r ^ 2 + b ^ 3 * (k : ℝ) ^ 2 * r) * h1'
    + (a * b ^ 2 * (k : ℝ) ^ 3 * r + a * b ^ 2 * (k : ℝ) ^ 3
      + b ^ 3 * (k : ℝ) ^ 3 * r + b ^ 3 * (k : ℝ) ^ 3) * h2'
    + (-b ^ 3 * (k : ℝ) ^ 2 * r ^ 2 - b ^ 3 * (k : ℝ) ^ 2 * r
      - b ^ 3 * (k : ℝ) * r ^ 3 - 2 * b ^ 3 * (k : ℝ) * r ^ 2 - b ^ 3 * r ^ 3) * h3'
