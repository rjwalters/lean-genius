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

set_option maxHeartbeats 1600000 in
/-- Discriminant inequality `4·α·γ ≥ β²` for the normalized-Newton inductive step,
    valid whenever the linear coefficient `β = 2·e₃·e₂·AD − (e₃e₂+e₁e₄)·B2` is
    non-positive (the case where the discriminant is actually needed; for `β ≥ 0`
    the quadratic `α·t² + β·t + γ` is trivially non-negative for `t ≥ 0`).

    Here `a b c d` are (casts of) the binomial coefficients `C(m,k−2), …, C(m,k+1)`,
    abstracted via the absorption identities `h1, h2, h3` (with `r = m−k+1`), and
    `e1 e2 e3 e4` are the elementary symmetric values `e_{k−2}(y), …, e_{k+1}(y)`.
    The hypotheses `hd1, hd2` are the normalized-Newton inductive hypotheses in
    cleared form, and `hcross` is the unnormalized cross-product inequality.

    The proof rests on the exact algebraic identity (verified by `ring` after
    eliminating `a, c, d` via the absorption identities): with
    `δ₁ = e₃²bd − e₂e₄c²`, `δ₂ = e₂²ac − e₁e₃b²`, `g = (k−1)(r−1)`,
    `S = δ₂e₃²bd + δ₁e₁e₃b²`, `R = 2abcd·e₂²e₃² − gS`,

    `((k+1)(r+1))²·a²b⁴c⁴d²·e₂²e₃²·(4αγ − β²)
       = 2(k−1)(2k+r+1)·(c+b)⁴·ab⁴c³d²·δ₂·e₂²e₃⁴
       + 2(r−1)(2r+k+1)·(c+b)⁴·a²b³c⁴d·δ₁·e₂⁴e₃²
       + 2g(2kr+2k+2r+1)·(c+b)⁴·ab³c³d·δ₁δ₂·e₂²e₃²
       + (c+b)⁴·b²c²·(gS)·R`,

    where every summand on the right is non-negative: `δ₁, δ₂ ≥ 0` by hypothesis,
    `S ≥ 0` termwise, and `R ≥ 0` because `R·(c+b)² = (−β)·e₂e₃·(k+1)(r+1)·abcd`
    (a second exact identity) and `β ≤ 0`. Equality holds exactly at geometric
    data (all inputs equal), which is why no slack-based `nlinarith` hint list
    could close this goal. -/
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
  have hkm1 : (0 : ℝ) ≤ k - 1 := by linarith
  have hrm1 : (0 : ℝ) ≤ r - 1 := by linarith
  have hb2 : (0 : ℝ) < b ^ 2 := by positivity
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  -- Degenerate case: e2·e3 = 0 forces both sides to vanish.
  rcases eq_or_lt_of_le (mul_nonneg he2 he3) with h23 | h23
  · have h14 : e1 * e4 = 0 :=
      le_antisymm (by linarith [hcross]) (mul_nonneg he1 he4)
    rcases mul_eq_zero.mp h23.symm with h20 | h30
    · -- e2 = 0: from hd2, e1·e3·b² ≤ 0, so e1·e3 = 0 and both sides vanish
      have h22 : e2 ^ 2 * (a * c) = 0 := by rw [h20]; ring
      have h13 : e1 * e3 = 0 := by
        rcases eq_or_lt_of_le (mul_nonneg he1 he3) with h | h
        · exact h.symm
        · exfalso; nlinarith [mul_pos h hb2, hd2, h22]
      have hLHS0 : 4 * (e2 ^ 2 * ((b + a) * (d + c)) - e1 * e3 * (c + b) ^ 2) *
          (e3 ^ 2 * ((b + a) * (d + c)) - e2 * e4 * (c + b) ^ 2) = 0 := by
        rw [h20, h13]; ring
      have hRHS0 : (2 * e3 * e2 * ((b + a) * (d + c)) -
          (e3 * e2 + e1 * e4) * (c + b) ^ 2) ^ 2 = 0 := by
        rw [h20, h14]; ring
      linarith [hLHS0, hRHS0]
    · -- e3 = 0: from hd1, e2·e4·c² ≤ 0, so e2·e4 = 0 and both sides vanish
      have h33 : e3 ^ 2 * (b * d) = 0 := by rw [h30]; ring
      have h24 : e2 * e4 = 0 := by
        rcases eq_or_lt_of_le (mul_nonneg he2 he4) with h | h
        · exact h.symm
        · exfalso; nlinarith [mul_pos h hc2, hd1, h33]
      have hLHS0 : 4 * (e2 ^ 2 * ((b + a) * (d + c)) - e1 * e3 * (c + b) ^ 2) *
          (e3 ^ 2 * ((b + a) * (d + c)) - e2 * e4 * (c + b) ^ 2) = 0 := by
        rw [h30, h24]; ring
      have hRHS0 : (2 * e3 * e2 * ((b + a) * (d + c)) -
          (e3 * e2 + e1 * e4) * (c + b) ^ 2) ^ 2 = 0 := by
        rw [h30, h14]; ring
      linarith [hLHS0, hRHS0]
  · -- Main case: e2, e3 > 0.
    have he2' : 0 < e2 := by
      rcases eq_or_lt_of_le he2 with h | h
      · exfalso; nlinarith [h23]
      · exact h
    have he3' : 0 < e3 := by
      rcases eq_or_lt_of_le he3 with h | h
      · exfalso; nlinarith [h23]
      · exact h
    -- Eliminate a, c, d via the absorption identities.
    have hc' : c = r * b / k := by
      rw [eq_div_iff hk0.ne']
      linear_combination h1
    have hd' : d = (r - 1) * c / (k + 1) := by
      rw [eq_div_iff hk1.ne']
      linear_combination h2
    have ha' : a = (k - 1) * b / (r + 1) := by
      rw [eq_div_iff hr1.ne']
      linear_combination h3
    -- The exact identity R·(c+b)² = (−β)·e₂e₃·(k+1)(r+1)·abcd.
    have hfact3 :
        (2 * (a * b * c * d) * (e2 ^ 2 * e3 ^ 2) -
            (k - 1) * (r - 1) *
              ((e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2) * (e3 ^ 2 * (b * d)) +
                (e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) * (e1 * e3 * b ^ 2))) * (c + b) ^ 2 =
          ((e3 * e2 + e1 * e4) * (c + b) ^ 2 - 2 * e3 * e2 * ((b + a) * (d + c))) *
            (e2 * e3 * ((k + 1) * (r + 1)) * (a * b * c * d)) := by
      rw [ha', hd', hc']
      field_simp
      ring
    -- R ≥ 0 (from β ≤ 0).
    have hR : 0 ≤ 2 * (a * b * c * d) * (e2 ^ 2 * e3 ^ 2) -
        (k - 1) * (r - 1) *
          ((e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2) * (e3 ^ 2 * (b * d)) +
            (e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) * (e1 * e3 * b ^ 2)) := by
      have hrhs : 0 ≤ ((e3 * e2 + e1 * e4) * (c + b) ^ 2 -
          2 * e3 * e2 * ((b + a) * (d + c))) *
            (e2 * e3 * ((k + 1) * (r + 1)) * (a * b * c * d)) := by
        apply mul_nonneg (by linarith)
        have h : (0 : ℝ) < e2 * e3 * ((k + 1) * (r + 1)) * (a * b * c * d) := by positivity
        exact h.le
      by_contra hcon
      push_neg at hcon
      have hcb : (0 : ℝ) < (c + b) ^ 2 := by positivity
      have hlt := mul_neg_of_neg_of_pos hcon hcb
      rw [hfact3] at hlt
      linarith
    -- S ≥ 0 termwise.
    have hd1' : 0 ≤ e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2 := by linarith
    have hd2' : 0 ≤ e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2 := by linarith
    have hS : 0 ≤ (e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2) * (e3 ^ 2 * (b * d)) +
        (e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) * (e1 * e3 * b ^ 2) :=
      add_nonneg
        (mul_nonneg hd2' (mul_nonneg (sq_nonneg e3) (mul_pos hb hd).le))
        (mul_nonneg hd1' (mul_nonneg (mul_nonneg he1 he3) (sq_nonneg b)))
    -- The master identity.
    have master :
        ((k + 1) * (r + 1)) ^ 2 * (a ^ 2 * b ^ 4 * c ^ 4 * d ^ 2) * (e2 ^ 2 * e3 ^ 2) *
          (4 * (e2 ^ 2 * ((b + a) * (d + c)) - e1 * e3 * (c + b) ^ 2) *
              (e3 ^ 2 * ((b + a) * (d + c)) - e2 * e4 * (c + b) ^ 2) -
            (2 * e3 * e2 * ((b + a) * (d + c)) - (e3 * e2 + e1 * e4) * (c + b) ^ 2) ^ 2) =
        2 * (k - 1) * (2 * k + r + 1) * (c + b) ^ 4 * (a * b ^ 4 * c ^ 3 * d ^ 2) *
            (e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2) * (e2 ^ 2 * e3 ^ 4) +
          2 * (r - 1) * (2 * r + k + 1) * (c + b) ^ 4 * (a ^ 2 * b ^ 3 * c ^ 4 * d) *
            (e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) * (e2 ^ 4 * e3 ^ 2) +
          2 * ((k - 1) * (r - 1)) * (2 * k * r + 2 * k + 2 * r + 1) * (c + b) ^ 4 *
            (a * b ^ 3 * c ^ 3 * d) *
            ((e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) * (e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2)) *
            (e2 ^ 2 * e3 ^ 2) +
          (c + b) ^ 4 * (b ^ 2 * c ^ 2) *
            ((k - 1) * (r - 1) *
              ((e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2) * (e3 ^ 2 * (b * d)) +
                (e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) * (e1 * e3 * b ^ 2))) *
            (2 * (a * b * c * d) * (e2 ^ 2 * e3 ^ 2) -
              (k - 1) * (r - 1) *
                ((e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2) * (e3 ^ 2 * (b * d)) +
                  (e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) * (e1 * e3 * b ^ 2))) := by
      rw [ha', hd', hc']
      field_simp
      ring
    -- Each right-hand summand is non-negative.
    have hcb4 : (0 : ℝ) < (c + b) ^ 4 := by positivity
    have hpos1 : 0 ≤ 2 * (k - 1) * (2 * k + r + 1) * (c + b) ^ 4 *
        (a * b ^ 4 * c ^ 3 * d ^ 2) * (e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2) *
        (e2 ^ 2 * e3 ^ 4) := by
      have h1' : 0 ≤ 2 * (k - 1) * (2 * k + r + 1) := by
        have := mul_nonneg hkm1 (show (0 : ℝ) ≤ 2 * k + r + 1 by linarith)
        linarith
      have h2' : (0 : ℝ) ≤ a * b ^ 4 * c ^ 3 * d ^ 2 := by positivity
      have h3' : (0 : ℝ) ≤ e2 ^ 2 * e3 ^ 4 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1' hcb4.le) h2') hd2') h3'
    have hpos2 : 0 ≤ 2 * (r - 1) * (2 * r + k + 1) * (c + b) ^ 4 *
        (a ^ 2 * b ^ 3 * c ^ 4 * d) * (e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) *
        (e2 ^ 4 * e3 ^ 2) := by
      have h1' : 0 ≤ 2 * (r - 1) * (2 * r + k + 1) := by
        have := mul_nonneg hrm1 (show (0 : ℝ) ≤ 2 * r + k + 1 by linarith)
        linarith
      have h2' : (0 : ℝ) ≤ a ^ 2 * b ^ 3 * c ^ 4 * d := by positivity
      have h3' : (0 : ℝ) ≤ e2 ^ 4 * e3 ^ 2 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1' hcb4.le) h2') hd1') h3'
    have hpos3 : 0 ≤ 2 * ((k - 1) * (r - 1)) * (2 * k * r + 2 * k + 2 * r + 1) *
        (c + b) ^ 4 * (a * b ^ 3 * c ^ 3 * d) *
        ((e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) * (e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2)) *
        (e2 ^ 2 * e3 ^ 2) := by
      have h1' : 0 ≤ 2 * ((k - 1) * (r - 1)) * (2 * k * r + 2 * k + 2 * r + 1) := by
        have hg := mul_nonneg hkm1 hrm1
        have hlin : (0 : ℝ) ≤ 2 * k * r + 2 * k + 2 * r + 1 := by
          have := mul_pos hk0 hr0
          nlinarith
        have := mul_nonneg hg hlin
        linarith
      have h2' : (0 : ℝ) ≤ a * b ^ 3 * c ^ 3 * d := by positivity
      have h3' : (0 : ℝ) ≤ e2 ^ 2 * e3 ^ 2 := by positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1' hcb4.le) h2')
        (mul_nonneg hd1' hd2')) h3'
    have hpos4 : 0 ≤ (c + b) ^ 4 * (b ^ 2 * c ^ 2) *
        ((k - 1) * (r - 1) *
          ((e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2) * (e3 ^ 2 * (b * d)) +
            (e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) * (e1 * e3 * b ^ 2))) *
        (2 * (a * b * c * d) * (e2 ^ 2 * e3 ^ 2) -
          (k - 1) * (r - 1) *
            ((e2 ^ 2 * (a * c) - e1 * e3 * b ^ 2) * (e3 ^ 2 * (b * d)) +
              (e3 ^ 2 * (b * d) - e2 * e4 * c ^ 2) * (e1 * e3 * b ^ 2))) := by
      have h1' : (0 : ℝ) ≤ (c + b) ^ 4 * (b ^ 2 * c ^ 2) := by positivity
      exact mul_nonneg (mul_nonneg h1'
        (mul_nonneg (mul_nonneg hkm1 hrm1) hS)) hR
    -- Assemble and divide by the positive prefactor.
    have hkey : 0 ≤ ((k + 1) * (r + 1)) ^ 2 * (a ^ 2 * b ^ 4 * c ^ 4 * d ^ 2) *
        (e2 ^ 2 * e3 ^ 2) *
        (4 * (e2 ^ 2 * ((b + a) * (d + c)) - e1 * e3 * (c + b) ^ 2) *
            (e3 ^ 2 * ((b + a) * (d + c)) - e2 * e4 * (c + b) ^ 2) -
          (2 * e3 * e2 * ((b + a) * (d + c)) - (e3 * e2 + e1 * e4) * (c + b) ^ 2) ^ 2) := by
      rw [master]
      have := add_nonneg (add_nonneg (add_nonneg hpos1 hpos2) hpos3) hpos4
      linarith
    have hpref : 0 < ((k + 1) * (r + 1)) ^ 2 * (a ^ 2 * b ^ 4 * c ^ 4 * d ^ 2) *
        (e2 ^ 2 * e3 ^ 2) := by
      have h1' : (0 : ℝ) < (k + 1) * (r + 1) := mul_pos hk1 hr1
      have h2' : (0 : ℝ) < a ^ 2 * b ^ 4 * c ^ 4 * d ^ 2 := by positivity
      have h3' : (0 : ℝ) < e2 ^ 2 * e3 ^ 2 := by positivity
      exact mul_pos (mul_pos (pow_pos h1' 2) h2') h3'
    by_contra hcon
    push_neg at hcon
    have hneg : 4 * (e2 ^ 2 * ((b + a) * (d + c)) - e1 * e3 * (c + b) ^ 2) *
        (e3 ^ 2 * ((b + a) * (d + c)) - e2 * e4 * (c + b) ^ 2) -
        (2 * e3 * e2 * ((b + a) * (d + c)) - (e3 * e2 + e1 * e4) * (c + b) ^ 2) ^ 2 < 0 := by
      linarith
    have := mul_neg_of_pos_of_neg hpref hneg
    linarith

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
