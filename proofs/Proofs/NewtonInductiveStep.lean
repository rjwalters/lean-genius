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
