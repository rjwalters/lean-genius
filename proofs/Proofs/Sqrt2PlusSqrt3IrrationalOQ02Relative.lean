import Proofs.Sqrt2PlusSqrt3IrrationalOQ02

/-
# Besicovitch induction heart, first relative level:  √c ∉ ℚ(√a, √b)   (OQ-02)

The general Besicovitch theorem (`sqrt2-plus-sqrt3-irrational-oq-02`) — the square
roots of distinct squarefree integers are ℚ-linearly independent — is proved by
induction on the number of prime radicands. The base file
`Sqrt2PlusSqrt3IrrationalOQ02.lean` discharges the **first** degree-doubling step
`√b ∉ ℚ(√a)` (`sqrtb_not_in_Qsqrta`) and the biquadratic independence of
`{1, √a, √b, √(ab)}` (`linearIndependent_one_sqrt_sqrt_sqrt`).

The sibling `Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ02.lean` leaves the *general*
induction heart `sqrt_prime_not_mem_multiquadratic` as `sorry`. This file proves
its **first non-trivial instance** completely and elementarily:

> For pairwise-coprime squarefree `a, b, c > 1`,
> `√c ∉ ℚ(√a, √b)`, i.e. there are **no** rationals `p, q, r, s` with
> `√c = p + q√a + r√b + s√(ab)`.

This is the `n = 2 → n = 3` step of Besicovitch's induction. Combined with the
biquadratic case it yields `[ℚ(√a, √b, √c) : ℚ] = 8` for such triples.

## Method (no field/Galois API — explicit ℚ-coordinates, reusing the base file)
Square `√c = p + q√a + r√b + s√(ab)`. Since `{1, √a, √b, √(ab)}` is ℚ-linearly
independent (`linearIndependent_one_sqrt_sqrt_sqrt`) and `c` is rational, matching
coordinates gives four equations
    p²+q²a+r²b+s²ab = c,   pq+rsb = 0,   pr+qsa = 0,   ps+qr = 0.
The last two force `r(p²−aq²) = s(p²−aq²) = 0`. Either
* `p² ≠ aq²`, so `r = s = 0` and `√c = p + q√a ∈ ℚ(√a)`, contradicting
  `sqrtb_not_in_Qsqrta` (radicands `a, c`); or
* `p² = aq²`, so `p = q = 0` (else `√a` rational), leaving `√c = r√b` or
  `√c = s√(ab)`, each making `√(bc)` resp. `√(abc)` rational — impossible as
  `bc`, `abc` are squarefree `> 1`.
-/

namespace Sqrt2PlusSqrt3IrrationalOQ02

open Real

/-- Auxiliary: if `t² · m = n` in ℝ for coprime squarefree `m, n > 1` (naturals),
then `√(m·n)` would be the rational `|t·m|`, contradicting its irrationality.
Used to kill the residual `√c = r√b` / `√c = s√(ab)` branches. -/
theorem prod_not_rat_sq {m n : ℕ} (t : ℚ)
    (hsm : Squarefree m) (hsn : Squarefree n) (hcop : m.Coprime n)
    (hm1 : m ≠ 1) (ht : (t : ℝ) ^ 2 * (m : ℝ) = (n : ℝ)) : False := by
  have hsmn : Squarefree (m * n) := (Nat.squarefree_mul hcop).mpr ⟨hsm, hsn⟩
  have hmn1 : m * n ≠ 1 := fun hh => hm1 (Nat.eq_one_of_dvd_one ⟨n, hh.symm⟩)
  have hirr : Irrational (Real.sqrt ((m : ℝ) * (n : ℝ))) := by
    have hI := irrational_sqrt_of_squarefree hsmn hmn1
    rwa [Nat.cast_mul] at hI
  -- √(m·n) = |t·m| is rational.
  have hsq : ((t : ℝ) * (m : ℝ)) ^ 2 = (m : ℝ) * (n : ℝ) := by
    rw [mul_pow, ← ht]; ring
  have hval : Real.sqrt ((m : ℝ) * (n : ℝ)) = ((|t * (m : ℚ)| : ℚ) : ℝ) := by
    rw [← hsq, Real.sqrt_sq_eq_abs]; push_cast; rw [abs_mul]
  exact hirr ⟨_, hval.symm⟩

/-- **Besicovitch induction heart, first relative level.** For pairwise-coprime
squarefree `a, b, c > 1`, `√c` is not a ℚ-linear combination of `1, √a, √b, √(ab)`
— equivalently `√c ∉ ℚ(√a, √b)`, so `[ℚ(√a,√b,√c) : ℚ] = 8`. -/
theorem sqrtc_not_mem_biquadratic {a b c : ℕ}
    (hsa : Squarefree a) (hsb : Squarefree b) (hsc : Squarefree c)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hc1 : c ≠ 1)
    (hab : a.Coprime b) (hac : a.Coprime c) (hbc : b.Coprime c) :
    ¬ ∃ p q r s : ℚ, Real.sqrt c
      = (p : ℝ) + (q : ℝ) * Real.sqrt a + (r : ℝ) * Real.sqrt b
        + (s : ℝ) * Real.sqrt ((a : ℝ) * (b : ℝ)) := by
  rintro ⟨p, q, r, s, hc⟩
  -- Irrationality inputs.
  have ha_irr := irrational_sqrt_of_squarefree hsa ha1
  have hb_irr := irrational_sqrt_of_squarefree hsb hb1
  have hc_irr := irrational_sqrt_of_squarefree hsc hc1
  have hac_irr : Irrational (Real.sqrt ((a : ℝ) * (c : ℝ))) := by
    have hsac : Squarefree (a * c) := (Nat.squarefree_mul hac).mpr ⟨hsa, hsc⟩
    have hac1 : a * c ≠ 1 := fun hh => ha1 (Nat.eq_one_of_dvd_one ⟨c, hh.symm⟩)
    have hI := irrational_sqrt_of_squarefree hsac hac1
    rwa [Nat.cast_mul] at hI
  have hsa2 : Real.sqrt (a : ℝ) ^ 2 = (a : ℝ) := Real.sq_sqrt (by positivity)
  have hsb2 : Real.sqrt (b : ℝ) ^ 2 = (b : ℝ) := Real.sq_sqrt (by positivity)
  have habmul : Real.sqrt ((a : ℝ) * (b : ℝ)) = Real.sqrt a * Real.sqrt b :=
    Real.sqrt_mul (by positivity) _
  -- Rewrite √c in the `A + B√a + …` shape with √(ab) expanded, then square.
  have hc' : Real.sqrt c
      = (p : ℝ) + (q : ℝ) * Real.sqrt a + (r : ℝ) * Real.sqrt b
        + (s : ℝ) * (Real.sqrt a * Real.sqrt b) := by rw [hc, habmul]
  have hR2 : (c : ℝ)
      = ((p : ℝ) + (q : ℝ) * Real.sqrt a + (r : ℝ) * Real.sqrt b
          + (s : ℝ) * (Real.sqrt a * Real.sqrt b)) ^ 2 := by
    rw [← hc']; exact (Real.sq_sqrt (by positivity)).symm
  -- Coordinates of `c` in the basis {1,√a,√b,√(ab)} all vanish (after moving c).
  have hEq :
      ((p ^ 2 + q ^ 2 * (a : ℚ) + r ^ 2 * (b : ℚ) + s ^ 2 * ((a : ℚ) * (b : ℚ))
          - (c : ℚ) : ℚ) : ℝ)
      + ((2 * (p * q + r * s * (b : ℚ)) : ℚ) : ℝ) * Real.sqrt a
      + ((2 * (p * r + q * s * (a : ℚ)) : ℚ) : ℝ) * Real.sqrt b
      + ((2 * (p * s + q * r) : ℚ) : ℝ) * Real.sqrt ((a : ℝ) * (b : ℝ)) = 0 := by
    rw [habmul]; push_cast
    linear_combination (-1 : ℝ) * hR2
      - ((q : ℝ) + (s : ℝ) * Real.sqrt b) ^ 2 * hsa2
      - ((r : ℝ) ^ 2 + (s : ℝ) ^ 2 * (a : ℝ) + 2 * (r : ℝ) * (s : ℝ) * Real.sqrt a) * hsb2
  obtain ⟨hP, hQ, hR, hS⟩ :=
    linearIndependent_one_sqrt_sqrt_sqrt hsa hsb ha1 hb1 hab _ _ _ _ hEq
  -- Turn the four coordinate equations into usable polynomial relations.
  have eP : p ^ 2 + q ^ 2 * (a : ℚ) + r ^ 2 * (b : ℚ) + s ^ 2 * ((a : ℚ) * (b : ℚ))
      = (c : ℚ) := by linear_combination hP
  have eQ : p * q + r * s * (b : ℚ) = 0 := by linear_combination (1 / 2 : ℚ) * hQ
  have eR : p * r + q * s * (a : ℚ) = 0 := by linear_combination (1 / 2 : ℚ) * hR
  have eS : p * s + q * r = 0 := by linear_combination (1 / 2 : ℚ) * hS
  -- r and s are annihilated by (p² − a q²).
  have hrf : r * (p ^ 2 - (a : ℚ) * q ^ 2) = 0 := by linear_combination p * eR - (a : ℚ) * q * eS
  have hsf : s * (p ^ 2 - (a : ℚ) * q ^ 2) = 0 := by linear_combination p * eS - q * eR
  by_cases hpaq : p ^ 2 - (a : ℚ) * q ^ 2 = 0
  · -- p² = a q²  ⟹  p = q = 0.
    have hq0 : q = 0 := by
      by_contra hq
      have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq
      have hpq : (p : ℝ) ^ 2 = (a : ℝ) * (q : ℝ) ^ 2 := by
        have hpq0 : p ^ 2 = (a : ℚ) * q ^ 2 := by linarith [hpaq]
        exact_mod_cast hpq0
      have hxR : ((p / q : ℚ) : ℝ) ^ 2 = (a : ℝ) := by
        push_cast; field_simp; linarith [hpq]
      exact ha_irr ⟨|p / q|, by rw [Rat.cast_abs, ← Real.sqrt_sq_eq_abs, hxR]⟩
    have hp0 : p = 0 := by
      have hp2 : p ^ 2 = 0 := by rw [hq0] at hpaq; ring_nf at hpaq ⊢; linarith [hpaq]
      exact pow_eq_zero_iff (by norm_num) |>.mp hp2
    subst hp0; subst hq0
    -- rs b = 0 ⟹ r = 0 or s = 0.
    have hrsb : r * s * (b : ℚ) = 0 := by linear_combination eQ
    have hbne : (b : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hsb.ne_zero
    rcases mul_eq_zero.mp hrsb with hrs | hb0
    · rcases mul_eq_zero.mp hrs with hr0 | hs0
      · -- r = 0 : √c = s √(ab), so √(c·ab) rational; use abc.
        subst hr0
        -- eP: s²·ab = c
        have hcab : (s : ℝ) ^ 2 * ((a : ℝ) * (b : ℝ)) = (c : ℝ) := by
          have h : s ^ 2 * ((a : ℚ) * (b : ℚ)) = (c : ℚ) := by linear_combination eP
          exact_mod_cast h
        have hsab : Squarefree (a * b) := (Nat.squarefree_mul hab).mpr ⟨hsa, hsb⟩
        have habc_cop : (a * b).Coprime c := Nat.coprime_mul_iff_left.mpr ⟨hac, hbc⟩
        have hab1 : a * b ≠ 1 := fun hh => ha1 (Nat.eq_one_of_dvd_one ⟨b, hh.symm⟩)
        exact prod_not_rat_sq s hsab hsc habc_cop hab1
          (by rw [Nat.cast_mul]; linarith [hcab])
      · -- s = 0 : √c = r √b, so √(bc) rational.
        subst hs0
        have hcb : (r : ℝ) ^ 2 * (b : ℝ) = (c : ℝ) := by
          have h : r ^ 2 * (b : ℚ) = (c : ℚ) := by linear_combination eP
          exact_mod_cast h
        exact prod_not_rat_sq r hsb hsc hbc hb1 hcb
    · exact hbne hb0
  · -- p² ≠ a q² ⟹ r = 0 and s = 0, so √c = p + q√a ∈ ℚ(√a).
    have hr0 : r = 0 := by
      rcases mul_eq_zero.mp hrf with h | h
      · exact h
      · exact absurd h hpaq
    have hs0 : s = 0 := by
      rcases mul_eq_zero.mp hsf with h | h
      · exact h
      · exact absurd h hpaq
    subst hr0; subst hs0
    apply sqrtb_not_in_Qsqrta (a := a) (b := c) ha_irr hc_irr hac_irr
    exact ⟨p, q, by rw [hc]; push_cast; ring⟩

/-- Concrete first instance: `√5 ∉ ℚ(√2, √3)`. There are no rationals with
`√5 = p + q√2 + r√3 + s√6`; hence `[ℚ(√2,√3,√5) : ℚ] = 8`. -/
theorem sqrt5_not_mem_Qsqrt2_sqrt3 :
    ¬ ∃ p q r s : ℚ, Real.sqrt 5
      = (p : ℝ) + (q : ℝ) * Real.sqrt 2 + (r : ℝ) * Real.sqrt 3
        + (s : ℝ) * Real.sqrt ((2 : ℝ) * (3 : ℝ)) := by
  have h := sqrtc_not_mem_biquadratic (a := 2) (b := 3) (c := 5)
    (Nat.prime_two.squarefree) (Nat.prime_three.squarefree)
    ((by norm_num : Nat.Prime 5).squarefree)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  simpa using h

end Sqrt2PlusSqrt3IrrationalOQ02
