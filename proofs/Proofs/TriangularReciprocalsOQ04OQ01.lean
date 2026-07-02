/-
  Reciprocals of Binomial Coefficients — General Depth-d Telescoping

  Result:  for every integer depth d ≥ 2,

      ∑_{n=1}^∞ 1/C(n+d-1, d) = d/(d-1).

  Equivalently, shifting the running index to n : ℕ (term at n being the reciprocal
  of the binomial C(n+d, d)),

      ∑_{n=0}^∞ 1/C(n+d, d) = d/(d-1).

  This is the general-depth analogue of the classical results
    • depth 1 (triangular):    ∑ 2/(n(n+1))            = 2,
    • depth 2 (tetrahedral):   ∑ 6/((n+1)(n+2)(n+3))   = 3/2   (`TriangularReciprocalsOQ04.lean`).
  The parent handles the single case d = 3 (value 3/2) by an explicit depth-2 partial
  fraction; here we prove the entire family d = 2, 3, 4, … at once.

  Method.  Write d = k+2 with k : ℕ (so d ≥ 2 and d-1 = k+1 is a unit).  Let

      P(n, m) = (n+1)(n+2)⋯(n+m)   (an ascending product of m consecutive integers),

  so that 1/C(n+d, d) = d! / P(n, d).  The key telescoping identity is

      d! / P(n, d) = g(n) - g(n+1),   g(n) = d! / ((d-1) · P(n, d-1)),

  which follows from the two one-step product recurrences
      P(n, m+1) = P(n, m) · (n+m+1)      (peel the last factor),
      P(n, m+1) = (n+1) · P(n+1, m)      (peel the first factor).
  Summing telescopes to g(0) = d!/((d-1)·(d-1)!) = d/(d-1), and the tail g(N) → 0
  since P(N, d-1) ≥ N+1.  Finally P(n, d) = C(n+d, d) · d!, giving the binomial form.

  No axioms, no sorries.
-/

import Mathlib

set_option linter.unusedVariables false

open Finset BigOperators Filter Topology

namespace TriangularReciprocalsOQ04OQ01

variable (k : ℕ)

/-- The ascending product `P(n, m) = (n+1)(n+2)⋯(n+m)` as a real number. -/
noncomputable def pochProd (n m : ℕ) : ℝ :=
  ∏ j ∈ Finset.range m, ((n : ℝ) + 1 + (j : ℝ))

/-- The reciprocal-binomial summand `1/C(n+d, d) = d!/P(n, d)` with `d = k+2`. -/
noncomputable def term (n : ℕ) : ℝ :=
  ((k + 2).factorial : ℝ) / pochProd n (k + 2)

/-- The telescoping antiderivative `g(n) = d!/((d-1)·P(n, d-1))` with `d = k+2`. -/
noncomputable def gAnti (n : ℕ) : ℝ :=
  ((k + 2).factorial : ℝ) / (((k : ℝ) + 1) * pochProd n (k + 1))

-- ═══════════════════════════════════════════════════
-- Product recurrences
-- ═══════════════════════════════════════════════════

/-- Peel the last factor: `P(n, m+1) = P(n, m) · (n+m+1)`. -/
theorem poch_rec2 (n m : ℕ) :
    pochProd n (m + 1) = pochProd n m * ((n : ℝ) + 1 + (m : ℝ)) := by
  unfold pochProd
  rw [Finset.prod_range_succ]

/-- Peel the first factor: `P(n, m+1) = (n+1) · P(n+1, m)`. -/
theorem poch_rec (n m : ℕ) :
    pochProd n (m + 1) = ((n : ℝ) + 1) * pochProd (n + 1) m := by
  unfold pochProd
  rw [Finset.prod_range_succ', Nat.cast_zero, add_zero, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  push_cast
  ring

/-- Every factor is positive, so the product is positive. -/
theorem pochProd_pos (n m : ℕ) : 0 < pochProd n m := by
  unfold pochProd
  apply Finset.prod_pos
  intro i _
  positivity

/-- Every factor is `≥ 1`, so the product is `≥ 1`. -/
theorem pochProd_one_le (n m : ℕ) : 1 ≤ pochProd n m := by
  induction m with
  | zero => simp [pochProd]
  | succ p ih =>
    rw [poch_rec2 n p]
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 + (p : ℝ) := by
      have : (0 : ℝ) ≤ (n : ℝ) + (p : ℝ) := by positivity
      linarith
    nlinarith [ih, h1, mul_nonneg (sub_nonneg.mpr ih) (sub_nonneg.mpr h1)]

/-- `P(0, m) = m!`. -/
theorem pochProd_zero (m : ℕ) : pochProd 0 m = ((m.factorial : ℝ)) := by
  induction m with
  | zero => simp [pochProd]
  | succ p ih =>
    rw [poch_rec2 0 p, ih]
    have hfac : (p + 1).factorial = (p + 1) * p.factorial := Nat.factorial_succ p
    rw [hfac]; push_cast; ring

/-- `P(n, m) · n! = (n+m)!`, an integer identity cast to `ℝ`. -/
theorem pochProd_mul_factorial (n m : ℕ) :
    pochProd n m * (n.factorial : ℝ) = ((n + m).factorial : ℝ) := by
  induction m with
  | zero => simp [pochProd]
  | succ p ih =>
    rw [poch_rec2 n p, mul_right_comm, ih]
    have e : n + (p + 1) = (n + p) + 1 := by ring
    rw [e]
    have hfac : ((n + p) + 1).factorial = ((n + p) + 1) * (n + p).factorial :=
      Nat.factorial_succ (n + p)
    rw [hfac]; push_cast; ring

-- ═══════════════════════════════════════════════════
-- Telescoping identity
-- ═══════════════════════════════════════════════════

/-- The depth-`d` telescoping identity `term n = g(n) - g(n+1)`. -/
theorem telescope (n : ℕ) : term k n = gAnti k n - gAnti k (n + 1) := by
  unfold term gAnti
  have hp2 : (0 : ℝ) < pochProd n (k + 2) := pochProd_pos _ _
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnk2 : (0 : ℝ) < (n : ℝ) + 1 + ((k : ℝ) + 1) := by positivity
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  -- P(n, k+2) = (n+1) · P(n+1, k+1)
  have hA : pochProd n (k + 2) = ((n : ℝ) + 1) * pochProd (n + 1) (k + 1) := poch_rec n (k + 1)
  -- P(n, k+2) = P(n, k+1) · (n+k+2)
  have hB : pochProd n (k + 2) = pochProd n (k + 1) * ((n : ℝ) + 1 + ((k : ℝ) + 1)) := by
    have h := poch_rec2 n (k + 1)
    push_cast at h
    linear_combination h
  -- express both (k+1)-products through P(n, k+2)
  have hXA : pochProd (n + 1) (k + 1) = pochProd n (k + 2) / ((n : ℝ) + 1) := by
    rw [eq_div_iff hn1.ne']; rw [hA]; ring
  have hXB : pochProd n (k + 1) = pochProd n (k + 2) / ((n : ℝ) + 1 + ((k : ℝ) + 1)) := by
    rw [eq_div_iff hnk2.ne']; rw [hB]
  rw [hXA, hXB]
  field_simp
  ring

-- ═══════════════════════════════════════════════════
-- Partial sums and limit
-- ═══════════════════════════════════════════════════

/-- Telescoped closed form: `∑_{i<N} term i = g(0) - g(N)`. -/
theorem partial_sum (N : ℕ) :
    ∑ i ∈ Finset.range N, term k i = gAnti k 0 - gAnti k N := by
  induction N with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, telescope k M]; ring

/-- `g(0) = d/(d-1) = (k+2)/(k+1)`. -/
theorem gAnti_zero : gAnti k 0 = ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
  unfold gAnti
  rw [pochProd_zero (k + 1)]
  have h1 : ((k + 2).factorial : ℝ) = ((k : ℝ) + 2) * ((k + 1).factorial : ℝ) := by
    have hfac : (k + 2).factorial = (k + 2) * (k + 1).factorial := Nat.factorial_succ (k + 1)
    rw [hfac]; push_cast; ring
  rw [h1]
  have hf : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast (k + 1).factorial_pos
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  field_simp

/-- The tail `g(N) → 0` as `N → ∞`. -/
theorem gAnti_tendsto : Tendsto (fun N : ℕ => gAnti k N) atTop (𝓝 0) := by
  set C : ℝ := ((k + 2).factorial : ℝ) / ((k : ℝ) + 1) with hC
  have hg0 : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun N : ℕ => C / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    have h := hg0.const_mul C
    rw [mul_zero] at h
    simpa [mul_one_div] using h
  apply squeeze_zero (g := fun N : ℕ => C / ((N : ℝ) + 1))
  · intro N
    unfold gAnti
    apply div_nonneg (by positivity)
    exact mul_nonneg (by positivity) (pochProd_pos N (k + 1)).le
  · intro N
    have hge : ((N : ℝ) + 1) ≤ pochProd N (k + 1) := by
      rw [poch_rec]
      have := mul_le_mul_of_nonneg_left (pochProd_one_le (N + 1) k)
        (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
      simpa using this
    unfold gAnti
    rw [hC, div_mul_eq_div_div, ← hC]
    gcongr
  · exact hlim

-- ═══════════════════════════════════════════════════
-- Main theorem
-- ═══════════════════════════════════════════════════

/-- The reciprocal binomial series sums to `g(0)`. -/
theorem hasSum_term : HasSum (term k) (gAnti k 0) := by
  have hnn : ∀ n, 0 ≤ term k n := by
    intro n; unfold term
    exact div_nonneg (by positivity) (pochProd_pos n (k + 2)).le
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hps : (fun N => ∑ i ∈ Finset.range N, term k i) = fun N => gAnti k 0 - gAnti k N :=
    funext (partial_sum k)
  rw [hps]
  have h := (tendsto_const_nhds (x := gAnti k 0)).sub (gAnti_tendsto k)
  simpa using h

/-- `term n = 1/C(n+k+2, k+2)`, connecting the product form to binomial coefficients. -/
theorem term_eq_inv_choose (n : ℕ) :
    term k n = 1 / ((Nat.choose (n + k + 2) (k + 2) : ℕ) : ℝ) := by
  have hle : k + 2 ≤ n + k + 2 := by omega
  have hn : Nat.choose (n + k + 2) (k + 2) * (k + 2).factorial * n.factorial
      = (n + k + 2).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial hle
    rwa [show (n + k + 2) - (k + 2) = n by omega] at h
  have hp : pochProd n (k + 2) * (n.factorial : ℝ) = ((n + k + 2).factorial : ℝ) := by
    have h := pochProd_mul_factorial n (k + 2)
    rwa [show n + (k + 2) = n + k + 2 from by ring] at h
  have hnR : ((Nat.choose (n + k + 2) (k + 2) : ℝ)) * ((k + 2).factorial : ℝ) * (n.factorial : ℝ)
      = ((n + k + 2).factorial : ℝ) := by exact_mod_cast hn
  have hn0 : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_pos.ne'
  have hpoch : pochProd n (k + 2)
      = (Nat.choose (n + k + 2) (k + 2) : ℝ) * ((k + 2).factorial : ℝ) := by
    have h2 : (Nat.choose (n + k + 2) (k + 2) : ℝ) * ((k + 2).factorial : ℝ) * (n.factorial : ℝ)
        = pochProd n (k + 2) * (n.factorial : ℝ) := by rw [hnR, hp]
    exact (mul_right_cancel₀ hn0 h2).symm
  unfold term
  rw [hpoch]
  have hc : (0 : ℝ) < (Nat.choose (n + k + 2) (k + 2) : ℝ) := by
    exact_mod_cast Nat.choose_pos hle
  have hf : (0 : ℝ) < ((k + 2).factorial : ℝ) := by exact_mod_cast (k + 2).factorial_pos
  field_simp

/-- **Reciprocal binomial sum (k-form).**  `∑_{n≥0} 1/C(n+k+2, k+2) = (k+2)/(k+1)`. -/
theorem reciprocal_binomial_hasSum :
    HasSum (fun n => 1 / ((Nat.choose (n + k + 2) (k + 2) : ℕ) : ℝ))
      (((k : ℝ) + 2) / ((k : ℝ) + 1)) := by
  have h := hasSum_term k
  rw [gAnti_zero] at h
  have he : (fun n => 1 / ((Nat.choose (n + k + 2) (k + 2) : ℕ) : ℝ)) = term k := by
    funext n; rw [term_eq_inv_choose]
  rw [he]; exact h

/-- **Reciprocal binomial sum (d-form).**  For every depth `d ≥ 2`,

      ∑_{n=0}^∞ 1/C(n+d, d) = d/(d-1),

    equivalently `∑_{m≥1} 1/C(m+d-1, d) = d/(d-1)`. -/
theorem reciprocal_binomial_sum_d (d : ℕ) (hd : 2 ≤ d) :
    HasSum (fun n => 1 / ((Nat.choose (n + d) d : ℕ) : ℝ)) ((d : ℝ) / ((d : ℝ) - 1)) := by
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 2 := ⟨d - 2, by omega⟩
  have h := reciprocal_binomial_hasSum k
  have e2 : (((k + 2 : ℕ) : ℝ)) / (((k + 2 : ℕ) : ℝ) - 1) = ((k : ℝ) + 2) / ((k : ℝ) + 1) := by
    push_cast; ring
  rw [e2]
  exact h

/-- tsum form of the general reciprocal-binomial identity. -/
theorem reciprocal_binomial_tsum (d : ℕ) (hd : 2 ≤ d) :
    ∑' n : ℕ, 1 / ((Nat.choose (n + d) d : ℕ) : ℝ) = (d : ℝ) / ((d : ℝ) - 1) :=
  (reciprocal_binomial_sum_d d hd).tsum_eq

-- ═══════════════════════════════════════════════════
-- Sanity checks
-- ═══════════════════════════════════════════════════

/-- Depth `d = 3` recovers the parent tetrahedral value `3/2`. -/
example : HasSum (fun n => 1 / ((Nat.choose (n + 3) 3 : ℕ) : ℝ)) (3 / 2 : ℝ) := by
  have h := reciprocal_binomial_sum_d 3 (by norm_num)
  norm_num at h
  simpa using h

/-- Depth `d = 2` gives `∑ 1/C(n+2,2) = 2`, the classical triangular value. -/
example : HasSum (fun n => 1 / ((Nat.choose (n + 2) 2 : ℕ) : ℝ)) (2 : ℝ) := by
  have h := reciprocal_binomial_sum_d 2 (by norm_num)
  norm_num at h
  simpa using h

end TriangularReciprocalsOQ04OQ01
