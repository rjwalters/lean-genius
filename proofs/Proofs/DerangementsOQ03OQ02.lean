/-
  Poisson(1) Approximation in Total Variation
  Open Question: derangements-oq-03-oq-02

  Main Result: The number of fixed points of a uniformly random permutation of [n]
  converges in total variation distance to the Poisson(1) distribution.

  Let X_n = #{i : σ(i) = i} for uniform random σ ∈ Sym(n). We prove:
    ∑' k, |P(X_n = k) - e⁻¹/k!| → 0  as n → ∞

  (The TV distance is half this ℓ¹ distance.)

  Proof:
  1. P(X_n = k) = D(n-k) / ((n-k)! · k!)  for k ≤ n,  0  for k > n
  2. |P(X_n = k) - e⁻¹/k!| ≤ 1/((n-k+1)!·k!)  for k ≤ n
     (using the alternating series bound |D(m)/m! - e⁻¹| ≤ 1/(m+1)!)
  3. ∑_{k=0}^n 1/((n+1-k)!·k!) = (∑_{k=0}^n C(n+1,k))/(n+1)! ≤ 2^{n+1}/(n+1)!
  4. 2^{n+1}/(n+1)! → 0
  5. ∑_{k>n} e⁻¹/k! → 0  (tail of convergent series)

  Axioms: 0
  Sorries: 0
-/

import Mathlib.Combinatorics.Derangements.Finite
import Mathlib.Combinatorics.Derangements.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

open Finset Nat Real BigOperators Filter Topology

noncomputable section

namespace DerangementsOQ03OQ02

-- ============================================================
-- Section I: Alternating Series Bound for Derangements
-- ============================================================

private def altTerm (k : ℕ) : ℝ := (-1 : ℝ) ^ k / (k.factorial : ℝ)
private def altPartialSum (n : ℕ) : ℝ := ∑ k ∈ range (n + 1), altTerm k

private lemma fpos (k : ℕ) : (0 : ℝ) < (k.factorial : ℝ) := Nat.cast_pos.mpr k.factorial_pos
private lemma fne (k : ℕ) : (k.factorial : ℝ) ≠ 0 := (fpos k).ne'

private lemma altTerm_abs (k : ℕ) : |altTerm k| = 1 / (k.factorial : ℝ) := by
  simp [altTerm, abs_div, abs_pow, abs_neg, abs_one]

private lemma altPartialSum_succ (n : ℕ) :
    altPartialSum (n + 1) = altPartialSum n + altTerm (n + 1) := by
  simp [altPartialSum, Finset.sum_range_succ]

private lemma summable_altTerm : Summable altTerm :=
  summable_pow_div_factorial (-1)

private theorem exp_neg_one_eq_tsum :
    rexp (-1) = ∑' k, altTerm k := by
  rw [show rexp (-1) = NormedSpace.exp ℝ (-1:ℝ) from by rw [Real.exp_eq_exp_ℝ],
      NormedSpace.exp_eq_tsum (𝕂 := ℝ) (𝔸 := ℝ)]
  apply tsum_congr; intro k; simp only [altTerm, smul_eq_mul]; ring

/-- General tail splitting: ∑' f = ∑_{k<N} f k + ∑' f(N+k) for summable f -/
private lemma tsum_split {f : ℕ → ℝ} (hf : Summable f) (N : ℕ) :
    ∑' k, f k = ∑ k ∈ range N, f k + ∑' k, f (N + k) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hshift : Summable (fun k => f (N + k)) :=
      hf.comp_injective (fun a b h => by omega)
    have hstep : ∑' k, f (N + k) = f N + ∑' k, f (N + 1 + k) := by
      rw [hshift.tsum_eq_zero_add]
      simp only [Nat.add_zero]
      congr 1
      apply tsum_congr; intro k; ring
    rw [ih, hstep, Finset.sum_range_succ]
    ring

private lemma alt_nonneg (m N : ℕ) :
    0 ≤ ∑ k ∈ range N, ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  match N with
  | 0 => simp
  | 1 =>
    simp only [range_one, sum_singleton, pow_zero, zero_add]
    exact div_nonneg one_pos.le (fpos m).le
  | N' + 2 =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    by_cases hN' : Even N'
    · obtain ⟨j, rfl⟩ := hN'  -- N' = j + j
      have hpair : 0 ≤ (-1:ℝ)^(j+j)/((m+(j+j)).factorial:ℝ) +
          (-1:ℝ)^(j+j+1)/((m+(j+j+1)).factorial:ℝ) := by
        have h1 : (-1:ℝ)^(j+j) = 1 := by
          rw [show j+j = 2*j from by ring]; simp [pow_mul, neg_one_sq]
        have h2 : (-1:ℝ)^(j+j+1) = -1 := by
          rw [show j+j+1 = 2*j+1 from by ring]; simp [pow_succ, pow_mul, neg_one_sq]
        rw [h1, h2]
        have hpos1 : (0:ℝ) < ((m+(j+j)).factorial:ℝ) := fpos _
        have hpos2 : (0:ℝ) < ((m+(j+j+1)).factorial:ℝ) := fpos _
        have hle : ((m+(j+j)).factorial:ℝ) ≤ ((m+(j+j+1)).factorial:ℝ) :=
          by exact_mod_cast Nat.factorial_le (by omega)
        rw [show (1:ℝ) / ((m+(j+j)).factorial:ℝ) + (-1:ℝ) / ((m+(j+j+1)).factorial:ℝ) =
          (((m+(j+j+1)).factorial:ℝ) - ((m+(j+j)).factorial:ℝ)) /
          (((m+(j+j)).factorial:ℝ) * ((m+(j+j+1)).factorial:ℝ)) from by field_simp; ring]
        exact div_nonneg (by linarith) (mul_pos hpos1 hpos2).le
      linarith [ih (j+j) (by omega), hpair]
    · rw [Nat.not_even_iff_odd] at hN'; obtain ⟨j, rfl⟩ := hN'
      have hpair : 0 ≤ (-1:ℝ)^(2*j)/((m+2*j).factorial:ℝ) +
          (-1:ℝ)^(2*j+1)/((m+(2*j+1)).factorial:ℝ) := by
        have h1 : (-1:ℝ)^(2*j) = 1 := by simp [pow_mul, neg_one_sq]
        have h2 : (-1:ℝ)^(2*j+1) = -1 := by simp [pow_succ, pow_mul, neg_one_sq]
        rw [h1, h2]
        have hpos1 : (0:ℝ) < ((m+2*j).factorial:ℝ) := fpos _
        have hpos2 : (0:ℝ) < ((m+(2*j+1)).factorial:ℝ) := fpos _
        have hle : ((m+2*j).factorial:ℝ) ≤ ((m+(2*j+1)).factorial:ℝ) :=
          by exact_mod_cast Nat.factorial_le (by omega)
        rw [show (1:ℝ) / ((m+2*j).factorial:ℝ) + (-1:ℝ) / ((m+(2*j+1)).factorial:ℝ) =
          (((m+(2*j+1)).factorial:ℝ) - ((m+2*j).factorial:ℝ)) /
          (((m+2*j).factorial:ℝ) * ((m+(2*j+1)).factorial:ℝ)) from by field_simp; ring]
        exact div_nonneg (by linarith) (mul_pos hpos1 hpos2).le
      have hlast : 0 ≤ (-1:ℝ)^(2*j+2)/((m+(2*j+2)).factorial:ℝ) :=
        div_nonneg (by simp [pow_succ, pow_mul]) (fpos _).le
      have hsucc : ∑ k ∈ range (2*j+1), ((-1:ℝ)^k / ((m+k).factorial:ℝ)) =
          ∑ k ∈ range (2*j), ((-1:ℝ)^k / ((m+k).factorial:ℝ)) +
          (-1:ℝ)^(2*j) / ((m+2*j).factorial:ℝ) := by
        rw [show 2*j+1 = 2*j + 1 from by omega, Finset.sum_range_succ]
      linarith [ih (2*j) (by omega), hpair, hlast, hsucc]

private lemma alt_le_first (m N : ℕ) :
    ∑ k ∈ range N, ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) ≤ 1 / (m.factorial : ℝ) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  match N with
  | 0 =>
    simp only [range_zero, sum_empty]
    exact div_nonneg one_pos.le (fpos m).le
  | 1 => simp [range_one, pow_zero, zero_add]
  | N' + 2 =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    by_cases hN' : Even N'
    · obtain ⟨j, rfl⟩ := hN'  -- N' = j + j
      have hneg : (-1:ℝ)^(j+j+1)/((m+(j+j+1)).factorial:ℝ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg
          (by rw [show j+j+1 = 2*j+1 from by ring]; simp [pow_succ, pow_mul, neg_one_sq])
          (fpos _).le
      have hss := Finset.sum_range_succ (fun k => (-1:ℝ)^k/((m+k).factorial:ℝ)) (j+j)
      linarith [ih (j+j+1) (by omega), hneg, hss]
    · rw [Nat.not_even_iff_odd] at hN'; obtain ⟨j, rfl⟩ := hN'
      have hpair : (-1:ℝ)^(2*j+1)/((m+(2*j+1)).factorial:ℝ) +
          (-1:ℝ)^(2*j+2)/((m+(2*j+2)).factorial:ℝ) ≤ 0 := by
        have h1 : (-1:ℝ)^(2*j+1) = -1 := by simp [pow_succ, pow_mul, neg_one_sq]
        have h2 : (-1:ℝ)^(2*j+2) = 1 := by
          rw [show 2*j+2 = 2*(j+1) from by ring]; simp [pow_mul, neg_one_sq]
        rw [h1, h2]
        have hpos1 : (0:ℝ) < ((m+(2*j+1)).factorial:ℝ) := fpos _
        have hpos2 : (0:ℝ) < ((m+(2*j+2)).factorial:ℝ) := fpos _
        have hle : ((m+(2*j+1)).factorial:ℝ) ≤ ((m+(2*j+2)).factorial:ℝ) :=
          by exact_mod_cast Nat.factorial_le (by omega)
        rw [show (-1:ℝ) / ((m+(2*j+1)).factorial:ℝ) + 1 / ((m+(2*j+2)).factorial:ℝ) =
          (((m+(2*j+1)).factorial:ℝ) - ((m+(2*j+2)).factorial:ℝ)) /
          (((m+(2*j+1)).factorial:ℝ) * ((m+(2*j+2)).factorial:ℝ)) from by field_simp; ring]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) (mul_pos hpos1 hpos2).le
      linarith [ih (2*j+1) (by omega), hpair]

private theorem alt_tail_bound (n : ℕ) :
    |∑' k, altTerm (n + 1 + k)| ≤ 1 / ((n + 1).factorial : ℝ) := by
  set m := n + 1
  have hfactor : ∀ k, altTerm (m + k) =
      (-1 : ℝ) ^ m * ((-1 : ℝ) ^ k / ((m + k).factorial : ℝ)) := by
    intro k; simp [altTerm, pow_add, mul_div_assoc]
  conv_lhs => arg 1; arg 1; ext k; rw [hfactor]
  rw [tsum_mul_left, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  have hbnd : Summable (fun k : ℕ => 1 / ((m + k).factorial : ℝ)) := by
    have h2 : Summable (fun k : ℕ => (1:ℝ) / (k.factorial : ℝ)) :=
      (summable_pow_div_factorial 1).congr (fun k => by simp [one_pow])
    exact h2.comp_injective (fun a b (h : m + a = m + b) => by omega)
  have hcs : Summable (fun k : ℕ => (-1:ℝ)^k / ((m+k).factorial:ℝ)) := by
    have haltshift : Summable (fun k : ℕ => altTerm (m + k)) :=
      summable_altTerm.comp_injective (fun a b (h : m + a = m + b) => by omega)
    have hpow_ne : (-1:ℝ)^m ≠ 0 := pow_ne_zero _ (by norm_num)
    -- altTerm(m+k)/(-1)^m = (-1)^k/(m+k)! via hfactor
    exact (haltshift.div_const ((-1:ℝ)^m)).congr (fun k => by
      rw [hfactor k]; field_simp [hpow_ne])
  have hlower : 0 ≤ ∑' k, (-1:ℝ)^k / ((m+k).factorial:ℝ) := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hcs.hasSum.tendsto_sum_nat
    filter_upwards with N; exact alt_nonneg m N
  rw [abs_of_nonneg hlower]
  apply le_of_tendsto hcs.hasSum.tendsto_sum_nat
  filter_upwards with N; exact alt_le_first m N

private lemma numDerangements_eq_factorial_mul_altPartialSum (n : ℕ) :
    (numDerangements n : ℝ) = (n.factorial : ℝ) * altPartialSum n := by
  induction n with
  | zero => simp [altPartialSum, altTerm]
  | succ n ih =>
    have hsucc_r : (numDerangements (n + 1) : ℝ) =
        ((n : ℝ) + 1) * (numDerangements n : ℝ) - (-1 : ℝ) ^ n := by
      exact_mod_cast numDerangements_succ n
    rw [hsucc_r, ih, altPartialSum_succ n]
    have hterm : ((n + 1).factorial : ℝ) * altTerm (n + 1) = (-1 : ℝ) ^ (n + 1) := by
      rw [altTerm, mul_comm]
      exact div_mul_cancel₀ _ (fne (n + 1))
    have hfact : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * ((n.factorial : ℝ)) := by
      exact_mod_cast Nat.factorial_succ n
    rw [mul_add, hterm, hfact, pow_succ]
    ring

/-- Sharp convergence rate: |D(m)/m! - e⁻¹| ≤ 1/(m+1)! -/
theorem derangement_rate (m : ℕ) :
    |(numDerangements m : ℝ) / (m.factorial : ℝ) - rexp (-1)| ≤ 1 / ((m + 1).factorial : ℝ) := by
  have hid : (numDerangements m : ℝ) / (m.factorial : ℝ) = altPartialSum m := by
    rw [numDerangements_eq_factorial_mul_altPartialSum]; field_simp [fne m]
  rw [hid, exp_neg_one_eq_tsum]
  simp only [altPartialSum]
  have hts : ∑' k, altTerm k = ∑ k ∈ range (m+1), altTerm k + ∑' k, altTerm (m + 1 + k) :=
    tsum_split summable_altTerm (m+1)
  rw [show ∑ k ∈ range (m+1), altTerm k - ∑' k, altTerm k =
      -(∑' k, altTerm (m + 1 + k)) from by linarith, abs_neg]
  exact alt_tail_bound m

/-!
## Section II: Fixed-Point PMF and Poisson(1) PMF
-/

/-- P(X_n = k) = D(n-k)/((n-k)!·k!) for k ≤ n, 0 otherwise -/
noncomputable def fixedPtPMF (n k : ℕ) : ℝ :=
  if k ≤ n then (numDerangements (n - k) : ℝ) / ((n - k).factorial * k.factorial : ℝ)
  else 0

/-- Poisson(1) PMF: P(Z = k) = e⁻¹/k! -/
noncomputable def poisson1PMF (k : ℕ) : ℝ := rexp (-1) / (k.factorial : ℝ)

lemma poisson1PMF_nonneg (k : ℕ) : 0 ≤ poisson1PMF k :=
  div_nonneg (Real.exp_nonneg _) (fpos k).le

lemma fixedPtPMF_nonneg (n k : ℕ) : 0 ≤ fixedPtPMF n k := by
  simp only [fixedPtPMF]; split_ifs with h
  · exact div_nonneg (Nat.cast_nonneg _) (mul_nonneg (fpos _).le (fpos _).le)
  · exact le_refl _

lemma fixedPtPMF_zero (n k : ℕ) (hk : n < k) : fixedPtPMF n k = 0 :=
  if_neg (not_le.mpr hk)

lemma summable_poisson1 : Summable poisson1PMF := by
  have h : Summable (fun k : ℕ => rexp (-1) * ((1:ℝ)^k / (k.factorial : ℝ))) :=
    (summable_pow_div_factorial 1).mul_left (rexp (-1))
  apply h.congr; intro k
  simp [poisson1PMF, one_pow, div_eq_mul_inv]

lemma summable_fixedPtPMF (n : ℕ) : Summable (fixedPtPMF n) :=
  summable_of_ne_finset_zero (s := range (n + 1)) (fun k hk => by
    simp only [mem_range, not_lt] at hk; exact fixedPtPMF_zero n k (by omega))

/-!
## Section III: Pointwise Error Bound
-/

private lemma fixedPtPMF_sub (n k : ℕ) (hk : k ≤ n) :
    fixedPtPMF n k - poisson1PMF k =
    ((numDerangements (n-k) : ℝ) / ((n-k).factorial : ℝ) - rexp (-1)) / (k.factorial : ℝ) := by
  simp only [fixedPtPMF, hk, ↓reduceIte, poisson1PMF]
  field_simp [fne k, fne (n-k)]

/-- For k ≤ n: |P(X_n=k) - e⁻¹/k!| ≤ 1/((n-k+1)!·k!) -/
lemma pointwise_bound (n k : ℕ) (hk : k ≤ n) :
    |fixedPtPMF n k - poisson1PMF k| ≤ 1 / (((n-k+1).factorial * k.factorial) : ℝ) := by
  rw [fixedPtPMF_sub n k hk, abs_div, abs_of_pos (fpos k), ← div_div]
  apply div_le_div_of_nonneg_right _ (fpos k).le
  exact derangement_rate (n - k)

/-!
## Section IV: Finite Sum Bound
-/

/-- Identity: 1/((n+1-k)!·k!) = C(n+1,k)/(n+1)! -/
private lemma inv_fact_eq_choose (n k : ℕ) (hk : k ≤ n) :
    (1 : ℝ) / (((n+1-k).factorial * k.factorial) : ℝ) =
    ((n+1).choose k : ℝ) / ((n+1).factorial : ℝ) := by
  rw [div_eq_div_iff (mul_pos (fpos _) (fpos _)).ne' (fpos _).ne', one_mul]
  have h' : ((n+1).choose k : ℝ) * (k.factorial : ℝ) * ((n+1-k).factorial : ℝ) =
      ((n+1).factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega)
  linear_combination -h'

/-- ∑_{k=0}^n 1/((n+1-k)!·k!) ≤ 2^{n+1}/(n+1)! -/
lemma finite_sum_bound (n : ℕ) :
    ∑ k ∈ range (n+1), (1 : ℝ) / (((n+1-k).factorial * k.factorial) : ℝ) ≤
    (2:ℝ)^(n+1) / ((n+1).factorial : ℝ) := by
  rw [Finset.sum_congr rfl (fun k hk => by
    simp only [mem_range] at hk; exact inv_fact_eq_choose n k (by omega)),
    ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (fpos _).le
  -- ∑_{k=0}^n C(n+1,k) ≤ 2^{n+1}
  -- Use (1+1)^(n+1) = ∑_{k=0}^{n+1} C(n+1,k) ≥ ∑_{k=0}^n C(n+1,k)
  have h_full : ∑ k ∈ range (n+2), (n+1).choose k = 2^(n+1) := by
    have h := add_pow (1:ℕ) 1 (n+1)
    simp only [one_pow, mul_one, one_mul] at h
    rw [show (1:ℕ)+1 = 2 from rfl] at h
    norm_cast at h; exact h.symm
  have h_split := sum_range_succ (fun k => (n+1).choose k) (n+1)
  rw [Nat.choose_self] at h_split
  have h_le : ∑ k ∈ range (n+1), (n+1).choose k ≤ 2^(n+1) := by
    have key : ∑ k ∈ range (n+1), (n+1).choose k + 1 = 2^(n+1) := by
      linarith [h_full, h_split]
    linarith
  exact_mod_cast h_le

/-!
## Section V: Tail Convergence
-/

/-- ∑' poisson1PMF(N+1+k) → 0 -/
theorem poisson1_tail_tendsto :
    Tendsto (fun N => ∑' k, poisson1PMF (N+1+k)) atTop (nhds 0) := by
  have htail : ∀ N, ∑' k, poisson1PMF (N+1+k) =
      ∑' k, poisson1PMF k - ∑ k ∈ range (N+1), poisson1PMF k := by
    intro N; linarith [tsum_split summable_poisson1 (N+1)]
  simp_rw [htail]
  rw [show (0:ℝ) = ∑' k, poisson1PMF k - ∑' k, poisson1PMF k from by ring]
  exact tendsto_const_nhds.sub
    (summable_poisson1.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1))

/-!
## Section VI: Summability of TV Integrand
-/

lemma summable_tv_integrand (n : ℕ) :
    Summable (fun k => |fixedPtPMF n k - poisson1PMF k|) := by
  apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) _
    ((summable_fixedPtPMF n).add summable_poisson1)
  intro k
  have ha := fixedPtPMF_nonneg n k; have hb := poisson1PMF_nonneg k
  rw [abs_le]; constructor <;> linarith

/-!
## Section VII: Main Theorem
-/

/-- Total variation ℓ¹ norm (= 2 × TV distance) between X_n and Poisson(1) -/
noncomputable def tvSum (n : ℕ) : ℝ := ∑' k, |fixedPtPMF n k - poisson1PMF k|

lemma tvSum_le (n : ℕ) :
    tvSum n ≤ (2:ℝ)^(n+1) / ((n+1).factorial:ℝ) + ∑' k, poisson1PMF (n+1+k) := by
  simp only [tvSum]
  rw [tsum_split (summable_tv_integrand n) (n+1)]
  refine _root_.add_le_add ?_ ?_
  · apply (Finset.sum_le_sum (fun k hk => ?_)).trans (finite_sum_bound n)
    simp only [mem_range] at hk
    rw [show n+1-k = n-k+1 from by omega]
    exact pointwise_bound n k (by omega)
  · apply le_of_eq; congr 1; ext k
    rw [fixedPtPMF_zero n (n+1+k) (by omega), zero_sub, abs_neg,
        abs_of_nonneg (poisson1PMF_nonneg _)]

private lemma pow_div_fact_tendsto :
    Tendsto (fun n => (2:ℝ)^(n+1) / ((n+1).factorial:ℝ)) atTop (nhds 0) :=
  ((summable_pow_div_factorial 2).tendsto_atTop_zero).comp (tendsto_add_atTop_nat 1)

/-- **Main Theorem**: Fixed-point distribution converges to Poisson(1) in total variation.
    ∑' k, |P(X_n = k) - e⁻¹/k!| → 0 as n → ∞. -/
theorem fixedPt_tv_tendsto : Tendsto tvSum atTop (nhds 0) := by
  apply squeeze_zero (fun n => tsum_nonneg (fun k => abs_nonneg _)) tvSum_le
  simpa using pow_div_fact_tendsto.add poisson1_tail_tendsto

/-- The k=0 special case: P(derangement) → 1/e recovers the classical result. -/
theorem derangement_prob_tendsto :
    Tendsto (fun n => (numDerangements n : ℝ) / (n.factorial : ℝ)) atTop (nhds (rexp (-1))) := by
  have htend : Tendsto (fun n => (1:ℝ) / ((n+1).factorial:ℝ)) atTop (nhds 0) := by
    have h := ((summable_pow_div_factorial 1).tendsto_atTop_zero).comp (tendsto_add_atTop_nat 1)
    simp only [one_pow] at h; exact h
  have hmain : Tendsto (fun n => (numDerangements n:ℝ)/(n.factorial:ℝ) - rexp (-1)) atTop (nhds 0) := by
    apply squeeze_zero_norm _ htend
    intro n; rw [Real.norm_eq_abs]; exact derangement_rate n
  simpa using hmain.add_const (rexp (-1))

end DerangementsOQ03OQ02

end
