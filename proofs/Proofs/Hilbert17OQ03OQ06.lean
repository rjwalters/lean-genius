/-
  Hilbert's 17th Problem — the sharp SOS threshold of the Motzkin family
  (research entry hilbert-17-oq-03-oq-06).

  For the one-parameter Motzkin family

      Mₐ(x,y) = x⁴y² + x²y⁴ + 1 − c·x²y²

  the sibling entry `hilbert-17-oq-03-oq-05` proves the sharp *PSD* threshold:
  `Mₐ` is non-negative on ℝ² ⟺ c ≤ 3 (the Motzkin polynomial sits at c = 3).

  This entry isolates the complementary sharp *SOS* threshold. By a Newton-polytope
  / coefficient obstruction (the engine of `hilbert-17-oq-03-oq-02`), `Mₐ` is a sum
  of squares of polynomials ⟺ c ≤ 0:

  - (⟸)  for c ≤ 0 the deficit term −c·x²y² is non-negative, and
            `Mₐ = (x²y)² + (xy²)² + (√(−c)·xy)² + 1²`
         is a literal sum of squares.
  - (⟹)  for c > 0 the `x²y²` coefficient of `Mₐ` is the negative number `−c`,
         but in any representation `Mₐ = ∑ qᵢ²` the degree bound and the vanishing
         of every pure-power coefficient force `[x²y²]Mₐ = ∑ ([xy]qᵢ)² ≥ 0`,
         a contradiction.

  Combining the two thresholds localizes the PSD ⊋ SOS gap along this family to
  the half-open interval `(0, 3]`: the members that are PSD but *not* SOS are
  exactly those with `0 < c ≤ 3`. So the famous Motzkin point c = 3 is not an
  isolated witness — the whole interval `(0,3]` separates the two cones, while the
  SOS cone closes off already at c = 0.

  The non-SOS direction is packaged as a reusable abstract obstruction
  `not_sos_of_neg_diag`: any bivariate polynomial of total degree ≤ 6 whose six
  pure-power coefficients `x⁶,x⁴,x²,y⁶,y⁴,y²` vanish and whose `x²y²` coefficient
  is negative cannot be a sum of squares.

  All results depend only on `propext / Classical.choice / Quot.sound`.
-/
import Mathlib
import Proofs.Hilbert17MotzkinNotSOS
import Proofs.Hilbert17OQ03OQ05

open MvPolynomial
open Hilbert17MotzkinNotSOS (mon eq_mon mon_eq_iff degree_mon deg_eq Xpp IsSOS
  topsq sum_sq_eq_zero sum_sq_real_eq_zero topForm_ne_zero
  pureX_extract pureY_extract coeff22_sq)
open Hilbert17OQ03OQ05 (motzkinPoly IsPSDMv motzkinPoly_psd_iff)

namespace Hilbert17OQ03OQ06

/-! ### A reusable non-SOS obstruction

`degree_bound'` is the parametric version of `Hilbert17MotzkinNotSOS.degree_bound`
(which is hard-coded to the Motzkin polynomial): for any target `P` of total
degree ≤ 6, every summand of a representation `∑ qᵢ² = P` has total degree ≤ 3. -/

/-- If `∑ qᵢ² = P` with `totalDegree P ≤ 6`, then every `qᵢ` has total degree ≤ 3. -/
lemma degree_bound' {m : ℕ} (P : MvPolynomial (Fin 2) ℝ) (hPdeg : P.totalDegree ≤ 6)
    (q : Fin m → MvPolynomial (Fin 2) ℝ)
    (h : ∑ i, (q i) ^ 2 = P) (j : Fin m) : (q j).totalDegree ≤ 3 := by
  by_contra hcon
  push_neg at hcon
  set D := Finset.univ.sup (fun i => (q i).totalDegree) with hDdef
  have hjD : (q j).totalDegree ≤ D :=
    Finset.le_sup (f := fun i => (q i).totalDegree) (Finset.mem_univ j)
  have hD1 : 1 ≤ D := by omega
  have hzero : homogeneousComponent (2 * D) P = 0 := by
    apply homogeneousComponent_eq_zero
    exact lt_of_le_of_lt hPdeg (by omega)
  rw [← h, map_sum] at hzero
  have hterm : ∀ i, homogeneousComponent (2 * D) ((q i) ^ 2) = (homogeneousComponent D (q i)) ^ 2 :=
    fun i => topsq (q i) D hD1 (Finset.le_sup (f := fun i => (q i).totalDegree) (Finset.mem_univ i))
  rw [Finset.sum_congr rfl (fun i _ => hterm i)] at hzero
  have htop0 := sum_sq_eq_zero (fun i => homogeneousComponent D (q i)) hzero
  obtain ⟨i₀, _, hi₀⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ) ⟨j, Finset.mem_univ j⟩ (fun i => (q i).totalDegree)
  have hi₀deg : (q i₀).totalDegree = D := by rw [hDdef, ← hi₀]
  have hqi0 : q i₀ ≠ 0 := by intro h0; rw [h0] at hi₀deg; simp at hi₀deg; omega
  have hne0 : homogeneousComponent D (q i₀) ≠ 0 := by
    rw [← hi₀deg]; exact topForm_ne_zero _ hqi0
  exact hne0 (htop0 i₀)

/-- **Abstract Newton-polytope obstruction to being a sum of squares.**
    A bivariate real polynomial of total degree ≤ 6 whose six pure-power
    coefficients (`x⁶, x⁴, x²` and `y⁶, y⁴, y²`) vanish and whose `x²y²`
    coefficient is negative is not a sum of squares of polynomials. -/
theorem not_sos_of_neg_diag (P : MvPolynomial (Fin 2) ℝ)
    (hPdeg : P.totalDegree ≤ 6)
    (h60 : coeff (mon 6 0) P = 0) (h40 : coeff (mon 4 0) P = 0) (h20 : coeff (mon 2 0) P = 0)
    (h06 : coeff (mon 0 6) P = 0) (h04 : coeff (mon 0 4) P = 0) (h02 : coeff (mon 0 2) P = 0)
    (h22 : coeff (mon 2 2) P < 0) : ¬ IsSOS P := by
  rintro ⟨m, q, hq⟩
  have hsum : ∑ i, (q i) ^ 2 = P := hq.symm
  -- Step 1: degree bound, in coefficient form
  have hdeg : ∀ j, ∀ μ : Fin 2 →₀ ℕ, 4 ≤ (μ 0 + μ 1) → coeff μ (q j) = 0 := by
    intro j μ hμ
    apply coeff_eq_zero_of_totalDegree_lt
    have hs : ∑ i ∈ μ.support, μ i = μ 0 + μ 1 := by
      rw [← Finsupp.degree_apply]; exact deg_eq μ
    rw [hs]; exact lt_of_le_of_lt (degree_bound' P hPdeg q hsum j) (by omega)
  -- Step 2: pure-axis vanishing for each qⱼ
  have hpx : ∀ j, ∀ k, 1 ≤ k → coeff (mon k 0) (q j) = 0 := by
    intro j
    have e60 : ∑ i, (coeff (mon 3 0) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 6 0) (q i ^ 2)) = coeff (mon 6 0) P := by
        rw [← coeff_sum, hsum]
      rw [h60] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureX_extract (q i) (hdeg i) 3 (by intro k hk hk3; exact absurd hk3 (by omega))).symm
    have c30 : ∀ i, coeff (mon 3 0) (q i) = 0 := sum_sq_real_eq_zero _ e60
    have e40 : ∑ i, (coeff (mon 2 0) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 4 0) (q i ^ 2)) = coeff (mon 4 0) P := by
        rw [← coeff_sum, hsum]
      rw [h40] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureX_extract (q i) (hdeg i) 2 (by intro k hk hk3; interval_cases k; exact c30 i)).symm
    have c20 : ∀ i, coeff (mon 2 0) (q i) = 0 := sum_sq_real_eq_zero _ e40
    have e20 : ∑ i, (coeff (mon 1 0) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 2 0) (q i ^ 2)) = coeff (mon 2 0) P := by
        rw [← coeff_sum, hsum]
      rw [h20] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureX_extract (q i) (hdeg i) 1
        (by intro k hk hk3; interval_cases k; exacts [c20 i, c30 i])).symm
    have c10 : ∀ i, coeff (mon 1 0) (q i) = 0 := sum_sq_real_eq_zero _ e20
    intro k hk
    rcases Nat.lt_or_ge k 4 with h4 | h4
    · interval_cases k
      · exact c10 j
      · exact c20 j
      · exact c30 j
    · exact hdeg j _ (by simp; omega)
  have hpy : ∀ j, ∀ k, 1 ≤ k → coeff (mon 0 k) (q j) = 0 := by
    intro j
    have e06 : ∑ i, (coeff (mon 0 3) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 0 6) (q i ^ 2)) = coeff (mon 0 6) P := by
        rw [← coeff_sum, hsum]
      rw [h06] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureY_extract (q i) (hdeg i) 3 (by intro k hk hk3; exact absurd hk3 (by omega))).symm
    have c03 : ∀ i, coeff (mon 0 3) (q i) = 0 := sum_sq_real_eq_zero _ e06
    have e04 : ∑ i, (coeff (mon 0 2) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 0 4) (q i ^ 2)) = coeff (mon 0 4) P := by
        rw [← coeff_sum, hsum]
      rw [h04] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureY_extract (q i) (hdeg i) 2 (by intro k hk hk3; interval_cases k; exact c03 i)).symm
    have c02 : ∀ i, coeff (mon 0 2) (q i) = 0 := sum_sq_real_eq_zero _ e04
    have e02 : ∑ i, (coeff (mon 0 1) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 0 2) (q i ^ 2)) = coeff (mon 0 2) P := by
        rw [← coeff_sum, hsum]
      rw [h02] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureY_extract (q i) (hdeg i) 1
        (by intro k hk hk3; interval_cases k; exacts [c02 i, c03 i])).symm
    have c01 : ∀ i, coeff (mon 0 1) (q i) = 0 := sum_sq_real_eq_zero _ e02
    intro k hk
    rcases Nat.lt_or_ge k 4 with h4 | h4
    · interval_cases k
      · exact c01 j
      · exact c02 j
      · exact c03 j
    · exact hdeg j _ (by simp; omega)
  -- Step 3: the x²y² coefficient is a sum of squares, contradicting h22
  have hfinal : coeff (mon 2 2) P = ∑ i, (coeff (mon 1 1) (q i)) ^ 2 := by
    rw [← hsum, coeff_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [pow_two (q i)]
    exact coeff22_sq (q i) (hpx i) (hpy i) (hdeg i)
  have hnn : (0 : ℝ) ≤ ∑ i, (coeff (mon 1 1) (q i)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [← hfinal] at hnn
  linarith

/-! ### Coefficients and degree of the Motzkin family -/

/-- The Motzkin family in monomial form. -/
lemma motzkinPoly_eq (c : ℝ) : motzkinPoly c =
    monomial (mon 4 2) 1 + monomial (mon 2 4) 1 + monomial (mon 0 0) 1
      - monomial (mon 2 2) c := by
  have hc2 : (C c * (X 0 ^ 2 * X 1 ^ 2) : MvPolynomial (Fin 2) ℝ) = monomial (mon 2 2) c := by
    rw [Xpp 2 2, C_mul_monomial, mul_one]
  rw [motzkinPoly, Xpp 4 2, Xpp 2 4, hc2,
    show (1 : MvPolynomial (Fin 2) ℝ) = monomial (mon 0 0) 1 by
      rw [show mon 0 0 = 0 by simp [mon], monomial_zero', map_one]]

private lemma coeff_mP (c : ℝ) (a b : ℕ) :
    coeff (mon a b) (motzkinPoly c) =
      (if (4 = a ∧ 2 = b) then 1 else 0) + (if (2 = a ∧ 4 = b) then 1 else 0)
        + (if (0 = a ∧ 0 = b) then 1 else 0) - (if (2 = a ∧ 2 = b) then c else 0) := by
  rw [motzkinPoly_eq]
  simp only [coeff_add, coeff_sub, coeff_monomial, mon_eq_iff]

lemma coeff_mP_22 (c : ℝ) : coeff (mon 2 2) (motzkinPoly c) = -c := by rw [coeff_mP]; norm_num
lemma coeff_mP_20 (c : ℝ) : coeff (mon 2 0) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num
lemma coeff_mP_40 (c : ℝ) : coeff (mon 4 0) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num
lemma coeff_mP_60 (c : ℝ) : coeff (mon 6 0) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num
lemma coeff_mP_02 (c : ℝ) : coeff (mon 0 2) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num
lemma coeff_mP_04 (c : ℝ) : coeff (mon 0 4) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num
lemma coeff_mP_06 (c : ℝ) : coeff (mon 0 6) (motzkinPoly c) = 0 := by rw [coeff_mP]; norm_num

lemma totalDegree_motzkinPoly (c : ℝ) : (motzkinPoly c).totalDegree ≤ 6 := by
  rw [motzkinPoly_eq]
  have hm : ∀ a b : ℕ, ∀ r : ℝ, a + b ≤ 6 → (monomial (mon a b) r).totalDegree ≤ 6 := by
    intro a b r hab
    calc (monomial (mon a b) r).totalDegree ≤ (mon a b).degree := totalDegree_monomial_le _ _
      _ = a + b := degree_mon a b
      _ ≤ 6 := hab
  refine le_trans (totalDegree_sub _ _) (max_le ?_ (hm 2 2 c (by norm_num)))
  refine le_trans (totalDegree_add _ _) (max_le ?_ (hm 0 0 1 (by norm_num)))
  exact le_trans (totalDegree_add _ _) (max_le (hm 4 2 1 (by norm_num)) (hm 2 4 1 (by norm_num)))

/-! ### The sharp SOS threshold -/

/-- **Non-SOS direction.** For `c > 0` the Motzkin family member `Mₐ` is not a
    sum of squares of polynomials (its `x²y²` coefficient `−c` is negative). -/
theorem motzkinPoly_not_sos {c : ℝ} (hc : 0 < c) : ¬ IsSOS (motzkinPoly c) :=
  not_sos_of_neg_diag (motzkinPoly c) (totalDegree_motzkinPoly c)
    (coeff_mP_60 c) (coeff_mP_40 c) (coeff_mP_20 c)
    (coeff_mP_06 c) (coeff_mP_04 c) (coeff_mP_02 c)
    (by rw [coeff_mP_22 c]; linarith)

/-- **SOS direction.** For `c ≤ 0` the Motzkin family member `Mₐ` is a sum of
    squares: `Mₐ = (x²y)² + (xy²)² + (√(−c)·xy)² + 1²`. -/
theorem motzkinPoly_sos {c : ℝ} (hc : c ≤ 0) : IsSOS (motzkinPoly c) := by
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s ^ 2 = -c := ⟨Real.sqrt (-c), Real.sq_sqrt (by linarith)⟩
  have hcs : (C s : MvPolynomial (Fin 2) ℝ) ^ 2 = - C c := by
    rw [← map_pow, hs, map_neg]
  have heq : motzkinPoly c = (X 0 ^ 2 * X 1) ^ 2 + (X 0 * X 1 ^ 2) ^ 2
      + (C s * (X 0 * X 1)) ^ 2 + (1 : MvPolynomial (Fin 2) ℝ) ^ 2 := by
    unfold motzkinPoly
    linear_combination (-(X 0 * X 1) ^ 2) * hcs
  refine ⟨4, ![X 0 ^ 2 * X 1, X 0 * X 1 ^ 2, C s * (X 0 * X 1), 1], ?_⟩
  rw [Fin.sum_univ_four]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  exact heq

/-- **Sharp SOS threshold of the Motzkin family.**  `Mₐ` is a sum of squares of
    polynomials if and only if `c ≤ 0`. -/
theorem motzkinPoly_sos_iff (c : ℝ) : IsSOS (motzkinPoly c) ↔ c ≤ 0 := by
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    exact motzkinPoly_not_sos hc h
  · exact motzkinPoly_sos

/-! ### Localizing the PSD ⊋ SOS gap -/

/-- **The PSD/SOS gap along the Motzkin family is exactly the interval `(0,3]`.**
    A member `Mₐ` is positive-semidefinite but *not* a sum of squares iff
    `0 < c ≤ 3`. Combined with the sharp PSD threshold (`c ≤ 3`, sibling oq-05)
    and the sharp SOS threshold (`c ≤ 0`, above), this shows the Motzkin point
    `c = 3` is not an isolated witness: the entire half-open interval separates
    the PSD and SOS cones. -/
theorem motzkinPoly_psd_not_sos_iff (c : ℝ) :
    (IsPSDMv (motzkinPoly c) ∧ ¬ IsSOS (motzkinPoly c)) ↔ (0 < c ∧ c ≤ 3) := by
  rw [motzkinPoly_psd_iff, motzkinPoly_sos_iff, not_le]
  tauto

/-- The classical Motzkin polynomial (`c = 3`) lies in the gap: PSD but not SOS. -/
theorem motzkin_three_psd_not_sos :
    IsPSDMv (motzkinPoly 3) ∧ ¬ IsSOS (motzkinPoly 3) :=
  (motzkinPoly_psd_not_sos_iff 3).2 ⟨by norm_num, le_refl 3⟩

end Hilbert17OQ03OQ06

-- Axiom audit: should list only propext, Classical.choice, Quot.sound.
-- #print axioms Hilbert17OQ03OQ06.motzkinPoly_sos_iff
-- #print axioms Hilbert17OQ03OQ06.motzkinPoly_psd_not_sos_iff
