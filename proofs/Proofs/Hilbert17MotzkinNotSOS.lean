/-
  Hilbert's 17th Problem — the Motzkin polynomial is NOT a sum of squares of
  polynomials (research entry hilbert-17-oq-03-oq-02).

  The Motzkin polynomial

      M(x,y) = x⁴y² + x²y⁴ - 3x²y² + 1

  is non-negative on all of ℝ² (its AM–GM certificate is in the parent entry
  `Hilbert17SumOfSquares.lean`), yet it is the canonical example of a
  non-negative polynomial that is *not* a sum of squares of polynomials. This is
  the negative half of Hilbert's 17th problem: such polynomials force the passage
  to sums of squares of *rational* functions (Artin's theorem).

  This file gives a fully elementary, 0-axiom proof of `motzkin_not_sos`,
  discharging the axiom `motzkin_not_sos_polynomial_aux` of the parent entry.

  ## Proof strategy (elementary, coefficient based)

  Suppose `M = ∑ᵢ qᵢ²`.

  1. **Degree bound** (`degree_bound`): each `qᵢ` has total degree ≤ 3. The
     degree-`2D` homogeneous component of a sum of squares is `∑ (top form)²`,
     which over ℝ vanishes only if every top form vanishes; since `M` has total
     degree 6, no `qᵢ` can have degree > 3.

  2. **Pure-axis coefficients vanish** (`pureX`, `pureY`): comparing the
     coefficients of `x⁶, x⁴, x²` (resp. `y⁶, y⁴, y²`) on both sides, and using
     that a sum of real squares is `0` only if each term is, forces the
     coefficients of `x, x², x³` (resp. `y, y², y³`) in every `qᵢ` to vanish.

  3. **The `x²y²` coefficient** (`coeff22_sq`): with the degree bound and the
     pure-axis vanishing, the only monomial pair of `qᵢ` contributing to `x²y²`
     in `qᵢ²` is `(xy)·(xy)`, so `[x²y²] qᵢ² = (cᵢ)²` where `cᵢ = [xy] qᵢ`.

  4. Summing: `-3 = [x²y²] M = ∑ᵢ (cᵢ)² ≥ 0`, a contradiction.

  All results depend only on `propext / Classical.choice / Quot.sound`.
-/
import Mathlib

open MvPolynomial

namespace Hilbert17MotzkinNotSOS

/-! ### Monomial bookkeeping in `Fin 2 →₀ ℕ` -/

/-- The exponent vector of `xᵃyᵇ`. -/
noncomputable def mon (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[simp] lemma mon_apply0 (a b : ℕ) : (mon a b) 0 = a := by simp [mon]
@[simp] lemma mon_apply1 (a b : ℕ) : (mon a b) 1 = b := by simp [mon]

lemma eq_mon (a : Fin 2 →₀ ℕ) : a = mon (a 0) (a 1) := by ext i; fin_cases i <;> simp

lemma mon_eq_iff (a b c d : ℕ) : (mon a b = mon c d) ↔ (a = c ∧ b = d) := by
  constructor
  · intro h
    exact ⟨by have := congrArg (fun f => f 0) h; simpa using this,
           by have := congrArg (fun f => f 1) h; simpa using this⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma degree_mon (a b : ℕ) : (mon a b).degree = a + b := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two, mon_apply0, mon_apply1]

lemma deg_eq (μ : Fin 2 →₀ ℕ) : μ.degree = μ 0 + μ 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-! ### The Motzkin polynomial -/

/-- `M(x,y) = x⁴y² + x²y⁴ - 3x²y² + 1`. -/
noncomputable def motzkin : MvPolynomial (Fin 2) ℝ :=
  X 0 ^ 4 * X 1 ^ 2 + X 0 ^ 2 * X 1 ^ 4 - 3 * X 0 ^ 2 * X 1 ^ 2 + 1

/-- A power product `xᵃyᵇ` as a monomial. -/
lemma Xpp (a b : ℕ) : (X 0 ^ a * X 1 ^ b : MvPolynomial (Fin 2) ℝ) = monomial (mon a b) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul]; rfl

lemma motzkin_eq : motzkin = monomial (mon 4 2) 1 + monomial (mon 2 4) 1
    - monomial (mon 2 2) 3 + monomial (mon 0 0) 1 := by
  have h3 : (3 * X 0 ^ 2 * X 1 ^ 2 : MvPolynomial (Fin 2) ℝ) = monomial (mon 2 2) 3 := by
    rw [mul_assoc, Xpp 2 2, ← map_ofNat (C : ℝ →+* _) 3, C_mul_monomial, mul_one]
  rw [motzkin, Xpp 4 2, Xpp 2 4, h3,
    show (1 : MvPolynomial (Fin 2) ℝ) = monomial (mon 0 0) 1 by
      rw [show mon 0 0 = 0 by simp [mon], monomial_zero', map_one]]

/-- The needed coefficients of `M`, read off from the monomial form. -/
private lemma coeff_motz (a b : ℕ) :
    coeff (mon a b) motzkin =
      (if (4 = a ∧ 2 = b) then 1 else 0) + (if (2 = a ∧ 4 = b) then 1 else 0)
        - (if (2 = a ∧ 2 = b) then 3 else 0) + (if (0 = a ∧ 0 = b) then 1 else 0) := by
  rw [motzkin_eq]
  simp only [coeff_add, coeff_sub, coeff_monomial, mon_eq_iff]

lemma coeff_motzkin_22 : coeff (mon 2 2) motzkin = -3 := by rw [coeff_motz]; norm_num
lemma coeff_motzkin_20 : coeff (mon 2 0) motzkin = 0 := by rw [coeff_motz]; norm_num
lemma coeff_motzkin_40 : coeff (mon 4 0) motzkin = 0 := by rw [coeff_motz]; norm_num
lemma coeff_motzkin_60 : coeff (mon 6 0) motzkin = 0 := by rw [coeff_motz]; norm_num
lemma coeff_motzkin_02 : coeff (mon 0 2) motzkin = 0 := by rw [coeff_motz]; norm_num
lemma coeff_motzkin_04 : coeff (mon 0 4) motzkin = 0 := by rw [coeff_motz]; norm_num
lemma coeff_motzkin_06 : coeff (mon 0 6) motzkin = 0 := by rw [coeff_motz]; norm_num

lemma totalDegree_motzkin : motzkin.totalDegree ≤ 6 := by
  rw [motzkin_eq]
  have hm : ∀ a b : ℕ, a + b ≤ 6 → (monomial (mon a b) (1 : ℝ)).totalDegree ≤ 6 := by
    intro a b hab
    calc (monomial (mon a b) (1 : ℝ)).totalDegree ≤ (mon a b).degree := totalDegree_monomial_le _ _
      _ = a + b := degree_mon a b
      _ ≤ 6 := hab
  have hm3 : (monomial (mon 2 2) (3 : ℝ)).totalDegree ≤ 6 := by
    calc (monomial (mon 2 2) (3 : ℝ)).totalDegree ≤ (mon 2 2).degree := totalDegree_monomial_le _ _
      _ = 4 := degree_mon 2 2
      _ ≤ 6 := by norm_num
  refine le_trans (totalDegree_add _ _) (max_le ?_ (hm 0 0 (by norm_num)))
  refine le_trans (totalDegree_sub _ _) (max_le ?_ hm3)
  exact le_trans (totalDegree_add _ _) (max_le (hm 4 2 (by norm_num)) (hm 2 4 (by norm_num)))

/-! ### Generic sum-of-squares facts -/

lemma totalDegree_eq_sup_degree (p : MvPolynomial (Fin 2) ℝ) :
    p.totalDegree = p.support.sup (fun s => s.degree) := by
  rw [MvPolynomial.totalDegree]; apply Finset.sup_congr rfl
  intro s _; exact (Finsupp.degree_apply s).symm

/-- A finite sum of squares of polynomials over ℝ vanishes only if each does. -/
lemma sum_sq_eq_zero {m : ℕ} (f : Fin m → MvPolynomial (Fin 2) ℝ)
    (h : ∑ i, (f i) ^ 2 = 0) (j : Fin m) : f j = 0 := by
  apply MvPolynomial.funext; intro x; rw [map_zero]
  have hx : ∑ i, (eval x (f i)) ^ 2 = 0 := by
    have := congrArg (eval x) h; simpa [map_sum, map_pow] using this
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ (eval x (f i)) ^ 2 := fun i _ => sq_nonneg _
  exact pow_eq_zero_iff (by norm_num)
    |>.1 ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 hx j (Finset.mem_univ j))

/-- A finite sum of squares of reals vanishes only if each does. -/
lemma sum_sq_real_eq_zero {m : ℕ} (c : Fin m → ℝ) (h : ∑ i, (c i) ^ 2 = 0) (j : Fin m) :
    c j = 0 := by
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ (c i) ^ 2 := fun i _ => sq_nonneg _
  exact pow_eq_zero_iff (by norm_num)
    |>.1 ((Finset.sum_eq_zero_iff_of_nonneg hnn).1 h j (Finset.mem_univ j))

/-- The top homogeneous form of a nonzero polynomial is nonzero. -/
lemma topForm_ne_zero (p : MvPolynomial (Fin 2) ℝ) (hp : p ≠ 0) :
    homogeneousComponent p.totalDegree p ≠ 0 := by
  have hne : p.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨μ, hμmem, hμsup⟩ := Finset.exists_mem_eq_sup p.support hne (fun s => s.degree)
  have hdeg : μ.degree = p.totalDegree := by rw [totalDegree_eq_sup_degree, ← hμsup]
  intro hzero
  have hcoeff : coeff μ (homogeneousComponent p.totalDegree p) = coeff μ p := by
    rw [coeff_homogeneousComponent, if_pos hdeg]
  rw [hzero, coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.1 hμmem) hcoeff.symm

lemma totalDegree_sub_top_lt (p : MvPolynomial (Fin 2) ℝ) (D : ℕ) (hD : 1 ≤ D)
    (hpD : p.totalDegree ≤ D) :
    (p - homogeneousComponent D p).totalDegree ≤ D - 1 := by
  rw [totalDegree_eq_sup_degree]; apply Finset.sup_le; intro μ hμ
  have hco : coeff μ (p - homogeneousComponent D p) ≠ 0 := MvPolynomial.mem_support_iff.1 hμ
  rw [coeff_sub, coeff_homogeneousComponent] at hco
  by_cases hd : μ.degree = D
  · rw [if_pos hd] at hco; simp at hco
  · rw [if_neg hd, sub_zero] at hco
    have : μ.degree ≤ p.totalDegree := by
      rw [totalDegree_eq_sup_degree]; exact Finset.le_sup (MvPolynomial.mem_support_iff.2 hco)
    omega

/-- The degree-`2D` component of a square equals the square of the degree-`D`
    component, whenever `D` bounds the total degree. -/
lemma topsq (p : MvPolynomial (Fin 2) ℝ) (D : ℕ) (hD : 1 ≤ D) (hpD : p.totalDegree ≤ D) :
    homogeneousComponent (2 * D) (p ^ 2) = (homogeneousComponent D p) ^ 2 := by
  set hd := homogeneousComponent D p with hhd
  set lo := p - hd with hlo
  have hdecomp : p = hd + lo := by rw [hlo]; ring
  have htd_lo : lo.totalDegree ≤ D - 1 := totalDegree_sub_top_lt p D hD hpD
  have htd_hd : hd.totalDegree ≤ D := (homogeneousComponent_isHomogeneous D p).totalDegree_le
  have hexp : p ^ 2 = hd ^ 2 + (hd * lo + hd * lo + lo ^ 2) := by rw [hdecomp]; ring
  rw [hexp, map_add]
  have h1 : homogeneousComponent (2 * D) (hd ^ 2) = hd ^ 2 := by
    have hh : (hd ^ 2) ∈ homogeneousSubmodule (Fin 2) ℝ (D + D) := by
      rw [sq]
      exact (homogeneousComponent_isHomogeneous D p).mul (homogeneousComponent_isHomogeneous D p)
    rw [homogeneousComponent_of_mem hh, if_pos (by omega)]
  have hmul : (hd * lo).totalDegree ≤ 2 * D - 1 := le_trans (totalDegree_mul _ _) (by omega)
  have h2 : homogeneousComponent (2 * D) (hd * lo + hd * lo + lo ^ 2) = 0 := by
    apply homogeneousComponent_eq_zero
    have hb2 : (lo ^ 2).totalDegree ≤ 2 * D - 1 := le_trans (totalDegree_pow _ _) (by omega)
    have : (hd * lo + hd * lo + lo ^ 2).totalDegree ≤ 2 * D - 1 := by
      refine le_trans (totalDegree_add _ _) ?_
      rw [max_le_iff]
      refine ⟨le_trans (totalDegree_add _ _) ?_, hb2⟩
      rw [max_le_iff]; exact ⟨hmul, hmul⟩
    omega
  rw [h1, h2, add_zero]

/-! ### Step 1: degree bound -/

/-- If `∑ qᵢ² = M` with `totalDegree M ≤ 6`, then every `qᵢ` has total degree ≤ 3. -/
lemma degree_bound {m : ℕ} (q : Fin m → MvPolynomial (Fin 2) ℝ)
    (h : ∑ i, (q i) ^ 2 = motzkin) (j : Fin m) : (q j).totalDegree ≤ 3 := by
  by_contra hcon
  push_neg at hcon
  set D := Finset.univ.sup (fun i => (q i).totalDegree) with hDdef
  have hjD : (q j).totalDegree ≤ D :=
    Finset.le_sup (f := fun i => (q i).totalDegree) (Finset.mem_univ j)
  have hD1 : 1 ≤ D := by omega
  have hzero : homogeneousComponent (2 * D) motzkin = 0 := by
    apply homogeneousComponent_eq_zero
    exact lt_of_le_of_lt totalDegree_motzkin (by omega)
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

/-! ### Step 2: pure-axis coefficient extractions -/

/-- Under the degree bound, `[x^{2n}] qᵢ²` collapses to `([xⁿ] qᵢ)²`. -/
lemma pureX_extract (q : MvPolynomial (Fin 2) ℝ)
    (hdeg : ∀ μ : Fin 2 →₀ ℕ, 4 ≤ (μ 0 + μ 1) → coeff μ q = 0)
    (n : ℕ) (hkill : ∀ k, n < k → k ≤ 3 → coeff (mon k 0) q = 0) :
    coeff (mon (2 * n) 0) (q * q) = (coeff (mon n 0) q) ^ 2 := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem ((mon n 0), (mon n 0))]
  · ring
  · rw [Finset.mem_antidiagonal]; ext i; fin_cases i <;> simp [mon] <;> omega
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    show coeff a q * coeff b q = 0
    have h0 : a 0 + b 0 = 2 * n := by have := congrArg (fun f => f 0) hab; simpa [mon] using this
    have h1 : a 1 + b 1 = 0 := by have := congrArg (fun f => f 1) hab; simpa [mon] using this
    have ha1 : a 1 = 0 := by omega
    have hb1 : b 1 = 0 := by omega
    have hanen : a 0 ≠ n := by
      intro he; apply hne
      have ea : a = mon n 0 := by rw [eq_mon a, he, ha1]
      have eb : b = mon n 0 := by rw [eq_mon b, hb1, show b 0 = n by omega]
      rw [ea, eb]
    rw [eq_mon a, ha1, eq_mon b, hb1, mul_eq_zero]
    rcases Nat.lt_or_ge (a 0) n with hlt | hge
    · right
      rcases Nat.lt_or_ge (b 0) 4 with hb4 | hb4
      · exact hkill _ (by omega) (by omega)
      · exact hdeg _ (by simp; omega)
    · left
      rcases Nat.lt_or_ge (a 0) 4 with ha4 | ha4
      · exact hkill _ (by omega) (by omega)
      · exact hdeg _ (by simp; omega)

/-- Under the degree bound, `[y^{2n}] qᵢ²` collapses to `([yⁿ] qᵢ)²`. -/
lemma pureY_extract (q : MvPolynomial (Fin 2) ℝ)
    (hdeg : ∀ μ : Fin 2 →₀ ℕ, 4 ≤ (μ 0 + μ 1) → coeff μ q = 0)
    (n : ℕ) (hkill : ∀ k, n < k → k ≤ 3 → coeff (mon 0 k) q = 0) :
    coeff (mon 0 (2 * n)) (q * q) = (coeff (mon 0 n) q) ^ 2 := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem ((mon 0 n), (mon 0 n))]
  · ring
  · rw [Finset.mem_antidiagonal]; ext i; fin_cases i <;> simp [mon] <;> omega
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    show coeff a q * coeff b q = 0
    have h0 : a 1 + b 1 = 2 * n := by have := congrArg (fun f => f 1) hab; simpa [mon] using this
    have h1 : a 0 + b 0 = 0 := by have := congrArg (fun f => f 0) hab; simpa [mon] using this
    have ha0 : a 0 = 0 := by omega
    have hb0 : b 0 = 0 := by omega
    have hanen : a 1 ≠ n := by
      intro he; apply hne
      have ea : a = mon 0 n := by rw [eq_mon a, he, ha0]
      have eb : b = mon 0 n := by rw [eq_mon b, hb0, show b 1 = n by omega]
      rw [ea, eb]
    rw [eq_mon a, ha0, eq_mon b, hb0, mul_eq_zero]
    rcases Nat.lt_or_ge (a 1) n with hlt | hge
    · right
      rcases Nat.lt_or_ge (b 1) 4 with hb4 | hb4
      · exact hkill _ (by omega) (by omega)
      · exact hdeg _ (by simp; omega)
    · left
      rcases Nat.lt_or_ge (a 1) 4 with ha4 | ha4
      · exact hkill _ (by omega) (by omega)
      · exact hdeg _ (by simp; omega)

/-! ### Step 3: the `x²y²` coefficient -/

/-- Under the degree bound and pure-axis vanishing, `[x²y²] qᵢ² = ([xy] qᵢ)²`. -/
lemma coeff22_sq (q : MvPolynomial (Fin 2) ℝ)
    (hpx : ∀ k, 1 ≤ k → coeff (mon k 0) q = 0)
    (hpy : ∀ k, 1 ≤ k → coeff (mon 0 k) q = 0)
    (hdeg : ∀ μ : Fin 2 →₀ ℕ, 4 ≤ (μ 0 + μ 1) → coeff μ q = 0) :
    coeff (mon 2 2) (q * q) = (coeff (mon 1 1) q) ^ 2 := by
  rw [coeff_mul, Finset.sum_eq_single_of_mem ((mon 1 1), (mon 1 1))]
  · ring
  · rw [Finset.mem_antidiagonal]; ext i; fin_cases i <;> simp [mon]
  · rintro ⟨a, b⟩ hab hne
    rw [Finset.mem_antidiagonal] at hab
    show coeff a q * coeff b q = 0
    have h0 : a 0 + b 0 = 2 := by have := congrArg (fun f => f 0) hab; simpa [mon] using this
    have h1 : a 1 + b 1 = 2 := by have := congrArg (fun f => f 1) hab; simpa [mon] using this
    have hnea : ¬ (a 0 = 1 ∧ a 1 = 1) := by
      rintro ⟨e0, e1⟩; apply hne
      have ha : a = mon 1 1 := by rw [eq_mon a, e0, e1]
      have hb : b = mon 1 1 := by rw [eq_mon b]; congr 1 <;> omega
      rw [ha, hb]
    rw [eq_mon a, eq_mon b, mul_eq_zero]
    rcases Nat.lt_or_ge (a 0 + a 1) 4 with hlt | hge
    · rcases Nat.eq_zero_or_pos (a 1) with ha1 | ha1
      · rcases Nat.eq_zero_or_pos (a 0) with ha0 | ha0
        · right; apply hdeg; simp; omega
        · left; rw [ha1]; apply hpx; omega
      · rcases Nat.eq_zero_or_pos (a 0) with ha0 | ha0
        · left; rw [ha0]; apply hpy; omega
        · rcases Nat.lt_or_ge (a 0) 2 with hx | hx
          · right; rw [show b 1 = 0 by omega]; apply hpx; omega
          · right; rw [show b 0 = 0 by omega]; apply hpy; omega
    · left; apply hdeg; simp; omega

/-! ### Assembling the non-existence proof -/

/-- A multivariate polynomial is a sum of squares of polynomials. (Matches the
    definition `IsSumOfSquaresMvPolynomial` of the parent entry.) -/
def IsSOS (p : MvPolynomial (Fin 2) ℝ) : Prop :=
  ∃ (m : ℕ) (q : Fin m → MvPolynomial (Fin 2) ℝ), p = ∑ i, q i ^ 2

/-- **The Motzkin polynomial is not a sum of squares of polynomials.** -/
theorem motzkin_not_sos : ¬ IsSOS motzkin := by
  rintro ⟨m, q, hq⟩
  -- abbreviate the sum-of-squares hypothesis in the convenient direction
  have hsum : ∑ i, (q i) ^ 2 = motzkin := hq.symm
  -- Step 1: degree bound and its coefficient form
  have hdeg : ∀ j, ∀ μ : Fin 2 →₀ ℕ, 4 ≤ (μ 0 + μ 1) → coeff μ (q j) = 0 := by
    intro j μ hμ
    apply coeff_eq_zero_of_totalDegree_lt
    have hs : ∑ i ∈ μ.support, μ i = μ 0 + μ 1 := by
      rw [← Finsupp.degree_apply]; exact deg_eq μ
    rw [hs]; exact lt_of_le_of_lt (degree_bound q hsum j) (by omega)
  -- Step 2: pure-axis vanishing for each qⱼ
  have hpx : ∀ j, ∀ k, 1 ≤ k → coeff (mon k 0) (q j) = 0 := by
    intro j
    -- c₃₀ = 0
    have e60 : ∑ i, (coeff (mon 3 0) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 6 0) (q i ^ 2)) = coeff (mon 6 0) motzkin := by
        rw [← coeff_sum, hsum]
      rw [coeff_motzkin_60] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureX_extract (q i) (hdeg i) 3 (by intro k hk hk3; exact absurd hk3 (by omega))).symm
    have c30 : ∀ i, coeff (mon 3 0) (q i) = 0 := sum_sq_real_eq_zero _ e60
    -- c₂₀ = 0
    have e40 : ∑ i, (coeff (mon 2 0) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 4 0) (q i ^ 2)) = coeff (mon 4 0) motzkin := by
        rw [← coeff_sum, hsum]
      rw [coeff_motzkin_40] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureX_extract (q i) (hdeg i) 2 (by intro k hk hk3; interval_cases k; exact c30 i)).symm
    have c20 : ∀ i, coeff (mon 2 0) (q i) = 0 := sum_sq_real_eq_zero _ e40
    -- c₁₀ = 0
    have e20 : ∑ i, (coeff (mon 1 0) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 2 0) (q i ^ 2)) = coeff (mon 2 0) motzkin := by
        rw [← coeff_sum, hsum]
      rw [coeff_motzkin_20] at this
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
      have : (∑ i, coeff (mon 0 6) (q i ^ 2)) = coeff (mon 0 6) motzkin := by
        rw [← coeff_sum, hsum]
      rw [coeff_motzkin_06] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureY_extract (q i) (hdeg i) 3 (by intro k hk hk3; exact absurd hk3 (by omega))).symm
    have c03 : ∀ i, coeff (mon 0 3) (q i) = 0 := sum_sq_real_eq_zero _ e06
    have e04 : ∑ i, (coeff (mon 0 2) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 0 4) (q i ^ 2)) = coeff (mon 0 4) motzkin := by
        rw [← coeff_sum, hsum]
      rw [coeff_motzkin_04] at this
      rw [← this]; apply Finset.sum_congr rfl; intro i _
      rw [pow_two (q i)]
      exact (pureY_extract (q i) (hdeg i) 2 (by intro k hk hk3; interval_cases k; exact c03 i)).symm
    have c02 : ∀ i, coeff (mon 0 2) (q i) = 0 := sum_sq_real_eq_zero _ e04
    have e02 : ∑ i, (coeff (mon 0 1) (q i)) ^ 2 = 0 := by
      have : (∑ i, coeff (mon 0 2) (q i ^ 2)) = coeff (mon 0 2) motzkin := by
        rw [← coeff_sum, hsum]
      rw [coeff_motzkin_02] at this
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
  -- Step 3: the x²y² coefficient is a sum of squares
  have hfinal : coeff (mon 2 2) motzkin = ∑ i, (coeff (mon 1 1) (q i)) ^ 2 := by
    rw [← hsum, coeff_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [pow_two (q i)]
    exact coeff22_sq (q i) (hpx i) (hpy i) (hdeg i)
  rw [coeff_motzkin_22] at hfinal
  have hnn : (0 : ℝ) ≤ ∑ i, (coeff (mon 1 1) (q i)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [← hfinal] at hnn
  norm_num at hnn

end Hilbert17MotzkinNotSOS

-- Axiom audit: should list only propext, Classical.choice, Quot.sound.
#print axioms Hilbert17MotzkinNotSOS.motzkin_not_sos
