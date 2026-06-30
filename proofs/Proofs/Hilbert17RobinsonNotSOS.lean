/-
  Hilbert's 17th Problem — Robinson's polynomial is NOT a sum of squares of
  polynomials (research entry hilbert-17-oq-03-oq-03).

  Robinson's polynomial (1973)

      R(x,y,z) = x⁶ + y⁶ + z⁶
                 - x⁴y² - y⁴z² - z⁴x² - x²y⁴ - y²z⁴ - z²x⁴
                 + 3x²y²z²

  is non-negative on all of ℝ³ (its Schur-inequality certificate is in the
  parent entry `Hilbert17SumOfSquares.lean`), yet — like the Motzkin polynomial
  — it is *not* a sum of squares of polynomials. This is the second classical
  counterexample feeding the negative half of Hilbert's 17th problem.

  This file gives a fully elementary, 0-axiom proof of `robinson_not_sos`,
  discharging the axiom `robinson_not_sos_aux` of the parent entry.

  ## Proof strategy (elementary, zero-set / linear algebra)

  Suppose `R = ∑ᵢ qᵢ²`.

  1. **Degree bound** (`degree_bound`): each `qᵢ` has total degree ≤ 3 — the
     degree-`2D` homogeneous component of a sum of squares is `∑ (top form)²`,
     which over ℝ vanishes only if every top form does, and `R` has degree 6.

  2. **Homogeneous reduction**: take the degree-6 homogeneous component of both
     sides. Because `R` is homogeneous of degree 6, `R = ∑ᵢ (qᵢ⁽³⁾)²` where
     `qᵢ⁽³⁾ = homogeneousComponent 3 qᵢ` is a *homogeneous cubic form*
     (`topsq`, with `D = 3`, `2·3 = 6`). No bottom-degree cascade is needed.

  3. **Vanishing on the zero set**: `R` vanishes at its ten real projective
     zeros `(1,±1,0), (1,0,±1), (0,1,±1), (1,±1,±1)`. Since a sum of real
     squares is `0` only if each term is, every cubic form `qᵢ⁽³⁾` vanishes at
     all ten points.

  4. **The decisive linear algebra** (`cubic_zero`): the 10×10 matrix of the
     ten cubic monomials evaluated at the ten points has determinant `128 ≠ 0`,
     so the only homogeneous cubic vanishing at all ten points is `0`. Hence
     every `qᵢ⁽³⁾ = 0`, forcing `R = 0` — contradicting `R(1,0,0) = 1`.

  All results depend only on `propext / Classical.choice / Quot.sound`.
-/
import Mathlib

open MvPolynomial

namespace Hilbert17RobinsonNotSOS

/-! ### Monomial bookkeeping in `Fin 3 →₀ ℕ` -/

/-- The exponent vector of `xᵃyᵇzᶜ`. -/
noncomputable def mon3 (a b c : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c

@[simp] lemma mon3_apply0 (a b c : ℕ) : (mon3 a b c) 0 = a := by simp [mon3]
@[simp] lemma mon3_apply1 (a b c : ℕ) : (mon3 a b c) 1 = b := by simp [mon3]
@[simp] lemma mon3_apply2 (a b c : ℕ) : (mon3 a b c) 2 = c := by simp [mon3]

lemma eq_mon3 (a : Fin 3 →₀ ℕ) : a = mon3 (a 0) (a 1) (a 2) := by
  ext i; fin_cases i <;> simp

lemma mon3_eq_iff (a b c d e f : ℕ) :
    (mon3 a b c = mon3 d e f) ↔ (a = d ∧ b = e ∧ c = f) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := congrArg (fun g => g 0) h; simpa using this
    · have := congrArg (fun g => g 1) h; simpa using this
    · have := congrArg (fun g => g 2) h; simpa using this
  · rintro ⟨rfl, rfl, rfl⟩; rfl

lemma deg_eq3 (μ : Fin 3 →₀ ℕ) : μ.degree = μ 0 + μ 1 + μ 2 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_three]

lemma degree_mon3 (a b c : ℕ) : (mon3 a b c).degree = a + b + c := by
  rw [deg_eq3, mon3_apply0, mon3_apply1, mon3_apply2]

/-- A power product `xᵃyᵇzᶜ` as a monomial. -/
lemma Xpp3 (a b c : ℕ) :
    (X 0 ^ a * X 1 ^ b * X 2 ^ c : MvPolynomial (Fin 3) ℝ) = monomial (mon3 a b c) 1 := by
  rw [X_pow_eq_monomial, X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, monomial_mul,
    one_mul, one_mul]; rfl

/-- Every homogeneous-degree-3 exponent vector in three variables is one of the
    ten cubic monomials. -/
lemma deg3_cases (μ : Fin 3 →₀ ℕ) (h : μ 0 + μ 1 + μ 2 = 3) :
    μ = mon3 3 0 0 ∨ μ = mon3 0 3 0 ∨ μ = mon3 0 0 3 ∨
    μ = mon3 2 1 0 ∨ μ = mon3 2 0 1 ∨ μ = mon3 1 2 0 ∨
    μ = mon3 0 2 1 ∨ μ = mon3 1 0 2 ∨ μ = mon3 0 1 2 ∨ μ = mon3 1 1 1 := by
  obtain ⟨a, b, c, rfl⟩ : ∃ a b c, μ = mon3 a b c := ⟨μ 0, μ 1, μ 2, eq_mon3 μ⟩
  simp only [mon3_apply0, mon3_apply1, mon3_apply2] at h
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  have hc : c ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;>
    first | (exfalso; omega) | simp

/-! ### The Robinson polynomial -/

/-- `R(x,y,z) = x⁶+y⁶+z⁶ - x⁴y² - y⁴z² - z⁴x² - x²y⁴ - y²z⁴ - z²x⁴ + 3x²y²z²`. -/
noncomputable def robinson : MvPolynomial (Fin 3) ℝ :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6
  - X 0 ^ 4 * X 1 ^ 2 - X 1 ^ 4 * X 2 ^ 2 - X 2 ^ 4 * X 0 ^ 2
  - X 0 ^ 2 * X 1 ^ 4 - X 1 ^ 2 * X 2 ^ 4 - X 2 ^ 2 * X 0 ^ 4
  + 3 * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2

/-- Robinson's polynomial is homogeneous of degree 6. -/
lemma robinson_isHom : robinson.IsHomogeneous 6 := by
  have hC3 : (3 : MvPolynomial (Fin 3) ℝ) = C (3 : ℝ) := by
    rw [map_ofNat]
  have h3 : (3 : MvPolynomial (Fin 3) ℝ).IsHomogeneous 0 := by
    rw [hC3]; exact isHomogeneous_C _ _
  have t1 : ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 6).IsHomogeneous 6 := isHomogeneous_X_pow 0 6
  have t2 : ((X 1 : MvPolynomial (Fin 3) ℝ) ^ 6).IsHomogeneous 6 := isHomogeneous_X_pow 1 6
  have t3 : ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 6).IsHomogeneous 6 := isHomogeneous_X_pow 2 6
  have t4 : ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 4 * X 1 ^ 2).IsHomogeneous 6 :=
    (isHomogeneous_X_pow 0 4).mul (isHomogeneous_X_pow 1 2)
  have t5 : ((X 1 : MvPolynomial (Fin 3) ℝ) ^ 4 * X 2 ^ 2).IsHomogeneous 6 :=
    (isHomogeneous_X_pow 1 4).mul (isHomogeneous_X_pow 2 2)
  have t6 : ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 4 * X 0 ^ 2).IsHomogeneous 6 :=
    (isHomogeneous_X_pow 2 4).mul (isHomogeneous_X_pow 0 2)
  have t7 : ((X 0 : MvPolynomial (Fin 3) ℝ) ^ 2 * X 1 ^ 4).IsHomogeneous 6 :=
    (isHomogeneous_X_pow 0 2).mul (isHomogeneous_X_pow 1 4)
  have t8 : ((X 1 : MvPolynomial (Fin 3) ℝ) ^ 2 * X 2 ^ 4).IsHomogeneous 6 :=
    (isHomogeneous_X_pow 1 2).mul (isHomogeneous_X_pow 2 4)
  have t9 : ((X 2 : MvPolynomial (Fin 3) ℝ) ^ 2 * X 0 ^ 4).IsHomogeneous 6 :=
    (isHomogeneous_X_pow 2 2).mul (isHomogeneous_X_pow 0 4)
  have t10 : ((3 : MvPolynomial (Fin 3) ℝ) * X 0 ^ 2 * X 1 ^ 2 * X 2 ^ 2).IsHomogeneous 6 :=
    (((h3.mul (isHomogeneous_X_pow 0 2)).mul (isHomogeneous_X_pow 1 2)).mul
      (isHomogeneous_X_pow 2 2))
  unfold robinson
  exact ((((((((t1.add t2).add t3).sub t4).sub t5).sub t6).sub t7).sub t8).sub t9).add t10

lemma totalDegree_robinson : robinson.totalDegree ≤ 6 := robinson_isHom.totalDegree_le

lemma comp6_robinson : homogeneousComponent 6 robinson = robinson := by
  ext d
  rw [coeff_homogeneousComponent]
  by_cases hd : d.degree = 6
  · rw [if_pos hd]
  · rw [if_neg hd, robinson_isHom.coeff_eq_zero hd]

/-- The evaluation of Robinson's polynomial at a point. -/
lemma eval_robinson (v : Fin 3 → ℝ) :
    eval v robinson =
      v 0 ^ 6 + v 1 ^ 6 + v 2 ^ 6
      - v 0 ^ 4 * v 1 ^ 2 - v 1 ^ 4 * v 2 ^ 2 - v 2 ^ 4 * v 0 ^ 2
      - v 0 ^ 2 * v 1 ^ 4 - v 1 ^ 2 * v 2 ^ 4 - v 2 ^ 2 * v 0 ^ 4
      + 3 * v 0 ^ 2 * v 1 ^ 2 * v 2 ^ 2 := by
  simp only [robinson, map_add, map_sub, map_mul, map_pow, map_ofNat, eval_X]

/-- `R` does not vanish identically: `R(1,0,0) = 1`. -/
lemma eval_robinson_100 : eval ![1, 0, 0] robinson = 1 := by
  rw [eval_robinson]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-- The ten real projective zeros of Robinson's polynomial. -/
lemma eval_robinson_P1 : eval ![1, 1, 0] robinson = 0 := by
  rw [eval_robinson]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
lemma eval_robinson_P2 : eval ![1, -1, 0] robinson = 0 := by
  rw [eval_robinson]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
lemma eval_robinson_P3 : eval ![1, 0, 1] robinson = 0 := by
  rw [eval_robinson]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
lemma eval_robinson_P4 : eval ![1, 0, -1] robinson = 0 := by
  rw [eval_robinson]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
lemma eval_robinson_P5 : eval ![0, 1, 1] robinson = 0 := by
  rw [eval_robinson]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
lemma eval_robinson_P6 : eval ![0, 1, -1] robinson = 0 := by
  rw [eval_robinson]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
lemma eval_robinson_P7 : eval ![1, 1, 1] robinson = 0 := by
  rw [eval_robinson]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
lemma eval_robinson_P8 : eval ![1, 1, -1] robinson = 0 := by
  rw [eval_robinson]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
lemma eval_robinson_P9 : eval ![1, -1, 1] robinson = 0 := by
  rw [eval_robinson]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
lemma eval_robinson_P10 : eval ![1, -1, -1] robinson = 0 := by
  rw [eval_robinson]; norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

/-! ### Generic sum-of-squares / degree facts -/

variable {σ : Type*}

lemma totalDegree_eq_sup_degree (p : MvPolynomial σ ℝ) :
    p.totalDegree = p.support.sup (fun s => s.degree) := by
  rw [MvPolynomial.totalDegree]; apply Finset.sup_congr rfl
  intro s _; exact (Finsupp.degree_apply s).symm

/-- A finite sum of squares of polynomials over ℝ vanishes only if each does. -/
lemma sum_sq_eq_zero {m : ℕ} (f : Fin m → MvPolynomial σ ℝ)
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
lemma topForm_ne_zero (p : MvPolynomial σ ℝ) (hp : p ≠ 0) :
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

lemma totalDegree_sub_top_lt (p : MvPolynomial σ ℝ) (D : ℕ) (hD : 1 ≤ D)
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
lemma topsq (p : MvPolynomial σ ℝ) (D : ℕ) (hD : 1 ≤ D) (hpD : p.totalDegree ≤ D) :
    homogeneousComponent (2 * D) (p ^ 2) = (homogeneousComponent D p) ^ 2 := by
  set hd := homogeneousComponent D p with hhd
  set lo := p - hd with hlo
  have hdecomp : p = hd + lo := by rw [hlo]; ring
  have htd_lo : lo.totalDegree ≤ D - 1 := totalDegree_sub_top_lt p D hD hpD
  have htd_hd : hd.totalDegree ≤ D := (homogeneousComponent_isHomogeneous D p).totalDegree_le
  have hexp : p ^ 2 = hd ^ 2 + (hd * lo + hd * lo + lo ^ 2) := by rw [hdecomp]; ring
  rw [hexp, map_add]
  have h1 : homogeneousComponent (2 * D) (hd ^ 2) = hd ^ 2 := by
    have hh : (hd ^ 2) ∈ homogeneousSubmodule σ ℝ (D + D) := by
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

/-- If `∑ qᵢ² = P` with `totalDegree P ≤ 6`, then every `qᵢ` has total degree ≤ 3. -/
lemma degree_bound {m : ℕ} (P : MvPolynomial σ ℝ) (hP : P.totalDegree ≤ 6)
    (q : Fin m → MvPolynomial σ ℝ) (h : ∑ i, (q i) ^ 2 = P) (j : Fin m) :
    (q j).totalDegree ≤ 3 := by
  by_contra hcon
  push_neg at hcon
  set D := Finset.univ.sup (fun i => (q i).totalDegree) with hDdef
  have hjD : (q j).totalDegree ≤ D :=
    Finset.le_sup (f := fun i => (q i).totalDegree) (Finset.mem_univ j)
  have hD1 : 1 ≤ D := by omega
  have hzero : homogeneousComponent (2 * D) P = 0 := by
    apply homogeneousComponent_eq_zero
    exact lt_of_le_of_lt hP (by omega)
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

/-! ### The decisive linear algebra: a homogeneous cubic vanishing at the ten
points is zero. -/

/-- The evaluation of a single cubic monomial `r·xᵃyᵇzᶜ` at `v`. -/
lemma eval_mon3 (v : Fin 3 → ℝ) (a b c : ℕ) (r : ℝ) :
    eval v (monomial (mon3 a b c) r) = r * v 0 ^ a * v 1 ^ b * v 2 ^ c := by
  rw [show monomial (mon3 a b c) r = C r * (X 0 ^ a * X 1 ^ b * X 2 ^ c) by
    rw [Xpp3, C_mul_monomial, mul_one]]
  simp only [map_mul, map_pow, eval_C, eval_X]; ring

/-- A homogeneous cubic equals the sum of its ten cubic-monomial terms. -/
lemma as_cubic (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 3) :
    q = monomial (mon3 3 0 0) (coeff (mon3 3 0 0) q)
      + monomial (mon3 0 3 0) (coeff (mon3 0 3 0) q)
      + monomial (mon3 0 0 3) (coeff (mon3 0 0 3) q)
      + monomial (mon3 2 1 0) (coeff (mon3 2 1 0) q)
      + monomial (mon3 2 0 1) (coeff (mon3 2 0 1) q)
      + monomial (mon3 1 2 0) (coeff (mon3 1 2 0) q)
      + monomial (mon3 0 2 1) (coeff (mon3 0 2 1) q)
      + monomial (mon3 1 0 2) (coeff (mon3 1 0 2) q)
      + monomial (mon3 0 1 2) (coeff (mon3 0 1 2) q)
      + monomial (mon3 1 1 1) (coeff (mon3 1 1 1) q) := by
  ext μ
  simp only [coeff_add, coeff_monomial]
  rcases eq_or_ne μ.degree 3 with hd | hd
  · have hdeg : μ 0 + μ 1 + μ 2 = 3 := by rw [← deg_eq3]; exact hd
    rcases deg3_cases μ hdeg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [mon3_eq_iff]
  · rw [hq.coeff_eq_zero hd]
    have hne : ∀ a b c : ℕ, a + b + c = 3 → mon3 a b c ≠ μ := by
      intro a b c habc heq
      apply hd
      rw [← heq, degree_mon3]; omega
    rw [if_neg (hne 3 0 0 (by norm_num)), if_neg (hne 0 3 0 (by norm_num)),
      if_neg (hne 0 0 3 (by norm_num)), if_neg (hne 2 1 0 (by norm_num)),
      if_neg (hne 2 0 1 (by norm_num)), if_neg (hne 1 2 0 (by norm_num)),
      if_neg (hne 0 2 1 (by norm_num)), if_neg (hne 1 0 2 (by norm_num)),
      if_neg (hne 0 1 2 (by norm_num)), if_neg (hne 1 1 1 (by norm_num))]
    simp

/-- **The crux.** A homogeneous cubic form in three real variables vanishing at
    the ten real projective zeros of Robinson's polynomial is the zero
    polynomial. (The 10×10 evaluation matrix has determinant 128.) -/
lemma cubic_zero (q : MvPolynomial (Fin 3) ℝ) (hq : q.IsHomogeneous 3)
    (h1 : eval ![1, 1, 0] q = 0) (h2 : eval ![1, -1, 0] q = 0)
    (h3 : eval ![1, 0, 1] q = 0) (h4 : eval ![1, 0, -1] q = 0)
    (h5 : eval ![0, 1, 1] q = 0) (h6 : eval ![0, 1, -1] q = 0)
    (h7 : eval ![1, 1, 1] q = 0) (h8 : eval ![1, 1, -1] q = 0)
    (h9 : eval ![1, -1, 1] q = 0) (h10 : eval ![1, -1, -1] q = 0) :
    q = 0 := by
  have hcub := as_cubic q hq
  -- Rewrite each evaluation as a linear combination of the ten coefficients.
  have E : ∀ v : Fin 3 → ℝ, eval v q =
      coeff (mon3 3 0 0) q * v 0 ^ 3 + coeff (mon3 0 3 0) q * v 1 ^ 3
      + coeff (mon3 0 0 3) q * v 2 ^ 3
      + coeff (mon3 2 1 0) q * v 0 ^ 2 * v 1 + coeff (mon3 2 0 1) q * v 0 ^ 2 * v 2
      + coeff (mon3 1 2 0) q * v 0 * v 1 ^ 2 + coeff (mon3 0 2 1) q * v 1 ^ 2 * v 2
      + coeff (mon3 1 0 2) q * v 0 * v 2 ^ 2 + coeff (mon3 0 1 2) q * v 1 * v 2 ^ 2
      + coeff (mon3 1 1 1) q * v 0 * v 1 * v 2 := by
    intro v
    conv_lhs => rw [hcub]
    simp only [map_add, eval_mon3]
    ring
  -- Plug in the ten points; each gives a linear equation in the coefficients.
  rw [E] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  -- Solve the invertible 10×10 system: every coefficient is zero.
  have za : coeff (mon3 3 0 0) q = 0 := by linarith
  have zb : coeff (mon3 0 3 0) q = 0 := by linarith
  have zc : coeff (mon3 0 0 3) q = 0 := by linarith
  have zd : coeff (mon3 2 1 0) q = 0 := by linarith
  have ze : coeff (mon3 2 0 1) q = 0 := by linarith
  have zf : coeff (mon3 1 2 0) q = 0 := by linarith
  have zg : coeff (mon3 0 2 1) q = 0 := by linarith
  have zh : coeff (mon3 1 0 2) q = 0 := by linarith
  have zi : coeff (mon3 0 1 2) q = 0 := by linarith
  have zj : coeff (mon3 1 1 1) q = 0 := by linarith
  -- A homogeneous cubic with all ten coefficients zero is zero.
  rw [hcub, za, zb, zc, zd, ze, zf, zg, zh, zi, zj]
  simp

/-! ### Assembling the non-existence proof -/

/-- A multivariate polynomial is a sum of squares of polynomials. (Matches the
    definition `IsSumOfSquaresMvPolynomial` of the parent entry.) -/
def IsSOS (p : MvPolynomial (Fin 3) ℝ) : Prop :=
  ∃ (m : ℕ) (q : Fin m → MvPolynomial (Fin 3) ℝ), p = ∑ i, q i ^ 2

/-- **Robinson's polynomial is not a sum of squares of polynomials.** -/
theorem robinson_not_sos : ¬ IsSOS robinson := by
  rintro ⟨m, q, hq⟩
  have hsum : ∑ i, (q i) ^ 2 = robinson := hq.symm
  -- Step 1: degree bound.
  have hdb : ∀ j, (q j).totalDegree ≤ 3 :=
    fun j => degree_bound robinson totalDegree_robinson q hsum j
  -- Step 2: R is the sum of squares of the homogeneous cubic parts.
  have hR : robinson = ∑ i, (homogeneousComponent 3 (q i)) ^ 2 := by
    rw [← comp6_robinson, ← hsum, map_sum]
    apply Finset.sum_congr rfl; intro i _
    exact topsq (q i) 3 (by norm_num) (hdb i)
  -- Step 3: each cubic part vanishes at the ten zeros.
  have hvan : ∀ v : Fin 3 → ℝ, eval v robinson = 0 →
      ∀ i, eval v (homogeneousComponent 3 (q i)) = 0 := by
    intro v hv i
    have hz : ∑ k, (eval v (homogeneousComponent 3 (q k))) ^ 2 = 0 := by
      have h2 : eval v robinson = ∑ k, (eval v (homogeneousComponent 3 (q k))) ^ 2 := by
        rw [hR, map_sum]; apply Finset.sum_congr rfl; intro k _; rw [map_pow]
      rw [← h2]; exact hv
    exact sum_sq_real_eq_zero _ hz i
  -- Step 4: each cubic part is therefore zero.
  have hQ0 : ∀ i, homogeneousComponent 3 (q i) = 0 := by
    intro i
    exact cubic_zero _ (homogeneousComponent_isHomogeneous 3 (q i))
      (hvan _ eval_robinson_P1 i) (hvan _ eval_robinson_P2 i) (hvan _ eval_robinson_P3 i)
      (hvan _ eval_robinson_P4 i) (hvan _ eval_robinson_P5 i) (hvan _ eval_robinson_P6 i)
      (hvan _ eval_robinson_P7 i) (hvan _ eval_robinson_P8 i) (hvan _ eval_robinson_P9 i)
      (hvan _ eval_robinson_P10 i)
  -- So R = 0, contradicting R(1,0,0) = 1.
  have hR0 : robinson = 0 := by
    rw [hR]; apply Finset.sum_eq_zero; intro i _; rw [hQ0 i]; ring
  have := eval_robinson_100
  rw [hR0] at this; simp at this

end Hilbert17RobinsonNotSOS

-- Axiom audit: should list only propext, Classical.choice, Quot.sound.
#print axioms Hilbert17RobinsonNotSOS.robinson_not_sos
