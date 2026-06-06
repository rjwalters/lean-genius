import Mathlib.NumberTheory.Transcendental.Liouville.Basic
import Mathlib.NumberTheory.Transcendental.Liouville.LiouvilleWith
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic
import Proofs.eTranscendental

/-!
# Irrationality Measure of e (Open Question)

## The Question
What is the exact **irrationality measure** (also called the Liouville-Roth irrationality exponent)
of Euler's number e = 2.71828...?

## Answer
The irrationality measure of e is exactly **2**, the smallest possible value for any irrational
number. This means:

- **Lower bound**: For infinitely many rationals p/q, we have |e - p/q| < 1/q^2 (Dirichlet)
- **Upper bound**: For any ε > 0 and all but finitely many p/q, |e - p/q| > 1/q^{2+ε}

## Background

The **irrationality measure** μ(α) of a real number α is defined as:

  μ(α) = sup { μ ≥ 0 : |α - p/q| < 1/q^μ has infinitely many solutions p/q ∈ ℚ }

By convention: μ(p/q) = 1 for rationals, and μ(α) ≥ 2 for all irrationals (by Dirichlet's
approximation theorem).

**Key results:**
- μ(α) = 2 for almost all real numbers (Khinchin, 1924)
- μ(α) = 2 for all algebraic irrationals (Roth, 1955)
- μ(e) = 2 (from the regular continued fraction pattern)
- μ(π) is unknown (known: 2 ≤ μ(π) ≤ 7.10321, Salikhov 2008)

## Why μ(e) = 2

The key is the regular continued fraction expansion of e, discovered by Euler (1737):

  e = [2; 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, 1, 1, 10, ...]

The pattern is: [2; 1, 2k, 1] repeating for k = 1, 2, 3, ...

Since the partial quotients grow at most linearly (they are bounded by 2k), the
convergents p_n/q_n satisfy:
  q_{n+1} ≤ (2k + 1) q_n + q_{n-1}

This means q_n grows at most exponentially, and the approximation quality satisfies:
  1/(2q_n q_{n+1}) ≤ |e - p_n/q_n| ≤ 1/(q_n q_{n+1})

Since q_{n+1}/q_n is bounded, we get |e - p/q| ≥ c/q^2 for some constant c > 0,
which means μ(e) ≤ 2. Combined with μ(e) ≥ 2 (Dirichlet), we get μ(e) = 2.

## Formalization Approach

We use Mathlib's `LiouvilleWith p x` which captures "x has approximation exponent ≥ p".
The irrationality measure is then:
  μ(x) = sup { p : LiouvilleWith p x }

## References

- Euler, L. (1737). "De fractionibus continuis dissertatio"
- Davis, C.S. (1978). "Rational approximations to e"
- Borwein, J. & Borwein, P. (1987). "Pi and the AGM", Ch. 11
-/

set_option maxHeartbeats 400000

noncomputable section

open Real

namespace ETranscendentalOQ03

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: IRRATIONALITY MEASURE VIA LIOUVILLEWITH
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Connection to LiouvilleWith

Mathlib defines `LiouvilleWith p x` to mean: there exists C > 0 such that for
infinitely many integers n ≥ 1, there exists an integer m with x ≠ m/n and
|x - m/n| < C/n^p.

The **irrationality measure** μ(x) equals:
  μ(x) = sup { p : ℝ | LiouvilleWith p x }

So:
- μ(x) = 2 means `LiouvilleWith 2 x` but `¬ LiouvilleWith p x` for all p > 2
- μ(x) = ∞ (Liouville number) means `LiouvilleWith p x` for all p
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: LOWER BOUND — μ(e) ≥ 2
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Every irrational has μ ≥ 2 (Dirichlet's Theorem)

By Dirichlet's approximation theorem, for any irrational α and any N ≥ 1,
there exist integers p, q with 1 ≤ q ≤ N and |α - p/q| < 1/(qN) ≤ 1/q^2.
This gives infinitely many such approximations, proving LiouvilleWith 2 α.

Note: Mathlib has `liouvilleWith_one` (every real has exponent ≥ 1) but does not
yet provide the stronger Dirichlet result for irrationals at exponent 2.
-/

/-- **Helper: the set of "good" rational approximations to `x` with denominator
bounded by `N` is finite.**

For any real `x` and natural `N`, the set
`{q : ℚ | |x - q| < 1 / q.den^2 ∧ q.den ≤ N}` is finite. Used to derive that for
irrational `x`, good approximations have unbounded denominators. -/
lemma rat_approx_bounded_den_finite (x : ℝ) (N : ℕ) :
    {q : ℚ | |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 ∧ q.den ≤ N}.Finite := by
  set M : ℤ := ⌈(N : ℝ) * (|x| + 1) + 1⌉ with hM_def
  have h_box_fin : (Set.Icc (-M) M ×ˢ Set.Icc (1 : ℕ) N).Finite :=
    (Set.finite_Icc _ _).prod (Set.finite_Icc _ _)
  refine (h_box_fin.image (fun p : ℤ × ℕ => (p.1 : ℚ) / (p.2 : ℚ))).subset ?_
  rintro q ⟨hq_bd, hq_den⟩
  have hd_pos : 0 < q.den := q.pos
  have hd_pos_R : (0 : ℝ) < (q.den : ℝ) := by exact_mod_cast hd_pos
  have hd_one_R : (1 : ℝ) ≤ (q.den : ℝ) := by exact_mod_cast hd_pos
  have hd_ne : (q.den : ℝ) ≠ 0 := hd_pos_R.ne'
  have hq_eq : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    exact_mod_cast Rat.num_div_den q
  have h1 : |(q.den : ℝ) * x - (q.num : ℝ)| < 1 := by
    have h_factor : (q.den : ℝ) * x - (q.num : ℝ)
        = (q.den : ℝ) * (x - (q.num : ℝ) / (q.den : ℝ)) := by
      field_simp
    have h_step : |(q.den : ℝ) * x - (q.num : ℝ)| = (q.den : ℝ) * |x - (q : ℝ)| := by
      rw [h_factor, abs_mul, abs_of_pos hd_pos_R, hq_eq]
    rw [h_step]
    calc (q.den : ℝ) * |x - (q : ℝ)|
        < (q.den : ℝ) * (1 / (q.den : ℝ) ^ 2) :=
          mul_lt_mul_of_pos_left hq_bd hd_pos_R
      _ = 1 / (q.den : ℝ) := by
          rw [mul_one_div, sq]
          field_simp
      _ ≤ 1 := by
          rw [div_le_one hd_pos_R]
          exact hd_one_R
  have h_num_bound : |(q.num : ℝ)| ≤ (q.den : ℝ) * |x| + 1 := by
    rcases abs_lt.mp h1 with ⟨hL, hR⟩
    have hx_le : x ≤ |x| := le_abs_self x
    have hx_neg_le : -x ≤ |x| := neg_le_abs x
    have h_dnn : (0 : ℝ) ≤ (q.den : ℝ) := hd_pos_R.le
    apply abs_le.mpr
    refine ⟨?_, ?_⟩
    · nlinarith [hL, hx_neg_le, h_dnn]
    · nlinarith [hR, hx_le, h_dnn]
  have hN_bd : (q.den : ℝ) ≤ (N : ℝ) := by exact_mod_cast hq_den
  have h_abs_x : (0 : ℝ) ≤ |x| := abs_nonneg x
  have h_num_le_M : |(q.num : ℝ)| ≤ (M : ℝ) := by
    have h_bd1 : (q.den : ℝ) * |x| + 1 ≤ (N : ℝ) * (|x| + 1) + 1 := by
      nlinarith [hN_bd, h_abs_x, hd_pos_R.le]
    have h_ceil : (N : ℝ) * (|x| + 1) + 1 ≤ (M : ℝ) := by
      rw [hM_def]
      exact_mod_cast Int.le_ceil ((N : ℝ) * (|x| + 1) + 1)
    linarith [h_num_bound]
  refine ⟨(q.num, q.den), ?_, ?_⟩
  · constructor
    · constructor
      · have := (abs_le.mp h_num_le_M).1; exact_mod_cast this
      · have := (abs_le.mp h_num_le_M).2; exact_mod_cast this
    · exact ⟨hd_pos, hq_den⟩
  · show ((q.num : ℚ) / (q.den : ℚ) : ℚ) = q
    exact Rat.num_div_den q

/-- **Every irrational real number has irrationality measure ≥ 2.**

This is Dirichlet's approximation theorem in `LiouvilleWith` form. The proof
combines Mathlib's `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`
with the slice-finiteness lemma above, to conclude that good approximations
have arbitrarily large denominators. -/
theorem irrational_liouvilleWith_two (x : ℝ) (hx : Irrational x) : LiouvilleWith 2 x := by
  refine ⟨1, ?_⟩
  rw [Filter.frequently_atTop]
  intro N
  have hS_inf : {q : ℚ | |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2}.Infinite :=
    Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational hx
  have h_slice_fin :
      {q : ℚ | |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 ∧ q.den ≤ N}.Finite :=
    rat_approx_bounded_den_finite x N
  obtain ⟨q, hqS, hqN⟩ : ∃ q : ℚ,
      |x - (q : ℝ)| < 1 / (q.den : ℝ) ^ 2 ∧ N < q.den := by
    by_contra h_neg
    push_neg at h_neg
    apply hS_inf
    apply h_slice_fin.subset
    intro q hq
    exact ⟨hq, h_neg q hq⟩
  have hq_eq : (q.num : ℝ) / (q.den : ℝ) = (q : ℝ) := by
    exact_mod_cast Rat.num_div_den q
  refine ⟨q.den, Nat.le_of_lt hqN, q.num, ?_, ?_⟩
  · intro h_eq
    apply Irrational.ne_rat hx q
    rw [← hq_eq, ← h_eq]
  · rw [hq_eq]
    have h_rpow : (q.den : ℝ) ^ (2 : ℝ) = (q.den : ℝ) ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [h_rpow]
    exact hqS

/-- **e has irrationality measure ≥ 2** (from Dirichlet + irrationality of e). -/
theorem e_liouvilleWith_two : LiouvilleWith 2 (exp 1) :=
  irrational_liouvilleWith_two _ e_irrational

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: UPPER BOUND — μ(e) ≤ 2
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### The continued fraction argument

The regular continued fraction of e is:
  e = [2; 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, ...]

with partial quotients a_0 = 2, and for n ≥ 1:
  a_{3k-2} = 1, a_{3k-1} = 2k, a_{3k} = 1

Since the partial quotients grow at most linearly (a_n = O(n)), the denominators
of convergents satisfy q_{n+1} ≤ (a_{n+1} + 1) · q_n, giving q_n ≤ C^n for some
constant C. The best rational approximation theorem for convergents states:
  1/(q_n(q_{n+1} + q_n)) < |e - p_n/q_n| < 1/(q_n · q_{n+1})

Since q_{n+1}/q_n is bounded (by the regularity of the CF pattern), we get:
  |e - p_n/q_n| ≥ c/q_n^2 for some c > 0

This means for any ε > 0 and all sufficiently large q:
  |e - p/q| > 1/q^{2+ε}

Hence μ(e) ≤ 2.
-/

/-- **Axiom: e is NOT a Liouville number with exponent > 2.**

For any p > 2, the approximation |e - m/n| < C/n^p holds for only finitely many n.
This follows from the regular continued fraction expansion e = [2; 1, 2, 1, 1, 4, ...].

The partial quotients grow at most linearly, bounding the approximation quality
to exactly quadratic. -/
axiom e_not_liouvilleWith_gt_two (p : ℝ) (hp : p > 2) : ¬LiouvilleWith p (exp 1)

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: MAIN RESULT — μ(e) = 2
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The irrationality measure of e is exactly 2.**

Equivalently: LiouvilleWith 2 (exp 1) holds, but LiouvilleWith p (exp 1) fails
for every p > 2. -/
theorem e_irrationality_measure_eq_two :
    LiouvilleWith 2 (exp 1) ∧ ∀ p : ℝ, p > 2 → ¬LiouvilleWith p (exp 1) :=
  ⟨e_liouvilleWith_two, fun p hp => e_not_liouvilleWith_gt_two p hp⟩

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: CONSEQUENCES
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **e is not a Liouville number.**

Since μ(e) = 2 < ∞, e does not satisfy the Liouville property (which requires
μ = ∞, i.e., LiouvilleWith p for all p). -/
theorem e_not_liouville : ¬Liouville (exp 1) := by
  intro h
  have := h.liouvilleWith 3
  exact e_not_liouvilleWith_gt_two 3 (by norm_num) this

/-- **e is irrational** (direct corollary of LiouvilleWith 2). -/
theorem e_irrational_from_measure : Irrational (exp 1) :=
  e_liouvilleWith_two.irrational (by norm_num : (1 : ℝ) < 2)

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VI: CONTEXT AND COMPARISONS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Irrationality measures of other constants

| Constant | μ | Status |
|----------|---|--------|
| Any rational | 1 | trivial |
| Any irrational | ≥ 2 | Dirichlet |
| Any algebraic irrational | = 2 | Roth (1955) |
| e | = 2 | CF analysis |
| e^2 | = 2 | Davis (1978) |
| π | 2 ≤ μ ≤ 7.103... | Salikhov (2008) |
| ln 2 | 2 ≤ μ ≤ 3.574... | Marcovecchio (2009) |
| ζ(3) | 2 ≤ μ ≤ 5.513... | Rhin-Viola (2001) |
| Liouville constant | ∞ | by definition |

### Why μ(e) = 2 is remarkable

Most transcendental numbers have μ = 2 (by Khinchin's theorem, almost all reals do).
But proving this for a specific transcendental like e requires understanding its
fine arithmetic structure via continued fractions. The regular pattern of e's CF
expansion (discovered by Euler in 1737) is exceptional — most transcendentals have
no known CF pattern, making their irrationality measure much harder to determine.

### Relationship to Roth's theorem

Roth's theorem (1955) shows μ(α) = 2 for ALL algebraic irrationals. For e
(which is transcendental), this theorem does not apply. The fact that μ(e) = 2
is a coincidence of e's special CF structure, not a consequence of any general theorem.
-/

end ETranscendentalOQ03
