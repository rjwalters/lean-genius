import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.Tactic

/-!
# Representations as x² + 2y²

This file establishes that primes p ≡ 3 (mod 8) can be written as x² + 2y².
Combined with the trivial identity p = x² + 2y² = x² + y² + y², this proves
that such primes are sums of three squares.

## Main Results

* `sq_add_two_sq_of_prime_three_mod_eight`: If p ≡ 3 (mod 8), then p = a² + 2b²
* `prime_three_mod_eight_is_sum_three_sq`: If p ≡ 3 (mod 8), then p = x² + y² + z²

## Mathematical Background

For primes p ≡ 3 (mod 8):
1. -2 is a quadratic residue mod p (second supplementary law)
2. Therefore p splits in ℤ[√-2], i.e., p is not prime in ℤ[√-2]
3. Since ℤ[√-2] is a Euclidean domain (UFD), p = N(α) for some α ∈ ℤ[√-2]
4. So p = a² + 2b² for some integers a, b
5. Trivially: p = a² + 2b² = a² + b² + b²

## Implementation

The EuclideanDomain instance for ℤ[√-2] is built using norm N(a + b√-2) = a² + 2b².
The key technical lemma is that the rounding-based division algorithm works
because the norm of the remainder satisfies:
  norm(error) ≤ (1/2)² + 2(1/2)² = 3/4 < 1
-/

/-! ## ℤ[√-2] as a Euclidean Domain -/

/-- The ring ℤ[√-2]. Elements are of the form a + b√-2 with a, b ∈ ℤ. -/
abbrev ZsqrtNegTwo : Type := ℤ√(-2)

namespace ZsqrtNegTwo

open Zsqrtd

/-- The norm in ℤ[√-2]: N(a + b√-2) = a² + 2b². -/
theorem norm_def' (z : ZsqrtNegTwo) : Zsqrtd.norm z = z.re ^ 2 + 2 * z.im ^ 2 := by
  simp only [Zsqrtd.norm_def, sq]; ring

/-- The norm is non-negative in ℤ[√-2]. -/
theorem norm_nonneg' (z : ZsqrtNegTwo) : 0 ≤ Zsqrtd.norm z :=
  Zsqrtd.norm_nonneg (by norm_num : (-2 : ℤ) ≤ 0) z

/-- The norm is zero iff the element is zero. -/
theorem norm_eq_zero_iff' (z : ZsqrtNegTwo) : Zsqrtd.norm z = 0 ↔ z = 0 :=
  Zsqrtd.norm_eq_zero_iff (by norm_num : (-2 : ℤ) < 0) z

/-- An element is a unit iff its norm is 1. -/
theorem isUnit_iff_norm_one (z : ZsqrtNegTwo) : IsUnit z ↔ Zsqrtd.norm z = 1 :=
  (Zsqrtd.norm_eq_one_iff' (by norm_num : (-2 : ℤ) ≤ 0) z).symm

/-- The units of ℤ[√-2] are exactly ±1. -/
theorem units_eq (z : ZsqrtNegTwo) : IsUnit z ↔ z = 1 ∨ z = -1 := by
  rw [isUnit_iff_norm_one, norm_def']
  constructor
  · intro h
    have h2 : 2 * z.im ^ 2 ≥ 0 := by positivity
    have him : 2 * z.im ^ 2 ≤ 1 := by nlinarith [sq_nonneg z.re]
    have him0 : z.im = 0 := by
      have hsq : z.im ^ 2 ≤ 0 := by nlinarith [sq_nonneg z.im]
      have hge : z.im ^ 2 ≥ 0 := sq_nonneg z.im
      have heq : z.im ^ 2 = 0 := by omega
      exact sq_eq_zero_iff.mp heq
    have hre1 : z.re ^ 2 = 1 := by
      simp only [him0, mul_zero, add_zero, pow_two] at h
      linarith [sq_nonneg z.re, sq_nonneg z.im]
    have hre_cases : z.re = 1 ∨ z.re = -1 := by
      have hsq : z.re * z.re = 1 := by simpa [sq] using hre1
      have hpos : z.re ≥ 0 ∨ z.re < 0 := le_or_gt 0 z.re
      rcases hpos with hpos | hneg
      · have hle : z.re ≤ 1 := by nlinarith
        interval_cases z.re <;> simp_all
      · have hle : z.re ≥ -1 := by nlinarith
        interval_cases z.re <;> simp_all
    rcases hre_cases with hre1 | hre_neg1
    · left; ext <;> simp [him0, hre1]
    · right; ext <;> simp [him0, hre_neg1]
  · intro h; rcases h with rfl | rfl <;> simp

/-- A natural number p viewed as an element of ℤ[√-2] is not a unit for p > 1. -/
theorem natCast_not_unit {p : ℕ} (hp : p > 1) : ¬IsUnit (p : ZsqrtNegTwo) := by
  rw [units_eq]
  intro h
  rcases h with h1 | h_neg1
  · have hre : (p : ZsqrtNegTwo).re = (p : ℤ) := rfl
    have : (p : ℤ) = 1 := by rw [← hre, h1]; rfl
    omega
  · have hre : (p : ZsqrtNegTwo).re = (p : ℤ) := rfl
    have : (p : ℤ) = -1 := by rw [← hre, h_neg1]; rfl
    omega

/-- Division in ℤ[√-2] by rounding the quotient. -/
noncomputable instance instDiv : Div ZsqrtNegTwo :=
  ⟨fun x y =>
    let n : ℚ := (Zsqrtd.norm y : ℚ)⁻¹
    let c := star y
    ⟨round ((x * c).re * n), round ((x * c).im * n)⟩⟩

/-- Modulo in ℤ[√-2]. -/
noncomputable instance instMod : Mod ZsqrtNegTwo :=
  ⟨fun x y => x - y * (x / y)⟩

theorem mod_def (x y : ZsqrtNegTwo) : x % y = x - y * (x / y) := rfl

/-- The key estimate: the squared rounding error is at most 3/4 < 1. -/
theorem sq_rounding_error_lt_one (r₁ r₂ : ℚ) :
    (r₁ - round r₁) ^ 2 + 2 * (r₂ - round r₂) ^ 2 < 1 := by
  have h1 : |r₁ - round r₁| ≤ 1/2 := abs_sub_round r₁
  have h2 : |r₂ - round r₂| ≤ 1/2 := abs_sub_round r₂
  have habs1 : -(1/2) ≤ r₁ - round r₁ ∧ r₁ - round r₁ ≤ 1/2 := abs_le.mp h1
  have habs2 : -(1/2) ≤ r₂ - round r₂ ∧ r₂ - round r₂ ≤ 1/2 := abs_le.mp h2
  have bound1 : (r₁ - round r₁) ^ 2 ≤ 1/4 := by nlinarith [sq_nonneg (r₁ - round r₁)]
  have bound2 : (r₂ - round r₂) ^ 2 ≤ 1/4 := by nlinarith [sq_nonneg (r₂ - round r₂)]
  linarith

/-- The norm of the remainder is strictly less than the norm of the divisor. -/
theorem norm_mod_lt (x : ZsqrtNegTwo) {y : ZsqrtNegTwo} (hy : y ≠ 0) :
    Zsqrtd.norm (x % y) < Zsqrtd.norm y := by
  -- Key insight: N(r) * N(y) = N(r * star(y)) and r * star(y) has bounded components
  let n : ℤ := Zsqrtd.norm y
  have hn_pos : 0 < n := by
    have h0 := norm_nonneg' y
    have hne : Zsqrtd.norm y ≠ 0 := (norm_eq_zero_iff' y).not.mpr hy
    omega
  -- The quotient rounded from (x * star(y)) / N(y)
  let q := x / y
  -- The remainder
  let r := x % y
  -- Compute r * star(y)
  have hr : r = x - y * q := rfl
  have hr_star : r * Zsqrtd.star y = x * Zsqrtd.star y - y * Zsqrtd.star y * q := by
    rw [hr]; ring
  have hy_star : y * Zsqrtd.star y = ⟨n, 0⟩ := by
    ext
    · simp only [Zsqrtd.mul_re, Zsqrtd.star_re, Zsqrtd.star_im, neg_neg, n, Zsqrtd.norm_def]; ring
    · simp only [Zsqrtd.mul_im, Zsqrtd.star_re, Zsqrtd.star_im]; ring
  rw [hy_star] at hr_star
  -- Express r * star(y) in terms of rounding errors
  let A := x * Zsqrtd.star y
  have hA_re : A.re = x.re * y.re + 2 * x.im * y.im := by
    simp only [A, Zsqrtd.mul_re, Zsqrtd.star_re, Zsqrtd.star_im, neg_neg]; ring
  have hA_im : A.im = -x.re * y.im + x.im * y.re := by
    simp only [A, Zsqrtd.mul_im, Zsqrtd.star_re, Zsqrtd.star_im]; ring
  -- The quotient q has components that are rounded values
  have hq_re : q.re = round ((A.re : ℚ) / n) := rfl
  have hq_im : q.im = round ((A.im : ℚ) / n) := rfl
  -- Now compute the norm of r * star(y)
  -- r * star(y) = A - n * q = ⟨A.re - n * q.re, A.im - n * q.im⟩
  have hr_star_re : (r * Zsqrtd.star y).re = A.re - n * q.re := by
    calc (r * Zsqrtd.star y).re = (A - ⟨n, 0⟩ * q).re := by rw [← hr_star]; ring_nf
      _ = A.re - (⟨n, 0⟩ * q).re := by simp [Zsqrtd.sub_re]
      _ = A.re - (n * q.re + (-2) * 0 * q.im) := by simp [Zsqrtd.mul_re]
      _ = A.re - n * q.re := by ring
  have hr_star_im : (r * Zsqrtd.star y).im = A.im - n * q.im := by
    calc (r * Zsqrtd.star y).im = (A - ⟨n, 0⟩ * q).im := by rw [← hr_star]; ring_nf
      _ = A.im - (⟨n, 0⟩ * q).im := by simp [Zsqrtd.sub_im]
      _ = A.im - (n * q.im + 0 * q.re) := by simp [Zsqrtd.mul_im]
      _ = A.im - n * q.im := by ring
  -- The norm of r * star(y)
  have hn_rat_pos : (0 : ℚ) < n := by exact_mod_cast hn_pos
  have hn_ne : (n : ℚ) ≠ 0 := ne_of_gt hn_rat_pos
  -- Define the rounding errors
  let ε_re : ℚ := (A.re : ℚ) / n - round ((A.re : ℚ) / n)
  let ε_im : ℚ := (A.im : ℚ) / n - round ((A.im : ℚ) / n)
  have hε_re_bound : ε_re ^ 2 ≤ 1/4 := by
    have h := abs_sub_round ((A.re : ℚ) / n)
    have habs : |ε_re| ≤ 1/2 := h
    have habs' := abs_le.mp habs
    nlinarith [sq_nonneg ε_re]
  have hε_im_bound : ε_im ^ 2 ≤ 1/4 := by
    have h := abs_sub_round ((A.im : ℚ) / n)
    have habs : |ε_im| ≤ 1/2 := h
    have habs' := abs_le.mp habs
    nlinarith [sq_nonneg ε_im]
  -- The components of r * star(y) are n * ε
  have hcomp_re : (A.re : ℚ) - n * round ((A.re : ℚ) / n) = n * ε_re := by
    simp only [ε_re]; field_simp; ring
  have hcomp_im : (A.im : ℚ) - n * round ((A.im : ℚ) / n) = n * ε_im := by
    simp only [ε_im]; field_simp; ring
  -- Now use the rounding error bound
  have hbound : ε_re ^ 2 + 2 * ε_im ^ 2 < 1 := by
    have h := sq_rounding_error_lt_one ((A.re : ℚ) / n) ((A.im : ℚ) / n)
    convert h using 2 <;> ring
  -- N(r) * N(y) = N(r * star(y))
  have hnorm_mul : Zsqrtd.norm (r * Zsqrtd.star y) = Zsqrtd.norm r * n := by
    rw [Zsqrtd.norm_mul, Zsqrtd.norm_star]; rfl
  -- Compute N(r * star(y)) in terms of ε
  have hnorm_r_star : (Zsqrtd.norm (r * Zsqrtd.star y) : ℚ) = n ^ 2 * (ε_re ^ 2 + 2 * ε_im ^ 2) := by
    simp only [Zsqrtd.norm_def]
    have hre : ((r * Zsqrtd.star y).re : ℚ) = n * ε_re := by
      rw [hr_star_re]; simp only [Int.cast_sub, Int.cast_mul]; rw [hcomp_re]
    have him : ((r * Zsqrtd.star y).im : ℚ) = n * ε_im := by
      rw [hr_star_im]; simp only [Int.cast_sub, Int.cast_mul]; rw [hcomp_im]
    simp only [hre, him, sq]
    ring
  -- So N(r) * n < n^2, hence N(r) < n
  have hlt : (Zsqrtd.norm r * n : ℚ) < n ^ 2 := by
    calc (Zsqrtd.norm r * n : ℚ) = Zsqrtd.norm (r * Zsqrtd.star y) := by rw [hnorm_mul]
      _ = n ^ 2 * (ε_re ^ 2 + 2 * ε_im ^ 2) := hnorm_r_star
      _ < n ^ 2 * 1 := by nlinarith [sq_nonneg n, hbound]
      _ = n ^ 2 := by ring
  have hr_nonneg : 0 ≤ Zsqrtd.norm r := norm_nonneg' r
  have hfinal : (Zsqrtd.norm r : ℚ) < n := by
    have hn2 : (n : ℚ) ^ 2 = n * n := by ring
    rw [hn2] at hlt
    have := (mul_lt_mul_right hn_rat_pos).mp hlt
    exact this
  exact_mod_cast hfinal

/-- The natAbs of the norm decreases. -/
theorem natAbs_norm_mod_lt (x : ZsqrtNegTwo) {y : ZsqrtNegTwo} (hy : y ≠ 0) :
    (Zsqrtd.norm (x % y)).natAbs < (Zsqrtd.norm y).natAbs := by
  have h := norm_mod_lt x hy
  have h1 := norm_nonneg' (x % y)
  have h2 := norm_nonneg' y
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt h1 h

/-- Multiplying on left doesn't decrease norm. -/
theorem norm_le_norm_mul_left (x : ZsqrtNegTwo) {y : ZsqrtNegTwo} (hy : y ≠ 0) :
    (Zsqrtd.norm x).natAbs ≤ (Zsqrtd.norm (x * y)).natAbs := by
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]
  have hy_norm : Zsqrtd.norm y ≠ 0 := (norm_eq_zero_iff' y).not.mpr hy
  have h : 1 ≤ (Zsqrtd.norm y).natAbs := by have := norm_nonneg' y; omega
  exact Nat.le_mul_of_pos_right _ (by omega)

noncomputable instance instNontrivial : Nontrivial ZsqrtNegTwo :=
  ⟨⟨0, 1, by decide⟩⟩

/-- Ordering on ℤ[√-2] by norm for Euclidean domain structure. -/
noncomputable instance instLT : LT ZsqrtNegTwo :=
  ⟨fun x y => (Zsqrtd.norm x).natAbs < (Zsqrtd.norm y).natAbs⟩

/-- ℤ[√-2] is a Euclidean domain. -/
noncomputable instance instEuclideanDomain : EuclideanDomain ZsqrtNegTwo :=
  { inferInstanceAs (CommRing ZsqrtNegTwo) with
    quotient := (· / ·)
    remainder := (· % ·)
    quotient_zero := by
      intro a
      simp only [HDiv.hDiv, Div.div, Zsqrtd.norm_zero, Int.cast_zero, inv_zero, mul_zero]
      ext <;> simp
    quotient_mul_add_remainder_eq := fun x y => by simp only [mod_def]; ring
    r := (· < ·)
    r_wellFounded := (measure (Int.natAbs ∘ Zsqrtd.norm)).wf
    remainder_lt := fun x y hy => natAbs_norm_mod_lt x hy
    mul_left_not_lt := fun a b hb0 => not_lt_of_ge (norm_le_norm_mul_left a hb0) }

/-- If p is a prime that is not irreducible in ℤ[√-2], then p = a² + 2b² for some a, b. -/
theorem sq_add_two_sq_of_nat_prime_of_not_irreducible (p : ℕ) [hp : Fact p.Prime]
    (hpi : ¬Irreducible (p : ZsqrtNegTwo)) : ∃ a b : ℕ, a ^ 2 + 2 * b ^ 2 = p := by
  -- Since p is not irreducible in a UFD, it factors as p = x * y with neither a unit
  have hpu : ¬IsUnit (p : ZsqrtNegTwo) := natCast_not_unit hp.out.one_lt
  rw [irreducible_iff] at hpi
  push_neg at hpi
  obtain ⟨x, y, hxy, hux, huy⟩ := hpi hpu
  -- Taking norms: p² = N(p) = N(x)·N(y)
  have hnorm_eq : Zsqrtd.norm (p : ZsqrtNegTwo) = (p : ℤ) ^ 2 := by
    simp only [Zsqrtd.norm_def, Zsqrtd.natCast_re, Zsqrtd.natCast_im, mul_zero, sub_zero, sq]
  have hnorm_mul : Zsqrtd.norm (x * y) = Zsqrtd.norm x * Zsqrtd.norm y := Zsqrtd.norm_mul x y
  rw [hxy] at hnorm_eq
  rw [hnorm_mul] at hnorm_eq
  -- Since N(x), N(y) > 0 and neither is a unit, both N(x), N(y) > 1
  have hx_norm_pos : 0 < Zsqrtd.norm x := by
    have h0 : 0 ≤ Zsqrtd.norm x := norm_nonneg' x
    rcases h0.eq_or_lt with heq | hpos
    · exfalso
      have hxz : x = 0 := (norm_eq_zero_iff' x).mp heq.symm
      -- If x = 0 then p = x * y = 0, but p > 0
      have : (p : ZsqrtNegTwo) = 0 := by rw [hxy, hxz, zero_mul]
      have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
      have : (p : ZsqrtNegTwo).re = 0 := by rw [this]; rfl
      simp only [Zsqrtd.natCast_re] at this
      omega
    · exact hpos
  have hy_norm_pos : 0 < Zsqrtd.norm y := by
    have h0 : 0 ≤ Zsqrtd.norm y := norm_nonneg' y
    rcases h0.eq_or_lt with heq | hpos
    · exfalso
      have hyz : y = 0 := (norm_eq_zero_iff' y).mp heq.symm
      -- If y = 0 then p = x * y = 0, but p > 0
      have : (p : ZsqrtNegTwo) = 0 := by rw [hxy, hyz, mul_zero]
      have hp_pos : (0 : ℤ) < p := by exact_mod_cast hp.out.pos
      have : (p : ZsqrtNegTwo).re = 0 := by rw [this]; rfl
      simp only [Zsqrtd.natCast_re] at this
      omega
    · exact hpos
  have hx_norm_ne_one : Zsqrtd.norm x ≠ 1 := by
    intro h; rw [isUnit_iff_norm_one] at hux; exact hux h
  have hy_norm_ne_one : Zsqrtd.norm y ≠ 1 := by
    intro h; rw [isUnit_iff_norm_one] at huy; exact huy h
  have hx_norm_gt_one : 1 < Zsqrtd.norm x := by omega
  have hy_norm_gt_one : 1 < Zsqrtd.norm y := by omega
  -- The only divisor of p² that is > 1 and < p² (since other factor > 1) is p
  have hdiv : Zsqrtd.norm x ∣ (p : ℤ) ^ 2 := by
    use Zsqrtd.norm y; exact hnorm_eq.symm
  have habs_div : (Zsqrtd.norm x).natAbs ∣ (p : ℕ) ^ 2 := by
    have : ((Zsqrtd.norm x).natAbs : ℤ) ∣ (p : ℤ) ^ 2 := by
      rw [Int.natAbs_dvd]; exact hdiv
    exact Int.natCast_dvd_natCast.mp this
  -- The divisors of p² for prime p are exactly {1, p, p²}
  have hp_pos : 0 < p := hp.out.pos
  have hdivisors : (Zsqrtd.norm x).natAbs = 1 ∨ (Zsqrtd.norm x).natAbs = p ∨ (Zsqrtd.norm x).natAbs = p ^ 2 := by
    -- Use the fact that for a prime p, divisors of p^2 are exactly 1, p, and p^2
    have hdvd_sq : (Zsqrtd.norm x).natAbs ∣ p ^ 2 := habs_div
    -- Write (Zsqrtd.norm x).natAbs = p^i for some i ≤ 2
    have hpow := (Nat.dvd_prime_pow hp.out).mp hdvd_sq
    obtain ⟨i, hi_le, hi_eq⟩ := hpow
    rcases i with _ | _ | _ | _
    · left; simp at hi_eq; exact hi_eq
    · right; left; simp at hi_eq; exact hi_eq
    · right; right; simp at hi_eq; exact hi_eq
    · omega
  have hnat_abs_pos : 0 < (Zsqrtd.norm x).natAbs := by
    rw [Int.natAbs_pos]; exact ne_of_gt hx_norm_pos
  have hne_one : (Zsqrtd.norm x).natAbs ≠ 1 := by
    intro h
    have : Zsqrtd.norm x = 1 := by
      have hnn := norm_nonneg' x
      omega
    exact hx_norm_ne_one this
  have hne_psq : (Zsqrtd.norm x).natAbs ≠ p ^ 2 := by
    intro h
    have hxabs : (Zsqrtd.norm x).natAbs = p ^ 2 := h
    have hx_int : Zsqrtd.norm x = (p : ℤ) ^ 2 := by
      have hnn := norm_nonneg' x
      have hcast : ((Zsqrtd.norm x).natAbs : ℤ) = Zsqrtd.norm x := Int.natAbs_of_nonneg hnn
      have : ((p : ℕ) ^ 2 : ℤ) = (p : ℤ) ^ 2 := by push_cast; ring
      rw [← hcast, hxabs]; exact this
    have hy_eq_one : Zsqrtd.norm y = 1 := by
      have h1 : (p : ℤ) ^ 2 * Zsqrtd.norm y = (p : ℤ) ^ 2 * 1 := by
        calc (p : ℤ) ^ 2 * Zsqrtd.norm y = Zsqrtd.norm x * Zsqrtd.norm y := by rw [hx_int]
          _ = (p : ℤ) ^ 2 := hnorm_eq
          _ = (p : ℤ) ^ 2 * 1 := by ring
      have hp2_ne : (p : ℤ) ^ 2 ≠ 0 := by positivity
      exact mul_left_cancel₀ hp2_ne h1
    exact hy_norm_ne_one hy_eq_one
  rcases hdivisors with h1 | hp1 | hp2
  · exact absurd h1 hne_one
  · -- N(x).natAbs = p, so N(x) = p (since N(x) > 0)
    have hx_norm_eq : Zsqrtd.norm x = p := by
      have hnn := norm_nonneg' x
      have hcast : ((Zsqrtd.norm x).natAbs : ℤ) = Zsqrtd.norm x := Int.natAbs_of_nonneg hnn
      rw [← hcast, hp1]
    -- Now x = a + b√-2 with a² + 2b² = p
    use x.re.natAbs, x.im.natAbs
    have h := hx_norm_eq
    rw [norm_def'] at h
    -- Need: x.re.natAbs² + 2 * x.im.natAbs² = p
    have hre_sq : (x.re.natAbs : ℤ) ^ 2 = x.re ^ 2 := Int.natAbs_sq x.re
    have him_sq : (x.im.natAbs : ℤ) ^ 2 = x.im ^ 2 := Int.natAbs_sq x.im
    have hint : (x.re.natAbs : ℤ) ^ 2 + 2 * (x.im.natAbs : ℤ) ^ 2 = p := by
      rw [hre_sq, him_sq]; exact h
    have hnat : (x.re.natAbs ^ 2 + 2 * x.im.natAbs ^ 2 : ℕ) = p := by
      have : ((x.re.natAbs ^ 2 + 2 * x.im.natAbs ^ 2 : ℕ) : ℤ) = (p : ℤ) := by
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        exact hint
      exact Int.ofNat_inj.mp this
    exact hnat
  · exact absurd hp2 hne_psq

end ZsqrtNegTwo

/-! ## Main Results on Primes p ≡ 3 (mod 8) -/

namespace SqAddTwoSq

open Zsqrtd

/-- The second supplementary law for -2: IsSquare(-2) when p % 8 = 3. -/
lemma neg_two_is_qr_of_three_mod_eight {p : ℕ} [Fact (Nat.Prime p)] (hmod : p % 8 = 3) :
    IsSquare (-2 : ZMod p) := by
  have hp2 : p ≠ 2 := by omega
  rw [ZMod.exists_sq_eq_neg_two_iff hp2]
  right; exact hmod

/-- The second supplementary law for -2: IsSquare(-2) when p % 8 = 1. -/
lemma neg_two_is_qr_of_one_mod_eight {p : ℕ} [Fact (Nat.Prime p)] (hmod : p % 8 = 1) :
    IsSquare (-2 : ZMod p) := by
  have hp2 : p ≠ 2 := by omega
  rw [ZMod.exists_sq_eq_neg_two_iff hp2]
  left; exact hmod

/-- p is not irreducible in ℤ[√-2] when -2 is a QR mod p. -/
lemma not_irreducible_of_neg_two_is_qr {p : ℕ} [hp : Fact (Nat.Prime p)]
    (h : IsSquare (-2 : ZMod p)) : ¬Irreducible (p : ZsqrtNegTwo) := by
  -- -2 is a QR mod p means ∃ c, c² ≡ -2 (mod p)
  obtain ⟨c, hc⟩ := h
  -- So p | c² + 2 = (c + √-2)(c - √-2) in ℤ[√-2]
  have hmod : c * c = -2 := hc.symm
  -- Lift c to an integer
  let c' : ℤ := c.val
  have hc'_mod : (c' : ZMod p) = c := by simp [c', ZMod.natCast_val]
  -- c² + 2 ≡ 0 (mod p)
  have hdiv_int : (p : ℤ) ∣ c' ^ 2 + 2 := by
    have h1 : ((c' ^ 2 + 2 : ℤ) : ZMod p) = 0 := by
      push_cast
      have hc'c : (c' : ZMod p) = c := hc'_mod
      rw [hc'c, sq, hmod]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (c' ^ 2 + 2) p).mp h1
  -- In ℤ[√-2]: c² + 2 = (c + √-2)(c - √-2), so p | (c + √-2)(c - √-2)
  let α : ZsqrtNegTwo := ⟨c', 1⟩   -- c + √-2
  let β : ZsqrtNegTwo := ⟨c', -1⟩  -- c - √-2
  have hprod : α * β = ⟨c' ^ 2 + 2, 0⟩ := by
    ext
    · simp only [α, β, Zsqrtd.re_mul]; ring
    · simp only [α, β, Zsqrtd.im_mul]; ring
  have hdiv_zsqrt : (p : ZsqrtNegTwo) ∣ α * β := by
    obtain ⟨k, hk⟩ := hdiv_int
    use ⟨k, 0⟩
    rw [hprod]
    ext
    · simp only [Zsqrtd.re_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast, hk]; ring
    · simp only [Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast]; ring
  -- If p were irreducible (hence prime in UFD), it would divide α or β
  intro hirr
  have hprime : Prime (p : ZsqrtNegTwo) := irreducible_iff_prime.mp hirr
  have hdiv_or : (p : ZsqrtNegTwo) ∣ α ∨ (p : ZsqrtNegTwo) ∣ β := hprime.dvd_or_dvd hdiv_zsqrt
  -- But p ∤ α and p ∤ β since their imaginary parts are ±1
  rcases hdiv_or with hdiv_α | hdiv_β
  · obtain ⟨q, hq⟩ := hdiv_α
    have him : α.im = ((p : ZsqrtNegTwo) * q).im := by rw [hq]
    simp only [α, Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast, mul_zero, zero_mul, add_zero] at him
    -- him : 1 = p * q.im
    have hdvd : (p : ℤ) ∣ 1 := ⟨q.im, by linarith⟩
    have hp1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
    have hp2 : 1 < (p : ℤ) := by exact_mod_cast hp.out.one_lt
    omega
  · obtain ⟨q, hq⟩ := hdiv_β
    have him : β.im = ((p : ZsqrtNegTwo) * q).im := by rw [hq]
    simp only [β, Zsqrtd.im_mul, Zsqrtd.re_natCast, Zsqrtd.im_natCast, mul_zero, zero_mul, add_zero] at him
    -- him : -1 = p * q.im
    have hdvd : (p : ℤ) ∣ -1 := ⟨q.im, by linarith⟩
    have hdvd1 : (p : ℤ) ∣ 1 := by
      have := Int.dvd_neg.mpr hdvd
      simp at this
      exact this
    have hp1 : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd1
    have hp2 : 1 < (p : ℤ) := by exact_mod_cast hp.out.one_lt
    omega

/-- If -2 is a quadratic residue mod p, then p = a² + 2b² for some a, b. -/
theorem sq_add_two_sq_of_prime {p : ℕ} [Fact (Nat.Prime p)] (h : IsSquare (-2 : ZMod p)) :
    ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = p := by
  have hirr := not_irreducible_of_neg_two_is_qr h
  obtain ⟨a, b, hab⟩ := ZsqrtNegTwo.sq_add_two_sq_of_nat_prime_of_not_irreducible p hirr
  refine ⟨a, b, ?_⟩
  have h1 : ((a ^ 2 + 2 * b ^ 2 : ℕ) : ℤ) = (p : ℤ) := by exact_mod_cast hab
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at h1
  exact h1

/-- Primes p ≡ 3 (mod 8) can be written as a² + 2b². -/
theorem sq_add_two_sq_of_prime_three_mod_eight {p : ℕ} [Fact (Nat.Prime p)] (hmod : p % 8 = 3) :
    ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = p := by
  have h := neg_two_is_qr_of_three_mod_eight hmod
  exact sq_add_two_sq_of_prime h

/-- Primes p ≡ 1 (mod 8) can be written as a² + 2b². -/
theorem sq_add_two_sq_of_prime_one_mod_eight {p : ℕ} [Fact (Nat.Prime p)] (hmod : p % 8 = 1) :
    ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = p := by
  have h := neg_two_is_qr_of_one_mod_eight hmod
  exact sq_add_two_sq_of_prime h

/-- If n = a² + 2b², then n = a² + b² + b². -/
theorem sq_add_two_sq_is_sum_three_sq {n : ℤ} {a b : ℤ} (h : a ^ 2 + 2 * b ^ 2 = n) :
    ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n := by
  use a, b, b
  linarith [sq_nonneg b]

/-- Primes p ≡ 3 (mod 8) are sums of three squares. -/
theorem prime_three_mod_eight_is_sum_three_sq' {p : ℕ} (hp : Nat.Prime p) (hmod : p % 8 = 3) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = p := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨a, b, hab⟩ := sq_add_two_sq_of_prime_three_mod_eight hmod
  exact sq_add_two_sq_is_sum_three_sq hab

/-! ## Examples -/

example : ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = 3 := ⟨1, 1, by norm_num⟩
example : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 3 := ⟨1, 1, 1, by norm_num⟩
example : ∃ a b : ℤ, a ^ 2 + 2 * b ^ 2 = 11 := ⟨3, 1, by norm_num⟩
example : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 11 := ⟨3, 1, 1, by norm_num⟩

end SqAddTwoSq
