/-
  Aristotle targets for Erdos437 (Square Partial Products)
  Routine supporting lemmas for automated proof search.
  See Erdos437Problem.lean for the main formalization.

  13 of 15 sorries proved manually:
  - IsSquare helpers (4): ⟨2^k, ring⟩, obtain + ring, ring, Nat.one_le_pow
  - Division arithmetic (4): le_div_iff/div_le_iff + linarith, Nat.cast_pos, div_le_one_of_le
  - u/exp/sqrt helpers (5): sqrt_nonneg, exp_le_exp.mpr, exp_lt_one_iff.mpr, sqrt_pos_of_pos, div_lt_iff + ring

  2 sorries remain for Aristotle:
  - partial_product_cons: complex List.foldl identity (non-trivial associativity)
  - pow_four_range_product: complex inductive list product formula
-/
import Mathlib

open Real Nat Finset

namespace Erdos437.Aristotle

/-
  ## Section 1: IsSquare Helpers
-/

/-- 4^k is a perfect square (= (2^k)^2) -/
lemma isSquare_pow_four (k : ℕ) : IsSquare (4 ^ k) :=
  ⟨2 ^ k, by ring⟩

/-- Product of two squares is a square -/
lemma isSquare_mul (a b : ℕ) (ha : IsSquare a) (hb : IsSquare b) : IsSquare (a * b) := by
  obtain ⟨m, hm⟩ := ha; obtain ⟨n, hn⟩ := hb
  exact ⟨m * n, by rw [hm, hn]; ring⟩

/-- 4^i * 4^j = 4^(i+j) -/
lemma pow_four_mul (i j : ℕ) : 4 ^ i * 4 ^ j = 4 ^ (i + j) := by ring

/-- 4^k ≥ 1 for all k -/
lemma pow_four_pos (k : ℕ) : 4 ^ k ≥ 1 :=
  Nat.one_le_pow k 4 (by norm_num)

/-
  ## Section 2: List Partial Products
-/

/-- Helper: foldl (·*·) with non-unit accumulator factors out the accumulator. -/
private lemma foldl_mul_acc (xs : List ℕ) (acc : ℕ) :
    xs.foldl (· * ·) acc = acc * xs.foldl (· * ·) 1 := by
  induction xs generalizing acc with
  | nil => simp
  | cons h t ih =>
    simp only [List.foldl_cons]
    rw [ih (acc * h), ih h]
    ring

/-- Partial product of a list is the product of the first k elements -/
lemma partial_product_cons (a : ℕ) (as : List ℕ) :
    (a :: as).foldl (· * ·) 1 = a * as.foldl (· * ·) 1 := by
  simp only [List.foldl_cons, one_mul]
  exact foldl_mul_acc as a

/-- The product of List.range k mapped to 4^(i+1) is 4^(k*(k+1)/2) -/
lemma pow_four_range_product (k : ℕ) :
    (List.range k).foldl (fun acc i => acc * 4 ^ (i + 1)) 1 =
    4 ^ (k * (k + 1) / 2) := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [ih, ← pow_add]
    congr 1
    -- Goal: n * (n + 1) / 2 + (n + 1) = (n + 1) * (n + 2) / 2
    have heven : 2 ∣ n * (n + 1) := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨m * (n + 1), by subst hm; ring⟩
      · exact ⟨n * (m + 1), by subst hm; ring⟩
    have heven2 : 2 ∣ (n + 1) * (n + 2) := by
      rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · exact ⟨(n + 1) * (m + 1), by subst hm; ring⟩
      · exact ⟨(m + 1) * (n + 2), by subst hm; ring⟩
    linarith [Nat.div_mul_cancel heven, Nat.div_mul_cancel heven2,
              show n * (n + 1) + 2 * (n + 1) = (n + 1) * (n + 2) from by ring]

/-
  ## Section 3: Division Arithmetic for L(x)/x
-/

/-- If a ≥ x * c and x > 0, then a / x ≥ c for reals -/
lemma div_ge_of_ge_mul (a x c : ℝ) (hx : x > 0) (h : a ≥ x * c) : a / x ≥ c :=
  (le_div_iff hx).mpr (by linarith)

/-- If a ≤ x * c and x > 0, then a / x ≤ c for reals -/
lemma div_le_of_le_mul (a x c : ℝ) (hx : x > 0) (h : a ≤ x * c) : a / x ≤ c :=
  (div_le_iff hx).mpr (by linarith)

/-- x > 0 as real when x ≥ 1 as natural -/
lemma cast_pos_of_ge_one (x : ℕ) (hx : x ≥ 1) : (x : ℝ) > 0 :=
  Nat.cast_pos.mpr (by omega)

/-- (L x : ℝ) / x is in [0, 1] when L x ≤ x -/
lemma div_L_le_one (L x : ℕ) (h : L ≤ x) (hx : x ≥ 1) : (L : ℝ) / x ≤ 1 :=
  div_le_one_of_le (by exact_mod_cast h) (by exact_mod_cast (show 0 ≤ x from by omega))

/-
  ## Section 4: u(x) = sqrt(log x * log log x) Properties
-/

/-- u(x) ≥ 0 for x ≥ 2 -/
lemma u_nonneg (x : ℕ) (hx : x ≥ 2) :
    Real.sqrt (Real.log x * Real.log (Real.log x)) ≥ 0 :=
  Real.sqrt_nonneg _

/-- Real.exp is monotone -/
lemma exp_mono (a b : ℝ) (h : a ≤ b) : Real.exp a ≤ Real.exp b :=
  Real.exp_le_exp.mpr h

/-- For c > 0 and u > 0, exp(-c * u) < 1 -/
lemma exp_neg_lt_one (c u : ℝ) (hc : c > 0) (hu : u > 0) : Real.exp (-(c * u)) < 1 :=
  Real.exp_lt_one_iff.mpr (by nlinarith [mul_pos hc hu])

/-- sqrt 2 > 0 -/
lemma sqrt_two_pos : Real.sqrt 2 > 0 :=
  Real.sqrt_pos_of_pos (by norm_num)

/-- 1 / sqrt 2 < sqrt 2 -/
lemma inv_sqrt_two_lt_sqrt_two : 1 / Real.sqrt 2 < Real.sqrt 2 := by
  have hpos : Real.sqrt 2 > 0 := Real.sqrt_pos_of_pos (by norm_num)
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [div_lt_iff hpos, h2]; norm_num

end Erdos437.Aristotle
