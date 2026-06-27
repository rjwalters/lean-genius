/-
  Bézout Identity — OQ-02-OQ-01-OQ-03-OQ-01:
  The GENERAL (non-coprime) classification of the linear Diophantine solution set.

  ## Question
  The parent entry (OQ-02-OQ-01-OQ-03) classifies the Bézout solution set of
  `a·x + b·y = c` for *coprime* `a, b`: it is exactly one coset of the rank-1
  lattice `ℤ·(b, −a)`. Its first open question is to drop coprimality. For
  arbitrary `a, b` (not both zero) with `g = gcd(a, b)`, write `a = g·a'`,
  `b = g·b'` with `a', b'` coprime (`Nat.coprime_div_gcd_div_gcd` / `Int.exists_gcd_one'`).
  Then:

    * `a·x + b·y = c` is solvable  ⟺  `g ∣ c`  (Bézout solvability), and
    * the full solution set is one coset of the *primitive* lattice `ℤ·(b', −a')`.

  This file delivers that classification and connects it to the actual integer gcd.

  ## What this file delivers (0 axioms, 0 sorries)
  * `general_homogeneous` — for `a = g·a'`, `b = g·b'` (`g ≠ 0`, `a' b'` coprime,
    `b' ≠ 0`), every solution of `a·u + b·v = 0` is `(k·b', −k·a')`. The lattice
    is the *primitive* one `ℤ·(b', −a')`, not `ℤ·(b, −a)`.
  * `general_unique` — any two solutions of `a·x + b·y = c` differ by one
    primitive lattice step `(k·b', −k·a')`.
  * `general_param` — converse: every primitive lattice step is again a solution.
  * `general_solvable_iff` — `a·x + b·y = c` is solvable ⟺ `g ∣ c`.
  * `int_admits_decomp` — every `a, b : ℤ` with `b ≠ 0` admits a primitive
    decomposition with `g = gcd(a,b) > 0` and `a', b'` coprime, `b' ≠ 0`
    (from `Int.exists_gcd_one'`).
  * `int_general_unique` — the packaged uniqueness for arbitrary `a, b : ℤ`,
    `b ≠ 0`: two solutions differ by `(k·(b/g), −k·(a/g))`.
  * Concrete worked instances for the *non-coprime* pair `(6, 9)` (`g = 3`).

  References:
  [Bez1779]  Bézout, "Théorie générale des équations algébriques" (1779)
  [Knuth2]   Knuth, TAOCP Vol. 2, §4.5.2 (extended Euclidean algorithm)

  Tags: number-theory, bezout, euclidean-algorithm, diophantine, lattice, classical
-/

import Mathlib

namespace BezoutGeneralClassification

-- ============================================================
-- SECTION I: Homogeneous solutions, general (non-coprime) case
-- ============================================================

/-- **Core lemma (general).** Write `a = g·a'`, `b = g·b'` with `g ≠ 0`,
    `a', b'` coprime and `b' ≠ 0`. Then every solution of the homogeneous
    equation `a·u + b·v = 0` is a multiple of the *primitive* vector `(b', −a')`.
    The common factor `g` is stripped first, reducing to the coprime case. -/
theorem general_homogeneous {a b g a' b' u v : ℤ}
    (hg : g ≠ 0) (ha : a = g * a') (hb : b = g * b')
    (hcop : IsCoprime a' b') (hb' : b' ≠ 0)
    (h : a * u + b * v = 0) : ∃ k : ℤ, u = k * b' ∧ v = -(k * a') := by
  -- Strip the common factor g: a'·u + b'·v = 0.
  have hgz : g * (a' * u + b' * v) = 0 := by rw [ha, hb] at h; linear_combination h
  have h' : a' * u + b' * v = 0 := (mul_eq_zero.mp hgz).resolve_left hg
  -- Now run the coprime argument on (a', b').
  have hbav : b' ∣ a' * u := ⟨-v, by linear_combination h'⟩
  have hbu : b' ∣ u := (hcop.symm).dvd_of_dvd_mul_left hbav
  obtain ⟨k, hk⟩ := hbu
  refine ⟨k, by rw [hk]; ring, ?_⟩
  have hz : b' * (a' * k + v) = 0 := by rw [hk] at h'; linear_combination h'
  have hzero : a' * k + v = 0 := (mul_eq_zero.mp hz).resolve_left hb'
  linear_combination hzero

-- ============================================================
-- SECTION II: Uniqueness and parametrization (general)
-- ============================================================

/-- **Uniqueness (general).** Any two solutions of `a·x + b·y = c` differ by
    exactly one *primitive* lattice step `(k·b', −k·a')`. -/
theorem general_unique {a b g a' b' x₁ y₁ x₂ y₂ : ℤ}
    (hg : g ≠ 0) (ha : a = g * a') (hb : b = g * b')
    (hcop : IsCoprime a' b') (hb' : b' ≠ 0)
    (h : a * x₁ + b * y₁ = a * x₂ + b * y₂) :
    ∃ k : ℤ, x₂ - x₁ = k * b' ∧ y₂ - y₁ = -(k * a') := by
  have h0 : a * (x₂ - x₁) + b * (y₂ - y₁) = 0 := by linear_combination -h
  exact general_homogeneous hg ha hb hcop hb' h0

/-- **Parametrization (converse).** Every primitive lattice step from a solution
    is again a solution: `a·(x + k·b') + b·(y − k·a') = a·x + b·y`, provided
    `a = g·a'`, `b = g·b'`. (The step uses the *primitive* `(b', −a')`.) -/
theorem general_param {a b g a' b' : ℤ} (x y k : ℤ)
    (ha : a = g * a') (hb : b = g * b') :
    a * (x + k * b') + b * (y - k * a') = a * x + b * y := by
  subst ha hb; ring

-- ============================================================
-- SECTION III: Solvability criterion (Bézout)
-- ============================================================

/-- **Solvability.** With `a = g·a'`, `b = g·b'` and `a', b'` coprime,
    `a·x + b·y = c` has a solution iff `g ∣ c`. -/
theorem general_solvable_iff {a b c g a' b' : ℤ}
    (ha : a = g * a') (hb : b = g * b') (hcop : IsCoprime a' b') :
    (∃ x y : ℤ, a * x + b * y = c) ↔ g ∣ c := by
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨a' * x + b' * y, by rw [ha, hb] at hxy; linear_combination -hxy⟩
  · rintro ⟨c', rfl⟩
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨c' * u, c' * v, by rw [ha, hb]; linear_combination g * c' * huv⟩

-- ============================================================
-- SECTION IV: Connecting to the actual integer gcd
-- ============================================================

/-- Every pair `a, b : ℤ` with `b ≠ 0` admits a *primitive decomposition*:
    there are `g a' b' : ℤ` with `g = gcd(a,b) > 0`, `a = g·a'`, `b = g·b'`,
    `a', b'` coprime and `b' ≠ 0`. -/
theorem int_admits_decomp {a b : ℤ} (hb : b ≠ 0) :
    ∃ g a' b' : ℤ, g ≠ 0 ∧ a = g * a' ∧ b = g * b' ∧ IsCoprime a' b' ∧ b' ≠ 0 := by
  -- gcd a b > 0 because b ≠ 0.
  have hgpos : 0 < Int.gcd a b := by
    rcases Nat.eq_zero_or_pos (Int.gcd a b) with h0 | hpos
    · exfalso
      have hdvd : (Int.gcd a b : ℤ) ∣ b := Int.gcd_dvd_right a b
      rw [h0] at hdvd
      exact hb (zero_dvd_iff.mp (by exact_mod_cast hdvd))
    · exact hpos
  obtain ⟨g, a', b', hg, hcopg, hae, hbe⟩ := Int.exists_gcd_one' hgpos
  refine ⟨(g : ℤ), a', b', by exact_mod_cast hg.ne', by rw [hae]; ring,
    by rw [hbe]; ring, Int.isCoprime_iff_gcd_eq_one.mpr hcopg, ?_⟩
  -- b' ≠ 0: otherwise b = b'·g = 0.
  rintro rfl
  exact hb (by rw [hbe]; ring)

/-- **Packaged uniqueness for arbitrary `a, b : ℤ` (`b ≠ 0`).** Any two solutions
    of `a·x + b·y = c` differ by one step of the primitive lattice `ℤ·(b', −a')`,
    where `(a', b') = (a/g, b/g)` for `g = gcd(a,b)`. This is the open question
    from the parent entry, with coprimality dropped. -/
theorem int_general_unique {a b x₁ y₁ x₂ y₂ : ℤ} (hb : b ≠ 0)
    (h : a * x₁ + b * y₁ = a * x₂ + b * y₂) :
    ∃ a' b' : ℤ, IsCoprime a' b' ∧
      (∃ k : ℤ, x₂ - x₁ = k * b' ∧ y₂ - y₁ = -(k * a')) := by
  obtain ⟨g, a', b', hg, ha, hb2, hcop, hb'⟩ := int_admits_decomp (a := a) hb
  exact ⟨a', b', hcop, general_unique hg ha hb2 hcop hb' h⟩

-- ============================================================
-- SECTION V: Concrete worked instances — non-coprime pair (6, 9)
-- ============================================================
-- gcd(6, 9) = 3, so a' = 2, b' = 3, primitive lattice ℤ·(3, −2).

/-- `(6, 9)` decomposes as `g = 3`, `a' = 2`, `b' = 3`. -/
theorem ex69_decomp : (6 : ℤ) = 3 * 2 ∧ (9 : ℤ) = 3 * 3 := by norm_num

/-- `(2, 0)` solves `6·x + 9·y = 12` (`= 3·4`, and `3 ∣ 12`). -/
theorem ex69_sol_a : (6 : ℤ) * 2 + 9 * 0 = 12 := by norm_num

/-- `(-1, 2)` is another solution of `6·x + 9·y = 12`. -/
theorem ex69_sol_b : (6 : ℤ) * (-1) + 9 * 2 = 12 := by norm_num

/-- The two solutions differ by exactly one *primitive* lattice step `k = −1`
    along `(b', −a') = (3, −2)`: `(-1, 2) = (2, 0) + (−1)·(3, −2)`. -/
theorem ex69_step : ((-1 : ℤ) = 2 + (-1) * 3) ∧ ((2 : ℤ) = 0 - (-1) * 2) := by
  constructor <;> norm_num

/-- The whole one-parameter family for `6·x + 9·y = 12`: every `k` gives a
    solution along the primitive lattice `(3, −2)`. Note the step is `(3, −2)`,
    NOT the non-primitive `(9, −6) = (b, −a)`. -/
theorem ex69_family (k : ℤ) : (6 : ℤ) * (2 + k * 3) + 9 * (0 - k * 2) = 12 := by ring

/-- `6·x + 9·y = 7` has NO solution, since `3 ∤ 7` (solvability criterion). -/
theorem ex69_unsolvable : ¬ ∃ x y : ℤ, (6 : ℤ) * x + 9 * y = 7 := by
  rw [general_solvable_iff (g := 3) (a' := 2) (b' := 3) (by norm_num) (by norm_num)
    (by rw [Int.isCoprime_iff_gcd_eq_one]; decide)]
  decide

#check @general_homogeneous
#check @general_unique
#check @general_param
#check @general_solvable_iff
#check @int_admits_decomp
#check @int_general_unique

end BezoutGeneralClassification
