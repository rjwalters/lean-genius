/-
  Bézout Identity — OQ-02-OQ-01-OQ-03:
  Constructive Bézout coefficients via the extended Euclidean algorithm,
  and their uniqueness modulo the homogeneous lattice.

  ## Question
  The parent line develops Bézout's identity and its consequences (Euclid's
  Lemma, the Fundamental Theorem of Arithmetic). Bézout's identity asserts the
  *existence* of integers s, t with  a · s + b · t = gcd(a, b).

  Mathlib's extended Euclidean algorithm (`Nat.gcdA`, `Nat.gcdB`) produces one
  concrete such pair. But the coefficients are NOT unique: if (s, t) works, so
  does (s + k·(b/g), t − k·(a/g)) for every integer k. This file settles the
  converse — the *uniqueness* / classification: those are the ONLY pairs, so the
  solution set of a·x + b·y = g is exactly one coset of the lattice ℤ·(b/g, −a/g).

  ## What this file delivers (0 axioms, 0 sorries)
  * `bezout_identity` — extended-gcd Bézout identity over ℤ (from `Nat.gcd_eq_gcd_ab`).
  * `coprime_homogeneous` — core lemma: for coprime a, b (b ≠ 0), every solution
    of a·u + b·v = 0 is u = k·b, v = −(k·a).
  * `coprime_bezout_unique` — uniqueness: two solutions of a·x + b·y = c differ by
    one lattice step (k·b, −k·a).
  * `coprime_bezout_param` — converse: every lattice step is again a solution.
  * `gcdA_gcdB_unique` — the extended-Euclid coefficients (gcdA, gcdB) are unique
    modulo (b, −a) for coprime a, b.
  * Concrete worked instances for the coprime pair (3, 5).

  References:
  [Bez1779]  Bézout, "Théorie générale des équations algébriques" (1779)
  [Knuth2]   Knuth, TAOCP Vol. 2, §4.5.2 (extended Euclidean algorithm)

  Tags: number-theory, bezout, euclidean-algorithm, diophantine, classical
-/

import Mathlib

namespace BezoutExtGcdUnique

-- ============================================================
-- SECTION I: Existence — the extended-Euclid Bézout identity
-- ============================================================

/-- Bézout's identity from Mathlib's extended Euclidean coefficients
    `Nat.gcdA`, `Nat.gcdB`: over ℤ, `gcd a b = a · gcdA a b + b · gcdB a b`. -/
theorem bezout_identity (a b : ℕ) :
    (Nat.gcd a b : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b :=
  Nat.gcd_eq_gcd_ab a b

-- ============================================================
-- SECTION II: Homogeneous solutions for coprime a, b
-- ============================================================

/-- **Core lemma.** For coprime integers `a, b` with `b ≠ 0`, every solution of
    the homogeneous equation `a·u + b·v = 0` is a lattice multiple of `(b, −a)`. -/
theorem coprime_homogeneous {a b u v : ℤ} (hab : IsCoprime a b) (hb : b ≠ 0)
    (h : a * u + b * v = 0) : ∃ k : ℤ, u = k * b ∧ v = -(k * a) := by
  have hbav : b ∣ a * u := ⟨-v, by linear_combination h⟩
  have hbu : b ∣ u := (hab.symm).dvd_of_dvd_mul_left hbav
  obtain ⟨k, hk⟩ := hbu
  refine ⟨k, by rw [hk]; ring, ?_⟩
  have hz : b * (a * k + v) = 0 := by rw [hk] at h; linear_combination h
  have hzero : a * k + v = 0 := (mul_eq_zero.mp hz).resolve_left hb
  linear_combination hzero

-- ============================================================
-- SECTION III: Uniqueness and parametrization
-- ============================================================

/-- **Uniqueness.** For coprime `a, b` with `b ≠ 0`, any two solutions of
    `a·x + b·y = c` differ by exactly one lattice step `(k·b, −k·a)`. -/
theorem coprime_bezout_unique {a b x₁ y₁ x₂ y₂ : ℤ} (hab : IsCoprime a b)
    (hb : b ≠ 0) (h : a * x₁ + b * y₁ = a * x₂ + b * y₂) :
    ∃ k : ℤ, x₂ - x₁ = k * b ∧ y₂ - y₁ = -(k * a) := by
  have h0 : a * (x₂ - x₁) + b * (y₂ - y₁) = 0 := by linear_combination -h
  exact coprime_homogeneous hab hb h0

/-- **Parametrization (converse).** Every lattice step from a solution is again
    a solution: `a·(x + k·b) + b·(y − k·a) = a·x + b·y`. -/
theorem coprime_bezout_param (a b x y k : ℤ) :
    a * (x + k * b) + b * (y - k * a) = a * x + b * y := by ring

-- ============================================================
-- SECTION IV: Specialization to the extended-Euclid coefficients
-- ============================================================

/-- For coprime naturals `a, b` with `b ≠ 0`, the extended-Euclid coefficients
    `(gcdA a b, gcdB a b)` are unique modulo `(b, −a)`. -/
theorem gcdA_gcdB_unique {a b : ℕ} (hab : Nat.Coprime a b) (hb : b ≠ 0)
    {x y : ℤ} (h : (a : ℤ) * x + b * y = 1) :
    ∃ k : ℤ, x - Nat.gcdA a b = k * b ∧ y - Nat.gcdB a b = -(k * a) := by
  have hcop : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
  have hb' : (b : ℤ) ≠ 0 := by exact_mod_cast hb
  have hg : (a : ℤ) * Nat.gcdA a b + b * Nat.gcdB a b = 1 := by
    have hbez := Nat.gcd_eq_gcd_ab a b
    rw [hab.gcd_eq_one] at hbez
    exact_mod_cast hbez.symm
  exact coprime_bezout_unique hcop hb' (by rw [hg, h])

-- ============================================================
-- SECTION V: Concrete worked instances (coprime pair 3, 5)
-- ============================================================

/-- `(2, −1)` is a Bézout pair for `(3, 5)`: `3·2 + 5·(−1) = 1`. -/
theorem ex35_a : (3 : ℤ) * 2 + 5 * (-1) = 1 := by norm_num

/-- `(−3, 2)` is another Bézout pair for `(3, 5)`: `3·(−3) + 5·2 = 1`. -/
theorem ex35_b : (3 : ℤ) * (-3) + 5 * 2 = 1 := by norm_num

/-- The two pairs differ by exactly one lattice step `k = −1`. -/
theorem ex35_step : ((-3 : ℤ) = 2 + (-1) * 5) ∧ ((2 : ℤ) = -1 - (-1) * 3) := by
  constructor <;> norm_num

/-- The whole one-parameter family for `(3, 5)`: every `k` gives a solution. -/
theorem ex35_family (k : ℤ) : (3 : ℤ) * (2 + k * 5) + 5 * (-1 - k * 3) = 1 := by
  ring

-- ============================================================
-- SECTION VI: General (non-coprime) classification
-- ============================================================

/-
The sections above settle the *coprime* case (`g = gcd a b = 1`), where the lattice is
`ℤ·(b, −a)`.  The file's headline claim, however, is the full classification: for general
`a, b` the solution set of `a·x + b·y = c` is one coset of `ℤ·(b/g, −a/g)`.  This section
discharges that general statement.

We parametrize by the reduced pair: write `a = g·a'`, `b = g·b'` with `a', b'` coprime
(so `a' = a/g`, `b' = b/g`) and `g ≠ 0`.  The canonical instance is `g = gcd a b`, but the
results hold for *any* such common-factor decomposition.  Each general theorem reduces to
its coprime counterpart by cancelling the common factor `g` (legitimate since `g ≠ 0`).
-/

/-- **General homogeneous solutions.**  With `a = g·a'`, `b = g·b'`, `a', b'` coprime,
`g ≠ 0`, `b' ≠ 0`, every solution of `a·u + b·v = 0` is a lattice multiple of
`(b', −a') = (b/g, −a/g)`.  Reduces to `coprime_homogeneous` after cancelling `g`. -/
theorem general_homogeneous {g a' b' u v : ℤ} (hab : IsCoprime a' b') (hg : g ≠ 0)
    (hb' : b' ≠ 0) (h : (g * a') * u + (g * b') * v = 0) :
    ∃ k : ℤ, u = k * b' ∧ v = -(k * a') := by
  have hcancel : g * (a' * u + b' * v) = 0 := by linear_combination h
  have h' : a' * u + b' * v = 0 := (mul_eq_zero.mp hcancel).resolve_left hg
  exact coprime_homogeneous hab hb' h'

/-- **General uniqueness.**  For `a = g·a'`, `b = g·b'` with `a', b'` coprime, `g ≠ 0`,
`b' ≠ 0`, any two solutions of `a·x + b·y = c` differ by one lattice step
`(k·(b/g), −k·(a/g))`. -/
theorem general_bezout_unique {g a' b' x₁ y₁ x₂ y₂ : ℤ} (hab : IsCoprime a' b')
    (hg : g ≠ 0) (hb' : b' ≠ 0)
    (h : (g * a') * x₁ + (g * b') * y₁ = (g * a') * x₂ + (g * b') * y₂) :
    ∃ k : ℤ, x₂ - x₁ = k * b' ∧ y₂ - y₁ = -(k * a') := by
  have h0 : (g * a') * (x₂ - x₁) + (g * b') * (y₂ - y₁) = 0 := by linear_combination -h
  exact general_homogeneous hab hg hb' h0

/-- **General parametrization (converse).**  Every lattice step `(k·(b/g), −k·(a/g))` from
a solution is again a solution, for any `a = g·a'`, `b = g·b'`. -/
theorem general_bezout_param (g a' b' x y k : ℤ) :
    (g * a') * (x + k * b') + (g * b') * (y - k * a') = (g * a') * x + (g * b') * y := by
  ring

/-- **General solvability (existence).**  If `g ∣ c` (write `c = g·c'`) then with
`a = g·a'`, `b = g·b'` and `a', b'` coprime the equation `a·x + b·y = c` has a solution,
namely `(c'·s, c'·t)` for a coprime Bézout pair `a'·s + b'·t = 1`.  Together with
`general_bezout_unique` this is the complete classification: solvable iff `g ∣ c`, and the
solution set is exactly one coset of `ℤ·(b/g, −a/g)`. -/
theorem general_solvable {g a' b' c c' : ℤ} (hab : IsCoprime a' b') (hc : c = g * c') :
    ∃ x y : ℤ, (g * a') * x + (g * b') * y = c := by
  obtain ⟨s, t, hst⟩ := hab
  exact ⟨c' * s, c' * t, by subst hc; linear_combination (g * c') * hst⟩

-- General worked instance: a = 6, b = 9, g = 3, a' = 2, b' = 3, equation 6x + 9y = 3.

/-- `(−1, 1)` solves `6x + 9y = 3`. -/
theorem ex69_a : (6 : ℤ) * (-1) + 9 * 1 = 3 := by norm_num

/-- One lattice step `k = 1` (lattice `(b/g, −a/g) = (3, −2)`) gives another solution. -/
theorem ex69_step : (6 : ℤ) * (-1 + 1 * 3) + 9 * (1 - 1 * 2) = 3 := by norm_num

/-- The whole one-parameter family for `6x + 9y = 3`: every `k` gives a solution. -/
theorem ex69_family (k : ℤ) : (6 : ℤ) * (-1 + k * 3) + 9 * (1 - k * 2) = 3 := by ring

-- ============================================================
-- SECTION VII: The canonical (reduced) Bézout representative
-- ============================================================

/-- **Canonical Bézout coefficient.**  For coprime `a, b` with `b > 0`, the solution set
of `a·x + b·y = c` — a coset of the lattice `ℤ·(b, −a)` — contains a *unique* member whose
`x`-coordinate is reduced modulo `b`, i.e. `0 ≤ x < b`.  This is the canonical
representative of the Bézout pair (the `x` is the modular inverse data `c·a⁻¹ mod b` when
`c = 1`).  Existence: reduce any `x₀` to `x₀ % b`.  Uniqueness: two reduced `x`-coordinates
differ by a multiple of `b` (by `coprime_bezout_unique`) yet both lie in `[0, b)`, forcing
equality.  This answers the second open question of the entry: the lattice coset has a
distinguished minimal representative. -/
theorem coprime_bezout_canonical {a b c : ℤ} (hab : IsCoprime a b) (hb : 0 < b)
    (x₀ y₀ : ℤ) (h₀ : a * x₀ + b * y₀ = c) :
    ∃! x : ℤ, (0 ≤ x ∧ x < b) ∧ ∃ y : ℤ, a * x + b * y = c := by
  have hb0 : b ≠ 0 := ne_of_gt hb
  refine ⟨x₀ % b, ⟨⟨Int.emod_nonneg x₀ hb0, Int.emod_lt_of_pos x₀ hb⟩,
      ⟨y₀ + a * (x₀ / b), ?_⟩⟩, ?_⟩
  · -- existence: `x₀ % b` keeps the equation solvable
    rw [Int.emod_def]
    linear_combination h₀
  · -- uniqueness: any reduced solution coincides with `x₀ % b`
    rintro x ⟨⟨hx0, hxb⟩, y, hxy⟩
    obtain ⟨k, hk, -⟩ := coprime_bezout_unique hab hb0
      (show a * x + b * y = a * x₀ + b * y₀ by rw [hxy, h₀])
    have hmod : x % b = x₀ % b := by
      conv_rhs => rw [show x₀ = x + b * k by linear_combination hk]
      rw [Int.add_mul_emod_self_left]
    rwa [Int.emod_eq_of_lt hx0 hxb] at hmod

/-- `x = 2` is the canonical Bézout `x`-coordinate for `(3, 5)` with `c = 1`:
    `0 ≤ 2 < 5` and `3·2 + 5·(−1) = 1`. -/
theorem ex35_canonical :
    (0 : ℤ) ≤ 2 ∧ (2 : ℤ) < 5 ∧ (3 : ℤ) * 2 + 5 * (-1) = 1 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

#check @coprime_homogeneous
#check @coprime_bezout_unique
#check @coprime_bezout_param
#check @gcdA_gcdB_unique
#check @general_homogeneous
#check @general_bezout_unique
#check @general_bezout_param
#check @general_solvable
#check @coprime_bezout_canonical

end BezoutExtGcdUnique
