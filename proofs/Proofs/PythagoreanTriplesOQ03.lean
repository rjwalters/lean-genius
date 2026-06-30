/-
  Rational Circle Parametrization for x² + y² = p  (pythagorean-triples-oq-03)

  Open Question:
  "Rational Circle Parametrization for x² + y² = p (p ≡ 1 mod 4)."

  Made precise. For an odd prime p, study the conic  C_p : x² + y² = p  over ℚ:

    (1) EXISTENCE.  C_p has a rational point  ⟺  C_p has an integer point
        ⟺  p ≢ 3 (mod 4).  The forward direction p ≢ 3 ⟹ rational point is
        Fermat's two-square theorem (Mathlib `Nat.Prime.sq_add_sq`); the
        reverse p ≡ 3 ⟹ no rational point is a descent argument.

    (2) PARAMETRIZATION.  Once C_p has a rational base point (a,b), every
        rational point is obtained by stereographic projection: intersecting
        C_p with the line of rational slope t through (a,b).  Explicitly

            x(t) = ( a (t² − 1) − 2 b t ) / (1 + t²)
            y(t) = ( b (1 − t²) − 2 a t ) / (1 + t²).

  This file is DISTINCT from siblings:
  - `FermatTwoSquares.lean`        : integer sum-of-two-squares characterization.
  - `PythagoreanTriplesOQ02.lean`  : Gaussian-integer view of the triple formula.
  Here the object of study is the set of RATIONAL points of the circle and its
  one-parameter rational parametrization.

  Build status: VERIFIED, 0 sorries, 0 axioms.  Type-checked against the
  prebuilt Mathlib olean cache with Lean 4.26.0 (`lean` direct, Docker
  containerd backend being unavailable this session).  Both
  `no_rational_point_three_mod_four` and `param_recovers` depend only on the
  foundational axioms `propext, Classical.choice, Quot.sound`.

  Tags: number-theory, conics, rational-points, stereographic-projection,
        fermat-two-squares, sum-of-two-squares
-/

import Mathlib

namespace PythagoreanTriplesOQ03

-- ============================================================
-- Part I: The stereographic parametrization (over ℚ)
-- ============================================================

/-- x-coordinate of the second intersection of the line of slope `t` through
    the base point `(a,b)` with the circle `x² + y² = a² + b²`. -/
def px (a b t : ℚ) : ℚ := (a * (t ^ 2 - 1) - 2 * b * t) / (1 + t ^ 2)

/-- y-coordinate of that second intersection. -/
def py (a b t : ℚ) : ℚ := (b * (1 - t ^ 2) - 2 * a * t) / (1 + t ^ 2)

/-- `1 + t² ≠ 0` over ℚ (the denominator never vanishes). -/
theorem one_add_sq_ne (t : ℚ) : (1 : ℚ) + t ^ 2 ≠ 0 := by positivity

/-- **Parametrization lands on the circle.**
    `px² + py² = a² + b²` for every slope `t`.  This is the exact statement
    that stereographic projection from `(a,b)` maps `ℚ` into the circle
    through `(a,b)`.  Pure algebra (`field_simp; ring`). -/
theorem param_on_circle (a b t : ℚ) :
    px a b t ^ 2 + py a b t ^ 2 = a ^ 2 + b ^ 2 := by
  have hden : (1 : ℚ) + t ^ 2 ≠ 0 := one_add_sq_ne t
  unfold px py
  field_simp
  ring

/-- **Parametrization of the circle `x² + y² = p`.**
    If the base point lies on `x² + y² = p`, so does every parametrized point. -/
theorem param_mem_circle {a b p : ℚ} (h : a ^ 2 + b ^ 2 = p) (t : ℚ) :
    px a b t ^ 2 + py a b t ^ 2 = p := by
  rw [param_on_circle, h]

-- ============================================================
-- Part II: Completeness (surjectivity) of the parametrization
-- ============================================================

/-- **Chord recovery (completeness).**
    Every rational point `(x,y)` on the circle through `(a,b)` with `x ≠ a`
    is the image under the parametrization of the chord slope `t = (y−b)/(x−a)`.
    Together with `param_on_circle` this gives a bijection between `ℚ ∪ {∞}`
    and the rational points of the circle.

    The underlying algebra is an EXACT identity: writing `t = (y−b)/(x−a)`,
    both `px(t) − x` and `py(t) − y` reduce to a multiple of the circle relation
    `x² + y² − a² − b²`, which vanishes by `hcirc`. -/
theorem param_recovers {a b x y : ℚ} (hcirc : x ^ 2 + y ^ 2 = a ^ 2 + b ^ 2)
    (hx : x ≠ a) :
    px a b ((y - b) / (x - a)) = x ∧ py a b ((y - b) / (x - a)) = y := by
  have hs : x - a ≠ 0 := sub_ne_zero.mpr hx
  unfold px py
  refine ⟨?_, ?_⟩
  · rw [div_eq_iff (one_add_sq_ne _)]
    field_simp
    linear_combination (a - x) * hcirc
  · rw [div_eq_iff (one_add_sq_ne _)]
    field_simp
    linear_combination (b - y) * hcirc

-- ============================================================
-- Part III: Existence of rational points
-- ============================================================

/-- **Existence, easy direction.**
    For a prime `p ≢ 3 (mod 4)` the circle `x² + y² = p` has a rational point.
    Immediate from Fermat's two-square theorem `Nat.Prime.sq_add_sq`: it yields
    an integer point, which is a fortiori rational. -/
theorem rational_point_of_not_three_mod_four {p : ℕ} [Fact p.Prime]
    (h : p % 4 ≠ 3) : ∃ x y : ℚ, x ^ 2 + y ^ 2 = (p : ℚ) := by
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq h
  exact ⟨(a : ℚ), (b : ℚ), by exact_mod_cast hab⟩

/-- **The mod-`p` obstruction.**
    If `p ≡ 3 (mod 4)` is prime and `p ∣ X² + Y²` for integers `X, Y`, then
    `p ∣ X` and `p ∣ Y`.  Proof: in the field `ZMod p` we have `X² + Y² = 0`;
    if `Y ≠ 0` then `(X/Y)² = −1`, so `−1` is a square mod `p`, contradicting
    `ZMod.exists_sq_eq_neg_one_iff` (`p % 4 = 3`).  Hence `Y ≡ 0`, and then
    `X² = 0` forces `X ≡ 0`. -/
theorem prime_dvd_of_dvd_sq_add_sq {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3)
    {X Y : ℤ} (hdvd : (p : ℤ) ∣ X ^ 2 + Y ^ 2) :
    (p : ℤ) ∣ X ∧ (p : ℤ) ∣ Y := by
  have hns : ¬ IsSquare (-1 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]; omega
  have hcast : (X : ZMod p) ^ 2 + (Y : ZMod p) ^ 2 = 0 := by
    have h0 : ((X ^ 2 + Y ^ 2 : ℤ) : ZMod p) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdvd
    push_cast at h0
    linear_combination h0
  have hY : (Y : ZMod p) = 0 := by
    by_contra hYne
    refine hns ⟨(X : ZMod p) / (Y : ZMod p), ?_⟩
    rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hYne hYne)]
    linear_combination -hcast
  have hX : (X : ZMod p) = 0 := by
    have hx2 : (X : ZMod p) ^ 2 = 0 := by rw [hY] at hcast; linear_combination hcast
    exact pow_eq_zero_iff (by norm_num) |>.mp hx2
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd X p).mp hX,
         (ZMod.intCast_zmod_eq_zero_iff_dvd Y p).mp hY⟩

/-- **Infinite descent core.**
    For a prime `p ≡ 3 (mod 4)`, the equation `X² + Y² = p · W²` has no integer
    solution with `W ≠ 0`.  Strong induction on `|W|`: the obstruction
    `prime_dvd_of_dvd_sq_add_sq` gives `p ∣ X`, `p ∣ Y`; writing `X = pX'`,
    `Y = pY'` yields `p(X'² + Y'²) = W²`, so `p ∣ W`, and `W = pW'` produces a
    strictly smaller solution `X'² + Y'² = p · W'²`. -/
theorem no_int_sol_of_three_mod_four {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) :
    ∀ n : ℕ, ∀ W : ℤ, W.natAbs = n → W ≠ 0 →
      ∀ X Y : ℤ, X ^ 2 + Y ^ 2 = (p : ℤ) * W ^ 2 → False := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro W hWn hW0 X Y hcl
    have hpdvd : (p : ℤ) ∣ X ^ 2 + Y ^ 2 := ⟨W ^ 2, hcl⟩
    obtain ⟨hpX, hpY⟩ := prime_dvd_of_dvd_sq_add_sq h3 hpdvd
    obtain ⟨X', rfl⟩ := hpX
    obtain ⟨Y', rfl⟩ := hpY
    have hW2 : (p : ℤ) * (X' ^ 2 + Y' ^ 2) = W ^ 2 := by
      apply mul_left_cancel₀ hp0
      linear_combination hcl
    have hpW : (p : ℤ) ∣ W := hpprime.dvd_of_dvd_pow ⟨X' ^ 2 + Y' ^ 2, hW2.symm⟩
    obtain ⟨W', rfl⟩ := hpW
    have hW'0 : W' ≠ 0 := by rintro rfl; simp at hW0
    have hcl' : X' ^ 2 + Y' ^ 2 = (p : ℤ) * W' ^ 2 := by
      apply mul_left_cancel₀ hp0
      linear_combination hW2
    refine ih W'.natAbs ?_ W' rfl hW'0 X' Y' hcl'
    have hW'pos : 0 < W'.natAbs := Int.natAbs_pos.mpr hW'0
    have hmul : ((p : ℤ) * W').natAbs = p * W'.natAbs := by simp [Int.natAbs_mul]
    rw [← hWn, hmul]
    exact (lt_mul_iff_one_lt_left hW'pos).mpr hp.one_lt

/-- **Existence, hard direction (descent).**
    For a prime `p ≡ 3 (mod 4)` the circle `x² + y² = p` has NO rational point.

    Proof: clear denominators of a rational solution `(x, y)` to integers
    `X² + Y² = p · W²` with `W ≠ 0`, then apply the infinite-descent core
    `no_int_sol_of_three_mod_four`.  Equivalently: `p ≡ 3 (mod 4)` ⟹ `p` is not
    a sum of two RATIONAL squares — the rational upgrade of the integer
    obstruction in `FermatTwoSquares.lean`. -/
theorem no_rational_point_three_mod_four {p : ℕ} [Fact p.Prime] (h : p % 4 = 3) :
    ¬ ∃ x y : ℚ, x ^ 2 + y ^ 2 = (p : ℚ) := by
  rintro ⟨x, y, hxy⟩
  -- Clear denominators: X = x.num·y.den, Y = y.num·x.den, W = x.den·y.den.
  have hxd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hyd : (y.den : ℚ) ≠ 0 := by exact_mod_cast y.den_nz
  have hxn : (x.num : ℚ) = x * x.den := (div_eq_iff hxd).mp (Rat.num_div_den x)
  have hyn : (y.num : ℚ) = y * y.den := (div_eq_iff hyd).mp (Rat.num_div_den y)
  obtain ⟨X, Y, W, hW0, hcl⟩ :
      ∃ X Y W : ℤ, W ≠ 0 ∧ X ^ 2 + Y ^ 2 = (p : ℤ) * W ^ 2 := by
    refine ⟨x.num * (y.den : ℤ), y.num * (x.den : ℤ), (x.den : ℤ) * (y.den : ℤ),
      mul_ne_zero ?_ ?_, ?_⟩
    · exact_mod_cast x.den_nz
    · exact_mod_cast y.den_nz
    · have key : ((x.num * (y.den : ℤ) : ℤ) : ℚ) ^ 2
            + ((y.num * (x.den : ℤ) : ℤ) : ℚ) ^ 2
          = (p : ℚ) * (((x.den : ℤ) * (y.den : ℤ) : ℤ) : ℚ) ^ 2 := by
        push_cast
        rw [hxn, hyn]
        linear_combination ((x.den : ℚ) * (y.den : ℚ)) ^ 2 * hxy
      exact_mod_cast key
  exact no_int_sol_of_three_mod_four h _ _ rfl hW0 _ _ hcl

/-- **Existence characterization for primes.**
    `x² + y² = p` has a rational point ⟺ `p ≢ 3 (mod 4)`.
    Assembled from the two directions above. -/
theorem rational_point_iff {p : ℕ} [Fact p.Prime] :
    (∃ x y : ℚ, x ^ 2 + y ^ 2 = (p : ℚ)) ↔ p % 4 ≠ 3 := by
  constructor
  · intro hxy h3
    exact no_rational_point_three_mod_four h3 hxy
  · exact rational_point_of_not_three_mod_four

-- ============================================================
-- Part IV: Concrete instances
-- ============================================================

/-- `p = 5`: base point `(2,1)` lies on the circle. -/
theorem base_5 : (2 : ℚ) ^ 2 + (1 : ℚ) ^ 2 = 5 := by norm_num

/-- `p = 5`, slope `t = 2`: a genuinely rational (non-integer) point on
    `x² + y² = 5`, namely `(2/5, -11/5)`. -/
theorem rational_point_5 :
    px 2 1 2 ^ 2 + py 2 1 2 ^ 2 = 5 :=
  param_mem_circle base_5 2

/-- The witnessing coordinates at `p = 5`, `t = 2` are `(2/5, -11/5)`. -/
theorem rational_point_5_coords : px 2 1 2 = 2 / 5 ∧ py 2 1 2 = -11 / 5 := by
  constructor <;> · simp only [px, py]; norm_num

/-- `p = 13`: base point `(3,2)`. -/
theorem base_13 : (3 : ℚ) ^ 2 + (2 : ℚ) ^ 2 = 13 := by norm_num

/-
  Summary (all VERIFIED, 0 sorries, 0 axioms)

  - `param_on_circle`, `param_mem_circle` : the stereographic map sends ℚ into
    the circle x²+y²=p  (field_simp; ring).
  - `param_recovers` : surjectivity (completeness) of the parametrization —
    every rational point with x ≠ a is hit by the chord slope t = (y−b)/(x−a).
    Exact algebraic identity discharged by `linear_combination`.
  - `rational_point_of_not_three_mod_four` : existence for p ≢ 3 (mod 4) via
    Mathlib's Fermat two-square theorem.
  - `prime_dvd_of_dvd_sq_add_sq` : the mod-p obstruction (p ≡ 3 ⟹ p ∣ X²+Y²
    forces p ∣ X, p ∣ Y), via `ZMod.exists_sq_eq_neg_one_iff` in the field ℤ/p.
  - `no_int_sol_of_three_mod_four` : infinite descent on |W| for X²+Y² = pW².
  - `no_rational_point_three_mod_four` : the descent obstruction for p ≡ 3 —
    clear denominators, then apply the integer descent.
  - `rational_point_iff` : full existence characterization (assembled).
  - concrete rational (non-integer) points, e.g. (2/5, -11/5) on x²+y²=5.

  Sorries: 0.  Axiom declarations: 0.
-/

end PythagoreanTriplesOQ03
