import Proofs.Erdos85DifferenceArrayBoundary

/-!
# Arithmetic of the diagonal-anchor surplus

If the parity refinement of the symmetric difference array is written as
`r = d + 3 - 4a`, the boundary divisibility has a small quadratic remainder.
This file isolates that calculation without enumerating cycle lengths.
-/

namespace Erdos85

/-- The real-cyclotomic norm at a character of order five is strictly
between two consecutive squares.  This is the first uniform Fourier
obstruction: it eliminates every equal-cycle parameter whose cycle length
is divisible by five. -/
theorem orderFiveNorm_not_isSquare (x : ℕ) (hx : 2 ≤ x) :
    ¬ IsSquare (x * x + x - 1) := by
  intro hsquare
  obtain ⟨y, hy⟩ := hsquare
  have hlo : x * x < y * y := by
    rw [← hy]
    omega
  have hhi : y * y < (x + 1) * (x + 1) := by
    rw [← hy]
    rw [show (x + 1) * (x + 1) = x * x + 2 * x + 1 by ring]
    omega
  have hxy : x < y := Nat.mul_self_lt_mul_self_iff.mp hlo
  have hyx : y < x + 1 := Nat.mul_self_lt_mul_self_iff.mp hhi
  omega

/-- The norm at primitive ninth roots, parametrized by the odd integer
`x = 2v+3`.  The expanded form avoids truncated subtraction in `ℕ`. -/
def orderNineNorm (v : ℕ) : ℕ :=
  16 * v ^ 4 + 104 * v ^ 3 + 240 * v ^ 2 + 230 * v + 76

/-- Identification with `P₄(x)=x⁴+x³-3x²-2x+1` at `x=2v+3`. -/
theorem orderNineNorm_eq_dirichletPolynomial (v : ℕ) :
    (orderNineNorm v : ℤ) =
      (2 * (v : ℤ) + 3) ^ 4 + (2 * (v : ℤ) + 3) ^ 3 -
        3 * (2 * (v : ℤ) + 3) ^ 2 - 2 * (2 * (v : ℤ) + 3) + 1 := by
  simp only [orderNineNorm]
  push_cast
  ring

/-- The primitive order-nine norm has an exact consecutive-square
sandwich. -/
theorem orderNineNorm_eq_square_add (v : ℕ) :
    orderNineNorm v =
      (4 * v ^ 2 + 13 * v + 8) ^ 2 + (7 * v ^ 2 + 22 * v + 12) := by
  simp only [orderNineNorm]
  ring

/-- The primitive order-nine real-cyclotomic norm is never a square for an
odd graph parameter `x ≥ 3`. -/
theorem orderNineNorm_not_isSquare (v : ℕ) :
    ¬ IsSquare (orderNineNorm v) := by
  intro hsquare
  obtain ⟨y, hy⟩ := hsquare
  let A := 4 * v ^ 2 + 13 * v + 8
  let B := 7 * v ^ 2 + 22 * v + 12
  have hrepr : orderNineNorm v = A ^ 2 + B := by
    simpa only [A, B] using orderNineNorm_eq_square_add v
  have hBpos : 0 < B := by
    dsimp only [B]
    omega
  have hBgap : B < 2 * A + 1 := by
    dsimp only [A, B]
    nlinarith [sq_nonneg (v : ℤ)]
  have hlo : A * A < y * y := by
    rw [← hy, hrepr, pow_two]
    omega
  have hhi : y * y < (A + 1) * (A + 1) := by
    rw [← hy, hrepr, pow_two]
    nlinarith
  have hAy : A < y := Nat.mul_self_lt_mul_self_iff.mp hlo
  have hyA : y < A + 1 := Nat.mul_self_lt_mul_self_iff.mp hhi
  omega

/-- If a square is divisible by three, it is divisible by nine. -/
theorem nine_dvd_of_three_dvd_of_isSquare {d : ℕ}
    (hthree : 3 ∣ d) (hsquare : IsSquare d) : 9 ∣ d := by
  obtain ⟨y, hy⟩ := hsquare
  have hthreeSq : 3 ∣ y ^ 2 := by
    simpa [pow_two, hy] using hthree
  have hthreeY : 3 ∣ y := Nat.prime_three.dvd_of_dvd_pow hthreeSq
  obtain ⟨z, hz⟩ := hthreeY
  refine ⟨z * z, ?_⟩
  rw [hy, hz]
  ring

/-- The boundary order can never be divisible by nine once the degree is. -/
theorem nine_not_dvd_boundary_of_nine_dvd_degree {d : ℕ}
    (hnine : 9 ∣ d) : ¬ 9 ∣ d * (d - 1) + 3 := by
  intro hboundary
  have hprod : 9 ∣ d * (d - 1) := dvd_mul_of_dvd_left hnine _
  have hsum : 9 ∣ 3 + d * (d - 1) := by
    simpa [Nat.add_comm] using hboundary
  have hthree : 9 ∣ 3 := (Nat.dvd_add_iff_left hprod).mpr hsum
  omega

/-- Arithmetic terminal for the order-nine Fourier branch.  Primitive
order-nine trace vanishing supplies `3 ∣ d`.  If the order-three norm `d`
is nonsquare, order-three trace vanishing supplies `9 ∣ d`; if it is a
square, divisibility by three already supplies the same conclusion. -/
theorem orderNine_boundary_contradiction
    {d : ℕ} (hboundary : 9 ∣ d * (d - 1) + 3)
    (hthree : 3 ∣ d) (hnonsquareTrace : ¬ IsSquare d → 9 ∣ d) : False := by
  have hnine : 9 ∣ d := by
    by_cases hsquare : IsSquare d
    · exact nine_dvd_of_three_dvd_of_isSquare hthree hsquare
    · exact hnonsquareTrace hsquare
  exact nine_not_dvd_boundary_of_nine_dvd_degree hnine hboundary

/-- Substituting `d = r + 4a - 3` into the boundary order shows that the
cycle length divides a quadratic in the diagonal-anchor surplus. -/
theorem dvd_surplusQuadratic_of_boundary
    {r d a : ℤ} (hform : d = r + 4 * a - 3)
    (hdiv : r ∣ d * (d - 1) + 3) :
    r ∣ 16 * a * a - 28 * a + 15 := by
  obtain ⟨k, hk⟩ := hdiv
  refine ⟨k - (r + 8 * a - 7), ?_⟩
  rw [hform] at hk
  nlinarith [hk]

/-- Surplus parameter one is incompatible with a cycle length at least five. -/
theorem surplus_ne_one_of_boundary
    {r d a : ℤ} (hr : 5 ≤ r) (hform : d = r + 4 * a - 3)
    (hdiv : r ∣ d * (d - 1) + 3) : a ≠ 1 := by
  intro ha
  have hthree : r ∣ 3 := by
    simpa [ha] using dvd_surplusQuadratic_of_boundary hform hdiv
  obtain ⟨k, hk⟩ := hthree
  have hrpos : 0 < r := by omega
  have hkpos : 0 < k := by nlinarith
  nlinarith

/-- Zero surplus forces the cycle length to divide fifteen. -/
theorem dvd_fifteen_of_zero_surplus
    {r d a : ℤ} (hform : d = r + 4 * a - 3)
    (hdiv : r ∣ d * (d - 1) + 3) (ha : a = 0) : r ∣ 15 := by
  simpa [ha] using dvd_surplusQuadratic_of_boundary hform hdiv

end Erdos85
