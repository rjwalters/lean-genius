import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-
# The Hadwiger–Finsler Inequality (a sharpening of Weitzenböck)

## What This Proves
For any triangle with side lengths `a, b, c` and area `T`,
  `a² + b² + c² ≥ 4·√3·T + (a−b)² + (b−c)² + (c−a)²`,
with equality **iff** the triangle is equilateral (`a = b = c`).

This is a genuine strengthening of Weitzenböck's inequality
`a² + b² + c² ≥ 4·√3·T`: the extra term
`(a−b)² + (b−c)² + (c−a)² ≥ 0` measures exactly how far the triangle is from
being equilateral, so Hadwiger–Finsler recovers Weitzenböck on dropping it and
quantifies the slack in the Weitzenböck bound.

## Approach
Write `T` through Heron's identity in squared form
  `16·T² = 2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴`,
and set
  `L := 2(ab + bc + ca) − (a² + b² + c²)`.
The algebraic identity `(a²+b²+c²) − [(a−b)²+(b−c)²+(c−a)²] = L` turns the target
into `L ≥ 4·√3·T`, which we square to `L² ≥ 48·T²` and discharge as an SOS.

The clean way to see the SOS is the **Ravi substitution**
  `p = b+c−a,  q = c+a−b,  r = a+b−c`,
under which `16·T² = (p+q+r)·p·q·r` and `L = pq + qr + rp`, so
  `L² − 48·T² = ½·((pq−qr)² + (qr−rp)² + (rp−pq)²) ≥ 0`
is an *unconditional* polynomial identity (true for all reals — no triangle
hypothesis). The triangle inequalities are needed only to get `L ≥ 0` (so the
squared inequality can be un-squared with the correct sign): then `p, q, r ≥ 0`
and `L = pq + qr + rp ≥ 0`. The same vanishing-SOS forces the equality case to be
equilateral. The √3 is handled by `Real.sqrt_sq`, exactly as in the parent
Weitzenböck proof.

This is not a named Mathlib result.
-/

namespace WeitzenbockInequalityOQ01OQ01

/-- Heron's area identity, squared and scaled by 16:
`16·T² = 2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴`. We take this as the algebraic
definition of the squared area of a triangle with sides `a, b, c` (same
convention as the parent Weitzenböck entry). -/
def heronArea16Sq (a b c : ℝ) : ℝ :=
  2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2
    - a ^ 4 - b ^ 4 - c ^ 4

/-- The Finsler excess term `(a−b)² + (b−c)² + (c−a)²`: the amount by which
Hadwiger–Finsler strengthens Weitzenböck. -/
def finslerExcess (a b c : ℝ) : ℝ :=
  (a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2

/-- The reduced linear functional `L := 2(ab+bc+ca) − (a²+b²+c²)`. The
Hadwiger–Finsler target `a²+b²+c² ≥ 4√3T + excess` is equivalent to `L ≥ 4√3T`. -/
def hadwigerL (a b c : ℝ) : ℝ :=
  2 * (a * b + b * c + c * a) - (a ^ 2 + b ^ 2 + c ^ 2)

/-- The excess term is nonnegative, so Hadwiger–Finsler is at least as strong as
Weitzenböck. -/
theorem finslerExcess_nonneg (a b c : ℝ) : 0 ≤ finslerExcess a b c := by
  unfold finslerExcess; positivity

/-- The excess vanishes exactly for an equilateral triangle: this is precisely
the condition under which Hadwiger–Finsler degenerates to Weitzenböck. -/
theorem finslerExcess_eq_zero_iff (a b c : ℝ) :
    finslerExcess a b c = 0 ↔ a = b ∧ b = c := by
  unfold finslerExcess
  constructor
  · intro h
    have h1 : (a - b) ^ 2 = 0 :=
      le_antisymm (by nlinarith [h, sq_nonneg (b - c), sq_nonneg (c - a)]) (sq_nonneg _)
    have h2 : (b - c) ^ 2 = 0 :=
      le_antisymm (by nlinarith [h, sq_nonneg (a - b), sq_nonneg (c - a)]) (sq_nonneg _)
    have hab : a - b = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h1
    have hbc : b - c = 0 := pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp h2
    exact ⟨sub_eq_zero.mp hab, sub_eq_zero.mp hbc⟩
  · rintro ⟨hab, hbc⟩; rw [hab, hbc]; ring

/-- Key algebraic identity: subtracting the Finsler excess from `a²+b²+c²`
collapses to `L`. -/
theorem sub_excess_eq_L (a b c : ℝ) :
    (a ^ 2 + b ^ 2 + c ^ 2) - finslerExcess a b c = hadwigerL a b c := by
  unfold finslerExcess hadwigerL; ring

/-- `L` is nonnegative on a genuine triangle. Via the Ravi substitution
`p = b+c−a ≥ 0`, `q = c+a−b ≥ 0`, `r = a+b−c ≥ 0`, we have `L = pq + qr + rp`, a
sum of products of nonnegative reals. -/
theorem hadwigerL_nonneg {a b c : ℝ} (hab : a ≤ b + c) (hbc : b ≤ c + a)
    (hca : c ≤ a + b) : 0 ≤ hadwigerL a b c := by
  have hp : 0 ≤ b + c - a := by linarith
  have hq : 0 ≤ c + a - b := by linarith
  have hr : 0 ≤ a + b - c := by linarith
  have e : hadwigerL a b c =
      (b + c - a) * (c + a - b) + (c + a - b) * (a + b - c)
        + (a + b - c) * (b + c - a) := by unfold hadwigerL; ring
  rw [e]
  have h1 := mul_nonneg hp hq
  have h2 := mul_nonneg hq hr
  have h3 := mul_nonneg hr hp
  linarith

/-- Squared form of Hadwiger–Finsler: `L² ≥ 48·T²`. This is the *unconditional*
SOS identity `L² − 48T² = ½((pq−qr)²+(qr−rp)²+(rp−pq)²) ≥ 0`; no triangle
hypothesis is needed here, only the Heron relation defining `T`. -/
theorem hadwiger_sq (a b c T : ℝ) (hT : 16 * T ^ 2 = heronArea16Sq a b c) :
    48 * T ^ 2 ≤ hadwigerL a b c ^ 2 := by
  have h48 : 48 * T ^ 2 = 3 * (16 * T ^ 2) := by ring
  rw [h48, hT]
  unfold heronArea16Sq hadwigerL
  -- p = b+c-a, q = c+a-b, r = a+b-c ; SOS in (pq-qr), (qr-rp), (rp-pq).
  nlinarith [sq_nonneg ((b + c - a) * (c + a - b) - (c + a - b) * (a + b - c)),
    sq_nonneg ((c + a - b) * (a + b - c) - (a + b - c) * (b + c - a)),
    sq_nonneg ((a + b - c) * (b + c - a) - (b + c - a) * (c + a - b))]

/-- For nonnegative reals, equality of squares implies equality. (Same helper as
the parent Weitzenböck entry.) -/
theorem eq_of_sq_eq_sq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ^ 2 = v ^ 2) :
    u = v := by
  have h1 : Real.sqrt (u ^ 2) = Real.sqrt (v ^ 2) := by rw [h]
  rwa [Real.sqrt_sq hu, Real.sqrt_sq hv] at h1

/-- **The Hadwiger–Finsler inequality.** For a triangle with side lengths
`a, b, c` satisfying the triangle inequalities and area `T` (given by Heron's
formula),
  `a² + b² + c² ≥ 4·√3·T + (a−b)² + (b−c)² + (c−a)²`. -/
theorem hadwiger_finsler (a b c T : ℝ) (hTnn : 0 ≤ T)
    (hab : a ≤ b + c) (hbc : b ≤ c + a) (hca : c ≤ a + b)
    (hT : 16 * T ^ 2 = heronArea16Sq a b c) :
    4 * Real.sqrt 3 * T + finslerExcess a b c ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have hLnn : 0 ≤ hadwigerL a b c := hadwigerL_nonneg hab hbc hca
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlhs : 0 ≤ 4 * Real.sqrt 3 * T := by positivity
  have hsqlhs : (4 * Real.sqrt 3 * T) ^ 2 = 48 * T ^ 2 := by
    have h : (4 * Real.sqrt 3 * T) ^ 2 = 16 * Real.sqrt 3 ^ 2 * T ^ 2 := by ring
    rw [h, hs]; ring
  have hcore : (4 * Real.sqrt 3 * T) ^ 2 ≤ hadwigerL a b c ^ 2 := by
    rw [hsqlhs]; exact hadwiger_sq a b c T hT
  have hkey : 4 * Real.sqrt 3 * T ≤ hadwigerL a b c := by
    calc 4 * Real.sqrt 3 * T
        = Real.sqrt ((4 * Real.sqrt 3 * T) ^ 2) := (Real.sqrt_sq hlhs).symm
      _ ≤ Real.sqrt (hadwigerL a b c ^ 2) := Real.sqrt_le_sqrt hcore
      _ = hadwigerL a b c := Real.sqrt_sq hLnn
  have hsub := sub_excess_eq_L a b c
  linarith

/-- **Hadwiger–Finsler implies Weitzenböck.** Dropping the nonnegative excess
term recovers the weaker bound `a² + b² + c² ≥ 4·√3·T`. -/
theorem weitzenbock_of_hadwiger (a b c T : ℝ) (hTnn : 0 ≤ T)
    (hab : a ≤ b + c) (hbc : b ≤ c + a) (hca : c ≤ a + b)
    (hT : 16 * T ^ 2 = heronArea16Sq a b c) :
    4 * Real.sqrt 3 * T ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have h := hadwiger_finsler a b c T hTnn hab hbc hca hT
  have hexc := finslerExcess_nonneg a b c
  linarith

/-- **Equality case.** For a genuine triangle with positive sides,
Hadwiger–Finsler is an equality iff the triangle is equilateral. The forward
direction comes from the vanishing SOS forcing the three Ravi differences to
zero; the reverse direction is a direct computation with `T = √3·a²/4`. -/
theorem hadwiger_finsler_eq_iff (a b c T : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hTnn : 0 ≤ T) (hab : a ≤ b + c) (hbc : b ≤ c + a)
    (hca : c ≤ a + b) (hT : 16 * T ^ 2 = heronArea16Sq a b c) :
    4 * Real.sqrt 3 * T + finslerExcess a b c = a ^ 2 + b ^ 2 + c ^ 2
      ↔ a = b ∧ b = c := by
  constructor
  · intro h
    -- At equality `4√3T = L`; square to `48T² = L²`, hence the SOS vanishes.
    have hLeq : 4 * Real.sqrt 3 * T = hadwigerL a b c := by
      rw [← sub_excess_eq_L]; linarith
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hsqlhs : (4 * Real.sqrt 3 * T) ^ 2 = 48 * T ^ 2 := by
      have h2 : (4 * Real.sqrt 3 * T) ^ 2 = 16 * Real.sqrt 3 ^ 2 * T ^ 2 := by ring
      rw [h2, hs]; ring
    have hpoly : (48 : ℝ) * T ^ 2 = hadwigerL a b c ^ 2 := by rw [← hsqlhs, hLeq]
    have hheron : (48 : ℝ) * T ^ 2 = 3 * heronArea16Sq a b c := by
      rw [show (48 : ℝ) * T ^ 2 = 3 * (16 * T ^ 2) by ring, hT]
    have hSOS : hadwigerL a b c ^ 2 - 3 * heronArea16Sq a b c = 0 := by linarith
    unfold hadwigerL heronArea16Sq at hSOS
    -- `L² − 3·heron = ½·(D1² + D2² + D3²)` where Dᵢ are the Ravi differences.
    have hsum : ((b + c - a) * (c + a - b) - (c + a - b) * (a + b - c)) ^ 2
        + ((c + a - b) * (a + b - c) - (a + b - c) * (b + c - a)) ^ 2
        + ((a + b - c) * (b + c - a) - (b + c - a) * (c + a - b)) ^ 2 = 0 := by
      linear_combination 2 * hSOS
    -- A sum of three squares is zero, so each square is zero.
    have nn1 : 0 ≤ ((b + c - a) * (c + a - b) - (c + a - b) * (a + b - c)) ^ 2 := sq_nonneg _
    have nn2 : 0 ≤ ((c + a - b) * (a + b - c) - (a + b - c) * (b + c - a)) ^ 2 := sq_nonneg _
    have nn3 : 0 ≤ ((a + b - c) * (b + c - a) - (b + c - a) * (c + a - b)) ^ 2 := sq_nonneg _
    have hD1 : ((b + c - a) * (c + a - b) - (c + a - b) * (a + b - c)) ^ 2 = 0 := by
      linarith [hsum, nn2, nn3]
    have hD2 : ((c + a - b) * (a + b - c) - (a + b - c) * (b + c - a)) ^ 2 = 0 := by
      linarith [hsum, nn1, nn3]
    have d1 : (b + c - a) * (c + a - b) - (c + a - b) * (a + b - c) = 0 :=
      pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hD1
    have d2 : (c + a - b) * (a + b - c) - (a + b - c) * (b + c - a) = 0 :=
      pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp hD2
    -- Factor the Ravi differences: each is twice a `(side gap)·(difference)`.
    have f1 : (a + b - c) * (a - b) = 0 := by linear_combination d2 / 2
    have f2 : (b + c - a) * (b - c) = 0 := by linear_combination - d1 / 2 - d2 / 2
    have f3 : (c + a - b) * (c - a) = 0 := by linear_combination d1 / 2
    -- `a = b`: if not, then `a+b-c = 0`, forcing `c = a+b`, which makes `f2` say
    -- `(2b)(−a) = 0`, contradicting positivity.
    have hAB : a = b := by
      by_contra hne
      have h1 : a + b - c = 0 := by
        rcases mul_eq_zero.mp f1 with hh | hh
        · exact hh
        · exact absurd (sub_eq_zero.mp hh) hne
      have hc2 : c = a + b := by linarith
      rw [hc2] at f2
      have hab2 : a * b = 0 := by linear_combination - f2 / 2
      exact (mul_pos ha hb).ne' hab2
    -- `b = c`: with `a = b`, `c+a-b = c > 0`, so `f3` forces `c = a = b`.
    have hfac : c + a - b = c := by rw [hAB]; ring
    rw [hfac] at f3
    have hBC : b = c := by
      rcases mul_eq_zero.mp f3 with hh | hh
      · exact absurd hh hc.ne'
      · have hca0 : c = a := sub_eq_zero.mp hh
        rw [hAB] at hca0; exact hca0.symm
    exact ⟨hAB, hBC⟩
  · rintro ⟨hab', hbc'⟩
    subst hab'
    subst hbc'
    have hzero : finslerExcess a a a = 0 := by unfold finslerExcess; ring
    rw [hzero, add_zero]
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    have hT3 : 16 * T ^ 2 = 3 * a ^ 4 := by rw [hT]; unfold heronArea16Sq; ring
    have hTval : T = Real.sqrt 3 * a ^ 2 / 4 := by
      have hrhsnn : 0 ≤ Real.sqrt 3 * a ^ 2 / 4 := by positivity
      have hTsq : T ^ 2 = (Real.sqrt 3 * a ^ 2 / 4) ^ 2 := by
        have hexp : (Real.sqrt 3 * a ^ 2 / 4) ^ 2 = 3 * a ^ 4 / 16 := by
          rw [div_pow, mul_pow, hs]; ring
        rw [hexp]; linarith [hT3]
      exact eq_of_sq_eq_sq hTnn hrhsnn hTsq
    rw [hTval,
      show 4 * Real.sqrt 3 * (Real.sqrt 3 * a ^ 2 / 4) = Real.sqrt 3 ^ 2 * a ^ 2 by ring, hs]
    ring

end WeitzenbockInequalityOQ01OQ01
