import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic

/-
# Unifying the weight family: a recurrence for the finite m-th moment ∑ kᵐ·xᵏ

## What This Proves

For a ratio `x`, a length `n`, and an exponent `m`, the *m-th moment*
finite weighted geometric sum

  momentSum m n x  :=  ∑_{k=0}^{n-1} kᵐ·xᵏ

(each geometric term `xᵏ` weighted by the `m`-th power of its index) satisfies,
over **any** commutative ring, the single division-free recurrence

  (1 − x) · momentSum m n x
      =  0ᵐ  −  nᵐ·xⁿ  +  x · ∑_{i=0}^{m−1} C(m,i) · momentSum i n x.       (★)

This is the unified statement behind the whole `∑ kᵐ·xᵏ` family.  Reading it as
`momentSum m n x = (…)/(1 − x)` and iterating, the denominator after fully
unwinding the `m` nested moments is exactly `(1 − x)^{m+1}`, and the numerator
is the finite analogue of the Eulerian polynomial Aₘ(x) (the *interior* part,
`0ᵐ + x·∑ C(m,i)·(numerator of moment i)`) corrected by the boundary term
`nᵐ·xⁿ`.  Specialising `m = 0, 1, 2` recovers the closed forms already in the
gallery:

  m = 0 : (1 − x)·∑_{k<n} xᵏ        = 1 − xⁿ
  m = 1 : (1 − x)·∑_{k<n} k·xᵏ      = −n·xⁿ + x·∑_{k<n} xᵏ
  m = 2 : (1 − x)·∑_{k<n} k²·xᵏ     = −n²·xⁿ + x·(∑_{k<n} xᵏ + 2·∑_{k<n} k·xᵏ)

Multiplying the `m = 1` line by `(1 − x)` and the `m = 2` line by `(1 − x)²`
reproduces the `(1 − x)²` and `(1 − x)³` closed forms of the parents
`geometric-series-oq-08-oq-01` and `geometric-series-oq-08-oq-01-oq-01`.

## Why a Recurrence (and not one explicit Eulerian formula)

The infinite series `∑_{k≥0} kᵐ·rᵏ = Aₘ(r)/(1 − r)^{m+1}` has a clean explicit
Eulerian-polynomial numerator, recorded in the gallery via the all-orders
moment `geometric-series-oq-07-oq-01` (Stirling form) and the Frobenius identity
`geometric-series-oq-07-oq-01-oq-01` (`eulerPoly`).  The **finite** sum carries,
in addition, an `n`-dependent *boundary* contribution `nᵐ·xⁿ` whose expansion in
powers of `n` has no single closed form independent of `m`.  Recurrence (★) is
therefore the sharpest fully general, fully explicit, division-free statement:
it is uniform in `m`, valid over any commutative ring, and reduces moment `m`
to *all* lower moments in one step.  The interior part of (★) is precisely the
Eulerian recurrence in the `n → ∞` limit (each `momentSum i n x → Aᵢ(x)/(1−x)^{i+1}`).

## Why This Is Not Already in Mathlib

Mathlib records the infinite linear and `choose`-weighted geometric series and
the plain finite geometric sum `geom_sum_eq`, but no finite m-th moment sum and
no recurrence linking the finite moments across `m`.

## Proof Strategy

1. **`sum_choose_mul_pow`.** `∑_{i<m} C(m,i)·aⁱ = (a+1)ᵐ − aᵐ`, from the binomial
   theorem `add_pow` with the top term `C(m,m)·aᵐ = aᵐ` peeled off.
2. **`momentSum_succ`.** Peel the top term with `Finset.sum_range_succ`.
3. **`momentSum_recurrence` (★).** Induction on `n`.  The base case is `0 = 0`;
   the step rewrites every `momentSum · (n+1)` with `momentSum_succ`, collapses
   the resulting `∑_{i<m} C(m,i)·nⁱ` via step 1 into `(n+1)ᵐ − nᵐ`, and closes
   with `linear_combination` against the induction hypothesis.  All index bases
   are kept as ring casts so the `n = 0` instance is well-defined (no ℕ
   truncated subtraction).
4. **Specialisations** `momentSum_recurrence_{zero,one,two}` instantiate `m`.

All results depend only on `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace GeometricSeriesOQ08OQ01OQ01OQ01

open Finset

variable {R : Type*} [CommRing R]

/-- The finite **m-th moment weighted geometric sum** `∑_{k=0}^{n-1} kᵐ·xᵏ`. -/
def momentSum (m n : ℕ) (x : R) : R :=
  ∑ k ∈ Finset.range n, (k : R) ^ m * x ^ k

/-- Binomial helper: `∑_{i<m} C(m,i)·aⁱ = (a+1)ᵐ − aᵐ` over any commutative ring.
The full binomial sum is `(a+1)ᵐ`; peeling off its top term `C(m,m)·aᵐ = aᵐ`
leaves the partial sum over `i < m`. -/
theorem sum_choose_mul_pow (m : ℕ) (a : R) :
    ∑ i ∈ Finset.range m, (m.choose i : R) * a ^ i = (a + 1) ^ m - a ^ m := by
  have h := add_pow a 1 m
  simp only [one_pow, mul_one] at h
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one] at h
  rw [h, add_sub_cancel_right]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Peeling the top term of a moment sum: `momentSum m (n+1) x = momentSum m n x + nᵐ·xⁿ`. -/
theorem momentSum_succ (m n : ℕ) (x : R) :
    momentSum m (n + 1) x = momentSum m n x + (n : R) ^ m * x ^ n := by
  simp only [momentSum, Finset.sum_range_succ]

/-- **Master recurrence (★).** Over any commutative ring,

  `(1 − x)·momentSum m n x = 0ᵐ − nᵐ·xⁿ + x·∑_{i<m} C(m,i)·momentSum i n x`.

Uniform in the exponent `m`, this reduces the `m`-th finite moment to all lower
moments in a single division-free step.  Iterating it clears the denominator
`(1 − x)^{m+1}`; its interior part is the Eulerian-polynomial recurrence in the
`n → ∞` limit. -/
theorem momentSum_recurrence (m n : ℕ) (x : R) :
    (1 - x) * momentSum m n x
      = (0 : R) ^ m - (n : R) ^ m * x ^ n
        + x * ∑ i ∈ Finset.range m, (m.choose i : R) * momentSum i n x := by
  induction n with
  | zero =>
    simp only [momentSum, Finset.sum_range_zero, mul_zero, pow_zero, mul_one,
      Finset.sum_const_zero, Nat.cast_zero, sub_self, add_zero]
  | succ n ih =>
    -- Expand the interior sum at `n+1` using `momentSum_succ` and collapse
    -- `∑_{i<m} C(m,i)·nⁱ` to `(n+1)ᵐ − nᵐ` via the binomial helper.
    have hsig : (∑ i ∈ Finset.range m, (m.choose i : R) * momentSum i (n + 1) x)
        = (∑ i ∈ Finset.range m, (m.choose i : R) * momentSum i n x)
          + x ^ n * (((n : R) + 1) ^ m - (n : R) ^ m) := by
      have hterm : ∀ i, (m.choose i : R) * momentSum i (n + 1) x
          = (m.choose i : R) * momentSum i n x
            + (m.choose i : R) * (n : R) ^ i * x ^ n := by
        intro i; rw [momentSum_succ]; ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib]
      congr 1
      rw [← Finset.sum_mul, sum_choose_mul_pow]
      ring
    rw [momentSum_succ, hsig, pow_succ]
    push_cast
    linear_combination ih

/-- `m = 0`: the plain finite geometric sum identity `(1 − x)·∑_{k<n} xᵏ = 1 − xⁿ`. -/
theorem momentSum_recurrence_zero (n : ℕ) (x : R) :
    (1 - x) * momentSum 0 n x = 1 - x ^ n := by
  have h := momentSum_recurrence 0 n x
  simpa using h

/-- `m = 1`: the linear arithmetico-geometric step
`(1 − x)·∑_{k<n} k·xᵏ = −n·xⁿ + x·∑_{k<n} xᵏ`. -/
theorem momentSum_recurrence_one (n : ℕ) (x : R) :
    (1 - x) * momentSum 1 n x = -(n : R) * x ^ n + x * momentSum 0 n x := by
  rw [momentSum_recurrence 1 n x, Finset.sum_range_one]
  simp only [pow_one, Nat.choose_zero_right, Nat.cast_one, one_mul]
  ring

/-- `m = 2`: the second-moment step
`(1 − x)·∑_{k<n} k²·xᵏ = −n²·xⁿ + x·(∑_{k<n} xᵏ + 2·∑_{k<n} k·xᵏ)`. -/
theorem momentSum_recurrence_two (n : ℕ) (x : R) :
    (1 - x) * momentSum 2 n x
      = -(n : R) ^ 2 * x ^ n + x * (momentSum 0 n x + 2 * momentSum 1 n x) := by
  have e2 : ∑ i ∈ Finset.range 2, (Nat.choose 2 i : R) * momentSum i n x
      = momentSum 0 n x + 2 * momentSum 1 n x := by
    simp [Finset.sum_range_succ]
  rw [momentSum_recurrence 2 n x, e2]
  have h0 : (0 : R) ^ 2 = 0 := by ring
  rw [h0]; ring

/-- Numerical sanity check over `ℤ`: `∑_{k<3} k·2ᵏ = 0 + 1·2 + 2·4 = 10`,
and the `m = 1` recurrence gives `(1 − 2)·10 = 0 − 3·8 + 2·(1 + 2 + 4) = −10`. -/
example : momentSum 1 3 (2 : ℤ) = 10 := by
  norm_num [momentSum, Finset.sum_range_succ]

end GeometricSeriesOQ08OQ01OQ01OQ01
