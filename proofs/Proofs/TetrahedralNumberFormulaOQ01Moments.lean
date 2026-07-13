import Proofs.TetrahedralNumberFormulaOQ01
import Mathlib.Combinatorics.Enumerative.Stirling

/-
# Ordinary Power Moments of Figurate Numbers via Stirling Numbers of the Second Kind

## What This Proves

The parent file `TetrahedralNumberFormulaOQ01` computes the **falling-factorial moments**
of a figurate (simplex-number) row in closed form:

    ∑_{k} (k)_r · P_d(k) = (d+r)_r · P_{d+r+1}(·)          (`descFactorial_moment_sum_simplex`)

where `(k)_r = k(k-1)⋯(k-r+1) = k.descFactorial r` is the falling factorial and
`P_d(n) = simplexNumber d n = C(n+d, d)` is the d-dimensional figurate number.  The
falling factorials are the *natural* discrete moment basis, but the **ordinary power
moments** `∑_k kᵐ · P_d(k)` are the ones one usually wants.  This file bridges the two by
formalizing the classical change of basis

    xᵐ = ∑_{r=0}^{m} S(m,r) · (x)_r                        (`pow_eq_sum_stirlingSecond_descFactorial`)

where `S(m,r) = Nat.stirlingSecond m r` is the Stirling number of the second kind.  This
power-to-falling-factorial expansion is the *defining* property of the Stirling numbers of
the second kind; Mathlib provides `Nat.stirlingSecond` and its recurrence but **not** this
identity, so it is built here.  Applying it termwise to the figurate moment gives the
capstone closed form for every ordinary power moment:

    ∑_{k ≤ N} kᵐ · P_d(k) = ∑_{r=0}^{m} S(m,r) · (d+r)_r · P_{d+r+1}(N-r)   (`pow_moment_sum_simplex`)

and, as a concrete instance, the second-moment hockey stick

    ∑_{k ≤ N} k² · P_d(k) = (d+1)·P_{d+2}(N-1) + (d+1)(d+2)·P_{d+3}(N-2)    (`sq_moment_sum_simplex`)

the discrete analogue of the continuous moment `∫₀ᴺ x²·x^d dx`.

## Approach

1. `mul_descFactorial_absorb` — the pointwise absorption `x·(x)_r = (x)_{r+1} + r·(x)_r`,
   the falling-factorial analogue of `x·xʳ = x^{r+1}`. Over `ℕ` it holds unconditionally
   (both sides vanish when `x < r`).
2. `pow_eq_sum_stirlingSecond_descFactorial` — the change of basis, by induction on `m`.
   The step multiplies the hypothesis by `x`, applies absorption termwise, and matches the
   two resulting sums against the Stirling recurrence
   `S(m+1,k+1) = (k+1)·S(m,k+1) + S(m,k)` (`Nat.stirlingSecond_succ_succ`) after a
   reindexing that consumes the vanishing boundary terms `S(m+1,0) = 0` and `S(m,m+1) = 0`.
3. `descFactorial_moment_fixed_range` — the parent moment re-expressed over a *fixed* top
   index `N` (rather than the `r`-dependent range `n+r+1`), so that a single summation range
   serves all orders `r ≤ m` simultaneously.
4. `pow_moment_sum_simplex` — expand `kᵐ`, swap the order of summation, and collapse each
   falling-factorial moment.
5. `sq_moment_sum_simplex` — the explicit `m = 2` instance.

## Honesty Note

This is exact, axiom-free discrete combinatorics: the change-of-basis identity is the
genuine missing Mathlib lemma, and the moment closed form is its direct consequence. It does
not touch any open analytic content — it is outward-facing infrastructure completing the
figurate moment theory begun in the parent file.
-/

namespace TetrahedralNumberFormulaOQ01

open Finset Nat

/-! ### The falling-factorial absorption identity -/

/-- **Falling-factorial absorption.** The discrete analogue of `x · xʳ = x^{r+1}`:
multiplying the falling factorial `(x)_r` by `x` raises the order by one, up to the
lower-order correction `r·(x)_r`:

    x · (x)_r = (x)_{r+1} + r · (x)_r.

Over `ℕ` this holds for *all* `x, r`: when `x ≥ r` it is the algebraic identity
`x = (x - r) + r` applied to `(x)_{r+1} = (x - r)·(x)_r`; when `x < r` both `(x)_r` and
`(x)_{r+1}` vanish, so both sides are `0`. This is the pointwise engine behind the
power-to-falling-factorial change of basis. -/
theorem mul_descFactorial_absorb (x r : ℕ) :
    x * x.descFactorial r = x.descFactorial (r + 1) + r * x.descFactorial r := by
  rw [Nat.descFactorial_succ, ← Nat.add_mul]
  rcases le_or_gt r x with h | h
  · rw [Nat.sub_add_cancel h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]
    ring

/-! ### The power-to-falling-factorial change of basis -/

/-- **Powers in the falling-factorial basis (Stirling second kind).** Every power expands as
a Stirling-weighted sum of falling factorials:

    xᵐ = ∑_{r=0}^{m} S(m,r) · (x)_r,

with `S(m,r) = Nat.stirlingSecond m r`. This is the identity that *characterises* the
Stirling numbers of the second kind; Mathlib defines `Nat.stirlingSecond` and proves its
recurrence but not this change of basis, so it is established here by induction on `m`.

The step multiplies the hypothesis by `x`, applies `mul_descFactorial_absorb` termwise to get
`∑ S(m,r)·(x)_{r+1} + ∑ r·S(m,r)·(x)_r`, and matches this against the target
`∑_{r} S(m+1,r)·(x)_r`. Peeling the `r = 0` term (`S(m+1,0) = 0`) and applying the Stirling
recurrence `S(m+1,r+1) = (r+1)·S(m,r+1) + S(m,r)` splits the target into exactly those two
sums, once the reindexing identity `∑ (r+1)·S(m,r+1)·(x)_{r+1} = ∑ r·S(m,r)·(x)_r` (whose
boundary terms vanish via `S(m,m+1) = 0`) is discharged. -/
theorem pow_eq_sum_stirlingSecond_descFactorial (x m : ℕ) :
    x ^ m = ∑ r ∈ range (m + 1), stirlingSecond m r * x.descFactorial r := by
  induction m with
  | zero => simp
  | succ m ih =>
    -- Reindexing identity for the "lower-order" sum: shifting the index up by one and
    -- absorbing the coefficient `r+1` matches the `r·S(m,r)` weighting; both boundary
    -- terms vanish (`S(m,m+1) = 0` on the left, the `r = 0` factor on the right).
    have key : (∑ r ∈ range (m + 1),
          (r + 1) * stirlingSecond m (r + 1) * x.descFactorial (r + 1))
        = ∑ r ∈ range (m + 1), r * stirlingSecond m r * x.descFactorial r := by
      rw [Finset.sum_range_succ
            (fun r => (r + 1) * stirlingSecond m (r + 1) * x.descFactorial (r + 1)) m,
          Finset.sum_range_succ'
            (fun r => r * stirlingSecond m r * x.descFactorial r) m]
      simp [stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self m)]
    -- Expand `x^{m+1}` via the hypothesis and termwise absorption.
    have expand : x ^ (m + 1)
        = (∑ r ∈ range (m + 1), stirlingSecond m r * x.descFactorial (r + 1))
          + ∑ r ∈ range (m + 1), r * stirlingSecond m r * x.descFactorial r := by
      rw [pow_succ, ih, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      calc stirlingSecond m r * x.descFactorial r * x
          = stirlingSecond m r * (x * x.descFactorial r) := by ring
        _ = stirlingSecond m r
              * (x.descFactorial (r + 1) + r * x.descFactorial r) := by
            rw [mul_descFactorial_absorb]
        _ = stirlingSecond m r * x.descFactorial (r + 1)
              + r * stirlingSecond m r * x.descFactorial r := by ring
    -- Transform the target `∑_{r ≤ m+1} S(m+1,r)·(x)_r` into the same two sums.
    rw [expand,
        Finset.sum_range_succ'
          (fun r => stirlingSecond (m + 1) r * x.descFactorial r) (m + 1)]
    have hrhs : (∑ r ∈ range (m + 1),
          stirlingSecond (m + 1) (r + 1) * x.descFactorial (r + 1))
        = (∑ r ∈ range (m + 1), stirlingSecond m r * x.descFactorial (r + 1))
          + ∑ r ∈ range (m + 1),
              (r + 1) * stirlingSecond m (r + 1) * x.descFactorial (r + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      rw [stirlingSecond_succ_succ]
      ring
    rw [hrhs, key]
    simp

/-! ### Fixed-range figurate moment -/

/-- **Falling-factorial moment over a fixed top index.** The parent
`descFactorial_moment_sum_simplex` sums over the order-dependent range `n + r + 1`. For the
power-moment application we need one summation range serving every order `r ≤ m` at once, so
here the same identity is re-expressed over a fixed top index `N` (with `r ≤ N`):

    ∑_{k ≤ N} (k)_r · P_d(k) = (d+r)_r · P_{d+r+1}(N-r).

This is `descFactorial_moment_sum_simplex` at `n = N - r`, using `N - r + r = N`. -/
theorem descFactorial_moment_fixed_range (r d N : ℕ) (h : r ≤ N) :
    ∑ k ∈ range (N + 1), k.descFactorial r * simplexNumber d k
      = (d + r).descFactorial r * simplexNumber (d + r + 1) (N - r) := by
  have hmoment := descFactorial_moment_sum_simplex r d (N - r)
  rwa [Nat.sub_add_cancel h] at hmoment

/-! ### Ordinary power moments -/

/-- **Ordinary power-moment hockey stick.** Weighting a figurate row by the ordinary power
`kᵐ` (rather than the falling factorial) and summing over `k ≤ N` collapses to a
Stirling-weighted sum of higher-dimensional figurate numbers:

    ∑_{k ≤ N} kᵐ · P_d(k) = ∑_{r=0}^{m} S(m,r) · (d+r)_r · P_{d+r+1}(N-r),

valid whenever `m ≤ N` (so every order `r ≤ m` fits the summation range). This is the
ordinary-moment companion of the parent's falling-factorial moment
`descFactorial_moment_sum_simplex`; the Stirling numbers of the second kind are exactly the
change-of-basis coefficients converting one moment basis into the other. The `m = 1` case
recovers the first moment `weighted_sum_simplex` (`S(1,0) = 0`, `S(1,1) = 1`,
`(d+1)_1 = d+1`); the `m = 2` case is `sq_moment_sum_simplex`.

Proof: expand `kᵐ` by `pow_eq_sum_stirlingSecond_descFactorial`, exchange the order of
summation (`Finset.sum_comm`), factor out the (`k`-independent) Stirling coefficient, and
collapse each inner falling-factorial moment with `descFactorial_moment_fixed_range`. -/
theorem pow_moment_sum_simplex (m d N : ℕ) (h : m ≤ N) :
    ∑ k ∈ range (N + 1), k ^ m * simplexNumber d k
      = ∑ r ∈ range (m + 1),
          stirlingSecond m r * ((d + r).descFactorial r * simplexNumber (d + r + 1) (N - r)) := by
  have hexp : ∀ k, k ^ m * simplexNumber d k
      = ∑ r ∈ range (m + 1),
          stirlingSecond m r * k.descFactorial r * simplexNumber d k := by
    intro k
    rw [pow_eq_sum_stirlingSecond_descFactorial k m, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun k _ => hexp k), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  have hrN : r ≤ N := le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)) h
  calc ∑ k ∈ range (N + 1),
          stirlingSecond m r * k.descFactorial r * simplexNumber d k
      = stirlingSecond m r
          * ∑ k ∈ range (N + 1), k.descFactorial r * simplexNumber d k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
    _ = stirlingSecond m r
          * ((d + r).descFactorial r * simplexNumber (d + r + 1) (N - r)) := by
        rw [descFactorial_moment_fixed_range r d N hrN]

/-- **Second-moment (quadratic) hockey stick.** The `m = 2` instance of
`pow_moment_sum_simplex`, written out with the concrete Stirling values
`S(2,0) = 0`, `S(2,1) = S(2,2) = 1` and the falling factorials `(d+1)_1 = d+1`,
`(d+2)_2 = (d+1)(d+2)`:

    ∑_{k ≤ N} k² · P_d(k) = (d+1)·P_{d+2}(N-1) + (d+1)(d+2)·P_{d+3}(N-2)      (N ≥ 2).

This is the exact discrete analogue of the continuous second moment
`∫₀ᴺ x²·x^d dx`, one rung above the first-moment hockey stick `weighted_sum_simplex`. -/
theorem sq_moment_sum_simplex (d N : ℕ) (h : 2 ≤ N) :
    ∑ k ∈ range (N + 1), k ^ 2 * simplexNumber d k
      = (d + 1) * simplexNumber (d + 2) (N - 1)
        + (d + 1) * (d + 2) * simplexNumber (d + 3) (N - 2) := by
  rw [pow_moment_sum_simplex 2 d N h]
  have hd2 : (d + 2).descFactorial 2 = (d + 1) * (d + 2) := by
    show (d + 2).descFactorial (1 + 1) = (d + 1) * (d + 2)
    rw [Nat.descFactorial_succ, Nat.descFactorial_one, show d + 2 - 1 = d + 1 from by omega]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    show stirlingSecond 2 0 = 0 from rfl, show stirlingSecond 2 1 = 1 from rfl,
    show stirlingSecond 2 2 = 1 from rfl, Nat.descFactorial_one, hd2,
    show d + 1 + 1 = d + 2 from rfl, show d + 2 + 1 = d + 3 from rfl,
    Nat.zero_mul, Nat.one_mul, Nat.zero_add]

/-- **Third-moment (cubic) hockey stick.** The `m = 3` instance of `pow_moment_sum_simplex`,
written out with the concrete Stirling values `S(3,0) = 0`, `S(3,1) = 1`, `S(3,2) = 3`,
`S(3,3) = 1` and the falling factorials `(d+1)_1 = d+1`, `(d+2)_2 = (d+1)(d+2)`,
`(d+3)_3 = (d+1)(d+2)(d+3)`:

    ∑_{k ≤ N} k³ · P_d(k)
      = (d+1)·P_{d+2}(N-1) + 3(d+1)(d+2)·P_{d+3}(N-2) + (d+1)(d+2)(d+3)·P_{d+4}(N-3)   (N ≥ 3).

The discrete analogue of the continuous third moment `∫₀ᴺ x³·x^d dx`, completing the moment
ladder `m = 0` (hockey stick) → `m = 1` (`weighted_sum_simplex`) → `m = 2`
(`sq_moment_sum_simplex`) → `m = 3` over the simplex kernel. -/
theorem cube_moment_sum_simplex (d N : ℕ) (h : 3 ≤ N) :
    ∑ k ∈ range (N + 1), k ^ 3 * simplexNumber d k
      = (d + 1) * simplexNumber (d + 2) (N - 1)
        + 3 * ((d + 1) * (d + 2)) * simplexNumber (d + 3) (N - 2)
        + (d + 1) * (d + 2) * (d + 3) * simplexNumber (d + 4) (N - 3) := by
  rw [pow_moment_sum_simplex 3 d N h]
  have hd2 : (d + 2).descFactorial 2 = (d + 1) * (d + 2) := by
    show (d + 2).descFactorial (1 + 1) = (d + 1) * (d + 2)
    rw [Nat.descFactorial_succ, Nat.descFactorial_one, show d + 2 - 1 = d + 1 from by omega]
  have hd3 : (d + 3).descFactorial 3 = (d + 1) * (d + 2) * (d + 3) := by
    have e2 : (d + 3).descFactorial 2 = (d + 2) * (d + 3) := by
      show (d + 3).descFactorial (1 + 1) = (d + 2) * (d + 3)
      rw [Nat.descFactorial_succ, Nat.descFactorial_one, show d + 3 - 1 = d + 2 from by omega]
    show (d + 3).descFactorial (2 + 1) = (d + 1) * (d + 2) * (d + 3)
    rw [Nat.descFactorial_succ, e2, show d + 3 - 2 = d + 1 from by omega]
    ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    show stirlingSecond 3 0 = 0 from rfl, show stirlingSecond 3 1 = 1 from rfl,
    show stirlingSecond 3 2 = 3 from rfl, show stirlingSecond 3 3 = 1 from rfl,
    Nat.descFactorial_one, hd2, hd3,
    show d + 1 + 1 = d + 2 from rfl, show d + 2 + 1 = d + 3 from rfl,
    show d + 3 + 1 = d + 4 from rfl, Nat.zero_mul, Nat.one_mul, Nat.zero_add]
  ring

end TetrahedralNumberFormulaOQ01

