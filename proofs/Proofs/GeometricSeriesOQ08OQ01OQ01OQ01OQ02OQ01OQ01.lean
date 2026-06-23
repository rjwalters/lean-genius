import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01

/-
# An analysis-free proof of the Eulerian (★∞) recurrence

## What This Proves

The parent `geometric-series-oq-08-oq-01-oq-01-oq-01-oq-02-oq-01` proves the
**polynomial recurrence** satisfied by the Eulerian polynomials
`Eₘ = eulerPoly m` (geometric normalisation):

  (1 − X)·Eₘ = 0ᵐ·(1 − X)^{m+1} + X·∑_{i<m} C(m,i)·Eᵢ·(1 − X)^{m−i}.   (★)

The parent's proof is *analytic*: both sides are shown to agree at every point of
the infinite set `(−1, 1)` (using the Frobenius closed form
`∑ₙ nᵐ rⁿ = Eₘ(r)/(1−r)^{m+1}` and the analytic moment recurrence), hence agree
as polynomials.  That route runs through real analysis (`tsum`, convergence of the
geometric series and its derivatives).

This entry answers the open question recorded on the parent: it gives a **purely
algebraic, analysis-free** derivation of (★), valid over an *arbitrary commutative
ring* `R`.  The proof rests on a new combinatorial identity about Stirling numbers
of the second kind that is not in Mathlib.

## The new content

* `sum_choose_mul_stirlingSecond` — the **binomial transform of the second-kind
  Stirling numbers**:

    ∑_{i≤n} C(n,i)·S(i,j) = S(n+1, j+1).

  Proved by induction on `n`, using only Pascal's rule and the Stirling recurrence
  `S(n+1,k+1) = (k+1)·S(n,k+1) + S(n,k)`.  The inductive step closes because two
  boundary terms vanish (`S(0,j+1)=0` and `C(n,n+1)=0`).  This identity is *not* in
  Mathlib.

* `sum_range_choose_mul_stirlingSecond` — the immediate corollary

    ∑_{i<m} C(m,i)·S(i,j) = (j+1)·S(m, j+1).

* `eulerPoly_recurrence_alg` — the headline: **(★) over any commutative ring**,
  proved with no appeal to analysis.  The strategy substitutes the Stirling closed
  form `Eₘ = ∑_{k≤m} S(m,k)·k!·Xᵏ·(1−X)^{m−k}` (`stirlingForm`, the Frobenius
  identity `eulerPoly_eq_stirlingForm` from the sibling line) into both sides of
  (★) and reduces the resulting polynomial identity, via a double-sum interchange,
  to the binomial transform above.

* `eulerPoly_recurrence` — the parent's exact `ℝ[X]` statement, re-derived here as a
  specialisation of `eulerPoly_recurrence_alg`: the analytic theorem now has an
  analysis-free proof (and is in fact a shadow of a ring-theoretic identity).

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and
`sorry`-free.
-/

namespace GeometricSeriesOQ08OQ01OQ01OQ01OQ02OQ01OQ01

open Finset Nat Polynomial

/-! ## Part 1: the binomial transform of the Stirling numbers (new)

`∑_{i≤n} C(n,i)·S(i,j) = S(n+1, j+1)`, proved purely from Pascal's rule and the
Stirling recurrence.  This is the combinatorial engine of the analysis-free proof.
-/

/-- **Binomial transform of Stirling numbers of the second kind.**
`∑_{i≤n} C(n,i)·S(i,j) = S(n+1, j+1)`.  (Not in Mathlib.) -/
theorem sum_choose_mul_stirlingSecond (n j : ℕ) :
    ∑ i ∈ range (n + 1), n.choose i * Nat.stirlingSecond i j
      = Nat.stirlingSecond (n + 1) (j + 1) := by
  induction n generalizing j with
  | zero =>
    rw [Finset.sum_range_one, Nat.choose_self, one_mul,
        Nat.stirlingSecond_succ_succ, Nat.stirlingSecond_zero_succ, mul_zero, zero_add]
  | succ n ih =>
    rcases j with _ | j'
    · -- column `j = 0`: only the `i = 0` term survives and `S(n+1,1) = 1`.
      rw [Nat.stirlingSecond_one_right, Finset.sum_eq_single 0]
      · simp [Nat.stirlingSecond_zero]
      · intro i _ hi0
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
        rw [Nat.stirlingSecond_succ_zero, mul_zero]
      · intro h; simp at h
    · -- the boundary-term shift lemma: `∑ g(i+1) = ∑ g i` since `g 0 = g(n+1) = 0`.
      have hcollapse :
          ∑ i ∈ range (n + 1), n.choose (i + 1) * Nat.stirlingSecond (i + 1) (j' + 1)
            = ∑ i ∈ range (n + 1), n.choose i * Nat.stirlingSecond i (j' + 1) := by
        have e1 := Finset.sum_range_succ'
          (fun i => n.choose i * Nat.stirlingSecond i (j' + 1)) (n + 1)
        have e2 := Finset.sum_range_succ
          (fun i => n.choose i * Nat.stirlingSecond i (j' + 1)) (n + 1)
        simp only [Nat.choose_zero_right, Nat.stirlingSecond_zero_succ, mul_zero,
          Nat.choose_succ_self, zero_mul, add_zero] at e1 e2
        omega
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.stirlingSecond_zero_succ, mul_zero, add_zero]
      have hsplit : ∀ i ∈ range (n + 1),
          (n + 1).choose (i + 1) * Nat.stirlingSecond (i + 1) (j' + 1)
            = n.choose i * Nat.stirlingSecond (i + 1) (j' + 1)
              + n.choose (i + 1) * Nat.stirlingSecond (i + 1) (j' + 1) := by
        intro i _; rw [Nat.choose_succ_succ, add_mul]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hcollapse]
      have hP : ∀ i ∈ range (n + 1),
          n.choose i * Nat.stirlingSecond (i + 1) (j' + 1)
            = (j' + 1) * (n.choose i * Nat.stirlingSecond i (j' + 1))
              + n.choose i * Nat.stirlingSecond i j' := by
        intro i _; rw [Nat.stirlingSecond_succ_succ]; ring
      rw [Finset.sum_congr rfl hP, Finset.sum_add_distrib, ← Finset.mul_sum,
          ih (j' + 1), ih j']
      conv_rhs => rw [Nat.stirlingSecond_succ_succ]
      ring

/-- The binomial transform over `range m` (the form used below):
`∑_{i<m} C(m,i)·S(i,j) = (j+1)·S(m, j+1)`. -/
theorem sum_range_choose_mul_stirlingSecond (m j : ℕ) :
    ∑ i ∈ range m, m.choose i * Nat.stirlingSecond i j
      = (j + 1) * Nat.stirlingSecond m (j + 1) := by
  have hstd := sum_choose_mul_stirlingSecond m j
  rw [Finset.sum_range_succ, Nat.choose_self, one_mul, Nat.stirlingSecond_succ_succ] at hstd
  exact Nat.add_right_cancel hstd

/-! ## Part 2: the polynomial reduction

Both sides of (★) (after multiplying out the Stirling closed form) collapse to the
same canonical sum
`∑_j C((j+1)!·S(m'+1,j+1))·X^{j+1}·(1−X)^{m'+1−j}`. -/

open GeometricSeriesOQ07OQ01OQ01

variable {R : Type*} [CommRing R]

/-- The canonical integrand of the convolution side, defined for all `(i, j)`. -/
private noncomputable def gterm (m' i j : ℕ) : R[X] :=
  ((m' + 1).choose i : R[X]) * C ((Nat.stirlingSecond i j * j ! : ℕ) : R)
    * X ^ (j + 1) * (1 - X) ^ (m' + 1 - j)

/-- The left-hand side of (★) in canonical form: multiplying the Stirling closed
form `N_{m'+1}` by `(1 − X)` raises every power and drops the (vanishing) `k = 0`
term, leaving `∑_j C((j+1)!·S(m'+1,j+1))·X^{j+1}·(1−X)^{m'+1−j}`. -/
theorem one_sub_X_mul_stirlingForm (m' : ℕ) :
    (1 - X) * (stirlingForm (m' + 1) : R[X])
      = ∑ j ∈ range (m' + 1),
          C (((j + 1)! * Nat.stirlingSecond (m' + 1) (j + 1) : ℕ) : R)
            * X ^ (j + 1) * (1 - X) ^ (m' + 1 - j) := by
  rw [stirlingForm, Finset.mul_sum, Finset.sum_range_succ']
  simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, map_zero, zero_mul, mul_zero, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ m' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have e1 : m' + 1 - (k + 1) = m' - k := by omega
  have e2 : m' + 1 - k = (m' - k) + 1 := by omega
  rw [e1, e2, Nat.mul_comm (Nat.stirlingSecond (m' + 1) (k + 1)) ((k + 1)!)]
  ring

/-- The right-hand (convolution) side of (★) in canonical form.  After substituting
the Stirling closed form, interchanging the double sum, and applying the binomial
transform `sum_range_choose_mul_stirlingSecond`, it reduces to exactly the same sum
as `one_sub_X_mul_stirlingForm`. -/
theorem X_mul_convolution_stirlingForm (m' : ℕ) :
    X * ∑ i ∈ range (m' + 1),
        ((m' + 1).choose i : R[X]) * stirlingForm i * (1 - X) ^ (m' + 1 - i)
      = ∑ j ∈ range (m' + 1),
          C (((j + 1)! * Nat.stirlingSecond (m' + 1) (j + 1) : ℕ) : R)
            * X ^ (j + 1) * (1 - X) ^ (m' + 1 - j) := by
  -- each `i`-slice becomes `∑_{j<m'+1} gterm m' i j` (extend the inner range; the
  -- added `j > i` terms vanish because `S(i,j) = 0`).
  rw [Finset.mul_sum]
  have hslice : ∀ i ∈ range (m' + 1),
      X * (((m' + 1).choose i : R[X]) * stirlingForm i * (1 - X) ^ (m' + 1 - i))
        = ∑ j ∈ range (m' + 1), gterm (R := R) m' i j := by
    intro i hi
    have hi' : i ≤ m' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [stirlingForm, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
    have hsub : range (i + 1) ⊆ range (m' + 1) := by
      intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro j hj
      have hj' : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have e1 : (i - j) + (m' + 1 - i) = m' + 1 - j := by omega
      simp only [gterm]
      rw [show m' + 1 - j = (i - j) + (m' + 1 - i) from e1.symm, pow_add]
      ring
    · intro j _ hj
      have hij : i < j := by
        simp only [Finset.mem_range, not_lt] at hj; omega
      simp [gterm, Nat.stirlingSecond_eq_zero_of_lt hij]
  rw [Finset.sum_congr rfl hslice, Finset.sum_comm]
  -- the double sum is now over a square; evaluate each `j`-slice.
  apply Finset.sum_congr rfl
  intro j _
  have hfac : ∑ i ∈ range (m' + 1), gterm (R := R) m' i j
      = (∑ i ∈ range (m' + 1),
          ((m' + 1).choose i : R[X]) * C ((Nat.stirlingSecond i j * j ! : ℕ) : R))
        * (X ^ (j + 1) * (1 - X) ^ (m' + 1 - j)) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _; simp only [gterm]; ring
  rw [hfac]
  -- the scalar bracket collapses to one constant via the binomial transform.
  have hnat : ∑ i ∈ range (m' + 1), (m' + 1).choose i * (Nat.stirlingSecond i j * j !)
      = (j + 1)! * Nat.stirlingSecond (m' + 1) (j + 1) := by
    have hpull : ∑ i ∈ range (m' + 1), (m' + 1).choose i * (Nat.stirlingSecond i j * j !)
        = j ! * ∑ i ∈ range (m' + 1), (m' + 1).choose i * Nat.stirlingSecond i j := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
    rw [hpull, sum_range_choose_mul_stirlingSecond, Nat.factorial_succ]; ring
  have hbracket : (∑ i ∈ range (m' + 1),
        ((m' + 1).choose i : R[X]) * C ((Nat.stirlingSecond i j * j ! : ℕ) : R))
      = C (((j + 1)! * Nat.stirlingSecond (m' + 1) (j + 1) : ℕ) : R) := by
    rw [← hnat, Nat.cast_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← map_natCast (C : R →+* R[X]) ((m' + 1).choose i), ← map_mul]
    congr 1
    push_cast
    ring
  rw [hbracket, mul_assoc]

/-! ## Part 3: the analysis-free Eulerian recurrence -/

/-- **The Eulerian (★∞) recurrence, proved purely algebraically.**  For every `m`
and over any commutative ring `R`,

  `(1 − X)·Eₘ = 0ᵐ·(1 − X)^{m+1} + X·∑_{i<m} C(m,i)·Eᵢ·(1 − X)^{m−i}`   in `R[X]`,

with no appeal to analysis.  For `m = 0` it is `(1 − X)·1 = (1 − X)`; for
`m = m'+1` both sides collapse, via the Stirling closed form and the binomial
transform `sum_choose_mul_stirlingSecond`, to the common canonical sum. -/
theorem eulerPoly_recurrence_alg (m : ℕ) :
    (1 - X) * (eulerPoly m : R[X])
      = (0 : R[X]) ^ m * (1 - X) ^ (m + 1)
        + X * ∑ i ∈ range m, (m.choose i : R[X]) * eulerPoly i * (1 - X) ^ (m - i) := by
  rcases m with _ | m'
  · simp [eulerPoly_zero]
  · have h0 : (0 : R[X]) ^ (m' + 1) = 0 := by simp
    rw [h0, zero_mul, zero_add, eulerPoly_eq_stirlingForm]
    have hsum : (∑ i ∈ range (m' + 1),
          ((m' + 1).choose i : R[X]) * eulerPoly i * (1 - X) ^ (m' + 1 - i))
        = ∑ i ∈ range (m' + 1),
          ((m' + 1).choose i : R[X]) * stirlingForm i * (1 - X) ^ (m' + 1 - i) := by
      apply Finset.sum_congr rfl; intro i _; rw [eulerPoly_eq_stirlingForm]
    rw [hsum, one_sub_X_mul_stirlingForm, X_mul_convolution_stirlingForm]

/-- **The parent's `ℝ[X]` recurrence, re-derived analysis-free.**  This is verbatim
the statement `geometric-series-oq-08-oq-01-oq-01-oq-01-oq-02-oq-01.eulerPoly_recurrence`,
whose original proof goes through real analysis; here it is the `R = ℝ`
specialisation of the ring-theoretic `eulerPoly_recurrence_alg`. -/
theorem eulerPoly_recurrence (m : ℕ) :
    (1 - X) * (eulerPoly m : ℝ[X])
      = (0 : ℝ[X]) ^ m * (1 - X) ^ (m + 1)
        + X * ∑ i ∈ range m, (m.choose i : ℝ[X]) * eulerPoly i * (1 - X) ^ (m - i) :=
  eulerPoly_recurrence_alg m

end GeometricSeriesOQ08OQ01OQ01OQ01OQ02OQ01OQ01
