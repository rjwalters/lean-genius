/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01:
# The Eulerian numbers via the combinatorial triangle recurrence

The parent entry `geometric-series-oq-07-oq-01-oq-01` builds the **Eulerian
polynomial** `eulerPoly m` by its classical first-order differential recurrence

  E₀ = 1,   E_{m+1} = X·(1-X)·E'ₘ + (m+1)·X·Eₘ,

and identifies it (Frobenius' identity) with the Stirling closed form.  Its
sibling `…-oq-02` reads palindromicity off the *coefficient recurrence*

  coeff(E_{m+1}, j+2) = (j+2)·coeff(Eₘ, j+2) − (j+1)·coeff(Eₘ, j+1)
                          + (m+1)·coeff(Eₘ, j+1),

extracted from the differential recurrence.  Neither entry connects the
coefficients to the textbook **combinatorial** definition of the Eulerian
numbers `⟨m,k⟩` — the number of permutations of `{1,…,m}` with exactly `k`
descents — which is governed by the triangle recurrence

  ⟨m,k⟩ = (k+1)·⟨m-1,k⟩ + (m-k)·⟨m-1,k-1⟩,   ⟨0,0⟩ = 1.

This entry answers the parent's recorded open question
`geometric-series-oq-07-oq-01-oq-01-oq-01`: we define the Eulerian numbers
`eulerian m k` directly by this combinatorial triangle recurrence and prove that
they are **exactly** the coefficients of the Eulerian polynomial,

  `coeff_eulerPoly_eq_eulerian` :  coeff(Eₘ, k+1) = ⟨m,k⟩   (m ≥ 1),

over an arbitrary commutative ring.  The proof is a clean induction on `m`: the
boundary index `k = 0` uses `coeff_eulerPoly_succ_one` (giving `⟨m,0⟩ = 1`), and
the generic index `k+1` is exactly the differential-recurrence coefficient
identity `coeff_eulerPoly_succ_add_two`, whose two lower-order terms collapse
into the triangle recurrence's weight `(m-k)`.  (Over a ring the weight is
`m - k`; over `ℕ` it is truncated subtraction, and the two agree precisely where
`⟨m,k⟩ ≠ 0`, i.e. `k ≤ m`.)

As corollaries that tie the combinatorial numbers back to the analytic origin we
obtain the **row sum** `∑_{k=0}^{m-1} ⟨m,k⟩ = m!` (`eulerian_row_sum`, the count
of all permutations, recovered from `Eₘ(1) = m!`) and the **combinatorial
palindromicity** `⟨m,k⟩ = ⟨m,m-1-k⟩` (`eulerian_symm`, read off the sibling's
`eulerPoly_coeff_symm`).

Mathlib has no Eulerian numbers, so the combinatorial triangle and its
identification with the geometric moment numerator are new here.  Everything is
`0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ02

namespace GeometricSeriesOQ07OQ01OQ01OQ01

open Polynomial Finset

open GeometricSeriesOQ07OQ01OQ01
  (eulerPoly eulerPoly_zero eulerPoly_succ eulerPoly_one eval_eulerPoly_one)

open GeometricSeriesOQ07OQ01OQ01OQ02
  (coeff_eulerPoly_zero_eq_zero coeff_eulerPoly_succ_one coeff_eulerPoly_succ_add_two
   eulerPoly_coeff_symm eulerPoly_natDegree)

/-! ## Part 1: the Eulerian numbers `⟨m,k⟩`

We define `eulerian m k` directly by the combinatorial triangle recurrence.  The
four pattern branches encode `⟨0,0⟩ = 1`, `⟨0,k+1⟩ = 0`, `⟨m+1,0⟩ = 1` and the
recurrence proper `⟨m+1,k+1⟩ = (k+2)·⟨m,k+1⟩ + (m-k)·⟨m,k⟩`. -/

/-- The **Eulerian number** `⟨m,k⟩`: the number of permutations of `{1,…,m}` with
exactly `k` descents, defined by the combinatorial triangle recurrence. -/
def eulerian : ℕ → ℕ → ℕ
  | 0,     0      => 1
  | 0,     (_ + 1) => 0
  | (_ + 1), 0      => 1
  | (m + 1), (k + 1) => (k + 2) * eulerian m (k + 1) + (m - k) * eulerian m k

@[simp] theorem eulerian_zero_zero : eulerian 0 0 = 1 := rfl

@[simp] theorem eulerian_zero_succ (k : ℕ) : eulerian 0 (k + 1) = 0 := rfl

@[simp] theorem eulerian_succ_zero (m : ℕ) : eulerian (m + 1) 0 = 1 := rfl

theorem eulerian_succ_succ (m k : ℕ) :
    eulerian (m + 1) (k + 1) = (k + 2) * eulerian m (k + 1) + (m - k) * eulerian m k := rfl

/-- The first column is `⟨m,0⟩ = 1` (the identity permutation is the unique one
with no descents). -/
theorem eulerian_right_zero (m : ℕ) : eulerian m 0 = 1 := by cases m <;> rfl

/-- Row 1 of the triangle: `⟨1,0⟩ = 1`, and `⟨1,k+1⟩ = 0`. -/
theorem eulerian_one (k : ℕ) : eulerian 1 k = if k = 0 then 1 else 0 := by
  cases k with
  | zero => rfl
  | succ k => simp [eulerian_succ_succ]

/-- The triangle vanishes above the diagonal: `⟨m,k⟩ = 0` for `k > m`
(a permutation of `m` letters has at most `m-1` descents). -/
theorem eulerian_eq_zero_of_lt : ∀ {m k : ℕ}, m < k → eulerian m k = 0 := by
  intro m
  induction m with
  | zero =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rfl
  | succ n ih =>
    intro k hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [eulerian_succ_succ, ih (by omega), ih (by omega)]
    ring

/-! ## Part 2: the identification with the coefficients of `eulerPoly`

The heart of the entry.  We work over an arbitrary commutative ring `R`. -/

variable {R : Type*} [CommRing R]

/-- **The Eulerian numbers are the coefficients of the Eulerian polynomial.**
For `m ≥ 1`, `coeff(Eₘ, k+1) = ⟨m,k⟩`.  This upgrades the parent's
"differential-recurrence + closed-form" identification of `eulerPoly` to the
textbook combinatorial definition of the Eulerian numbers. -/
theorem coeff_eulerPoly_eq_eulerian {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    (eulerPoly m : R[X]).coeff (k + 1) = (eulerian m k : R) := by
  induction m, hm using Nat.le_induction generalizing k with
  | base =>
    rw [eulerPoly_one, eulerian_one]
    cases k with
    | zero => simp
    | succ k =>
      rw [coeff_X]
      simp
  | succ m hm ih =>
    cases k with
    | zero =>
      -- boundary index: ⟨m+1,0⟩ = 1
      rw [coeff_eulerPoly_succ_one, coeff_eulerPoly_zero_eq_zero hm,
        show (1 : ℕ) = 0 + 1 from rfl, ih 0]
      rw [eulerian_right_zero m, eulerian_right_zero (m + 1)]
      push_cast; ring
    | succ k =>
      -- generic index: the triangle recurrence
      rw [show k + 1 + 1 = k + 2 from rfl, coeff_eulerPoly_succ_add_two m k,
        show k + 2 = k + 1 + 1 from rfl, ih (k + 1), ih k, eulerian_succ_succ]
      by_cases hk : k ≤ m
      · push_cast [Nat.cast_sub hk]; ring
      · have hz : eulerian m k = 0 := eulerian_eq_zero_of_lt (by omega)
        rw [hz]; push_cast; ring

/-! ## Part 3: corollaries tying the combinatorial numbers to the analytic origin -/

/-- **Row sum.**  The Eulerian numbers in row `m` sum to `m!` — every one of the
`m!` permutations of `{1,…,m}` has some number `0 ≤ k ≤ m-1` of descents.  This is
recovered from the analytic identity `Eₘ(1) = m!` of the parent entry. -/
theorem eulerian_row_sum {m : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ range m, eulerian m k = Nat.factorial m := by
  have h : ((∑ k ∈ range m, eulerian m k : ℕ) : ℝ) = (Nat.factorial m : ℝ) := by
    push_cast
    have hdeg : (eulerPoly m : ℝ[X]).natDegree = m := eulerPoly_natDegree hm
    have heval : (eulerPoly m : ℝ[X]).eval 1 = (Nat.factorial m : ℝ) := eval_eulerPoly_one m
    rw [eval_eq_sum_range, hdeg] at heval
    simp only [one_pow, mul_one] at heval
    rw [Finset.sum_range_succ', coeff_eulerPoly_zero_eq_zero hm, add_zero] at heval
    rw [← heval]
    exact Finset.sum_congr rfl fun i _ => (coeff_eulerPoly_eq_eulerian hm i).symm
  exact_mod_cast h

/-- **Combinatorial palindromicity** `⟨m,k⟩ = ⟨m,m-1-k⟩`: the descent statistic is
symmetric under reversing a permutation.  Read off the sibling entry's coefficient
symmetry `eulerPoly_coeff_symm`. -/
theorem eulerian_symm {m : ℕ} (hm : 1 ≤ m) {k : ℕ} (hk : k ≤ m - 1) :
    eulerian m k = eulerian m (m - 1 - k) := by
  have e1 : (eulerPoly m : ℤ[X]).coeff (k + 1) = (eulerian m k : ℤ) :=
    coeff_eulerPoly_eq_eulerian hm k
  have e2 : (eulerPoly m : ℤ[X]).coeff (m - 1 - k + 1) = (eulerian m (m - 1 - k) : ℤ) :=
    coeff_eulerPoly_eq_eulerian hm (m - 1 - k)
  have hsymm : (eulerPoly m : ℤ[X]).coeff (k + 1)
      = (eulerPoly m : ℤ[X]).coeff (m + 1 - (k + 1)) := eulerPoly_coeff_symm hm (k + 1)
  rw [show m + 1 - (k + 1) = m - 1 - k + 1 from by omega] at hsymm
  have : (eulerian m k : ℤ) = (eulerian m (m - 1 - k) : ℤ) := by rw [← e1, ← e2, hsymm]
  exact_mod_cast this

/-! ## Part 4: the triangle, low rows (sanity checks)

  ⟨1,·⟩ = 1
  ⟨2,·⟩ = 1, 1
  ⟨3,·⟩ = 1, 4, 1
  ⟨4,·⟩ = 1, 11, 11, 1
  ⟨5,·⟩ = 1, 26, 66, 26, 1 -/

example : eulerian 1 0 = 1 := rfl
example : eulerian 2 0 = 1 ∧ eulerian 2 1 = 1 := by decide
example : eulerian 3 0 = 1 ∧ eulerian 3 1 = 4 ∧ eulerian 3 2 = 1 := by decide
example : eulerian 4 0 = 1 ∧ eulerian 4 1 = 11 ∧ eulerian 4 2 = 11 ∧ eulerian 4 3 = 1 := by decide
example : eulerian 5 1 = 26 ∧ eulerian 5 2 = 66 := by decide
example : ∑ k ∈ range 4, eulerian 4 k = 24 := by decide

end GeometricSeriesOQ07OQ01OQ01OQ01
