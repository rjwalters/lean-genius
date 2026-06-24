/-
  Multivariate (r-fold) Vandermonde via Generating Functions

  Open Question (arithmetic-series-oq-02-oq-02-oq-03-oq-02):
  "Lift the two-factor generating-function proof of the parallel Vandermonde
   identity to arbitrarily many factors.  In the formal power series ring, the
   product of r negative-binomial generating functions is again a negative
   binomial generating function (just exponent addition), so extracting a single
   coefficient yields the r-fold Vandermonde convolution."

  The sibling file (ArithmeticSeriesOQ02OQ02OQ03) proves the TWO-factor identity
      Σ_{i+j=n} C(i+a,a)·C(j+b,b) = C(n+a+b+1, a+b+1)
  by writing negBin(a)·negBin(b) = negBin(a+b+1) and reading off coefficients.

  Here we generalize to an arbitrary finite family (a_i)_{i∈s}:
      ∏_{i∈s} negBin(a_i) = geom ^ (Σ_{i∈s} (a_i + 1))
  which is `Finset.prod_pow_eq_pow_sum` — the SAME "algebra replaces
  combinatorics" phenomenon, now across r factors.  Extracting the n-th
  coefficient (via `PowerSeries.coeff_prod`, a sum over `finsuppAntidiag`) gives
  the multivariate Vandermonde convolution
      Σ_{l : Σ l_i = n} ∏_{i∈s} C(l_i + a_i, a_i) = C(n + Σ(a_i+1) - 1, …).

  This file is self-contained: it restates the geometric-series / simplicial
  scaffolding (geom, negBin, coeff_negBin, hockey stick) so it does not depend on
  the sibling file's compilation.

  Tags: combinatorics, generating-functions, power-series, vandermonde,
        multivariate, formal-proof
-/

import Mathlib

namespace ArithmeticSeriesOQ02OQ02OQ03OQ02

open Finset BigOperators

-- ============================================================
-- Part 0: Simplicial Numbers and the Hockey Stick
-- ============================================================

/-- Simplicial numbers: S_k(n) = C(n+k, k). -/
def simplicial (k n : ℕ) : ℕ := Nat.choose (n + k) k

@[simp]
theorem simplicial_zero (n : ℕ) : simplicial 0 n = 1 := by
  simp [simplicial, Nat.choose_zero_right]

@[simp]
theorem simplicial_start (k : ℕ) : simplicial k 0 = 1 := by
  simp [simplicial, Nat.choose_self]

/-- Pascal recurrence for simplicial numbers. -/
theorem simplicial_succ (k n : ℕ) :
    simplicial (k + 1) (n + 1) = simplicial (k + 1) n + simplicial k (n + 1) := by
  simp only [simplicial]
  rw [show n + 1 + (k + 1) = (n + k + 1) + 1 from by ring,
      show n + (k + 1) = n + k + 1 from by ring,
      show n + 1 + k = n + k + 1 from by ring]
  linarith [Nat.choose_succ_succ (n + k + 1) k]

/-- Hockey stick identity for simplicial numbers. -/
theorem hockey_stick (k n : ℕ) :
    ∑ i ∈ range (n + 1), simplicial k i = simplicial (k + 1) n := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, ih]; exact (simplicial_succ k n).symm

-- ============================================================
-- Part I: Formal Power Series Scaffolding
-- ============================================================

noncomputable section

open PowerSeries

/-- The geometric series g = Σ_{n≥0} x^n, representing 1/(1-x). -/
def geom : PowerSeries ℕ := PowerSeries.mk (fun _ => 1)

/-- The negative binomial generating function negBin(k) = g^{k+1} = (1-x)^{-(k+1)};
    its n-th coefficient is C(n+k, k) = simplicial k n. -/
def negBin (k : ℕ) : PowerSeries ℕ := geom ^ (k + 1)

/-- The geometric series has all coefficients equal to 1. -/
theorem coeff_geom (n : ℕ) : PowerSeries.coeff n geom = 1 := by
  simp [geom, PowerSeries.coeff_mk]

/-- The n-th coefficient of negBin(k) is the simplicial number C(n+k, k).
    Induction on k using the Cauchy product and the hockey stick. -/
theorem coeff_negBin (k n : ℕ) :
    PowerSeries.coeff n (negBin k) = simplicial k n := by
  induction k generalizing n with
  | zero =>
    simp [negBin, pow_one, coeff_geom, simplicial, Nat.choose_zero_right]
  | succ k ih =>
    have hprod : negBin (k + 1) = negBin k * geom := by
      simp only [negBin]; rw [pow_succ]
    rw [hprod, PowerSeries.coeff_mul]
    have hterm : ∀ p ∈ Finset.antidiagonal n,
        PowerSeries.coeff p.1 (negBin k) * PowerSeries.coeff p.2 geom =
          simplicial k p.1 := by
      intro p _; rw [ih, coeff_geom, mul_one]
    rw [Finset.sum_congr rfl hterm,
        Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i _ => simplicial k i)]
    exact hockey_stick k n

-- ============================================================
-- Part II: The r-fold Algebraic Product Formula
-- ============================================================

/-- **The multivariate product formula.**

    The product of the negative-binomial generating functions `negBin (a i)`
    over a finite index set `s` is again a power of the geometric series:
        ∏_{i∈s} (1-x)^{-(a_i+1)} = (1-x)^{-(Σ_{i∈s}(a_i+1))}.

    Because `negBin k = geom ^ (k+1)`, this is precisely exponent addition,
    `Finset.prod_pow_eq_pow_sum`.  The entire combinatorial content of the
    r-fold Vandermonde identity is captured by this single algebraic step —
    exactly as the two-factor `negBin_mul` is one `pow_add`. -/
theorem negBin_prod {ι : Type*} (s : Finset ι) (a : ι → ℕ) :
    ∏ i ∈ s, negBin (a i) = geom ^ (∑ i ∈ s, (a i + 1)) := by
  simp only [negBin]
  exact Finset.prod_pow_eq_pow_sum s (fun i => a i + 1) geom

/-- The `n`-th coefficient of `geom ^ (k+1)` is the simplicial number `C(n+k,k)`,
    a restatement of `coeff_negBin` through `negBin k = geom ^ (k+1)`. -/
theorem coeff_geom_pow_succ (k n : ℕ) :
    PowerSeries.coeff n (geom ^ (k + 1)) = simplicial k n := by
  simpa [negBin] using coeff_negBin k n

-- ============================================================
-- Part III: The Multivariate Vandermonde Identity
-- ============================================================

/-- **Multivariate Vandermonde, exact coefficient form.**

    The r-fold convolution sum equals the `n`-th coefficient of the single
    power series `geom ^ (Σ_{i∈s}(a_i+1))`:
        Σ_{Σ l_i = n} ∏_{i∈s} C(l_i + a_i, a_i)
          = [x^n] (1-x)^{-(Σ_{i∈s}(a_i+1))}.

    The left-hand sum ranges over `finsuppAntidiag s n`, i.e. all ways of
    writing `n` as `Σ_{i∈s} l_i` with `l_i ≥ 0`.  The proof reads off the
    coefficient of `∏_{i∈s} negBin (a_i)` two ways: `PowerSeries.coeff_prod`
    (a `finsuppAntidiag` sum) on one side and `negBin_prod` (a single power)
    on the other.

    No nonemptiness hypothesis is needed; the empty-index case degenerates to
    `[x^n] 1 = [n = 0]`. -/
theorem multivariate_vandermonde_gf {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℕ) (n : ℕ) :
    ∑ l ∈ finsuppAntidiag s n, ∏ i ∈ s, simplicial (a i) (l i) =
      PowerSeries.coeff n (geom ^ (∑ i ∈ s, (a i + 1))) := by
  rw [← negBin_prod, PowerSeries.coeff_prod]
  refine Finset.sum_congr rfl (fun l _ => Finset.prod_congr rfl (fun i _ => ?_))
  rw [coeff_negBin]

/-- **Multivariate Vandermonde, simplicial form.**

    For a nonempty index set `s`, the r-fold convolution of simplicial numbers
    is a single simplicial number:
        Σ_{Σ l_i = n} ∏_{i∈s} C(l_i + a_i, a_i)
          = C(n + (Σ_{i∈s}(a_i+1)) - 1, (Σ_{i∈s}(a_i+1)) - 1).

    Specializing to a two-element index set with exponents `a, b` recovers the
    two-factor parallel Vandermonde (exponent `a + b + 1`).  Nonemptiness
    guarantees `Σ(a_i+1) ≥ 1`, so the `-1` is benign. -/
theorem multivariate_vandermonde {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (a : ι → ℕ) (n : ℕ) :
    ∑ l ∈ finsuppAntidiag s n, ∏ i ∈ s, simplicial (a i) (l i) =
      simplicial ((∑ i ∈ s, (a i + 1)) - 1) n := by
  rw [multivariate_vandermonde_gf]
  obtain ⟨M, hM⟩ : ∃ M, (∑ i ∈ s, (a i + 1)) = M + 1 := by
    obtain ⟨j, hj⟩ := hs
    have hpos : 1 ≤ ∑ i ∈ s, (a i + 1) :=
      le_trans (Nat.le_add_left 1 (a j))
        (Finset.single_le_sum (f := fun i => a i + 1) (fun i _ => Nat.zero_le _) hj)
    exact ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  rw [hM, coeff_geom_pow_succ]
  congr 1

-- ============================================================
-- Part IV: Specialization to `Fin (r+1)` (always nonempty)
-- ============================================================

/-- The multivariate Vandermonde over the full index set `Fin (r+1)`, which is
    automatically nonempty.  Taking `r = 1` is the two-factor identity; `r = 2`
    is the genuinely new three-factor convolution. -/
theorem multivariate_vandermonde_fin (r : ℕ) (a : Fin (r + 1) → ℕ) (n : ℕ) :
    ∑ l ∈ finsuppAntidiag (univ : Finset (Fin (r + 1))) n, ∏ i, simplicial (a i) (l i) =
      simplicial ((∑ i, (a i + 1)) - 1) n :=
  multivariate_vandermonde univ univ_nonempty a n

-- ============================================================
-- Part V: Concrete Verification
-- ============================================================

/-- Three-factor convolution with all exponents `0` collapses to a single
    simplicial number `C(n+2, 2)`: the number of ways to write `n = i+j+k`. -/
theorem threefold_const_zero (n : ℕ) :
    ∑ l ∈ finsuppAntidiag (univ : Finset (Fin 3)) n, ∏ i, simplicial 0 (l i) =
      simplicial 2 n := by
  have h := multivariate_vandermonde_fin 2 (fun _ => 0) n
  simpa [Fin.sum_univ_three] using h

/-- Concrete instance: the compositions of `2` into three nonnegative parts
    number `C(4,2) = 6`. -/
theorem check_threefold_count :
    ∑ l ∈ finsuppAntidiag (univ : Finset (Fin 3)) 2, ∏ i, simplicial 0 (l i) = 6 := by
  rw [threefold_const_zero]; decide

end

/-
  Summary

  This file lifts the two-factor generating-function proof of the parallel
  Vandermonde identity to an arbitrary finite family of factors — the
  "multivariate generating functions" open question.

  **The r-fold Approach**:
  1. coeff_negBin:  [x^n] geom^(k+1) = C(n+k,k)  (induction + hockey stick).
  2. negBin_prod:   ∏_{i∈s} negBin(a_i) = geom ^ (Σ_{i∈s}(a_i+1))
                    — `Finset.prod_pow_eq_pow_sum`, the r-factor analogue of the
                    two-factor `negBin_mul` (a single `pow_add`).
  3. multivariate_vandermonde_gf:  read off the n-th coefficient of the product
                    via `PowerSeries.coeff_prod` (a sum over `finsuppAntidiag`).
  4. multivariate_vandermonde:  the simplicial closed form for nonempty s.
  5. multivariate_vandermonde_fin:  the always-nonempty `Fin (r+1)` packaging;
                    r=1 is the two-factor identity, r=2 the new three-factor case.

  **Why This Matters**:
  The same algebraic principle that collapses the two-factor Vandermonde to one
  `pow_add` collapses the r-factor Vandermonde to one `prod_pow_eq_pow_sum`.
  All multivariate combinatorial content lives in the single coefficient
  extraction lemma — a clean illustration of the power of generating functions
  across arbitrarily many variables.

  0 literal `axiom` declarations; one `native_decide` numeric sanity check
  (see meta.json assumptions / Lean.ofReduceBool).
-/

end ArithmeticSeriesOQ02OQ02OQ03OQ02
