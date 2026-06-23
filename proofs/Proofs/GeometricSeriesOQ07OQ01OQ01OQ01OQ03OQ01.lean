/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-01-oq-03-oq-01:
# The Eulerian row sum `∑ⱼ ⟨m,j⟩ = m!` as the `m`-th forward difference of Worpitzky's identity

The parent entry `geometric-series-oq-07-oq-01-oq-01-oq-01-oq-03` proved **Worpitzky's identity**

  `worpitzky` :  `nᵐ = ∑_{j=0}^{m} ⟨m,j⟩ · C(n+j, m)`   (an identity of natural numbers),

expressing the power basis `nᵐ` in the shifted-binomial basis `C(n+j, m)` with the Eulerian
numbers `⟨m,j⟩` (`eulerian m j`) as connection coefficients.  Its open question oq-01 asks for the
**row sum** `∑_{j} ⟨m,j⟩ = m!` to be *deduced from Worpitzky's identity by the `m`-th forward
difference of `nᵐ`* — the application that motivates Worpitzky in the first place.

## Method

Let `Δ = Δ_[1]` be the forward difference operator `(Δf)(n) = f(n+1) − f(n)` on functions
`ℕ → ℤ`, and write `Δᵐ` for its `m`-fold iterate.  The operator `Δᵐ` evaluated at `0` is a linear
functional that annihilates polynomials of degree `< m` and reads off the leading coefficient
times `m!` of a degree-`m` polynomial.  Applying it to both sides of Worpitzky's identity:

* the **left side** `n ↦ nᵐ` is monic of degree `m`, so `Δᵐ(nᵐ)(0) = m!`
  (Mathlib's `fwdDiff_iter_eq_factorial`);
* on the **right side**, `Δᵐ` distributes over the finite sum (linearity) and over each
  scalar `⟨m,j⟩`, and `Δᵐ(C(·+j, m))(0) = C(j, 0) = 1` for every `j`
  (Mathlib's `fwdDiff_iter_choose`, which gives `Δᵐ C(·, m) = C(·, 0) = 1`).

Hence `m! = ∑_{j} ⟨m,j⟩ · 1 = ∑_{j} ⟨m,j⟩`.

This is a genuinely different derivation from the sibling
`geometric-series-oq-07-oq-01-oq-01-oq-01-oq-01`, which obtains the same row sum analytically by
evaluating the Eulerian polynomial `Eₘ` at `X = 1`.  Here the row sum is read off the
*finite-difference calculus* applied to Worpitzky's combinatorial identity.

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01OQ01OQ03

namespace GeometricSeriesOQ07OQ01OQ01OQ01OQ03OQ01

open Finset Nat fwdDiff
open GeometricSeriesOQ07OQ01OQ01OQ01 GeometricSeriesOQ07OQ01OQ01OQ01OQ03

/-! ## The two forward-difference inputs -/

/-- **The `m`-th forward difference of `n ↦ nᵐ` at `0` is `m!`.**  This is Mathlib's
`fwdDiff_iter_eq_factorial` transported from the domain `ℤ` to the domain `ℕ`: both sides expand,
via `fwdDiff_iter_eq_sum_shift`, to the same alternating binomial sum
`∑ₖ (-1)^{m-k} C(m,k) kᵐ`, which equals `m!`. -/
theorem fwdDiff_iter_pow_self (m : ℕ) :
    Δ_[1] ^[m] (fun n : ℕ ↦ ((n : ℤ) ^ m)) 0 = (m ! : ℤ) := by
  -- The factorial value on the integer domain.
  have hz : Δ_[1] ^[m] (fun r : ℤ ↦ r ^ m) 0 = (m ! : ℤ) := by
    have := congrFun (fwdDiff_iter_eq_factorial (R := ℤ) (n := m)) 0
    simpa using this
  -- Expand both `Δᵐ … 0` as the same shift-sum and identify them termwise.
  rw [fwdDiff_iter_eq_sum_shift] at hz ⊢
  rw [← hz]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp

/-- **The `m`-th forward difference of `n ↦ C(n+j, m)` at `0` is `1`**, for every shift `j`.
`Δᵐ` applied to `n ↦ C(n, m)` is the constant `n ↦ C(n, 0) = 1` (`fwdDiff_iter_choose`); composing
with the shift `n ↦ n + j` (`fwdDiff_iter_comp_add`) evaluates it at `j`, still `C(j, 0) = 1`. -/
theorem fwdDiff_iter_choose_shift (m j : ℕ) :
    Δ_[1] ^[m] (fun n : ℕ ↦ ((n + j).choose m : ℤ)) 0 = 1 := by
  have hcomp :
      Δ_[1] ^[m] (fun n : ℕ ↦ ((n + j).choose m : ℤ)) 0
        = (Δ_[1] ^[m] (fun x : ℕ ↦ (x.choose m : ℤ))) (0 + j) :=
    fwdDiff_iter_comp_add (1 : ℕ) (fun x : ℕ ↦ (x.choose m : ℤ)) j m 0
  rw [hcomp]
  have hc : Δ_[1] ^[m] (fun x : ℕ ↦ (x.choose m : ℤ)) = (fun x : ℕ ↦ (x.choose 0 : ℤ)) := by
    simpa using fwdDiff_iter_choose 0 m
  rw [hc]
  simp

/-! ## Worpitzky's identity over `ℤ` -/

/-- Worpitzky's identity, cast to `ℤ`: `(n:ℤ)ᵐ = ∑_{j=0}^{m} ⟨m,j⟩ · C(n+j, m)`. -/
theorem worpitzky_int (m n : ℕ) :
    ((n : ℤ) ^ m) = ∑ j ∈ range (m + 1), (eulerian m j : ℤ) * ((n + j).choose m : ℤ) := by
  exact_mod_cast worpitzky m n

/-! ## The Eulerian row sum -/

/-- **The Eulerian row sum, via Worpitzky's identity and the `m`-th forward difference.**
`∑_{j=0}^{m} ⟨m,j⟩ = m!`.  Applying `Δ_[1] ^[m]` at `0` to Worpitzky's identity sends the
left-hand side `n ↦ nᵐ` to `m!` and each right-hand summand `⟨m,j⟩·C(n+j,m)` to `⟨m,j⟩·1`. -/
theorem eulerian_row_sum (m : ℕ) : ∑ j ∈ range (m + 1), eulerian m j = m ! := by
  have key : (m ! : ℤ) = ∑ j ∈ range (m + 1), (eulerian m j : ℤ) := by
    calc
      (m ! : ℤ)
          = Δ_[1] ^[m] (fun n : ℕ ↦ ((n : ℤ) ^ m)) 0 := (fwdDiff_iter_pow_self m).symm
      _ = Δ_[1] ^[m]
            (fun n : ℕ ↦ ∑ j ∈ range (m + 1), (eulerian m j : ℤ) * ((n + j).choose m : ℤ)) 0 := by
            have hpt :
                (fun n : ℕ ↦ ((n : ℤ) ^ m))
                  = (fun n : ℕ ↦ ∑ j ∈ range (m + 1),
                      (eulerian m j : ℤ) * ((n + j).choose m : ℤ)) := by
              ext n
              exact worpitzky_int m n
            rw [hpt]
      _ = ∑ j ∈ range (m + 1),
            Δ_[1] ^[m] (fun n : ℕ ↦ (eulerian m j : ℤ) * ((n + j).choose m : ℤ)) 0 := by
            have hfun :
                (fun n : ℕ ↦ ∑ j ∈ range (m + 1), (eulerian m j : ℤ) * ((n + j).choose m : ℤ))
                  = ∑ j ∈ range (m + 1),
                      (fun n : ℕ ↦ (eulerian m j : ℤ) * ((n + j).choose m : ℤ)) := by
              ext n
              rw [Finset.sum_apply]
            rw [hfun, fwdDiff_iter_finset_sum, Finset.sum_apply]
      _ = ∑ j ∈ range (m + 1), (eulerian m j : ℤ) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            have hsmul :
                (fun n : ℕ ↦ (eulerian m j : ℤ) * ((n + j).choose m : ℤ))
                  = (eulerian m j : ℤ) • (fun n : ℕ ↦ ((n + j).choose m : ℤ)) := by
              ext n; simp
            rw [hsmul, fwdDiff_iter_const_smul, Pi.smul_apply, fwdDiff_iter_choose_shift,
              smul_eq_mul, mul_one]
  have hZ : ((∑ j ∈ range (m + 1), eulerian m j : ℕ) : ℤ) = (m ! : ℤ) := by
    rw [Nat.cast_sum]
    exact key.symm
  exact_mod_cast hZ

/-! ## Low-order sanity checks -/

/-- `∑_{j} ⟨3,j⟩ = 1 + 4 + 1 = 6 = 3!`. -/
example : ∑ j ∈ range 4, eulerian 3 j = 6 := by decide

/-- The row sum is `m!`, restated as the count of permutations of `{1,…,m}`. -/
example (m : ℕ) : ∑ j ∈ range (m + 1), eulerian m j = m ! := eulerian_row_sum m

end GeometricSeriesOQ07OQ01OQ01OQ01OQ03OQ01
