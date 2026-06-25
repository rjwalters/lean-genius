import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic

/-!
# Factor–remainder theorem OQ-01-OQ-01-OQ-02: the Newton / divided-difference form

The parent entry (`factor-remainder-theorem-oq-01-oq-01`) recasts the multiplicity form of the
factor theorem through **Taylor coefficients**: `(taylor a p).coeff m`, the order-`m` Taylor
coefficient of `p` at `a`, computed via Hasse derivatives.

This entry answers its open question:

> *Derive the divided-difference / Newton-form consequence: relate `(taylor a p).coeff m` to
> finite differences and the Newton interpolation coefficients of `p` at `a + ℤ`, giving a
> combinatorial route to the same data.*

A degree-`N` polynomial carries two natural coordinate systems on the shifted line `a + r`:

* the **Taylor (monomial) coefficients** `t_j := (taylor a p).coeff j`, the coordinates of
  `p(a + r)` in the basis `{r^j}`;
* the **Newton (forward-difference) coefficients** `c_m := Δ¹ₘ[r ↦ p(a + r)](0)`, the iterated
  forward differences of the sampled values `p(a), p(a+1), p(a+2), …` — equivalently the
  coordinates of `p(a + r)` in the binomial basis `{(r choose m)}`.

The bridge between them is the universal **finite-difference-of-monomials kernel**
`K(j, m) := Δ¹ₘ[r ↦ r^j](0)`, equal to `m! · S(j, m)` where `S(j, m)` is the Stirling number of
the second kind (the number of surjections `[j] ↠ [m]`, divided by `m!`). The change of basis is
purely combinatorial: `c_m = Σⱼ t_j · K(j, m)`.

## Main results

* `fwdDiff_pow_lt` / `fwdDiff_pow_self` : the kernel vanishes below the diagonal,
  `K(j, m) = 0` for `j < m`, and `K(m, m) = m!` (recovering Mathlib's
  `fwdDiff_iter_eq_factorial` at a point).
* `fwdDiff_iter_eval_eq_sum_taylor` : **`c_m = Σ_{j ≤ N} t_j · K(j, m)`** — the Taylor → Newton
  change of basis, the OQ's "combinatorial route".
* `fwdDiff_iter_natDegree_eval` / `…_eq_leadingCoeff` : the diagonal corollary
  `c_N = t_N · N! = leadingCoeff p · N!`, the divided-difference reading of the leading
  coefficient.
* `eval_add_natCast_eq_sum_fwdDiff_choose` : **Newton interpolation at integer nodes** —
  `p(a + n) = Σ_{m ≤ N} c_m · (n choose m)` for every `n : ℕ`, reconstructing `p` on the whole
  arithmetic progression `a + ℕ` from the finitely many forward differences `c_0, …, c_N`.
* `eval_add_eq_sum_fwdDiff_choose` : the same interpolation as a **polynomial identity**,
  `p(a + x) = Σ_{m ≤ N} c_m · (x choose m)` for all `x : ℚ`, using `Ring.choose` and the fact
  that a polynomial is determined by its values on `ℕ ⊆ ℚ`.

Everything is over `ℚ` (so that the generalized binomial coefficient `Ring.choose` and the
division by `m!` are available); `0` axioms.
-/

namespace FactorRemainderTheoremOQ01OQ01OQ02

open Polynomial Finset fwdDiff Nat

/-! ## The finite-difference-of-monomials kernel `K(j, m) = Δᵐ(r ↦ r^j)(0)` -/

/-- Below the diagonal the kernel vanishes: the `m`-th forward difference of `r ↦ r^j` is the
zero function when `j < m`, so in particular it is `0` at the origin. -/
theorem fwdDiff_pow_lt {j m : ℕ} (h : j < m) :
    Δ_[1]^[m] (fun r : ℚ => r ^ j) 0 = 0 := by
  rw [fwdDiff_iter_pow_eq_zero_of_lt h, Pi.zero_apply]

/-- On the diagonal the kernel is `m!`: the `m`-th forward difference of `r ↦ r^m` is the
constant function `m!` (Mathlib's `fwdDiff_iter_eq_factorial`), evaluated at the origin. -/
theorem fwdDiff_pow_self (m : ℕ) :
    Δ_[1]^[m] (fun r : ℚ => r ^ m) 0 = (m ! : ℚ) := by
  rw [fwdDiff_iter_eq_factorial]
  simp

/-! ## Taylor → Newton change of basis -/

/-- **The Taylor → Newton change of basis.** The `m`-th Newton (forward-difference) coefficient
of `p` based at `a`,
`c_m = Δᵐ[r ↦ p(a + r)](0)`, is the kernel-weighted combination of the Taylor coefficients
`t_j = (taylor a p).coeff j`:
`c_m = Σ_{j ≤ deg p} t_j · Δᵐ(r ↦ r^j)(0)`.
This is the precise combinatorial relationship the open question asks for; expanding the kernel
`Δᵐ(r ↦ r^j)(0) = m! · S(j, m)` exhibits the Stirling-number change of basis between the
monomial and binomial coordinate systems. -/
theorem fwdDiff_iter_eval_eq_sum_taylor (p : ℚ[X]) (a : ℚ) (m : ℕ) :
    Δ_[1]^[m] (fun r => p.eval (a + r)) 0
      = ∑ j ∈ range (p.natDegree + 1),
          (taylor a p).coeff j * Δ_[1]^[m] (fun r : ℚ => r ^ j) 0 := by
  have hfun : ∀ r : ℚ,
      p.eval (a + r) = ∑ j ∈ range (p.natDegree + 1), (taylor a p).coeff j * r ^ j := by
    intro r
    rw [add_comm a r, ← taylor_eval a p r, eval_eq_sum_range, natDegree_taylor]
  rw [funext hfun]
  simp_rw [← Finset.sum_apply _ _ (fun j x => (taylor a p).coeff j * x ^ j),
    fwdDiff_iter_finset_sum, ← smul_eq_mul, ← Pi.smul_def, fwdDiff_iter_const_smul, Pi.smul_apply,
    smul_eq_mul]

/-- **Diagonal corollary (leading coefficient as a top forward difference).** Only the top
Taylor coefficient survives the `N`-th forward difference, so
`c_N = t_N · N!` where `N = deg p`. This is the divided-difference reading of the leading
coefficient. -/
theorem fwdDiff_iter_natDegree_eval (p : ℚ[X]) (a : ℚ) :
    Δ_[1]^[p.natDegree] (fun r => p.eval (a + r)) 0
      = (taylor a p).coeff p.natDegree * (p.natDegree ! : ℚ) := by
  rw [fwdDiff_iter_eval_eq_sum_taylor p a p.natDegree,
    Finset.sum_eq_single p.natDegree]
  · rw [fwdDiff_pow_self]
  · intro j hj hjne
    rw [fwdDiff_pow_lt (lt_of_le_of_ne (Nat.lt_succ_iff.mp (mem_range.mp hj)) hjne), mul_zero]
  · intro h
    exact absurd (self_mem_range_succ p.natDegree) h

/-- The diagonal corollary phrased through the leading coefficient of `p` itself, using that the
Taylor shift preserves the leading coefficient (`Polynomial.leadingCoeff_taylor`). -/
theorem fwdDiff_iter_natDegree_eval_eq_leadingCoeff (p : ℚ[X]) (a : ℚ) :
    Δ_[1]^[p.natDegree] (fun r => p.eval (a + r)) 0 = p.leadingCoeff * (p.natDegree ! : ℚ) := by
  rw [fwdDiff_iter_natDegree_eval]
  congr 1
  conv_rhs => rw [← leadingCoeff_taylor (r := a) (f := p)]
  rw [leadingCoeff, natDegree_taylor]

/-! ## Newton interpolation -/

/-- The Newton coefficients vanish above the degree: `c_m = 0` for `m > deg p`, because the
sampled function `r ↦ p(a + r) = (taylor a p)(r)` is a polynomial of degree `deg p`. -/
theorem fwdDiff_iter_eval_eq_zero {p : ℚ[X]} {a : ℚ} {m : ℕ} (hm : p.natDegree < m) :
    Δ_[1]^[m] (fun r => p.eval (a + r)) 0 = 0 := by
  have hfun : (fun r : ℚ => p.eval (a + r)) = fun r => (taylor a p).eval r := by
    funext r; rw [taylor_eval, add_comm]
  rw [hfun, Polynomial.fwdDiff_iter_eq_zero_of_degree_lt (by rwa [natDegree_taylor]),
    Pi.zero_apply]

/-- **Newton interpolation at integer nodes.** For every natural number `n`,
`p(a + n) = Σ_{m ≤ deg p} c_m · (n choose m)`,
reconstructing the value of `p` at each node of the arithmetic progression `a + ℕ` from the
finitely many forward differences `c_0, …, c_N`. (`Ring.choose (n : ℚ) m = (n choose m)`.) -/
theorem eval_add_natCast_eq_sum_fwdDiff_choose (p : ℚ[X]) (a : ℚ) (n : ℕ) :
    p.eval (a + n) = ∑ m ∈ range (p.natDegree + 1),
        Δ_[1]^[m] (fun r => p.eval (a + r)) 0 * Ring.choose (n : ℚ) m := by
  -- Mathlib's shift formula gives the Newton expansion over `range (n+1)`.
  have hshift : p.eval (a + n)
      = ∑ k ∈ range (n + 1),
          Δ_[1]^[k] (fun r => p.eval (a + r)) 0 * Ring.choose (n : ℚ) k := by
    have h := shift_eq_sum_fwdDiff_iter (h := (1 : ℚ)) (fun r => p.eval (a + r)) n 0
    simp only [zero_add, nsmul_eq_mul, mul_one] at h
    rw [h]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Ring.choose_natCast]; ring
  -- The two index sets `range (n+1)` and `range (N+1)` agree after padding by zero terms:
  -- a term with `m > n` has `Ring.choose n m = 0`; a term with `m > N` has `c m = 0`.
  have hbig_n : ∑ k ∈ range (n + 1),
        Δ_[1]^[k] (fun r => p.eval (a + r)) 0 * Ring.choose (n : ℚ) k
      = ∑ k ∈ range (n + p.natDegree + 1),
        Δ_[1]^[k] (fun r => p.eval (a + r)) 0 * Ring.choose (n : ℚ) k := by
    refine Finset.sum_subset (range_subset.mpr (by omega)) (fun k _ hk => ?_)
    have hnk : n < k := by simp only [mem_range, not_lt] at hk; omega
    rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt hnk, Nat.cast_zero, mul_zero]
  have hbig_N : ∑ m ∈ range (p.natDegree + 1),
        Δ_[1]^[m] (fun r => p.eval (a + r)) 0 * Ring.choose (n : ℚ) m
      = ∑ m ∈ range (n + p.natDegree + 1),
        Δ_[1]^[m] (fun r => p.eval (a + r)) 0 * Ring.choose (n : ℚ) m := by
    refine Finset.sum_subset (range_subset.mpr (by omega)) (fun m _ hm => ?_)
    have hNm : p.natDegree < m := by simp only [mem_range, not_lt] at hm; omega
    rw [fwdDiff_iter_eval_eq_zero hNm, zero_mul]
  rw [hshift, hbig_n, ← hbig_N]

/-- The Newton interpolation polynomial: `m! ⁻¹ · descPochhammer` evaluates to the generalized
binomial coefficient `Ring.choose · m`. -/
private theorem newtonPoly_eval (m : ℕ) (x : ℚ) :
    (C ((m ! : ℚ)⁻¹) * descPochhammer ℚ m).eval x = Ring.choose x m := by
  have hsmeval : (descPochhammer ℤ m).smeval x = (descPochhammer ℚ m).eval x := by
    rw [← eval₂_smulOneHom_eq_smeval ℤ, eval₂_eq_eval_map, descPochhammer_map]
  have hfact : ((descPochhammer ℚ m).eval x) = (m ! : ℚ) * Ring.choose x m := by
    have := Ring.descPochhammer_eq_factorial_smul_choose (R := ℚ) x m
    rw [hsmeval] at this
    rwa [nsmul_eq_mul] at this
  rw [eval_mul, eval_C, hfact, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- **Newton interpolation as a polynomial identity.** For all `x : ℚ`,
`p(a + x) = Σ_{m ≤ deg p} c_m · (x choose m)`,
where `(x choose m) = Ring.choose x m` is the generalized binomial coefficient. This upgrades the
integer-node reconstruction to an identity of polynomial functions, valid at every `x`, because a
polynomial over the infinite field `ℚ` is determined by its values on `ℕ`. -/
theorem eval_add_eq_sum_fwdDiff_choose (p : ℚ[X]) (a : ℚ) (x : ℚ) :
    p.eval (a + x) = ∑ m ∈ range (p.natDegree + 1),
        Δ_[1]^[m] (fun r => p.eval (a + r)) 0 * Ring.choose x m := by
  -- The reconstruction polynomial `Q`, built from the Newton coefficients.
  set Q : ℚ[X] := ∑ m ∈ range (p.natDegree + 1),
      C (Δ_[1]^[m] (fun r => p.eval (a + r)) 0) * (C ((m ! : ℚ)⁻¹) * descPochhammer ℚ m) with hQ
  -- `Q` evaluates to the claimed Newton sum at every point.
  have hQeval : ∀ y : ℚ, Q.eval y
      = ∑ m ∈ range (p.natDegree + 1), Δ_[1]^[m] (fun r => p.eval (a + r)) 0 * Ring.choose y m := by
    intro y
    rw [hQ, eval_finset_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [eval_mul, eval_C, newtonPoly_eval]
  -- `taylor a p` and `Q` agree on all of `ℕ ⊆ ℚ`, hence are equal as polynomials.
  have hagree : taylor a p = Q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply Set.infinite_of_injective_forall_mem
      (f := (Nat.cast : ℕ → ℚ)) (Nat.cast_injective)
    intro n
    simp only [Set.mem_setOf_eq, hQeval, taylor_eval]
    rw [add_comm, ← eval_add_natCast_eq_sum_fwdDiff_choose p a n]
  -- Conclude by evaluating the polynomial identity at `x`.
  rw [add_comm a x, ← taylor_eval a p x, hagree, hQeval]

end FactorRemainderTheoremOQ01OQ01OQ02
