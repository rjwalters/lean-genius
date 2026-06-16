/-
  Chebyshev Bounds OQ-04-OQ-01 — Weak Mertens estimate (floor-identity route)

  Companion to `ChebyshevBoundsOQ04OQ01.lean`. Self-contained: imports only
  Mathlib so it is portable to Aristotle `prove_file` (no `Proofs.*` imports).

  ## Goal

  Prove the *weak Mertens reciprocal bound*

      |M₁(N)| ≤ 1,   where  M₁(N) := Σ_{d=1}^{N} μ(d)/d.

  This is the tight form of the |Σ μ(d)/d| ≤ 1 + log N estimate needed for the
  Selberg symmetry step toward an elementary PNT. The route avoids
  summation-by-parts entirely (the classical Dirichlet hyperbola / floor route):

  - **Step 1 (floor identity).** Σ_{d=1}^{N} μ(d)·⌊N/d⌋ = 1 for N ≥ 1.
    Because ⌊N/d⌋ = #{m ∈ Icc 1 N : d ∣ m}, swap the order of the double sum
    over `d ∣ m` and collapse the inner sum via the Möbius indicator
    Σ_{d ∣ m} μ(d) = [m = 1].
  - **Step 2 (decompose the floor).** ⌊N/d⌋ = N/d − fract(N/d) over ℝ, hence
    N·M₁(N) = 1 + Σ_{d=1}^{N} μ(d)·fract(N/d).
  - **Step 3 (bound).** |fract| < 1 and the d = 1 term vanishes, so
    |N·M₁(N)| < N, giving |M₁(N)| ≤ 1 after dividing by N > 0.

  No axioms are introduced; the parent `chebyshevPsi_asymptotic` axiom remains
  the open target.
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Divisors

open Finset
open scoped BigOperators ArithmeticFunction

namespace ChebyshevBoundsOQ04OQ01

/-- The reciprocal Mertens partial sum `M₁(N) := Σ_{1 ≤ d ≤ N} μ(d)/d`, in ℝ. -/
noncomputable def mertensRecip (N : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) / (d : ℝ)

/-- `M₁(0) = 0` since `Icc 1 0 = ∅`. -/
theorem mertensRecip_zero : mertensRecip 0 = 0 := by
  unfold mertensRecip
  rw [Finset.Icc_eq_empty_of_lt (by decide : (0 : ℕ) < 1)]
  simp

/-- The number of multiples of `d` in `Icc 1 N` equals `N / d` (nat division).
    `⌊N/d⌋ = #{m : 1 ≤ m ≤ N, d ∣ m}`.
    Mathlib hook: `Nat.Ioc_filter_dvd_card_eq_div N d : #{x ∈ Ioc 0 N | d ∣ x} = N / d`,
    combined with `Finset.Ioc 0 N = Finset.Icc 1 N` (for ℕ, since `Ioc 0 N` and
    `Icc 1 N` describe the same set `{1, …, N}`). -/
theorem card_multiples_Icc (N d : ℕ) :
    ((Finset.Icc 1 N).filter (fun m => d ∣ m)).card = N / d := by
  sorry

/-- **Möbius indicator**: `Σ_{d ∣ m} μ(d) = [m = 1]` cast to ℤ.
    Mathlib hook: `(μ * ζ) m = ∑_{d ∣ m} μ d` via `ArithmeticFunction.coe_mul_zeta_apply`
    (or `coe_zeta_mul_apply`), and `μ * ζ = 1` via `ArithmeticFunction.moebius_mul_coe_zeta`;
    then `ArithmeticFunction.one_apply` gives `(1 : ArithmeticFunction ℤ) m = if m = 1 then 1 else 0`. -/
theorem sum_moebius_divisors (m : ℕ) (hm : 1 ≤ m) :
    ∑ d ∈ m.divisors, ArithmeticFunction.moebius d = if m = 1 then 1 else 0 := by
  sorry

/-- **Step 1 — floor identity**: `Σ_{d=1}^{N} μ(d)·⌊N/d⌋ = 1` for `N ≥ 1`.
    Proof: rewrite `N/d` as the count of multiples, swap the double sum over the
    `d ∣ m` relation, collapse the inner sum by the Möbius indicator. -/
theorem sum_moebius_mul_floor (N : ℕ) (hN : 1 ≤ N) :
    ∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℤ) * ((N / d : ℕ) : ℤ) = 1 := by
  sorry

/-- **Step 2 — real form**: `N·M₁(N) = 1 + Σ_{d=1}^{N} μ(d)·fract(N/d)`.
    Obtained by writing `⌊N/d⌋ = N/d − fract(N/d)` over ℝ in Step 1. -/
theorem mul_mertensRecip_eq (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) * mertensRecip N
      = 1 + ∑ d ∈ Finset.Icc 1 N,
          (ArithmeticFunction.moebius d : ℝ) * Int.fract ((N : ℝ) / (d : ℝ)) := by
  sorry

/-- The fractional remainder sum is bounded by `N − 1`: the `d = 1` term
    vanishes (`fract` of an integer is `0`) and every other term has
    `|μ(d)·fract| ≤ 1`, with `N − 1` such terms.
    Mathlib hooks: `Int.fract_intCast` / `Int.fract_natCast` (the `d = 1` term:
    `fract (N/1) = fract N = 0`), `Int.fract_nonneg`, `Int.fract_lt_one`,
    `ArithmeticFunction.abs_moebius_le_one`, `Finset.abs_sum_le_sum_abs`. -/
theorem fract_sum_abs_le (N : ℕ) (hN : 1 ≤ N) :
    |∑ d ∈ Finset.Icc 1 N,
        (ArithmeticFunction.moebius d : ℝ) * Int.fract ((N : ℝ) / (d : ℝ))|
      ≤ (N : ℝ) - 1 := by
  sorry

/-- **Weak Mertens reciprocal bound**: `|M₁(N)| ≤ 1` for all `N`.
    For `N = 0` both sides are `0 ≤ 1`; for `N ≥ 1` combine Steps 2–3 and divide
    by `N > 0`. -/
theorem mertensRecip_abs_le_one (N : ℕ) : |mertensRecip N| ≤ 1 := by
  sorry

end ChebyshevBoundsOQ04OQ01
