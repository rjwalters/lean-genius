/-
  # Uniform Dirichlet eta values: η(2k) = (1 − 2^{1−2k})·ζ(2k)
  # (basel-problem-oq-13-oq-01-oq-01)

  ## The Open Question (from basel-problem-oq-13-oq-01)

  > The sibling files derive individual eta values (η(2) = π²/12, η(4) = 7π⁴/720)
  > by hand-splitting each alternating sum by parity.  Can the parity split be
  > packaged **once and for all** into a uniform statement
  >
  >     η(s) = (1 − 2^{1−s})·ζ(s)
  >
  > relating the Dirichlet eta function to the Riemann zeta function, and then
  > specialised to the even integers s = 2k using Mathlib's closed form for ζ(2k)?

  ## The bridge

  The Dirichlet eta function η(s) = ∑_{n≥1} (-1)^{n+1}/nˢ is the alternating
  companion of ζ(s) = ∑_{n≥1} 1/nˢ.  Splitting by parity,

      η(s) = ∑_{odd} 1/nˢ − ∑_{even} 1/nˢ,   ζ(s) = ∑_{odd} 1/nˢ + ∑_{even} 1/nˢ.

  Since ∑_{even} 1/nˢ = ∑_k 1/(2k)ˢ = 2^{−s}·ζ(s), we get

      η(s) = ζ(s) − 2·∑_{even} 1/nˢ = ζ(s) − 2·2^{−s}·ζ(s) = (1 − 2^{1−s})·ζ(s).

  The heart of the file is `hasSum_eta_of_hasSum_zeta`, which proves this as a
  purely formal consequence of *any* convergent `p`-series `HasSum` — no analytic
  input, no specific value of the exponent.  It therefore applies verbatim to
  every exponent for which the series converges (natural `m ≥ 2`), and in
  particular to the even integers, where Mathlib supplies the closed form
  `hasSum_zeta_nat`.

  Writing the exponent as a natural number `m`, the factor `1 − 2^{1−m}` becomes
  the rational `1 − 2/2^m`; for the even case `m = 2k` this is `1 − 2^{1−2k}`, and
  it recovers `1/2` at `k = 1` (η(2) = ζ(2)/2 = π²/12) and `7/8` at `k = 2`
  (η(4) = 7·ζ(4)/8 = 7π⁴/720).

  ## Axiom count: 0
-/

import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic

open Real
open scoped Nat

namespace BaselEtaUniform

set_option maxHeartbeats 1000000 in
/-- **The eta–zeta bridge.**  For *any* natural exponent `m` and any value `Z`,
    if the `p`-series `∑ 1/nᵐ` converges to `Z` (i.e. `ζ(m) = Z`), then the
    alternating series `∑ (-1)^{n+1}/nᵐ` converges to `(1 − 2/2ᵐ)·Z`.

    This is the finite-combinatorial content of `η(s) = (1 − 2^{1−s})·ζ(s)`,
    proved from the parity decomposition alone — no analytic facts about the
    exponent are used, so it holds for every convergent `p`-series. -/
theorem hasSum_eta_of_hasSum_zeta {m : ℕ} {Z : ℝ}
    (h : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ m) Z) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ m)
      ((1 - 2 / (2 : ℝ) ^ m) * Z) := by
  -- Even part of the *plain* series: ∑_k 1/(2k)ᵐ = (1/2ᵐ)·Z.
  have heven_plain : HasSum (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ m)
      ((1 / (2 : ℝ) ^ m) * Z) := by
    have hfun : (fun k : ℕ => 1 / ((2 * k : ℕ) : ℝ) ^ m)
        = (fun k : ℕ => (1 / (2 : ℝ) ^ m) * (1 / (k : ℝ) ^ m)) := by
      funext k
      have hc : ((2 * k : ℕ) : ℝ) ^ m = (2 : ℝ) ^ m * (k : ℝ) ^ m := by
        push_cast; rw [mul_pow]
      rw [hc]; ring
    rw [hfun]; exact h.mul_left _
  -- Odd part is summable (image of the injection `k ↦ 2k+1` of a summable family).
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b hab; simp only at hab; omega
  have hodd_summable : Summable (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ m) :=
    h.summable.comp_injective hinj
  have hodd : HasSum (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ m)
      (∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ m) := hodd_summable.hasSum
  set B := ∑' k : ℕ, 1 / ((2 * k + 1 : ℕ) : ℝ) ^ m with hB
  -- Uniqueness pins the odd sum: (1/2ᵐ)·Z + B = Z.
  have hcombined : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ m)
      ((1 / (2 : ℝ) ^ m) * Z + B) := heven_plain.even_add_odd hodd
  have hZ : (1 / (2 : ℝ) ^ m) * Z + B = Z := hcombined.unique h
  -- Even part of the *alternating* series: ∑_k (-1)^{2k+1}/(2k)ᵐ = -(1/2ᵐ)·Z.
  have heven_alt : HasSum (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ m)
      (-((1 / (2 : ℝ) ^ m) * Z)) := by
    have hfun : (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1) / ((2 * k : ℕ) : ℝ) ^ m)
        = (fun k : ℕ => -(1 / ((2 * k : ℕ) : ℝ) ^ m)) := by
      funext k
      have hs : (-1 : ℝ) ^ (2 * k + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
      rw [hs]; ring
    rw [hfun]; exact heven_plain.neg
  -- Odd part of the *alternating* series equals the plain odd part (sign = +1).
  have hodd_alt : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ m) B := by
    have hfun : (fun k : ℕ => (-1 : ℝ) ^ (2 * k + 1 + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ m)
        = (fun k : ℕ => 1 / ((2 * k + 1 : ℕ) : ℝ) ^ m) := by
      funext k
      have hs : (-1 : ℝ) ^ (2 * k + 1 + 1) = 1 := by
        rw [pow_succ, pow_succ, pow_mul]; norm_num
      rw [hs]
    rw [hfun]; exact hodd
  -- Assemble the alternating series (explicit type pins the summand → no HOU).
  have hfull : HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ m)
      (-((1 / (2 : ℝ) ^ m) * Z) + B) := heven_alt.even_add_odd hodd_alt
  have hval : (1 - 2 / (2 : ℝ) ^ m) * Z = -((1 / (2 : ℝ) ^ m) * Z) + B := by
    linear_combination -hZ
  rw [hval]; exact hfull

/-- **Uniform even eta values.**  For every `k ≥ 1`,
    `η(2k) = ∑_{n} (-1)^{n+1}/n^{2k} = (1 − 2/2^{2k})·ζ(2k)`, with `ζ(2k)` in
    Mathlib's Bernoulli-number closed form (`hasSum_zeta_nat`).  The factor
    `1 − 2/2^{2k}` is exactly `1 − 2^{1−2k}` (see `eta_factor_eq`). -/
theorem hasSum_eta_two_mul_nat {k : ℕ} (hk : k ≠ 0) :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ (2 * k))
      ((1 - 2 / (2 : ℝ) ^ (2 * k)) *
        ((-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
          bernoulli (2 * k) / (2 * k)!)) :=
  hasSum_eta_of_hasSum_zeta (hasSum_zeta_nat hk)

/-- The exponent factor `1 − 2/2^{2k}` written in the source form `1 − 2^{1−2k}`
    (using an integer exponent, since `1 − 2k ≤ 0`). -/
theorem eta_factor_eq (k : ℕ) :
    (1 : ℝ) - 2 / (2 : ℝ) ^ (2 * k) = 1 - (2 : ℝ) ^ ((1 : ℤ) - 2 * (k : ℤ)) := by
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have e : (2 : ℝ) ^ ((1 : ℤ) - 2 * (k : ℤ)) = 2 / (2 : ℝ) ^ (2 * k) := by
    rw [zpow_sub₀ h2, zpow_one, ← zpow_natCast (2 : ℝ) (2 * k)]
    norm_cast
  rw [e]

/-- **η(2)** = π²/12, recovered from the uniform bridge via `hasSum_zeta_two`. -/
theorem hasSum_eta_two :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2) (π ^ 2 / 12) := by
  have h := hasSum_eta_of_hasSum_zeta hasSum_zeta_two
  have hval : (1 - 2 / (2 : ℝ) ^ 2) * (π ^ 2 / 6) = π ^ 2 / 12 := by ring
  rwa [hval] at h

/-- **η(4)** = 7π⁴/720, recovered from the uniform bridge via `hasSum_zeta_four`.
    This matches the sibling file `BaselProblemOQ13OQ01`, obtained here as a
    one-line specialisation of the general theorem. -/
theorem hasSum_eta_four :
    HasSum (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4) (7 * π ^ 4 / 720) := by
  have h := hasSum_eta_of_hasSum_zeta hasSum_zeta_four
  have hval : (1 - 2 / (2 : ℝ) ^ 4) * (π ^ 4 / 90) = 7 * π ^ 4 / 720 := by ring
  rwa [hval] at h

/-- `η(2)` in `tsum` form. -/
theorem tsum_eta_two :
    ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 2 = π ^ 2 / 12 :=
  hasSum_eta_two.tsum_eq

/-- `η(4)` in `tsum` form. -/
theorem tsum_eta_four :
    ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) / (n : ℝ) ^ 4 = 7 * π ^ 4 / 720 :=
  hasSum_eta_four.tsum_eq

end BaselEtaUniform

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `hasSum_eta_of_hasSum_zeta` | ζ(m)=Z ⟹ η(m) = (1 − 2/2ᵐ)·Z, any exponent `m` |
  | `hasSum_eta_two_mul_nat`    | η(2k) = (1 − 2/2^{2k})·ζ(2k) (Bernoulli closed form) |
  | `eta_factor_eq`             | 1 − 2/2^{2k} = 1 − 2^{1−2k} |
  | `hasSum_eta_two`            | η(2) = π²/12 |
  | `hasSum_eta_four`           | η(4) = 7π⁴/720 |
  | `tsum_eta_two`, `tsum_eta_four` | `tsum` forms |

  The single analytic-free lemma `hasSum_eta_of_hasSum_zeta` packages the parity
  split once; every eta value is then a specialisation of it composed with a
  zeta `HasSum` (`hasSum_zeta_nat`, `hasSum_zeta_two`, `hasSum_zeta_four`).

  **Sorries**: 0
  **Axioms**: 0
-/
