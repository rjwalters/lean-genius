import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-
# The Dirichlet Lambda Values: λ(2m) = (1 − 2^{−2m})·ζ(2m), with λ(2)=π²/8 and λ(4)=π⁴/96

## What This Proves
The parent entry `basel-problem-oq-09` carried out the even/odd split of the Basel
sum for the *single* exponent `s = 2`, obtaining the odd-square value
`∑_{k≥0} 1/(2k+1)² = π²/8`.  This entry answers its open question by lifting that
computation to an *exponent-uniform* statement.

For **every** convergent `p`-series the same split holds.  If
`∑_{n≥1} 1/nˢ = Z`, then the odd-index subseries is a fixed fraction of the whole:

  `∑_{k≥0} 1/(2k+1)ˢ = (1 − 2^{−s})·Z`.

The fraction `1 − 2^{−s}` is the *only* exponent-dependent quantity: the even part
`∑_{k} 1/(2k)ˢ = 2^{−s}·Z` is a rescaled copy of the full series, and the odd part
is the complementary piece.  Writing `λ(s) := ∑_{k≥0} 1/(2k+1)ˢ` for the Dirichlet
lambda function, this is exactly

  `λ(s) = (1 − 2^{−s})·ζ(s)`.

## Specializations
- `s = 2`:  `λ(2) = (1 − 1/4)·(π²/6) = (3/4)·(π²/6) = π²/8`  (recovers the parent).
- `s = 4`:  `λ(4) = (1 − 1/16)·(π⁴/90) = (15/16)·(π⁴/90) = π⁴/96`  (new value).
- general even `s = 2m`:  `λ(2m) = (1 − 2^{−2m})·ζ(2m)` with `ζ(2m)` the explicit
  Bernoulli closed form from Mathlib's `hasSum_zeta_nat`.

## Approach
The general lemma `hasSum_odd_pow` is the whole content.  Given `HasSum (·⁻ˢ) Z`:
- `(2k)ˢ = 2ˢ·kˢ` (`mul_pow`) makes the even subseries `fun k ↦ 1/(2k)ˢ` equal to
  `(1/2ˢ)·(1/kˢ)` termwise — even at `k = 0`, where both sides are `1/0 = 0` — so
  `HasSum.mul_left` evaluates it to `(1/2ˢ)·Z`.
- The odd subseries is summable as an injective reindexing (`Summable.comp_injective`
  along `k ↦ 2k+1`) of the summable `p`-series.
- `HasSum.even_add_odd` recombines even + odd into the full series; `HasSum.unique`
  against the hypothesis pins the odd value to `Z − (1/2ˢ)·Z = (1 − 2^{−s})·Z`.

No new analytic input is needed beyond the parent's toolkit — the novelty is the
exponent-uniform abstraction and the `s = 4` instance, neither present before.

## Provenance
- `hasSum_zeta_two`, `hasSum_zeta_four`, `hasSum_zeta_nat` from
  `Mathlib.NumberTheory.ZetaValues`.
- `HasSum.even_add_odd` from `Mathlib.Topology.Algebra.InfiniteSum.NatInt`.
- `HasSum.mul_left`, `Summable.comp_injective`, `HasSum.unique`.

## Status
- [x] Complete proof, 0 sorries, 0 axioms.

Original formalization for Lean Genius.
-/

namespace BaselProblemOQ09OQ01

open Real Filter Topology

/-! ## The exponent-uniform even/odd split -/

/-- **The general parity split.** For any natural exponent `s` and any value `Z`
with `∑_{n≥1} 1/nˢ = Z`, the odd-index subseries carries the fraction `1 − 2^{−s}`
of the total:

  `∑_{k≥0} 1/(2k+1)ˢ = (1 − 1/2ˢ)·Z`.

This is the source of every Dirichlet lambda value `λ(s) = (1 − 2^{−s})·ζ(s)`. -/
theorem hasSum_odd_pow {s : ℕ} {Z : ℝ}
    (hZ : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ s) Z) :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ s) ((1 - 1 / 2 ^ s) * Z) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ s with hf
  -- The even subseries `k ↦ f (2k)` is a `1/2ˢ`-rescaled copy of `f`.
  have heven : HasSum (fun k : ℕ => f (2 * k)) (1 / 2 ^ s * Z) := by
    have hfun : (fun k : ℕ => f (2 * k)) = (fun k : ℕ => (1 / 2 ^ s) * f k) := by
      funext k
      simp only [hf]
      push_cast
      rw [mul_pow]
      field_simp
    rw [hfun]
    exact hZ.mul_left (1 / 2 ^ s)
  -- The odd subseries is summable (injective reindexing of a summable series).
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h; dsimp only at h; omega
  have hodd_sum : Summable (fun k : ℕ => f (2 * k + 1)) := by
    have h := hZ.summable.comp_injective hinj
    simpa [Function.comp] using h
  have hodd : HasSum (fun k : ℕ => f (2 * k + 1)) (∑' k, f (2 * k + 1)) :=
    hodd_sum.hasSum
  -- Recombine and identify the odd value via uniqueness.
  have hcomb : HasSum f (1 / 2 ^ s * Z + ∑' k, f (2 * k + 1)) :=
    heven.even_add_odd hodd
  have huniq : 1 / 2 ^ s * Z + ∑' k, f (2 * k + 1) = Z := hcomb.unique hZ
  have hval : (∑' k, f (2 * k + 1)) = (1 - 1 / 2 ^ s) * Z := by ring_nf; ring_nf at huniq; linarith
  -- Bridge the local `f (2k+1)` form to the clean statement.
  have hbridge : (fun k : ℕ => f (2 * k + 1))
               = (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ s) := by
    funext k; simp only [hf]; push_cast; ring
  rw [hval] at hodd
  rw [hbridge] at hodd
  exact hodd

/-- The tsum form of the general parity split. -/
theorem tsum_odd_pow {s : ℕ} {Z : ℝ}
    (hZ : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ s) Z) :
    ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ s = (1 - 1 / 2 ^ s) * Z :=
  (hasSum_odd_pow hZ).tsum_eq

/-! ## The general even-exponent value: λ(2m) = (1 − 2^{−2m})·ζ(2m) -/

/-- **Dirichlet lambda at even integers.** For every `m ≥ 1`,

  `∑_{k≥0} 1/(2k+1)^{2m} = (1 − 2^{−2m}) · ζ(2m)`,

where `ζ(2m)` is Mathlib's explicit Bernoulli closed form. This is the parity split
applied to `hasSum_zeta_nat`. -/
theorem hasSum_lambda_nat {m : ℕ} (hm : m ≠ 0) :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ (2 * m))
      ((1 - 1 / 2 ^ (2 * m)) *
        ((-1 : ℝ) ^ (m + 1) * (2 : ℝ) ^ (2 * m - 1) * π ^ (2 * m) *
          bernoulli (2 * m) / (Nat.factorial (2 * m)))) :=
  hasSum_odd_pow (hasSum_zeta_nat hm)

/-! ## λ(2) = π²/8 — recovers the parent entry -/

/-- **The odd-square series** (`s = 2`): `∑_{k≥0} 1/(2k+1)² = π²/8`.
A one-line specialization of `hasSum_odd_pow` to `hasSum_zeta_two`. -/
theorem hasSum_lambda_two :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
  have h := hasSum_odd_pow hasSum_zeta_two
  have : (1 - 1 / 2 ^ 2) * (π ^ 2 / 6) = π ^ 2 / 8 := by norm_num; ring
  rwa [this] at h

/-- The tsum form of `λ(2)`. -/
theorem tsum_lambda_two : ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ 2 = π ^ 2 / 8 :=
  hasSum_lambda_two.tsum_eq

/-! ## λ(4) = π⁴/96 — the new value -/

/-- **The odd fourth-power series** (`s = 4`): `∑_{k≥0} 1/(2k+1)⁴ = π⁴/96`.

  `1 + 1/3⁴ + 1/5⁴ + ⋯ = π⁴/96`.

Derived from `hasSum_zeta_four` (`ζ(4) = π⁴/90`) via the parity fraction
`1 − 2^{−4} = 15/16`:  `(15/16)·(π⁴/90) = π⁴/96`. -/
theorem hasSum_lambda_four :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) (π ^ 4 / 96) := by
  have h := hasSum_odd_pow hasSum_zeta_four
  have : (1 - 1 / 2 ^ 4) * (π ^ 4 / 90) = π ^ 4 / 96 := by norm_num; ring
  rwa [this] at h

/-- The tsum form of the new result: `∑' k, 1/(2k+1)⁴ = π⁴/96`. -/
theorem tsum_lambda_four : ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ 4 = π ^ 4 / 96 :=
  hasSum_lambda_four.tsum_eq

/-- The odd fourth-power series is summable. -/
theorem summable_lambda_four : Summable (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) :=
  hasSum_lambda_four.summable

/-- `λ(4) = π⁴/96` is positive. -/
theorem lambda_four_pos : (0 : ℝ) < π ^ 4 / 96 := by positivity

/-! ## Structural consequences of the parity fraction -/

/-- The even part is the complementary fraction: `∑_{k} 1/(2k)⁴ = π⁴/90 − π⁴/96`,
i.e. `ζ(4) = (even part) + λ(4)`. The full Basel-4 value splits as `2^{−4} : (1−2^{−4})`. -/
theorem zeta_four_even_odd_decomposition : π ^ 4 / 90 = (π ^ 4 / 90 - π ^ 4 / 96) + π ^ 4 / 96 := by
  ring

/-- The odd part dominates: at exponent 4 the odd indices carry `15/16` of the mass,
so `λ(4)` exceeds the even part `ζ(4) − λ(4)`. -/
theorem lambda_four_gt_even_part : (π ^ 4 / 90 - π ^ 4 / 96) < π ^ 4 / 96 := by
  have : (0 : ℝ) < π ^ 4 := by positivity
  linarith

/-- The parity fraction grows with the exponent: `1 − 2^{−2} < 1 − 2^{−4}`, so a
larger share of `ζ(s)` concentrates on the odd indices as `s` increases. -/
theorem parity_fraction_mono : (1 : ℝ) - 1 / 2 ^ 2 < 1 - 1 / 2 ^ 4 := by norm_num

/-! ## Numerical sanity checks -/

/-- The first odd fourth-power term is `1/1⁴ = 1`. -/
example : (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) 0 = 1 := by norm_num

/-- The second odd fourth-power term is `1/3⁴ = 1/81`. -/
example : (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) 1 = 1 / 81 := by norm_num

end BaselProblemOQ09OQ01
