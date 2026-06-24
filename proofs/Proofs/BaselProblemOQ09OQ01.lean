import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic

/-
# The Dirichlet Lambda Parity Split: λ(s) = (1 − 2⁻ˢ)·ζ(s)

## What This Proves
For **every** exponent `s` and **every** value `Z` realising the zeta-type sum
`∑_{n≥1} 1/nˢ = Z`, the reciprocals of the *odd* powers carry exactly the
fraction `(1 − 2⁻ˢ)` of the mass:

  λ(s) := ∑_{k≥0} 1/(2k+1)ˢ = (1 − 1/2ˢ) · ζ(s),

while the *even* powers carry the complementary `2⁻ˢ`:

  ∑_{k≥1} 1/(2k)ˢ = (1/2ˢ) · ζ(s).

Specialising to the explicit even zeta values from Mathlib gives

  λ(2) = (1 − 1/4)·(π²/6) = π²/8       (recovers `basel-problem-oq-09`)
  λ(4) = (1 − 1/16)·(π⁴/90) = π⁴/96    (new)

## Approach
The parent entry `basel-problem-oq-09` carried out the even/odd decomposition
only for the single exponent `s = 2`. Here we abstract the argument over an
arbitrary exponent `s` and an arbitrary realised sum `Z`:

1. The even subseries `k ↦ 1/(2k)ˢ` is a rescaled copy of the whole series,
   because `(2k)ˢ = 2ˢ·kˢ`; hence it has sum `(1/2ˢ)·Z`.
2. The odd subseries is an injective reindexing of a summable series, so it is
   summable and has *some* sum.
3. `HasSum.even_add_odd` recombines the two subseries into the full series, and
   uniqueness of sums forces the odd value to be `Z − (1/2ˢ)·Z = (1 − 1/2ˢ)·Z`.

Nothing in steps 1–3 uses the *value* `Z`, so the lemma is fully general; the
concrete `π²/8` and `π⁴/96` are one-line specialisations against
`hasSum_zeta_two` and `hasSum_zeta_four`.

## Provenance
- Foundations: `hasSum_zeta_two`, `hasSum_zeta_four`
  (`Mathlib.NumberTheory.ZetaValues`).
- Split: `HasSum.even_add_odd` (`Mathlib.Topology.Algebra.InfiniteSum.NatInt`).
- Rescaling: `HasSum.mul_left`; summability via `Summable.comp_injective`;
  value identification via `HasSum.unique`.

This entry answers the open question `basel-problem-oq-09-oq-01`.

## Status
- [x] Complete proof, 0 sorries, 0 axioms.

Original formalization for Lean Genius.
-/

namespace BaselProblemOQ09OQ01

open Real Filter Topology

/-! ## The general parity split (arbitrary exponent and realised sum) -/

/-- **The even part, general form.** If `∑ₙ 1/nˢ = Z`, then the even-power
subseries sums to `(1/2ˢ)·Z`, because `(2k)ˢ = 2ˢ·kˢ`. -/
theorem hasSum_even_of_hasSum {s : ℕ} {Z : ℝ}
    (hZ : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ s) Z) :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ)) ^ s) ((1 / 2 ^ s) * Z) := by
  have hfun : (fun k : ℕ => 1 / (2 * (k : ℝ)) ^ s)
            = (fun k : ℕ => (1 / 2 ^ s) * (1 / (k : ℝ) ^ s)) := by
    funext k; rw [mul_pow]; ring
  rw [hfun]
  exact hZ.mul_left _

/-- **The odd part, general form — the parity split.** If `∑ₙ 1/nˢ = Z`, then
the odd-power subseries sums to `(1 − 1/2ˢ)·Z`. This is the statement
`λ(s) = (1 − 2⁻ˢ)·ζ(s)` for any realised zeta value. -/
theorem hasSum_odd_of_hasSum {s : ℕ} {Z : ℝ}
    (hZ : HasSum (fun n : ℕ => 1 / (n : ℝ) ^ s) Z) :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ s) ((1 - 1 / 2 ^ s) * Z) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ s with hf
  -- Even part in the `f (2*k)` shape required by `even_add_odd`.
  have heven : HasSum (fun k : ℕ => f (2 * k)) ((1 / 2 ^ s) * Z) := by
    have hfun : (fun k : ℕ => f (2 * k))
              = (fun k : ℕ => (1 / 2 ^ s) * f k) := by
      funext k; simp only [hf]; push_cast; rw [mul_pow]; ring
    rw [hfun]; exact hZ.mul_left _
  -- The odd subseries is summable (injective reindexing of a summable series).
  have hinj : Function.Injective (fun k : ℕ => 2 * k + 1) := by
    intro a b h; dsimp only at h; omega
  have hodd_sum : Summable (fun k : ℕ => f (2 * k + 1)) := by
    have h := hZ.summable.comp_injective hinj
    simpa [Function.comp] using h
  have hodd : HasSum (fun k : ℕ => f (2 * k + 1)) (∑' k, f (2 * k + 1)) :=
    hodd_sum.hasSum
  -- Recombine even + odd into the full series, then identify the odd value.
  have hcomb : HasSum f ((1 / 2 ^ s) * Z + ∑' k, f (2 * k + 1)) :=
    heven.even_add_odd hodd
  have huniq : (1 / 2 ^ s) * Z + ∑' k, f (2 * k + 1) = Z := hcomb.unique hZ
  have hval : (∑' k, f (2 * k + 1)) = (1 - 1 / 2 ^ s) * Z := by
    have hstep : (∑' k, f (2 * k + 1)) = Z - (1 / 2 ^ s) * Z := by linarith
    rw [hstep]; ring
  -- Bridge the local `f`-form to the clean statement.
  rw [hval] at hodd
  have hbridge : (fun k : ℕ => f (2 * k + 1))
               = (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ s) := by
    funext k; simp only [hf]; push_cast; ring
  rw [hbridge] at hodd
  exact hodd

/-! ## Concrete even zeta values

The explicit `λ(2m)` follow by feeding Mathlib's closed forms into the general
lemma; each is a one-line numeric simplification of `(1 − 1/2^{2m})·ζ(2m)`. -/

/-- **λ(2) = π²/8.** Recovers the parent result `basel-problem-oq-09`. -/
theorem hasSum_lambda_two :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) (π ^ 2 / 8) := by
  have h := hasSum_odd_of_hasSum (s := 2) hasSum_zeta_two
  have heq : (1 - 1 / (2 : ℝ) ^ 2) * (π ^ 2 / 6) = π ^ 2 / 8 := by ring
  rwa [heq] at h

/-- **λ(4) = π⁴/96.** The new result: `(1 − 1/16)·(π⁴/90) = π⁴/96`. -/
theorem hasSum_lambda_four :
    HasSum (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) (π ^ 4 / 96) := by
  have h := hasSum_odd_of_hasSum (s := 4) hasSum_zeta_four
  have heq : (1 - 1 / (2 : ℝ) ^ 4) * (π ^ 4 / 90) = π ^ 4 / 96 := by ring
  rwa [heq] at h

/-! ## tsum forms and summability -/

/-- `∑' k, 1/(2k+1)² = π²/8`. -/
theorem tsum_lambda_two : ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ 2 = π ^ 2 / 8 :=
  hasSum_lambda_two.tsum_eq

/-- `∑' k, 1/(2k+1)⁴ = π⁴/96`. -/
theorem tsum_lambda_four : ∑' k : ℕ, 1 / (2 * (k : ℝ) + 1) ^ 4 = π ^ 4 / 96 :=
  hasSum_lambda_four.tsum_eq

/-- The odd fourth-power series is summable. -/
theorem summable_lambda_four :
    Summable (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) :=
  hasSum_lambda_four.summable

/-! ## Sanity checks on the parity factor and values -/

/-- The even and odd fourth-power masses recombine to ζ(4) = π⁴/90:
`π⁴/720 + π⁴/96 = π⁴/90` (even mass `(1/16)·π⁴/90 = π⁴/1440`… check via ζ). -/
theorem lambda_four_decomposition :
    (1 / 2 ^ 4 : ℝ) * (π ^ 4 / 90) + π ^ 4 / 96 = π ^ 4 / 90 := by ring

/-- The parity factor at `s` and `s` complementary parts sum to one:
`1/2ˢ + (1 − 1/2ˢ) = 1`. -/
theorem parity_factor_complement (s : ℕ) :
    (1 / 2 ^ s : ℝ) + (1 - 1 / 2 ^ s) = 1 := by ring

/-- λ(4) is positive. -/
theorem lambda_four_pos : (0 : ℝ) < π ^ 4 / 96 := by positivity

/-- The first odd fourth-power term is `1/1⁴ = 1`. -/
example : (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) 0 = 1 := by norm_num

/-- The second odd fourth-power term is `1/3⁴ = 1/81`. -/
example : (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 4) 1 = 1 / 81 := by norm_num

end BaselProblemOQ09OQ01
