import Mathlib

/-
# Euler's Identity in the p-adic Setting: the Obstruction

## The Question

Euler's identity `exp(π·i) + 1 = 0` — equivalently `exp(π·i) = -1` — is the flagship
consequence of Euler's formula `exp(x·i) = cos x + i·sin x` over `ℂ`. A natural
extension question (this entry's parent open question) is:

  *Is there a formalization of Euler's identity as a theorem in the p-adic setting?*

The honest answer is **no**, and this file records the precise, machine-checked
reason. Euler's identity has three ingredients — `exp`, `i`, and `π` — and in the
`p`-adic world they do not coexist in a way that lets the equation `exp(x) = -1` have
any solution.

## Why there is no p-adic Euler identity

1. **No `π`.** There is no canonical `p`-adic period. The complex identity singles out
   `π·i` as the point where `exp` first returns a "half turn"; `ℚ_p` has no such
   distinguished element because the `p`-adic exponential is *injective* on its domain
   of convergence and has no periodicity.

2. **The `p`-adic exponential barely converges.** The series `∑ xⁿ/n!` converges in
   `ℚ_p` only on the small disk `v_p(x) > 1/(p-1)`; for `p` odd this is exactly the
   maximal ideal `p·ℤ_p`. Mathlib has **no** `p`-adic exponential at all (there is no
   `Padics/Exp` file, and the generic `NormedSpace.exp` returns junk off the disk of
   convergence over `ℚ_p`), so there is nothing to set `= -1` in the first place.

3. **The range of `exp` misses `-1`.** Where the `p`-adic exponential *does* converge
   (on `p·ℤ_p` for odd `p`), its values are **principal units**: they lie in
   `1 + p·ℤ_p`, i.e. they are `≡ 1 (mod p)`. But for an odd prime `p` the element `-1`
   is **not** a principal unit: `-1 - 1 = -2` is a unit of `ℤ_p`, so `-1 ≢ 1 (mod p)`.
   Hence the equation `exp(x) = -1` is unsolvable — the algebraic core of "no `p`-adic
   Euler identity."

This file formalizes ingredient (3) — the algebraic obstruction that makes the whole
question collapse — together with a residue-level record of the one ingredient that
*does* survive: a square root of `-1` (a `p`-adic "`i`") exists at the residue-field
level exactly when `p ≢ 3 (mod 4)`.

## What is proved here (all fully verified, 0 axioms, 0 sorries)

* `padicInt_norm_neg_two` : for an odd prime `p`, `‖(-2 : ℤ_[p])‖ = 1`
  (`-2` is a `p`-adic unit).
* `neg_one_sub_one_norm_eq_one` : `‖(-1 : ℤ_[p]) - 1‖ = 1` for odd `p` — `-1` sits at
  maximal distance `1` from `1`.
* `neg_one_not_principal_unit` : for odd `p`, no principal unit equals `-1`
  (`∀ x ∈ maximalIdeal, 1 + x ≠ -1`). This is the obstruction: since the convergent
  `p`-adic exponential maps into `1 + p·ℤ_p`, it can never output `-1`.
* `neg_two_mem_maximalIdeal_iff` : the contrast at `p = 2` — `-2` *is* in the maximal
  ideal exactly when `p = 2`, so the odd-prime hypothesis is sharp.
* `padic_i_exists_residue_iff` : a residue-level square root of `-1` exists in
  `ZMod p` iff `p % 4 ≠ 3` — the surviving "`i`" ingredient.

## Honesty note

The connection between `neg_one_not_principal_unit` and "the `p`-adic `exp` never
equals `-1`" rests on the standard fact that the convergent `p`-adic exponential maps
the maximal ideal into the principal units `1 + p·ℤ_p`. That fact about `exp` is *not*
formalized here (Mathlib has no `p`-adic `exp` to state it against); what is
machine-checked is the purely algebraic statement that `-1` lies outside the target
group `1 + p·ℤ_p`. The prose above is the mathematical bridge, not a Lean theorem.
-/

namespace EulerIdentityOQ02

variable (p : ℕ) [hp : Fact p.Prime]

/-- For an odd prime `p`, `2` is a `p`-adic unit, so `‖(-2 : ℤ_[p])‖ = 1`. -/
theorem padicInt_norm_neg_two (hodd : p ≠ 2) : ‖(-2 : ℤ_[p])‖ = 1 := by
  -- `p ∤ 2`: distinct primes never divide one another.
  have hpdvd : ¬ (p : ℤ) ∣ (-2 : ℤ) := by
    rw [dvd_neg]
    intro h
    have h2 : p ∣ 2 := by exact_mod_cast h
    exact hodd ((Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp h2)
  have hcast : (-2 : ℤ_[p]) = ((-2 : ℤ) : ℤ_[p]) := by push_cast; ring
  -- Since `p ∤ -2`, the norm is *not* `< 1`; combined with `≤ 1` it equals `1`.
  have hnlt : ¬ ‖(-2 : ℤ_[p])‖ < 1 := by
    rw [hcast, PadicInt.norm_int_lt_one_iff_dvd]; exact hpdvd
  exact le_antisymm (PadicInt.norm_le_one _) (not_lt.mp hnlt)

/-- For an odd prime `p`, `-1` lies at maximal distance `1` from `1` in `ℤ_[p]`:
`‖(-1 : ℤ_[p]) - 1‖ = 1`. -/
theorem neg_one_sub_one_norm_eq_one (hodd : p ≠ 2) :
    ‖(-1 : ℤ_[p]) - 1‖ = 1 := by
  have h : (-1 : ℤ_[p]) - 1 = (-2 : ℤ_[p]) := by ring
  rw [h]
  exact padicInt_norm_neg_two p hodd

/-- **The obstruction.** For an odd prime `p`, no principal unit equals `-1`: for every
`x` in the maximal ideal `p·ℤ_p`, `1 + x ≠ -1`. Since the convergent `p`-adic
exponential maps `p·ℤ_p` into the principal units `1 + p·ℤ_p`, this shows `exp(x) = -1`
has no solution — there is no `p`-adic Euler identity. -/
theorem neg_one_not_principal_unit (hodd : p ≠ 2) (x : ℤ_[p])
    (hx : x ∈ IsLocalRing.maximalIdeal ℤ_[p]) : (1 : ℤ_[p]) + x ≠ -1 := by
  intro heq
  have hx2 : x = (-2 : ℤ_[p]) := by linear_combination heq
  have hnorm : ‖x‖ < 1 := by
    rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at hx
    exact hx
  rw [hx2, padicInt_norm_neg_two p hodd] at hnorm
  exact lt_irrefl (1 : ℝ) hnorm

/-- Sharpness of the odd hypothesis: `-2 ∈ maximalIdeal ℤ_[p]` exactly when `p = 2`.
For odd `p` the obstruction above holds; at `p = 2`, `-1` *is* a principal unit
(though the 2-adic exponential converges only on `4·ℤ_2` and so still misses `-1`, by a
finer argument not needed here). -/
theorem neg_two_mem_maximalIdeal_iff :
    (-2 : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] ↔ p = 2 := by
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]
  have hcast : (-2 : ℤ_[p]) = ((-2 : ℤ) : ℤ_[p]) := by push_cast; ring
  rw [hcast, PadicInt.norm_int_lt_one_iff_dvd, dvd_neg]
  constructor
  · intro h
    have h2 : p ∣ 2 := by exact_mod_cast h
    exact (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp h2
  · rintro rfl
    norm_num

/-- The one surviving ingredient, at the residue level: a `p`-adic "`i`" (a square root
of `-1`) exists in the residue field `ZMod p` iff `p ≢ 3 (mod 4)`. This is the
residue-field shadow of when `√(-1) ∈ ℚ_p`; the lift to `ℚ_p` is by Hensel's lemma for
odd `p`. -/
theorem padic_i_exists_residue_iff :
    IsSquare (-1 : ZMod p) ↔ p % 4 ≠ 3 :=
  ZMod.exists_sq_eq_neg_one_iff

end EulerIdentityOQ02
