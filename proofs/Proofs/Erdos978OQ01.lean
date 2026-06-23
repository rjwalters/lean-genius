/-
Erdős Problem #978 — OQ-01: The local square-obstruction structure of n⁴ + 2

Source: https://erdosproblems.com/978
Parent: Proofs/Erdos978Problem.lean  (Erdős #978, the (k−2)-power-free question)

## The open problem

Erdős asked whether n⁴ + 2 represents infinitely many squarefree numbers (the
k = 4, (k−2)-power-free case of #978). This is OPEN: it lies outside the range
k ≥ 9 reached by Heath-Brown (2006) and Browning (2011), and the squarefree
square-sieve for a quartic is beyond current technology. Hooley (1967) only gives
the (k−1) = cubefree result. So the conjecture itself is not a Lean target.

## What IS provable, and what this file contributes

The standard squarefree heuristic predicts a *positive density* of squarefree
values, hence infinitely many. The two ingredients that are genuinely finite,
self-contained, and verifiable in Lean are:

1.  **No fixed square obstruction.** There is no integer m > 1 whose square
    divides n⁴ + 2 for every n — the trivial "answer is NO" route is closed.
    (`no_fixed_square_obstruction`: the value at n = 0 is 2, and m² ∣ 2 forces
    m² ≤ 2.)  In particular ρ(p²) := #{n : p² ∣ n⁴+2} never fills all residues.

2.  **The dominant local obstruction at p = 3 is fully explicit.** Among small
    primes p = 3 is the leading contributor to the local density product
    C = ∏ₚ (1 − ρ(p²)/p²). Here `9 ∣ n⁴+2 ⟺ n ≡ 2 or 7 (mod 9)`: exactly two of
    the nine residue classes are obstructed, so 7/9 are "safe". This is a clean
    `decide`-checked fact over `ZMod 9`, lifted to ℤ, and it yields infinitely
    many n with 9 ∤ n⁴+2 (every multiple of 9 works).

All results below are 0-axiom and machine-checked (no `native_decide`; the
`decide` calls reduce inside the kernel over the finite ring `ZMod 9`).

This does not resolve the open conjecture — it formalizes the necessary local
conditions that the heuristic rests on, at the dominant prime.
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

open Finset

namespace Erdos978OQ01

/-- The polynomial value under study, `F n = n⁴ + 2`. -/
def F (n : ℤ) : ℤ := n ^ 4 + 2

/-! ## Part I — No fixed square obstruction

The first thing one must rule out is a *global* square: some fixed `m > 1` with
`m² ∣ n⁴ + 2` for all `n`. Such an `m` would make `n⁴ + 2` never squarefree and
settle the conjecture negatively. There is none, for the cheapest possible
reason: the value at `n = 0` is `2`. -/

/-- `F 0 = 2`. -/
@[simp] theorem F_zero : F 0 = 2 := by norm_num [F]

/-- **No fixed square divides every value of `n⁴ + 2`.**
For any modulus `m > 1`, some value `n⁴ + 2` is not divisible by `m²`
(witness `n = 0`, value `2`, and `m² ∣ 2` would force `m² ≤ 2 < 4`). -/
theorem no_fixed_square_obstruction (m : ℤ) (hm : 1 < m) :
    ∃ n : ℤ, ¬ (m ^ 2 ∣ F n) := by
  refine ⟨0, ?_⟩
  rw [F_zero]
  intro h
  have hle := Int.le_of_dvd (by norm_num) h
  have h2 : 2 ≤ m := by omega
  nlinarith [hle, h2, sq_nonneg (m - 2)]

/-! ## Part II — The dominant local obstruction at `p = 3`

`p = 3` is the smallest prime with `x⁴ ≡ −2 (mod 9)` solvable, and the leading
term of the local density product. We pin down its contribution exactly. -/

/-- Over the finite ring `ZMod 9`, `n⁴ + 2 = 0` for exactly the residues
`n = 2` and `n = 7`. -/
theorem zmod_nine_root_iff (n : ZMod 9) :
    n ^ 4 + 2 = 0 ↔ n = 2 ∨ n = 7 := by decide +revert

/-- **The 3²-obstruction, over ℤ.** `9 ∣ n⁴ + 2` iff `n ≡ 2` or `n ≡ 7 (mod 9)`. -/
theorem nine_dvd_iff (n : ℤ) :
    (9 : ℤ) ∣ F n ↔ (n : ZMod 9) = 2 ∨ (n : ZMod 9) = 7 := by
  rw [← zmod_nine_root_iff,
      show (9 : ℤ) = ((9 : ℕ) : ℤ) by norm_num,
      ← ZMod.intCast_zmod_eq_zero_iff_dvd, F]
  push_cast
  tauto

/-- Exactly `2` of the `9` residues mod `9` are obstructed: `ρ(9) = 2`. -/
theorem obstructed_card :
    (univ.filter (fun n : ZMod 9 => n ^ 4 + 2 = 0)).card = 2 := by decide

/-- The other `7` residues are "safe": `9 ∤ n⁴+2`. A positive proportion
(`7/9 > 0`), which is what the squarefree heuristic at `p = 3` requires. -/
theorem safe_card :
    (univ.filter (fun n : ZMod 9 => n ^ 4 + 2 ≠ 0)).card = 7 := by decide

/-- The obstruction is non-vacuous: `9 ∣ F 2` (indeed `F 2 = 18 = 2·3²`). -/
theorem nine_dvd_F_two : (9 : ℤ) ∣ F 2 := by norm_num [F]

/-- And `9 ∣ F 7` (here `F 7 = 2403 = 3³·89`, the second obstructed class). -/
theorem nine_dvd_F_seven : (9 : ℤ) ∣ F 7 := by norm_num [F]

/-! ## Part III — Infinitely many values avoid the `p = 3` square

Because the obstructed residues are `2, 7 (mod 9)`, every multiple of `9` gives a
value with `9 ∤ n⁴+2`. There is a multiple of `9` above any bound, so infinitely
many `n` escape the dominant local square. -/

/-- **Infinitely many `n` with `9 ∤ n⁴ + 2`.** For every bound `N` there is an
`n > N` (namely a multiple of `9`) whose value escapes the `3²` obstruction. -/
theorem infinitely_many_nine_safe (N : ℤ) :
    ∃ n : ℤ, N < n ∧ ¬ (9 : ℤ) ∣ F n := by
  refine ⟨9 * ((N.natAbs : ℤ) + 1), by omega, ?_⟩
  rw [nine_dvd_iff]
  have h0 : ((9 * ((N.natAbs : ℤ) + 1) : ℤ) : ZMod 9) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact dvd_mul_right 9 _
  rw [h0]
  decide

end Erdos978OQ01
