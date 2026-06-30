import Mathlib
import Proofs.LagrangeFourSquaresWaringG2OQ03OQ05OQ01

/-!
# The per-step law of the non-three-square density error, and why `−5` cannot sustain

**Open question (`...-oq-03-oq-05-oq-01-oq-01`)**, a direct sequel to `oq-03-oq-05-oq-01`
(*"the density error `6·excludedCount N − N` is one-sided and genuinely unbounded, with order
`Θ(log N)`"*).

The parent settled the dichotomy by telescoping the `oq-03-oq-05` recursion
`excludedCount N = N/8 + excludedCount ⌈N/4⌉` into `E(N) = E(⌈N/4⌉) + δ(N)`, where
`E(N) = 6·excludedCount N − N` and `δ(N)` depends only on `N mod 8`, taking the eight values
`0, 0, −1, −2, −3, −3, −4, −5`.  It did this arithmetic *inline*, for the one extremal family
`a k`.  The parent also asserted the order is `Θ(log N)`, with the family `a k` (all steps
`δ = −4`) realising the lower bound.

This file isolates the per-step law as a reusable lemma and pins down the structure of the
worst case, addressing the natural next question:

> *Is the extremal rate really `4` per descent step (the family `a k`), given that a single
> step can cost as much as `5` (residue `7`)?  Why does `−5` not give a faster family?*

## What is new here

* `delta` is defined as a genuine function of the residue, `delta r = ⌊(r+3)/4⌋ − r`, and the
  **per-step law** `error_step` proves, for *every* `N`,
  `E(N) = E(⌈N/4⌉) + delta (N % 8)` — the parent's inline telescoping, now a standalone lemma.
* The **per-step bounds** `delta_nonpos` and `neg_five_le_delta` (`−5 ≤ delta (N%8) ≤ 0`) and
  the exact residue characterisations `delta_eq_zero_iff` (`r ∈ {0,1}`),
  `delta_eq_neg_four_iff` (`r = 6`), `delta_eq_neg_five_iff` (`r = 7`).
* The **sustainability obstruction** `quot_even_of_mod_seven`: when `N ≡ 7 (mod 8)` — the only
  residue with the maximal cost `δ = −5` — the next term `⌈N/4⌉` is **even**, hence not
  `≡ 7 (mod 8)`.  So a `−5` step is never immediately followed by another `−5`: the maximal
  single-step cost cannot sustain, which is exactly why the parent's all-`−4` family (residue
  `6`, which *does* chain to itself, `mod6_chains`) is the natural extremal one.
* The clean **descent inequality** `gap_step_le`: `gap N ≤ gap ⌈N/4⌉ + 5` where
  `gap N = N − 6·excludedCount N ≥ 0`, the per-step form behind the `Θ(log N)` bound.

All proofs are axiom-free and reuse the merged `oq-03-oq-05` recursion verbatim.

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/

open LagrangeFourSquaresWaringG2OQ03OQ05
open LagrangeFourSquaresWaringG2OQ03OQ05OQ01

namespace LagrangeFourSquaresWaringG2OQ03OQ05OQ01OQ01

/-! ## The per-step error contribution as a function of the residue -/

/-- **The per-step error contribution** `δ`, as an explicit function of the residue
`r = N mod 8`: `delta r = ⌊(r+3)/4⌋ − r`.  Over `r = 0,…,7` it takes the values
`0, 0, −1, −2, −3, −3, −4, −5`. -/
def delta (r : ℕ) : ℤ := ((r + 3) / 4 : ℕ) - (r : ℤ)

/-- **The per-step law.**  For every `N`, the density error `E(N) = 6·excludedCount N − N`
satisfies `E(N) = E(⌈N/4⌉) + delta (N mod 8)`.  This is the parent's inline telescoping of the
`oq-03-oq-05` recursion, isolated as a reusable lemma; `delta (N % 8)` depends only on the
residue. -/
theorem error_step (N : ℕ) :
    (6 : ℤ) * excludedCount N - N
      = ((6 : ℤ) * excludedCount ((N + 3) / 4) - ((N + 3) / 4 : ℕ)) + delta (N % 8) := by
  have hrec := excludedCount_rec N
  simp only [delta]
  rw [hrec]
  push_cast
  omega

/-! ## Per-step bounds and the residue dictionary -/

/-- Every descent step has nonpositive contribution: `delta (N mod 8) ≤ 0`. -/
theorem delta_nonpos (N : ℕ) : delta (N % 8) ≤ 0 := by
  simp only [delta]; omega

/-- No step costs more than `5`: `−5 ≤ delta (N mod 8)`. -/
theorem neg_five_le_delta (N : ℕ) : -5 ≤ delta (N % 8) := by
  simp only [delta]; omega

/-- A step is free (`delta = 0`) exactly for residues `0` and `1`. -/
theorem delta_eq_zero_iff (N : ℕ) : delta (N % 8) = 0 ↔ N % 8 = 0 ∨ N % 8 = 1 := by
  simp only [delta]; omega

/-- The cost is `4` exactly at residue `6`. -/
theorem delta_eq_neg_four_iff (N : ℕ) : delta (N % 8) = -4 ↔ N % 8 = 6 := by
  simp only [delta]; omega

/-- The maximal cost `5` occurs exactly at residue `7`. -/
theorem delta_eq_neg_five_iff (N : ℕ) : delta (N % 8) = -5 ↔ N % 8 = 7 := by
  simp only [delta]; omega

/-! ## Why the maximal cost cannot sustain -/

/-- **The `−5` step cannot chain.**  If `N ≡ 7 (mod 8)` — the unique residue with the maximal
cost `δ = −5` — then `⌈N/4⌉ = (N+3)/4` is **even**, so it is not `≡ 7 (mod 8)` and the next
step costs at most `4`.  This is why a sustained rate of `5` per step is impossible. -/
theorem quot_even_of_mod_seven (N : ℕ) (h : N % 8 = 7) : ((N + 3) / 4) % 2 = 0 := by
  omega

/-- **Residue `6` chains to itself.**  If `N ≡ 6 (mod 8)` and `N/8` is `≡ 2 (mod 4)`, then
`⌈N/4⌉ ≡ 6 (mod 8)` as well, so the cost-`4` step repeats — this is the mechanism behind the
parent's all-`−4` extremal family `a k`, the genuinely sustainable worst case. -/
theorem mod6_chains (N : ℕ) (h : N % 8 = 6) (h2 : (N / 8) % 4 = 2) :
    ((N + 3) / 4) % 8 = 6 := by
  omega

/-! ## The descent inequality -/

/-- The nonnegative gap `gap N = N − 6·excludedCount N` drops by exactly `−delta` per step. -/
theorem gap_step (N : ℕ) :
    (N : ℤ) - 6 * excludedCount N
      = (((N + 3) / 4 : ℕ) - 6 * excludedCount ((N + 3) / 4)) - delta (N % 8) := by
  have h := error_step N
  linarith

/-- **The per-step descent inequality** behind the `Θ(log N)` bound: each `⌈·/4⌉` step adds at
most `5` to the gap `gap N = N − 6·excludedCount N`. -/
theorem gap_step_le (N : ℕ) :
    (N : ℤ) - 6 * excludedCount N
      ≤ (((N + 3) / 4 : ℕ) - 6 * excludedCount ((N + 3) / 4)) + 5 := by
  have h := gap_step N
  have hb := neg_five_le_delta N
  linarith

/-- The gap is nonnegative and the per-step increment is at most `5`: the structural content of
"the one-sided error is `O(log N)`", combined with the parent's `six_excludedCount_le`. -/
theorem gap_nonneg_and_step (N : ℕ) :
    0 ≤ (N : ℤ) - 6 * excludedCount N ∧
      (N : ℤ) - 6 * excludedCount N
        ≤ (((N + 3) / 4 : ℕ) - 6 * excludedCount ((N + 3) / 4)) + 5 := by
  refine ⟨?_, gap_step_le N⟩
  have h := six_excludedCount_le N
  have : (6 : ℤ) * excludedCount N ≤ N := by exact_mod_cast h
  linarith

end LagrangeFourSquaresWaringG2OQ03OQ05OQ01OQ01

/-!
## Summary

* `delta` — the per-step error contribution as a function of `N mod 8`.
* `error_step` — the per-step law `E(N) = E(⌈N/4⌉) + delta (N mod 8)` for every `N`.
* `delta_nonpos`, `neg_five_le_delta`, and the residue dictionary — the eight step values.
* `quot_even_of_mod_seven` — the maximal cost `δ = −5` (residue `7`) cannot chain, because the
  next term is even; whereas `mod6_chains` shows residue `6` (cost `4`) does chain, the
  mechanism of the parent's sustainable extremal family.
* `gap_step_le` / `gap_nonneg_and_step` — the per-step descent inequality behind the one-sided
  `O(log N)` bound.

So the parent's `Θ(log N)` dichotomy rests on a single residue law, and the extremal *rate* is
`4` (sustainable, residue `6`) rather than `5` (residue `7`, which is forced to be isolated).

**Status**: 0 sorries, 0 `axiom` declarations, no `native_decide`.
-/
