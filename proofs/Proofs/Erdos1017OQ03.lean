import Mathlib

/-
# Erdős #1017 (OQ-03): closed forms and strict growth of the Turán extremal bound
# (erdos-1017-oq-03)

## Background

Erdős Problem #1017 concerns `f(n,k)`, the minimum number of complete subgraphs
needed to edge-partition every `n`-vertex `k`-edge graph. The Erdős–Goodman–Pósa
bound is `f ≤ ⌊n²/4⌋`, with the complete bipartite graph `K_{⌊n/2⌋,⌈n/2⌉}` (the
Turán extremal graph) achieving equality. The governing quantity is the **Turán
bound** `T(n) = ⌊n²/4⌋`, formalized in `Erdos1017OQ01.lean` with its product form
`T(n) = ⌊n/2⌋·(n − ⌊n/2⌋)` and basic monotonicity.

This sibling entry supplies the **explicit even/odd closed forms** and the
**strict** growth of `T`, which the parametric estimates of the partition problem
rely on. (Self-contained: `T` is re-declared, depending only on Mathlib.)

## Result

1. `turanBound_two_mul` — `T(2m) = m²`.
2. `turanBound_two_mul_add_one` — `T(2m+1) = m(m+1)`.
   (Together: the extremal `K_{m,m}` has `m²` edges, and `K_{m,m+1}` has
   `m(m+1)` edges.)
3. `turanBound_succ_diff` — the exact increment `T(n+1) − T(n) = ⌊(n+1)/2⌋`.
4. `turanBound_strictMono` — `T` is **strictly increasing** for `n ≥ 1`
   (`T(n) < T(n+1)`), sharpening the file's non-strict monotonicity.
5. `turanBound_le_sq_div_four` — the real-valued envelope `T(n) ≤ n²/4`.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

namespace Erdos1017OQ03

/-- The Turán extremal bound `T(n) = ⌊n²/4⌋` (re-declared from `Erdos1017OQ01`). -/
def turanBound (n : ℕ) : ℕ := n ^ 2 / 4

/-- **Even closed form:** `T(2m) = m²` — the extremal `K_{m,m}` has `m²` edges. -/
theorem turanBound_two_mul (m : ℕ) : turanBound (2 * m) = m ^ 2 := by
  unfold turanBound
  rw [show (2 * m) ^ 2 = 4 * m ^ 2 by ring, Nat.mul_div_cancel_left _ (by norm_num)]

/-- **Odd closed form:** `T(2m+1) = m(m+1)` — the extremal `K_{m,m+1}` has
    `m(m+1)` edges. -/
theorem turanBound_two_mul_add_one (m : ℕ) : turanBound (2 * m + 1) = m * (m + 1) := by
  unfold turanBound
  rw [show (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 by ring]
  omega

/-- **The exact increment:** `T(n+1) − T(n) = ⌊(n+1)/2⌋`. Adding a vertex to the
    balanced complete bipartite graph adds `⌈n/2⌉ = ⌊(n+1)/2⌋` edges. -/
theorem turanBound_succ_diff (n : ℕ) :
    turanBound (n + 1) - turanBound n = (n + 1) / 2 := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- n = m + m
    rw [show m + m + 1 = 2 * m + 1 from by ring, show m + m = 2 * m from by ring,
      turanBound_two_mul_add_one, turanBound_two_mul]
    have h : m * (m + 1) = m ^ 2 + m := by ring
    omega
  · -- n = 2m + 1
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) from by ring, turanBound_two_mul,
      turanBound_two_mul_add_one]
    have h : (m + 1) ^ 2 = m * (m + 1) + (m + 1) := by ring
    omega

/-- **Strict monotonicity:** `T(n) < T(n+1)` for `n ≥ 1`, sharpening the
    non-strict bound — each added vertex strictly increases the extremal edge
    count once the graph is nonempty. -/
theorem turanBound_strictMono (n : ℕ) (hn : 1 ≤ n) :
    turanBound n < turanBound (n + 1) := by
  have hdiff : turanBound (n + 1) - turanBound n = (n + 1) / 2 := turanBound_succ_diff n
  have hpos : 0 < (n + 1) / 2 := by omega
  omega

/-- **Real envelope:** `T(n) ≤ n²/4` over `ℝ` — the floor never exceeds the exact
    quarter-square. -/
theorem turanBound_le_sq_div_four (n : ℕ) :
    (turanBound n : ℝ) ≤ (n : ℝ) ^ 2 / 4 := by
  unfold turanBound
  have h : (((n ^ 2 / 4 : ℕ)) : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) / 4 := Nat.cast_div_le
  calc ((n ^ 2 / 4 : ℕ) : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) / 4 := h
    _ = (n : ℝ) ^ 2 / 4 := by push_cast; ring

/-
## Significance

The Turán bound `T(n) = ⌊n²/4⌋` is the extremal value in the Erdős–Goodman–Pósa
clique-partition theorem underlying Erdős #1017: it is both the worst-case number
of complete subgraphs needed and the edge count of the extremal complete
bipartite graph. The companion file records its product form and monotonicity;
this entry adds the explicit parity-split closed forms `T(2m) = m²`,
`T(2m+1) = m(m+1)`, the exact one-step increment `⌊(n+1)/2⌋`, the strict growth
for `n ≥ 1`, and the real envelope `T(n) ≤ n²/4`.

The closed forms make the extremal edge counts (`K_{m,m}` has `m²`, `K_{m,m+1}`
has `m(m+1)`) explicit, and the increment formula is exactly the quantity the
parametric question "can `f < ⌊n²/4⌋` once `k > n²/4`?" measures against: each
unit of edge surplus over `T(n)` is what a `K_4`-or-larger clique might convert
into a saving. The strict monotonicity guarantees the extremal threshold genuinely
grows with `n`, with no plateaus, so the dense regime `k > T(n)` is always
nonempty for `n ≥ 1`.
-/

end Erdos1017OQ03
