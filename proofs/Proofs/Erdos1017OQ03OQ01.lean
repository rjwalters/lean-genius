import Mathlib

/-
# Erdős #1017 (OQ-03 → OQ-01): the quarter-square ↔ triangular-number bridge
# (erdos-1017-oq-03-oq-01)

## Background

Erdős Problem #1017 concerns the extremal **Turán bound** `T(n) = ⌊n²/4⌋` — both the
worst-case number of complete subgraphs needed to edge-partition an `n`-vertex graph
and the edge count of the balanced complete bipartite (Turán) graph. The sibling file
`Erdos1017OQ03.lean` records its parity-split closed forms `T(2m) = m²`, `T(2m+1) = m(m+1)`,
the one-step increment `⌊(n+1)/2⌋`, and the two-sided envelope `(n²−1)/4 ≤ T(n) ≤ n²/4`.

This child entry records the **exact link between the quarter-square sequence `T` and
the triangular numbers**. The central identity

  `T(n) + T(n+1) = C(n+1, 2) = n(n+1)/2`

says that two consecutive quarter-squares sum to a triangular number, giving a clean
combinatorial reading: the edge counts of the two extremal bipartite graphs on `n` and
`n+1` vertices add up to the number of edges of the *complete* graph `K_{n+1}`. Together
with the exact two-step increment `T(n+2) = T(n) + (n+1)` and the accumulation formula
`T(n) = ∑_{k<n} ⌈k/2⌉`, this pins the additive structure of `T`.

## Result

1. `turanBound_succ` — the additive one-step increment `T(n+1) = T(n) + ⌊(n+1)/2⌋`.
2. `turanBound_two_step` — the exact two-step increment `T(n+2) = T(n) + (n+1)`
   (division-free; the symmetric `±1` shift about `n+1` adds exactly `n+1` edges).
3. `turanBound_two_step_diff` — the subtraction form `T(n+2) − T(n) = n+1`.
4. `turanBound_add_succ` — the exact identity `2·(T(n) + T(n+1)) = n(n+1)`
   (a consecutive pair of quarter-squares is twice a triangular number).
5. `turanBound_add_succ_triangular` — `T(n) + T(n+1) = n(n+1)/2`, the `n`-th
   triangular number.
6. `turanBound_add_succ_choose` — `T(n) + T(n+1) = C(n+1, 2)`, the edge count of
   `K_{n+1}` (the quarter-square ↔ binomial bridge).
7. `turanBound_eq_sum` — the accumulation formula `T(n) = ∑_{k<n} ⌊(k+1)/2⌋`,
   expressing `T` as the running sum of its increments `⌈k/2⌉`.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

namespace Erdos1017OQ03OQ01

/-- The Turán extremal bound `T(n) = ⌊n²/4⌋` (re-declared; depends only on Mathlib). -/
def turanBound (n : ℕ) : ℕ := n ^ 2 / 4

/-- **Additive one-step increment:** `T(n+1) = T(n) + ⌊(n+1)/2⌋`. Adding one vertex to
    the balanced complete bipartite graph adds `⌈n/2⌉ = ⌊(n+1)/2⌋` edges. -/
theorem turanBound_succ (n : ℕ) : turanBound (n + 1) = turanBound n + (n + 1) / 2 := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- n = m + m
    have e0 : turanBound (m + m) = m ^ 2 := by
      unfold turanBound; rw [show (m + m) ^ 2 = 4 * m ^ 2 by ring]; omega
    have e1 : turanBound (m + m + 1) = m ^ 2 + m := by
      unfold turanBound; rw [show (m + m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 by ring]; omega
    rw [e0, e1]; omega
  · -- n = 2m + 1
    have e1 : turanBound (2 * m + 1) = m ^ 2 + m := by
      unfold turanBound; rw [show (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 by ring]; omega
    have e2 : turanBound (2 * m + 1 + 1) = m ^ 2 + 2 * m + 1 := by
      unfold turanBound; rw [show (2 * m + 1 + 1) ^ 2 = 4 * (m ^ 2 + 2 * m + 1) by ring]; omega
    rw [e1, e2]; omega

/-- **Exact two-step increment:** `T(n+2) = T(n) + (n+1)` — division-free. Expanding the
    balanced bipartite graph by two vertices (a symmetric `±1` shift about `n+1`) adds
    exactly `n+1` edges, independent of the parity of `n`. -/
theorem turanBound_two_step (n : ℕ) : turanBound (n + 2) = turanBound n + (n + 1) := by
  unfold turanBound
  rw [show (n + 2) ^ 2 = n ^ 2 + (n + 1) * 4 by ring, Nat.add_mul_div_right _ _ (by norm_num)]

/-- **Two-step difference:** `T(n+2) − T(n) = n+1`, the subtraction form of the exact
    two-step increment. -/
theorem turanBound_two_step_diff (n : ℕ) : turanBound (n + 2) - turanBound n = n + 1 := by
  have h := turanBound_two_step n; omega

/-- **Quarter-square pair = twice a triangular number:** `2·(T(n) + T(n+1)) = n(n+1)`.
    Two consecutive quarter-squares add to a triangular number (the exact, division-free
    form). -/
theorem turanBound_add_succ (n : ℕ) :
    2 * (turanBound n + turanBound (n + 1)) = n * (n + 1) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- n = m + m
    have e0 : turanBound (m + m) = m ^ 2 := by
      unfold turanBound; rw [show (m + m) ^ 2 = 4 * m ^ 2 by ring]; omega
    have e1 : turanBound (m + m + 1) = m ^ 2 + m := by
      unfold turanBound; rw [show (m + m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 by ring]; omega
    rw [e0, e1]; ring
  · -- n = 2m + 1
    have e1 : turanBound (2 * m + 1) = m ^ 2 + m := by
      unfold turanBound; rw [show (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 by ring]; omega
    have e2 : turanBound (2 * m + 1 + 1) = (m + 1) ^ 2 := by
      unfold turanBound; rw [show (2 * m + 1 + 1) ^ 2 = 4 * (m + 1) ^ 2 by ring]; omega
    rw [e1, e2]; ring

/-- **Triangular-number form:** `T(n) + T(n+1) = n(n+1)/2`, the `n`-th triangular number.
    The sum of the two consecutive extremal bipartite edge counts is exactly `1 + 2 + ⋯ + n`. -/
theorem turanBound_add_succ_triangular (n : ℕ) :
    turanBound n + turanBound (n + 1) = n * (n + 1) / 2 := by
  have h := turanBound_add_succ n; omega

/-- **Quarter-square ↔ binomial bridge:** `T(n) + T(n+1) = C(n+1, 2)`. The two extremal
    bipartite edge counts on `n` and `n+1` vertices sum to the edge count of the complete
    graph `K_{n+1}` — every edge of `K_{n+1}` is accounted for exactly once. -/
theorem turanBound_add_succ_choose (n : ℕ) :
    turanBound n + turanBound (n + 1) = Nat.choose (n + 1) 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel, turanBound_add_succ_triangular]
  congr 1
  ring

/-- **Accumulation formula:** `T(n) = ∑_{k<n} ⌊(k+1)/2⌋`. The Turán bound is the running
    sum of its one-step increments `⌈k/2⌉ = ⌊(k+1)/2⌋`. -/
theorem turanBound_eq_sum (n : ℕ) :
    turanBound n = ∑ k ∈ Finset.range n, (k + 1) / 2 := by
  induction n with
  | zero => simp [turanBound]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, turanBound_succ]

/-
## Significance

The Turán bound `T(n) = ⌊n²/4⌋` is the extremal value of the Erdős–Goodman–Pósa
clique-partition theorem underlying Erdős #1017. The sibling `Erdos1017OQ03.lean`
records its closed forms, monotonicity, and real envelope; this entry records the
**additive bridge to the triangular numbers**:

- The central identity `T(n) + T(n+1) = C(n+1, 2) = n(n+1)/2` says two consecutive
  quarter-squares sum to a triangular number — combinatorially, the edge counts of the
  extremal bipartite graphs on `n` and `n+1` vertices together tile the complete graph
  `K_{n+1}`.
- The exact two-step increment `T(n+2) = T(n) + (n+1)` is division-free and parity-blind:
  every symmetric two-vertex expansion of the balanced bipartite graph adds exactly
  `n+1` edges.
- The accumulation formula `T(n) = ∑_{k<n} ⌈k/2⌉` expresses `T` as the running sum of its
  increments, tying the closed form back to the one-step growth law.

Together these pin the additive/telescoping structure of the quarter-square sequence,
complementing the multiplicative quarter-square identity `T(m+n) − T(m−n) = m·n` and the
discrete convexity recorded in the sibling file.
-/

end Erdos1017OQ03OQ01
