import Mathlib

/-
# Erdős #1017 (OQ-02): extremality of the balanced split in the Turán bound
# (erdos-1017-oq-02)

## Background

Erdős Problem #1017 concerns `f(n,k)`, the minimum number of complete subgraphs
needed to edge-partition every `n`-vertex `k`-edge graph. The Erdős–Goodman–Pósa
bound is `f ≤ ⌊n²/4⌋`, and the **complete bipartite graph** `K_{a,n-a}` — which is
triangle-free, so its `a·(n−a)` edges must be taken as individual cliques —
realises the worst case. The extremal example is the *balanced* graph
`K_{⌊n/2⌋,⌈n/2⌉}`, whose edge count equals the Turán bound `T(n) = ⌊n²/4⌋`.

The parent file `Erdos1017OQ01.lean` proves `K_{a,b}` has `a·b` edges and is
triangle-free; the sibling `Erdos1017OQ03.lean` gives the closed forms of `T`.
**Neither establishes *why* the balanced split is the one that attains `T(n)`.**
That is the quantitative content of this entry.

## Result

Writing the `n` vertices as `a + (n − a)`, the complete bipartite graph `K_{a,n-a}`
has `a·(n − a)` edges. We prove:

1. `four_mul_mul_le_add_sq` — the integer AM–GM kernel `4·a·b ≤ (a+b)²`.
2. `four_mul_mul_lt_add_sq` — its **strict** form when `a ≠ b`.
3. `mul_compl_le_turanBound` — **the upper bound** `a·(n − a) ≤ T(n)` for every
   split `a ≤ n`: no complete bipartite graph on `n` vertices has more than
   `⌊n²/4⌋` edges.
4. `balanced_mul_compl_eq_turanBound` — **equality at balance**
   `⌊n/2⌋·(n − ⌊n/2⌋) = T(n)`: the balanced split attains the bound.
5. `exists_balanced_max` — consequently `T(n)` is exactly the **maximum** of
   `a·(n − a)` over all splits, witnessed by `a = ⌊n/2⌋`.
6. `even_unbalanced_lt` — for even `n = 2m`, the balanced split is the **unique**
   maximiser: every `a ≠ m` gives strictly fewer than `m²` edges.

Together these pin down the Erdős–Goodman–Pósa extremal graph: among all complete
bipartite graphs on `n` vertices, edge count is maximised exactly at the balanced
split, with value `⌊n²/4⌋`.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

namespace Erdos1017OQ02

/-- The Turán extremal bound `T(n) = ⌊n²/4⌋` (re-declared from `Erdos1017OQ01`). -/
def turanBound (n : ℕ) : ℕ := n ^ 2 / 4

/-- **Even closed form:** `T(2m) = m²` (re-derived locally for self-containment). -/
theorem turanBound_two_mul (m : ℕ) : turanBound (2 * m) = m ^ 2 := by
  unfold turanBound
  rw [show (2 * m) ^ 2 = 4 * m ^ 2 by ring, Nat.mul_div_cancel_left _ (by norm_num)]

/-- **Odd closed form:** `T(2m+1) = m(m+1)`. -/
theorem turanBound_two_mul_add_one (m : ℕ) : turanBound (2 * m + 1) = m * (m + 1) := by
  unfold turanBound
  rw [show (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 by ring]
  omega

/-- **Integer AM–GM kernel:** `4·a·b ≤ (a+b)²` over `ℕ`. The gap is the perfect
    square `(a−b)²`; we expose it by the case split `a ≤ b` / `b ≤ a` so the proof
    never relies on truncated subtraction. -/
theorem four_mul_mul_le_add_sq (a b : ℕ) : 4 * (a * b) ≤ (a + b) ^ 2 := by
  rcases le_total a b with hab | hab
  · obtain ⟨d, rfl⟩ := Nat.le.dest hab
    nlinarith [Nat.zero_le (d ^ 2)]
  · obtain ⟨d, rfl⟩ := Nat.le.dest hab
    nlinarith [Nat.zero_le (d ^ 2)]

/-- **Strict integer AM–GM:** `4·a·b < (a+b)²` whenever `a ≠ b` — the square gap
    `(a−b)²` is then at least `1`. -/
theorem four_mul_mul_lt_add_sq (a b : ℕ) (h : a ≠ b) : 4 * (a * b) < (a + b) ^ 2 := by
  rcases le_total a b with hab | hab
  · obtain ⟨d, rfl⟩ := Nat.le.dest hab
    have hd : 1 ≤ d := by omega
    nlinarith [hd]
  · obtain ⟨d, rfl⟩ := Nat.le.dest hab
    have hd : 1 ≤ d := by omega
    nlinarith [hd]

/-- **The upper bound.** For any split `a ≤ n`, the complete bipartite graph
    `K_{a,n-a}` has `a·(n − a) ≤ T(n)` edges: no complete bipartite graph on `n`
    vertices exceeds `⌊n²/4⌋` edges. -/
theorem mul_compl_le_turanBound (n a : ℕ) (h : a ≤ n) :
    a * (n - a) ≤ turanBound n := by
  unfold turanBound
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 4)]
  have hb : a + (n - a) = n := Nat.add_sub_cancel' h
  calc a * (n - a) * 4 = 4 * (a * (n - a)) := by ring
    _ ≤ (a + (n - a)) ^ 2 := four_mul_mul_le_add_sq a (n - a)
    _ = n ^ 2 := by rw [hb]

/-- **Equality at balance.** The balanced split `a = ⌊n/2⌋` attains the bound:
    `⌊n/2⌋·(n − ⌊n/2⌋) = T(n)`. -/
theorem balanced_mul_compl_eq_turanBound (n : ℕ) :
    (n / 2) * (n - n / 2) = turanBound n := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- n = m + m
    have h1 : (m + m) / 2 = m := by omega
    have h2 : m + m - m = m := by omega
    rw [h1, h2, show m + m = 2 * m from by ring, turanBound_two_mul]
    ring
  · -- n = 2*m + 1
    have h1 : (2 * m + 1) / 2 = m := by omega
    have h2 : 2 * m + 1 - m = m + 1 := by omega
    rw [h1, h2, turanBound_two_mul_add_one]

/-- **`T(n)` is the maximum.** Combining the upper bound with equality at balance,
    `T(n)` is exactly the largest edge count among complete bipartite graphs on `n`
    vertices, witnessed by the balanced split `a = ⌊n/2⌋`. -/
theorem exists_balanced_max (n : ℕ) :
    ∃ a, a ≤ n ∧ a * (n - a) = turanBound n :=
  ⟨n / 2, Nat.div_le_self n 2, balanced_mul_compl_eq_turanBound n⟩

/-- **Uniqueness for even `n`.** When `n = 2m`, the balanced split is the *unique*
    maximiser: any unequal split `a ≠ m` yields strictly fewer than `m² = T(2m)`
    edges. -/
theorem even_unbalanced_lt (m a : ℕ) (ha : a ≤ 2 * m) (hne : a ≠ m) :
    a * (2 * m - a) < turanBound (2 * m) := by
  rw [turanBound_two_mul]
  have hb : a + (2 * m - a) = 2 * m := Nat.add_sub_cancel' ha
  have hne' : a ≠ 2 * m - a := by omega
  have key : 4 * (a * (2 * m - a)) < (a + (2 * m - a)) ^ 2 :=
    four_mul_mul_lt_add_sq a (2 * m - a) hne'
  rw [hb, show (2 * m) ^ 2 = 4 * m ^ 2 from by ring] at key
  exact Nat.lt_of_mul_lt_mul_left key

/-
## Significance

The Erdős–Goodman–Pósa theorem behind Erdős #1017 says every `n`-vertex graph can
be edge-partitioned into at most `⌊n²/4⌋` complete subgraphs, and that the bound is
sharp on a triangle-free graph, where every edge is its own clique. The sharp
example is the balanced complete bipartite graph `K_{⌊n/2⌋,⌈n/2⌉}`.

This entry supplies the extremal-graph fact that makes that example *the* extremal
one: among all complete bipartite splits `K_{a,n-a}` of the vertex set, the edge
count `a·(n − a)` is maximised precisely at the balanced split `a = ⌊n/2⌋`, with
maximum value `⌊n²/4⌋` (`mul_compl_le_turanBound` + `balanced_mul_compl_eq_turanBound`
⟹ `exists_balanced_max`), and for even `n` the maximiser is unique
(`even_unbalanced_lt`). The companion files record the edge count and triangle-
freeness of `K_{a,b}` and the closed forms of `T`; this one explains why the
balanced split, and no other, realises the Turán value.
-/

end Erdos1017OQ02
