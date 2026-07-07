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
6. `turanBound_four_mul` — the exact integer identity `4·T(n) = n² − (n mod 2)`
   (equivalently `n² mod 4 = n mod 2`).
7. `turanBound_ge_sq_sub_one_div_four` — the matching lower real envelope
   `(n² − 1)/4 ≤ T(n)`, sandwiching `T` as `(n² − 1)/4 ≤ T(n) ≤ n²/4`.
8. `turanBound_quarter_square` — the classical **quarter-square multiplication
   identity** `T(m+n) − T(m−n) = m·n` (for `n ≤ m`), recovering a product as the
   gap between the quarter-squares of sum and difference.
9. `turanBound_second_diff` — the exact discrete **second difference**
   `T(n+2) + T(n) = 2·T(n+1) + (n+1) mod 2`.
10. `turanBound_convex` — `T` is a **convex** integer sequence
    (`2·T(n+1) ≤ T(n+2) + T(n)`).

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

/-- **Exact integer identity:** `4·T(n) = n² − (n mod 2)`. The quarter-square loses
    exactly the parity bit: nothing for even `n`, one unit for odd `n`. Equivalently
    `n² mod 4 = n mod 2`, so the floor `⌊n²/4⌋` is `n²/4` rounded down by `0` or `¼`. -/
theorem turanBound_four_mul (n : ℕ) : 4 * turanBound n = n ^ 2 - n % 2 := by
  unfold turanBound
  have hmod : n ^ 2 % 4 = n % 2 := by
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [show (m + m) ^ 2 = 4 * m ^ 2 by ring]; omega
    · rw [show (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 by ring]; omega
  have hsplit := Nat.div_add_mod (n ^ 2) 4
  omega

/-- **Lower real envelope:** `(n² − 1)/4 ≤ T(n)` over `ℝ`. Together with
    `turanBound_le_sq_div_four` this sandwiches the Turán bound,
    `(n² − 1)/4 ≤ T(n) ≤ n²/4`, with equality on the right for even `n` and on the
    left for odd `n` (the floor discards at most `¼`). -/
theorem turanBound_ge_sq_sub_one_div_four (n : ℕ) :
    ((n : ℝ) ^ 2 - 1) / 4 ≤ (turanBound n : ℝ) := by
  unfold turanBound
  have hmod : n ^ 2 % 4 ≤ 1 := by
    rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [show (m + m) ^ 2 = 4 * m ^ 2 by ring]; omega
    · rw [show (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 by ring]; omega
  have hsplit := Nat.div_add_mod (n ^ 2) 4
  have hint : (n : ℝ) ^ 2 ≤ 4 * ((n ^ 2 / 4 : ℕ) : ℝ) + 1 := by
    have hnat : n ^ 2 ≤ 4 * (n ^ 2 / 4) + 1 := by omega
    have hcast := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at hcast
    linarith
  linarith

/-- **Quarter-square multiplication identity:** `T(m+n) − T(m−n) = m·n` (for `n ≤ m`).
    This is the classical identity that turns the Turán bound into a *multiplication
    table*: the product `m·n` is recovered as the gap between the quarter-squares of
    the sum and the difference. Combinatorially, expanding the balanced bipartite
    graph from `m−n` to `m+n` vertices (a symmetric `±n` shift about `m`) adds exactly
    `m·n` edges. The parity bits of `m+n` and `m−n` agree (they differ by `2n`), so
    the floors cancel cleanly. -/
theorem turanBound_quarter_square (m n : ℕ) (h : n ≤ m) :
    turanBound (m + n) = turanBound (m - n) + m * n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  -- `m = n + d`, so `m + n = 2*n + d`, `m - n = d`, `m * n = (n + d) * n`.
  have hsub : n + d - n = d := by omega
  have hadd : n + d + n = 2 * n + d := by ring
  rw [hsub, hadd]
  have h1 := turanBound_four_mul (2 * n + d)
  have h2 := turanBound_four_mul d
  have hsq : (2 * n + d) ^ 2 = d ^ 2 + 4 * ((n + d) * n) := by ring
  have hpar : (2 * n + d) % 2 = d % 2 := by omega
  omega

/-- **Exact second difference:** `T(n+2) + T(n) = 2·T(n+1) + (n+1) mod 2`. The
    discrete second difference `Δ²T(n) = T(n+2) − 2·T(n+1) + T(n)` equals `1` at even
    `n` and `0` at odd `n`. It is the increment of the increment `⌊(n+1)/2⌋`, which
    bumps up exactly when `n` is even. -/
theorem turanBound_second_diff (n : ℕ) :
    turanBound (n + 2) + turanBound n = 2 * turanBound (n + 1) + (n + 1) % 2 := by
  have hle : ∀ k, turanBound k ≤ turanBound (k + 1) := fun k => by
    unfold turanBound; exact Nat.div_le_div_right (Nat.pow_le_pow_left (Nat.le_succ k) 2)
  have hd1 : turanBound (n + 1) - turanBound n = (n + 1) / 2 := turanBound_succ_diff n
  have hd2 : turanBound (n + 2) - turanBound (n + 1) = (n + 2) / 2 :=
    turanBound_succ_diff (n + 1)
  have hm1 := hle n
  have hm2 : turanBound (n + 1) ≤ turanBound (n + 2) := hle (n + 1)
  omega

/-- **Discrete convexity:** `2·T(n+1) ≤ T(n+2) + T(n)`, i.e. `T` is a convex integer
    sequence (its second difference is `≥ 0`). The quarter-square never bends
    downward, so the extremal edge count has no concave dips as `n` grows. -/
theorem turanBound_convex (n : ℕ) :
    2 * turanBound (n + 1) ≤ turanBound (n + 2) + turanBound n := by
  have h := turanBound_second_diff n
  omega

/-! ### 8. Extremal product characterization: `T(n) = max_{a+b=n} a·b`.

The closed forms above give the *value* of `T` but not the extremal *principle*
behind it. Erdős #1017's bound `⌊n²/4⌋` is the Turán/Mantel extremal edge count:
the complete bipartite graph `K_{a,b}` on `a+b = n` vertices has `a·b` edges, and
`⌊n²/4⌋` is exactly the **maximum** of `a·b` over all balanced/unbalanced splits.
We pin this down: every product `a·b` with `a+b = n` is at most `T(n)`
(`turanBound_ge_mul`), and the balanced split `⌊n/2⌋·⌈n/2⌉` attains it
(`turanBound_eq_mul_split`). Hence `T(n)` is the greatest element of the set of
achievable edge products — the AM-GM optimum `4·a·b = (a+b)² − (a−b)²`. -/

/-- Every bipartition product is bounded by the Turán bound:
    `a·b ≤ T(a+b)` for all `a, b`. This is the AM-GM optimum
    `4ab = (a+b)² − (a−b)²`, with the odd-parity deficit absorbed by
    `(a−b)² ≥ (a+b) mod 2` (equal parity of `a−b` and `a+b`). -/
theorem turanBound_ge_mul (a b : ℕ) : a * b ≤ turanBound (a + b) := by
  have h4 : 4 * turanBound (a + b) = (a + b) ^ 2 - (a + b) % 2 := turanBound_four_mul (a + b)
  rcases Nat.even_or_odd (a + b) with he | ho
  · -- even split: `4ab ≤ (a+b)²`.
    have h0 : (a + b) % 2 = 0 := Nat.even_iff.mp he
    rw [h0] at h4
    have key : 4 * (a * b) ≤ (a + b) ^ 2 := by
      have hz : (4 * (a * b) : ℤ) ≤ ((a + b) ^ 2 : ℤ) := by
        nlinarith [sq_nonneg ((a : ℤ) - (b : ℤ))]
      exact_mod_cast hz
    omega
  · -- odd split: `a ≠ b`, so `(a−b)² ≥ 1` gives `4ab + 1 ≤ (a+b)²`.
    have h1 : (a + b) % 2 = 1 := Nat.odd_iff.mp ho
    rw [h1] at h4
    have hne : (a : ℤ) - b ≠ 0 := by
      intro hcontra
      have hab : a = b := by
        have : (a : ℤ) = b := by linarith
        exact_mod_cast this
      subst hab
      omega
    have hsq : (1 : ℤ) ≤ ((a : ℤ) - b) ^ 2 := by
      rcases hne.lt_or_gt with hl | hl <;> nlinarith
    have key : 4 * (a * b) + 1 ≤ (a + b) ^ 2 := by
      have hz : (4 * (a * b) + 1 : ℤ) ≤ ((a + b) ^ 2 : ℤ) := by nlinarith [hsq]
      exact_mod_cast hz
    omega

/-- The balanced split attains the bound: `T(n) = ⌊n/2⌋·(n − ⌊n/2⌋)`. Together with
    `turanBound_ge_mul` this shows `T(n)` is the maximum edge-product `a·b` over all
    `a + b = n`, realized by the balanced complete bipartite graph. -/
theorem turanBound_eq_mul_split (n : ℕ) : turanBound n = (n / 2) * (n - n / 2) := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show m + m = 2 * m from by ring, turanBound_two_mul,
      show (2 * m) / 2 = m from by omega, show 2 * m - m = m from by omega]
    ring
  · rw [turanBound_two_mul_add_one, show (2 * m + 1) / 2 = m from by omega,
      show 2 * m + 1 - m = m + 1 from by omega]

/-- **`T(n)` is the greatest achievable edge-product.** The Turán bound is exactly
    the maximum of `a·b` over all bipartitions `a + b = n`: it is achieved (by the
    balanced split) and dominates every split. This is the extremal characterization
    of `⌊n²/4⌋` underlying Erdős #1017. -/
theorem turanBound_isGreatest_product (n : ℕ) :
    IsGreatest {p : ℕ | ∃ a b, a + b = n ∧ p = a * b} (turanBound n) := by
  constructor
  · -- membership: the balanced split `(n/2, n − n/2)` realizes `T(n)`.
    exact ⟨n / 2, n - n / 2, by omega, turanBound_eq_mul_split n⟩
  · -- upper bound: every product is at most `T(n)`.
    rintro p ⟨a, b, rfl, rfl⟩
    exact turanBound_ge_mul a b

/-
## Significance

The Turán bound `T(n) = ⌊n²/4⌋` is the extremal value in the Erdős–Goodman–Pósa
clique-partition theorem underlying Erdős #1017: it is both the worst-case number
of complete subgraphs needed and the edge count of the extremal complete
bipartite graph. The companion file records its product form and monotonicity;
this entry adds the explicit parity-split closed forms `T(2m) = m²`,
`T(2m+1) = m(m+1)`, the exact one-step increment `⌊(n+1)/2⌋`, the strict growth
for `n ≥ 1`, the exact integer identity `4·T(n) = n² − (n mod 2)`, and the
two-sided real envelope `(n² − 1)/4 ≤ T(n) ≤ n²/4`. The sandwich pins `T(n)`
within `¼` of the exact quarter-square `n²/4`, making the asymptotics
`T(n) ∼ n²/4` immediate. The 2026-06-30 additions record the **algebraic
structure** of `T`: the quarter-square multiplication identity
`T(m+n) − T(m−n) = m·n` (the device that historically turned quarter-square
tables into multiplication tables), the exact second difference
`Δ²T(n) = (n+1) mod 2`, and the resulting **discrete convexity** of `T` — so the
extremal edge count grows without any concave dips.

The closed forms make the extremal edge counts (`K_{m,m}` has `m²`, `K_{m,m+1}`
has `m(m+1)`) explicit, and the increment formula is exactly the quantity the
parametric question "can `f < ⌊n²/4⌋` once `k > n²/4`?" measures against: each
unit of edge surplus over `T(n)` is what a `K_4`-or-larger clique might convert
into a saving. The strict monotonicity guarantees the extremal threshold genuinely
grows with `n`, with no plateaus, so the dense regime `k > T(n)` is always
nonempty for `n ≥ 1`.
-/

end Erdos1017OQ03

-- Axiom audit: foundational axioms only; no `Lean.ofReduceBool`, no `sorryAx`.
#print axioms Erdos1017OQ03.turanBound_ge_mul
#print axioms Erdos1017OQ03.turanBound_isGreatest_product
