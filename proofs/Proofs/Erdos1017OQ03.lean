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

/-- **Convexity of `T`:** `2·T(n+1) ≤ T(n) + T(n+2)`, i.e. the increments
    `T(n+1) − T(n) = ⌊(n+1)/2⌋` are nondecreasing in `n`. Where strict monotonicity
    says `T` never plateaus, convexity says its growth never decelerates — the Turán
    extremal count accelerates as vertices are added. -/
theorem turanBound_convex (n : ℕ) :
    2 * turanBound (n + 1) ≤ turanBound n + turanBound (n + 1 + 1) := by
  have h1 := turanBound_succ_diff n
  have h2 := turanBound_succ_diff (n + 1)
  have hm1 : turanBound n ≤ turanBound (n + 1) := by
    unfold turanBound; exact Nat.div_le_div_right (Nat.pow_le_pow_left (Nat.le_succ n) 2)
  have hm2 : turanBound (n + 1) ≤ turanBound (n + 1 + 1) := by
    unfold turanBound; exact Nat.div_le_div_right (Nat.pow_le_pow_left (Nat.le_succ (n + 1)) 2)
  omega

/-- **Asymptotic `T(n) ∼ n²/4`:** `T(n)/n² → 1/4` as `n → ∞`. The two-sided envelope
    `(n² − 1)/4 ≤ T(n) ≤ n²/4` divides through by `n²` to the squeeze
    `1/4 − 1/(4n²) ≤ T(n)/n² ≤ 1/4`, and the left side tends to `1/4` (since
    `(n²)⁻¹ → 0`). This is the precise asymptotic the sandwich was built to deliver. -/
theorem turanBound_div_sq_tendsto :
    Filter.Tendsto (fun n : ℕ => (turanBound n : ℝ) / (n : ℝ) ^ 2)
      Filter.atTop (nhds (1 / 4)) := by
  -- `n² → ∞`, hence `(n²)⁻¹ → 0`
  have hsq : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 2) Filter.atTop Filter.atTop :=
    (Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hinv : Filter.Tendsto (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) Filter.atTop (nhds 0) := by
    simpa using hsq.inv_tendsto_atTop
  -- the lower squeeze function `1/4 − (1/4)·(n²)⁻¹ → 1/4`
  have hlow : Filter.Tendsto (fun n : ℕ => 1 / 4 - 1 / 4 * ((n : ℝ) ^ 2)⁻¹)
      Filter.atTop (nhds (1 / 4)) := by
    have h0 : Filter.Tendsto (fun n : ℕ => 1 / 4 * ((n : ℝ) ^ 2)⁻¹) Filter.atTop (nhds 0) := by
      simpa using hinv.const_mul (1 / 4 : ℝ)
    simpa using h0.const_sub (1 / 4 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · -- `1/4 − 1/(4n²) ≤ T(n)/n²`
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsqpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ hsqpos]
    have hne : (n : ℝ) ^ 2 ≠ 0 := ne_of_gt hsqpos
    have hexp : (1 / 4 - 1 / 4 * ((n : ℝ) ^ 2)⁻¹) * (n : ℝ) ^ 2 = ((n : ℝ) ^ 2 - 1) / 4 := by
      field_simp
    rw [hexp]
    exact turanBound_ge_sq_sub_one_div_four n
  · -- `T(n)/n² ≤ 1/4`
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hsqpos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hsqpos]
    linarith [turanBound_le_sq_div_four n]

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
`T(n) ∼ n²/4` immediate.

The closed forms make the extremal edge counts (`K_{m,m}` has `m²`, `K_{m,m+1}`
has `m(m+1)`) explicit, and the increment formula is exactly the quantity the
parametric question "can `f < ⌊n²/4⌋` once `k > n²/4`?" measures against: each
unit of edge surplus over `T(n)` is what a `K_4`-or-larger clique might convert
into a saving. The strict monotonicity guarantees the extremal threshold genuinely
grows with `n`, with no plateaus, so the dense regime `k > T(n)` is always
nonempty for `n ≥ 1`.
-/

end Erdos1017OQ03
