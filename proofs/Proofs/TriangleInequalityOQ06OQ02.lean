import Mathlib

/-
# The n-Point Telescoping Reverse Triangle Inequality (OQ-06-OQ-02)

The parent `triangle-inequality-oq-06` records the *three-point* reverse triangle
inequality `|d(x,z) - d(y,z)| ≤ d(x,y)` and its *quadrilateral* strengthening
`|d(x,y) - d(x',y')| ≤ d(x,x') + d(y,y')` (moving both endpoints), together with
their sharpness.  This child answers the natural next question: **what happens when
the two endpoints are joined not by a single edge but by a whole polygonal chain
`x₀, x₁, …, xₙ`?**

## The genuine content

The clean, substantive generalisation is the **telescoping reverse triangle
inequality**: for any chain `f : ℕ → α` and any fixed reference point `w`,

```
  |d(f 0, w) - d(f n, w)| ≤ Σ_{i < n} d(f i, f (i+1)).
```

The distance from a *moving* point to a fixed reference `w` changes by at most the
total length of the path the point travels.  For `n = 1` this is exactly the
three-point reverse inequality; the general statement is the *reverse* companion of
the polygon (path) inequality `d(f 0, f n) ≤ Σ d(f i, f (i+1))`.

The proof is a two-step composition — the three-point reverse inequality
`abs_dist_sub_le` feeding the polygon inequality `dist_le_range_sum_dist` — so the
inequality itself is short.  The **new mathematical content of this file is the
sharpness layer**: we certify that the telescoping bound is attained by an entire
family (any monotone real chain lying left of `w`), so it cannot be improved, and we
pin an explicit numeric witness.

## Contents

* `telescoping_reverse_triangle` — the main inequality (`α` a pseudometric space);
* `telescoping_reverse_triangle_one_sided` — the version without the absolute value;
* `reverse_triangle_of_telescoping` — the `n = 1` case recovers `abs_dist_sub_le`,
  witnessing that this genuinely generalises the parent;
* `telescoping_reverse_triangle_stated` — the faithful form of the problem
  statement, comparing the endpoint `xₙ`'s distance from `x₀` and from a side point
  `y` joined to `x₀` by one edge;
* `telescoping_reverse_triangle_sharp_mono` — **sharpness**: for a monotone real
  chain `a₀ ≤ a₁ ≤ ⋯ ≤ aₙ ≤ w`, the inequality is an *equality*;
* `telescoping_reverse_triangle_sharp_witness` — an explicit `0,1,2` chain with
  `w = 10` attaining the bound (`|10 - 8| = 1 + 1`).

Everything is `0`-axiom / `0`-sorry.
-/

namespace TriangleInequalityOQ06OQ02

/-! ## The main inequality (pseudometric spaces) -/

variable {α : Type*} [PseudoMetricSpace α]

/-- **n-Point telescoping reverse triangle inequality.**  The distance from a moving
point to a fixed reference `w` changes by at most the total length of the polygonal
path `f 0, f 1, …, f n`:
`|d(f 0, w) - d(f n, w)| ≤ Σ_{i < n} d(f i, f (i+1))`.

This is the *reverse* companion of the polygon inequality
`d(f 0, f n) ≤ Σ d(f i, f (i+1))`. -/
theorem telescoping_reverse_triangle (f : ℕ → α) (n : ℕ) (w : α) :
    |dist (f 0) w - dist (f n) w| ≤ ∑ i ∈ Finset.range n, dist (f i) (f (i + 1)) :=
  (abs_dist_sub_le (f 0) (f n) w).trans (dist_le_range_sum_dist f n)

/-- One-sided form of the telescoping reverse inequality (no absolute value). -/
theorem telescoping_reverse_triangle_one_sided (f : ℕ → α) (n : ℕ) (w : α) :
    dist (f 0) w - dist (f n) w ≤ ∑ i ∈ Finset.range n, dist (f i) (f (i + 1)) :=
  (le_abs_self _).trans (telescoping_reverse_triangle f n w)

/-- The `n = 1` case recovers the three-point reverse triangle inequality
`|d(x,w) - d(y,w)| ≤ d(x,y)`, confirming that the telescoping bound genuinely
generalises the parent `triangle-inequality-oq-06`. -/
theorem reverse_triangle_of_telescoping (x y w : α) :
    |dist x w - dist y w| ≤ dist x y := by
  have h := telescoping_reverse_triangle (fun i => if i = 0 then x else y) 1 w
  simpa using h

/-! ## The faithful problem statement

The problem statement compares the endpoint `xₙ`'s distance from the chain's start
`x₀` and from a side point `y` joined to `x₀` by a single edge:
`|d(x₀, xₙ) - d(y, xₙ)| ≤ d(x₀, y) + Σ_{i < n} d(x i, x (i+1))`.
Since the three-point reverse inequality already gives `≤ d(x₀, y)` on its own, the
nonnegative chain sum only slackens the bound; we record the faithful form for the
gallery. -/

/-- **Faithful form of the stated inequality.**
`|d(x₀, xₙ) - d(y, xₙ)| ≤ d(x₀, y) + Σ_{i < n} d(x i, x (i+1))`. -/
theorem telescoping_reverse_triangle_stated (x : ℕ → α) (y : α) (n : ℕ) :
    |dist (x 0) (x n) - dist y (x n)|
      ≤ dist (x 0) y + ∑ i ∈ Finset.range n, dist (x i) (x (i + 1)) := by
  have h1 : |dist (x 0) (x n) - dist y (x n)| ≤ dist (x 0) y := abs_dist_sub_le _ _ _
  have h2 : (0 : ℝ) ≤ ∑ i ∈ Finset.range n, dist (x i) (x (i + 1)) :=
    Finset.sum_nonneg fun i _ => dist_nonneg
  linarith

/-! ## Sharpness

The telescoping bound is attained by an entire family: any monotone real chain lying
to the left of the reference point `w`.  Hence the constant `1` in front of the sum
cannot be lowered and no term can be dropped — the inequality is sharp. -/

/-- **Sharpness of the telescoping reverse inequality.**  For a monotone real chain
`a 0 ≤ a 1 ≤ ⋯ ≤ a n ≤ w`, the telescoping reverse triangle inequality is an
*equality*:
`|d(a 0, w) - d(a n, w)| = Σ_{i < n} d(a i, a (i+1))`.

Both sides equal `a n - a 0`: the right-hand path sum telescopes, and on the left the
reference point `w` sits beyond the whole chain. -/
theorem telescoping_reverse_triangle_sharp_mono
    (a : ℕ → ℝ) (n : ℕ) (w : ℝ) (hmono : Monotone a) (hw : a n ≤ w) :
    |dist (a 0) w - dist (a n) w| = ∑ i ∈ Finset.range n, dist (a i) (a (i + 1)) := by
  have h0n : a 0 ≤ a n := hmono (Nat.zero_le n)
  have h0w : a 0 ≤ w := le_trans h0n hw
  -- The path sum telescopes to `a n - a 0`.
  have hsum : ∑ i ∈ Finset.range n, dist (a i) (a (i + 1)) = a n - a 0 := by
    have hstep : ∀ i ∈ Finset.range n,
        dist (a i) (a (i + 1)) = a (i + 1) - a i := by
      intro i _
      rw [Real.dist_eq, abs_of_nonpos (by linarith [hmono (Nat.le_succ i)])]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_range_sub a n]
  -- On the left, `w` lies beyond the chain, so both distances open up cleanly.
  have hd0 : dist (a 0) w = w - a 0 := by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; ring
  have hdn : dist (a n) w = w - a n := by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; ring
  rw [hsum, hd0, hdn, abs_of_nonneg (by linarith)]
  ring

/-- **Explicit sharp witness.**  The chain `0, 1, 2` with reference point `w = 10`
attains the telescoping bound: `|d(0,10) - d(2,10)| = |10 - 8| = 2 = 1 + 1 =
d(0,1) + d(1,2)`. -/
theorem telescoping_reverse_triangle_sharp_witness :
    |dist ((0 : ℝ)) 10 - dist ((2 : ℝ)) 10|
      = ∑ i ∈ Finset.range 2, dist ((i : ℝ)) ((i : ℝ) + 1) := by
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [Real.dist_eq]

/-! ## Axiom audit

All results above are `0`-axiom (depending only on the ordinary foundational axioms
`propext` / `Classical.choice` / `Quot.sound` — no `sorryAx`, no `Lean.ofReduceBool`,
no `decide` / `native_decide`).  The core inequality composes the Mathlib lemmas
`abs_dist_sub_le` and `dist_le_range_sum_dist`; the genuinely new content is the
sharpness layer `telescoping_reverse_triangle_sharp_mono`. -/

end TriangleInequalityOQ06OQ02
