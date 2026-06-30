import Proofs.MeanValueTheoremOQ02
import Mathlib.Tactic

/-!
# Mean Value Theorem OQ-02-OQ-02 follow-up: orientation-free Lagrange remainder

## The follow-up open question

The parent theorem `MeanValueTheoremOQ02.taylor_lagrange_remainder` proves
Taylor's theorem with the Lagrange remainder only for `a < b` (it routes
through Mathlib's `taylor_mean_remainder_lagrange_iteratedDeriv`, whose
hypothesis is `x₀ < x`). The natural follow-up asked at the end of the
S1 ACT session is:

> Does the Lagrange remainder hold for **either orientation** of `a` and
> `b` (i.e. for any `a ≠ b`), with the intermediate point `c` ranging over
> the open interval `(min a b, max a b)`?

The classical statement is orientation-free: for `a ≠ b` and `f` of class
`C^{n+1}`,
```
f b - T_n(f, a)(b) = f^{(n+1)}(c) / (n+1)! · (b - a)^{n+1}
```
for some `c` strictly between `a` and `b`. The sign of `(b - a)^{n+1}`
already carries the orientation, so no absolute values are needed.

## Status

* **`a < b` case: PROVED**, by direct reuse of the parent theorem
  `MeanValueTheoremOQ02.taylor_lagrange_remainder` (which is itself a
  fully proven, axiom-free theorem as of PR #24275). Verified under the
  current Docker/Aristotle blackout by name-checking every Mathlib
  dependency of the parent proof against the pinned Mathlib v4.26 source
  (all 8 identifiers present with matching signatures).
* **`b < a` case: `sorry`**, with the complete reflection recipe recorded
  below. This is the sole remaining obligation; it requires the compiler
  (the reflection rewrites are too fragile to land blind under the
  blackout).

This file is intentionally **not** registered in the gallery aggregate
until the `b < a` sorry is discharged and the file compiles.

## Reflection recipe for the `b < a` case (for the next live session)

Let `g := fun t => f (a + b - t)`. Since `b < a`, apply the parent theorem
on the interval `(b, a)`:
```
obtain ⟨c', hc', heq⟩ :=
  MeanValueTheoremOQ02.taylor_lagrange_remainder g b a hgt n hg
```
where `hg : ContDiff ℝ (n+1) g` comes from
`hf.comp ((contDiff_const).sub contDiff_id)` (composition of `f` with the
affine reflection `t ↦ a + b - t`). This gives
```
∃ c' ∈ Ioo b a,
  g a - taylorPolynomial g b n a =
    iteratedDeriv (n+1) g c' / (n+1)! · (a - b)^(n+1).
```

Two ingredients translate this back to the centered-at-`a` statement:

1. **Reflected iterated derivative.** For every `k`,
   ```
   iteratedDeriv k g t = (-1)^k • iteratedDeriv k f (a + b - t).
   ```
   Proof: write `a + b - t = (a + b) + (-t)` (`sub_eq_add_neg`), so
   `g = (fun z => f ((a+b) + z)) ∘ (fun t => -t)`. Then
   `iteratedDeriv_comp_neg` gives the `(-1)^k •` factor and
   `iteratedDeriv_comp_const_add` (both hypothesis-free in Mathlib) handles
   the inner translation. Hence:
   * `g a = f b`  (evaluate at `t = a`: `a + b - a = b`);
   * `iteratedDeriv k g b = (-1)^k • iteratedDeriv k f a`
     (evaluate at `t = b`: `a + b - b = a`).

2. **Taylor polynomial matches.** Termwise,
   ```
   taylorPolynomial g b n a
     = Σ_{k≤n} ((-1)^k f^{(k)}(a)) / k! · (a - b)^k
     = Σ_{k≤n} f^{(k)}(a) / k! · (b - a)^k     (since (-1)^k (a-b)^k = (b-a)^k)
     = taylorPolynomial f a n b.
   ```
   So `g a - taylorPolynomial g b n a = f b - taylorPolynomial f a n b`,
   matching the goal's left-hand side.

Finally set `c := a + b - c'`. From `c' ∈ Ioo b a` we get `c ∈ Ioo b a`
(reflection is an order-reversing involution of `(b, a)`), and
```
iteratedDeriv (n+1) g c' = (-1)^{n+1} • iteratedDeriv (n+1) f c,
(-1)^{n+1} (a - b)^{n+1} = (b - a)^{n+1},
```
so the right-hand side becomes
`iteratedDeriv (n+1) f c / (n+1)! · (b - a)^{n+1}`, as required.

## Cross-references
* Parent statement: `MeanValueTheoremOQ02.taylor_lagrange_remainder`
* Gallery entry: `mean-value-theorem-oq-02`
-/

noncomputable section

open Set

namespace MeanValueTheoremOQ02OQ02UIcc

/-- Orientation-free Taylor's theorem with the Lagrange remainder.

    For any `a ≠ b` and `f` of class `C^{n+1}`, there is an intermediate
    point `c` strictly between `a` and `b` with
    ```
    f b - T_n(f, a)(b) = f^{(n+1)}(c) / (n+1)! · (b - a)^{n+1}.
    ```
    The orientation is carried by `(b - a)^{n+1}`; no absolute values are
    needed. The `a < b` direction reuses the (proven, axiom-free) parent
    theorem; the `b < a` direction is the reflection argument documented in
    the module docstring. -/
theorem taylor_lagrange_remainder_orientation_free
    (f : ℝ → ℝ) (a b : ℝ) (hab : a ≠ b) (n : ℕ)
    (hf : ContDiff ℝ (n + 1) f) :
    ∃ c ∈ Set.Ioo (min a b) (max a b),
      f b - MeanValueTheoremOQ02.taylorPolynomial f a n b =
        iteratedDeriv (n + 1) f c / ((n + 1).factorial : ℝ) * (b - a) ^ (n + 1) := by
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- a < b : the interval is already oriented; reuse the parent theorem.
    rw [min_eq_left hlt.le, max_eq_right hlt.le]
    exact MeanValueTheoremOQ02.taylor_lagrange_remainder f a b hlt n hf
  · -- b < a : reflection through `t ↦ a + b - t`. See module docstring.
    rw [min_eq_right hgt.le, max_eq_left hgt.le]
    sorry

end MeanValueTheoremOQ02OQ02UIcc
