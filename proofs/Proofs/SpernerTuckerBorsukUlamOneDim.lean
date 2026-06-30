/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-!
# One-dimensional Borsuk–Ulam theorem (continuous capstone of `n = 1` Tucker)

The companion file `SpernerTuckerOneDim.lean` proves the **combinatorial** core of
the `n = 1` Borsuk–Ulam theorem: for a sign labelling of a path that is *antipodal
on the boundary*, some edge is **complementary** (its endpoints carry opposite
signs). That is the discrete statement
`TuckerOneDim.exists_complementary_edge`.

This file completes the `n = 1` line by carrying out the standard
**Tucker ⟹ Borsuk–Ulam** reduction. In general that reduction is an analytic
limit argument (refine the triangulation, mesh `→ 0`, extract a convergent
subsequence by compactness). In **dimension one** the limit collapses entirely to
the **Intermediate Value Theorem**: a continuous function whose two boundary
values are *antipodal* (`f a = - f b`) must vanish somewhere in between, exactly
as a discrete sign-change must occur across an antipodal boundary.

## Main results

* `BorsukUlamOneDim.exists_zero_of_antipodal`: the continuous analogue of
  `exists_complementary_edge`. If `f` is continuous on the interval between `a`
  and `b` with antipodal boundary values `f a = - f b`, then `f` has a zero in
  that interval.
* `BorsukUlamOneDim.borsuk_ulam_circle`: the **one-dimensional Borsuk–Ulam
  theorem**. A continuous `1`-periodic function `f : ℝ → ℝ` (equivalently, a
  continuous real function on the circle `S¹`) takes **equal values at some pair
  of antipodal points** `c` and `c + 1/2`.

## Relationship to the discrete result

The dictionary between the discrete (`SpernerTuckerOneDim`) and continuous
statements is:

| discrete (Tucker, `n = 1`)            | continuous (Borsuk–Ulam, `n = 1`)         |
|---------------------------------------|-------------------------------------------|
| sign labelling `λ : Fin (N+1) → ZMod 2` | continuous `f : ℝ → ℝ`                   |
| antipodal boundary `λ 0 ≠ λ (last N)` | antipodal boundary `f a = - f b`          |
| complementary edge (`λ` changes sign) | zero of `f` (IVT)                         |
| odd #complementary-edges (parity)     | nonempty zero set (connectedness/IVT)     |

Both are instances of "an antipodal boundary forces an interior witness"; the
discrete witness is counted by a `ZMod 2` parity, the continuous one by the
intermediate value theorem.

## References

* A. W. Tucker, *Some topological properties of disk and sphere* (1946).
* J. Matoušek, *Using the Borsuk–Ulam Theorem* (2003).

## Tags

Borsuk-Ulam, Tucker, antipodal, intermediate value theorem, circle
-/

open Set

namespace BorsukUlamOneDim

/-- `0` always lies in the (unordered) interval between `x` and `-x`. -/
private lemma zero_mem_uIcc_neg (x : ℝ) : (0 : ℝ) ∈ Set.uIcc x (-x) := by
  rw [Set.mem_uIcc]
  rcases le_total x 0 with h | h
  · exact Or.inl ⟨h, by linarith⟩
  · exact Or.inr ⟨by linarith, h⟩

/-- **One-dimensional Borsuk–Ulam, zero form** — the continuous analogue of the
discrete `TuckerOneDim.exists_complementary_edge`.

If `f` is continuous on the interval between `a` and `b` and its boundary values
are **antipodal** (`f a = - f b`), then `f` has a zero somewhere in the interval.
This is the intermediate value theorem applied at the value `0`, which always
lies between `f a` and `f b = - f a`. -/
theorem exists_zero_of_antipodal {a b : ℝ} (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.uIcc a b)) (hanti : f a = - f b) :
    ∃ c ∈ Set.uIcc a b, f c = 0 := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (f a) (f b) := by
    rw [hanti, Set.uIcc_comm]; exact zero_mem_uIcc_neg (f b)
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc hf h0
  exact ⟨c, hc, hfc⟩

/-- **One-dimensional Borsuk–Ulam theorem.** A continuous `1`-periodic function
`f : ℝ → ℝ` — equivalently, a continuous real-valued function on the circle
`S¹ = ℝ / ℤ` — takes **equal values at some pair of antipodal points**: there is
a point `c` with `f c = f (c + 1/2)`.

The proof is the textbook reduction to the one-variable case: the *antipodal
difference* `g x = f x - f (x + 1/2)` satisfies `g 0 = - g (1/2)` (using
`1`-periodicity, `f 1 = f 0`), so `g` has antipodal boundary values on
`[0, 1/2]` and hence a zero there by `exists_zero_of_antipodal`. -/
theorem borsuk_ulam_circle (f : ℝ → ℝ) (hf : Continuous f)
    (hper : ∀ x, f (x + 1) = f x) :
    ∃ c, f c = f (c + 1 / 2) := by
  -- `f 1 = f 0` from `1`-periodicity (with `0 + 1 = 1`).
  have hf1 : f 1 = f 0 := by simpa using hper 0
  -- The antipodal difference `g x = f x - f (x + 1/2)` is continuous.
  have hcont : Continuous (fun x => f x - f (x + 1 / 2)) := by fun_prop
  -- Its boundary values on `[0, 1/2]` are antipodal: `g 0 = - g (1/2)`.
  have hanti : (fun x => f x - f (x + 1 / 2)) 0
      = -((fun x => f x - f (x + 1 / 2)) (1 / 2)) := by
    simp only
    rw [show (0 : ℝ) + 1 / 2 = 1 / 2 by norm_num,
        show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num, hf1]
    ring
  -- IVT on the antipodal difference yields a coincident antipodal pair.
  obtain ⟨c, _, hc⟩ :=
    exists_zero_of_antipodal (fun x => f x - f (x + 1 / 2)) hcont.continuousOn hanti
  have hc' : f c - f (c + 1 / 2) = 0 := hc
  exact ⟨c, by linarith⟩

end BorsukUlamOneDim
