import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-
# Equality Case of the Reverse Minkowski Inequality (cauchy-schwarz-integral-oq-02-oq-03-oq-01)

## The Open Question (from cauchy-schwarz-integral-oq-02-oq-03)

The parent file proved the **reverse Minkowski / reverse triangle inequality**
`|‖f‖ − ‖g‖| ≤ ‖f + g‖`, deriving it (for `p = 2`) from the Cauchy–Schwarz *lower*
bound `⟪f,g⟫ ≥ −‖f‖·‖g‖`, mirroring how the forward inequality uses the CS *upper*
bound. The natural follow-up:

> **When is the reverse Minkowski inequality an equality?** Characterise the pairs
> `(f, g)` for which `|‖f‖ − ‖g‖| = ‖f + g‖`.

## The Answer

Equality holds **iff the two vectors are antiparallel** — one is a *nonpositive* real
multiple of the other. The clean, division-free, zero-tolerant statement is

```
|‖u‖ − ‖v‖| = ‖u + v‖   ↔   ‖v‖ • u = −(‖u‖ • v).
```

### Why: the Cauchy–Schwarz lower bound must be *tight*

For a real inner-product space, expanding `‖u+v‖²` and `(‖u‖−‖v‖)²` shows
```
|‖u‖ − ‖v‖| = ‖u + v‖   ⟺   ⟪u,v⟫ = −‖u‖·‖v‖,
```
i.e. equality in reverse Minkowski is *exactly* saturation of the CS lower bound
`⟪u,v⟫ ≥ −‖u‖‖v‖`. By the equality case of Cauchy–Schwarz
(`inner_eq_norm_mul_iff_real`, applied to `(u, −v)`), this is equivalent to
`‖v‖ • u = −(‖u‖ • v)`, and for nonzero vectors to `v = r • u` for some `r < 0`.

### The mirror picture

This is the exact dual of the *forward* triangle equality
`‖u + v‖ = ‖u‖ + ‖v‖ ↔ ‖v‖ • u = ‖u‖ • v` (vectors *parallel*, `r ≥ 0`,
Mathlib's `norm_add_eq_iff_real`): the forward case saturates the CS *upper* bound,
the reverse case saturates the CS *lower* bound.

## Status (0 axioms, 0 sorries)
-/

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace ReverseMinkowskiEqCase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
## Section I: Reduction to the Cauchy–Schwarz lower bound

Equality `|‖u‖ − ‖v‖| = ‖u + v‖` is, after squaring both (nonnegative) sides and
expanding via `norm_add_sq_real`, exactly the statement that the inner product attains
its Cauchy–Schwarz *lower* bound: `⟪u,v⟫ = −‖u‖·‖v‖`.
-/

/-- **Equality in reverse Minkowski ⟺ the CS lower bound is tight.**
`|‖u‖ − ‖v‖| = ‖u + v‖` holds iff `⟪u,v⟫ = −‖u‖·‖v‖`. -/
theorem reverse_minkowski_eq_iff_inner (u v : E) :
    |‖u‖ - ‖v‖| = ‖u + v‖ ↔ ⟪u, v⟫_ℝ = -(‖u‖ * ‖v‖) := by
  rw [← pow_left_inj₀ (abs_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0),
    sq_abs, norm_add_sq_real]
  have expand : (‖u‖ - ‖v‖) ^ 2 = ‖u‖ ^ 2 + 2 * (-(‖u‖ * ‖v‖)) + ‖v‖ ^ 2 := by ring
  constructor
  · intro h; linarith [expand]
  · intro h; rw [h]; ring

/-!
## Section II: The vector characterisation (antiparallel)

Feeding the CS equality case `inner_eq_norm_mul_iff_real` the pair `(u, −v)` turns the
inner-product condition into the clean vector identity `‖v‖ • u = −(‖u‖ • v)`.
This form is symmetric, division-free, and handles the degenerate cases (`u = 0` or
`v = 0`) automatically.
-/

/-- **Equality case of reverse Minkowski (vector form).**
`|‖u‖ − ‖v‖| = ‖u + v‖ ↔ ‖v‖ • u = −(‖u‖ • v)` — the two vectors are *antiparallel*. -/
theorem reverse_minkowski_eq_iff (u v : E) :
    |‖u‖ - ‖v‖| = ‖u + v‖ ↔ ‖v‖ • u = -(‖u‖ • v) := by
  rw [reverse_minkowski_eq_iff_inner]
  have h := inner_eq_norm_mul_iff_real (x := u) (y := -v)
  simp only [inner_neg_right, norm_neg, smul_neg] at h
  rw [neg_eq_iff_eq_neg] at h
  exact h

/-- The reverse Minkowski inequality `|‖u‖ − ‖v‖| ≤ ‖u + v‖`, re-derived from the CS
lower bound (kept private as a helper for the strict-inequality characterisation). -/
private theorem reverse_minkowski_le (u v : E) : |‖u‖ - ‖v‖| ≤ ‖u + v‖ := by
  have h_cs : |⟪u, v⟫_ℝ| ≤ ‖u‖ * ‖v‖ := abs_real_inner_le_norm u v
  have h_ge : -(‖u‖ * ‖v‖) ≤ ⟪u, v⟫_ℝ := (abs_le.mp h_cs).1
  have h_sq : (‖u‖ - ‖v‖) ^ 2 ≤ ‖u + v‖ ^ 2 := by rw [norm_add_sq_real]; nlinarith [h_ge]
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (norm_nonneg _)] at h_sqrt

/-- **Strict reverse Minkowski.** The inequality is *strict* exactly when the vectors
are not antiparallel: `|‖u‖ − ‖v‖| < ‖u + v‖ ↔ ‖v‖ • u ≠ −(‖u‖ • v)`. -/
theorem reverse_minkowski_lt_iff (u v : E) :
    |‖u‖ - ‖v‖| < ‖u + v‖ ↔ ‖v‖ • u ≠ -(‖u‖ • v) := by
  rw [← not_iff_not, not_lt, not_ne_iff, ← reverse_minkowski_eq_iff]
  exact ⟨fun h => le_antisymm (reverse_minkowski_le u v) h, fun h => h.ge⟩

/-!
## Section III: Antiparallel = negative scalar multiple (nonzero vectors)

For nonzero `u, v` the vector condition `‖v‖ • u = −(‖u‖ • v)` is precisely
`v = r • u` for some `r < 0`: the vectors point in genuinely opposite directions.
-/

/-- **Equality case for nonzero vectors.** When `u ≠ 0` and `v ≠ 0`,
`|‖u‖ − ‖v‖| = ‖u + v‖` iff `v` is a *negative* real multiple of `u`. -/
theorem reverse_minkowski_eq_iff_neg_smul {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    |‖u‖ - ‖v‖| = ‖u + v‖ ↔ ∃ r : ℝ, r < 0 ∧ v = r • u := by
  have hne : ‖u‖ * ‖v‖ ≠ 0 := mul_ne_zero (norm_ne_zero_iff.2 hu) (norm_ne_zero_iff.2 hv)
  rw [reverse_minkowski_eq_iff_inner]
  have key := real_inner_div_norm_mul_norm_eq_neg_one_iff u v
  rw [div_eq_iff hne, neg_one_mul] at key
  rw [key]
  exact and_iff_right hu

/-!
## Section IV: Difference form and the forward/reverse mirror

Replacing `v` by `−v` converts the sum form into the difference form: equality in
`|‖u‖ − ‖v‖| = ‖u − v‖` characterises *parallel* vectors `‖v‖ • u = ‖u‖ • v` — the same
condition as the forward triangle equality `norm_add_eq_iff_real`.
-/

/-- **Difference form.** `|‖u‖ − ‖v‖| = ‖u − v‖ ↔ ‖v‖ • u = ‖u‖ • v` (vectors *parallel*),
obtained from `reverse_minkowski_eq_iff` by `v ↦ −v`. -/
theorem reverse_minkowski_sub_eq_iff (u v : E) :
    |‖u‖ - ‖v‖| = ‖u - v‖ ↔ ‖v‖ • u = ‖u‖ • v := by
  have h := reverse_minkowski_eq_iff u (-v)
  simp only [norm_neg, smul_neg, neg_neg, ← sub_eq_add_neg] at h
  exact h

/-- **The forward/reverse mirror, made explicit.** Forward triangle equality
(`‖u + v‖ = ‖u‖ + ‖v‖`, parallel) and reverse-with-difference equality
(`|‖u‖ − ‖v‖| = ‖u − v‖`, also parallel) are governed by the *same* collinearity
condition `‖v‖ • u = ‖u‖ • v`, hence are equivalent to each other. -/
theorem forward_iff_reverse_sub (u v : E) :
    ‖u + v‖ = ‖u‖ + ‖v‖ ↔ |‖u‖ - ‖v‖| = ‖u - v‖ := by
  rw [norm_add_eq_iff_real, reverse_minkowski_sub_eq_iff]

/-!
## Section V: Specialisation to L²(μ)

`Lp ℝ 2 μ` is a real inner-product space, so the equality case applies verbatim,
answering the open question in the measure-theoretic setting that motivated it.
-/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Equality case of reverse Minkowski in `L²(μ)`.** For `f, g ∈ L²(μ)`,
`|‖f‖ − ‖g‖| = ‖f + g‖` iff `‖g‖ • f = −(‖f‖ • g)`. -/
theorem reverse_minkowski_eq_iff_l2 (f g : Lp ℝ 2 μ) :
    |‖f‖ - ‖g‖| = ‖f + g‖ ↔ ‖g‖ • f = -(‖f‖ • g) :=
  reverse_minkowski_eq_iff f g

end ReverseMinkowskiEqCase
