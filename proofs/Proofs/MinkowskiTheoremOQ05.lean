/-
# Power-Sum Convexity Bound and the Optimality of `2^(p-1)` (OQ-05)

## What This Proves

For a real exponent `p ≥ 1` and nonnegative reals `a, b`,
```
(a + b) ^ p ≤ 2 ^ (p - 1) · (a ^ p + b ^ p),
```
and the constant `2 ^ (p - 1)` is the **best possible**: equality holds at `a = b`,
and any constant `C` for which the inequality holds for all nonnegative `a, b`
must satisfy `C ≥ 2 ^ (p - 1)`. We package this as the statement that
`2 ^ (p - 1)` is the *least* element of the set of admissible constants:
```
IsLeast { C | ∀ a b ≥ 0, (a + b) ^ p ≤ C · (a ^ p + b ^ p) } (2 ^ (p - 1)).
```

This is the two-variable power-mean / convexity scaling bound underlying the `ℓ^p`
quasi-norm comparison constants: it is the reverse companion (for `p ≥ 1`) of the
sub-additivity `(a + b)^p ≥ a^p + b^p`, and it sharpens to an exact equality on the
diagonal `a = b`.

## Relation to Mathlib

Mathlib proves the inequality only for `ℝ≥0` (`NNReal.rpow_add_le_mul_rpow_add_rpow`,
`Mathlib/Analysis/MeanInequalitiesPow.lean`) and for `ℝ≥0∞`. The **real-valued
nonnegative** formulation — the one used directly when comparing `ℓ^p` constants over
`ℝ` — is absent, as is any statement that `2 ^ (p - 1)` is the optimal constant.
Here we:

1. Transport the `ℝ≥0` inequality to `ℝ` via the coercion
   (`rpow_add_le_two_rpow_sub_one_mul`).
2. Prove the diagonal equality `(a + a) ^ p = 2 ^ (p - 1) · (a ^ p + a ^ p)`
   (`rpow_add_self_eq`), the sharpness witness — note this holds for *every* real `p`.
3. Prove the lower bound on any admissible constant
   (`two_rpow_sub_one_le_of_forall`); the test point `a = b = 1` forces `C ≥ 2^(p-1)`.
4. Combine (1) and (3) into the optimality statement `isLeast_two_rpow_sub_one`.

## Key Techniques

- **NNReal → ℝ transport**: `lift _ to ℝ≥0` plus `exact_mod_cast` carries the
  Mathlib `ℝ≥0` inequality across the order-embedding coercion.
- **rpow arithmetic**: `Real.mul_rpow`, `Real.rpow_add`, `Real.rpow_sub`,
  `Real.rpow_one` to manipulate `2 ^ p = 2 · 2 ^ (p - 1)` and the diagonal equality.
- **Optimality via a test point**: evaluating the universal hypothesis at
  `a = b = 1` gives `2 ^ p ≤ 2 C`, hence `2 ^ (p - 1) ≤ C`.
-/

import Mathlib

open scoped NNReal

namespace MinkowskiTheoremOQ05

/-- **Power-sum convexity bound (real-valued form).** For `p ≥ 1` and nonnegative
reals `a, b`,
`(a + b) ^ p ≤ 2 ^ (p - 1) · (a ^ p + b ^ p)`.

This is the real-valued nonnegative version of Mathlib's
`NNReal.rpow_add_le_mul_rpow_add_rpow`, obtained by transporting the `ℝ≥0`
inequality through the coercion `ℝ≥0 → ℝ`. -/
theorem rpow_add_le_two_rpow_sub_one_mul (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    {p : ℝ} (hp : 1 ≤ p) :
    (a + b) ^ p ≤ (2 : ℝ) ^ (p - 1) * (a ^ p + b ^ p) := by
  lift a to ℝ≥0 using ha with a
  lift b to ℝ≥0 using hb with b
  have h := NNReal.rpow_add_le_mul_rpow_add_rpow a b hp
  exact_mod_cast h

/-- **Sharpness on the diagonal.** At `a = b` the inequality is an exact equality:
`(a + a) ^ p = 2 ^ (p - 1) · (a ^ p + a ^ p)`.

Together with `two_rpow_sub_one_le_of_forall` this shows the constant `2 ^ (p - 1)`
cannot be lowered. The identity holds for *every* real exponent `p` (it is pure
`rpow` arithmetic: both sides equal `2 ^ p · a ^ p`). -/
theorem rpow_add_self_eq (a : ℝ) (ha : 0 ≤ a) (p : ℝ) :
    (a + a) ^ p = (2 : ℝ) ^ (p - 1) * (a ^ p + a ^ p) := by
  have e1 : a + a = 2 * a := by ring
  have key : (2 : ℝ) ^ (p - 1) * (a ^ p + a ^ p)
      = (2 : ℝ) ^ (p - 1) * (2 : ℝ) ^ (1 : ℝ) * a ^ p := by
    rw [Real.rpow_one]; ring
  have hp1 : (p - 1) + 1 = p := by ring
  rw [e1, Real.mul_rpow (by norm_num) ha, key,
    ← Real.rpow_add (by norm_num : (0:ℝ) < 2), hp1]

/-- **Optimality of the constant.** If `C` is any constant for which
`(a + b) ^ p ≤ C · (a ^ p + b ^ p)` holds for all nonnegative `a, b`, then
`2 ^ (p - 1) ≤ C`.

The test point `a = b = 1` gives `2 ^ p ≤ 2 C`, and `2 ^ (p - 1) = 2 ^ p / 2`. -/
theorem two_rpow_sub_one_le_of_forall (C : ℝ) {p : ℝ}
    (h : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) ^ p ≤ C * (a ^ p + b ^ p)) :
    (2 : ℝ) ^ (p - 1) ≤ C := by
  have hbase := h 1 1 (by norm_num) (by norm_num)
  simp only [Real.one_rpow] at hbase
  have e11 : (1 : ℝ) + 1 = 2 := by norm_num
  rw [e11] at hbase
  -- hbase : (2 : ℝ) ^ p ≤ C * 2
  have e : (2 : ℝ) ^ (p - 1) = (2 : ℝ) ^ p / 2 := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2), Real.rpow_one]
  rw [e]
  linarith

/-- **The optimal constant is `2 ^ (p - 1)`.** For `p ≥ 1`, the constant
`2 ^ (p - 1)` is the least element of the set of constants `C` for which the
power-sum bound `(a + b) ^ p ≤ C · (a ^ p + b ^ p)` holds for all nonnegative
`a, b`.

This is the precise sense in which `2 ^ (p - 1)` is sharp: it is admissible
(`rpow_add_le_two_rpow_sub_one_mul`) and no smaller constant is
(`two_rpow_sub_one_le_of_forall`). -/
theorem isLeast_two_rpow_sub_one {p : ℝ} (hp : 1 ≤ p) :
    IsLeast {C : ℝ | ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) ^ p ≤ C * (a ^ p + b ^ p)}
      ((2 : ℝ) ^ (p - 1)) := by
  constructor
  · intro a b ha hb
    exact rpow_add_le_two_rpow_sub_one_mul a b ha hb hp
  · intro C hC
    exact two_rpow_sub_one_le_of_forall C hC

end MinkowskiTheoremOQ05
