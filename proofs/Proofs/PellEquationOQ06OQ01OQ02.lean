import Mathlib.NumberTheory.Pell
import Mathlib.Tactic

/-!
# The negative Pell chain as the norm −1 coset of `Pell.Solution₁ 2`

The parent entry (`pell-equation-oq-06-oq-01`) classifies the positive-integer
solutions of the **negative** Pell equation `x² − 2y² = −1` and proves the
scalar identity

  `(x² + 2y²)² − 2·(2xy)² = 1`   (`negPell_sq_is_pos_pell`),

showing that squaring a norm −1 solution produces a norm +1 solution.  That
statement lives entirely in `ℤ`; it does not touch Mathlib's group-theoretic
model of the Pell equation.

This follow-up **promotes the squaring bridge into Mathlib's `Pell.Solution₁ 2`**
— the commutative group of solutions of `X² − 2Y² = 1`, realised as the
norm +1 units of `ℤ√2`.  The organising principle is the *coset structure* of
the unit group of `ℤ√2`:

* the norm −1 solutions form a single coset of the norm +1 subgroup;
* the product of **two** norm −1 solutions has norm `(−1)·(−1) = +1`, so it lands
  in `Solution₁ 2` (`negMul`);
* the squaring bridge is exactly the diagonal of that product (`negSquare`), and
  the promoted value is *literally* the square `⟨x,y⟩²` inside `ℤ√2`
  (`coe_negSquare`);
* multiplying a positive solution by a negative one stays in the negative coset
  (`posMul_neg_norm`), witnessing that the negatives are the "other half" of the
  unit group.

Everything is derived from norm-multiplicativity of `ℤ√2` (Brahmagupta's
identity), so the proofs are `sorry`-free and axiom-free (no `native_decide`).

## Main statements

* `negMul_norm`  — Brahmagupta identity for `d = 2`: a product of two norm −1
  solutions is a norm +1 solution (scalar form).
* `negMul`       — the promotion of that product into `Pell.Solution₁ 2`.
* `coe_negMul`   — the promoted value is the honest product `⟨x₁,y₁⟩·⟨x₂,y₂⟩`
  in `ℤ√2`.
* `negSquare`    — the squaring bridge, valued in `Pell.Solution₁ 2`.
* `coe_negSquare`— the promoted square equals `⟨x,y⟩²` in `ℤ√2`.
* `negSquare_one_one` — the fundamental negative solution `(1,1)` squares to the
  fundamental positive Pell solution `(3,2)`.
* `posMul_neg_norm`   — the negative solutions are closed under the
  `Solution₁ 2`-action, i.e. they form a coset.
-/

namespace PellEquationOQ06OQ0102

open Pell

/-- **Brahmagupta identity for `d = 2` (scalar form).**  The product of two
solutions of the *negative* Pell equation `x² − 2y² = −1` satisfies the
*positive* Pell equation, because the norm form is multiplicative and
`(−1)·(−1) = 1`. -/
theorem negMul_norm (x₁ y₁ x₂ y₂ : ℤ)
    (h₁ : x₁ ^ 2 - 2 * y₁ ^ 2 = -1) (h₂ : x₂ ^ 2 - 2 * y₂ ^ 2 = -1) :
    (x₁ * x₂ + 2 * y₁ * y₂) ^ 2 - 2 * (x₁ * y₂ + y₁ * x₂) ^ 2 = 1 := by
  have key : (x₁ * x₂ + 2 * y₁ * y₂) ^ 2 - 2 * (x₁ * y₂ + y₁ * x₂) ^ 2
      = (x₁ ^ 2 - 2 * y₁ ^ 2) * (x₂ ^ 2 - 2 * y₂ ^ 2) := by ring
  rw [key, h₁, h₂]; norm_num

/-- **Promotion of a product of two negative-Pell solutions into
`Pell.Solution₁ 2`.**  Given two solutions of `x² − 2y² = −1`, their `ℤ√2`
product is a genuine element of Mathlib's positive Pell solution group. -/
def negMul (x₁ y₁ x₂ y₂ : ℤ)
    (h₁ : x₁ ^ 2 - 2 * y₁ ^ 2 = -1) (h₂ : x₂ ^ 2 - 2 * y₂ ^ 2 = -1) :
    Solution₁ 2 :=
  Solution₁.mk (x₁ * x₂ + 2 * y₁ * y₂) (x₁ * y₂ + y₁ * x₂)
    (negMul_norm x₁ y₁ x₂ y₂ h₁ h₂)

@[simp] theorem negMul_x (x₁ y₁ x₂ y₂ : ℤ)
    (h₁ : x₁ ^ 2 - 2 * y₁ ^ 2 = -1) (h₂ : x₂ ^ 2 - 2 * y₂ ^ 2 = -1) :
    (negMul x₁ y₁ x₂ y₂ h₁ h₂).x = x₁ * x₂ + 2 * y₁ * y₂ := rfl

@[simp] theorem negMul_y (x₁ y₁ x₂ y₂ : ℤ)
    (h₁ : x₁ ^ 2 - 2 * y₁ ^ 2 = -1) (h₂ : x₂ ^ 2 - 2 * y₂ ^ 2 = -1) :
    (negMul x₁ y₁ x₂ y₂ h₁ h₂).y = x₁ * y₂ + y₁ * x₂ := rfl

/-- The promoted solution's underlying `ℤ√2` value is *literally* the product of
the two negative solutions embedded in `ℤ√2`. -/
theorem coe_negMul (x₁ y₁ x₂ y₂ : ℤ)
    (h₁ : x₁ ^ 2 - 2 * y₁ ^ 2 = -1) (h₂ : x₂ ^ 2 - 2 * y₂ ^ 2 = -1) :
    ((negMul x₁ y₁ x₂ y₂ h₁ h₂ : Solution₁ 2) : ℤ√2)
      = (⟨x₁, y₁⟩ : ℤ√2) * ⟨x₂, y₂⟩ := by
  unfold negMul
  rw [Solution₁.coe_mk]
  ext <;> simp

/-- **The squaring bridge, promoted to `Pell.Solution₁ 2`.**  Squaring a single
negative-Pell solution `(x, y)` yields the positive Pell solution
`(x² + 2y², 2xy)`, now realised as an element of Mathlib's group. -/
def negSquare (x y : ℤ) (h : x ^ 2 - 2 * y ^ 2 = -1) : Solution₁ 2 :=
  negMul x y x y h h

@[simp] theorem negSquare_x (x y : ℤ) (h : x ^ 2 - 2 * y ^ 2 = -1) :
    (negSquare x y h).x = x ^ 2 + 2 * y ^ 2 := by
  unfold negSquare; rw [negMul_x]; ring

@[simp] theorem negSquare_y (x y : ℤ) (h : x ^ 2 - 2 * y ^ 2 = -1) :
    (negSquare x y h).y = 2 * x * y := by
  unfold negSquare; rw [negMul_y]; ring

/-- The promoted square is genuinely the group-square: its underlying `ℤ√2`
value equals `⟨x,y⟩²`.  This is the precise sense in which the scalar identity
`negPell_sq_is_pos_pell` "is" squaring inside Mathlib's Pell model. -/
theorem coe_negSquare (x y : ℤ) (h : x ^ 2 - 2 * y ^ 2 = -1) :
    ((negSquare x y h : Solution₁ 2) : ℤ√2) = (⟨x, y⟩ : ℤ√2) ^ 2 := by
  unfold negSquare; rw [coe_negMul, sq]

/-- The fundamental negative solution `(1,1)` (indeed `1² − 2·1² = −1`) squares to
the **fundamental positive Pell solution** `(3,2)` (`3² − 2·2² = 1`) of
`Pell.Solution₁ 2`. -/
theorem negSquare_one_one :
    negSquare 1 1 (by norm_num) = Solution₁.mk 3 2 (by norm_num) := by
  ext <;> simp

/-- **Coset closure.**  Multiplying a positive Pell solution `a ∈ Solution₁ 2` by
a negative solution `(x, y)` yields another negative solution (norm
`(+1)·(−1) = −1`).  Together with `negMul` this shows the norm −1 solutions form
a single coset of the norm +1 subgroup — the negative chain is exactly "half" of
the unit group of `ℤ√2`. -/
theorem posMul_neg_norm (a : Solution₁ 2) (x y : ℤ)
    (h : x ^ 2 - 2 * y ^ 2 = -1) :
    (a.x * x + 2 * a.y * y) ^ 2 - 2 * (a.x * y + a.y * x) ^ 2 = -1 := by
  have key : (a.x * x + 2 * a.y * y) ^ 2 - 2 * (a.x * y + a.y * x) ^ 2
      = (a.x ^ 2 - 2 * a.y ^ 2) * (x ^ 2 - 2 * y ^ 2) := by ring
  rw [key, a.prop, h]; ring

/-- Sanity check: the next negative solution `(7,5)` squares to the positive
solution `(99,70)` (indeed `99² − 2·70² = 1`). -/
example : negSquare 7 5 (by norm_num) = Solution₁.mk 99 70 (by norm_num) := by
  ext <;> simp

#check @negMul
#check @negSquare
#check @coe_negSquare
#check @posMul_neg_norm

end PellEquationOQ06OQ0102
