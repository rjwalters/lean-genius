/-
# Markov Equation — Vieta Jumping as a Fiber Involution (OQ-05)

The parent development (`Proofs.MarkovEquation`) establishes that, fixing the
first two coordinates `x, y`, the map

  z ↦ 3xy − z

sends a Markov triple `(x, y, z)` to another Markov triple `(x, y, 3xy − z)`
(`markov_vieta`), and that this map is an involution in the third coordinate
(`markov_vieta_involutive`). It also computes the *product* of the two roots,
`z · (3xy − z) = x² + y²` (`markov_root_prod`).

What the parent leaves open — and what this file supplies — is the **structural
converse**: is `3xy − z` the *only* alternative? Concretely, fixing `x` and `y`,
the third coordinate ranges over the roots of the monic quadratic

  g(t) = t² − 3xy·t + (x² + y²),

which over an integral domain has **at most two** roots. Hence the fibre of the
Markov solution set over a fixed `(x, y)` is *exactly* the two-element set
`{z, 3xy − z}`, and Vieta jumping is a genuine **involutive permutation** of that
fibre. This is the precise justification for the informal phrase "`z` and `z'`
are the two roots of the quadratic" used throughout the Markov-tree literature.

We prove, all axiom-free and over `ℤ`:

* `markov_quadratic`   — every Markov `z` is a root of the monic quadratic `g`;
* `markov_vieta_sum`   — Vieta's *sum* formula `z + (3xy − z) = 3xy`
                          (companion to the parent's product formula);
* `markov_root_diff_sq`— the squared root-gap equals the discriminant
                          `(2z − 3xy)² = 9x²y² − 4(x² + y²)`;
* `markov_fiber_pair`  — **uniqueness**: any Markov `w` over `(x, y)` equals `z`
                          or `3xy − z` (the quadratic has ≤ 2 roots);
* `markov_fiber_eq`    — the fibre is exactly the doubleton `{z, 3xy − z}`;
* `markov_self_neighbor` — the two roots coincide iff `2z = 3xy`
                          (discriminant-zero / repeated-root boundary);
* `vietaPerm`          — Vieta jumping packaged as an `Equiv.Perm ℤ` that
                          preserves the Markov fibre.

None of these are in Mathlib (which has no Markov-equation development at all);
they build directly on the parent file.
-/
import Mathlib
import Proofs.MarkovEquation

namespace MarkovEquationOQ05

open MarkovEquation

/-! ## The monic quadratic and Vieta's formulas

Fixing `x, y`, the Markov equation `x² + y² + z² = 3xyz` says exactly that `z` is
a root of the monic quadratic `g(t) = t² − 3xy·t + (x² + y²)`. -/

/-- Every Markov third coordinate is a root of the monic quadratic
`g(t) = t² − 3xy·t + (x² + y²)`. -/
theorem markov_quadratic {x y z : ℤ} (h : IsMarkov x y z) :
    z ^ 2 - 3 * x * y * z + (x ^ 2 + y ^ 2) = 0 := by
  obtain ⟨_, _, _, he⟩ := h
  linear_combination he

/-- **Vieta's sum formula.** The two `z`-roots sum to `3xy`. This is the additive
companion of the parent's product formula `markov_root_prod`. -/
theorem markov_vieta_sum (x y z : ℤ) : z + (3 * x * y - z) = 3 * x * y := by ring

/-- **Discriminant / root-gap identity.** For a Markov triple the squared gap
between the two roots equals the discriminant of the quadratic:
`(2z − 3xy)² = 9x²y² − 4(x² + y²) = (3xy)² − 4(x² + y²)`. -/
theorem markov_root_diff_sq {x y z : ℤ} (h : IsMarkov x y z) :
    (2 * z - 3 * x * y) ^ 2 = 9 * x ^ 2 * y ^ 2 - 4 * (x ^ 2 + y ^ 2) := by
  obtain ⟨_, _, _, he⟩ := h
  have hz : z ^ 2 = 3 * x * y * z - x ^ 2 - y ^ 2 := by linarith
  calc (2 * z - 3 * x * y) ^ 2
      = 4 * z ^ 2 - 12 * x * y * z + 9 * x ^ 2 * y ^ 2 := by ring
    _ = 4 * (3 * x * y * z - x ^ 2 - y ^ 2) - 12 * x * y * z + 9 * x ^ 2 * y ^ 2 := by rw [hz]
    _ = 9 * x ^ 2 * y ^ 2 - 4 * (x ^ 2 + y ^ 2) := by ring

/-! ## Fibre uniqueness — the neighbour is the *only* alternative

A monic quadratic over the integral domain `ℤ` has at most two roots. Since both
`z` and any competing Markov value `w` (over the same `x, y`) are roots of the
same quadratic, `w` is forced to be `z` or its Vieta partner `3xy − z`. -/

/-- **Fibre uniqueness (≤ 2 roots).** If `(x, y, z)` and `(x, y, w)` are both
Markov triples, then `w = z` or `w = 3xy − z`. Equivalently: fixing `x, y`, the
third coordinate takes at most the two Vieta-conjugate values. -/
theorem markov_fiber_pair {x y z w : ℤ} (h : IsMarkov x y z) (hw : IsMarkov x y w) :
    w = z ∨ w = 3 * x * y - z := by
  have hwq : w ^ 2 - 3 * x * y * w + (x ^ 2 + y ^ 2) = 0 := markov_quadratic hw
  have hzp : z * (3 * x * y - z) = x ^ 2 + y ^ 2 := markov_root_prod h
  -- `g(w) = 0` factors as `(w − z)(w − (3xy − z)) = 0`.
  have key : (w - z) * (w - (3 * x * y - z)) = 0 := by linear_combination hwq + hzp
  rcases mul_eq_zero.mp key with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (sub_eq_zero.mp h2)

/-- **The Markov fibre is a doubleton.** Fixing `x, y`, the set of valid third
coordinates is exactly `{z, 3xy − z}`. Combines uniqueness (`markov_fiber_pair`,
the `⊆` direction) with existence (`h` and `markov_vieta`, the `⊇` direction). -/
theorem markov_fiber_eq {x y z : ℤ} (h : IsMarkov x y z) :
    {w : ℤ | IsMarkov x y w} = {z, 3 * x * y - z} := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hw; exact markov_fiber_pair h hw
  · rintro (rfl | rfl)
    · exact h
    · exact markov_vieta h

/-- **Repeated-root boundary.** The two Vieta conjugates coincide precisely when
`2z = 3xy` (equivalently, when the discriminant `(2z − 3xy)²` vanishes). -/
theorem markov_self_neighbor (x y z : ℤ) : 3 * x * y - z = z ↔ 2 * z = 3 * x * y := by
  constructor <;> intro h <;> linarith

/-! ## Vieta jumping as an involutive permutation

Fixing `x, y`, the map `z ↦ 3xy − z` is an involution of all of `ℤ`, so it is a
permutation (`Equiv.Perm ℤ`). It restricts to an involution of the two-element
Markov fibre, swapping the two roots. -/

/-- The Vieta map `z ↦ 3xy − z` is involutive on `ℤ`. -/
theorem vieta_involutive (x y : ℤ) :
    Function.Involutive (fun z : ℤ => 3 * x * y - z) := by
  intro z; simp only; ring

/-- **Vieta jumping as a permutation.** For fixed `x, y`, `z ↦ 3xy − z` is a
permutation of `ℤ` (an involution). -/
def vietaPerm (x y : ℤ) : Equiv.Perm ℤ := (vieta_involutive x y).toPerm

@[simp] theorem vietaPerm_apply (x y z : ℤ) : vietaPerm x y z = 3 * x * y - z := rfl

/-- `vietaPerm` is its own inverse. -/
@[simp] theorem vietaPerm_symm (x y : ℤ) : (vietaPerm x y).symm = vietaPerm x y := rfl

/-- Applying `vietaPerm` twice returns the original coordinate. -/
theorem vietaPerm_involutive (x y z : ℤ) : vietaPerm x y (vietaPerm x y z) = z := by
  simp

/-- `vietaPerm` preserves the Markov fibre: it maps Markov triples to Markov
triples over the same `(x, y)`. -/
theorem vietaPerm_mem {x y z : ℤ} (h : IsMarkov x y z) :
    IsMarkov x y (vietaPerm x y z) := by
  rw [vietaPerm_apply]; exact markov_vieta h

/-- **Fixed points of Vieta jumping.** `vietaPerm x y` fixes `z` iff `2z = 3xy`,
i.e. exactly at the repeated-root boundary. -/
theorem vietaPerm_fixed (x y z : ℤ) : vietaPerm x y z = z ↔ 2 * z = 3 * x * y := by
  rw [vietaPerm_apply]; exact markov_self_neighbor x y z

end MarkovEquationOQ05
