/-
# Ultrametric balls of a fixed radius partition the space (OQ-07)

The parent `triangle-inequality` proves the *forward* inequality
`d(x, z) ≤ d(x, y) + d(y, z)`.  In a **non-Archimedean (ultrametric)** space the
*strong* triangle inequality

  `d(x, z) ≤ max (d(x, y)) (d(y, z))`

holds, and it forces a rigid geometry of balls.  The literal OQ-07 question asks to
derive that *every point of an open ball is its center*:

  `y ∈ ball x r  →  ball x r = ball y r`.

Mathlib already records this single fact (`IsUltrametricDist.ball_eq_of_mem`).  The
**genuinely new content** of this file is the *structural* upgrade that Mathlib does
**not** bundle:

* the fixed-radius relation `SameBall r x y := d(x, y) < r` is an **equivalence
  relation** (for `r > 0`) — reflexivity is `d(x,x) = 0 < r`, symmetry is `dist_comm`,
  and **transitivity is exactly the strong triangle inequality** `max_lt`;
* its equivalence classes are *precisely* the open balls of radius `r`
  (`ballSetoid_class`, `balls_eq_classes`);
* therefore the radius-`r` balls form a **partition** of the whole space
  (`balls_isPartition` : `Setoid.IsPartition`), from which pairwise-disjointness and
  the covering property drop out (`balls_pairwiseDisjoint`, `balls_sUnion_eq_univ`).

So in an ultrametric space "being within `r`" is a *transitive* notion — which is the
conceptual reason a ball has no distinguished centre.  We close with the concrete
instantiation on the `p`-adic numbers `ℚ_[p]` (an ultrametric field), where the
radius-`1` balls are the residue discs partitioning the field.

This is distinct from the existing siblings, which treat the *inequality itself*
(`triangle-inequality-oq-02` p-adic, `triangle-inequality-oq-03` abstract "every
triangle is isosceles"); here the object of study is the induced **ball partition**.

**Status**: Complete — 0 sorries, 0 axioms.
-/

import Mathlib

namespace TriangleInequalityOQ07

open Metric Set

variable {X : Type*} [MetricSpace X] [IsUltrametricDist X]

/-- The "same radius-`r` ball" relation: two points are related when they lie within
distance `< r`.  Equivalently `x ∈ ball y r`. -/
def SameBall (r : ℝ) (x y : X) : Prop := dist x y < r

omit [IsUltrametricDist X] in
lemma sameBall_iff_mem_ball {r : ℝ} {x y : X} : SameBall r x y ↔ x ∈ ball y r :=
  mem_ball.symm

/-- **The fixed-radius "same ball" relation is an equivalence relation.**  The three
axioms are, respectively, `d(x,x) = 0 < r`, `dist_comm`, and the *strong* triangle
inequality (transitivity is what fails in a general metric space). -/
def ballSetoid (r : ℝ) (hr : 0 < r) : Setoid X where
  r := SameBall r
  iseqv :=
    { refl := fun x => by simp only [SameBall, dist_self]; exact hr
      symm := fun {x y} h => by
        show dist y x < r
        rwa [dist_comm]
      trans := fun {x y z} hxy hyz =>
        lt_of_le_of_lt (IsUltrametricDist.dist_triangle_max x y z) (max_lt hxy hyz) }

/-- The equivalence class of `y` under `ballSetoid r` is exactly the open ball
`ball y r`. -/
lemma ballSetoid_class (r : ℝ) (hr : 0 < r) (y : X) :
    {x | (ballSetoid r hr) x y} = ball y r := by
  ext x
  simp only [Set.mem_setOf_eq, mem_ball]
  rfl

/-- The equivalence classes of `ballSetoid r` are *precisely* the open balls of
radius `r`. -/
lemma balls_eq_classes (r : ℝ) (hr : 0 < r) :
    (ballSetoid r hr).classes = {s : Set X | ∃ y : X, s = ball y r} := by
  ext s
  simp only [Setoid.classes, Set.mem_setOf_eq, ballSetoid_class r hr]

/-- **Ultrametric balls partition the space.**  For any `r > 0`, the collection of
open balls of radius `r` is a partition of `X`: every point lies in a unique such
ball.  This is the structural heart of OQ-07. -/
theorem balls_isPartition (r : ℝ) (hr : 0 < r) :
    Setoid.IsPartition {s : Set X | ∃ y : X, s = ball y r} := by
  rw [← balls_eq_classes r hr]
  exact Setoid.isPartition_classes _

/-- The radius-`r` balls are pairwise disjoint (as distinct blocks of the partition).
Equivalently: two open balls of the same radius are equal or disjoint. -/
theorem balls_pairwiseDisjoint (r : ℝ) (hr : 0 < r) :
    {s : Set X | ∃ y : X, s = ball y r}.PairwiseDisjoint id :=
  (balls_isPartition r hr).pairwiseDisjoint

/-- The radius-`r` balls cover the whole space. -/
theorem balls_sUnion_eq_univ (r : ℝ) (hr : 0 < r) :
    ⋃₀ {s : Set X | ∃ y : X, s = ball y r} = Set.univ :=
  (balls_isPartition r hr).sUnion_eq_univ

/-- **Every point of an open ball is its center** — the literal OQ-07 statement,
now seen as the "class representatives are interchangeable" facet of the partition. -/
theorem ball_eq_of_mem (r : ℝ) {x y : X} (h : y ∈ ball x r) : ball x r = ball y r :=
  IsUltrametricDist.ball_eq_of_mem h

/-- Two open balls of the same radius are equal or disjoint (the dichotomy underlying
the partition). -/
theorem ball_eq_or_disjoint (r : ℝ) (x y : X) :
    ball x r = ball y r ∨ Disjoint (ball x r) (ball y r) :=
  IsUltrametricDist.ball_eq_or_disjoint x y r

/-- Each radius-`r` ball is clopen — the topological shadow of the partition (an
ultrametric space is totally disconnected). -/
theorem isClopen_ball (r : ℝ) (x : X) : IsClopen (ball x r) :=
  IsUltrametricDist.isClopen_ball x r

/-! ### Concrete instance: the `p`-adic numbers `ℚ_[p]`

`ℚ_[p]` carries an `IsUltrametricDist` instance, so the radius-`1` balls (the residue
discs `{y : ‖y - a‖ < 1}`) partition the field. -/

section Padic
variable (p : ℕ) [Fact p.Prime]

/-- In `ℚ_[p]`, the radius-`1` balls partition the field. -/
example : Setoid.IsPartition {s : Set ℚ_[p] | ∃ y : ℚ_[p], s = ball y 1} :=
  balls_isPartition 1 one_pos

/-- In `ℚ_[p]`, any point of a unit ball is its center. -/
example {x y : ℚ_[p]} (h : y ∈ ball x 1) : ball x 1 = ball y 1 :=
  ball_eq_of_mem 1 h

end Padic

end TriangleInequalityOQ07
