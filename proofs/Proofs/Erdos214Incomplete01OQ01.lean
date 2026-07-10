/-
# Erdős #214: the √2-scaled integer lattice is unit-distance-free
  (the hypothesis of Problem #214 is non-vacuous)

## Source
The gallery entry `erdos-214` (Juhász's theorem: a unit-distance-free set has a
unit square in its complement) defines the example set

  `ScaledLattice = { (√2·a, √2·b) : a, b ∈ ℤ }`

but proves nothing about it. This entry supplies the missing verification that
`ScaledLattice` is genuinely **unit-distance-free**, so the hypothesis of #214 is
non-vacuous — a concrete, fully machine-checked (0-axiom) witness, independent of
the axiomatized Juhász theorem.

## What This Proves

For two points of `ScaledLattice`, say `(√2·a, √2·b)` and `(√2·a', √2·b')`, the
squared Euclidean distance is

  `(√2)²·(a-a')² + (√2)²·(b-b')² = 2·((a-a')² + (b-b')²)`,

an **even** integer. It can never equal `1²= 1`, because `2·(m² + k²) = 1` is
impossible for integers `m, k` (the left side is even). Hence no two lattice
points are at distance exactly `1`.

**Main results:**
- `dist_eq_coords`: the coordinate formula `dist p q = √((p₀-q₀)² + (p₁-q₁)²)`.
- `two_mul_sq_add_sq_ne_one`: `2·(m² + k²) ≠ 1` for integers `m, k` (the arithmetic core).
- `scaledLattice_dist_ne_one`: any two points of `ScaledLattice` are at distance `≠ 1`.
- `scaledLattice_unitDistanceFree`: `ScaledLattice` is unit-distance-free.
- `scaledLattice_nonempty`: `0 ∈ ScaledLattice` (the set is inhabited).

## Structure of the Argument

`dist_eq_coords` unfolds the Euclidean norm on `EuclideanSpace ℝ (Fin 2)` to the
two-coordinate Pythagorean form (mirroring the `dist_coords` helper of the parent
entry). Substituting the lattice coordinates and using `(√2)² = 2` collapses each
squared coordinate difference to `2·(integer)²`; the radicand is `2·((a-a')² +
(b-b')²)`. If its square root were `1`, squaring gives `2·((a-a')² + (b-b')²) = 1`,
refuted by `two_mul_sq_add_sq_ne_one` (an `omega` parity argument after casting
back to `ℤ`). Note the conclusion needs no `p ≠ q` hypothesis: the distance is
never `1` even for equal points (it is then `0`).

Fully machine-checked, self-contained over Mathlib, no `sorry`, no extra axioms
(in particular it does **not** use the parent's `juhasz_1979` / `juhasz_stronger`).

## Depends on
Mathlib only. Re-states the parent's `Plane`, `dist`, `IsUnitDistanceFree`,
`ScaledLattice` so the result stands free of the axiomatized core.
-/

import Mathlib

set_option linter.unusedVariables false

namespace Erdos214Incomplete01OQ01

/-- The Euclidean plane `ℝ²`. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- Euclidean distance between two points of the plane. -/
noncomputable def dist (p q : Plane) : ℝ := ‖p - q‖

/-- `S` is **unit-distance-free** if no two distinct points are exactly distance `1` apart. -/
def IsUnitDistanceFree (S : Set Plane) : Prop :=
  ∀ p q : Plane, p ∈ S → q ∈ S → p ≠ q → dist p q ≠ 1

/-- The **`√2`-scaled integer lattice** `{ (√2·a, √2·b) : a, b ∈ ℤ }`. -/
def ScaledLattice : Set Plane :=
  {p : Plane | ∃ a b : ℤ, p 0 = Real.sqrt 2 * a ∧ p 1 = Real.sqrt 2 * b}

/-- **Coordinate distance formula.** On `EuclideanSpace ℝ (Fin 2)` the distance is
the Pythagorean combination of the two coordinate differences. -/
theorem dist_eq_coords (p q : Plane) :
    dist p q = Real.sqrt ((p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2) := by
  unfold dist
  rw [← dist_eq_norm, EuclideanSpace.dist_eq, Fin.sum_univ_two]
  simp only [Real.dist_eq, sq_abs]

/-- **Arithmetic core.** `2·(m² + k²) = 1` is impossible for integers `m, k`: the
left-hand side is even. -/
theorem two_mul_sq_add_sq_ne_one (m k : ℤ) : 2 * ((m : ℝ) ^ 2 + (k : ℝ) ^ 2) ≠ 1 := by
  intro h
  have hc : ((2 * (m ^ 2 + k ^ 2) : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by push_cast; linarith
  have : 2 * (m ^ 2 + k ^ 2) = 1 := by exact_mod_cast hc
  omega

/-- **Any two points of `ScaledLattice` are at distance `≠ 1`.** The squared
distance is `2·((a-a')² + (b-b')²)`, an even integer, never equal to `1`. (No
`p ≠ q` hypothesis is needed.) -/
theorem scaledLattice_dist_ne_one {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice) : dist p q ≠ 1 := by
  obtain ⟨a, b, hpa, hpb⟩ := hp
  obtain ⟨a', b', hqa, hqb⟩ := hq
  rw [dist_eq_coords]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : (p 0 - q 0) ^ 2 = 2 * ((a : ℝ) - a') ^ 2 := by
    rw [hpa, hqa]
    have e : (Real.sqrt 2 * (a : ℝ) - Real.sqrt 2 * a') ^ 2
        = Real.sqrt 2 ^ 2 * ((a : ℝ) - a') ^ 2 := by ring
    rw [e, hs]
  have hy : (p 1 - q 1) ^ 2 = 2 * ((b : ℝ) - b') ^ 2 := by
    rw [hpb, hqb]
    have e : (Real.sqrt 2 * (b : ℝ) - Real.sqrt 2 * b') ^ 2
        = Real.sqrt 2 ^ 2 * ((b : ℝ) - b') ^ 2 := by ring
    rw [e, hs]
  rw [hx, hy]
  intro hcontra
  have hnn : 0 ≤ 2 * ((a : ℝ) - a') ^ 2 + 2 * ((b : ℝ) - b') ^ 2 := by positivity
  have h1 := Real.sq_sqrt hnn
  rw [hcontra] at h1
  have hsq : 2 * ((a : ℝ) - a') ^ 2 + 2 * ((b : ℝ) - b') ^ 2 = 1 := by simpa using h1.symm
  have hkey : 2 * (((a - a' : ℤ) : ℝ) ^ 2 + ((b - b' : ℤ) : ℝ) ^ 2) = 1 := by
    push_cast; linarith
  exact two_mul_sq_add_sq_ne_one (a - a') (b - b') hkey

/-- **The `√2`-scaled integer lattice is unit-distance-free** — so the hypothesis
of Erdős #214 is non-vacuous. Immediate from `scaledLattice_dist_ne_one`. -/
theorem scaledLattice_unitDistanceFree : IsUnitDistanceFree ScaledLattice :=
  fun p q hp hq _ => scaledLattice_dist_ne_one hp hq

/-- `ScaledLattice` is inhabited: the origin lies in it (`a = b = 0`). -/
theorem scaledLattice_nonempty : (0 : Plane) ∈ ScaledLattice := by
  refine ⟨0, 0, ?_, ?_⟩ <;> simp

/-!
## Strengthening: `√2·ℤ²` is free of an infinite family of distances

`scaledLattice_unitDistanceFree` is the special case `n = 1` of a much stronger
fact.  The squared distance between two lattice points is
`2·((a-a')² + (b-b')²)`, an **even** integer, so it can never equal an **odd**
integer.  Hence no two lattice points are at distance `√n` for *any* odd `n` — of
which unit distance (`√1 = 1`) is merely the first instance.  This exhibits
`√2·ℤ²` as simultaneously free of the infinite family of distances
`{√1, √3, √5, √7, …}`, a genuine generalization of the non-vacuity witness.
-/

/-- **Squared lattice distances are even integers.**  For any two points of
`ScaledLattice`, `dist p q ^ 2 = 2·m` for some integer `m ≥ 0` (namely
`m = (a-a')² + (b-b')²`).  This is the structural fact underlying every
"distance-free" statement about the lattice. -/
theorem scaledLattice_dist_sq_even {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice) :
    ∃ m : ℤ, 0 ≤ m ∧ dist p q ^ 2 = 2 * (m : ℝ) := by
  obtain ⟨a, b, hpa, hpb⟩ := hp
  obtain ⟨a', b', hqa, hqb⟩ := hq
  refine ⟨(a - a') ^ 2 + (b - b') ^ 2, by positivity, ?_⟩
  rw [dist_eq_coords]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : (p 0 - q 0) ^ 2 = 2 * ((a : ℝ) - a') ^ 2 := by
    rw [hpa, hqa]
    have e : (Real.sqrt 2 * (a : ℝ) - Real.sqrt 2 * a') ^ 2
        = Real.sqrt 2 ^ 2 * ((a : ℝ) - a') ^ 2 := by ring
    rw [e, hs]
  have hy : (p 1 - q 1) ^ 2 = 2 * ((b : ℝ) - b') ^ 2 := by
    rw [hpb, hqb]
    have e : (Real.sqrt 2 * (b : ℝ) - Real.sqrt 2 * b') ^ 2
        = Real.sqrt 2 ^ 2 * ((b : ℝ) - b') ^ 2 := by ring
    rw [e, hs]
  have hnn : 0 ≤ (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by positivity
  rw [Real.sq_sqrt hnn, hx, hy]
  push_cast; ring

/-- **`√2·ℤ²` avoids every odd square-root distance.**  For any odd natural `n`,
no two points of `ScaledLattice` are at distance `√n`: the squared distance is
even, but `n` is odd.  Taking `n = 1` recovers `scaledLattice_unitDistanceFree`.
(No `p ≠ q` hypothesis is needed: for `p = q` the distance is `0 ≠ √n` since
`n ≥ 1`.) -/
theorem scaledLattice_dist_ne_sqrt_odd {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice)
    {n : ℕ} (hodd : Odd n) : dist p q ≠ Real.sqrt n := by
  intro h
  obtain ⟨m, _, hm⟩ := scaledLattice_dist_sq_even hp hq
  have hsq : dist p q ^ 2 = (n : ℝ) := by
    rw [h, Real.sq_sqrt (by positivity)]
  rw [hsq] at hm
  have hz : (n : ℤ) = 2 * m := by exact_mod_cast hm
  obtain ⟨j, hj⟩ := hodd
  subst hj
  omega

/-- **Concrete instance:** no two points of `√2·ℤ²` are at distance `√3`
(`n = 3`, odd). -/
theorem scaledLattice_dist_ne_sqrt_three {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice) :
    dist p q ≠ Real.sqrt 3 :=
  scaledLattice_dist_ne_sqrt_odd hp hq (n := 3) (by decide)

/-- `scaledLattice_unitDistanceFree` is the `n = 1` case of
`scaledLattice_dist_ne_sqrt_odd` (`√1 = 1`), confirming the generalization
subsumes the original non-vacuity witness. -/
theorem scaledLattice_unitDistanceFree_of_odd : IsUnitDistanceFree ScaledLattice := by
  intro p q hp hq _
  have h := scaledLattice_dist_ne_sqrt_odd hp hq (n := 1) (by decide)
  simpa [Real.sqrt_one] using h

/-!
## Further strengthening: an infinite family of *even* avoided distances

The odd result above is not the whole story: the squared distance is not merely
even, it is `2·(u² + v²)` — twice a **sum of two integer squares**.  Since a sum
of two squares is never `≡ 3 (mod 4)`, the squared distance is never `≡ 6 (mod 8)`.
Hence `√2·ℤ²` also avoids every distance `√n` with `n ≡ 6 (mod 8)` — the infinite
family `√6, √14, √22, …` of *even* distances, none of which is caught by the
odd-`n` result.
-/

/-- **A sum of two integer squares is never `≡ 3 (mod 4)`.**  Each square is
`0` or `1 (mod 4)` (even/odd split), so the sum lies in `{0, 1, 2} (mod 4)`. -/
theorem sq_add_sq_mod_four_ne_three (u v : ℤ) : (u ^ 2 + v ^ 2) % 4 ≠ 3 := by
  have key : ∀ w : ℤ, w ^ 2 % 4 = 0 ∨ w ^ 2 % 4 = 1 := by
    intro w
    rcases Int.even_or_odd w with ⟨k, hk⟩ | ⟨k, hk⟩
    · left; subst hk
      have : (k + k) ^ 2 = 4 * k ^ 2 := by ring
      rw [this]; omega
    · right; subst hk
      have : (2 * k + 1) ^ 2 = 4 * (k ^ 2 + k) + 1 := by ring
      rw [this]; omega
  rcases key u with hu | hu <;> rcases key v with hv | hv <;> omega

/-- **Squared lattice distances are twice a sum of two squares.**  Sharpens
`scaledLattice_dist_sq_even` by exposing the two-square structure of the even
factor: `dist p q ^ 2 = 2·(u² + v²)` with `u = a − a'`, `v = b − b'`. -/
theorem scaledLattice_dist_sq_two_mul_sq_add_sq {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice) :
    ∃ u v : ℤ, dist p q ^ 2 = 2 * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2) := by
  obtain ⟨a, b, hpa, hpb⟩ := hp
  obtain ⟨a', b', hqa, hqb⟩ := hq
  refine ⟨a - a', b - b', ?_⟩
  rw [dist_eq_coords]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hx : (p 0 - q 0) ^ 2 = 2 * ((a : ℝ) - a') ^ 2 := by
    rw [hpa, hqa]
    have e : (Real.sqrt 2 * (a : ℝ) - Real.sqrt 2 * a') ^ 2
        = Real.sqrt 2 ^ 2 * ((a : ℝ) - a') ^ 2 := by ring
    rw [e, hs]
  have hy : (p 1 - q 1) ^ 2 = 2 * ((b : ℝ) - b') ^ 2 := by
    rw [hpb, hqb]
    have e : (Real.sqrt 2 * (b : ℝ) - Real.sqrt 2 * b') ^ 2
        = Real.sqrt 2 ^ 2 * ((b : ℝ) - b') ^ 2 := by ring
    rw [e, hs]
  have hnn : 0 ≤ (p 0 - q 0) ^ 2 + (p 1 - q 1) ^ 2 := by positivity
  rw [Real.sq_sqrt hnn, hx, hy]
  push_cast; ring

/-- **`√2·ℤ²` avoids every distance `√n` with `n ≡ 6 (mod 8)`.**  The squared
distance is `2·(u² + v²)`; if it equalled `n ≡ 6 (mod 8)` then `u² + v² ≡ 3 (mod 4)`,
impossible by `sq_add_sq_mod_four_ne_three`.  This is a genuinely *new* infinite
family of avoided distances — all **even** (`√6, √14, √22, …`), none reachable from
the odd-`n` theorem. -/
theorem scaledLattice_dist_ne_sqrt_six_mod_eight {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice)
    {n : ℕ} (hn : n % 8 = 6) : dist p q ≠ Real.sqrt n := by
  intro h
  obtain ⟨u, v, huv⟩ := scaledLattice_dist_sq_two_mul_sq_add_sq hp hq
  have hsq : dist p q ^ 2 = (n : ℝ) := by rw [h, Real.sq_sqrt (by positivity)]
  rw [hsq] at huv
  have hz : (n : ℤ) = 2 * (u ^ 2 + v ^ 2) := by exact_mod_cast huv
  have h3 := sq_add_sq_mod_four_ne_three u v
  omega

/-- **Concrete instance:** no two points of `√2·ℤ²` are at distance `√6`
(`n = 6 ≡ 6 mod 8`, an *even* distance beyond the reach of the odd-`n` result). -/
theorem scaledLattice_dist_ne_sqrt_six {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice) :
    dist p q ≠ Real.sqrt 6 :=
  scaledLattice_dist_ne_sqrt_six_mod_eight hp hq (n := 6) (by decide)

/-!
## The complete mod-8 dichotomy for achievable distances

The squared distance is `2·(u² + v²)` with `u² + v² ≢ 3 (mod 4)`, so it lies in
`{0, 2, 4} (mod 8)`.  This single arithmetic fact *characterizes* the achievable
integer square-distances of `√2·ℤ²` modulo `8`, and unifies both previous avoidance
families: the odd `n` (residues `1, 3, 5, 7`) and `n ≡ 6 (mod 8)` results are exactly
the residues `{1, 3, 5, 6, 7}` that are **not** in `{0, 2, 4}`.
-/

/-- **Achievable distances lie in `{0, 2, 4} (mod 8)`.**  If two points of
`ScaledLattice` are at distance `√n` (`n : ℕ`), then `n ≡ 0, 2, or 4 (mod 8)`.
Indeed `n = 2·(u² + v²)` and `u² + v² ≢ 3 (mod 4)`, so `2·(u² + v²) ∈ {0,2,4} (mod 8)`.
This is the positive companion to the avoidance theorems: it pins the *only* residues
mod `8` a lattice distance can realize. -/
theorem scaledLattice_achievable_mod_eight {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice)
    {n : ℕ} (h : dist p q = Real.sqrt n) :
    n % 8 = 0 ∨ n % 8 = 2 ∨ n % 8 = 4 := by
  obtain ⟨u, v, huv⟩ := scaledLattice_dist_sq_two_mul_sq_add_sq hp hq
  have hsq : dist p q ^ 2 = (n : ℝ) := by rw [h, Real.sq_sqrt (by positivity)]
  rw [hsq] at huv
  have hz : (n : ℤ) = 2 * (u ^ 2 + v ^ 2) := by exact_mod_cast huv
  have h3 := sq_add_sq_mod_four_ne_three u v
  omega

/-- **Complete mod-8 avoidance.**  `√2·ℤ²` avoids `√n` for *every* `n` with
`n ≡ 1, 3, 5, 6, or 7 (mod 8)` — the exact complement of the achievable residues
`{0, 2, 4}`.  This single statement subsumes both `scaledLattice_dist_ne_sqrt_odd`
(residues `1, 3, 5, 7`) and `scaledLattice_dist_ne_sqrt_six_mod_eight` (residue `6`),
and is the sharp mod-8 boundary of the lattice's distance set. -/
theorem scaledLattice_dist_ne_sqrt_of_mod_eight {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice) {n : ℕ}
    (hn : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 6 ∨ n % 8 = 7) :
    dist p q ≠ Real.sqrt n := by
  intro h
  have hach := scaledLattice_achievable_mod_eight hp hq h
  omega

end Erdos214Incomplete01OQ01
