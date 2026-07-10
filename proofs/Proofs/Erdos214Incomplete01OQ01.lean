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

/-!
## Beyond mod 8: the achievable residues `{0, 2, 4}` are **not** sharp

The mod-8 dichotomy pins the achievable square-distances to residues `{0, 2, 4} (mod 8)`,
but it is *not* a complete characterization: `√12` has `12 ≡ 4 (mod 8)` — an allowed
residue — yet it is still avoided.  Indeed `dist² = 2·(u² + v²) = 12` forces
`u² + v² = 6`, and `6` is **not** a sum of two integer squares.  The clean obstruction is
mod `8`: a sum of two squares is never `≡ 6 (mod 8)` (each square is `0, 1, 4 (mod 8)`, and
no two of those sum to `6`).  This yields a genuinely new infinite avoided family
`n ≡ 12 (mod 16)` — i.e. `√12, √28, √44, …` — lying *outside* the reach of the mod-8
dichotomy, showing the achievable set is strictly finer than any single modular condition.
-/

/-- **A sum of two integer squares is never `≡ 6 (mod 8)`.**  Each square is
`0, 1, or 4 (mod 8)` (from the even/odd split of the base, refined once more), and no two
of `{0, 1, 4}` sum to `6 (mod 8)`.  This is the mod-`8` sharpening of
`sq_add_sq_mod_four_ne_three` needed to rule out `u² + v² = 6`. -/
theorem sq_add_sq_mod_eight_ne_six (u v : ℤ) : (u ^ 2 + v ^ 2) % 8 ≠ 6 := by
  have key : ∀ w : ℤ, w ^ 2 % 8 = 0 ∨ w ^ 2 % 8 = 1 ∨ w ^ 2 % 8 = 4 := by
    intro w
    rcases Int.even_or_odd w with ⟨k, hk⟩ | ⟨k, hk⟩
    · subst hk
      rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · left
        have h : (k + k) ^ 2 = 8 * (2 * j ^ 2) := by subst hj; ring
        rw [h]; omega
      · right; right
        have h : (k + k) ^ 2 = 8 * (2 * j ^ 2 + 2 * j) + 4 := by subst hj; ring
        rw [h]; omega
    · subst hk
      rcases Int.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
      · right; left
        have h : (2 * k + 1) ^ 2 = 8 * (2 * j ^ 2 + j) + 1 := by subst hj; ring
        rw [h]; omega
      · right; left
        have h : (2 * k + 1) ^ 2 = 8 * (2 * j ^ 2 + 3 * j + 1) + 1 := by subst hj; ring
        rw [h]; omega
  rcases key u with hu | hu | hu <;> rcases key v with hv | hv | hv <;> omega

/-- **`√2·ℤ²` avoids every distance `√n` with `n ≡ 12 (mod 16)`.**  Then
`dist² = 2·(u² + v²) = n` forces `u² + v² ≡ 6 (mod 8)`, impossible by
`sq_add_sq_mod_eight_ne_six`.  This is a *new* infinite avoided family `√12, √28, √44, …`
lying **beyond** the mod-8 dichotomy: each such `n` has `n ≡ 4 (mod 8)`, an achievable
residue, so none of these are caught by `scaledLattice_dist_ne_sqrt_of_mod_eight`. -/
theorem scaledLattice_dist_ne_sqrt_twelve_mod_sixteen {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice)
    {n : ℕ} (hn : n % 16 = 12) : dist p q ≠ Real.sqrt n := by
  intro h
  obtain ⟨u, v, huv⟩ := scaledLattice_dist_sq_two_mul_sq_add_sq hp hq
  have hsq : dist p q ^ 2 = (n : ℝ) := by rw [h, Real.sq_sqrt (by positivity)]
  rw [hsq] at huv
  have hz : (n : ℤ) = 2 * (u ^ 2 + v ^ 2) := by exact_mod_cast huv
  have h6 := sq_add_sq_mod_eight_ne_six u v
  omega

/-- **Concrete instance:** no two points of `√2·ℤ²` are at distance `√12`
(`n = 12 ≡ 12 mod 16`).  Although `12 ≡ 4 (mod 8)` is an *achievable* residue, `√12` is
nonetheless avoided — the first witness that the mod-8 dichotomy is not the final word. -/
theorem scaledLattice_dist_ne_sqrt_twelve {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice) :
    dist p q ≠ Real.sqrt 12 :=
  scaledLattice_dist_ne_sqrt_twelve_mod_sixteen hp hq (n := 12) (by decide)

/-!
## Sharpness: the achievable square-distances are *exactly* `2·(u² + v²)`

Every theorem above is one-directional: it lists square-distances the lattice does
*not* realize.  The converse closes the loop.  For any integers `u, v` the concrete
pair `(√2·u, √2·v)` and the origin `0` are both lattice points, and their squared
distance is `(√2·u)² + (√2·v)² = 2·(u² + v²)`.  Hence **every** value `2·(u² + v²)`
genuinely *is* a squared lattice distance.  Combined with
`scaledLattice_dist_sq_two_mul_sq_add_sq` (the forward inclusion), this yields the
**exact** characterization of the achievable distances of `√2·ℤ²`:
`√n` is realized ⟺ `n = 2·(u² + v²)`, i.e. `n/2` is a sum of two integer squares.
All the avoidance families above are then precisely its unrealizable instances.
-/

/-- The concrete lattice point `(√2·u, √2·v) ∈ √2·ℤ²`, built from two integer
coordinates. -/
noncomputable def latticePoint (u v : ℤ) : Plane :=
  !₂[Real.sqrt 2 * u, Real.sqrt 2 * v]

/-- The first coordinate of `latticePoint u v` is `√2·u`. -/
@[simp] theorem latticePoint_zero (u v : ℤ) : latticePoint u v 0 = Real.sqrt 2 * u := by
  simp [latticePoint, PiLp.toLp_apply]

/-- The second coordinate of `latticePoint u v` is `√2·v`. -/
@[simp] theorem latticePoint_one (u v : ℤ) : latticePoint u v 1 = Real.sqrt 2 * v := by
  simp [latticePoint, PiLp.toLp_apply]

/-- `latticePoint u v` really lies in `ScaledLattice` (witnesses `a = u`, `b = v`). -/
theorem latticePoint_mem (u v : ℤ) : latticePoint u v ∈ ScaledLattice :=
  ⟨u, v, latticePoint_zero u v, latticePoint_one u v⟩

/-- **Realizability.**  For any integers `u, v`, the value `2·(u² + v²)` is genuinely a
squared lattice distance: it is achieved by `latticePoint u v` and the origin `0`.  This
is the converse of `scaledLattice_dist_sq_two_mul_sq_add_sq`. -/
theorem scaledLattice_realizes (u v : ℤ) :
    ∃ p q : Plane, p ∈ ScaledLattice ∧ q ∈ ScaledLattice ∧
      dist p q = Real.sqrt (2 * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2)) := by
  refine ⟨latticePoint u v, 0, latticePoint_mem u v, scaledLattice_nonempty, ?_⟩
  rw [dist_eq_coords]
  have hz0 : (0 : Plane) 0 = 0 := by simp
  have hz1 : (0 : Plane) 1 = 0 := by simp
  rw [latticePoint_zero, latticePoint_one, hz0, hz1]
  congr 1
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have e : (Real.sqrt 2 * (u : ℝ) - 0) ^ 2 + (Real.sqrt 2 * (v : ℝ) - 0) ^ 2
      = Real.sqrt 2 ^ 2 * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2) := by ring
  rw [e, hs]

/-- **Exact characterization of the achievable distances of `√2·ℤ²`.**  For a natural
number `n`, some pair of lattice points is at distance `√n` **iff** `n = 2·(u² + v²)` for
integers `u, v` — equivalently, `n` is even and `n/2` is a sum of two squares.  The
forward direction is `scaledLattice_dist_sq_two_mul_sq_add_sq`; the reverse is
`scaledLattice_realizes`.  This is the sharp statement to which every avoidance theorem
above (odd `n`, `n ≡ 6 mod 8`, `n ≡ 12 mod 16`, …) is a special unrealizable case. -/
theorem scaledLattice_achievable_iff (n : ℕ) :
    (∃ p q : Plane, p ∈ ScaledLattice ∧ q ∈ ScaledLattice ∧ dist p q = Real.sqrt n)
      ↔ ∃ u v : ℤ, (n : ℤ) = 2 * (u ^ 2 + v ^ 2) := by
  constructor
  · rintro ⟨p, q, hp, hq, h⟩
    obtain ⟨u, v, huv⟩ := scaledLattice_dist_sq_two_mul_sq_add_sq hp hq
    have hsq : dist p q ^ 2 = (n : ℝ) := by rw [h, Real.sq_sqrt (by positivity)]
    rw [hsq] at huv
    exact ⟨u, v, by exact_mod_cast huv⟩
  · rintro ⟨u, v, huv⟩
    obtain ⟨p, q, hp, hq, h⟩ := scaledLattice_realizes u v
    refine ⟨p, q, hp, hq, ?_⟩
    rw [h]
    congr 1
    have : (n : ℝ) = 2 * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2) := by exact_mod_cast huv
    rw [this]

/-- **Concrete realization:** `√8` *is* a lattice distance (`8 = 2·(2² + 0²)`), witnessing
that residue `0 (mod 8)` is genuinely achieved — the achievable residue set `{0, 2, 4}` is
sharp as a set even though not every `n` in it is realized (cf. `√12`). -/
theorem scaledLattice_realizes_sqrt_eight :
    ∃ p q : Plane, p ∈ ScaledLattice ∧ q ∈ ScaledLattice ∧ dist p q = Real.sqrt 8 := by
  obtain ⟨p, q, hp, hq, h⟩ := scaledLattice_realizes 2 0
  refine ⟨p, q, hp, hq, ?_⟩
  rw [h]; congr 1; norm_num

/-!
## The minimal positive distance of `√2·ℤ²` is exactly `√2`

Every result above describes *which* distances the lattice avoids or realizes,
but none pins down its **smallest positive** distance.  The exact
characterization `dist² = 2·(u² + v²)` supplies it at once: the radicand is either
`0` (coincident points) or `≥ 2` (any nonzero integer combination), so the lattice
has **no** distance in the open interval `(0, √2)`.  This "gap" bound is *sharp* —
`√2` itself is attained (`latticePoint 1 0` and the origin) — so the minimal
positive distance is exactly `√2`, the nearest-neighbour spacing of the lattice.
-/

/-- **Distance gap.**  Any two points of `ScaledLattice` are either *coincident*
(distance `0`) or at least `√2` apart: the squared distance `2·((a-a')² + (b-b')²)`
is either `0` or `≥ 2`, since `(a-a')² + (b-b')²` is a nonnegative integer that,
when nonzero, is `≥ 1`.  Hence the lattice realizes **no** distance in the open
interval `(0, √2)`. -/
theorem scaledLattice_dist_eq_zero_or_ge_sqrt_two {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice) :
    dist p q = 0 ∨ Real.sqrt 2 ≤ dist p q := by
  obtain ⟨a, b, hpa, hpb⟩ := hp
  obtain ⟨a', b', hqa, hqb⟩ := hq
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
  rw [dist_eq_coords, hx, hy]
  rcases eq_or_ne ((a - a') ^ 2 + (b - b') ^ 2) 0 with h0 | h0
  · left
    have hc : ((a : ℝ) - a') ^ 2 + ((b : ℝ) - b') ^ 2 = 0 := by exact_mod_cast h0
    have hz : 2 * ((a : ℝ) - a') ^ 2 + 2 * ((b : ℝ) - b') ^ 2 = 0 := by linarith
    rw [hz, Real.sqrt_zero]
  · right
    have hnn : (0 : ℤ) ≤ (a - a') ^ 2 + (b - b') ^ 2 := by positivity
    have hM : (1 : ℤ) ≤ (a - a') ^ 2 + (b - b') ^ 2 := by omega
    have hM' : (1 : ℝ) ≤ ((a : ℝ) - a') ^ 2 + ((b : ℝ) - b') ^ 2 := by exact_mod_cast hM
    have hR : (2 : ℝ) ≤ 2 * ((a : ℝ) - a') ^ 2 + 2 * ((b : ℝ) - b') ^ 2 := by linarith
    exact Real.sqrt_le_sqrt hR

/-- **Minimal positive distance.**  Any two *distinct* points of `ScaledLattice`
are at distance at least `√2`.  Immediate from the distance-gap dichotomy: the
`distance 0` branch forces `p = q` (via `‖p - q‖ = 0`), contradicting `p ≠ q`. -/
theorem scaledLattice_dist_ge_sqrt_two {p q : Plane}
    (hp : p ∈ ScaledLattice) (hq : q ∈ ScaledLattice) (hpq : p ≠ q) :
    Real.sqrt 2 ≤ dist p q := by
  rcases scaledLattice_dist_eq_zero_or_ge_sqrt_two hp hq with h0 | h
  · exfalso
    apply hpq
    have hsub : p - q = 0 := by
      unfold dist at h0
      exact norm_eq_zero.mp h0
    exact sub_eq_zero.mp hsub
  · exact h

/-- **Sharpness of the gap.**  The bound `√2` is attained: `latticePoint 1 0` and the
origin `0` are distinct lattice points exactly `√2` apart (`n = 2 = 2·(1² + 0²)`).
Together with `scaledLattice_dist_ge_sqrt_two` this shows the minimal positive
distance of `√2·ℤ²` is **exactly** `√2` — its nearest-neighbour spacing. -/
theorem scaledLattice_realizes_sqrt_two :
    ∃ p q : Plane, p ∈ ScaledLattice ∧ q ∈ ScaledLattice ∧ dist p q = Real.sqrt 2 := by
  obtain ⟨p, q, hp, hq, h⟩ := scaledLattice_realizes 1 0
  refine ⟨p, q, hp, hq, ?_⟩
  rw [h]; congr 1; norm_num

end Erdos214Incomplete01OQ01
