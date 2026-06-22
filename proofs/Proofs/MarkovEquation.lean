/-
# The Markov Equation x² + y² + z² = 3xyz — Complete Classification of Solutions

The Markov equation is the Diophantine equation

  x² + y² + z² = 3·x·y·z

over the positive integers. Its positive solutions (Markov triples) form the
famous *Markov tree*, rooted at the singular solution (1,1,1), with every other
solution obtained by repeatedly applying *Vieta jumping* moves (and permuting
coordinates).

This file gives a fully elementary, axiom-free proof of the structural theorem:

  **Every positive Markov triple can be reduced to (1,1,1) by a finite sequence
  of Vieta-jumping moves and coordinate transpositions.**

The proof is by descent on the coordinate sum x + y + z, exactly mirroring the
descent used for the negative Pell equation. The arithmetic heart is the
inequality `g(y) ≤ 0` for the quadratic `g(t) = t² − 3xy·t + (x²+y²)` whose roots
are `z` and its Vieta partner `z' = 3xy − z`; this forces `z' ≤ y`, so replacing
the maximal coordinate strictly decreases the sum.

This is not in Mathlib (Mathlib's `Pell.Solution₁` handles only norm-+1 binary
Pell equations); the Markov equation requires its own ternary descent.
-/
import Mathlib

namespace MarkovEquation

/-- A **Markov triple**: positive integers with `x² + y² + z² = 3xyz`. -/
def IsMarkov (x y z : ℤ) : Prop :=
  0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 2 + y ^ 2 + z ^ 2 = 3 * x * y * z

/-- The singular solution `(1,1,1)` is a Markov triple. -/
theorem markov_one : IsMarkov 1 1 1 := by
  refine ⟨one_pos, one_pos, one_pos, by ring⟩

/-! ## Symmetry of the equation -/

/-- Swapping the first two coordinates preserves Markov triples. -/
theorem markov_swap12 {x y z : ℤ} (h : IsMarkov x y z) : IsMarkov y x z := by
  obtain ⟨hx, hy, hz, he⟩ := h
  exact ⟨hy, hx, hz, by linear_combination he⟩

/-- Swapping the last two coordinates preserves Markov triples. -/
theorem markov_swap23 {x y z : ℤ} (h : IsMarkov x y z) : IsMarkov x z y := by
  obtain ⟨hx, hy, hz, he⟩ := h
  exact ⟨hx, hz, hy, by linear_combination he⟩

/-! ## Vieta jumping

Fixing `x` and `y`, the equation is a quadratic in `z`; its two roots multiply to
`x² + y²`. The map `z ↦ 3xy − z` swaps the two roots, hence sends a Markov triple
to a Markov triple. -/

/-- The product of the two `z`-roots equals `x² + y²`. -/
theorem markov_root_prod {x y z : ℤ} (h : IsMarkov x y z) :
    z * (3 * x * y - z) = x ^ 2 + y ^ 2 := by
  obtain ⟨_, _, _, he⟩ := h
  linear_combination -he

/-- **Vieta jump.** Replacing `z` by its conjugate root `3xy − z` yields another
Markov triple. -/
theorem markov_vieta {x y z : ℤ} (h : IsMarkov x y z) : IsMarkov x y (3 * x * y - z) := by
  obtain ⟨hx, hy, hz, he⟩ := h
  have hzz : z * (3 * x * y - z) = x ^ 2 + y ^ 2 := by linear_combination -he
  have hpos : 0 < x ^ 2 + y ^ 2 := by positivity
  refine ⟨hx, hy, ?_, by linear_combination he⟩
  -- positivity of the new coordinate: z·z' = x²+y² > 0 with z > 0 forces z' > 0
  nlinarith [hzz, hpos, hz]

/-- The Vieta jump is an involution in the third coordinate. -/
theorem markov_vieta_involutive (x y z : ℤ) : 3 * x * y - (3 * x * y - z) = z := by ring

/-! ## The descent inequality

For a *sorted* Markov triple `x ≤ y ≤ z` with `z ≥ 2`, the largest coordinate is
the strict maximum (`y < z`), and the Vieta jump on it strictly decreases it:
`3xy − z < z`. This is the engine of the descent. -/

/-- In a sorted Markov triple with `z ≥ 2`, the top coordinate is a strict maximum. -/
theorem markov_top_strict {x y z : ℤ} (h : IsMarkov x y z)
    (hxy : x ≤ y) (hyz : y ≤ z) (hz2 : 2 ≤ z) : y < z := by
  obtain ⟨hx, hy, hz, he⟩ := h
  rcases lt_or_eq_of_le hyz with hlt | heq
  · exact hlt
  · exfalso
    -- y = z forces x² = z²(3x − 2), impossible for 1 ≤ x ≤ z, z ≥ 2
    subst heq
    nlinarith [he, hx, hxy, hz2, mul_nonneg (sub_nonneg.2 hxy) (sub_nonneg.2 hxy),
      mul_nonneg (sub_nonneg.2 hx) (sq_nonneg y)]

/-- **Descent.** The Vieta jump on the maximal coordinate strictly decreases it. -/
theorem markov_vieta_lt {x y z : ℤ} (h : IsMarkov x y z)
    (hxy : x ≤ y) (hyz : y ≤ z) (hz2 : 2 ≤ z) : 3 * x * y - z < z := by
  have hyz' : y < z := markov_top_strict h hxy hyz hz2
  obtain ⟨hx, hy, hz, he⟩ := h
  have hx1 : (1 : ℤ) ≤ x := hx
  -- (y − z)(y − z') = x² + 2y² − 3xy², which is ≤ 0
  have hgy : (y - z) * (y - (3 * x * y - z)) = x ^ 2 + 2 * y ^ 2 - 3 * x * y ^ 2 := by
    linear_combination -he
  have hle : x ^ 2 + 2 * y ^ 2 - 3 * x * y ^ 2 ≤ 0 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hx1) (sq_nonneg y), sq_nonneg (y - x), hx1, hxy]
  have hprod : (y - z) * (y - (3 * x * y - z)) ≤ 0 := by rw [hgy]; exact hle
  -- y − z < 0 and the product ≤ 0 give z' ≤ y
  have hz'y : 3 * x * y - z ≤ y := by nlinarith [hprod, hyz']
  -- root product: z·z' = x² + y², so x² + y² = z·z' ≤ z·y < z²
  have hp : z * (3 * x * y - z) = x ^ 2 + y ^ 2 := by linear_combination -he
  have hsq : x ^ 2 + y ^ 2 < z ^ 2 := by nlinarith [hp, hz'y, hyz', hz]
  -- finally 3xyz = x²+y²+z² < 2z², and z > 0, give 3xy < 2z
  nlinarith [hsq, he, hz]

/-! ## Reachability in the Markov tree

A *move* is either a coordinate transposition or a Vieta jump. Two triples are
reachable from one another if connected by a finite sequence of moves. -/

/-- One move in the Markov tree. -/
inductive Step : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ → Prop
  | swap12 (x y z : ℤ) : Step (x, y, z) (y, x, z)
  | swap23 (x y z : ℤ) : Step (x, y, z) (x, z, y)
  | vieta (x y z : ℤ) : Step (x, y, z) (x, y, 3 * x * y - z)

/-- Reachability: the reflexive–transitive closure of `Step`. -/
def Reachable : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ → Prop :=
  Relation.ReflTransGen Step

/-- Markov triples are closed under any single move: the three permutation /
Vieta moves all preserve `IsMarkov`. -/
theorem isMarkov_of_step {p q : ℤ × ℤ × ℤ} (hp : IsMarkov p.1 p.2.1 p.2.2)
    (hs : Step p q) : IsMarkov q.1 q.2.1 q.2.2 := by
  cases hs with
  | swap12 x y z => exact markov_swap12 hp
  | swap23 x y z => exact markov_swap23 hp
  | vieta x y z => exact markov_vieta hp

/-- Any Markov triple can be moved (via ≤ 3 transpositions) to a *sorted*
representative `a ≤ b ≤ c` with the same coordinate sum. -/
theorem sort_reachable {x y z : ℤ} (h : IsMarkov x y z) :
    ∃ a b c, IsMarkov a b c ∧ a ≤ b ∧ b ≤ c ∧ a + b + c = x + y + z ∧
      Reachable (x, y, z) (a, b, c) := by
  rcases le_total x y with hxy | hxy <;> rcases le_total y z with hyz | hyz <;>
    rcases le_total x z with hxz | hxz
  -- x ≤ y, y ≤ z  ⇒ (x,y,z)
  · exact ⟨x, y, z, h, hxy, hyz, by ring, Relation.ReflTransGen.refl⟩
  · exact ⟨x, y, z, h, hxy, hyz, by ring, Relation.ReflTransGen.refl⟩
  -- x ≤ y, z ≤ y, x ≤ z ⇒ (x,z,y)
  · exact ⟨x, z, y, markov_swap23 h, hxz, hyz, by ring,
      Relation.ReflTransGen.single (Step.swap23 x y z)⟩
  -- x ≤ y, z ≤ y, z ≤ x ⇒ (z,x,y)
  · exact ⟨z, x, y, markov_swap12 (markov_swap23 h), hxz, hxy, by ring,
      (Relation.ReflTransGen.single (Step.swap23 x y z)).tail (Step.swap12 x z y)⟩
  -- y ≤ x, y ≤ z, x ≤ z ⇒ (y,x,z)
  · exact ⟨y, x, z, markov_swap12 h, hxy, hxz, by ring,
      Relation.ReflTransGen.single (Step.swap12 x y z)⟩
  -- y ≤ x, y ≤ z, z ≤ x ⇒ (y,z,x)
  · exact ⟨y, z, x, markov_swap23 (markov_swap12 h), hyz, hxz, by ring,
      (Relation.ReflTransGen.single (Step.swap12 x y z)).tail (Step.swap23 y x z)⟩
  -- y ≤ x, z ≤ y, x ≤ z : forces x = y = z region; sorted (z,y,x)
  · exact ⟨z, y, x, markov_swap23 (markov_swap12 (markov_swap23 h)), hyz, hxy, by ring,
      ((Relation.ReflTransGen.single (Step.swap23 x y z)).tail
        (Step.swap12 x z y)).tail (Step.swap23 z x y)⟩
  -- y ≤ x, z ≤ y, z ≤ x ⇒ (z,y,x)
  · exact ⟨z, y, x, markov_swap23 (markov_swap12 (markov_swap23 h)), hyz, hxy, by ring,
      ((Relation.ReflTransGen.single (Step.swap23 x y z)).tail
        (Step.swap12 x z y)).tail (Step.swap23 z x y)⟩

/-- **Main theorem (descent form).** Every positive Markov triple is reachable
from the root `(1,1,1)` by a finite sequence of moves. The proof is by strong
induction on the coordinate sum: sort the triple, and if it is not `(1,1,1)`,
Vieta-jump the maximal coordinate to strictly reduce the sum. -/
theorem markov_reachable_one : ∀ (n : ℕ) (x y z : ℤ), IsMarkov x y z →
    (x + y + z).toNat = n → Reachable (x, y, z) (1, 1, 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro x y z h hn
    obtain ⟨a, b, c, hM, hab, hbc, hsum, hreach⟩ := sort_reachable h
    refine hreach.trans ?_
    have ha1 : (1 : ℤ) ≤ a := hM.1
    have hc0 : (0 : ℤ) < c := hM.2.2.1
    by_cases hc1 : c = 1
    · -- c = 1 with 1 ≤ a ≤ b ≤ c = 1 forces a = b = c = 1
      obtain rfl : a = 1 := by omega
      obtain rfl : b = 1 := by omega
      obtain rfl : c = 1 := hc1
      exact Relation.ReflTransGen.refl
    · -- c ≥ 2: descend
      have hc2 : 2 ≤ c := by omega
      have hM' : IsMarkov a b (3 * a * b - c) := markov_vieta hM
      have hlt : 3 * a * b - c < c := markov_vieta_lt hM hab hbc hc2
      have hd0 : 0 < 3 * a * b - c := hM'.2.2.1
      refine Relation.ReflTransGen.head (Step.vieta a b c) ?_
      refine IH ((a + b + (3 * a * b - c)).toNat) ?_ a b (3 * a * b - c) hM' rfl
      -- the new coordinate sum is strictly smaller
      have hbpos : 0 < a + b + c := by linarith
      have hkey : a + b + (3 * a * b - c) < a + b + c := by linarith
      have h2 : (a + b + (3 * a * b - c)).toNat < (a + b + c).toNat :=
        (Int.toNat_lt_toNat hbpos).2 hkey
      rwa [show (a + b + c).toNat = n from by rw [hsum]; exact hn] at h2

/-- **Classification.** Every positive Markov triple lies in the Markov tree
rooted at `(1,1,1)`. -/
theorem markov_classification {x y z : ℤ} (h : IsMarkov x y z) :
    Reachable (x, y, z) (1, 1, 1) :=
  markov_reachable_one _ x y z h rfl

/-! ## Consequences and small triples -/

/-- The **singular solution** is the unique Markov triple with all coordinates
equal: `(t,t,t)` is Markov iff `t = 1`. -/
theorem markov_all_eq {t : ℤ} (h : IsMarkov t t t) : t = 1 := by
  obtain ⟨ht, _, _, he⟩ := h
  -- 3t² = 3t³ ⇒ t²(t−1) = 0 ⇒ t = 1 for t > 0
  have h3 : (3 : ℤ) * (t ^ 2 * (t - 1)) = 0 := by linear_combination -he
  have h0 : t ^ 2 * (t - 1) = 0 := by linarith
  rcases mul_eq_zero.1 h0 with h1 | h1
  · exfalso; nlinarith [mul_pos ht ht, h1]
  · linarith

/-- `(1,1,2)` is a Markov triple — the first Vieta child of the root. -/
theorem markov_one_one_two : IsMarkov 1 1 2 := ⟨one_pos, one_pos, by norm_num, by ring⟩

/-- `(1,2,5)` is a Markov triple. -/
theorem markov_one_two_five : IsMarkov 1 2 5 := ⟨one_pos, by norm_num, by norm_num, by ring⟩

/-- `(2,5,29)` is a Markov triple. -/
theorem markov_two_five_twentynine : IsMarkov 2 5 29 :=
  ⟨by norm_num, by norm_num, by norm_num, by ring⟩

/-- The first Vieta jump: `(1,1,2)` is obtained from the root by a single move. -/
theorem markov_step_root_to_112 : Step (1, 1, 1) (1, 1, 2) := by
  have h : (2 : ℤ) = 3 * 1 * 1 - 1 := by norm_num
  rw [h]; exact Step.vieta 1 1 1

end MarkovEquation
