/-
  Erdős Problem #634 — Why the area-only dissection predicate is vacuous

  Source: https://erdosproblems.com/634

  The base formalization (`Erdos634Problem.lean`) models a dissection of a
  triangle `T` into `n` pieces by the single condition

      area_partition : (∑ i, (pieces i).area) = T.area

  i.e. the piece areas *add up* to the area of `T`. This is explicitly flagged
  there as "necessary but not sufficient": it says nothing about the pieces
  actually covering `T` or being interior-disjoint.

  This file makes the inadequacy precise. We prove that the area-only predicate
  `IsDissectable` is satisfied by **every** `n ≥ 1`:

      dissectable_of_pos : ∀ n, 1 ≤ n → IsDissectable n

  The witness is trivial: take `T` to be a unit equilateral triangle and take
  the `n` pieces to be `n` congruent equilateral triangles each of side
  `1/√n`, hence each of area `(1/n)·√3/4`; their areas sum to `√3/4 = area(T)`.

  Consequences:
  * The positive results of the problem (`k²`, `2k²`, `3k²`, `6k²`, `k²+m²`,
    `27`, …) all become one-line corollaries — but *vacuously*, carrying no
    geometric content.
  * More importantly, `IsDissectable 7` and `IsDissectable 11` are **provable**
    here. Since Beeson's theorem asserts `¬IsDissectable 7` and
    `¬IsDissectable 11` (postulated as axioms in the base file), the area-only
    predicate is logically *incompatible* with Beeson's negative results: it
    cannot express them without inconsistency.

  Moral: a faithful formalization must require genuine covering and
  interior-disjointness of the pieces — exactly the strengthening carried out
  in the `-oq-02` covering line of work (`Erdos634MedialCoveringOQ02.lean`).
  This file is a self-contained, axiom-free critique of the naive definition;
  it deliberately does **not** import the false Beeson axioms, so it is itself
  consistent.

  Tags: geometry, dissection, formalization-critique, erdos, open-problem
-/

import Mathlib

namespace Erdos634AreaCollapse

open Finset

/-- A triangle represented by its three side lengths, with positivity and the
    three triangle inequalities. (Mirrors `Erdos634.Triangle`.) -/
structure Triangle where
  a : ℝ
  b : ℝ
  c : ℝ
  ha : a > 0
  hb : b > 0
  hc : c > 0
  tab : a + b > c
  tbc : b + c > a
  tca : c + a > b

/-- Congruence: equality of the (unordered) multiset of side lengths. -/
def Congruent (T₁ T₂ : Triangle) : Prop :=
  Multiset.ofList [T₁.a, T₁.b, T₁.c] = Multiset.ofList [T₂.a, T₂.b, T₂.c]

/-- Semiperimeter. -/
noncomputable def Triangle.s (T : Triangle) : ℝ := (T.a + T.b + T.c) / 2

/-- Area via Heron's formula. -/
noncomputable def Triangle.area (T : Triangle) : ℝ :=
  Real.sqrt (T.s * (T.s - T.a) * (T.s - T.b) * (T.s - T.c))

/-- Area-only dissection: the piece areas sum to the area of `T`.
    This is the exact predicate used in the base formalization. -/
structure Dissection (T : Triangle) (n : ℕ) where
  pieces : Fin n → Triangle
  area_partition : (∑ i, (pieces i).area) = T.area

/-- All pieces are congruent to each other. -/
def IsCongruentDissection (T : Triangle) (n : ℕ) (D : Dissection T n) : Prop :=
  ∀ i j : Fin n, Congruent (D.pieces i) (D.pieces j)

/-- `n` is (area-only) dissectable: some triangle has an area-only dissection
    into `n` mutually congruent triangles. -/
def IsDissectable (n : ℕ) : Prop :=
  ∃ T : Triangle, ∃ D : Dissection T n, IsCongruentDissection T n D

/-- The equilateral triangle with side length `s > 0`. -/
noncomputable def equil (s : ℝ) (hs : 0 < s) : Triangle where
  a := s
  b := s
  c := s
  ha := hs
  hb := hs
  hc := hs
  tab := by linarith
  tbc := by linarith
  tca := by linarith

/-- The area of an equilateral triangle of side `s > 0` is `s²·√3/4`. -/
theorem equil_area (s : ℝ) (hs : 0 < s) :
    (equil s hs).area = s ^ 2 * Real.sqrt 3 / 4 := by
  unfold Triangle.area
  have hs2 : (equil s hs).s = 3 * s / 2 := by
    unfold Triangle.s equil; ring
  rw [hs2]
  show Real.sqrt (3 * s / 2 * (3 * s / 2 - s) * (3 * s / 2 - s) * (3 * s / 2 - s))
      = s ^ 2 * Real.sqrt 3 / 4
  rw [show 3 * s / 2 * (3 * s / 2 - s) * (3 * s / 2 - s) * (3 * s / 2 - s)
        = (s ^ 2 * Real.sqrt 3 / 4) ^ 2 from ?_]
  · exact Real.sqrt_sq (by positivity)
  · rw [div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
    ring

/-- **Collapse of the area-only predicate.** Every `n ≥ 1` is area-dissectable:
    cut a unit equilateral triangle into `n` congruent equilateral pieces of
    side `1/√n`. The construction ignores geometry entirely — it only balances
    areas — which is exactly the defect being exposed. -/
theorem dissectable_of_pos (n : ℕ) (hn : 1 ≤ n) : IsDissectable n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hnR' : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hpos : 0 < Real.sqrt (1 / n) := Real.sqrt_pos.mpr (by positivity)
  refine ⟨equil 1 one_pos, ⟨fun _ => equil (Real.sqrt (1 / n)) hpos, ?_⟩, ?_⟩
  · -- area balance
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [equil_area, equil_area, Real.sq_sqrt (by positivity), nsmul_eq_mul]
    field_simp
  · -- all pieces are the same triangle, hence congruent
    intro i j; rfl

/-- Positive-result corollaries — all *vacuous* under the area-only predicate. -/
theorem squares_dissectable (k : ℕ) (hk : 1 ≤ k) : IsDissectable (k ^ 2) :=
  dissectable_of_pos _ (Nat.one_le_pow 2 k (by omega))

theorem two_squares_dissectable (n : ℕ) (hn : 1 ≤ n) : IsDissectable (2 * n ^ 2) :=
  dissectable_of_pos _ (by have := Nat.one_le_pow 2 n (by omega); omega)

theorem three_squares_dissectable (n : ℕ) (hn : 1 ≤ n) : IsDissectable (3 * n ^ 2) :=
  dissectable_of_pos _ (by have := Nat.one_le_pow 2 n (by omega); omega)

theorem six_squares_dissectable (n : ℕ) (hn : 1 ≤ n) : IsDissectable (6 * n ^ 2) :=
  dissectable_of_pos _ (by have := Nat.one_le_pow 2 n (by omega); omega)

theorem sum_squares_dissectable (n m : ℕ) (hn : 1 ≤ n) (_hm : 1 ≤ m) :
    IsDissectable (n ^ 2 + m ^ 2) :=
  dissectable_of_pos _ (by have := Nat.one_le_pow 2 n (by omega); omega)

theorem twenty_seven_dissectable : IsDissectable 27 :=
  dissectable_of_pos 27 (by norm_num)

/-- **The punchline.** `7` is area-dissectable — even though Beeson proved it is
    *not* dissectable as a genuine geometric tiling. Hence the area-only
    predicate provably contradicts Beeson's theorem. -/
theorem area_dissectable_seven : IsDissectable 7 :=
  dissectable_of_pos 7 (by norm_num)

/-- Likewise `11`. -/
theorem area_dissectable_eleven : IsDissectable 11 :=
  dissectable_of_pos 11 (by norm_num)

/-- Stated as an incompatibility: **no** predicate that both (i) is implied by
    the area-only dissection data and (ii) forbids `7` can be consistent.
    Concretely, adjoining Beeson's `¬IsDissectable 7` to this file yields `False`. -/
theorem beeson_axiom_inconsistent_with_area_predicate
    (beeson : ¬ IsDissectable 7) : False :=
  beeson area_dissectable_seven

#check @dissectable_of_pos
#check @area_dissectable_seven

end Erdos634AreaCollapse
