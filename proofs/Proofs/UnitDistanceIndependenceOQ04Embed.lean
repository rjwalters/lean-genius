/-
# The Moser spindle is realised in ℝ², completing χ_f(ℝ²) ≥ 3.5

Open question `unit-distance-independence-oq-04` (Frankl–Wilson 1981):
the fractional chromatic number of the unit-distance graph on the plane
satisfies **χ_f(ℝ²) ≥ 3.5**.

`UnitDistanceIndependenceOQ04.lean` built the axiom-free engine

    χ_f(G) ≥ |V(G)| / α(G)                                         (★)

for finite graphs, an abstract `moserSpindle : SimpleGraph (Fin 7)` with
independence number `2` (hence `χ_f(moserSpindle) ≥ 7/2`), and the coordinate-
free transport theorem `fractionalChromaticNumber_ge_of_iso_moserSpindle`,
which pushes the `3.5` bound along **any** graph isomorphism
`moserSpindle ≃g H`.  The one missing ingredient it recorded was the explicit
planar embedding: a concrete `S ⊆ ℝ²` whose unit-distance graph is isomorphic to
the abstract spindle.

This file supplies exactly that, reusing the fully-verified planar Moser spindle
already constructed in `UnitDistanceIndependenceOQ01.lean` (the `χ(ℝ²) ≥ 4`
proof).  That file fixed 7 points `pt 0 … pt 6 ∈ ℝ²` and proved the **eleven**
spindle edges are unit distances.  To pin down the *graph* (not just its edges)
we must also verify the **ten** non-edges are **not** unit distances; this is the
new geometric content here.  Every squared distance lies in `ℚ(√33)`: the eleven
edges equal `1` exactly (the `√33 = √3·√11` cross term cancels), while each of
the ten non-edges equals `3`, `1/3`, or `(k ± √33)/6` with `k ∈ {7,9}`, all
distinguishable from `1` using only `√33 > 0` and `(√33)² = 33`.

With all 21 distances settled, the unit-distance graph `planeSpindle` on the 7
points is proved *equal* to `moserSpindle`, giving the isomorphism and hence

    (7 : ℝ)/2 ≤ χ_f(planeSpindle),      i.e.   χ_f ≥ 3.5

for a genuine finite unit-distance subgraph of the plane — the Frankl–Wilson
certificate, fully realised in ℝ².

## Status

0 sorries, 0 axioms (only `propext / Classical.choice / Quot.sound`).  No
`native_decide`.
-/
import Mathlib
import Proofs.UnitDistanceIndependence
import Proofs.UnitDistanceIndependenceOQ01
import Proofs.UnitDistanceIndependenceOQ04

open Finset
open UnitDistanceIndependenceOQ01
open UnitDistanceIndependence.FractionalChromatic

namespace UnitDistanceIndependence.OQ04Embed

noncomputable section

/-! ## Arithmetic of the surd `√3 · √11 = √33` -/

/-- `√3 · √11 > 0`. -/
theorem cross_pos : 0 < s3 * s11 :=
  mul_pos (Real.sqrt_pos.mpr (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))

/-- `(√3 · √11)² = 33`. -/
theorem cross_sq : (s3 * s11) ^ 2 = 33 := by
  rw [mul_pow, show s3 ^ 2 = 3 from Real.sq_sqrt (by norm_num),
      show s11 ^ 2 = 11 from Real.sq_sqrt (by norm_num)]
  norm_num

/-- From a squared-distance value `≠ 1`, conclude the distance is `≠ 1`. -/
theorem dist_ne_one_of_sq (x₁ y₁ x₂ y₂ v : ℝ)
    (hv : (x₁ - x₂) ^ 2 + (y₁ - y₂) ^ 2 = v) (hv1 : v ≠ 1) :
    dist (mk x₁ y₁) (mk x₂ y₂) ≠ 1 := by
  intro hd
  apply hv1
  rw [← hv, ← dist_mk_sq, hd]
  norm_num

/-! ## The ten non-edges are not unit distances

We use the point labels of `UnitDistanceIndependenceOQ01.pt`:
`0 = (0,0)`, `1 = (1,0)`, `2 = (½, √3/2)`, `3 = (3/2, √3/2)`, and `4,5,6` are the
`θ`-rotations (`cos θ = 5/6`, `sin θ = √11/6`) of `1,2,3`. -/

theorem n03 : dist (pt 0) (pt 3) ≠ 1 := by
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  show dist (mk 0 0) (mk (3 / 2) (s3 / 2)) ≠ 1
  refine dist_ne_one_of_sq _ _ _ _ 3 ?_ ?_
  · linear_combination (1 / 4 : ℝ) * hs3
  · norm_num

theorem n06 : dist (pt 0) (pt 6) ≠ 1 := by
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs11 : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  show dist (mk 0 0) (rot (mk (3 / 2) (s3 / 2))) ≠ 1
  rw [rot_mk]
  refine dist_ne_one_of_sq _ _ _ _ 3 ?_ ?_
  · linear_combination ((s3 ^ 2 + 9) / 144) * hs11 + (1 / 4 : ℝ) * hs3
  · norm_num

theorem n14 : dist (pt 1) (pt 4) ≠ 1 := by
  have hs11 : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  show dist (mk 1 0) (rot (mk 1 0)) ≠ 1
  rw [rot_mk]
  refine dist_ne_one_of_sq _ _ _ _ (1 / 3) ?_ ?_
  · linear_combination (1 / 36 : ℝ) * hs11
  · norm_num

theorem n15 : dist (pt 1) (pt 5) ≠ 1 := by
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs11 : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  show dist (mk 1 0) (rot (mk (1 / 2) (s3 / 2))) ≠ 1
  rw [rot_mk]
  refine dist_ne_one_of_sq _ _ _ _ ((7 + s3 * s11) / 6) ?_ ?_
  · linear_combination ((s3 ^ 2 + 1) / 144) * hs11 + (1 / 4 : ℝ) * hs3
  · intro h; nlinarith [cross_pos]

theorem n16 : dist (pt 1) (pt 6) ≠ 1 := by
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs11 : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  show dist (mk 1 0) (rot (mk (3 / 2) (s3 / 2))) ≠ 1
  rw [rot_mk]
  refine dist_ne_one_of_sq _ _ _ _ ((9 + s3 * s11) / 6) ?_ ?_
  · linear_combination ((s3 ^ 2 + 9) / 144) * hs11 + (1 / 4 : ℝ) * hs3
  · intro h; nlinarith [cross_pos]

theorem n24 : dist (pt 2) (pt 4) ≠ 1 := by
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs11 : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  show dist (mk (1 / 2) (s3 / 2)) (rot (mk 1 0)) ≠ 1
  rw [rot_mk]
  refine dist_ne_one_of_sq _ _ _ _ ((7 - s3 * s11) / 6) ?_ ?_
  · linear_combination (1 / 4 : ℝ) * hs3 + (1 / 36 : ℝ) * hs11
  · intro h
    have ht : s3 * s11 = 1 := by linarith
    have hc := cross_sq
    rw [ht] at hc; norm_num at hc

theorem n25 : dist (pt 2) (pt 5) ≠ 1 := by
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs11 : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  show dist (mk (1 / 2) (s3 / 2)) (rot (mk (1 / 2) (s3 / 2))) ≠ 1
  rw [rot_mk]
  refine dist_ne_one_of_sq _ _ _ _ (1 / 3) ?_ ?_
  · linear_combination ((s3 ^ 2 + 1) / 144) * hs11 + (1 / 12 : ℝ) * hs3
  · norm_num

theorem n26 : dist (pt 2) (pt 6) ≠ 1 := by
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs11 : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  show dist (mk (1 / 2) (s3 / 2)) (rot (mk (3 / 2) (s3 / 2))) ≠ 1
  rw [rot_mk]
  refine dist_ne_one_of_sq _ _ _ _ ((9 - s3 * s11) / 6) ?_ ?_
  · linear_combination ((s3 ^ 2 + 9) / 144) * hs11 + (1 / 12 : ℝ) * hs3
  · intro h
    have ht : s3 * s11 = 3 := by linarith
    have hc := cross_sq
    rw [ht] at hc; norm_num at hc

theorem n34 : dist (pt 3) (pt 4) ≠ 1 := by
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs11 : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  show dist (mk (3 / 2) (s3 / 2)) (rot (mk 1 0)) ≠ 1
  rw [rot_mk]
  refine dist_ne_one_of_sq _ _ _ _ ((9 - s3 * s11) / 6) ?_ ?_
  · linear_combination (1 / 4 : ℝ) * hs3 + (1 / 36 : ℝ) * hs11
  · intro h
    have ht : s3 * s11 = 3 := by linarith
    have hc := cross_sq
    rw [ht] at hc; norm_num at hc

theorem n35 : dist (pt 3) (pt 5) ≠ 1 := by
  have hs3 : s3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs11 : s11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  show dist (mk (3 / 2) (s3 / 2)) (rot (mk (1 / 2) (s3 / 2))) ≠ 1
  rw [rot_mk]
  refine dist_ne_one_of_sq _ _ _ _ ((9 + s3 * s11) / 6) ?_ ?_
  · linear_combination ((s3 ^ 2 + 1) / 144) * hs11 + (1 / 12 : ℝ) * hs3
  · intro h; nlinarith [cross_pos]

/-! Reversed orientations (via `dist_comm`), needed for the symmetric
`fromRel` comparison below. -/

theorem n30 : dist (pt 3) (pt 0) ≠ 1 := by rw [dist_comm]; exact n03
theorem n60 : dist (pt 6) (pt 0) ≠ 1 := by rw [dist_comm]; exact n06
theorem n41 : dist (pt 4) (pt 1) ≠ 1 := by rw [dist_comm]; exact n14
theorem n51 : dist (pt 5) (pt 1) ≠ 1 := by rw [dist_comm]; exact n15
theorem n61 : dist (pt 6) (pt 1) ≠ 1 := by rw [dist_comm]; exact n16
theorem n42 : dist (pt 4) (pt 2) ≠ 1 := by rw [dist_comm]; exact n24
theorem n52 : dist (pt 5) (pt 2) ≠ 1 := by rw [dist_comm]; exact n25
theorem n62 : dist (pt 6) (pt 2) ≠ 1 := by rw [dist_comm]; exact n26
theorem n43 : dist (pt 4) (pt 3) ≠ 1 := by rw [dist_comm]; exact n34
theorem n53 : dist (pt 5) (pt 3) ≠ 1 := by rw [dist_comm]; exact n35

/-! ## The planar unit-distance graph on the seven spindle points -/

/-- Two spindle points are adjacent when they are at Euclidean distance `1`. -/
def planeRel (i j : Fin 7) : Prop := dist (pt i) (pt j) = 1

/-- The unit-distance graph on the seven Moser-spindle points in ℝ². -/
def planeSpindle : SimpleGraph (Fin 7) := SimpleGraph.fromRel planeRel

noncomputable instance : DecidableRel planeSpindle.Adj := fun _ _ => Classical.dec _

/-- Each of the eleven spindle edges is realised as a unit distance. -/
theorem edge_of_moserRel (i j : Fin 7) (h : moserRel i j) :
    dist (pt i) (pt j) = 1 := by
  simp only [moserRel] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact dist01
  · exact dist02
  · exact dist12
  · exact dist13
  · exact dist23
  · exact dist04
  · exact dist05
  · exact dist45
  · exact dist46
  · exact dist56
  · exact dist36

/-- Each of the ten spindle non-edges fails to be a unit distance. -/
theorem nonedge_dist_ne (i j : Fin 7) (hne : i ≠ j)
    (h1 : ¬ moserRel i j) (h2 : ¬ moserRel j i) : dist (pt i) (pt j) ≠ 1 := by
  fin_cases i <;> fin_cases j <;>
    first
      | exact absurd rfl hne
      | exact absurd (by decide) h1
      | exact absurd (by decide) h2
      | exact n03 | exact n30 | exact n06 | exact n60 | exact n14 | exact n41
      | exact n15 | exact n51 | exact n16 | exact n61 | exact n24 | exact n42
      | exact n25 | exact n52 | exact n26 | exact n62 | exact n34 | exact n43
      | exact n35 | exact n53

/-- **The planar unit-distance graph is (literally) the Moser spindle.** -/
theorem moser_eq_plane : moserSpindle = planeSpindle := by
  ext i j
  simp only [moserSpindle, planeSpindle, SimpleGraph.fromRel_adj]
  refine and_congr_right (fun hne => ?_)
  simp only [planeRel]
  constructor
  · rintro (h | h)
    · exact Or.inl (edge_of_moserRel i j h)
    · exact Or.inr (edge_of_moserRel j i h)
  · rintro (h | h) <;> by_contra hc <;> push_neg at hc
    · exact nonedge_dist_ne i j hne hc.1 hc.2 h
    · exact nonedge_dist_ne j i (Ne.symm hne) hc.2 hc.1 h

/-- The identity graph isomorphism `moserSpindle ≃g planeSpindle`. -/
def isoMP : moserSpindle ≃g planeSpindle where
  toEquiv := Equiv.refl (Fin 7)
  map_rel_iff' := by intro a b; simp only [Equiv.refl_apply]; rw [moser_eq_plane]

/-! ## The Frankl–Wilson bound, realised in ℝ² -/

/-- **χ_f ≥ 7/2 for a genuine planar unit-distance graph.**

The unit-distance graph on the seven Moser-spindle points in ℝ² has fractional
chromatic number at least `7/2 = 3.5`.  Since `χ_f(ℝ²)` is the supremum of
`χ_f` over finite unit-distance subgraphs, this is the Frankl–Wilson lower bound
`χ_f(ℝ²) ≥ 3.5`, now witnessed by an explicit ℝ² construction. -/
theorem planeSpindle_fractionalChromaticNumber_ge :
    (7 : ℝ) / 2 ≤ fractionalChromaticNumber planeSpindle :=
  fractionalChromaticNumber_ge_of_iso_moserSpindle planeSpindle isoMP

/-- Decimal restatement: `χ_f ≥ 3.5` for the planar Moser spindle. -/
theorem planeSpindle_fractionalChromaticNumber_ge' :
    (3.5 : ℝ) ≤ fractionalChromaticNumber planeSpindle := by
  have h := planeSpindle_fractionalChromaticNumber_ge
  norm_num at h ⊢
  linarith [h]

/-- The adjacency of `planeSpindle` is exactly the unit-distance relation on the
seven points: it is a bona fide finite unit-distance subgraph of ℝ². -/
theorem planeSpindle_adj_iff (i j : Fin 7) :
    planeSpindle.Adj i j ↔ (i ≠ j ∧ dist (pt i) (pt j) = 1) := by
  simp only [planeSpindle, SimpleGraph.fromRel_adj, planeRel]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, by rw [dist_comm]; exact h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

end

end UnitDistanceIndependence.OQ04Embed
