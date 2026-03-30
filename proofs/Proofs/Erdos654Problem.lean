/-
# Erdős Problem #654 — Distinct Distances with No Four Concyclic

Given n points x₁, ..., xₙ ∈ ℝ² with no four points on a circle,
must there exist some xᵢ with at least (1 - o(1))n distinct distances
to the other points?

**Status: OPEN.**

Known: Every point has at least (n-1)/3 distinct distances.
Weaker variant (Erdős–Pach): under general position (no 3 collinear),
does some point have ≥ (1/3 + c)n distinct distances?

Reference: https://erdosproblems.com/654
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/- ## Core Definitions -/

/-- A point configuration in the plane. -/
def PointConfig (n : ℕ) := Fin n → ℝ × ℝ

/-- No four points lie on a common circle. -/
def NoFourConcyclic (P : PointConfig n) : Prop :=
  ∀ i₁ i₂ i₃ i₄ : Fin n,
    i₁ ≠ i₂ → i₁ ≠ i₃ → i₁ ≠ i₄ → i₂ ≠ i₃ → i₂ ≠ i₄ → i₃ ≠ i₄ →
    ¬∃ (c : ℝ × ℝ) (r : ℝ), r > 0 ∧
      dist (P i₁) c = r ∧ dist (P i₂) c = r ∧
      dist (P i₃) c = r ∧ dist (P i₄) c = r

/-- The number of distinct distances from point xᵢ to all other points. -/
noncomputable def distinctDistances (P : PointConfig n) (i : Fin n) : ℕ :=
  ((Finset.univ.filter (· ≠ i)).image (fun j => dist (P i) (P j))).card

/-- The maximum number of distinct distances from any single point. -/
noncomputable def maxDistinctDistances (P : PointConfig n) [NeZero n] : ℕ :=
  Finset.univ.sup' ⟨⟨0, NeZero.pos n⟩, Finset.mem_univ _⟩ (distinctDistances P)

/- ## Known Lower Bound -/

/-- Every point has at least (n-1)/3 distinct distances when
    no four are concyclic. -/
/- ## The Main Conjecture -/

/-- **Erdős Problem #654**: Under the no-four-concyclic condition,
    some point must determine (1 - o(1))n distinct distances.
    Formally: for every ε > 0, for large enough n, some xᵢ has
    ≥ (1 - ε)n distinct distances. -/
/- ## Erdős–Pach Weaker Variant -/

/-- General position: no three points are collinear. -/
def NoThreeCollinear (P : PointConfig n) : Prop :=
  ∀ i₁ i₂ i₃ : Fin n, i₁ ≠ i₂ → i₂ ≠ i₃ → i₁ ≠ i₃ →
    ¬∃ (a b c : ℝ), (a, b) ≠ (0, 0) ∧
      a * (P i₁).1 + b * (P i₁).2 = c ∧
      a * (P i₂).1 + b * (P i₂).2 = c ∧
      a * (P i₃).1 + b * (P i₃).2 = c

/-- Erdős–Pach weaker conjecture: under general position,
    does some point have ≥ (1/3 + c)n distinct distances for
    some absolute constant c > 0? -/
/- ## Context: Erdős Distinct Distances Problem -/

/-- Without any restriction, the Guth–Katz theorem (2015) gives
    Ω(n/log n) distinct distances in total. Problem #654 asks for
    near-n distinct distances from a SINGLE point, under geometric
    restrictions on the configuration. -/
/-- On a circle, at most 2 points determine each distance from
    the center. So the no-four-concyclic condition prevents
    many repeated distances from a single point. -/
theorem circle_distance_bound (P : PointConfig n) (hP : NoFourConcyclic P)
    (i : Fin n) (d : ℝ) (hd : 0 < d) :
    ((Finset.univ.filter (fun j => j ≠ i ∧ dist (P i) (P j) = d)).card) ≤ 3 := by
  by_contra h
  push_neg at h
  set S := Finset.univ.filter (fun j : Fin n => j ≠ i ∧ dist (P i) (P j) = d)
  -- Extract 4 distinct elements from S (|S| ≥ 4)
  have ⟨j₁, hj₁⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have ⟨j₂, hj₂⟩ := Finset.card_pos.mp (show 0 < (S.erase j₁).card by
    rw [Finset.card_erase_of_mem hj₁]; omega)
  have h12 : j₂ ≠ j₁ := Finset.ne_of_mem_erase hj₂
  have hj₂' : j₂ ∈ S := Finset.mem_of_mem_erase hj₂
  have ⟨j₃, hj₃⟩ := Finset.card_pos.mp (show 0 < ((S.erase j₁).erase j₂).card by
    rw [Finset.card_erase_of_mem hj₂, Finset.card_erase_of_mem hj₁]; omega)
  have h32 : j₃ ≠ j₂ := Finset.ne_of_mem_erase hj₃
  have hj₃_e1 : j₃ ∈ S.erase j₁ := Finset.mem_of_mem_erase hj₃
  have h31 : j₃ ≠ j₁ := Finset.ne_of_mem_erase hj₃_e1
  have hj₃' : j₃ ∈ S := Finset.mem_of_mem_erase hj₃_e1
  have ⟨j₄, hj₄⟩ := Finset.card_pos.mp (show 0 < (((S.erase j₁).erase j₂).erase j₃).card by
    rw [Finset.card_erase_of_mem hj₃,
        Finset.card_erase_of_mem hj₂,
        Finset.card_erase_of_mem hj₁]; omega)
  have h43 : j₄ ≠ j₃ := Finset.ne_of_mem_erase hj₄
  have hj₄_e12 : j₄ ∈ (S.erase j₁).erase j₂ := Finset.mem_of_mem_erase hj₄
  have h42 : j₄ ≠ j₂ := Finset.ne_of_mem_erase hj₄_e12
  have hj₄_e1 : j₄ ∈ S.erase j₁ := Finset.mem_of_mem_erase hj₄_e12
  have h41 : j₄ ≠ j₁ := Finset.ne_of_mem_erase hj₄_e1
  have hj₄' : j₄ ∈ S := Finset.mem_of_mem_erase hj₄_e1
  -- Extract distance properties from membership in S
  have hd₁ : dist (P i) (P j₁) = d := ((Finset.mem_filter.mp hj₁).2).2
  have hd₂ : dist (P i) (P j₂) = d := ((Finset.mem_filter.mp hj₂').2).2
  have hd₃ : dist (P i) (P j₃) = d := ((Finset.mem_filter.mp hj₃').2).2
  have hd₄ : dist (P i) (P j₄) = d := ((Finset.mem_filter.mp hj₄').2).2
  -- All 4 points lie on the circle centered at P i with radius d
  rw [dist_comm] at hd₁ hd₂ hd₃ hd₄
  exact hP j₁ j₂ j₃ j₄ h12.symm h31.symm h41.symm h32.symm h42.symm h43.symm
    ⟨P i, d, hd, hd₁, hd₂, hd₃, hd₄⟩
