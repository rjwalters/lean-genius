/-
  Aristotle targets for Erdős Problem #798
  Routine supporting lemmas for automated proof search.
  See Erdos798Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main bounds (Erdős-Purdy lower, Alon upper) which are axiomatized
  - Known results provable from Mathlib (cardinality, combinatorics, analysis)
  - Clean theorem statements with no definition sorries
  - No axioms

  The main file formalizes: t(n) = min points in {1,...,n}^2 whose
  lines cover all lattice points. Result: t(n) = Theta(n^{2/3} log n).
-/
import Mathlib

namespace Erdos798Aristotle

open Set Real Finset

/- ## Definitions (mirrored from Erdos798Problem.lean) -/

/-- The lattice grid {1,...,n}^2. -/
def latticeGrid (n : ℕ) : Set (ℤ × ℤ) :=
  {p | 1 ≤ p.1 ∧ p.1 ≤ n ∧ 1 ≤ p.2 ∧ p.2 ≤ n}

/-- Line through two distinct points. -/
def lineThroughPoints (p q : ℤ × ℤ) : Set (ℤ × ℤ) :=
  if p = q then {p}
  else {r : ℤ × ℤ | ∃ t : ℚ, r.1 = p.1 + t * (q.1 - p.1) ∧
                             r.2 = p.2 + t * (q.2 - p.2)}

/-- A set S covers the grid if every lattice point lies on a line from S. -/
def pointsCoversGrid (S : Set (ℤ × ℤ)) (n : ℕ) : Prop :=
  ∀ r ∈ latticeGrid n, ∃ p q : ℤ × ℤ, p ∈ S ∧ q ∈ S ∧ p ≠ q ∧
    r ∈ lineThroughPoints p q

/-- t(n): minimum covering points. -/
noncomputable def t (n : ℕ) : ℕ :=
  sInf {k : ℕ | ∃ S : Finset (ℤ × ℤ), S.card = k ∧
    (↑S : Set (ℤ × ℤ)) ⊆ latticeGrid n ∧
    pointsCoversGrid (↑S) n}

/- ## Routine Lemmas -/

-- Lattice grid properties
/-- The lattice grid {1,...,n}^2 has n^2 points. -/
theorem latticeGrid_card (n : ℕ) (hn : n ≥ 1) :
    (latticeGrid n).ncard = n ^ 2 := by
  have heq : latticeGrid n = (Set.Icc (1 : ℤ) ↑n) ×ˢ (Set.Icc (1 : ℤ) ↑n) := by
    ext ⟨x, y⟩; simp [latticeGrid, Set.mem_prod, Set.mem_Icc]
  rw [heq, Set.ncard_prod (Set.finite_Icc _ _) (Set.finite_Icc _ _)]
  suffices h : (Set.Icc (1 : ℤ) ↑n).ncard = n by rw [h]; ring
  rw [Set.ncard_eq_toFinset_card’ (Set.Icc (1 : ℤ) ↑n)]
  simp only [Set.toFinset_Icc, Finset.card_Icc]
  omega

/-- The lattice grid is finite. -/
theorem latticeGrid_finite (n : ℕ) :
    (latticeGrid n).Finite := by
  apply Set.Finite.subset (Set.Finite.prod (Set.finite_Icc (1 : ℤ) n) (Set.finite_Icc 1 n))
  intro ⟨x, y⟩ ⟨h1, h2, h3, h4⟩
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

/-- A point (i,j) with 1 ≤ i,j ≤ n is in the lattice grid. -/
theorem mem_latticeGrid (n : ℕ) (i j : ℤ)
    (hi1 : 1 ≤ i) (hi2 : i ≤ n) (hj1 : 1 ≤ j) (hj2 : j ≤ n) :
    (i, j) ∈ latticeGrid n :=
  ⟨hi1, hi2, hj1, hj2⟩

-- Line properties
/-- A point lies on the line through it and any other point. -/
theorem mem_lineThroughPoints_left (p q : ℤ × ℤ) :
    p ∈ lineThroughPoints p q := by
  simp only [lineThroughPoints]
  split
  · exact Set.mem_singleton _
  · exact ⟨0, by simp⟩

/-- The second point also lies on the line. -/
theorem mem_lineThroughPoints_right (p q : ℤ × ℤ) :
    q ∈ lineThroughPoints p q := by
  simp only [lineThroughPoints]
  split
  · next h => rw [h]; exact Set.mem_singleton _
  · exact ⟨1, by simp⟩

/-- Lines are symmetric: the line through p,q equals the line through q,p. -/
theorem lineThroughPoints_symm (p q : ℤ × ℤ) :
    lineThroughPoints p q = lineThroughPoints q p := by
  simp only [lineThroughPoints]
  split_ifs with h1 h2 h2
  · rw [h1]
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · ext r
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨t, ht1, ht2⟩
      exact ⟨1 - t, by push_cast; linarith, by push_cast; linarith⟩
    · rintro ⟨t, ht1, ht2⟩
      exact ⟨1 - t, by push_cast; linarith, by push_cast; linarith⟩

-- Combinatorial bound
/-- k points determine at most k*(k-1)/2 lines. -/
theorem lines_from_points (S : Finset (ℤ × ℤ)) :
    ∃ L : Finset (Set (ℤ × ℤ)), L.card ≤ S.card.choose 2 ∧
    ∀ p q : ℤ × ℤ, p ∈ S → q ∈ S → p ≠ q →
    lineThroughPoints p q ∈ L := by sorry

-- Asymptotic (with hypothesis instead of axiom)
/-- If t(n) ≤ C·n^{2/3}·log n, then t(n) = o(n). -/
theorem t_is_o_n
    (C : ℝ) (hC : C > 0)
    (hbound : ∀ n : ℕ, n ≥ 2 → (t n : ℝ) ≤ C * n ^ (2/3 : ℝ) * Real.log n) :
    ∀ ε : ℝ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, (t n : ℝ) < ε * n := by sorry

end Erdos798Aristotle
