import Proofs.Erdos85PositiveExcessOnePincer

/-!
# Trace-to-count bridges for the excess-one pincer

The mixed moment `tr(M C²)` counts oriented matching chords of the
antipodal two-factor.  This file turns that walk count into twice the
number of matching-chordal centres.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Oriented matching chords through the antipodal centre `X`. -/
def matchingChordOrientations
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : V) : Finset (V × V) := by
  classical
  exact ((antipodalNeighbors G X).product (antipodalNeighbors G X)).filter
    fun p => p.2 ∈ triangleFreeNeighbors G p.1

/-- A chordal two-element antipodal neighbourhood contributes exactly two
oriented matching chords. -/
theorem card_matchingChordOrientations_of_chordal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hanti : ∀ X, (antipodalNeighbors G X).card = 2) (X : V)
    (hX : IsMatchingChordalCenter G X) :
    (matchingChordOrientations G X).card = 2 := by
  classical
  obtain ⟨a, b, hab, hpairs⟩ := Finset.card_eq_two.mp (hanti X)
  have hba : b ∈ triangleFreeNeighbors G a :=
    hX a (by simp [hpairs]) b (by simp [hpairs]) hab
  have habTF : a ∈ triangleFreeNeighbors G b :=
    (mem_triangleFreeNeighbors_comm G b a).mpr hba
  have hself : ∀ x : V, x ∉ triangleFreeNeighbors G x := by
    intro x hx
    exact G.loopless.irrefl x ((mem_triangleFreeNeighbors G x x).mp hx).1
  have hbaRaw : G.Adj a b ∧
      G.neighborFinset a ∩ G.neighborFinset b = ∅ := by
    have h := (mem_triangleFreeNeighbors G a b).mp hba
    exact ⟨h.1, Finset.card_eq_zero.mp h.2⟩
  have habRaw : G.Adj b a ∧
      G.neighborFinset b ∩ G.neighborFinset a = ∅ := by
    have h := (mem_triangleFreeNeighbors G b a).mp habTF
    exact ⟨h.1, Finset.card_eq_zero.mp h.2⟩
  have heq : matchingChordOrientations G X = {(a, b), (b, a)} := by
    apply Finset.ext
    intro p
    constructor
    · intro hp
      rcases p with ⟨x, y⟩
      have hp' := Finset.mem_filter.mp hp
      have hprod := Finset.mem_product.mp hp'.1
      rw [hpairs] at hprod
      simp only [Finset.mem_insert, Finset.mem_singleton,
        Prod.fst, Prod.snd] at hprod hp'
      rcases hprod.1 with rfl | rfl <;> rcases hprod.2 with rfl | rfl
      · exact (hself _ hp'.2).elim
      · simp
      · simp
      · exact (hself _ hp'.2).elim
    · intro hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
          ⟨by simp [hpairs], by simp [hpairs]⟩, hba⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr
          ⟨by simp [hpairs], by simp [hpairs]⟩, habTF⟩
  rw [heq]
  simp [hab]

/-- A nonchordal two-element antipodal neighbourhood contributes no
oriented matching chord. -/
theorem card_matchingChordOrientations_of_not_chordal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hanti : ∀ X, (antipodalNeighbors G X).card = 2) (X : V)
    (hX : ¬ IsMatchingChordalCenter G X) :
    (matchingChordOrientations G X).card = 0 := by
  classical
  obtain ⟨a, b, hab, hpairs⟩ := Finset.card_eq_two.mp (hanti X)
  have hba : b ∉ triangleFreeNeighbors G a := by
    intro hba
    apply hX
    intro x hx y hy hxy
    rw [hpairs] at hx hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact hba
    · exact (mem_triangleFreeNeighbors_comm G _ _).mpr hba
    · exact (hxy rfl).elim
  have habTF : a ∉ triangleFreeNeighbors G b := by
    intro h
    exact hba ((mem_triangleFreeNeighbors_comm G b a).mp h)
  have hself : ∀ x : V, x ∉ triangleFreeNeighbors G x := by
    intro x hx
    exact G.loopless.irrefl x ((mem_triangleFreeNeighbors G x x).mp hx).1
  have hbaRaw : ¬(G.Adj a b ∧
      G.neighborFinset a ∩ G.neighborFinset b = ∅) := by
    intro h
    apply hba
    exact (mem_triangleFreeNeighbors G a b).mpr
      ⟨h.1, Finset.card_eq_zero.mpr h.2⟩
  have habRaw : ¬(G.Adj b a ∧
      G.neighborFinset b ∩ G.neighborFinset a = ∅) := by
    intro h
    apply habTF
    exact (mem_triangleFreeNeighbors G b a).mpr
      ⟨h.1, Finset.card_eq_zero.mpr h.2⟩
  simp [matchingChordOrientations, hpairs]
  intro x y hx hy hxy hempty
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact G.loopless.irrefl _ hxy
  · exact hbaRaw ⟨hxy, hempty⟩
  · exact habRaw ⟨hxy, hempty⟩
  · exact G.loopless.irrefl _ hxy

/-- The matching--antipodal-square trace is twice the number of chordal
centres. -/
theorem trace_matching_antipodal_sq_eq_two_mul_chordalCenters
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hanti : ∀ X, (antipodalNeighbors G X).card = 2) :
    Matrix.trace
      ((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) =
      2 * (matchingChordalCenters G).card := by
  classical
  let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  have hlocal : ∀ X : V,
      ((matchingChordOrientations G X).card : ℤ) =
        ∑ x : V, ∑ y : V, M x y * C y X * C X x := by
    intro X
    have hcount : ((matchingChordOrientations G X).card : ℤ) =
        ∑ x ∈ antipodalNeighbors G X,
          ∑ y ∈ antipodalNeighbors G X, M x y := by
      calc
        ((matchingChordOrientations G X).card : ℤ) =
            ∑ p ∈ (antipodalNeighbors G X).product
              (antipodalNeighbors G X),
                if p.2 ∈ triangleFreeNeighbors G p.1 then 1 else 0 := by
          simp [matchingChordOrientations, Finset.sum_boole]
        _ = ∑ p ∈ (antipodalNeighbors G X).product
              (antipodalNeighbors G X), M p.1 p.2 := by
          apply Finset.sum_congr rfl
          intro p _
          simp [M, SimpleGraph.adjMatrix_apply,
            triangleFreeEdgeGraph_adj]
        _ = ∑ x ∈ antipodalNeighbors G X,
              ∑ y ∈ antipodalNeighbors G X, M x y := by
          simpa using Finset.sum_product
            (antipodalNeighbors G X) (antipodalNeighbors G X)
            (fun p : V × V => M p.1 p.2)
    rw [hcount]
    symm
    calc
      (∑ x : V, ∑ y : V, M x y * C y X * C X x) =
          (C * (M * C)) X X := by
        simp only [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        ring
      _ = ∑ x ∈ antipodalNeighbors G X, (M * C) x X := by
        rw [(antipodalGraph G).adjMatrix_mul_apply,
          antipodalGraph_neighborFinset]
      _ = ∑ x ∈ antipodalNeighbors G X,
          ∑ y ∈ antipodalNeighbors G X, M x y := by
        apply Finset.sum_congr rfl
        intro x _
        rw [(antipodalGraph G).mul_adjMatrix_apply,
          antipodalGraph_neighborFinset]
  have hwalk : Matrix.trace (M * C * C) =
      ∑ X : V, ((matchingChordOrientations G X).card : ℤ) := by
    rw [Matrix.trace]
    calc
      (∑ x : V, (M * C * C) x x) =
          ∑ x : V, ∑ X : V, ∑ y : V,
            M x y * C y X * C X x := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro X _
        rw [Matrix.mul_apply, Finset.sum_mul]
      _ = ∑ X : V, ∑ x : V, ∑ y : V,
            M x y * C y X * C X x := by
        exact Finset.sum_comm
      _ = ∑ X : V, ((matchingChordOrientations G X).card : ℤ) := by
        apply Finset.sum_congr rfl
        intro X _
        exact (hlocal X).symm
  have hsum : (∑ X : V,
      ((matchingChordOrientations G X).card : ℤ)) =
      2 * (matchingChordalCenters G).card := by
    calc
      (∑ X : V, ((matchingChordOrientations G X).card : ℤ)) =
          ∑ X : V, if X ∈ matchingChordalCenters G then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro X _
        by_cases hX : X ∈ matchingChordalCenters G
        · rw [if_pos hX]
          have hchord : IsMatchingChordalCenter G X := by
            simpa [matchingChordalCenters] using hX
          exact_mod_cast card_matchingChordOrientations_of_chordal
            G hanti X hchord
        · rw [if_neg hX]
          have hnchord : ¬ IsMatchingChordalCenter G X := by
            simpa [matchingChordalCenters] using hX
          exact_mod_cast card_matchingChordOrientations_of_not_chordal
            G hanti X hnchord
      _ = 2 * (matchingChordalCenters G).card := by
        simp
        ring
  change Matrix.trace (M * C * C) =
    2 * (matchingChordalCenters G).card
  rw [hwalk, hsum]

end

end Erdos85
