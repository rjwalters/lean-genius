import Proofs.Erdos85OddSquareOrderNonregularProfile
import Proofs.Erdos85RegularCubicResidualFiberHistogram

/-! # Five-bin high-incidence census at odd square order q = 9

Node: B.3 / GAP B-CLASSIFY.  Every vertex of a q=9 nonregular square-order
profile has between zero and four high neighbors.  The profile's exact first
two incidence moments therefore become a finite five-bin histogram problem.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def squareOrderNineHighIncidenceHistogram
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) : ℕ :=
  boundedHistogram Finset.univ (squareOrderHighIncidenceCount G 9) t

/-- Complete five-bin census.  Besides the exact zeroth, first and second
moments, every high vertex lies in the zero-incidence bin. -/
theorem squareOrderNine_highIncidenceHistogram_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9) :
    let c := squareOrderNineHighIncidenceHistogram G
    let h := (squareOrderHighVertices G 9).card
    (∑ t ∈ Finset.range 5, c t) = 81 ∧
      (∑ t ∈ Finset.range 5, t * c t) = 10 * h ∧
      (∑ t ∈ Finset.range 5, t ^ 2 * c t) = h * (h + 9) ∧
      h ≤ c 0 := by
  classical
  dsimp only
  let H := squareOrderHighVertices G 9
  let k : V → ℕ := squareOrderHighIncidenceCount G 9
  let c := squareOrderNineHighIncidenceHistogram G
  have hkzero {x : V} (hx : x ∈ H) : k x = 0 := by
    have hinter : G.neighborFinset x ∩ H = ∅ := by
      ext y
      constructor
      · intro hy
        have hy' := Finset.mem_inter.mp hy
        have hadj : G.Adj x y := (G.mem_neighborFinset x y).mp hy'.1
        exact (hp.high_independent hx hy'.2 hadj).elim
      · intro hy
        simp at hy
    simp [k, squareOrderHighIncidenceCount, H, hinter]
  have hkbound : ∀ x ∈ (Finset.univ : Finset V), k x ≤ 4 := by
    intro x _
    by_cases hx : x ∈ H
    · rw [hkzero hx]
      omega
    · rcases hp.degree_dichotomy x with hxlow | hxhigh
      · have hle := hp.low_incidence_bound hxlow
        change 2 * k x ≤ 9 at hle
        omega
      · have hxmem : x ∈ H := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxhigh⟩
        exact (hx hxmem).elim
  obtain ⟨hzero, hone, htwo⟩ :=
    boundedHistogram_moments (Finset.univ : Finset V) k 4 hkbound
  have hfirst : (∑ x : V, k x) = 10 * H.card := by
    simpa [k, H] using hp.first_moment
  have hsecond : (∑ x : V, (k x) ^ 2) = H.card * (H.card + 9) := by
    simpa [k, H] using hp.second_moment
  have hsubset : H ⊆ (Finset.univ.filter fun x : V ↦ k x = 0) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hkzero hx⟩
  have hzeroBin : H.card ≤ c 0 := by
    have := Finset.card_le_card hsubset
    simpa [c, squareOrderNineHighIncidenceHistogram,
      boundedHistogram, k] using this
  have hzero' : (∑ t ∈ Finset.range 5, c t) = 81 := by
    simpa [c, squareOrderNineHighIncidenceHistogram, k, hcard] using hzero
  have hone' : (∑ t ∈ Finset.range 5, t * c t) = 10 * H.card := by
    simpa [c, squareOrderNineHighIncidenceHistogram, k, hfirst] using hone
  have htwo' : (∑ t ∈ Finset.range 5, t ^ 2 * c t) =
      H.card * (H.card + 9) := by
    simpa [c, squareOrderNineHighIncidenceHistogram, k, hsecond] using htwo
  exact ⟨hzero', hone', htwo', hzeroBin⟩

end

end Erdos85

#print axioms Erdos85.squareOrderNine_highIncidenceHistogram_ledger
