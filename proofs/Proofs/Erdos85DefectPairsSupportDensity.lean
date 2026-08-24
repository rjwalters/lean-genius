import Proofs.Erdos85DyadicStoppingSupportDefectPenalizedCherrySqueeze

/-!
# Density of defect pairs in a large support

In an `r`-regular graph, a vertex set `B` contributes `r|B|` directed
incidences.  Its complement can receive at most `r|Bᶜ|` of them, so the
remaining internal incidences force

`r|B| ≤ 2 e(B) + r|Bᶜ|`.

For the second-order defect graph at binary square order, `r=q-1`.  This is
the graph-native support-size input behind the defect-pair penalty: a marked
support larger than half the vertices necessarily contains many forbidden
pairs.  The inequality is not by itself a terminal contradiction.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The spanning subgraph consisting of the edges of `D` with both endpoints
in `B`.  Keeping the ambient vertex type avoids subtype bookkeeping in later
pair-count consumers. -/
def supportedEdgeGraph
    {V : Type*} [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (B : Finset V) : SimpleGraph V where
  Adj u v := D.Adj u v ∧ u ∈ B ∧ v ∈ B
  symm := ⟨by
    intro u v h
    exact ⟨D.adj_symm h.1, h.2.2, h.2.1⟩⟩
  loopless := ⟨by
    intro u h
    exact D.irrefl h.1⟩

@[simp] theorem supportedEdgeGraph_adj
    {V : Type*} [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (B : Finset V) (u v : V) :
    (supportedEdgeGraph D B).Adj u v ↔ D.Adj u v ∧ u ∈ B ∧ v ∈ B :=
  Iff.rfl

instance supportedEdgeGraph_decidableRel
    {V : Type*} [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (B : Finset V) :
    DecidableRel (supportedEdgeGraph D B).Adj := by
  intro u v
  simp only [supportedEdgeGraph_adj]
  infer_instance

/-- A regular graph's internal directed incidence mass is large whenever the
set is larger than its complement. -/
theorem regular_internal_incidence_density
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {r : ℕ} (hreg : ∀ v, D.degree v = r) (B : Finset V) :
    r * B.card ≤
      (∑ v ∈ B, (D.neighborFinset v ∩ B).card) +
        r * (Bᶜ : Finset V).card := by
  have htotal := regular_shore_compl_incidence_sum D hreg B B
  have hout :
      (∑ v ∈ (Bᶜ : Finset V), (D.neighborFinset v ∩ B).card) ≤
        r * (Bᶜ : Finset V).card := by
    calc
      (∑ v ∈ (Bᶜ : Finset V), (D.neighborFinset v ∩ B).card) ≤
          ∑ _v ∈ (Bᶜ : Finset V), r := by
        apply Finset.sum_le_sum
        intro v hv
        calc
          (D.neighborFinset v ∩ B).card ≤ (D.neighborFinset v).card :=
            Finset.card_le_card Finset.inter_subset_left
          _ = D.degree v := D.card_neighborFinset_eq_degree v
          _ = r := hreg v
      _ = r * (Bᶜ : Finset V).card := by simp [Nat.mul_comm]
  omega

/-- Edge-count form of `regular_internal_incidence_density`. -/
theorem regular_supported_edge_density
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {r : ℕ} (hreg : ∀ v, D.degree v = r) (B : Finset V) :
    r * B.card ≤
      2 * (supportedEdgeGraph D B).edgeFinset.card +
        r * (Bᶜ : Finset V).card := by
  have h := regular_internal_incidence_density D hreg B
  have hinter :
      (∑ v ∈ B, (D.neighborFinset v ∩ B).card) =
        2 * (supportedEdgeGraph D B).edgeFinset.card := by
    classical
    calc
      (∑ v ∈ B, (D.neighborFinset v ∩ B).card) =
          ∑ v ∈ B, (supportedEdgeGraph D B).degree v := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [← (supportedEdgeGraph D B).card_neighborFinset_eq_degree]
        congr 1
        ext w
        simp [SimpleGraph.mem_neighborFinset, hv, and_comm]
      _ = ∑ v : V, (supportedEdgeGraph D B).degree v := by
        apply Finset.sum_subset (Finset.subset_univ B)
        intro v hvU hvB
        rw [SimpleGraph.degree_eq_zero_iff_notMem_support]
        intro hvSupp
        obtain ⟨w, hvw⟩ := hvSupp
        exact hvB (supportedEdgeGraph_adj D B v w |>.mp hvw).2.1
      _ = 2 * (supportedEdgeGraph D B).edgeFinset.card :=
        (supportedEdgeGraph D B).sum_degrees_eq_twice_card_edges
  rwa [hinter] at h

/-- The internal edges of the supported defect graph are exactly the
canonical two-element defect pairs used by the forbidden-cherry bound. -/
theorem supportedSecondOrder_edge_card_eq_defectPairs
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (B : Finset V) :
    (supportedEdgeGraph (secondOrderDefectGraph G) B).edgeFinset.card =
      (secondOrderDefectPairs G B).card := by
  classical
  let H := supportedEdgeGraph (secondOrderDefectGraph G) B
  apply Finset.card_bij (fun e _he => e.toFinset)
  · intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    change e.toFinset ∈ (B.powersetCard 2).filter (fun T =>
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (secondOrderDefectGraph G).Adj u v)
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · constructor
      · intro x hx
        induction e using Sym2.inductionOn with
        | _ u v =>
          simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
            Finset.mem_singleton] at hx
          have huvB :=
            ((supportedEdgeGraph_adj (secondOrderDefectGraph G) B u v).mp he).2
          rcases hx with rfl | rfl
          · exact huvB.1
          · exact huvB.2
      · exact Sym2.card_toFinset_of_not_isDiag e
          ((supportedEdgeGraph (secondOrderDefectGraph G) B).not_isDiag_of_mem_edgeFinset
            (by simpa [H] using he))
    · intro u hu v hv huv
      induction e using Sym2.inductionOn with
      | _ x y =>
        simp only [Sym2.toFinset_mk_eq, Finset.mem_insert,
          Finset.mem_singleton] at hu hv
        have hxy :=
          ((supportedEdgeGraph_adj (secondOrderDefectGraph G) B x y).mp he).1
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact (huv rfl).elim
        · exact hxy
        · exact hxy.symm
        · exact (huv rfl).elim
  · intro e he f hf hef
    induction e using Sym2.inductionOn with
    | _ u v =>
      induction f using Sym2.inductionOn with
      | _ x y =>
        have hef' : ({u, v} : Finset V) = {x, y} := by
          simpa [Sym2.toFinset_mk_eq] using hef
        have huv : u ≠ v := by
          have hn : ¬s(u, v).IsDiag :=
            (supportedEdgeGraph (secondOrderDefectGraph G) B).not_isDiag_of_mem_edgeFinset he
          simpa [Sym2.mk_isDiag_iff] using hn
        have hxy : x ≠ y := by
          have hn : ¬s(x, y).IsDiag :=
            (supportedEdgeGraph (secondOrderDefectGraph G) B).not_isDiag_of_mem_edgeFinset hf
          simpa [Sym2.mk_isDiag_iff] using hn
        have hu : u = x ∨ u = y := by
          have : u ∈ ({x, y} : Finset V) := by
            rw [← hef']
            simp
          simpa using this
        have hv : v = x ∨ v = y := by
          have : v ∈ ({x, y} : Finset V) := by
            rw [← hef']
            simp
          simpa using this
        rw [Sym2.eq_iff]
        aesop
  · intro T hT
    change T ∈ (B.powersetCard 2).filter (fun T =>
      ∀ u ∈ T, ∀ v ∈ T, u ≠ v → (secondOrderDefectGraph G).Adj u v) at hT
    have hdata := Finset.mem_filter.mp hT
    have hsub := (Finset.mem_powersetCard.mp hdata.1).1
    obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp
      (Finset.mem_powersetCard.mp hdata.1).2
    refine ⟨s(u, v), ?_, Sym2.toFinset_mk_eq⟩
    rw [SimpleGraph.mem_edgeFinset]
    exact (supportedEdgeGraph_adj (secondOrderDefectGraph G) B u v).mpr
      ⟨hdata.2 u (by simp) v (by simp) huv,
        hsub (by simp), hsub (by simp)⟩

/-- At binary square order, a marked support larger than half the vertices
contains a quantitatively forced number of internal defect pairs. -/
theorem binarySquare_secondOrderDefectPairs_support_density
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q : ℕ} (hcard : Fintype.card V = q * q)
    (hDreg : ∀ v, (secondOrderDefectGraph G).degree v = q - 1)
    (B : Finset V) :
    (q - 1) * B.card ≤
      2 * (secondOrderDefectPairs G B).card +
        (q - 1) * (q * q - B.card) := by
  have h := regular_supported_edge_density
    (secondOrderDefectGraph G) hDreg B
  rw [supportedSecondOrder_edge_card_eq_defectPairs G B] at h
  rwa [Finset.card_compl, hcard] at h

/-- The defect-penalized cherry squeeze together with its graph-native
support-density constraint.  This package lets arithmetic consumers retain
the actual number of internal defect pairs instead of replacing it by zero. -/
theorem c4Free_binarySquare_dyadicStoppingSupport_defectDensity_cherry_squeeze
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hq : 3 ≤ q)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (j : ℕ)
    (hdiv : ∀ v, 2 ^ j ∣ (G.neighborFinset v ∩ S).card)
    (hqdiv : 2 ^ (j + 1) ∣ q) :
    let B := dyadicOccupancySupport G S j
    S.card * (dyadicStoppingServiceMinimum q S.card j).choose 2 +
          (Sᶜ : Finset V).card *
            (dyadicStoppingServiceMinimum q (Sᶜ : Finset V).card j).choose 2 ≤
        B.card.choose 2 - (secondOrderDefectPairs G B).card ∧
      (q - 1) * B.card ≤
        2 * (secondOrderDefectPairs G B).card +
          (q - 1) * (q * q - B.card) := by
  dsimp only
  exact ⟨c4Free_dyadicStoppingSupport_twoShore_defectPenalized_cherry_squeeze
      G hfree hreg S j hdiv hqdiv,
    binarySquare_secondOrderDefectPairs_support_density
      G hcard (binarySquare_regular_secondOrderDefect_degree_eq
        G hfree hq hreg hcard) (dyadicOccupancySupport G S j)⟩

end

end Erdos85

#print axioms Erdos85.regular_internal_incidence_density
#print axioms Erdos85.regular_supported_edge_density
#print axioms Erdos85.supportedSecondOrder_edge_card_eq_defectPairs
#print axioms Erdos85.binarySquare_secondOrderDefectPairs_support_density
#print axioms
  Erdos85.c4Free_binarySquare_dyadicStoppingSupport_defectDensity_cherry_squeeze
