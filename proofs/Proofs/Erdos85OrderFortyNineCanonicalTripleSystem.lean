import Proofs.Erdos85OrderFortyNineGraphPrefixNormalization
import Proofs.Erdos85OrderFortyNineRowSemantics

/-!
# Canonical triple-support systems at order 49

This file composes the graph-facing prefix normalization with the semantic
content of the finite witness tables.  Its output is coordinate-free: after
one further permutation of the nine high labels, the graph's complete family
of three-point high supports is exactly one of the canonical representative
systems used by the certified SAT instances.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

open OrderFortyNineWitnessTable

/-- Relabeling the high coordinates acts on every labeled support by the
corresponding `Finset.map`. -/
theorem orderFortyNineLabeledHighSupport_trans
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (σ : Equiv.Perm (Fin 9)) (x : V) :
    orderFortyNineLabeledHighSupport G (e.trans σ) x =
      (orderFortyNineLabeledHighSupport G e x).map σ.toEmbedding := by
  unfold orderFortyNineLabeledHighSupport
  rw [Finset.map_map]
  rfl

/-- The graph's three-point high supports, in a chosen labeling, are exactly
the triples of `rep` (viewed as ordinary finite sets of natural numbers). -/
def OrderFortyNineCanonicalTripleSystemSpec
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (rep : OrderFortyNineH9System) : Prop :=
  let X := (orderFortyNineLowVertices G).filter fun x =>
    (orderFortyNineHighSupport G x).card = 3
  (∀ x ∈ X, ∃ T ∈ h9SystemTriples rep,
    (orderFortyNineLabeledHighSupport G e x).image Fin.val = T.toFinset) ∧
  (∀ T ∈ h9SystemTriples rep, ∃ x ∈ X,
    (orderFortyNineLabeledHighSupport G e x).image Fin.val = T.toFinset)

/-- A semantic table witness for a list enumerating all triple-support
vertices produces a canonical graph labeling. -/
theorem exists_canonicalTripleSystem_of_row
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {reps : Array OrderFortyNineH9System} {row : Row}
    (hspec : RowSemanticSpec reps row)
    (e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9)
    (xs : List V)
    (hX : (orderFortyNineLowVertices G).filter (fun x =>
      (orderFortyNineHighSupport G x).card = 3) = xs.toFinset)
    (hrow : row.1 = xs.map fun x =>
      tripleDigits (orderFortyNineLabeledHighSupport G e x)) :
    ∃ rep, ∃ e' : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
      reps[row.2.1]? = some rep ∧
      OrderFortyNineCanonicalTripleSystemSpec G e' rep := by
  let supports := xs.map fun x => orderFortyNineLabeledHighSupport G e x
  have hrow' : row.1 = supports.map tripleDigits := by
    dsimp only [supports]
    rw [List.map_map]
    simpa only [Function.comp_def] using hrow
  obtain ⟨rep, σ, hrep, hforward, hback⟩ :=
    OrderFortyNineWitnessTable.RowSemanticSpec.transport_supports
      hspec supports hrow'
  refine ⟨rep, e.trans σ, hrep, ?_, ?_⟩
  · intro x hx
    have hxin : x ∈ xs := by
      rw [hX] at hx
      simpa using hx
    have hsupport : orderFortyNineLabeledHighSupport G e x ∈ supports :=
      List.mem_map.mpr ⟨x, hxin, rfl⟩
    obtain ⟨T, hT, hEq⟩ := hforward _ hsupport
    refine ⟨T, hT, ?_⟩
    rw [orderFortyNineLabeledHighSupport_trans]
    exact hEq
  · intro T hT
    obtain ⟨S, hS, hEq⟩ := hback T hT
    obtain ⟨x, hx, hxS⟩ := List.mem_map.mp hS
    refine ⟨x, ?_, ?_⟩
    · rw [hX]
      simpa using hx
    · subst S
      rw [orderFortyNineLabeledHighSupport_trans]
      exact hEq

/-- Every graph in the two-triple, nine-high stratum has a canonical
representative support system. -/
theorem orderFortyNine_exists_canonicalT2System
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 2) :
    ∃ row ∈ tableT2, ∃ rep,
      orderFortyNineH9T2Systems[row.2.1]? = some rep ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
        OrderFortyNineCanonicalTripleSystemSpec G e rep := by
  obtain ⟨x, y, hX, hxy, e, row, hrowmem, hrow⟩ :=
    orderFortyNine_exists_tableT2_row_of_tripleSupportCount_two
      G hfree hHigh hcount
  have hXlist : (orderFortyNineLowVertices G).filter (fun z =>
      (orderFortyNineHighSupport G z).card = 3) = [x, y].toFinset := by
    simpa [hxy] using hX
  obtain ⟨rep, e', hrep, hcanon⟩ := exists_canonicalTripleSystem_of_row
    G (exists_rep_rowPerm_systemSpec_of_mem_tableT2 hrowmem) e [x, y]
      hXlist (by simpa using hrow)
  exact ⟨row, hrowmem, rep, hrep, e', hcanon⟩

/-- Every graph in the three-triple, nine-high stratum has a canonical
representative support system. -/
theorem orderFortyNine_exists_canonicalT3System
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 3) :
    ∃ row ∈ tableT3, ∃ rep,
      orderFortyNineH9T3Systems[row.2.1]? = some rep ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
        OrderFortyNineCanonicalTripleSystemSpec G e rep := by
  obtain ⟨x, y, z, hX, e, row, hrowmem, hrow⟩ :=
    orderFortyNine_exists_tableT3_row_of_tripleSupportCount_three
      G hfree hHigh hcount
  have hXlist : (orderFortyNineLowVertices G).filter (fun u =>
      (orderFortyNineHighSupport G u).card = 3) = [x, y, z].toFinset := by
    simpa using hX
  obtain ⟨rep, e', hrep, hcanon⟩ := exists_canonicalTripleSystem_of_row
    G (exists_rep_rowPerm_systemSpec_of_mem_tableT3 hrowmem) e [x, y, z]
      hXlist (by simpa using hrow)
  exact ⟨row, hrowmem, rep, hrep, e', hcanon⟩

/-- Every graph in the four-triple, nine-high stratum has a canonical
representative support system.  The residual ordering chosen by L1 is
irrelevant because the semantic specification is setwise. -/
theorem orderFortyNine_exists_canonicalT4System
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 4) :
    ∃ row ∈ tableT4, ∃ rep,
      orderFortyNineH9T4Systems[row.2.1]? = some rep ∧
      ∃ e : {v // v ∈ orderFortyNineHighVertices G} ≃ Fin 9,
        OrderFortyNineCanonicalTripleSystemSpec G e rep := by
  obtain ⟨x, y, z, w, hX, e, row, hrowmem, hrow | hrow⟩ :=
    orderFortyNine_exists_tableT4_row_of_tripleSupportCount_four
      G hfree hHigh hcount
  · have hXlist : (orderFortyNineLowVertices G).filter (fun u =>
        (orderFortyNineHighSupport G u).card = 3) = [x, y, z, w].toFinset := by
      simpa using hX
    obtain ⟨rep, e', hrep, hcanon⟩ := exists_canonicalTripleSystem_of_row
      G (exists_rep_rowPerm_systemSpec_of_mem_tableT4 hrowmem) e [x, y, z, w]
        hXlist (by simpa using hrow)
    exact ⟨row, hrowmem, rep, hrep, e', hcanon⟩
  · have hXlist : (orderFortyNineLowVertices G).filter (fun u =>
        (orderFortyNineHighSupport G u).card = 3) = [x, y, w, z].toFinset := by
      rw [hX]
      ext u
      simp only [List.mem_toFinset, List.mem_cons,
        Finset.mem_insert, Finset.mem_singleton]
      tauto
    obtain ⟨rep, e', hrep, hcanon⟩ := exists_canonicalTripleSystem_of_row
      G (exists_rep_rowPerm_systemSpec_of_mem_tableT4 hrowmem) e [x, y, w, z]
        hXlist (by simpa using hrow)
    exact ⟨row, hrowmem, rep, hrep, e', hcanon⟩

end

end Erdos85
