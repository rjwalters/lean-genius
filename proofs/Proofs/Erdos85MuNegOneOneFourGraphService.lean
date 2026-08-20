import Proofs.Erdos85MuNegOneOneFourGraphRelations

/-!
# Service fields for the μ=-1 `(1,4)` finite semantics

Node: outline F.3 (bridge increment 3c-ii-g; squad msg 14102).

Wires the banked server classification and admissibility into the two
service fields of the finite-semantics record, for the concrete
relations: every twelve-set target of an active owner is served by a
generated hit variable, and the server is unique by common-server
uniqueness plus owner-vertex injectivity.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

/-- Value form of pair membership. -/
theorem muNegOnePairMem_iff (p : Nat × Nat) (w : Nat) :
    muNegOnePairMem p w = true ↔ p.1 = w ∨ p.2 = w := by
  unfold muNegOnePairMem
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq]

/-- Twelve-set members are internal codes. -/
theorem muNegOneTwelve_mem_lt (p : Nat × Nat) {w : Nat}
    (hw : w ∈ muNegOneTwelve p) : w < 16 := by
  unfold muNegOneTwelve at hw
  exact List.mem_range.mp (List.mem_of_mem_filter hw)

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)
  [DecidableEq (G.induce c.supp).ConnectedComponent]

section Service

variable (u v : ZMod 8 → c.supp) (uTri vTri : Bool)

/-- The owner vertex of a pair-member owner is adjacent to the coded
target. -/
theorem muNegOne_ownerVertex_adj_target
    {f : Fin 80} {tf : V}
    (htf : MuNegOneOwnerVertex G c u v uTri vTri f tf)
    {w : Nat}
    (hpm : muNegOnePairMem (muNegOneOwnerAt uTri vTri f) w = true) :
    G.Adj tf (muNegOneCodeVertex G c u v w) := by
  rcases (muNegOnePairMem_iff _ w).mp hpm with h | h
  · rw [← h]
    exact htf.2.1.symm
  · rw [← h]
    exact htf.2.2.symm

/-- **Service existence** for the concrete relations. -/
theorem muNegOne_service_exists_graph
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hmodeu : if uTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) v) :
    ∀ aa, aa < 80 →
      muNegOneOwnerActive (muNegOneDGraph G c u v) aa = true →
      ∀ w ∈ muNegOneTwelve ((muNegOneOwners uTri vTri)[aa]!),
        ∃ bb, bb < 80 ∧ bb ≠ aa ∧
          muNegOnePairMem ((muNegOneOwners uTri vTri)[bb]!) w = true ∧
          (min aa bb, max aa bb) ∈ muNegOneHitPairs uTri vTri ∧
          muNegOneXGraph G c u v uTri vTri (min aa bb) (max aa bb) = true := by
  intro aa haa hact w hw
  have hw16 : w < 16 := muNegOneTwelve_mem_lt _ hw
  have hcont : (muNegOneTwelve
      (muNegOneOwnerAt uTri vTri ⟨aa, haa⟩)).contains w = true := by
    rw [List.contains_eq_mem]
    exact decide_eq_true hw
  obtain ⟨te, hte, _⟩ := muNegOne_ownerVertex_of_active G c u v uTri vTri
    hfree hmodeu hmodev (e := ⟨aa, haa⟩) hact
  obtain ⟨f, hfne, tf, htf, hadj, hpm⟩ := muNegOne_server_classification
    G c hfree hreg hcard hc a b hab u v huinj hvinj hurange hvrange
    hu hv uTri vTri hmodeu hmodev hte hw16 hcont
  refine ⟨f.val, f.2, ?_, hpm, ?_, ?_⟩
  · intro h
    exact hfne (Fin.ext h)
  · rcases Nat.lt_or_ge aa f.val with hlt | hge
    · rw [Nat.min_eq_left (Nat.le_of_lt hlt),
        Nat.max_eq_right (Nat.le_of_lt hlt)]
      exact mem_muNegOneHitPairs_of_ownerVertices_adj G c u v uTri vTri
        hfree a b hab huinj hvinj hurange hvrange hu hv
        (e := ⟨aa, haa⟩) (f := f) hlt hte htf hadj
    · have hlt : f.val < aa := by
        have hne : f.val ≠ aa := fun h => hfne (Fin.ext h)
        omega
      rw [Nat.min_eq_right (Nat.le_of_lt hlt),
        Nat.max_eq_left (Nat.le_of_lt hlt)]
      exact mem_muNegOneHitPairs_of_ownerVertices_adj G c u v uTri vTri
        hfree a b hab huinj hvinj hurange hvrange hu hv
        (e := f) (f := ⟨aa, haa⟩) hlt htf hte hadj.symm
  · rcases Nat.lt_or_ge aa f.val with hlt | hge
    · rw [Nat.min_eq_left (Nat.le_of_lt hlt),
        Nat.max_eq_right (Nat.le_of_lt hlt)]
      rw [muNegOneXGraph_true_iff]
      exact ⟨haa, f.2, te, tf, hte, htf, hadj⟩
    · have hlt : f.val < aa := by
        have hne : f.val ≠ aa := fun h => hfne (Fin.ext h)
        omega
      rw [Nat.min_eq_right (Nat.le_of_lt hlt),
        Nat.max_eq_left (Nat.le_of_lt hlt)]
      rw [muNegOneXGraph_true_iff]
      exact ⟨f.2, haa, tf, te, htf, hte, hadj.symm⟩

/-- Extract an adjacency between the owner vertices of the two indices
of a true hit variable, oriented to the given order. -/
theorem muNegOneXGraph_extract
    (hfree : ¬ containsC4 V G)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    {aa bb : Nat} (haa : aa < 80) (hbb : bb < 80)
    (hX : muNegOneXGraph G c u v uTri vTri (min aa bb) (max aa bb) = true)
    {ta : V}
    (hta : MuNegOneOwnerVertex G c u v uTri vTri ⟨aa, haa⟩ ta) :
    ∃ tb : V, MuNegOneOwnerVertex G c u v uTri vTri ⟨bb, hbb⟩ tb ∧
      G.Adj ta tb := by
  rw [muNegOneXGraph_true_iff] at hX
  obtain ⟨h1, h2, t1, t2, ht1, ht2, hadj⟩ := hX
  rcases Nat.le_total aa bb with hle | hle
  · have e1 : (⟨min aa bb, h1⟩ : Fin 80) = ⟨aa, haa⟩ :=
      Fin.ext (Nat.min_eq_left hle)
    have e2 : (⟨max aa bb, h2⟩ : Fin 80) = ⟨bb, hbb⟩ :=
      Fin.ext (Nat.max_eq_right hle)
    rw [e1] at ht1
    rw [e2] at ht2
    have : t1 = ta := muNegOneOwnerVertex_unique G c u v uTri vTri hfree
      a b hab huinj hvinj hurange hvrange _ ht1 hta
    subst this
    exact ⟨t2, ht2, hadj⟩
  · have e1 : (⟨min aa bb, h1⟩ : Fin 80) = ⟨bb, hbb⟩ :=
      Fin.ext (Nat.min_eq_right hle)
    have e2 : (⟨max aa bb, h2⟩ : Fin 80) = ⟨aa, haa⟩ :=
      Fin.ext (Nat.max_eq_left hle)
    rw [e1] at ht1
    rw [e2] at ht2
    have : t2 = ta := muNegOneOwnerVertex_unique G c u v uTri vTri hfree
      a b hab huinj hvinj hurange hvrange _ ht2 hta
    subst this
    exact ⟨t1, ht1, hadj.symm⟩

/-- **Service uniqueness** for the concrete relations. -/
theorem muNegOne_service_unique_graph
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8) (hcard : Fintype.card V = 8 * 8)
    (hc : c.supp.ncard = 8 * 2)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hurange : Set.range u = a.supp) (hvrange : Set.range v = b.supp)
    (hmodeu : if uTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) u
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) u)
    (hmodev : if vTri then
        MuNegOneOneFourTriangleShoreMode (exteriorPairGraph G c.supp) v
      else MuNegOneOneFourTfShoreMode (exteriorPairGraph G c.supp) v) :
    ∀ aa, aa < 80 →
      muNegOneOwnerActive (muNegOneDGraph G c u v) aa = true →
      ∀ w ∈ muNegOneTwelve ((muNegOneOwners uTri vTri)[aa]!),
      ∀ bb cc, bb < 80 → bb ≠ aa →
        muNegOnePairMem ((muNegOneOwners uTri vTri)[bb]!) w = true →
        (min aa bb, max aa bb) ∈ muNegOneHitPairs uTri vTri →
        muNegOneXGraph G c u v uTri vTri (min aa bb) (max aa bb) = true →
        cc < 80 → cc ≠ aa →
        muNegOnePairMem ((muNegOneOwners uTri vTri)[cc]!) w = true →
        (min aa cc, max aa cc) ∈ muNegOneHitPairs uTri vTri →
        muNegOneXGraph G c u v uTri vTri (min aa cc) (max aa cc) = true →
        bb = cc := by
  intro aa haa hact w hw bb cc hbb hbne hpmb _ hXb hcc hcne hpmc _ hXc
  have hw16 : w < 16 := muNegOneTwelve_mem_lt _ hw
  obtain ⟨te, hte, _⟩ := muNegOne_ownerVertex_of_active G c u v uTri vTri
    hfree hmodeu hmodev (e := ⟨aa, haa⟩) hact
  obtain ⟨tb, htb, hteb⟩ := muNegOneXGraph_extract G c u v uTri vTri
    hfree a b hab huinj hvinj hurange hvrange haa hbb hXb hte
  obtain ⟨tc, htc, htec⟩ := muNegOneXGraph_extract G c u v uTri vTri
    hfree a b hab huinj hvinj hurange hvrange haa hcc hXc hte
  -- both servers are common neighbors of the source vertex and target.
  have hbw : G.Adj tb (muNegOneCodeVertex G c u v w) :=
    muNegOne_ownerVertex_adj_target G c u v uTri vTri htb hpmb
  have hcw : G.Adj tc (muNegOneCodeVertex G c u v w) :=
    muNegOne_ownerVertex_adj_target G c u v uTri vTri htc hpmc
  have hne : te ≠ muNegOneCodeVertex G c u v w := by
    intro h
    apply hte.1
    rw [h]
    exact muNegOneCodeVertex_mem_supp G c u v w
  have hbc : tb = tc := commonServer_unique G hfree hne
    hteb hbw.symm htec hcw.symm
  subst hbc
  have := muNegOneOwnerVertex_inj G c u v uTri vTri hfree
    (q := 8) (by omega) hreg hcard hc a b hab huinj hvinj
    hurange hvrange htb htc
  exact congrArg Fin.val this

end Service

end

end Erdos85

#print axioms Erdos85.muNegOne_service_exists_graph
#print axioms Erdos85.muNegOne_service_unique_graph
