import Proofs.Erdos85CubicResidualRowExcessBridge
import Proofs.Erdos85EdgeIndexedServiceCubicEightCycleCensus

/-! # Cubic fiber bounds for same-shore nonantipodal targets -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def eightCycleSingleEndpointCubeValue (k i : ZMod 8) : ℕ :=
  if i = k - 1 ∨ i = k + 1 then 3
  else if i = k - 3 ∨ i = k + 3 then 1 else 0

def eightCycleEndpointPairCubeValue (k i j : ZMod 8) : ℕ :=
  eightCycleSingleEndpointCubeValue k i +
    eightCycleSingleEndpointCubeValue k j

def eightCycleEndpointPairNeighborCount (k i j : ZMod 8) : ℕ :=
  (if i = k - 1 ∨ i = k + 1 then 1 else 0) +
    (if j = k - 1 ∨ j = k + 1 then 1 else 0)

def h305SameShoreCubicBudget25Coordinates (i j : ZMod 8) :
    Finset (ZMod 8) :=
  Finset.univ.filter fun k ↦ eightCycleEndpointPairCubeValue k i j = 3

def h305SameShoreCubicBudget27Coordinates (i j : ZMod 8) :
    Finset (ZMod 8) :=
  Finset.univ.filter fun k ↦ eightCycleEndpointPairCubeValue k i j = 1

set_option maxRecDepth 100000 in
theorem h305SameShore_nonantipodal_coordinate_finiteFacts :
    ∀ i j : ZMod 8,
      (j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7) →
      (h305SameShoreCubicBudget25Coordinates i j).card = 4 ∧
      (h305SameShoreCubicBudget27Coordinates i j).card = 4 ∧
      Disjoint (h305SameShoreCubicBudget25Coordinates i j)
        (h305SameShoreCubicBudget27Coordinates i j) ∧
      h305SameShoreCubicBudget25Coordinates i j ∪
        h305SameShoreCubicBudget27Coordinates i j = Finset.univ := by
  native_decide

set_option maxRecDepth 100000 in
theorem h305SameShore_nonantipodal_value_neighbor_finiteFacts :
    ∀ i j : ZMod 8,
      (j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7) →
      i ≠ j ∧ ∀ k : ZMod 8,
        (eightCycleEndpointPairCubeValue k i j = 3 →
          eightCycleEndpointPairNeighborCount k i j = 1) ∧
        (eightCycleEndpointPairCubeValue k i j = 1 →
          eightCycleEndpointPairNeighborCount k i j = 0) := by
  native_decide

def h305SameShoreCubicBudget25Vertices
    {V : Type*} [DecidableEq V]
    (u : ZMod 8 → V) (i j : ZMod 8) : Finset V :=
  (h305SameShoreCubicBudget25Coordinates i j).image u

def h305SameShoreCubicBudget16Vertices
    {V : Type*} [DecidableEq V]
    (u : ZMod 8 → V) (i j : ZMod 8) : Finset V :=
  (h305SameShoreCubicBudget27Coordinates i j).image u

def h305SameShoreCubicBudget17Vertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (v : ZMod 8 → V) : Finset V :=
  Finset.univ.image v

/-- For a nonantipodal same-shore target, the four coordinates receiving
internal cubic mass three, the four receiving mass one, and all eight
coordinates on the other shore form the required `4/4/8` partition. -/
theorem h305SameShore_nonantipodal_cubicCoordinatePartition
    {V : Type*} [Fintype V] [DecidableEq V]
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v) (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (i j : ZMod 8)
    (hodd : j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7) :
    let X25 := h305SameShoreCubicBudget25Vertices u i j
    let X16 := h305SameShoreCubicBudget16Vertices u i j
    let X17 := h305SameShoreCubicBudget17Vertices v
    X25.card = 4 ∧ X16.card = 4 ∧ X17.card = 8 ∧
      Disjoint X25 X16 ∧ Disjoint X25 X17 ∧ Disjoint X16 X17 ∧
      X25 ∪ X16 ∪ X17 = Finset.univ := by
  classical
  dsimp only
  obtain ⟨h25c, h16c, hdcoord, hcoordcover⟩ :=
    h305SameShore_nonantipodal_coordinate_finiteFacts i j hodd
  have h25card : (h305SameShoreCubicBudget25Vertices u i j).card = 4 := by
    rw [h305SameShoreCubicBudget25Vertices,
      Finset.card_image_of_injective _ huinj, h25c]
  have h16card : (h305SameShoreCubicBudget16Vertices u i j).card = 4 := by
    rw [h305SameShoreCubicBudget16Vertices,
      Finset.card_image_of_injective _ huinj, h16c]
  have h17card : (h305SameShoreCubicBudget17Vertices v).card = 8 := by
    rw [h305SameShoreCubicBudget17Vertices,
      Finset.card_image_of_injective _ hvinj]
    simp
  have h2516 : Disjoint (h305SameShoreCubicBudget25Vertices u i j)
      (h305SameShoreCubicBudget16Vertices u i j) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨l, hl, hkl⟩
    exact Finset.disjoint_left.mp hdcoord hk (huinj hkl ▸ hl)
  have h2517 : Disjoint (h305SameShoreCubicBudget25Vertices u i j)
      (h305SameShoreCubicBudget17Vertices v) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨l, hl, h⟩
    exact hdisj k l h.symm
  have h1617 : Disjoint (h305SameShoreCubicBudget16Vertices u i j)
      (h305SameShoreCubicBudget17Vertices v) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨l, hl, h⟩
    exact hdisj k l h.symm
  have hfull : h305SameShoreCubicBudget25Vertices u i j ∪
      h305SameShoreCubicBudget16Vertices u i j ∪
      h305SameShoreCubicBudget17Vertices v = Finset.univ := by
    ext x
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    rcases hcover x with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hk : k ∈ h305SameShoreCubicBudget25Coordinates i j ∪
          h305SameShoreCubicBudget27Coordinates i j := by
        rw [hcoordcover]
        simp
      rcases Finset.mem_union.mp hk with hk | hk
      · exact Or.inl (Or.inl (Finset.mem_image.mpr ⟨k, hk, rfl⟩))
      · exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨k, hk, rfl⟩))
    · exact Or.inr (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩)
  exact ⟨h25card, h16card, h17card, h2516, h2517, h1617, hfull⟩

theorem internalEndpointNeighbor_card_sameShore
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j k : ZMod 8) (hij : i ≠ j)
    (ha : a.1.toFinset = {u i, u j}) :
    (internalEndpointNeighborFinset H R (u k) a).card =
      eightCycleEndpointPairNeighborCount k i j := by
  classical
  have hi : H.Adj (u k) (u i) ↔ i = k - 1 ∨ i = k + 1 := by
    rw [← H.mem_neighborFinset, hu k]
    simp [huinj.eq_iff]
  have hj : H.Adj (u k) (u j) ↔ j = k - 1 ∨ j = k + 1 := by
    rw [← H.mem_neighborFinset, hu k]
    simp [huinj.eq_iff]
  have huij : u i ≠ u j := huinj.ne hij
  unfold internalEndpointNeighborFinset eightCycleEndpointPairNeighborCount
  rw [ha]
  rw [Finset.card_filter, Finset.sum_pair huij]
  simp only [← hi, ← hj]

/-- On the target shore, internal cube values three and one give the exact
service budgets and residual-neighbor counts used by the sharp minima. -/
theorem sameShore_nonantipodal_cubicBudget_neighborCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hCreg : ∀ b, Cedge.degree b = 6)
    (u : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (a : R.edgeFinset) (i j k : ZMod 8)
    (hodd : j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7)
    (ha : a.1.toFinset = {u i, u j}) :
    (eightCycleEndpointPairCubeValue k i j = 3 →
      incidentServiceCubicWalkMass R Cedge (u k) a = 25 ∧
      (incidentServiceNeighborFiber R Cedge (u k) a).card = 0) ∧
    (eightCycleEndpointPairCubeValue k i j = 1 →
      incidentServiceCubicWalkMass R Cedge (u k) a = 27 ∧
      (incidentServiceNeighborFiber R Cedge (u k) a).card = 1) := by
  have hij := (h305SameShore_nonantipodal_value_neighbor_finiteFacts
    i j hodd).1
  have hvalues := (h305SameShore_nonantipodal_value_neighbor_finiteFacts
    i j hodd).2 k
  have hcensus := incidentServiceCubicWalkMass_add_eightCycle_values_eq_twentyEight
    H R Cedge hservice hHreg hCreg u huinj hu k i j hij a ha
  change incidentServiceCubicWalkMass R Cedge (u k) a +
    eightCycleEndpointPairCubeValue k i j = 28 at hcensus
  have hlaw :=
    internalEndpointNeighbor_card_add_incidentServiceNeighborFiber_card
      H R Cedge hservice (u k) a
  rw [internalEndpointNeighbor_card_sameShore H R u huinj hu a i j k hij ha]
    at hlaw
  constructor
  · intro h3
    have hn := hvalues.1 h3
    omega
  · intro h1
    have hn := hvalues.2 h1
    omega

theorem sameShore_otherShore_cubicBudget_neighborCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hzeroVU : ∀ k l,
      Fintype.card {p : H.Walk (v l) (u k) | p.length = 3} = 0)
    (a : R.edgeFinset) (i j l : ZMod 8) (hij : i ≠ j)
    (ha : a.1.toFinset = {u i, u j}) :
    incidentServiceCubicWalkMass R Cedge (v l) a = 28 ∧
      (incidentServiceNeighborFiber R Cedge (v l) a).card = 1 := by
  classical
  have huij : u i ≠ u j := huinj.ne hij
  have hinternal : internalEndpointCubicWalkMass H R (v l) a = 0 := by
    unfold internalEndpointCubicWalkMass
    rw [ha, ← Finset.sum_filter]
    have hfilter : (Finset.univ.filter fun x : V ↦
        x ∈ ({u i, u j} : Finset V)) = {u i, u j} := by
      ext x
      simp
    change (∑ x ∈ Finset.univ.filter (fun x : V ↦
        x ∈ ({u i, u j} : Finset V)),
          Fintype.card {p : H.Walk (v l) x | p.length = 3}) = 0
    rw [hfilter, Finset.sum_pair huij, hzeroVU i l, hzeroVU j l]
  have hni : ¬ H.Adj (v l) (u i) := by
    intro h
    have hm := (H.mem_neighborFinset (v l) (u i)).mpr h
    rw [hv l] at hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · exact hdisj i (l - 1) hm
    · exact hdisj i (l + 1) (Finset.mem_singleton.mp hm)
  have hnj : ¬ H.Adj (v l) (u j) := by
    intro h
    have hm := (H.mem_neighborFinset (v l) (u j)).mpr h
    rw [hv l] at hm
    rcases Finset.mem_insert.mp hm with hm | hm
    · exact hdisj j (l - 1) hm
    · exact hdisj j (l + 1) (Finset.mem_singleton.mp hm)
  have hneighbor :
      (internalEndpointNeighborFinset H R (v l) a).card = 0 := by
    unfold internalEndpointNeighborFinset
    rw [ha, Finset.card_filter, Finset.sum_pair huij]
    simp [hni, hnj]
  have hcensus := edgeIndexedService_cubicWalkCensus
    H R Cedge hservice hHreg hCreg (v l) a
  rw [hinternal] at hcensus
  have hlaw :=
    internalEndpointNeighbor_card_add_incidentServiceNeighborFiber_card
      H R Cedge hservice (v l) a
  rw [hneighbor] at hlaw
  omega

/-- Pointwise `105/52/59` bounds for a same-shore nonantipodal target. -/
theorem h305_sameShore_nonantipodal_cubicResidualFiber_pointwise_bounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hzeroVU : ∀ k l,
      Fintype.card {p : H.Walk (v l) (u k) | p.length = 3} = 0)
    (a : R.edgeFinset) (i j : ZMod 8)
    (hodd : j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7)
    (ha : a.1.toFinset = {u i, u j}) :
    let X25 := h305SameShoreCubicBudget25Vertices u i j
    let X16 := h305SameShoreCubicBudget16Vertices u i j
    let X17 := h305SameShoreCubicBudget17Vertices v
    (∀ x ∈ X25, 105 ≤ ∑ b ∈ cubicResidualFiber R Cedge x a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) ∧
    (∀ x ∈ X16, 52 ≤ ∑ b ∈ cubicResidualFiber R Cedge x a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) ∧
    (∀ x ∈ X17, 59 ≤ ∑ b ∈ cubicResidualFiber R Cedge x a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2) := by
  classical
  dsimp only
  have hij := (h305SameShore_nonantipodal_value_neighbor_finiteFacts
    i j hodd).1
  constructor
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
    have h3 := (Finset.mem_filter.mp hk).2
    obtain ⟨hmass, hnbr⟩ :=
      (sameShore_nonantipodal_cubicBudget_neighborCard
        H R Cedge hservice hHreg hCreg u huinj hu a i j k hodd ha).1 h3
    exact cubicResidualFiber_squareMass_ge_105_of_budget25
      R Cedge hfree hRreg hCreg (u k) a hmass hnbr
  · constructor
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
      have h1 := (Finset.mem_filter.mp hk).2
      obtain ⟨hmass, hnbr⟩ :=
        (sameShore_nonantipodal_cubicBudget_neighborCard
          H R Cedge hservice hHreg hCreg u huinj hu a i j k hodd ha).2 h1
      exact cubicResidualFiber_squareMass_ge_52_of_budget27_neighborOne
        R Cedge hfree hRreg hCreg (u k) a hmass hnbr
    · intro x hx
      rcases Finset.mem_image.mp hx with ⟨l, hl, rfl⟩
      obtain ⟨hmass, hnbr⟩ := sameShore_otherShore_cubicBudget_neighborCard
        H R Cedge hservice hHreg hCreg u v huinj hv hdisj hzeroVU
          a i j l hij ha
      exact cubicResidualFiber_squareMass_ge_59_of_budget28_neighborOne
        R Cedge hfree hRreg hCreg (v l) a hmass hnbr

theorem h305_sameShore_nonantipodal_cubicResidualEdge_squareMass_ge_550
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (hzeroVU : ∀ k l,
      Fintype.card {p : H.Walk (v l) (u k) | p.length = 3} = 0)
    (a : R.edgeFinset) (i j : ZMod 8)
    (hodd : j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7)
    (ha : a.1.toFinset = {u i, u j}) :
    550 ≤ ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  let X25 := h305SameShoreCubicBudget25Vertices u i j
  let X16 := h305SameShoreCubicBudget16Vertices u i j
  let X17 := h305SameShoreCubicBudget17Vertices v
  obtain ⟨h25card, h16card, h17card, h2516, h2517, h1617, hfull⟩ :=
    h305SameShore_nonantipodal_cubicCoordinatePartition
      u v huinj hvinj hdisj hcover i j hodd
  obtain ⟨h25, h16, h17⟩ :=
    h305_sameShore_nonantipodal_cubicResidualFiber_pointwise_bounds
      H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hu hv hdisj
        hzeroVU a i j hodd ha
  exact cubicResidualEdge_squareMass_ge_550_of_partition
    R Cedge a X25 X16 X17 h25card h16card h17card h2516 h2517 h1617
      hfull h25 h16 h17

/-- Same-shore nonantipodal row bound with cross-walk vanishing discharged
from the actual two distinct connected components. -/
theorem h305_sameShore_nonantipodal_cubicResidualEdge_squareMass_ge_550_of_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hHreg : ∀ x, H.degree x = 2) (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (A B : H.ConnectedComponent) (hAB : A ≠ B)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hurange : Set.range u = A.supp) (hvrange : Set.range v = B.supp)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (a : R.edgeFinset) (i j : ZMod 8)
    (hodd : j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7)
    (ha : a.1.toFinset = {u i, u j}) :
    550 ≤ ∑ b ∈ cubicResidualEdgeFinset R Cedge a,
      (residualFiberCubicWalkCount R Cedge a b) ^ 2 := by
  apply h305_sameShore_nonantipodal_cubicResidualEdge_squareMass_ge_550
    H R Cedge hservice hfree hHreg hRreg hCreg u v huinj hvinj hu hv
      hdisj hcover
  · exact fun k l ↦ lengthThreeWalk_card_eq_zero_of_distinct_components
      H B A hAB.symm v u hvrange hurange l k
  · exact hodd
  · exact ha

/-- Therefore every same-shore nonantipodal target contributes at least four
units to the standard cubic histogram excess. -/
theorem h305_sameShore_nonantipodal_cubicRowHistogramExcess_ge_four_of_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hfree : ¬ containsC4 R.edgeFinset Cedge)
    (hcard : Fintype.card R.edgeFinset = 48)
    (hHreg : ∀ x, H.degree x = 2) (hRreg : ∀ x, R.degree x = 6)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (A B : H.ConnectedComponent) (hAB : A ≠ B)
    (u v : ZMod 8 → V) (huinj : Function.Injective u)
    (hvinj : Function.Injective v)
    (hurange : Set.range u = A.supp) (hvrange : Set.range v = B.supp)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, H.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (a : R.edgeFinset) (i j : ZMod 8)
    (hodd : j - i = 1 ∨ j - i = 3 ∨ j - i = 5 ∨ j - i = 7)
    (ha : a.1.toFinset = {u i, u j}) :
    4 ≤ cubicRowHistogramExcess Cedge a := by
  apply cubicRowHistogramExcess_ge_four_of_residual_squareMass_ge_550
    R Cedge hfree hcard hCreg a
  exact h305_sameShore_nonantipodal_cubicResidualEdge_squareMass_ge_550_of_components
    H R Cedge hservice hfree hHreg hRreg hCreg A B hAB u v huinj hvinj
      hurange hvrange hu hv hdisj hcover a i j hodd ha

end

end Erdos85

#print axioms Erdos85.h305SameShore_nonantipodal_coordinate_finiteFacts
#print axioms Erdos85.h305SameShore_nonantipodal_cubicCoordinatePartition
#print axioms
  Erdos85.h305_sameShore_nonantipodal_cubicResidualEdge_squareMass_ge_550
#print axioms
  Erdos85.h305_sameShore_nonantipodal_cubicRowHistogramExcess_ge_four_of_components
