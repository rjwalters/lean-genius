import Proofs.Erdos85TriangleProjection
import Proofs.Erdos85SecondOrderEvenDefect

/-!
# The adjacency polynomial of a union of triangles

A 2-regular graph whose two neighbors at every vertex are adjacent is a
disjoint union of triangles.  Its adjacency matrix satisfies `D²=D+2I`.
This is the graph-specific input for the canonical triangle projection.
-/

namespace Erdos85

open SimpleGraph

/-- Local formulation of being a disjoint union of triangles. -/
def IsLocallyTriangleUnion {V : Type*} (D : SimpleGraph V) : Prop :=
  ∀ x y z : V, D.Adj x y → D.Adj x z → y ≠ z → D.Adj y z

/-- A 2-factor all of whose connected components have order three is locally
a union of triangles. -/
theorem locallyTriangleUnion_of_component_order_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ x : V, D.degree x = 2)
    (hthree : ∀ c : D.ConnectedComponent, c.supp.ncard = 3) :
    IsLocallyTriangleUnion D := by
  intro x y z hxy hxz hyz
  have hxy_ne : x ≠ y := fun h => by
    subst y
    exact D.loopless.irrefl x hxy
  have hxz_ne : x ≠ z := fun h => by
    subst z
    exact D.loopless.irrefl x hxz
  let c := D.connectedComponentMk x
  have hxmem : x ∈ c.supp := by
    simp [c, SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hymem : y ∈ c.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  have hzmem : z ∈ c.supp := by
    rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
    exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm
  have hsub : ({x, y, z} : Set V) ⊆ c.supp := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · exact hxmem
    · exact hymem
    · exact hzmem
  have htriplecard : ({x, y, z} : Set V).ncard = 3 := by
    simp [hxy_ne, hxz_ne, hyz]
  have heq : ({x, y, z} : Set V) = c.supp := by
    apply Set.eq_of_subset_of_ncard_le hsub
    · rw [hthree c, htriplecard]
  have hneighbors : D.neighborFinset y ⊆ ({x, z} : Finset V) := by
    intro w hw
    have hyw : D.Adj y w := (D.mem_neighborFinset y w).mp hw
    have hwmem : w ∈ c.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      calc
        D.connectedComponentMk w = D.connectedComponentMk y :=
          (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hyw).symm
        _ = c := (SimpleGraph.ConnectedComponent.mem_supp_iff c y).mp hymem
    have hwtriple : w = x ∨ w = y ∨ w = z := by
      rw [← heq] at hwmem
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hwmem
    have hwy : w ≠ y := fun h => by
      subst w
      exact D.loopless.irrefl y hyw
    rcases hwtriple with rfl | rfl | rfl
    · simp
    · exact (hwy rfl).elim
    · simp
  have hneighborEq : D.neighborFinset y = ({x, z} : Finset V) := by
    apply Finset.eq_of_subset_of_card_le hneighbors
    rw [D.card_neighborFinset_eq_degree, hreg]
    simp [hxz_ne]
  have : z ∈ D.neighborFinset y := by
    rw [hneighborEq]
    simp
  exact (D.mem_neighborFinset y z).mp this

/-- In a 2-regular graph whose components have order three, two vertices are
adjacent exactly when they are distinct and lie in the same component. -/
theorem adj_iff_ne_and_connectedComponentMk_eq_of_order_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ x : V, D.degree x = 2)
    (hthree : ∀ c : D.ConnectedComponent, c.supp.ncard = 3)
    {x y : V} :
    D.Adj x y ↔ x ≠ y ∧ D.connectedComponentMk x = D.connectedComponentMk y := by
  let c := D.connectedComponentMk x
  let cs : Finset V := (Set.toFinite c.supp).toFinset
  have hxmem : x ∈ cs := by
    simp [cs, c, SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hcardcs : cs.card = 3 := by
    calc
      cs.card = c.supp.ncard := by
        exact (Set.ncard_eq_toFinset_card c.supp (Set.toFinite c.supp)).symm
      _ = 3 := hthree c
  have hsub : D.neighborFinset x ⊆ cs.erase x := by
    intro z hz
    have hxz : D.Adj x z := (D.mem_neighborFinset x z).mp hz
    have hzmem : z ∈ c.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      exact (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm
    exact Finset.mem_erase.mpr ⟨(D.ne_of_adj hxz).symm, by simpa [cs] using hzmem⟩
  have hneighbors : D.neighborFinset x = cs.erase x := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [D.card_neighborFinset_eq_degree, hreg,
      Finset.card_erase_of_mem hxmem, hcardcs]
  constructor
  · intro hxy
    exact ⟨D.ne_of_adj hxy,
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy⟩
  · rintro ⟨hxy, hcomp⟩
    apply (D.mem_neighborFinset x y).mp
    rw [hneighbors]
    apply Finset.mem_erase.mpr
    refine ⟨hxy.symm, ?_⟩
    have hymem : y ∈ c.supp := by
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      simpa [c] using hcomp.symm
    simpa [cs] using hymem

theorem card_common_eq_one_of_locallyTriangleUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ x : V, D.degree x = 2)
    (htri : IsLocallyTriangleUnion D)
    {x y : V} (hxy : D.Adj x y) :
    (D.neighborFinset x ∩ D.neighborFinset y).card = 1 := by
  have hset : D.neighborFinset x ∩ D.neighborFinset y =
      (D.neighborFinset x).erase y := by
    ext z
    constructor
    · intro hz
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz
      have hzy : z ≠ y := by
        intro h
        subst z
        exact D.loopless.irrefl y hz.2
      exact Finset.mem_erase.mpr ⟨hzy, (D.mem_neighborFinset x z).mpr hz.1⟩
    · intro hz
      simp only [Finset.mem_erase, Finset.mem_inter,
        SimpleGraph.mem_neighborFinset] at hz ⊢
      refine ⟨hz.2, ?_⟩
      exact htri x y z hxy hz.2 hz.1.symm
  rw [hset, Finset.card_erase_of_mem]
  · rw [D.card_neighborFinset_eq_degree, hreg]
  · exact (D.mem_neighborFinset x y).mpr hxy

theorem card_common_eq_zero_of_not_adj_locallyTriangleUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (htri : IsLocallyTriangleUnion D)
    {x y : V} (hxy : x ≠ y) (hnadj : ¬D.Adj x y) :
    (D.neighborFinset x ∩ D.neighborFinset y).card = 0 := by
  rw [Finset.card_eq_zero]
  ext z
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
    Finset.notMem_empty, iff_false]
  rintro ⟨hxz, hyz⟩
  exact hnadj (htri z x y hxz.symm hyz.symm hxy)

/-- The adjacency operator of a locally triangular 2-factor obeys the
triangle polynomial `D²=D+2I`. -/
theorem adjMatrix_sq_eq_add_two_of_locallyTriangleUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ x : V, D.degree x = 2)
    (htri : IsLocallyTriangleUnion D) :
    D.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ + Matrix.diagonal (fun _ : V => (2 : ℤ)) := by
  ext x y
  by_cases hxy : x = y
  · subst y
    rw [D.adjMatrix_mul_self_apply_self, hreg]
    simp [Matrix.add_apply, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply]
  · rw [adjMatrix_sq_apply_eq_card_common]
    by_cases hadj : D.Adj x y
    · rw [card_common_eq_one_of_locallyTriangleUnion D hreg htri hadj]
      simp [Matrix.add_apply, Matrix.diagonal_apply,
        SimpleGraph.adjMatrix_apply, hadj, hxy]
    · rw [card_common_eq_zero_of_not_adj_locallyTriangleUnion
          D htri hxy hadj]
      simp [Matrix.add_apply, Matrix.diagonal_apply,
        SimpleGraph.adjMatrix_apply, hadj, hxy]

/-- Rational form used by the spectral projection. -/
theorem adjMatrix_sq_eq_add_two_of_locallyTriangleUnion_rat
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ x : V, D.degree x = 2)
    (htri : IsLocallyTriangleUnion D) :
    D.adjMatrix ℚ * D.adjMatrix ℚ =
      D.adjMatrix ℚ + Matrix.diagonal (fun _ : V => (2 : ℚ)) := by
  ext x y
  have hsquare :
      (D.adjMatrix ℚ * D.adjMatrix ℚ) x y =
        ((D.neighborFinset x ∩ D.neighborFinset y).card : ℚ) := by
    rw [D.adjMatrix_mul_apply]
    simp only [SimpleGraph.adjMatrix_apply]
    rw [Finset.sum_boole]
    have hfilt : (D.neighborFinset x).filter (fun z => D.Adj z y) =
        D.neighborFinset x ∩ D.neighborFinset y := by
      ext z
      simp [SimpleGraph.mem_neighborFinset, D.adj_comm]
    rw [hfilt]
  rw [hsquare]
  by_cases hxy : x = y
  · subst y
    have hcard : (D.neighborFinset x ∩ D.neighborFinset x).card = 2 := by
      simp [D.card_neighborFinset_eq_degree, hreg]
    rw [hcard]
    simp [Matrix.add_apply, Matrix.diagonal_apply,
      SimpleGraph.adjMatrix_apply]
  · by_cases hadj : D.Adj x y
    · rw [card_common_eq_one_of_locallyTriangleUnion D hreg htri hadj]
      simp [Matrix.add_apply, Matrix.diagonal_apply,
        SimpleGraph.adjMatrix_apply, hadj, hxy]
    · rw [card_common_eq_zero_of_not_adj_locallyTriangleUnion
          D htri hxy hadj]
      simp [Matrix.add_apply, Matrix.diagonal_apply,
        SimpleGraph.adjMatrix_apply, hadj, hxy]

/-- Endomorphism form of the triangle polynomial, ready for
`trianglePlusProjection`. -/
theorem adjMatrix_toLin_sq_eq_add_two_of_locallyTriangleUnion
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hreg : ∀ x : V, D.degree x = 2)
    (htri : IsLocallyTriangleUnion D) :
    (D.adjMatrix ℚ).toLin' * (D.adjMatrix ℚ).toLin' =
      (D.adjMatrix ℚ).toLin' + (2 : ℚ) • LinearMap.id := by
  have hm := adjMatrix_sq_eq_add_two_of_locallyTriangleUnion_rat D hreg htri
  have hdiag : Matrix.diagonal (fun _ : V => (2 : ℚ)) =
      (2 : ℚ) • (1 : Matrix V V ℚ) := by
    ext x y
    by_cases hxy : x = y
    · subst y
      simp [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
    · simp [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply, hxy]
  rw [hdiag] at hm
  have ht := congrArg Matrix.toLin' hm
  rw [Module.End.mul_eq_comp]
  simpa only [Matrix.toLin'_mul, map_add, map_smul,
    Matrix.toLin'_one] using ht

/-- On 33 vertices the component-orthogonal kernel of the triangle
projection has dimension 22.  The proof uses the trace of the idempotent
projection, avoiding a separate enumeration of its eleven components. -/
theorem finrank_trianglePlusProjection_ker_eq_twentyTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hcard : Fintype.card V = 33)
    (hreg : ∀ x : V, D.degree x = 2)
    (htri : IsLocallyTriangleUnion D) :
    Module.finrank ℚ
      (LinearMap.ker (trianglePlusProjection (D.adjMatrix ℚ).toLin')) = 22 := by
  let T : (V → ℚ) →ₗ[ℚ] (V → ℚ) := (D.adjMatrix ℚ).toLin'
  let P := trianglePlusProjection T
  have hT : T * T = T + (2 : ℚ) • LinearMap.id :=
    adjMatrix_toLin_sq_eq_add_two_of_locallyTriangleUnion D hreg htri
  have htraceT : LinearMap.trace ℚ (V → ℚ) T = 0 := by
    change LinearMap.trace ℚ (V → ℚ) (D.adjMatrix ℚ).toLin' = 0
    rw [Matrix.trace_toLin'_eq]
    exact SimpleGraph.trace_adjMatrix ℚ D
  have hfinrank : Module.finrank ℚ (V → ℚ) = 33 := by
    rw [Module.finrank_pi_fintype]
    simp [hcard]
  have htraceP : LinearMap.trace ℚ (V → ℚ) P = 11 := by
    simp only [P, trianglePlusProjection]
    rw [map_smul, map_add, htraceT, LinearMap.trace_id, hfinrank]
    norm_num
  have hproj := LinearMap.IsIdempotentElem.isProj_range P
    (trianglePlusProjection_isIdempotent T hT)
  have hrankQ :
      (Module.finrank ℚ (LinearMap.range P) : ℚ) = 11 := by
    rw [← hproj.trace]
    exact htraceP
  have hrank : Module.finrank ℚ (LinearMap.range P) = 11 := by
    exact_mod_cast hrankQ
  have hsum := Submodule.finrank_add_eq_of_isCompl
    (trianglePlusProjection_isCompl T hT)
  change Module.finrank ℚ (LinearMap.range P) +
      Module.finrank ℚ (LinearMap.ker P) =
        Module.finrank ℚ (V → ℚ) at hsum
  have hker : Module.finrank ℚ (LinearMap.ker P) = 22 := by omega
  simpa [P, T] using hker

end Erdos85
