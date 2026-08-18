import Proofs.Erdos85SecondOrderQuotient
import Proofs.Erdos85ConflictRegular
import Proofs.Erdos85OrderSixtyFourComponentComplexGram
import Proofs.Erdos85OrderSixteenPairQuotientArithmetic

/-! # From cycle--pair separation to the component quotient bounds -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Commutation of two graph adjacency matrices descends from `ℂ` to `ℝ`.
This lets the complex H16 Gram calculation feed the real Laplacian quotient
API. -/
theorem adjMatrix_comm_real_of_complex
    {V : Type*} [Fintype V] [DecidableEq V]
    (R H : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel H.Adj]
    (hcomm : R.adjMatrix ℂ * H.adjMatrix ℂ =
      H.adjMatrix ℂ * R.adjMatrix ℂ) :
    R.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * R.adjMatrix ℝ := by
  have hz : R.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * R.adjMatrix ℤ := by
    have hm : (R.adjMatrix ℤ * H.adjMatrix ℤ).map (Int.castRingHom ℂ) =
        (H.adjMatrix ℤ * R.adjMatrix ℤ).map (Int.castRingHom ℂ) := by
      simpa only [Matrix.map_mul, adjMatrix_map_intCast] using hcomm
    ext x y
    apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℂ)))
    simpa using congrFun (congrFun hm x) y
  have hr := congrArg (fun M ↦ M.map (Int.castRingHom ℝ)) hz
  simpa only [Matrix.map_mul, adjMatrix_map_intCast] using hr

/-- In a C4-free two-factor, a commuting pair graph separated from all
two-step conflicts has at most `|c|-3` neighbors inside each cycle component.
The three unavailable vertices are the vertex itself and its two vertices in
the common-neighbor conflict graph. -/
theorem componentQuotientMatrix_diag_add_three_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (R H : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel H.Adj]
    [Fintype H.ConnectedComponent] [DecidableEq H.ConnectedComponent]
    (hfree : ¬ containsC4 V H) (hHreg : ∀ x, H.degree x = 2)
    (hsep : ∀ {x y}, R.Adj x y →
      (H.neighborFinset x ∩ H.neighborFinset y).card = 0)
    (c : H.ConnectedComponent) :
    componentQuotientMatrix R H c c + 3 ≤ c.supp.ncard := by
  classical
  let x := componentRepresentative H c
  let A := componentNeighborFinset R H c x
  let B := (commonNeighborConflict H).neighborFinset x
  have hx : x ∈ c.supp := componentRepresentative_mem H c
  have hAcard : A.card = componentQuotientMatrix R H c c := by
    rfl
  have hBcard : B.card = 2 := by
    dsimp [B]
    rw [degree_commonNeighborConflict_of_regular_c4Free H hfree hHreg x]
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    have hRxy : R.Adj x y := by
      exact (R.mem_neighborFinset x y).mp
        (Finset.mem_filter.mp hyA).1
    have hconf : (commonNeighborConflict H).Adj x y :=
      ((commonNeighborConflict H).mem_neighborFinset x y).mp hyB
    have hnonempty := (commonNeighborConflict_adj_iff H x y).mp hconf |>.2
    rw [Finset.card_eq_zero.mp (hsep hRxy)] at hnonempty
    exact Finset.not_nonempty_empty hnonempty
  have hAsub : A ⊆ c.supp.toFinite.toFinset.erase x := by
    intro y hy
    have hyc : H.connectedComponentMk y = c :=
      (Finset.mem_filter.mp hy).2
    have hySupp : y ∈ c.supp := by
      simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hyc
    have hyx : y ≠ x := by
      intro h
      subst y
      exact R.loopless.irrefl x ((R.mem_neighborFinset x x).mp
        (Finset.mem_filter.mp hy).1)
    simp [hySupp, hyx]
  have hBsub : B ⊆ c.supp.toFinite.toFinset.erase x := by
    intro y hy
    have hconf : (commonNeighborConflict H).Adj x y :=
      ((commonNeighborConflict H).mem_neighborFinset x y).mp hy
    obtain ⟨hxy, hne⟩ := (commonNeighborConflict_adj_iff H x y).mp hconf
    obtain ⟨z, hz⟩ := hne
    obtain ⟨hxz, hyz⟩ := Finset.mem_inter.mp hz
    have hxzAdj : H.Adj x z := (H.mem_neighborFinset x z).mp hxz
    have hyzAdj : H.Adj y z := (H.mem_neighborFinset y z).mp hyz
    have hcompXZ :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxzAdj
    have hcompYZ :=
      SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hyzAdj
    have hyc : H.connectedComponentMk y = c := by
      have hxc : H.connectedComponentMk x = c := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hx
      calc
        H.connectedComponentMk y = H.connectedComponentMk z := hcompYZ
        _ = H.connectedComponentMk x := hcompXZ.symm
        _ = c := hxc
    have hySupp : y ∈ c.supp := by
      simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hyc
    exact Finset.mem_erase.mpr ⟨hxy.symm, by simpa using hySupp⟩
  have hunion : A ∪ B ⊆ c.supp.toFinite.toFinset.erase x :=
    Finset.union_subset hAsub hBsub
  have hcardUnion := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisj, hAcard, hBcard] at hcardUnion
  have hcardSupp : c.supp.toFinite.toFinset.card = c.supp.ncard := by
    exact (Set.ncard_eq_toFinset_card c.supp c.supp.toFinite).symm
  have hxmem : x ∈ c.supp.toFinite.toFinset := by simpa using hx
  rw [Finset.card_erase_of_mem hxmem, hcardSupp] at hcardUnion
  omega

/-- All four arithmetic conditions consumed by the finite H16 quotient
terminals. -/
theorem componentQuotientMatrix_sixRegular_pair_conditions
    {V : Type*} [Fintype V] [DecidableEq V]
    (R H : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel H.Adj]
    [Fintype H.ConnectedComponent] [DecidableEq H.ConnectedComponent]
    (hfree : ¬ containsC4 V H) (hHreg : ∀ x, H.degree x = 2)
    (hRreg : ∀ x, R.degree x = 6)
    (hcomm : R.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * R.adjMatrix ℝ)
    (hsep : ∀ {x y}, R.Adj x y →
      (H.neighborFinset x ∩ H.neighborFinset y).card = 0) :
    (∀ c : H.ConnectedComponent,
      ∑ e, componentQuotientMatrix R H c e = 6) ∧
    (∀ c e : H.ConnectedComponent,
      c.supp.ncard * componentQuotientMatrix R H c e =
        e.supp.ncard * componentQuotientMatrix R H e c) ∧
    (∀ c : H.ConnectedComponent,
      componentQuotientMatrix R H c c + 3 ≤ c.supp.ncard) ∧
    (∀ c e : H.ConnectedComponent,
      componentQuotientMatrix R H c e ≤ e.supp.ncard) := by
  constructor
  · intro c
    rw [sum_componentQuotientMatrix_row, hRreg]
  constructor
  · exact componentQuotientMatrix_balance R H 2 hHreg hcomm
  constructor
  · exact componentQuotientMatrix_diag_add_three_le
      R H hfree hHreg hsep
  · intro c e
    let A := componentNeighborFinset R H e (componentRepresentative H c)
    have hsub : A ⊆ e.supp.toFinite.toFinset := by
      intro y hy
      have hyc : H.connectedComponentMk y = e :=
        (Finset.mem_filter.mp hy).2
      have hySupp : y ∈ e.supp := by
        simpa [SimpleGraph.ConnectedComponent.mem_supp_iff] using hyc
      simpa using hySupp
    have hc := Finset.card_le_card hsub
    have hAcard : A.card = componentQuotientMatrix R H c e := by rfl
    have hcardSupp : e.supp.toFinite.toFinset.card = e.supp.ncard := by
      exact (Set.ncard_eq_toFinset_card e.supp e.supp.toFinite).symm
    rwa [hAcard, hcardSupp] at hc

/-- Transport an abstract component-indexed quotient ledger across a finite
enumeration.  This is the final interface from graph components to the
explicit `Fin k` arithmetic terminals. -/
theorem exists_sixRegularPairQuotientFeasible_of_equiv
    {C : Type*} [Fintype C] {k : ℕ}
    (size : C → ℕ) (Q : C → C → ℕ)
    (s : Fin k → ℕ) (e : Fin k ≃ C)
    (hsize : ∀ i, size (e i) = s i)
    (hrow : ∀ c, ∑ d, Q c d = 6)
    (hbal : ∀ c d, size c * Q c d = size d * Q d c)
    (hdiag : ∀ c, Q c c + 3 ≤ size c)
    (hbound : ∀ c d, Q c d ≤ size d) :
    ∃ q : Fin k → Fin k → ℕ,
      SixRegularPairQuotientFeasible s q := by
  let q : Fin k → Fin k → ℕ := fun i j ↦ Q (e i) (e j)
  refine ⟨q, ?_⟩
  constructor
  · intro i
    change (∑ j, Q (e i) (e j)) = 6
    rw [e.sum_comp]
    exact hrow (e i)
  constructor
  · intro i j
    change s i * Q (e i) (e j) = s j * Q (e j) (e i)
    rw [← hsize i, ← hsize j]
    exact hbal (e i) (e j)
  constructor
  · intro i
    change Q (e i) (e i) + 3 ≤ s i
    rw [← hsize i]
    exact hdiag (e i)
  · intro i j
    change Q (e i) (e j) ≤ s j
    rw [← hsize j]
    exact hbound (e i) (e j)

end

end Erdos85
