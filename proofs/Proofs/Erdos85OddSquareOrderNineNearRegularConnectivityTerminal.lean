import Proofs.Erdos85OddSquareOrderNineNearRegularCutArithmetic

/-! # Component-balance terminal for the q=9 ordinary defect graph

This module joins the two arithmetic halves of the reviewed connectivity
argument.  A component not containing the unique bin-three point has `n₀`
bin-zero and `n₁` bin-one vertices.  Counting its B0--B1 defect edges in the
two directions gives `3 n₀ = 5 n₁`, hence its order is divisible by eight.
The near-regular cut classification excludes every such proper order.
-/

namespace Erdos85

/-- A disconnected nonempty graph has a connected component different from
the component containing any prescribed owner vertex.  Its support is
nonempty and omits the owner, hence is a proper shore.  This is the generic
selection step used to choose the non-owner ordinary-defect component. -/
theorem exists_nonowner_connectedComponent_of_not_connected
    {V : Type*} [Nonempty V] (D : SimpleGraph V) (owner : V)
    (hnot : ¬ D.Connected) :
    ∃ c : D.ConnectedComponent,
      c ≠ D.connectedComponentMk owner ∧
      c.supp.Nonempty ∧ owner ∉ c.supp ∧ c.supp ≠ Set.univ := by
  have hnotPreconnected : ¬ D.Preconnected := by
    intro hpre
    exact hnot ⟨hpre⟩
  simp only [SimpleGraph.Preconnected] at hnotPreconnected
  push Not at hnotPreconnected
  obtain ⟨u, v, huv⟩ := hnotPreconnected
  have huvComponent : D.connectedComponentMk u ≠ D.connectedComponentMk v := by
    intro huvEq
    exact huv (SimpleGraph.ConnectedComponent.exact huvEq)
  obtain ⟨c, hc⟩ :
      ∃ c : D.ConnectedComponent, c ≠ D.connectedComponentMk owner := by
    by_cases hu : D.connectedComponentMk u ≠ D.connectedComponentMk owner
    · exact ⟨D.connectedComponentMk u, hu⟩
    · have huOwner : D.connectedComponentMk u = D.connectedComponentMk owner :=
        Classical.not_not.mp hu
      have hv : D.connectedComponentMk v ≠ D.connectedComponentMk owner := by
        intro hvOwner
        exact huvComponent (huOwner.trans hvOwner.symm)
      exact ⟨D.connectedComponentMk v, hv⟩
  have howner : owner ∉ c.supp := by
    intro hmem
    have hm := (SimpleGraph.ConnectedComponent.mem_supp_iff c owner).mp hmem
    exact hc hm.symm
  refine ⟨c, hc, c.nonempty_supp, howner, ?_⟩
  intro hsupp
  exact howner (hsupp ▸ Set.mem_univ owner)

/-- Neighbor closure of a finite shore is exactly the vanishing oriented cut
sum used by the C4-free defect cut identity. -/
theorem sum_neighbor_inter_compl_eq_zero_of_neighborFinset_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S : Finset V)
    (hclosed : ∀ u ∈ S, D.neighborFinset u ⊆ S) :
    ∑ u ∈ S, (D.neighborFinset u ∩ (Finset.univ \ S)).card = 0 := by
  apply Finset.sum_eq_zero
  intro u hu
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  have hvParts := Finset.mem_inter.mp hv
  have hvOutside := (Finset.mem_sdiff.mp hvParts.2).2
  exact hvOutside (hclosed u hu hvParts.1)

/-- A shore closed inside the non-high induced graph gives both ambient
zero-cut equations needed by the graph-to-admissibility adapter, provided
the removed high vertices are isolated in the defect graph.  Symmetry makes
the relative complement closed automatically. -/
theorem two_zeroBoundarySums_of_relative_closed_and_isolated
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (H S : Finset V)
    (hSsub : S ⊆ Finset.univ \ H)
    (hclosed : ∀ x ∈ S,
      D.neighborFinset x ∩ (Finset.univ \ H) ⊆ S)
    (hiso : ∀ h ∈ H, D.neighborFinset h = ∅) :
    (∑ x ∈ S,
      (D.neighborFinset x ∩ (Finset.univ \ S)).card) = 0 ∧
    (let T := (Finset.univ \ H) \ S
      ∑ x ∈ T,
        (D.neighborFinset x ∩ (Finset.univ \ T)).card) = 0 := by
  classical
  let O := Finset.univ \ H
  let T := O \ S
  have hnoHigh {x y : V} (hxO : x ∈ O) (hxy : D.Adj x y) : y ∉ H := by
    intro hyH
    have hxin : x ∈ D.neighborFinset y := by
      simpa [SimpleGraph.mem_neighborFinset, D.adj_comm] using hxy
    rw [hiso y hyH] at hxin
    exact Finset.notMem_empty x hxin
  have hSclosed : ∀ x ∈ S, D.neighborFinset x ⊆ S := by
    intro x hxS y hyN
    have hxO : x ∈ O := hSsub hxS
    have hxy : D.Adj x y := by simpa using hyN
    have hyO : y ∈ O := Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ y, hnoHigh hxO hxy⟩
    exact hclosed x hxS (Finset.mem_inter.mpr ⟨hyN, hyO⟩)
  have hTclosed : ∀ x ∈ T, D.neighborFinset x ⊆ T := by
    intro x hxT y hyN
    have hxParts := Finset.mem_sdiff.mp hxT
    have hxy : D.Adj x y := by simpa using hyN
    have hyO : y ∈ O := Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ y, hnoHigh hxParts.1 hxy⟩
    have hyNotS : y ∉ S := by
      intro hyS
      have hxS := hclosed y hyS (Finset.mem_inter.mpr ⟨by
        simpa [SimpleGraph.mem_neighborFinset, D.adj_comm] using hxy, hxParts.1⟩)
      exact hxParts.2 hxS
    exact Finset.mem_sdiff.mpr ⟨hyO, hyNotS⟩
  constructor
  · exact sum_neighbor_inter_compl_eq_zero_of_neighborFinset_subset
      D S hSclosed
  · dsimp only
    exact sum_neighbor_inter_compl_eq_zero_of_neighborFinset_subset
      D T hTclosed

/-- Finite call-site form of the non-owner selection lemma.  The returned
shore is nonempty, has cardinality strictly below the ambient order, omits
the owner, and is closed under every graph neighbor; equivalently its graph
edge boundary is zero. -/
theorem exists_nonempty_proper_nonowner_zeroBoundaryShore_of_not_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (owner : V)
    (hnot : ¬ D.Connected) :
    ∃ S : Finset V,
      0 < S.card ∧ S.card < Fintype.card V ∧ owner ∉ S ∧
      ∀ u ∈ S, D.neighborFinset u ⊆ S := by
  letI : Nonempty V := ⟨owner⟩
  obtain ⟨c, _, hcNonempty, howner, _⟩ :=
    exists_nonowner_connectedComponent_of_not_connected D owner hnot
  let S := Finset.univ.filter fun v => v ∈ c.supp
  have hSpos : 0 < S.card := by
    rw [Finset.card_pos]
    obtain ⟨v, hv⟩ := hcNonempty
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv⟩⟩
  have hSsubset : S ⊆ Finset.univ := Finset.subset_univ S
  have hSne : S ≠ Finset.univ := by
    intro hEq
    have hownerS : owner ∈ S := by
      rw [hEq]
      exact Finset.mem_univ owner
    exact howner (Finset.mem_filter.mp hownerS).2
  have hScard : S.card < Fintype.card V := by
    rw [← Finset.card_univ]
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hSsubset, hSne⟩)
  have hownerS : owner ∉ S := by
    intro hmem
    exact howner (Finset.mem_filter.mp hmem).2
  refine ⟨S, hSpos, hScard, hownerS, ?_⟩
  intro u hu v hv
  have huSupp : u ∈ c.supp := (Finset.mem_filter.mp hu).2
  have huv : D.Adj u v := by simpa using hv
  have hvSupp : v ∈ c.supp :=
    SimpleGraph.ConnectedComponent.mem_supp_of_adj_mem_supp c huSupp huv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvSupp⟩

/-- Selection directly in an induced graph, returned as a finset of ambient
vertices.  A disconnected induced graph has a nonempty proper component not
containing a chosen owner; its ambient image is relatively neighbor-closed. -/
theorem exists_nonempty_proper_nonowner_relativeClosedShore_of_induce_not_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (U : Finset V)
    (owner : {x // x ∈ U})
    (hnot : ¬ (D.induce (↑U : Set V)).Connected) :
    ∃ S : Finset V,
      0 < S.card ∧ S.card < U.card ∧ owner.1 ∉ S ∧ S ⊆ U ∧
      ∀ x ∈ S, D.neighborFinset x ∩ U ⊆ S := by
  classical
  let K := D.induce (↑U : Set V)
  obtain ⟨S', hSpos, hSlt, howner, hclosed⟩ :=
    exists_nonempty_proper_nonowner_zeroBoundaryShore_of_not_connected
      K owner hnot
  let S : Finset V := S'.image Subtype.val
  have hcard : S.card = S'.card := by
    dsimp only [S]
    rw [Finset.card_image_iff.mpr Subtype.val_injective.injOn]
  have hUcard : Fintype.card {x // x ∈ U} = U.card := by
    exact Fintype.card_coe U
  refine ⟨S, by simpa [hcard] using hSpos, ?_, ?_, ?_, ?_⟩
  · simpa [hcard, hUcard] using hSlt
  · intro hmem
    have : owner ∈ S' := by
      rw [Finset.mem_image] at hmem
      obtain ⟨z, hz, hzo⟩ := hmem
      have : z = owner := Subtype.ext hzo
      simpa [this] using hz
    exact howner this
  · intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact z.2
  · intro x hxS y hy
    rw [Finset.mem_image] at hxS
    obtain ⟨x', hx'S, rfl⟩ := hxS
    have hyParts := Finset.mem_inter.mp hy
    let y' : {x // x ∈ U} := ⟨y, hyParts.2⟩
    have hyK : y' ∈ K.neighborFinset x' := by
      rw [K.mem_neighborFinset]
      change D.Adj x'.1 y'.1
      exact (D.mem_neighborFinset x'.1 y'.1).mp hyParts.1
    have hyS' := hclosed x' hx'S hyK
    exact Finset.mem_image.mpr ⟨y', hyS', rfl⟩

/-- If every vertex of `B₀` has three neighbors in `B₁` and every vertex
of `B₁` has five neighbors in `B₀`, double-counting the cross edges gives
the component balance `3 |B₀| = 5 |B₁|`.  At the graph call site the two
sets are the colour classes restricted to a zero-boundary component. -/
theorem three_mul_card_eq_five_mul_card_of_cross_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (B₀ B₁ : Finset V)
    (h₀ : ∀ x ∈ B₀, (D.neighborFinset x ∩ B₁).card = 3)
    (h₁ : ∀ y ∈ B₁, (D.neighborFinset y ∩ B₀).card = 5) :
    3 * B₀.card = 5 * B₁.card := by
  classical
  have hrow (x : V) :
      (D.neighborFinset x ∩ B₁).card =
        ∑ y ∈ B₁, if D.Adj x y then 1 else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext y
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  have hcol (y : V) :
      (D.neighborFinset y ∩ B₀).card =
        ∑ x ∈ B₀, if D.Adj x y then 1 else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext x
    simp [SimpleGraph.mem_neighborFinset, D.adj_comm, and_comm]
  have hcross :
      (∑ x ∈ B₀, (D.neighborFinset x ∩ B₁).card) =
        ∑ y ∈ B₁, (D.neighborFinset y ∩ B₀).card := by
    simp_rw [hrow, hcol]
    exact Finset.sum_comm
  calc
    3 * B₀.card = ∑ _x ∈ B₀, 3 := by simp [Nat.mul_comm]
    _ = ∑ x ∈ B₀, (D.neighborFinset x ∩ B₁).card := by
      apply Finset.sum_congr rfl
      intro x hx
      exact (h₀ x hx).symm
    _ = ∑ y ∈ B₁, (D.neighborFinset y ∩ B₀).card := hcross
    _ = ∑ _y ∈ B₁, 5 := by
      apply Finset.sum_congr rfl
      intro y hy
      exact h₁ y hy
    _ = 5 * B₁.card := by simp [Nat.mul_comm]

/-- Restricting two global colour classes to a neighbor-closed shore preserves
their pointwise cross-degrees.  Consequently global degrees three and five
give the exact `3 : 5` balance inside every union of graph components. -/
theorem three_mul_card_inter_eq_five_mul_card_inter_of_closed_shore
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (S B₀ B₁ : Finset V)
    (hclosed : ∀ x ∈ S, D.neighborFinset x ⊆ S)
    (h₀ : ∀ x ∈ B₀, (D.neighborFinset x ∩ B₁).card = 3)
    (h₁ : ∀ y ∈ B₁, (D.neighborFinset y ∩ B₀).card = 5) :
    3 * (B₀ ∩ S).card = 5 * (B₁ ∩ S).card := by
  apply three_mul_card_eq_five_mul_card_of_cross_degrees D (B₀ ∩ S) (B₁ ∩ S)
  · intro x hx
    have hxParts := Finset.mem_inter.mp hx
    have hinter :
        D.neighborFinset x ∩ (B₁ ∩ S) = D.neighborFinset x ∩ B₁ := by
      ext y
      simp only [Finset.mem_inter]
      constructor
      · exact fun hy => ⟨hy.1, hy.2.1⟩
      · intro hy
        exact ⟨hy.1, hy.2, hclosed x hxParts.2 hy.1⟩
    rw [hinter]
    exact h₀ x hxParts.1
  · intro y hy
    have hyParts := Finset.mem_inter.mp hy
    have hinter :
        D.neighborFinset y ∩ (B₀ ∩ S) = D.neighborFinset y ∩ B₀ := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · exact fun hx => ⟨hx.1, hx.2.1⟩
      · intro hx
        exact ⟨hx.1, hx.2, hclosed y hyParts.2 hx.1⟩
    rw [hinter]
    exact h₁ y hyParts.1

/-- Induced-subgraph form of the closed-shore balance theorem.  It is enough
that `S` be closed under neighbors lying in an ambient vertex set `U`, provided
both colour classes lie in `U`.  This is the form used for components of the
ordinary induced defect graph inside the full second-order defect graph. -/
theorem three_mul_card_inter_eq_five_mul_card_inter_of_relative_closed_shore
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (U S B₀ B₁ : Finset V)
    (hB₀U : B₀ ⊆ U) (hB₁U : B₁ ⊆ U)
    (hclosed : ∀ x ∈ S, D.neighborFinset x ∩ U ⊆ S)
    (h₀ : ∀ x ∈ B₀, (D.neighborFinset x ∩ B₁).card = 3)
    (h₁ : ∀ y ∈ B₁, (D.neighborFinset y ∩ B₀).card = 5) :
    3 * (B₀ ∩ S).card = 5 * (B₁ ∩ S).card := by
  apply three_mul_card_eq_five_mul_card_of_cross_degrees D (B₀ ∩ S) (B₁ ∩ S)
  · intro x hx
    have hxParts := Finset.mem_inter.mp hx
    have hinter :
        D.neighborFinset x ∩ (B₁ ∩ S) = D.neighborFinset x ∩ B₁ := by
      ext y
      simp only [Finset.mem_inter]
      constructor
      · exact fun hy => ⟨hy.1, hy.2.1⟩
      · intro hy
        exact ⟨hy.1, hy.2,
          hclosed x hxParts.2 (Finset.mem_inter.mpr ⟨hy.1, hB₁U hy.2⟩)⟩
    rw [hinter]
    exact h₀ x hxParts.1
  · intro y hy
    have hyParts := Finset.mem_inter.mp hy
    have hinter :
        D.neighborFinset y ∩ (B₀ ∩ S) = D.neighborFinset y ∩ B₀ := by
      ext x
      simp only [Finset.mem_inter]
      constructor
      · exact fun hx => ⟨hx.1, hx.2.1⟩
      · intro hx
        exact ⟨hx.1, hx.2,
          hclosed y hyParts.2 (Finset.mem_inter.mpr ⟨hx.1, hB₀U hx.2⟩)⟩
    rw [hinter]
    exact h₁ y hyParts.1

/-- The exact `3 n₀ = 5 n₁` component balance forces the total component
order to be divisible by eight. -/
theorem eight_dvd_of_three_mul_eq_five_mul
    (n₀ n₁ : ℕ) (hbalance : 3 * n₀ = 5 * n₁) :
    8 ∣ n₀ + n₁ := by
  have hfive : 5 ∣ n₀ := by
    omega
  obtain ⟨k, rfl⟩ := hfive
  have hn₁ : n₁ = 3 * k := by
    omega
  subst n₁
  use k
  omega

/-- The component handshake identity immediately supplies the parity input
used by the finite cut classification.  The addition-shaped hypothesis avoids
Nat subtraction at the graph call site. -/
theorem orderNine_component_colour_sum_even_of_handshake
    (e s b₁ b₂ b₃ : ℕ)
    (hhandshake : 2 * e + (b₁ + b₂ + b₃) = 8 * s) :
    (b₁ + b₂ + b₃) % 2 = 0 := by
  omega

/-- Abstract terminal consumed by the graph-level connectivity proof.

The graph layer only has to provide a nonempty proper component, its three
high-root incidence counts, the two cut inequalities, parity, and the
two-sided B0--B1 edge count.  No component enumeration or graph census is
hidden in this statement. -/
theorem false_of_orderNine_nearRegular_proper_component_balance
    (s : Fin 78) (b₁ b₂ b₃ : Fin 11) (n₀ n₁ : ℕ)
    (hs : s.1 ≠ 0)
    (hcard : s.1 = n₀ + n₁)
    (hparity : (b₁.1 + b₂.1 + b₃.1) % 2 = 0)
    (hadm : orderNineNearRegularComponentAdmissible s.1 b₁.1 b₂.1 b₃.1)
    (hbalance : 3 * n₀ = 5 * n₁) :
    False := by
  have height : 8 ∣ s.1 := by
    rw [hcard]
    exact eight_dvd_of_three_mul_eq_five_mul n₀ n₁ hbalance
  exact orderNine_nearRegular_eight_not_dvd_proper_component_order
    s b₁ b₂ b₃ hs hparity hadm height

/-- Parity-free form of the component-balance terminal.  The exact two-sided
cut inequalities already exclude every nonzero eight-divisible shore, so the
graph-level connectivity argument does not need a separate handshake count. -/
theorem false_of_orderNine_nearRegular_component_balance
    (s : Fin 78) (b₁ b₂ b₃ : Fin 11) (n₀ n₁ : ℕ)
    (hs : s.1 ≠ 0)
    (hcard : s.1 = n₀ + n₁)
    (hadm : orderNineNearRegularComponentAdmissible s.1 b₁.1 b₂.1 b₃.1)
    (hbalance : 3 * n₀ = 5 * n₁) :
    False := by
  have height : 8 ∣ s.1 := by
    rw [hcard]
    exact eight_dvd_of_three_mul_eq_five_mul n₀ n₁ hbalance
  exact orderNine_nearRegular_eight_not_dvd_of_admissible
    s b₁ b₂ b₃ hs hadm height

/-- Natural-number call-site form of the parity-free terminal.  The graph
assembly naturally produces finset cardinalities and their strict bounds;
this wrapper performs the bounded `Fin` packaging once. -/
theorem false_of_orderNine_nearRegular_component_balance_nat
    (s b₁ b₂ b₃ n₀ n₁ : ℕ)
    (hs : s ≠ 0) (hslt : s < 78)
    (hb₁ : b₁ < 11) (hb₂ : b₂ < 11) (hb₃ : b₃ < 11)
    (hcard : s = n₀ + n₁)
    (hadm : orderNineNearRegularComponentAdmissible s b₁ b₂ b₃)
    (hbalance : 3 * n₀ = 5 * n₁) :
    False := by
  exact false_of_orderNine_nearRegular_component_balance
    ⟨s, hslt⟩ ⟨b₁, hb₁⟩ ⟨b₂, hb₂⟩ ⟨b₃, hb₃⟩ n₀ n₁
    hs hcard hadm hbalance

/-- Call-site form using the actual defect-component handshake equation
instead of asking the graph layer to separately state its parity consequence. -/
theorem false_of_orderNine_nearRegular_component_handshake_and_balance
    (s : Fin 78) (b₁ b₂ b₃ : Fin 11) (e n₀ n₁ : ℕ)
    (hs : s.1 ≠ 0)
    (hcard : s.1 = n₀ + n₁)
    (hhandshake : 2 * e + (b₁.1 + b₂.1 + b₃.1) = 8 * s.1)
    (hadm : orderNineNearRegularComponentAdmissible s.1 b₁.1 b₂.1 b₃.1)
    (hbalance : 3 * n₀ = 5 * n₁) :
    False := by
  apply false_of_orderNine_nearRegular_proper_component_balance
    s b₁ b₂ b₃ n₀ n₁ hs hcard
  · exact orderNine_component_colour_sum_even_of_handshake
      e s.1 b₁.1 b₂.1 b₃.1 hhandshake
  · exact hadm
  · exact hbalance

#print axioms eight_dvd_of_three_mul_eq_five_mul
#print axioms exists_nonowner_connectedComponent_of_not_connected
#print axioms sum_neighbor_inter_compl_eq_zero_of_neighborFinset_subset
#print axioms two_zeroBoundarySums_of_relative_closed_and_isolated
#print axioms exists_nonempty_proper_nonowner_zeroBoundaryShore_of_not_connected
#print axioms exists_nonempty_proper_nonowner_relativeClosedShore_of_induce_not_connected
#print axioms three_mul_card_eq_five_mul_card_of_cross_degrees
#print axioms three_mul_card_inter_eq_five_mul_card_inter_of_closed_shore
#print axioms three_mul_card_inter_eq_five_mul_card_inter_of_relative_closed_shore
#print axioms orderNine_component_colour_sum_even_of_handshake
#print axioms false_of_orderNine_nearRegular_proper_component_balance
#print axioms false_of_orderNine_nearRegular_component_balance
#print axioms false_of_orderNine_nearRegular_component_balance_nat
#print axioms false_of_orderNine_nearRegular_component_handshake_and_balance

end Erdos85
