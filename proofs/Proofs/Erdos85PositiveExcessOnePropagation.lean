import Proofs.Erdos85PositiveExcessOneOperator

/-!
# Propagation of excess-one serving multiplicity

The entrywise conservation law `AD = DA` turns double use of a potential
serving arc into a new adjacency on the antipodal two-factor.  This is the
operator-discharge step needed for the global canonical-isolate count.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A triangle-free partner is automatically the isolated vertex in the
corresponding branch around every other neighbor of its partner. -/
theorem triangleFreePartner_isolated_in_secondLayerBranch
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u a x : V) (haTF : a ∈ triangleFreeNeighbors G u)
    (hxu : G.Adj x u) (hax : a ≠ x) :
    ∃ ha : a ∈ secondLayerBranch G x ⟨u, hxu⟩,
      (G.induce (secondLayerBranch G x ⟨u, hxu⟩)).degree ⟨a, ha⟩ = 0 := by
  classical
  have hua : G.Adj u a := (mem_triangleFreeNeighbors G u a).mp haTF |>.1
  have hcommon : (G.neighborFinset u ∩ G.neighborFinset a).card = 0 :=
    (mem_triangleFreeNeighbors G u a).mp haTF |>.2
  have hxa : ¬G.Adj x a := by
    intro hxa
    have hxmem : x ∈ G.neighborFinset u ∩ G.neighborFinset a :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset u x).mpr hxu.symm,
          (G.mem_neighborFinset a x).mpr hxa.symm⟩
    have := Finset.card_pos.mpr ⟨x, hxmem⟩
    omega
  have haBranch : a ∈ secondLayerBranch G x ⟨u, hxu⟩ := by
    rw [secondLayerBranch, Finset.mem_sdiff]
    refine ⟨(G.mem_neighborFinset u a).mpr hua, ?_⟩
    rw [Finset.mem_insert]
    push_neg
    exact ⟨hax, fun haN => hxa ((G.mem_neighborFinset x a).mp haN)⟩
  refine ⟨haBranch, ?_⟩
  rw [← (G.induce (secondLayerBranch G x ⟨u, hxu⟩)).card_neighborFinset_eq_degree,
    Finset.card_eq_zero]
  ext b
  constructor
  · intro hb
    have hab : G.Adj a b.1 := by
      simpa [SimpleGraph.mem_neighborFinset] using hb
    have hub : G.Adj u b.1 :=
      (G.mem_neighborFinset u b.1).mp (Finset.mem_sdiff.mp b.2).1
    have hbmem : b.1 ∈ G.neighborFinset u ∩ G.neighborFinset a :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset u b.1).mpr hub,
          (G.mem_neighborFinset a b.1).mpr hab⟩
    have := Finset.card_pos.mpr ⟨b.1, hbmem⟩
    omega
  · simp

/-- Entrywise `AD = DA` for an arbitrary regular `C₄`-free graph. -/
theorem card_filter_adj_secondOrderDefect_comm_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d) (x y : V) :
    (((secondOrderDefectGraph G).neighborFinset y).filter
          (fun z => G.Adj x z)).card =
      (((secondOrderDefectGraph G).neighborFinset x).filter
          (fun z => G.Adj z y)).card := by
  let D := secondOrderDefectGraph G
  have hcomm := adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hentry := congrFun (congrFun hcomm x) y
  change (G.adjMatrix ℤ * D.adjMatrix ℤ) x y =
    (D.adjMatrix ℤ * G.adjMatrix ℤ) x y at hentry
  rw [D.mul_adjMatrix_apply, D.adjMatrix_mul_apply] at hentry
  simp only [SimpleGraph.adjMatrix_apply, Finset.sum_boole,
    Int.ofNat_inj] at hentry
  simpa [D] using hentry

/-- **Double-service propagation.**  Suppose two distinct defect-neighbors
of `X` are both adjacent to `u`.  If `u` has only one triangle-free partner,
commutation forces an antipodal neighbor of `u` to be adjacent to `X` as
well. -/
theorem exists_adj_antipodal_of_two_adj_defectNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ z, G.degree z = d)
    (u X x y : V) (hxy : x ≠ y)
    (hxD : x ∈ (secondOrderDefectGraph G).neighborFinset X)
    (hyD : y ∈ (secondOrderDefectGraph G).neighborFinset X)
    (hux : G.Adj u x) (huy : G.Adj u y)
    (hTFone : (triangleFreeNeighbors G u).card = 1) :
    ∃ w ∈ antipodalNeighbors G u, G.Adj w X := by
  classical
  let L := ((secondOrderDefectGraph G).neighborFinset X).filter
    (fun z => G.Adj u z)
  let R := ((secondOrderDefectGraph G).neighborFinset u).filter
    (fun z => G.Adj z X)
  have hxL : x ∈ L := Finset.mem_filter.mpr ⟨hxD, hux⟩
  have hyL : y ∈ L := Finset.mem_filter.mpr ⟨hyD, huy⟩
  have hLtwo : 2 ≤ L.card := by
    have hp : ({x, y} : Finset V).card = 2 := by simp [hxy]
    rw [← hp]
    apply Finset.card_le_card
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hxL
    · exact hyL
  have hLR : L.card = R.card := by
    simpa [L, R] using
      card_filter_adj_secondOrderDefect_comm_of_regular
        G hfree hreg u X
  have hRtwo : 2 ≤ R.card := by omega
  by_contra hnone
  push_neg at hnone
  have hsub : R ⊆ triangleFreeNeighbors G u := by
    intro z hz
    have hzD := (Finset.mem_filter.mp hz).1
    rw [secondOrderDefectGraph_neighborFinset G u] at hzD
    rcases Finset.mem_union.mp hzD with hzAnti | hzTF
    · exact (hnone z hzAnti (Finset.mem_filter.mp hz).2).elim
    · exact hzTF
  have hRle : R.card ≤ (triangleFreeNeighbors G u).card :=
    Finset.card_le_card hsub
  rw [hTFone] at hRle
  omega

/-- In the actual canonical-isolate configuration, propagation is exact:
if a root `u` sees both antipodes of an external vertex `X`, then exactly
one of the two antipodes of `u` sees `X`. -/
theorem card_adj_antipodal_eq_one_of_root_sees_both
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4)
    (x : V) (u : {z : V // z ∈ G.neighborSet x})
    (a : secondLayerBranch G x u)
    (haIso : (G.induce (secondLayerBranch G x u)).degree a = 0)
    (X : {z : V // z ≠ x}) (hXext : X ∈ externalRepairCandidates G x)
    (haX : G.Adj a.1 X.1)
    (hboth : ∀ z ∈ antipodalNeighbors G X.1, G.Adj u.1 z) :
    (((antipodalNeighbors G u.1).filter fun z => G.Adj z X.1).card) = 1 := by
  classical
  let D := secondOrderDefectGraph G
  let L := (D.neighborFinset X.1).filter fun z => G.Adj u.1 z
  let R := (D.neighborFinset u.1).filter fun z => G.Adj z X.1
  have huTF := root_mem_triangleFreeNeighbors_of_isolated_secondLayerBranch
    G hfree x u a haIso
  have hauTF : a.1 ∈ triangleFreeNeighbors G u.1 :=
    (mem_triangleFreeNeighbors_comm G a.1 u.1).mp huTF
  have hTFu := excessOne_triangleFreeNeighbors_card_eq_one_of_odd
    G hfree hd hodd hreg hcard u.1
  have hCX := antipodalGraph_degree_eq_two_of_odd_excessOne
    G hfree hd hodd hreg hcard X.1
  have huX : u.1 ≠ X.1 := by
    intro h
    have hXnot : ¬G.Adj X.1 x :=
      (mem_externalRepairCandidates G x X).mp hXext |>.1
    exact hXnot (h ▸ u.2.symm)
  have ha_not_TFX : a.1 ∉ triangleFreeNeighbors G X.1 := by
    rw [mem_triangleFreeNeighbors_comm]
    exact external_not_triangleFreePartner_of_isolated_matched_branch
      G hfree hd hodd hreg hcard x u a haIso X hXext
  have hnoTF : ∀ z ∈ triangleFreeNeighbors G X.1, ¬G.Adj u.1 z := by
    intro z hzTF huz
    have haz : a.1 ≠ z := by
      intro h
      exact ha_not_TFX (h ▸ hzTF)
    have huX' : u.1 ≠ X.1 := huX
    exact hfree (containsC4_of_two_common
      (x := u.1) (y := X.1) (v := a.1) (v' := z)
      huX' haz
      ((mem_triangleFreeNeighbors G a.1 u.1).mp huTF).1
      haX huz.symm ((mem_triangleFreeNeighbors G X.1 z).mp hzTF).1.symm)
  have hLeq : L = antipodalNeighbors G X.1 := by
    ext z
    simp only [L, Finset.mem_filter]
    rw [secondOrderDefectGraph_neighborFinset G X.1]
    constructor
    · rintro ⟨hzD, huz⟩
      rcases Finset.mem_union.mp hzD with hzC | hzTF
      · exact hzC
      · exact (hnoTF z hzTF huz).elim
    · intro hzC
      exact ⟨Finset.mem_union_left _ hzC, hboth z hzC⟩
  have hLcard : L.card = 2 := by
    rw [hLeq, ← antipodalGraph_neighborFinset G X.1,
      (antipodalGraph G).card_neighborFinset_eq_degree]
    exact hCX
  have hLR : L.card = R.card := by
    simpa [L, R, D] using
      card_filter_adj_secondOrderDefect_comm_of_regular
        G hfree hreg u.1 X.1
  have hRcard : R.card = 2 := by omega
  let Cpart := (antipodalNeighbors G u.1).filter fun z => G.Adj z X.1
  let Tpart := (triangleFreeNeighbors G u.1).filter fun z => G.Adj z X.1
  have hTcard : Tpart.card = 1 := by
    have haT : a.1 ∈ Tpart := Finset.mem_filter.mpr ⟨hauTF, haX⟩
    have hpos : 1 ≤ Tpart.card := Finset.one_le_card.mpr ⟨a.1, haT⟩
    have hle : Tpart.card ≤ (triangleFreeNeighbors G u.1).card := by
      apply Finset.card_le_card
      intro z hz
      exact (Finset.mem_filter.mp hz).1
    rw [hTFu] at hle
    omega
  have hdisj : Disjoint Cpart Tpart := by
    rw [Finset.disjoint_left]
    intro z hzC hzT
    exact (Finset.disjoint_left.mp
      (disjoint_antipodal_triangleFreeNeighbors G u.1))
        (Finset.mem_filter.mp hzC).1 (Finset.mem_filter.mp hzT).1
  have hRsplit : R = Cpart ∪ Tpart := by
    simp only [R, Cpart, Tpart]
    rw [secondOrderDefectGraph_neighborFinset G u.1,
      Finset.filter_union]
  have hsum : R.card = Cpart.card + Tpart.card := by
    rw [hRsplit, Finset.card_union_of_disjoint hdisj]
  change Cpart.card = 1
  omega

/-- Every row of the matching commutator has exactly `d-1` negative
entries.  These are the global capacity slots for canonical-isolate demands. -/
theorem card_matchingCommutator_negative_support
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) (x : V) :
    let B := G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ
    ((Finset.univ : Finset V).filter fun y => B x y - B y x = -1).card =
      d - 1 := by
  classical
  dsimp only
  let B := G.adjMatrix ℤ * (triangleFreeEdgeGraph G).adjMatrix ℤ
  have hcardTF := excessOne_triangleFreeNeighbors_card_eq_one_of_odd
    G hfree hd hodd hreg hcard x
  obtain ⟨mx, hmx⟩ := Finset.card_eq_one.mp hcardTF
  have hmxMem : mx ∈ triangleFreeNeighbors G x := by simp [hmx]
  have hBcol : ∀ y,
      B y x = G.adjMatrix ℤ y mx := by
    intro y
    simp only [B]
    rw [(triangleFreeEdgeGraph G).mul_adjMatrix_apply,
      triangleFreeEdgeGraph_neighborFinset, hmx]
    simp only [Finset.sum_singleton]
  have heq : ((Finset.univ : Finset V).filter fun y =>
      B x y - B y x = -1) = (G.neighborFinset mx).erase x := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase]
    constructor
    · intro hy
      have hByx := adjMatrix_mul_triangleFreeEdgeGraph_apply_eq_zero_or_one
        G hfree hd hodd hreg hcard y x
      have hBxy := adjMatrix_mul_triangleFreeEdgeGraph_apply_eq_zero_or_one
        G hfree hd hodd hreg hcard x y
      change B y x = 0 ∨ B y x = 1 at hByx
      change B x y = 0 ∨ B x y = 1 at hBxy
      have hvals : B x y = 0 ∧ B y x = 1 := by
        rcases hBxy with h0 | h1 <;> rcases hByx with h0' | h1' <;> omega
      have hyx : y ≠ x := by
        intro h
        subst y
        omega
      refine ⟨hyx, ?_⟩
      apply (G.mem_neighborFinset mx y).mpr
      have : G.Adj y mx := by
        simpa [hBcol, SimpleGraph.adjMatrix_apply] using hvals.2
      exact this.symm
    · rintro ⟨hyx, hymx⟩
      have hByx : B y x = 1 := by
        rw [hBcol, SimpleGraph.adjMatrix_apply,
          if_pos ((G.mem_neighborFinset mx y).mp hymx |>.symm)]
      have hprod := adjMatrix_mul_triangleFreeEdgeGraph_opposite_mul_eq_zero
        G hfree hd hodd hreg hcard hyx
      change B y x * B x y = 0 at hprod
      have hBxy : B x y = 0 := by
        rw [hByx] at hprod
        simpa using hprod
      omega
  rw [heq, Finset.card_erase_of_mem]
  · rw [G.card_neighborFinset_eq_degree, hreg mx]
  · exact (G.mem_neighborFinset mx x).mpr
      ((mem_triangleFreeNeighbors G x mx).mp hmxMem).1.symm

end

end Erdos85
