import Proofs.Erdos85SquareOrderDefectNeighborhoodDesign

/-! # The forced incidence profile when there are two high vertices -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- At square order `64`, if there are exactly two degree-nine vertices, the
first two high-incidence moments force one unique vertex incident with both
of them.  Every other vertex is incident with at most one high vertex. -/
theorem squareOrder_eight_twoHigh_exists_unique_incidenceTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 8 ∨ G.degree v = 8)
    (hcard : Fintype.card V = 8 * 8)
    (hhigh : (squareOrderHighVertices G 8).card = 2) :
    ∃ x : V,
      squareOrderHighIncidenceCount G 8 x = 2 ∧
        ∀ y : V, y ≠ x → squareOrderHighIncidenceCount G 8 y ≤ 1 := by
  classical
  let k := squareOrderHighIncidenceCount G 8
  let excess : V → ℕ := fun x => k x * (k x - 1)
  have hfirst : (∑ x : V, k x) = 18 := by
    have h := squareOrder_sum_highNeighborCount_eq G 8
    simpa [k, squareOrderHighIncidenceCount, hhigh] using h
  have hsecond : (∑ x : V, (k x) ^ 2) = 20 := by
    have h := squareOrder_sum_highNeighborCount_sq_eq
      G hfree (d := 8) (by omega) hmin hcover hcard
    change (∑ x : V, (k x) ^ 2) =
      (squareOrderHighVertices G 8).card *
        ((squareOrderHighVertices G 8).card + 8) at h
    rw [hhigh] at h
    norm_num at h
    exact h
  have hdecomp : (∑ x : V, (k x) ^ 2) =
      (∑ x : V, k x) + ∑ x : V, excess x := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : k x = 0
    · simp [excess, hx]
    · obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hx
      dsimp [excess]
      rw [hn]
      simp only [Nat.succ_sub_one]
      rw [pow_two, Nat.mul_succ]
      omega
  have hexcess : (∑ x : V, excess x) = 2 := by
    rw [hsecond, hfirst] at hdecomp
    omega
  have hexcess_le : ∀ x : V, excess x ≤ 2 := by
    intro x
    calc
      excess x ≤ ∑ y : V, excess y := by
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ x)
      _ = 2 := hexcess
  have hk_le_two : ∀ x : V, k x ≤ 2 := by
    intro x
    calc
      k x ≤ (squareOrderHighVertices G 8).card := by
        exact Finset.card_le_card Finset.inter_subset_right
      _ = 2 := hhigh
  have hexistsPositive : ∃ x : V, 0 < excess x := by
    by_contra h
    push Not at h
    have hzero : ∀ x : V, excess x = 0 := by
      intro x
      have hx := h x
      omega
    have : (∑ x : V, excess x) = 0 := by simp [hzero]
    omega
  obtain ⟨x, hxPositive⟩ := hexistsPositive
  have hxTwo : k x = 2 := by
    have hxle := hk_le_two x
    interval_cases hx : k x <;> simp [excess, hx] at hxPositive ⊢
  refine ⟨x, hxTwo, ?_⟩
  intro y hyx
  have hyle := hk_le_two y
  by_contra hy
  change ¬ k y ≤ 1 at hy
  have hyTwo : k y = 2 := by omega
  have hxExcess : excess x = 2 := by simp [excess, hxTwo]
  have hyExcess : excess y = 2 := by simp [excess, hyTwo]
  have hsumErase := Finset.sum_erase_add
    (Finset.univ : Finset V) excess (Finset.mem_univ x)
  rw [hexcess, hxExcess] at hsumErase
  have heraseZero : (∑ z ∈ (Finset.univ : Finset V).erase x, excess z) = 0 := by
    omega
  have hyMem : y ∈ (Finset.univ : Finset V).erase x := by simp [hyx]
  have hallZero : ∀ z ∈ (Finset.univ : Finset V).erase x, excess z = 0 := by
    exact Finset.sum_eq_zero_iff.mp heraseZero
  have hyZero := hallZero y hyMem
  omega

/-- Under the same two-high hypotheses, exactly sixteen vertices are
incident with one high vertex.  Together with the preceding theorem this
recovers the `(n₁,n₂) = (16,1)` part of the order-64 scout profile from the
uniform moment identities. -/
theorem squareOrder_eight_twoHigh_card_incidenceOne_eq_sixteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 8 ∨ G.degree v = 8)
    (hcard : Fintype.card V = 8 * 8)
    (hhigh : (squareOrderHighVertices G 8).card = 2) :
    ((Finset.univ : Finset V).filter fun x =>
      squareOrderHighIncidenceCount G 8 x = 1).card = 16 := by
  classical
  let k := squareOrderHighIncidenceCount G 8
  obtain ⟨x, hxTwo, hother⟩ :=
    squareOrder_eight_twoHigh_exists_unique_incidenceTwo
      G hfree hmin hcover hcard hhigh
  change k x = 2 at hxTwo
  change ∀ y : V, y ≠ x → k y ≤ 1 at hother
  have hfirst : (∑ y : V, k y) = 18 := by
    have h := squareOrder_sum_highNeighborCount_eq G 8
    simpa [k, squareOrderHighIncidenceCount, hhigh] using h
  have hsumErase : ∑ y ∈ (Finset.univ : Finset V).erase x, k y = 16 := by
    have h := Finset.sum_erase_add
      (Finset.univ : Finset V) k (Finset.mem_univ x)
    rw [hfirst, hxTwo] at h
    omega
  have hsumFilter :
      (∑ y ∈ (Finset.univ : Finset V).erase x, k y) =
        (((Finset.univ : Finset V).erase x).filter fun y => k y = 1).card := by
    calc
      (∑ y ∈ (Finset.univ : Finset V).erase x, k y) =
          ∑ y ∈ (Finset.univ : Finset V).erase x,
            if k y = 1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
        have hyle := hother y hyx
        by_cases hyOne : k y = 1
        · simp [hyOne]
        · have hyZero : k y = 0 := by omega
          simp [hyZero]
      _ = (((Finset.univ : Finset V).erase x).filter fun y => k y = 1).card := by
        rw [← Finset.sum_filter]
        simp
  have hxNot : ¬ k x = 1 := by omega
  have heraseFilter :
      ((Finset.univ : Finset V).erase x).filter (fun y => k y = 1) =
        (Finset.univ : Finset V).filter (fun y => k y = 1) := by
    ext y
    by_cases hyx : y = x
    · subst y
      simp [hxNot]
    · simp [hyx]
  change ((Finset.univ : Finset V).filter fun y => k y = 1).card = 16
  rw [← heraseFilter, ← hsumFilter, hsumErase]

/-- The unique incidence-two point is low, and after deleting its two high
neighbors its remaining neighborhood has cardinality six.  This constructs
the six-point set used in the two-high saturation argument. -/
theorem squareOrder_eight_twoHigh_exists_low_incidenceTwo_with_six_lowNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 8 ∨ G.degree v = 8)
    (hcard : Fintype.card V = 8 * 8)
    (hhigh : (squareOrderHighVertices G 8).card = 2) :
    ∃ x : V,
      G.degree x = 8 ∧
      squareOrderHighIncidenceCount G 8 x = 2 ∧
      (G.neighborFinset x \ squareOrderHighVertices G 8).card = 6 := by
  classical
  obtain ⟨x, hxTwo, hunique⟩ :=
    squareOrder_eight_twoHigh_exists_unique_incidenceTwo
      G hfree hmin hcover hcard hhigh
  have hxNotHigh : x ∉ squareOrderHighVertices G 8 := by
    intro hxHigh
    have hxZero := squareOrder_highNeighborCount_eq_zero_of_high
      G hcover hxHigh
    change squareOrderHighIncidenceCount G 8 x = 0 at hxZero
    omega
  have hxDegree : G.degree x = 8 := by
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
        G hfree (d := 8) (by omega) hmin hcover hcard x with hx | hx
    · exact hx
    · exfalso
      exact hxNotHigh (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩)
  have hsplit := Finset.card_sdiff_add_card_inter
    (G.neighborFinset x) (squareOrderHighVertices G 8)
  have hneighborCard : (G.neighborFinset x).card = 8 := by
    rw [G.card_neighborFinset_eq_degree, hxDegree]
  change (G.neighborFinset x ∩ squareOrderHighVertices G 8).card = 2 at hxTwo
  refine ⟨x, hxDegree, hxTwo, ?_⟩
  rw [hneighborCard] at hsplit
  omega

end

end Erdos85
