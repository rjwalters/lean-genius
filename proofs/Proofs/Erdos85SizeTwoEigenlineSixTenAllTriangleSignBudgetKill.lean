import Proofs.Erdos85SizeTwoEigenlineSixTenAllTriangleHighReduction
import Proofs.Erdos85SizeTwoEigenlineGridInstantiation

/-!
# The opposite-sign defect budget kills the all-triangle 6+10 sector

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

By the same-side census every component vertex has exactly `2`
opposite-sign defect neighbours.  In the all-triangle `6+10` stratum the
surviving long antipodal support is `{±3,±4}` (high reduction), and
`±3` is odd, so the two long offsets `±3` already exhaust the whole
opposite-sign budget of every long vertex: there are **no** cross
opposite-sign defect edges.  A short vertex has only three opposite-sign
candidates on its own hexagon — its two cycle neighbours (triangle
edges, hence non-defect) and the antipode — so its opposite-sign defect
degree is at most `1 < 2`.  Contradiction: the whole all-triangle `6+10`
sector is impossible, with no certificate.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- **Sign-budget kill of the all-triangle 6+10 sector.**  A size-two
eigenline component whose internal graph is an all-triangle `C6 ⊔ C10`
cannot exist: long antipodal support is forced to `{±3,±4}`, which
exhausts the long opposite-sign defect budget, starving the short
vertices of their two opposite-sign defect neighbours. -/
theorem binarySquare_regular_sizeTwoPart_eight_sixTen_allTriangle_signBudget_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      3 * s x)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10)
    (v : ZMod 10 → c.supp) (hvinj : Function.Injective v)
    (hvrange : Set.range v = b.supp)
    (hv : ∀ z, (G.induce c.supp).neighborFinset (v z) =
      {v (z - 1), v (z + 1)})
    (hball : ∀ z : c.supp, z ∈ b.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0)
    (u : ZMod 6 → c.supp) (huinj : Function.Injective u)
    (hurange : Set.range u = a.supp)
    (hu : ∀ z, (G.induce c.supp).neighborFinset (u z) =
      {u (z - 1), u (z + 1)})
    (haall : ∀ z : c.supp, z ∈ a.supp →
      (triangleFreeEdgeGraph G).degree z.1 = 0) :
    False := by
  -- The surviving long antipodal support is `{±3, ±4}`.
  have hhigh :=
    binarySquare_regular_sizeTwoPart_eight_sixTen_long_allTriangle_high_support
      G hfree hreg hcard c hc s hs_in hs_out hA_in hDs a b ha hb
        v hvinj hvrange hv hball
  have hab : a ≠ b := by
    intro h
    rw [h] at ha
    rw [ha] at hb
    norm_num at hb
  -- Ambient adjacency along each cycle.
  have hvadj : ∀ z : ZMod 10, G.Adj ((v z) : V) ((v (z + 1)) : V) := by
    intro z
    have hsub : (G.induce c.supp).Adj (v z) (v (z + 1)) := by
      rw [← (G.induce c.supp).mem_neighborFinset, hv]
      simp
    exact hsub
  have huadj : ∀ z : ZMod 6, G.Adj ((u z) : V) ((u (z + 1)) : V) := by
    intro z
    have hsub : (G.induce c.supp).Adj (u z) (u (z + 1)) := by
      rw [← (G.induce c.supp).mem_neighborFinset, hu]
      simp
    exact hsub
  -- Sign alternation along each cycle.
  have hvalt : ∀ z : ZMod 10, s ((v (z + 1)) : V) = -(s ((v z) : V)) := by
    intro z
    refine (internal_alternation G hfree (by norm_num) hreg hcard c hc s
      hs_in hs_out hA_in (v z).2).2 _ ?_
    rw [componentNeighborFinset, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset]
    exact ⟨hvadj z,
      (SimpleGraph.ConnectedComponent.mem_supp_iff c _).mp (v (z + 1)).2⟩
  have hualt : ∀ z : ZMod 6, s ((u (z + 1)) : V) = -(s ((u z) : V)) := by
    intro z
    refine (internal_alternation G hfree (by norm_num) hreg hcard c hc s
      hs_in hs_out hA_in (u z).2).2 _ ?_
    rw [componentNeighborFinset, Finset.mem_filter,
      SimpleGraph.mem_neighborFinset]
    exact ⟨huadj z,
      (SimpleGraph.ConnectedComponent.mem_supp_iff c _).mp (u (z + 1)).2⟩
  -- Third-neighbour alternation on the long cycle.
  have hvalt3 : ∀ z : ZMod 10, s ((v (z + 3)) : V) = -(s ((v z) : V)) := by
    intro z
    have h1 := hvalt z
    have h2 := hvalt (z + 1)
    have h3 := hvalt (z + 2)
    rw [show z + 1 + 1 = z + 2 by ring] at h2
    rw [show z + 2 + 1 = z + 3 by ring] at h3
    omega
  -- Census input in the `(q : ℤ) - 5` form.
  have hDs' : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      (((8 : ℕ) : ℤ) - 5) * s x := by
    intro x
    rw [hDs x]
    push_cast
    ring
  -- The opposite-sign defect neighbours of a long vertex are exactly the
  -- two long `±3` offsets.
  have hlongpair : ∀ i : ZMod 10,
      ((secondOrderDefectGraph G).neighborFinset ((v i) : V)).filter
        (fun y => s y = -(s ((v i) : V))) =
      {((v (i + 3)) : V), ((v (i - 3)) : V)} := by
    intro i
    have hcen := (sameSide_defect_degree G hfree (by norm_num) hreg hcard c s
      hs_in hDs' (v i).2).2
    have hs3 : s ((v (i + 3)) : V) = -(s ((v i) : V)) := hvalt3 i
    have hs3' : s ((v (i - 3)) : V) = -(s ((v i) : V)) := by
      have h := hvalt3 (i - 3)
      rw [show i - 3 + 3 = i by ring] at h
      omega
    have hne : ((v (i + 3)) : V) ≠ ((v (i - 3)) : V) := by
      intro h
      have heq : i + 3 = i - 3 := hvinj (Subtype.ext h)
      have h37 : (3 : ZMod 10) = -3 :=
        add_left_cancel (a := i) (by rw [heq]; ring)
      exact absurd h37 (by decide)
    have hD3 : (secondOrderDefectGraph G).Adj ((v i) : V) ((v (i + 3)) : V) := by
      refine (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl ?_)
      refine (hhigh i (i + 3)).mpr ?_
      left
      ring
    have hD3' : (secondOrderDefectGraph G).Adj ((v i) : V) ((v (i - 3)) : V) := by
      refine (SimpleGraph.sup_adj _ _ _ _).mpr (Or.inl ?_)
      refine (hhigh i (i - 3)).mpr ?_
      right; right; right
      have : i - 3 - i = -3 := by ring
      rw [this]
      decide
    have hpair_sub : ({((v (i + 3)) : V), ((v (i - 3)) : V)} : Finset V) ⊆
        ((secondOrderDefectGraph G).neighborFinset ((v i) : V)).filter
          (fun y => s y = -(s ((v i) : V))) := by
      intro y hy
      rw [Finset.mem_insert, Finset.mem_singleton] at hy
      rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
      rcases hy with h | h <;> subst h
      · exact ⟨hD3, hs3⟩
      · exact ⟨hD3', hs3'⟩
    refine (Finset.eq_of_subset_of_card_le hpair_sub ?_).symm
    rw [hcen, Finset.card_pair hne]
  -- Short-cycle sign values.
  have hu1 : s ((u 1) : V) = -(s ((u 0) : V)) := by
    have h := hualt 0
    rwa [show (0 : ZMod 6) + 1 = 1 by decide] at h
  have hu2 : s ((u 2) : V) = s ((u 0) : V) := by
    have h := hualt 1
    rw [show (1 : ZMod 6) + 1 = 2 by decide] at h
    omega
  have hu3 : s ((u 3) : V) = -(s ((u 0) : V)) := by
    have h := hualt 2
    rw [show (2 : ZMod 6) + 1 = 3 by decide] at h
    omega
  have hu4 : s ((u 4) : V) = s ((u 0) : V) := by
    have h := hualt 3
    rw [show (3 : ZMod 6) + 1 = 4 by decide] at h
    omega
  have hu5 : s ((u 5) : V) = -(s ((u 0) : V)) := by
    have h := hualt 4
    rw [show (4 : ZMod 6) + 1 = 5 by decide] at h
    omega
  -- The short base vertex.
  set w : c.supp := u 0 with hw
  have hwa : w ∈ a.supp := by
    rw [← hurange]
    exact ⟨0, rfl⟩
  have hwsign : s (w : V) = -1 ∨ s (w : V) = 1 := hs_in _ w.2
  -- Coverage: every component vertex lies on one of the two cycles.
  have hcardsupp : Fintype.card c.supp = 16 := by
    have h := hc
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card] at h
    omega
  have hcover : ∀ x : c.supp, (∃ j, v j = x) ∨ (∃ k, u k = x) := by
    have himgv : (Finset.univ.image v).card = 10 := by
      rw [Finset.card_image_of_injective _ hvinj, Finset.card_univ]
      simp
    have himgu : (Finset.univ.image u).card = 6 := by
      rw [Finset.card_image_of_injective _ huinj, Finset.card_univ]
      simp
    have hdisj : Disjoint (Finset.univ.image v) (Finset.univ.image u) := by
      rw [Finset.disjoint_left]
      rintro x hx hx'
      rw [Finset.mem_image] at hx hx'
      obtain ⟨j, -, hj⟩ := hx
      obtain ⟨k, -, hk⟩ := hx'
      have hxb : x ∈ b.supp := by
        rw [← hvrange]
        exact ⟨j, hj⟩
      have hxa : x ∈ a.supp := by
        rw [← hurange]
        exact ⟨k, hk⟩
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hxa hxb
      exact hab (by rw [← hxa, ← hxb])
    have huniv : Finset.univ.image v ∪ Finset.univ.image u =
        (Finset.univ : Finset c.supp) := by
      apply Finset.eq_univ_of_card
      rw [Finset.card_union_of_disjoint hdisj, himgv, himgu, hcardsupp]
    intro x
    have hx : x ∈ Finset.univ.image v ∪ Finset.univ.image u := by
      rw [huniv]
      exact Finset.mem_univ x
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hx
    rcases hx with ⟨j, -, hj⟩ | ⟨k, -, hk⟩
    · exact Or.inl ⟨j, hj⟩
    · exact Or.inr ⟨k, hk⟩
  -- No triangle-free edges at short vertices.
  have hnotf : ∀ y : V, ¬ (triangleFreeEdgeGraph G).Adj (w : V) y := by
    intro y hadj
    have h0 := haall w hwa
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_zero] at h0
    have hmem : y ∈ (triangleFreeEdgeGraph G).neighborFinset (w : V) :=
      (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj
    rw [h0] at hmem
    exact Finset.notMem_empty _ hmem
  -- Adjacent short vertices are not defect neighbours of `w`.
  have hnoD_adj : ∀ y : V, G.Adj (w : V) y →
      ¬ (secondOrderDefectGraph G).Adj (w : V) y := by
    intro y hGadj hD
    rcases (SimpleGraph.sup_adj _ _ _ _).mp hD with hant | htf
    · rw [antipodalGraph_adj] at hant
      exact ((mem_antipodalNeighbors G _ _).mp hant).2.1 hGadj
    · exact hnotf y htf
  have hadj01 : G.Adj (w : V) ((u 1) : V) := by
    have h := huadj 0
    rwa [show (0 : ZMod 6) + 1 = 1 by decide] at h
  have hadj05 : G.Adj (w : V) ((u 5) : V) := by
    have h := huadj 5
    rw [show (5 : ZMod 6) + 1 = 0 by decide] at h
    exact h.symm
  -- The opposite-sign defect neighbours of `w` land in the singleton `{u 3}`.
  have hsub : ((secondOrderDefectGraph G).neighborFinset (w : V)).filter
      (fun y => s y = -(s (w : V))) ⊆ {((u 3) : V)} := by
    intro y hy
    rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset] at hy
    obtain ⟨hDwy, hsy⟩ := hy
    have hyc : y ∈ c.supp := defect_neighbor_mem_supp G c w.2 hDwy
    rcases hcover ⟨y, hyc⟩ with ⟨j, hj⟩ | ⟨k, hk⟩
    · -- Long side: `w` would be a `±3` long offset, impossible.
      exfalso
      have hyv : ((v j) : V) = y := by rw [hj]
      have hD' : (secondOrderDefectGraph G).Adj ((v j) : V) (w : V) := by
        rw [hyv]
        exact hDwy.symm
      have hsw : s (w : V) = -(s ((v j) : V)) := by
        rw [hyv]
        omega
      have hmem : (w : V) ∈
          ((secondOrderDefectGraph G).neighborFinset ((v j) : V)).filter
            (fun y => s y = -(s ((v j) : V))) := by
        rw [Finset.mem_filter, SimpleGraph.mem_neighborFinset]
        exact ⟨hD', hsw⟩
      rw [hlongpair j, Finset.mem_insert, Finset.mem_singleton] at hmem
      have hwb : w ∈ b.supp := by
        rcases hmem with h | h
        · rw [← hvrange]
          exact ⟨j + 3, Subtype.ext h.symm⟩
        · rw [← hvrange]
          exact ⟨j - 3, Subtype.ext h.symm⟩
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hwa hwb
      exact hab (by rw [← hwa, ← hwb])
    · -- Short side: only the antipode `u 3` survives.
      have hyu : ((u k) : V) = y := by rw [hk]
      have hk6 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 :=
        (by decide :
          ∀ m : ZMod 6, m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5) k
      rcases hk6 with h | h | h | h | h | h <;> subst h
      · -- `y = w`: a defect loop / sign clash.
        exfalso
        rw [← hyu] at hsy
        rw [← hw] at hsy
        omega
      · exfalso
        rw [← hyu] at hDwy
        exact hnoD_adj _ hadj01 hDwy
      · exfalso
        rw [← hyu] at hsy
        omega
      · rw [Finset.mem_singleton, ← hyu]
      · exfalso
        rw [← hyu] at hsy
        omega
      · exfalso
        rw [← hyu] at hDwy
        exact hnoD_adj _ hadj05 hDwy
  -- The census demands two opposite-sign defect neighbours: contradiction.
  have hcen := (sameSide_defect_degree G hfree (by norm_num) hreg hcard c s
    hs_in hDs' w.2).2
  have hle := Finset.card_le_card hsub
  rw [hcen, Finset.card_singleton] at hle
  omega

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_sixTen_allTriangle_signBudget_false
