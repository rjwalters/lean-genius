import Proofs.Erdos85SizeTwoEigenlineGridInstantiation

/-!
# Parity and minimum order of internal size-two cycles

Node: `SIZE-TWO-EIGENLINE(q)` beneath outline F.3.

The alternating eigenline flips sign across every edge of the internal
ambient two-factor.  Closing an internal cycle therefore forces its length
to be even.  Together with simplicity and the C4 exclusion, every such cycle
has at least six vertices.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every internal ambient cycle supporting the alternating eigenline has
even order and at least six vertices. -/
theorem binarySquare_regular_sizeTwoPart_internalCycle_even_six_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (a : (G.induce c.supp).ConnectedComponent) :
    Even a.supp.ncard ∧ 6 ≤ a.supp.ncard := by
  obtain ⟨x, p, hp, hpverts, _hpgraph, hlen4, _hdistanceTwo⟩ :=
    binarySquare_regular_sizeTwoPart_exists_cycle_of_internalComponent
      G hfree hq hreg hcard c hc a
  have hplen : p.length = a.supp.ncard := by
    calc
      p.length = Nat.card p.toSubgraph.verts :=
        (isCycle_card_verts_eq_length hp).symm
      _ = p.toSubgraph.verts.ncard := Nat.card_coe_set_eq _
      _ = a.supp.ncard := congrArg Set.ncard hpverts
  have hflip : ∀ i : ℕ, i < p.length →
      s (p.getVert (i + 1)).1 = -s (p.getVert i).1 := by
    intro i hi
    have hadj : G.Adj (p.getVert i).1 (p.getVert (i + 1)).1 := by
      simpa using p.adj_getVert_succ hi
    have hmem : (p.getVert (i + 1)).1 ∈
        componentNeighborFinset G (secondOrderDefectGraph G) c
          (p.getVert i).1 := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hadj,
        (ConnectedComponent.mem_supp_iff c _).mp (p.getVert (i + 1)).2⟩
    exact (internal_alternation G hfree hq hreg hcard c hc s hs_in hs_out
      hA_in (p.getVert i).2).2 _ hmem
  have hsign : ∀ i : ℕ, i ≤ p.length →
      s (p.getVert i).1 = (-1 : ℤ) ^ i * s (p.getVert 0).1 := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        rw [hflip i (by omega), ih (by omega), pow_succ]
        ring
  have hclosed := hsign p.length (le_refl _)
  rw [p.getVert_length] at hclosed
  have hclosed' : s (p.getVert 0).1 =
      (-1 : ℤ) ^ p.length * s (p.getVert 0).1 := by
    simpa using hclosed
  have hpow : (-1 : ℤ) ^ p.length = 1 := by
    rcases hs_in (p.getVert 0).1 (p.getVert 0).2 with hs | hs
    · rw [hs] at hclosed'
      nlinarith
    · rw [hs] at hclosed'
      nlinarith
  have hevenLength : Even p.length :=
    (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℤ) ≠ 1)).mp hpow
  have hsixLength : 6 ≤ p.length := by
    obtain ⟨k, hk⟩ := hevenLength
    have hthree := hp.three_le_length
    omega
  exact ⟨by simpa [← hplen] using hevenLength, by simpa [← hplen] using hsixLength⟩

/-- At order 64, two distinct internal cycles exhaust a normalized size-two
component.  Their only possible ordered size pairs are `(6,10)`, `(10,6)`,
and `(8,8)`. -/
theorem binarySquare_regular_sizeTwoPart_eight_internalCycle_pair_sizes
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
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (a b : (G.induce c.supp).ConnectedComponent) (hab : a ≠ b) :
    (a.supp.ncard = 6 ∧ b.supp.ncard = 10) ∨
      (a.supp.ncard = 10 ∧ b.supp.ncard = 6) ∨
      (a.supp.ncard = 8 ∧ b.supp.ncard = 8) := by
  classical
  let H := G.induce c.supp
  have hcycle (d : H.ConnectedComponent) :
      Even d.supp.ncard ∧ 6 ≤ d.supp.ncard :=
    binarySquare_regular_sizeTwoPart_internalCycle_even_six_le
      G hfree (by omega) hreg hcard c hc s hs_in hs_out hA_in d
  have hsum : (∑ d : H.ConnectedComponent, d.supp.ncard) = 16 := by
    calc
      (∑ d : H.ConnectedComponent, d.supp.ncard) = Fintype.card c.supp :=
        sum_connectedComponent_supp_ncard H
      _ = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
      _ = 16 := by omega
  have hcardComp : Fintype.card H.ConnectedComponent ≤ 2 := by
    have hlower : 6 * Fintype.card H.ConnectedComponent ≤
        ∑ d : H.ConnectedComponent, d.supp.ncard := by
      calc
        6 * Fintype.card H.ConnectedComponent =
            ∑ _d : H.ConnectedComponent, 6 := by simp [Nat.mul_comm]
        _ ≤ ∑ d : H.ConnectedComponent, d.supp.ncard := by
          apply Finset.sum_le_sum
          intro d _
          exact (hcycle d).2
    omega
  have hcases (d : H.ConnectedComponent) : d = a ∨ d = b := by
    by_contra hd
    push Not at hd
    have hthree : 3 ≤ Fintype.card H.ConnectedComponent := by
      calc
        3 = ({a, b, d} : Finset H.ConnectedComponent).card := by
          simp [hab, hd.1.symm, hd.2.symm]
        _ ≤ (Finset.univ : Finset H.ConnectedComponent).card :=
          Finset.card_le_card (by simp)
        _ = Fintype.card H.ConnectedComponent := Finset.card_univ
    omega
  have huniv : (Finset.univ : Finset H.ConnectedComponent) = {a, b} := by
    ext d
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
      true_iff]
    exact hcases d
  rw [huniv, Finset.sum_insert (by simpa using hab), Finset.sum_singleton] at hsum
  obtain ⟨ka, hka⟩ := (hcycle a).1
  obtain ⟨kb, hkb⟩ := (hcycle b).1
  rcases (hcycle a).2 with ha6
  rcases (hcycle b).2 with hb6
  omega

end


end Erdos85

#print axioms Erdos85.binarySquare_regular_sizeTwoPart_internalCycle_even_six_le
#print axioms Erdos85.binarySquare_regular_sizeTwoPart_eight_internalCycle_pair_sizes
