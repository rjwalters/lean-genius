import Proofs.Erdos85SquareMinimumLayerSqueeze
import Proofs.Erdos85OddComponentClosure

/-!
# The mass-two escape from the square minimum squeeze

The strongest residual configurations in the minimum-layer moment bound put
exactly two units of quotient row mass into strictly larger components.  Since
every positive minimum-to-larger entry is at least two, this forces a unique
larger target, with quotient entry two and target order exactly twice the
minimum order.  This file isolates that conclusion for use by mixed-parity
and cyclic-cover arguments.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- A finite family of naturals with total two, in which every positive term
is at least two, has a unique nonzero term and that term equals two. -/
theorem existsUnique_eq_two_of_sum_eq_two_of_pos_ge_two
    {I : Type*} [DecidableEq I]
    (S : Finset I) (q : I → ℕ)
    (hsum : ∑ i ∈ S, q i = 2)
    (hgap : ∀ i ∈ S, 0 < q i → 2 ≤ q i) :
    ∃! i, i ∈ S ∧ q i = 2 := by
  have hne : ∑ i ∈ S, q i ≠ 0 := by omega
  obtain ⟨i, hiS, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hiLe : q i ≤ ∑ j ∈ S, q j :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hiS
  have hiPos : 0 < q i := Nat.pos_of_ne_zero hi0
  have hiEq : q i = 2 := by
    have := hgap i hiS hiPos
    omega
  refine ⟨i, ⟨hiS, hiEq⟩, ?_⟩
  intro j hj
  have hjPos : 0 < q j := by omega
  have hjEq : q j = 2 := by
    have hjLe : q j ≤ ∑ k ∈ S, q k :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hj.1
    have := hgap j hj.1 hjPos
    omega
  by_contra hji
  have hjErase : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hji, hj.1⟩
  have hrestLe : q j ≤ ∑ k ∈ S.erase i, q k :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hjErase
  have hsplit : (∑ k ∈ S.erase i, q k) + q i = ∑ k ∈ S, q k := by
    rw [Finset.sum_erase_add _ _ hiS]
  rw [hiEq, hsum] at hsplit
  omega

/-- A globally oriented degree-two cyclic cover is invariant under the
half-turn of its source cycle.  This identifies the deck involution without
choosing either global orientation. -/
theorem cycleCoverMap_halfTurn_invariant
    {r : ℕ} [NeZero r]
    (f : ZMod (2 * r) → ZMod r)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1)) :
    ∀ y, f (y + (r : ZMod (2 * r))) = f y := by
  intro y
  rcases horient with hforward | hreverse
  · have hind : ∀ k : ℕ,
        f (y + (k : ZMod (2 * r))) = f y + (k : ZMod r) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Nat.cast_succ, show y + ((k : ZMod (2 * r)) + 1) =
            (y + (k : ZMod (2 * r))) + 1 by ring, hforward, ih,
            Nat.cast_succ]
          ring
    have hr := hind r
    rw [ZMod.natCast_self] at hr
    simpa using hr
  · have hind : ∀ k : ℕ,
        f (y + (k : ZMod (2 * r))) = f y - (k : ZMod r) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Nat.cast_succ, show y + ((k : ZMod (2 * r)) + 1) =
            (y + (k : ZMod (2 * r))) + 1 by ring, hreverse, ih,
            Nat.cast_succ]
          ring
    have hr := hind r
    rw [ZMod.natCast_self] at hr
    simpa using hr

/-- The two antipodal target vertices of an oriented double cover have
identical neighbours in the source cycle. -/
theorem cycleCover_adjacency_halfTurn_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ZMod r → V) (v : ZMod (2 * r) → V)
    (f : ZMod (2 * r) → ZMod r)
    (hadj : ∀ x y, G.Adj (u x) (v y) ↔ x = f y)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1)) :
    ∀ x y, G.Adj (u x) (v (y + (r : ZMod (2 * r)))) ↔
      G.Adj (u x) (v y) := by
  intro x y
  rw [hadj, hadj, cycleCoverMap_halfTurn_invariant f horient y]

/-- **Unique double-cover escape.**  If the total quotient row mass from a
minimum defect component to longer components is two, there is a unique such
component.  Its forward quotient entry is two, its reverse entry is one, and
its order is twice the minimum order (hence even). -/
theorem secondOrder_minimum_mass_two_unique_doubleCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ l.supp.ncard)
    (hmass :
      (∑ e ∈ Finset.univ.filter
          (fun e : (secondOrderDefectGraph G).ConnectedComponent ↦
            c.supp.ncard < e.supp.ncard),
        componentQuotientMatrix G (secondOrderDefectGraph G) c e) = 2) :
    ∃! e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard < e.supp.ncard ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c e = 2 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e c = 1 ∧
      e.supp.ncard = 2 * c.supp.ncard ∧ Even e.supp.ncard := by
  let D := secondOrderDefectGraph G
  let Q := componentQuotientMatrix G D
  let L : Finset D.ConnectedComponent :=
    Finset.univ.filter (fun e ↦ c.supp.ncard < e.supp.ncard)
  have hgap : ∀ e ∈ L, 0 < Q c e → 2 ≤ Q c e := by
    intro e heL hpos
    have hlt : c.supp.ncard < e.supp.ncard :=
      (Finset.mem_filter.mp heL).2
    have hs := secondOrder_componentQuotientMatrix_entries_of_size_lt
      G hfree hd heven hmin hcard c e hlt hpos
    by_contra hnot
    have hqOne : Q c e = 1 := by omega
    have hqOne' : componentQuotientMatrix G
        (secondOrderDefectGraph G) c e = 1 := by
      simpa [Q, D] using hqOne
    rw [hqOne', mul_one] at hs
    omega
  have hmass' : ∑ e ∈ L, Q c e = 2 := by simpa [L, Q, D] using hmass
  obtain ⟨e, he, heUnique⟩ :=
    existsUnique_eq_two_of_sum_eq_two_of_pos_ge_two L (fun x ↦ Q c x)
      hmass' hgap
  have heLt : c.supp.ncard < e.supp.ncard :=
    (Finset.mem_filter.mp he.1).2
  have hePos : 0 < Q c e := by omega
  have hs := secondOrder_minimumComponent_longer_edge_structure
    G hfree hd heven hmin hcard c e hcmin heLt hePos
  have heQ : componentQuotientMatrix G
      (secondOrderDefectGraph G) c e = 2 := by
    simpa [Q, D] using he.2
  have heSize : e.supp.ncard = 2 * c.supp.ncard := by
    have hprod := hs.2.2.1
    rw [heQ] at hprod
    omega
  have heEven : Even e.supp.ncard := by
    rw [heSize]
    exact even_two_mul _
  refine ⟨e, ⟨heLt, heQ, hs.1, heSize, heEven⟩, ?_⟩
  intro j hj
  apply heUnique
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.1⟩, hj.2.1⟩

end

end Erdos85
