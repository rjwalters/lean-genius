import Proofs.Erdos85SquareMinimumLayerSqueeze
import Proofs.Erdos85OddComponentClosure
import Proofs.Erdos85SquareQuotientGraphBound

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

/-- The analogous quantization at total mass three: since two positive
terms would already contribute at least four, there is a unique nonzero
term and it equals three. -/
theorem existsUnique_eq_three_of_sum_eq_three_of_pos_ge_two
    {I : Type*} [DecidableEq I]
    (S : Finset I) (q : I → ℕ)
    (hsum : ∑ i ∈ S, q i = 3)
    (hgap : ∀ i ∈ S, 0 < q i → 2 ≤ q i) :
    ∃! i, i ∈ S ∧ q i = 3 := by
  have hne : ∑ i ∈ S, q i ≠ 0 := by omega
  obtain ⟨i, hiS, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hiLe : q i ≤ ∑ j ∈ S, q j :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hiS
  have hiPos : 0 < q i := Nat.pos_of_ne_zero hi0
  have hiTwo : 2 ≤ q i := hgap i hiS hiPos
  have hrest : ∑ j ∈ S.erase i, q j + q i = 3 := by
    rw [Finset.sum_erase_add _ _ hiS, hsum]
  have hiEq : q i = 3 := by
    by_contra hneThree
    have hiEqTwo : q i = 2 := by omega
    have hrestOne : ∑ j ∈ S.erase i, q j = 1 := by omega
    have hrestNe : ∑ j ∈ S.erase i, q j ≠ 0 := by omega
    obtain ⟨j, hjS, hj0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hrestNe
    have hjPos : 0 < q j := Nat.pos_of_ne_zero hj0
    have hjInS : j ∈ S := Finset.mem_of_mem_erase hjS
    have hjTwo : 2 ≤ q j := hgap j hjInS hjPos
    have hjLe : q j ≤ ∑ k ∈ S.erase i, q k :=
      Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hjS
    omega
  refine ⟨i, ⟨hiS, hiEq⟩, ?_⟩
  intro j hj
  by_contra hji
  have hjErase : j ∈ S.erase i := Finset.mem_erase.mpr ⟨hji, hj.1⟩
  have hjLe : q j ≤ ∑ k ∈ S.erase i, q k :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hjErase
  rw [hiEq] at hrest
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

/-- Apart from their common source-cycle neighbour, the two vertices in a
deck-involution fiber cannot have another common neighbour in a `C4`-free
graph.  This is the local exclusivity input needed by parity arguments on the
even target cycle. -/
theorem cycleCover_halfTurn_commonNeighbor_exclusive
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ZMod r → V) (v : ZMod (2 * r) → V)
    (hvinj : Function.Injective v)
    (f : ZMod (2 * r) → ZMod r)
    (hadj : ∀ x y, G.Adj (u x) (v y) ↔ x = f y)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1))
    (y : ZMod (2 * r)) (w : V) (hw : w ≠ u (f y)) :
    ¬ (G.Adj w (v y) ∧
      G.Adj w (v (y + (r : ZMod (2 * r))))) := by
  intro hboth
  have hrPos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hrCast : (r : ZMod (2 * r)) ≠ 0 := by
    intro hz
    have hdvd : 2 * r ∣ r :=
      (ZMod.natCast_eq_zero_iff r (2 * r)).mp hz
    have hle : 2 * r ≤ r := Nat.le_of_dvd hrPos hdvd
    omega
  have hyShift : y ≠ y + (r : ZMod (2 * r)) := by
    intro heq
    apply hrCast
    have := congrArg (fun z : ZMod (2 * r) ↦ z - y) heq
    simpa using this.symm
  have hvNe : v y ≠ v (y + (r : ZMod (2 * r))) :=
    hvinj.ne hyShift
  have hsrcY : G.Adj (u (f y)) (v y) :=
    (hadj (f y) y).mpr rfl
  have hsrcShift : G.Adj (u (f y))
      (v (y + (r : ZMod (2 * r)))) := by
    apply (hadj (f y) (y + (r : ZMod (2 * r)))).mpr
    exact (cycleCoverMap_halfTurn_invariant f horient y).symm
  exact hfree (containsC4_of_two_common hvNe hw hboth.1 hboth.2
    hsrcY hsrcShift)

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

/-- **Mass-three quantization.**  Total minimum-to-larger row mass three is
a unique triple cover.  Since a minimum component has odd order, the target
order is odd as well. -/
theorem secondOrder_minimum_mass_three_unique_tripleCover
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
        componentQuotientMatrix G (secondOrderDefectGraph G) c e) = 3) :
    ∃! e : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard < e.supp.ncard ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) c e = 3 ∧
      componentQuotientMatrix G (secondOrderDefectGraph G) e c = 1 ∧
      e.supp.ncard = 3 * c.supp.ncard ∧ Odd e.supp.ncard := by
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
  have hmass' : ∑ e ∈ L, Q c e = 3 := by simpa [L, Q, D] using hmass
  obtain ⟨e, he, heUnique⟩ :=
    existsUnique_eq_three_of_sum_eq_three_of_pos_ge_two L (fun x ↦ Q c x)
      hmass' hgap
  have heLt : c.supp.ncard < e.supp.ncard :=
    (Finset.mem_filter.mp he.1).2
  have hePos : 0 < Q c e := by omega
  have hs := secondOrder_minimumComponent_longer_edge_structure
    G hfree hd heven hmin hcard c e hcmin heLt hePos
  have heQ : componentQuotientMatrix G
      (secondOrderDefectGraph G) c e = 3 := by
    simpa [Q, D] using he.2
  have heSize : e.supp.ncard = 3 * c.supp.ncard := by
    have hprod := hs.2.2.1
    rw [heQ] at hprod
    omega
  have hcOdd := secondOrder_minimumComponent_order_odd
    G hfree hd heven hmin hcard c hcmin
  have heOdd : Odd e.supp.ncard := by
    rw [heSize, Nat.odd_mul]
    exact ⟨by decide, hcOdd⟩
  refine ⟨e, ⟨heLt, heQ, hs.1, heSize, heOdd⟩, ?_⟩
  intro j hj
  apply heUnique
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.1⟩, hj.2.1⟩

/-- In the exact-square family, the mass-three case already lies strictly
below the one-third wedge: its unique target is odd and has normalized order
`3a`, so the strict odd-component bound applies. -/
theorem secondOrder_square_minimum_mass_three_lt_third
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d p N s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hp : p.Prime) (hp7 : 7 ≤ p)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hdEq : d = s * s + 3) (hpEq : p = d + s) (hNEq : N = d - s)
    (hall : ∀ e : (secondOrderDefectGraph G).ConnectedComponent,
      p ∣ e.supp.ncard)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ l.supp.ncard)
    (hmass :
      (∑ e ∈ Finset.univ.filter
          (fun e : (secondOrderDefectGraph G).ConnectedComponent ↦
            c.supp.ncard < e.supp.ncard),
        componentQuotientMatrix G (secondOrderDefectGraph G) c e) = 3) :
    3 * (c.supp.ncard / p) < s := by
  obtain ⟨e, he, _⟩ := secondOrder_minimum_mass_three_unique_tripleCover
    G hfree hd heven hmin hcard c hcmin hmass
  have heBound := secondOrder_odd_square_coefficient_lt_root
    G hfree hd heven hmin hcard hp hp7 hboundary hdEq hpEq hNEq hall
      e he.2.2.2.2
  have hpPos : 0 < p := hp.pos
  have hcSize : c.supp.ncard = p * (c.supp.ncard / p) :=
    (Nat.mul_div_cancel' (hall c)).symm
  have heSize : e.supp.ncard = p * (e.supp.ncard / p) :=
    (Nat.mul_div_cancel' (hall e)).symm
  have hcoeff : e.supp.ncard / p = 3 * (c.supp.ncard / p) := by
    apply Nat.eq_of_mul_eq_mul_left hpPos
    calc
      p * (e.supp.ncard / p) = e.supp.ncard := heSize.symm
      _ = 3 * c.supp.ncard := he.2.2.2.1
      _ = 3 * (p * (c.supp.ncard / p)) :=
        congrArg (fun n : ℕ ↦ 3 * n) hcSize
      _ = p * (3 * (c.supp.ncard / p)) :=
        Nat.mul_left_comm 3 p (c.supp.ncard / p)
  rwa [hcoeff] at heBound

end

end Erdos85
