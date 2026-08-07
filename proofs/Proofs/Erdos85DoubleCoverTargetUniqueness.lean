import Proofs.Erdos85SquareMinimumDoubleCoverEscape

/-!
# A cyclic double-cover target has a unique source component

If a cycle of order `2r` were a cyclic double-cover target of two disjoint
cycles of order `r`, each antipodal pair in the target would have one common
neighbor in each source.  Those two distinct common neighbors form a
four-cycle with the antipodal pair.  This packages that observation using
`cycleCover_halfTurn_commonNeighbor_exclusive`.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- A globally oriented cyclic cover repeats after one full turn of its
source cycle, independently of the target modulus. -/
theorem cycleCoverMap_sourcePeriod_invariant
    {r n : ℕ} [NeZero r]
    (f : ZMod n → ZMod r)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1)) :
    ∀ y, f (y + (r : ZMod n)) = f y := by
  intro y
  rcases horient with hforward | hreverse
  · have hind : ∀ k : ℕ,
        f (y + (k : ZMod n)) = f y + (k : ZMod r) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Nat.cast_succ, show y + ((k : ZMod n) + 1) =
            (y + (k : ZMod n)) + 1 by ring, hforward, ih,
            Nat.cast_succ]
          ring
    have hr := hind r
    rw [ZMod.natCast_self] at hr
    simpa using hr
  · have hind : ∀ k : ℕ,
        f (y + (k : ZMod n)) = f y - (k : ZMod r) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          rw [Nat.cast_succ, show y + ((k : ZMod n) + 1) =
            (y + (k : ZMod n)) + 1 by ring, hreverse, ih,
            Nat.cast_succ]
          ring
    have hr := hind r
    rw [ZMod.natCast_self] at hr
    simpa using hr

/-- **Two disjoint source cycles cannot cover one proper multiple target.** -/
theorem false_of_two_disjoint_cycleCovers_same_multipleTarget
    {V : Type*} [Fintype V] [DecidableEq V]
    {r m : ℕ} [NeZero r] (hm2 : 2 ≤ m)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u₁ u₂ : ZMod r → V) (v : ZMod (m * r) → V)
    (hvinj : Function.Injective v)
    (hdisjoint : ∀ x z, u₁ x ≠ u₂ z)
    (f₁ f₂ : ZMod (m * r) → ZMod r)
    (hadj₁ : ∀ x y, G.Adj (u₁ x) (v y) ↔ x = f₁ y)
    (hadj₂ : ∀ x y, G.Adj (u₂ x) (v y) ↔ x = f₂ y)
    (horient₁ : (∀ y, f₁ (y + 1) = f₁ y + 1) ∨
      (∀ y, f₁ (y + 1) = f₁ y - 1))
    (horient₂ : (∀ y, f₂ (y + 1) = f₂ y + 1) ∨
      (∀ y, f₂ (y + 1) = f₂ y - 1)) : False := by
  let y : ZMod (m * r) := 0
  have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hrCast : (r : ZMod (m * r)) ≠ 0 := by
    intro hz
    have hdvd : m * r ∣ r := (ZMod.natCast_eq_zero_iff r (m * r)).mp hz
    have hle : m * r ≤ r := Nat.le_of_dvd hrpos hdvd
    nlinarith
  have hyShift : y ≠ y + (r : ZMod (m * r)) := by
    intro heq
    apply hrCast
    have := congrArg (fun z : ZMod (m * r) ↦ z - y) heq
    simpa using this.symm
  have hvNe : v y ≠ v (y + (r : ZMod (m * r))) :=
    hvinj.ne hyShift
  have hsourceNe : u₂ (f₂ y) ≠ u₁ (f₁ y) :=
    (hdisjoint (f₁ y) (f₂ y)).symm
  have h₂y : G.Adj (u₂ (f₂ y)) (v y) :=
    (hadj₂ (f₂ y) y).mpr rfl
  have h₂shift : G.Adj (u₂ (f₂ y))
      (v (y + (r : ZMod (m * r)))) := by
    apply (hadj₂ (f₂ y) (y + (r : ZMod (m * r)))).mpr
    exact (cycleCoverMap_sourcePeriod_invariant f₂ horient₂ y).symm
  have h₁y : G.Adj (u₁ (f₁ y)) (v y) :=
    (hadj₁ (f₁ y) y).mpr rfl
  have h₁shift : G.Adj (u₁ (f₁ y))
      (v (y + (r : ZMod (m * r)))) := by
    apply (hadj₁ (f₁ y) (y + (r : ZMod (m * r)))).mpr
    exact (cycleCoverMap_sourcePeriod_invariant f₁ horient₁ y).symm
  exact hfree (containsC4_of_two_common hvNe hsourceNe h₂y h₂shift
    h₁y h₁shift)

/-- Modulus-transport form of the multiple-target obstruction. -/
theorem false_of_two_disjoint_cycleCovers_same_multipleTarget_of_moduli
    {V : Type*} [Fintype V] [DecidableEq V]
    {r₁ r₂ n m : ℕ} [NeZero r₁]
    (hm2 : 2 ≤ m) (hr : r₂ = r₁) (hn : n = m * r₁)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u₁ : ZMod r₁ → V) (u₂ : ZMod r₂ → V) (v : ZMod n → V)
    (hvinj : Function.Injective v)
    (hdisjoint : ∀ x z, u₁ x ≠ u₂ z)
    (f₁ : ZMod n → ZMod r₁) (f₂ : ZMod n → ZMod r₂)
    (hadj₁ : ∀ x y, G.Adj (u₁ x) (v y) ↔ x = f₁ y)
    (hadj₂ : ∀ x y, G.Adj (u₂ x) (v y) ↔ x = f₂ y)
    (horient₁ : (∀ y, f₁ (y + 1) = f₁ y + 1) ∨
      (∀ y, f₁ (y + 1) = f₁ y - 1))
    (horient₂ : (∀ y, f₂ (y + 1) = f₂ y + 1) ∨
      (∀ y, f₂ (y + 1) = f₂ y - 1)) : False := by
  subst r₂
  subst n
  exact false_of_two_disjoint_cycleCovers_same_multipleTarget hm2 G hfree
    u₁ u₂ v hvinj hdisjoint f₁ f₂ hadj₁ hadj₂ horient₁ horient₂

/-- **Two disjoint cycles cannot cover the same doubled target.** -/
theorem false_of_two_disjoint_cycleCovers_same_doubleTarget
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u₁ u₂ : ZMod r → V) (v : ZMod (2 * r) → V)
    (hvinj : Function.Injective v)
    (hdisjoint : ∀ x z, u₁ x ≠ u₂ z)
    (f₁ f₂ : ZMod (2 * r) → ZMod r)
    (hadj₁ : ∀ x y, G.Adj (u₁ x) (v y) ↔ x = f₁ y)
    (hadj₂ : ∀ x y, G.Adj (u₂ x) (v y) ↔ x = f₂ y)
    (horient₁ : (∀ y, f₁ (y + 1) = f₁ y + 1) ∨
      (∀ y, f₁ (y + 1) = f₁ y - 1))
    (horient₂ : (∀ y, f₂ (y + 1) = f₂ y + 1) ∨
      (∀ y, f₂ (y + 1) = f₂ y - 1)) : False := by
  let y : ZMod (2 * r) := 0
  let w : V := u₂ (f₂ y)
  have hw : w ≠ u₁ (f₁ y) := by
    exact (hdisjoint (f₁ y) (f₂ y)).symm
  have hexclusive := cycleCover_halfTurn_commonNeighbor_exclusive
    G hfree u₁ v hvinj f₁ hadj₁ horient₁ y w hw
  apply hexclusive
  constructor
  · exact (hadj₂ (f₂ y) y).mpr rfl
  · apply (hadj₂ (f₂ y) (y + (r : ZMod (2 * r)))).mpr
    exact (cycleCoverMap_halfTurn_invariant f₂ horient₂ y).symm

/-- **Graph-facing uniqueness of the source of a doubled target.**  Two
distinct defect components of order `r` cannot both have reverse quotient
entry one from the same defect component labeled by `ZMod (2*r)`. -/
theorem secondOrder_doubleCover_target_source_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 3 ≤ r)
    (c₁ c₂ e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcne : c₁ ≠ c₂)
    (u₁ u₂ : ZMod r → V) (v : ZMod (2 * r) → V)
    (hu₁ : Function.Injective u₁) (hu₂ : Function.Injective u₂)
    (hv : Function.Injective v)
    (hu₁Range : Set.range u₁ = c₁.supp)
    (hu₂Range : Set.range u₂ = c₂.supp)
    (hvRange : Set.range v = e.supp)
    (hu₁D : ∀ x, (secondOrderDefectGraph G).neighborFinset (u₁ x) =
      {u₁ (x - 1), u₁ (x + 1)})
    (hu₂D : ∀ x, (secondOrderDefectGraph G).neighborFinset (u₂ x) =
      {u₂ (x - 1), u₂ (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)})
    (hone₁ : componentQuotientMatrix G (secondOrderDefectGraph G) e c₁ = 1)
    (hone₂ : componentQuotientMatrix G (secondOrderDefectGraph G) e c₂ = 1) :
    False := by
  letI : NeZero (2 * r) := ⟨by
    have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
    omega⟩
  have htwoR : 3 ≤ 2 * r := by omega
  obtain ⟨f₁, hadj₁, horient₁⟩ :=
    exists_cycleCoverMap_of_componentQuotient_eq_one
      G hfree hd heven hmin hcard hr htwoR c₁ e u₁ v hu₁ hv
        hu₁Range hvRange hu₁D hvD hone₁
  obtain ⟨f₂, hadj₂, horient₂⟩ :=
    exists_cycleCoverMap_of_componentQuotient_eq_one
      G hfree hd heven hmin hcard hr htwoR c₂ e u₂ v hu₂ hv
        hu₂Range hvRange hu₂D hvD hone₂
  have hdisjoint : ∀ x z, u₁ x ≠ u₂ z := by
    intro x z hxz
    have hx₁ : u₁ x ∈ c₁.supp := by
      rw [← hu₁Range]
      exact ⟨x, rfl⟩
    have hz₂ : u₂ z ∈ c₂.supp := by
      rw [← hu₂Range]
      exact ⟨z, rfl⟩
    have hc₁ : (secondOrderDefectGraph G).connectedComponentMk (u₁ x) = c₁ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c₁ (u₁ x)).mp hx₁
    have hc₂ : (secondOrderDefectGraph G).connectedComponentMk (u₂ z) = c₂ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c₂ (u₂ z)).mp hz₂
    apply hcne
    rw [hxz] at hc₁
    exact hc₁.symm.trans hc₂
  exact false_of_two_disjoint_cycleCovers_same_doubleTarget
    G hfree u₁ u₂ v hv hdisjoint f₁ f₂ hadj₁ hadj₂ horient₁ horient₂

/-- **Graph-facing uniqueness for every proper cyclic-cover target.** -/
theorem secondOrder_multipleCover_target_source_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r m : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 3 ≤ r) (hm2 : 2 ≤ m)
    (c₁ c₂ e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcne : c₁ ≠ c₂)
    (u₁ u₂ : ZMod r → V) (v : ZMod (m * r) → V)
    (hu₁ : Function.Injective u₁) (hu₂ : Function.Injective u₂)
    (hv : Function.Injective v)
    (hu₁Range : Set.range u₁ = c₁.supp)
    (hu₂Range : Set.range u₂ = c₂.supp)
    (hvRange : Set.range v = e.supp)
    (hu₁D : ∀ x, (secondOrderDefectGraph G).neighborFinset (u₁ x) =
      {u₁ (x - 1), u₁ (x + 1)})
    (hu₂D : ∀ x, (secondOrderDefectGraph G).neighborFinset (u₂ x) =
      {u₂ (x - 1), u₂ (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)})
    (hone₁ : componentQuotientMatrix G (secondOrderDefectGraph G) e c₁ = 1)
    (hone₂ : componentQuotientMatrix G (secondOrderDefectGraph G) e c₂ = 1) :
    False := by
  letI : NeZero (m * r) := ⟨by
    have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
    nlinarith⟩
  have hmr : 3 ≤ m * r := by nlinarith
  obtain ⟨f₁, hadj₁, horient₁⟩ :=
    exists_cycleCoverMap_of_componentQuotient_eq_one
      G hfree hd heven hmin hcard hr hmr c₁ e u₁ v hu₁ hv
        hu₁Range hvRange hu₁D hvD hone₁
  obtain ⟨f₂, hadj₂, horient₂⟩ :=
    exists_cycleCoverMap_of_componentQuotient_eq_one
      G hfree hd heven hmin hcard hr hmr c₂ e u₂ v hu₂ hv
        hu₂Range hvRange hu₂D hvD hone₂
  have hdisjoint : ∀ x z, u₁ x ≠ u₂ z := by
    intro x z hxz
    have hx₁ : u₁ x ∈ c₁.supp := by
      rw [← hu₁Range]
      exact ⟨x, rfl⟩
    have hz₂ : u₂ z ∈ c₂.supp := by
      rw [← hu₂Range]
      exact ⟨z, rfl⟩
    have hc₁ : (secondOrderDefectGraph G).connectedComponentMk (u₁ x) = c₁ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c₁ (u₁ x)).mp hx₁
    have hc₂ : (secondOrderDefectGraph G).connectedComponentMk (u₂ z) = c₂ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c₂ (u₂ z)).mp hz₂
    apply hcne
    rw [hxz] at hc₁
    exact hc₁.symm.trans hc₂
  exact false_of_two_disjoint_cycleCovers_same_multipleTarget
    hm2 G hfree u₁ u₂ v hv hdisjoint f₁ f₂ hadj₁ hadj₂ horient₁ horient₂

/-- **Intrinsic quotient formulation.**  A component strictly larger than
the minimum order is quotient-adjacent to at most one minimum component.
No cyclic labeling data is required from the caller. -/
theorem secondOrder_minimum_largerTarget_source_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₁ c₂ e : (secondOrderDefectGraph G).ConnectedComponent)
    (hc₁min : ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
      c₁.supp.ncard ≤ l.supp.ncard)
    (hsame : c₂.supp.ncard = c₁.supp.ncard)
    (hlt : c₁.supp.ncard < e.supp.ncard)
    (hpos₁ : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) c₁ e)
    (hpos₂ : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) c₂ e) :
    c₁ = c₂ := by
  by_contra hcne
  let D := secondOrderDefectGraph G
  let m := componentQuotientMatrix G D c₁ e
  have hc₂min : ∀ l : D.ConnectedComponent,
      c₂.supp.ncard ≤ l.supp.ncard := by
    intro l
    rw [hsame]
    exact hc₁min l
  have hlt₂ : c₂.supp.ncard < e.supp.ncard := by omega
  have hs₁ := secondOrder_minimumComponent_longer_edge_structure
    G hfree hd heven hmin hcard c₁ e hc₁min hlt hpos₁
  have hs₂ := secondOrder_minimumComponent_longer_edge_structure
    G hfree hd heven hmin hcard c₂ e hc₂min hlt₂ hpos₂
  have hm2 : 2 ≤ m := by
    dsimp only [m, D]
    by_contra hm
    have hm1 : componentQuotientMatrix G
        (secondOrderDefectGraph G) c₁ e = 1 := by omega
    rw [hm1, mul_one] at hs₁
    omega
  have hn : e.supp.ncard = m * c₁.supp.ncard := by
    dsimp only [m, D]
    rw [mul_comm]
    exact hs₁.2.2.1.symm
  obtain ⟨u, hu, huRange, huD, hthree⟩ :=
    exists_mixed_cycle_labeling G hfree hd heven hmin hcard
  letI : NeZero c₁.supp.ncard :=
    ⟨Nat.ne_of_gt (by have := hthree c₁; omega)⟩
  letI : NeZero c₂.supp.ncard :=
    ⟨Nat.ne_of_gt (by have := hthree c₂; omega)⟩
  letI : NeZero e.supp.ncard :=
    ⟨Nat.ne_of_gt (by have := hthree e; omega)⟩
  obtain ⟨f₁, hadj₁, horient₁, -⟩ :=
    exists_minimumComponent_longer_cycleCover
      G hfree hd heven hmin hcard (hthree c₁) (hthree e)
        c₁ e hc₁min hlt hpos₁ (u c₁) (u e) (hu c₁) (hu e)
        (huRange c₁) (huRange e) (huD c₁) (huD e)
  obtain ⟨f₂, hadj₂, horient₂, -⟩ :=
    exists_minimumComponent_longer_cycleCover
      G hfree hd heven hmin hcard (hthree c₂) (hthree e)
        c₂ e hc₂min hlt₂ hpos₂ (u c₂) (u e) (hu c₂) (hu e)
        (huRange c₂) (huRange e) (huD c₂) (huD e)
  have hdisjoint : ∀ x z, u c₁ x ≠ u c₂ z := by
    intro x z hxz
    have hx₁ : u c₁ x ∈ c₁.supp := by
      rw [← huRange c₁]
      exact ⟨x, rfl⟩
    have hz₂ : u c₂ z ∈ c₂.supp := by
      rw [← huRange c₂]
      exact ⟨z, rfl⟩
    have hcc₁ : D.connectedComponentMk (u c₁ x) = c₁ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c₁ (u c₁ x)).mp hx₁
    have hcc₂ : D.connectedComponentMk (u c₂ z) = c₂ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c₂ (u c₂ z)).mp hz₂
    apply hcne
    rw [hxz] at hcc₁
    exact hcc₁.symm.trans hcc₂
  exact false_of_two_disjoint_cycleCovers_same_multipleTarget_of_moduli
    hm2 hsame hn G hfree (u c₁) (u c₂) (u e) (hu e) hdisjoint
      f₁ f₂ hadj₁ hadj₂ horient₁ horient₂

end

end Erdos85
