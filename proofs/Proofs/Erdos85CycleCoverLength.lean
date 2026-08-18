import Proofs.Erdos85CycleCoverRigidity

/-!
# Length divisibility for cyclic covers

The local orientation theorem for a one-neighbor cycle block immediately
forces the target cycle length to divide the source cycle length.  This file
packages that deck-theoretic conclusion for use by the saturated
minimum-layer defect covering.
-/

namespace Erdos85

/-- A locally cycle-intertwining map from an `n`-cycle to an `r`-cycle can
close after `n` steps only when `r ∣ n`. -/
theorem cycleMap_length_dvd
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr : 3 ≤ r) (f : ZMod n → ZMod r)
    (hpair : ∀ y, ({f (y - 1), f (y + 1)} : Set (ZMod r)) =
      {f y - 1, f y + 1}) :
    r ∣ n := by
  rcases cycleMap_global_orientation hr f hpair with hforward | hreverse
  · have hiter : ∀ m : ℕ,
        f (m : ZMod n) = f 0 + (m : ZMod r) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          calc
            f ((m + 1 : ℕ) : ZMod n) = f ((m : ZMod n) + 1) := by
              rw [Nat.cast_add, Nat.cast_one]
            _ = f (m : ZMod n) + 1 := hforward _
            _ = f 0 + ((m : ZMod r) + 1) := by rw [ih]; ring
            _ = f 0 + ((m + 1 : ℕ) : ZMod r) := by
              rw [Nat.cast_add, Nat.cast_one]
    have hn := hiter n
    have hncast : (n : ZMod r) = 0 := by
      have hnzero : (n : ZMod n) = 0 := ZMod.natCast_self n
      rw [hnzero] at hn
      have hcancel : f 0 + (n : ZMod r) = f 0 + 0 := by
        simpa using hn.symm
      exact add_left_cancel hcancel
    exact (ZMod.natCast_eq_zero_iff n r).mp hncast
  · have hiter : ∀ m : ℕ,
        f (m : ZMod n) = f 0 - (m : ZMod r) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          calc
            f ((m + 1 : ℕ) : ZMod n) = f ((m : ZMod n) + 1) := by
              rw [Nat.cast_add, Nat.cast_one]
            _ = f (m : ZMod n) - 1 := hreverse _
            _ = f 0 - ((m : ZMod r) + 1) := by rw [ih]; ring
            _ = f 0 - ((m + 1 : ℕ) : ZMod r) := by
              rw [Nat.cast_add, Nat.cast_one]
    have hn := hiter n
    have hncast : (n : ZMod r) = 0 := by
      have hnzero : (n : ZMod n) = 0 := ZMod.natCast_self n
      rw [hnzero] at hn
      have : f 0 - (n : ZMod r) = f 0 := hn.symm
      exact sub_eq_self.mp this
    exact (ZMod.natCast_eq_zero_iff n r).mp hncast

/-- A locally bijective graph map between parametrized cycles induces the
coordinate map required by `cycleMap_length_dvd`. -/
theorem cycleCover_length_dvd_of_localBijection
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (DX : SimpleGraph X) [DecidableRel DX.Adj]
    (DY : SimpleGraph Y) [DecidableRel DY.Adj]
    (owner : X → Y)
    {n r : ℕ} [NeZero n] [NeZero r]
    (hr : 3 ≤ r)
    (u : ZMod n → X) (v : ZMod r → Y)
    (hvinj : Function.Injective v)
    (hu : ∀ z, DX.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, DY.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hmap : ∀ {x y}, DX.Adj x y → DY.Adj (owner x) (owner y))
    (hlift : ∀ (x : X) (b : Y), DY.Adj (owner x) b →
      ∃ w : X, DX.Adj x w ∧ owner w = b)
    (hownerRange : ∀ z, owner (u z) ∈ Set.range v) :
    r ∣ n := by
  classical
  have hfExists : ∀ z : ZMod n, ∃ a : ZMod r, v a = owner (u z) := by
    intro z
    simpa only [Set.mem_range] using hownerRange z
  let f : ZMod n → ZMod r := fun z => Classical.choose (hfExists z)
  have hfval : ∀ z, v (f z) = owner (u z) := fun z =>
    Classical.choose_spec (hfExists z)
  have hvaluePair : ∀ z,
      ({v (f (z - 1)), v (f (z + 1))} : Set Y) =
        {v (f z - 1), v (f z + 1)} := by
    intro z
    have himage :
        (DX.neighborFinset (u z)).image owner =
          DY.neighborFinset (owner (u z)) := by
      ext b
      constructor
      · intro hb
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
        exact (DY.mem_neighborFinset (owner (u z)) (owner w)).mpr
          (hmap ((DX.mem_neighborFinset (u z) w).mp hw))
      · intro hb
        have hbAdj : DY.Adj (owner (u z)) b :=
          (DY.mem_neighborFinset (owner (u z)) b).mp hb
        obtain ⟨w, huw, hwb⟩ := hlift (u z) b hbAdj
        exact Finset.mem_image.mpr
          ⟨w, (DX.mem_neighborFinset (u z) w).mpr huw, hwb⟩
    rw [hu z] at himage
    rw [← hfval z, hv (f z)] at himage
    have himage' :
        ({owner (u (z - 1)), owner (u (z + 1))} : Finset Y) =
          {v (f z - 1), v (f z + 1)} := by
      simpa using himage
    have hset := congrArg (fun t : Finset Y => (↑t : Set Y)) himage'
    simpa [hfval] using hset
  have hpair : ∀ z,
      ({f (z - 1), f (z + 1)} : Set (ZMod r)) =
        {f z - 1, f z + 1} := by
    intro z
    have hvp := hvaluePair z
    rw [Set.pair_eq_pair_iff] at hvp
    rw [Set.pair_eq_pair_iff]
    rcases hvp with h | h
    · exact Or.inl ⟨hvinj h.1, hvinj h.2⟩
    · exact Or.inr ⟨hvinj h.1, hvinj h.2⟩
  exact cycleMap_length_dvd hr f hpair

/-- For a locally bijective cycle cover, membership of one owner in the
target cycle propagates around the whole source cycle.  Thus a single base
point replaces the global range hypothesis. -/
theorem cycleCover_length_dvd_of_localBijection_of_start
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (DX : SimpleGraph X) [DecidableRel DX.Adj]
    (DY : SimpleGraph Y) [DecidableRel DY.Adj]
    (owner : X → Y)
    {n r : ℕ} [NeZero n] [NeZero r]
    (hr : 3 ≤ r)
    (u : ZMod n → X) (v : ZMod r → Y)
    (hvinj : Function.Injective v)
    (hu : ∀ z, DX.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hv : ∀ z, DY.neighborFinset (v z) = {v (z - 1), v (z + 1)})
    (hmap : ∀ {x y}, DX.Adj x y → DY.Adj (owner x) (owner y))
    (hlift : ∀ (x : X) (b : Y), DY.Adj (owner x) b →
      ∃ w : X, DX.Adj x w ∧ owner w = b)
    (hstart : owner (u 0) ∈ Set.range v) :
    r ∣ n := by
  have hnat : ∀ m : ℕ, owner (u (m : ZMod n)) ∈ Set.range v := by
    intro m
    induction m with
    | zero => simpa using hstart
    | succ m ih =>
        obtain ⟨t, ht⟩ := ih
        have hadjSource : DX.Adj (u (m : ZMod n)) (u ((m : ZMod n) + 1)) := by
          apply (DX.mem_neighborFinset (u (m : ZMod n)) _).mp
          rw [hu]
          simp
        have hadjTarget : DY.Adj (v t) (owner (u ((m : ZMod n) + 1))) := by
          rw [ht]
          exact hmap hadjSource
        have hmem : owner (u ((m : ZMod n) + 1)) ∈
            DY.neighborFinset (v t) :=
          (DY.mem_neighborFinset (v t) _).mpr hadjTarget
        rw [hv t] at hmem
        simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
        rcases hmem with hminus | hplus
        · refine ⟨t - 1, ?_⟩
          simpa [Nat.cast_succ] using hminus.symm
        · refine ⟨t + 1, ?_⟩
          simpa [Nat.cast_succ] using hplus.symm
  apply cycleCover_length_dvd_of_localBijection
    DX DY owner hr u v hvinj hu hv hmap hlift
  intro z
  simpa only [ZMod.natCast_zmod_val] using hnat z.val

/-- A locally bijective map between finite two-regular graphs makes the size
of the target component divide the size of the source component.  This is
the component-level form of cyclic-cover divisibility: the cycle coordinates
and the relevant target component are constructed internally. -/
theorem cycleCover_component_card_dvd_of_localBijection
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (DX : SimpleGraph X) [DecidableRel DX.Adj]
    (DY : SimpleGraph Y) [DecidableRel DY.Adj]
    (owner : X → Y)
    (hdegY : ∀ y, DY.degree y = 2)
    (hmap : ∀ {x y}, DX.Adj x y → DY.Adj (owner x) (owner y))
    (hlift : ∀ (x : X) (b : Y), DY.Adj (owner x) b →
      ∃! w : X, DX.Adj x w ∧ owner w = b)
    (x : X) :
    (DY.connectedComponentMk (owner x)).supp.ncard ∣
      (DX.connectedComponentMk x).supp.ncard := by
  classical
  let cx := DX.connectedComponentMk x
  let cy := DY.connectedComponentMk (owner x)
  have hx : x ∈ cx.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ x).mpr rfl
  have hy : owner x ∈ cy.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff _ (owner x)).mpr rfl
  have hdegX : ∀ z, DX.degree z = 2 := by
    intro z
    have himage : (DX.neighborFinset z).image owner =
        DY.neighborFinset (owner z) := by
      ext b
      constructor
      · intro hb
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hb
        exact (DY.mem_neighborFinset _ _).mpr
          (hmap ((DX.mem_neighborFinset _ _).mp hw))
      · intro hb
        obtain ⟨w, hw, _⟩ := hlift z b ((DY.mem_neighborFinset _ _).mp hb)
        exact Finset.mem_image.mpr
          ⟨w, (DX.mem_neighborFinset _ _).mpr hw.1, hw.2⟩
    have hinj : Set.InjOn owner (DX.neighborFinset z : Set X) := by
      intro w₁ hw₁ w₂ hw₂ heq
      have htarget : DY.Adj (owner z) (owner w₁) :=
        hmap ((DX.mem_neighborFinset _ _).mp hw₁)
      obtain ⟨_w, _hw, huniq⟩ := hlift z (owner w₁) htarget
      exact (huniq w₁
        ⟨(DX.mem_neighborFinset _ _).mp hw₁, rfl⟩).trans
          (huniq w₂
            ⟨(DX.mem_neighborFinset _ _).mp hw₂, heq.symm⟩).symm
    rw [← DX.card_neighborFinset_eq_degree,
      ← Finset.card_image_iff.mpr hinj, himage,
      DY.card_neighborFinset_eq_degree, hdegY]
  have hcyclesX : DX.IsCycles := by
    intro z _
    rw [← Set.fintypeCard_eq_ncard, DX.card_neighborSet_eq_degree]
    exact hdegX z
  have hcyclesY : DY.IsCycles := by
    intro z _
    rw [← Set.fintypeCard_eq_ncard, DY.card_neighborSet_eq_degree]
    exact hdegY z
  have hneighX : (DX.neighborSet x).Nonempty :=
    DX.neighborSet_nonempty.mpr ((DX.degree_pos x).mp (by rw [hdegX]; omega))
  have hneighY : (DY.neighborSet (owner x)).Nonempty :=
    DY.neighborSet_nonempty.mpr
      ((DY.degree_pos (owner x)).mp (by rw [hdegY]; omega))
  obtain ⟨p, hp, hpverts⟩ :=
    hcyclesX.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hx hneighX
  obtain ⟨q, hq, hqverts⟩ :=
    hcyclesY.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hy hneighY
  obtain ⟨u, _huinj, hurange, hu⟩ :=
    exists_zmod_cycleParam_neighborFinset hp hdegX
  obtain ⟨v, hvinj, hvrange, hv⟩ :=
    exists_zmod_cycleParam_neighborFinset hq hdegY
  letI : NeZero p.length := ⟨by
    have := hp.three_le_length
    omega⟩
  letI : NeZero q.length := ⟨by
    have := hq.three_le_length
    omega⟩
  have hxRange : x ∈ Set.range u := by
    rw [hurange, hpverts]
    exact hx
  obtain ⟨t, ht⟩ := hxRange
  let u' : ZMod p.length → X := fun z => u (z + t)
  have hu' : ∀ z, DX.neighborFinset (u' z) =
      {u' (z - 1), u' (z + 1)} := by
    intro z
    rw [show u' z = u (z + t) by rfl, hu]
    change ({u (z + t - 1), u (z + t + 1)} : Finset X) =
      {u (z - 1 + t), u (z + 1 + t)}
    congr 2 <;> abel_nf
  have hu'zero : u' 0 = x := by
    simpa [u'] using ht
  have hyRange : owner x ∈ Set.range v := by
    rw [hvrange, hqverts]
    exact hy
  have hdiv : q.length ∣ p.length := by
    apply cycleCover_length_dvd_of_localBijection_of_start
      DX DY owner hq.three_le_length u' v hvinj hu' hv hmap
        (fun a b hab => (hlift a b hab).exists)
    rw [hu'zero]
    exact hyRange
  have hpCard : p.length = cx.supp.ncard := by
    calc
      p.length = p.toSubgraph.verts.ncard := by
        rw [← Set.fintypeCard_eq_ncard]
        simpa using (isCycle_card_verts_eq_length hp).symm
      _ = cx.supp.ncard := congrArg Set.ncard hpverts
  have hqCard : q.length = cy.supp.ncard := by
    calc
      q.length = q.toSubgraph.verts.ncard := by
        rw [← Set.fintypeCard_eq_ncard]
        simpa using (isCycle_card_verts_eq_length hq).symm
      _ = cy.supp.ncard := congrArg Set.ncard hqverts
  simpa [hpCard, hqCard] using hdiv

end Erdos85
