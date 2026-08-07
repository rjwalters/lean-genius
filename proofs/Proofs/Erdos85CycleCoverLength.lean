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

end Erdos85
