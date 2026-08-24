import Proofs.Erdos85GraphEdgeIndicatorPotential

/-!
# Extracting an odd-weight cycle from odd holonomy

The Eulerian price terminal first produces a closed walk of K-weight one.
This file upgrades that witness to an actual `Walk.IsCycle` of K-weight one,
as required by the cycle-space formulation in `(73rnz_cjibkq)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem isPath_length_one_of_endpointEdge
    {V : Type*} {G : SimpleGraph V} {v u : V} (p : G.Walk v u)
    (hp : p.IsPath) (he : s(u, v) ∈ p.edges) : p.length = 1 := by
  cases p with
  | nil => simp at he
  | @cons _ w _ e q =>
    rw [Walk.edges_cons, List.mem_cons] at he
    rw [Walk.cons_isPath_iff] at hp
    rcases he with heq | hmem
    · rw [Sym2.eq_iff] at heq
      have hvw : v ≠ w := e.ne
      have huw : u = w := by
        rcases heq with ⟨_, h2⟩ | ⟨h1, _⟩
        · exact absurd h2 hvw
        · exact h1
      subst huw
      rw [Walk.isPath_iff_eq_nil] at hp
      have : q = Walk.nil := hp.1
      subst this
      simp
    · exact absurd (Walk.snd_mem_support_of_mem_edges q hmem) hp.2

/-- Rotating a closed walk preserves the sum of any directed dart weight. -/
theorem f2WalkWeight_rotate
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (k : V → V → ZMod 2) {u z : V} (p : G.Walk u u)
    (hz : z ∈ p.support) :
    f2WalkWeight k (p.rotate z hz) = f2WalkWeight k p := by
  unfold f2WalkWeight
  exact ((p.rotate_darts z hz).map
    (fun d => k d.fst d.snd)).perm.sum_eq

/-- Strong-induction workhorse: a closed walk of F₂-weight one contains a
weight-one cycle no longer than itself. -/
theorem exists_oddWeight_cycle_aux
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (k : V → V → ZMod 2) (hsymm : ∀ u v, k u v = k v u)
    (n : ℕ) : ∀ {u : V} (w : G.Walk u u), w.length = n →
      f2WalkWeight k w = 1 →
      ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧
        f2WalkWeight k c = 1 ∧ c.length ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro u w hlen hweight
    by_cases hcyc : w.IsCycle
    · exact ⟨u, w, hcyc, hweight, by rw [hlen]⟩
    · cases w with
      | nil => simp at hweight
      | @cons _ v _ h p =>
        rw [Walk.cons_isCycle_iff] at hcyc
        have hnp : ¬ p.IsPath := by
          intro hpath
          have hin : s(u, v) ∈ p.edges := by
            by_contra hnin
            exact hcyc ⟨hpath, hnin⟩
          have h1 : p.length = 1 :=
            isPath_length_one_of_endpointEdge p hpath hin
          cases p with
          | nil => simp at h1
          | @cons _ y _ h' q =>
            cases q with
            | nil =>
                simp [f2WalkWeight, hsymm] at hweight
                have htwo : (2 : ZMod 2) = 0 := by decide
                rw [← two_mul, htwo, zero_mul] at hweight
                exact zero_ne_one hweight
            | @cons _ z _ h'' q' =>
                simp [Walk.length_cons] at h1
        rw [Walk.isPath_def, List.nodup_iff_count_le_one] at hnp
        push Not at hnp
        obtain ⟨z, hz2⟩ := hnp
        have hzp : z ∈ p.support := List.count_pos_iff.mp (by omega)
        have hzw : z ∈ (Walk.cons h p).support := by
          rw [Walk.support_cons]
          exact List.mem_cons_of_mem _ hzp
        set r : G.Walk z z := (Walk.cons h p).rotate z hzw with hrdef
        have hlenr : r.length = n := by
          rw [hrdef, Walk.length_rotate]
          exact hlen
        have hweightr : f2WalkWeight k r = 1 := by
          rw [hrdef, f2WalkWeight_rotate]
          exact hweight
        have hcount : r.support.tail.count z = p.support.count z := by
          have hperm : r.support.tail ~r p.support := by
            have h0 : ((Walk.cons h p).rotate z hzw).support.tail
                ~r (Walk.cons h p).support.tail := by
              apply Walk.support_rotate
            rw [← hrdef] at h0
            simpa only [Walk.support_cons, List.tail_cons] using h0
          exact hperm.perm.count_eq z
        clear_value r
        clear hrdef
        cases r with
        | nil => simp at hweightr
        | @cons _ m _ e r' =>
          have hlenr' : r'.length + 1 = n := by
            rw [Walk.length_cons] at hlenr
            exact hlenr
          have hcz : 1 < r'.support.count z := by
            rw [Walk.support_cons, List.tail_cons] at hcount
            rw [hcount]
            exact hz2
          have hz' : z ∈ r'.support := List.count_pos_iff.mp (by omega)
          have hts : (r'.takeUntil z hz').length +
              (r'.dropUntil z hz').length = r'.length := by
            have ht := congrArg Walk.length (r'.take_spec hz')
            rwa [Walk.length_append] at ht
          have htailcount : 1 ≤
              (r'.dropUntil z hz').support.tail.count z := by
            have hsplit : r'.support.count z =
                (r'.takeUntil z hz').support.count z +
                  (r'.dropUntil z hz').support.tail.count z := by
              conv_lhs => rw [← r'.take_spec hz']
              rw [Walk.support_append, List.count_append]
            rw [Walk.count_support_takeUntil_eq_one] at hsplit
            omega
          have hdr1 : 1 ≤ (r'.dropUntil z hz').length := by
            have hc1 : (r'.dropUntil z hz').support.tail.count z ≤
                (r'.dropUntil z hz').support.tail.length := List.count_le_length
            rw [List.length_tail, Walk.length_support] at hc1
            omega
          have hra1 : 1 ≤
              (Walk.cons e (r'.takeUntil z hz')).length := by
            rw [Walk.length_cons]
            omega
          have hsum : (Walk.cons e (r'.takeUntil z hz')).length +
              (r'.dropUntil z hz').length = n := by
            rw [Walk.length_cons]
            omega
          have hsplitWeight := congrArg (f2WalkWeight k) (r'.take_spec hz')
          rw [f2WalkWeight_append] at hsplitWeight
          rw [f2WalkWeight_cons, ← hsplitWeight] at hweightr
          have hsumWeight :
              f2WalkWeight k (Walk.cons e (r'.takeUntil z hz')) +
                f2WalkWeight k (r'.dropUntil z hz') = 1 := by
            rw [f2WalkWeight_cons]
            simpa [add_assoc] using hweightr
          have hone :
              f2WalkWeight k (Walk.cons e (r'.takeUntil z hz')) = 1 ∨
                f2WalkWeight k (r'.dropUntil z hz') = 1 := by
            have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
            rcases hbinary (f2WalkWeight k
              (Walk.cons e (r'.takeUntil z hz'))) with ha | ha <;>
              rcases hbinary (f2WalkWeight k
                (r'.dropUntil z hz')) with hb | hb <;> simp_all
          rcases hone with ha | hb
          · obtain ⟨x, c, hcycle, hcweight, hcle⟩ :=
              ih (Walk.cons e (r'.takeUntil z hz')).length (by omega)
                (Walk.cons e (r'.takeUntil z hz')) rfl ha
            exact ⟨x, c, hcycle, hcweight, by omega⟩
          · obtain ⟨x, c, hcycle, hcweight, hcle⟩ :=
              ih (r'.dropUntil z hz').length (by omega)
                (r'.dropUntil z hz') rfl hb
            exact ⟨x, c, hcycle, hcweight, by omega⟩

/-- Every symmetric-weight closed walk of weight one contains an actual
weight-one cycle. -/
theorem exists_oddWeight_cycle_of_closedWalk
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (k : V → V → ZMod 2) (hsymm : ∀ u v, k u v = k v u)
    {u : V} (w : G.Walk u u) (hweight : f2WalkWeight k w = 1) :
    ∃ (x : V) (c : G.Walk x x), c.IsCycle ∧
      f2WalkWeight k c = 1 ∧ c.length ≤ w.length :=
  exists_oddWeight_cycle_aux k hsymm w.length w rfl hweight

/-- Graph-price specialization: odd K-holonomy contains an actual routing
cycle of odd K-weight. -/
theorem exists_odd_graphEdgeIndicator_cycle_of_closedWalk
    {V : Type*} [DecidableEq V] (P K : SimpleGraph V)
    {u : V} (w : P.Walk u u)
    (hweight : f2WalkWeight (graphEdgeIndicator K) w = 1) :
    ∃ (x : V) (c : P.Walk x x), c.IsCycle ∧
      f2WalkWeight (graphEdgeIndicator K) c = 1 ∧ c.length ≤ w.length :=
  exists_oddWeight_cycle_of_closedWalk
    (graphEdgeIndicator K) (graphEdgeIndicator_symm K) w hweight

end


end Erdos85

#print axioms Erdos85.f2WalkWeight_rotate
#print axioms Erdos85.exists_oddWeight_cycle_of_closedWalk
#print axioms Erdos85.exists_odd_graphEdgeIndicator_cycle_of_closedWalk
