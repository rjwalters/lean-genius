import Proofs.Erdos85H3PairBridge

/-!
# Splitting the pair-cell search into independent parts

Phase 1 of the engine does not depend on the leaf test.  Selecting the
phase-1 leaves by a state key modulo `m` therefore splits the search into
`m` independent Boolean computations whose conjunction has the same
soundness consequence as the unsplit search.

No finite search is run in this file.
-/

namespace Erdos85
namespace H3Pair

/-- A cheap key of a partial graph, used only to distribute phase-1 leaves. -/
def stKey (s : St) : Nat :=
  s.rows.toArray.foldl (fun acc r => (acc * 31 + r) % 1000003) 0

/-- Leaf test of part `r` of `m`: leaves with another key are accepted
without search. -/
def leafPart (m r : Nat) (s : St) : Bool :=
  decide (stKey s % m ≠ r) || leaf1 30 40 s

/-- Part `r` of the `m`-way split search from the initial state. -/
def pairPart (m r : Nat) : Bool := dfs1 (leafPart m r) 70 s0

theorem dfs1_succ (leaf : St → Bool) (fuel : Nat) (s : St) :
    dfs1 leaf (fuel + 1) s =
      match findClause s with
      | none => leaf s
      | some (u, w) =>
        decide (3 ≤ u.val) && clauseOpen s u w &&
          (fiberList w).all fun x =>
            decide (x = u) || twinSkip s u w x ||
              match s.tryAdd u x with
              | none => true
              | some s' => dfs1 leaf fuel s' := by
  rfl

theorem dfs1_sound_parts (m : Nat) (hm : 0 < m) :
    ∀ (fuel : Nat) (s : St), s.WF →
      (∀ r, r < m → dfs1 (leafPart m r) fuel s = true) →
      ∀ adj, Model adj → Compat s adj → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro s _ h
    have := h 0 hm
    simp [dfs1] at this
  | succ fuel ih =>
    intro s hs h adj M hc
    cases hfc : findClause s with
    | none =>
      have hleaf := h _ (Nat.mod_lt (stKey s) hm)
      rw [dfs1_succ, hfc] at hleaf
      dsimp only at hleaf
      unfold leafPart at hleaf
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hleaf
      rcases hleaf with hleaf | hleaf
      · exact hleaf rfl
      · exact leaf1_sound 30 40 s hs hleaf adj M hc
    | some p =>
      obtain ⟨u, w⟩ := p
      have hall : ∀ r, r < m → 3 ≤ u.val ∧ ∀ x ∈ fiberList w,
          (decide (x = u) || twinSkip s u w x ||
            match s.tryAdd u x with
            | none => true
            | some s' => dfs1 (leafPart m r) fuel s') = true := by
        intro r hr
        have hthis := h r hr
        rw [dfs1_succ, hfc] at hthis
        dsimp only at hthis
        rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hthis
        exact ⟨hthis.1.1, List.all_eq_true.mp hthis.2⟩
      have hu : 3 ≤ u.val := (hall 0 hm).1
      have key : ∀ (n : Nat) (k : V), k.val = n → ∀ adj, Model adj → Compat s adj →
          adj u k = true → col k w = true → False := by
        intro n
        induction n using Nat.strong_induction_on with
        | _ n ihn =>
          intro k hkn adj M hc huk hkw
          have hkmem : k ∈ fiberList w := mem_fiberList k w hkw
          have hku : k ≠ u := by
            intro h
            rw [h, M.irrefl] at huk
            cases huk
          cases hskipc : twinSkip s u w k with
          | true =>
            unfold twinSkip at hskipc
            obtain ⟨y, hy, hcond⟩ := List.any_eq_true.mp hskipc
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
            obtain ⟨⟨⟨hlt, hyu⟩, hrows⟩, hmask⟩ := hcond
            have hyw : col y w = true := fiberList_col w y hy
            have hrow : ∀ b, s.adj y b = s.adj k b := by
              intro b
              unfold St.adj
              rw [hrows]
            obtain ⟨M', hc'⟩ := twin_transport hs M hc y k (col_low y w hyw).1
              (col_low k w hkw).1 hmask hrow
            refine ihn y.val (by omega) y rfl _ M' hc' ?_ hyw
            show adj (Equiv.swap y k u) (Equiv.swap y k y) = true
            rw [Equiv.swap_apply_left,
              Equiv.swap_apply_of_ne_of_ne (fun h => hyu h.symm) (fun h => hku h.symm)]
            exact huk
          | false =>
            cases htry : s.tryAdd u k with
            | none =>
              have := tryAdd_none hs M hc htry
              rw [huk] at this
              cases this
            | some s' =>
              obtain ⟨hs', _, _, _, hcompat⟩ := tryAdd_some hs htry
              refine ih s' hs' ?_ adj M (hcompat adj M hc huk)
              intro r hr
              have hk := (hall r hr).2 k hkmem
              rw [hskipc, htry] at hk
              dsimp only at hk
              simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.false_eq_true,
                or_false] at hk
              rcases hk with hk | hk
              · exact absurd hk hku
              · exact hk
      obtain ⟨k, hk, hkw⟩ := M.colEx u hu w
      exact key k.val k rfl adj M hc hk hkw

/-- All parts of an `m`-way split exclude the canonical `t = 0` three-high
representative. -/
theorem threeHighCanonicalRepresentativeExcluded_zero_of_parts (m : Nat) (hm : 0 < m)
    (h : ∀ r, r < m → pairPart m r = true) :
    ThreeHighCanonicalRepresentativeExcluded 0 := by
  intro edges hc
  obtain ⟨M, hcompat⟩ := model_of_constraints (adj := orderFortyNineBitAdj edges)
    (orderFortyNineBitAdj_comm edges)
    (fun a => by simp [orderFortyNineBitAdj]) hc
  exact dfs1_sound_parts m hm 70 s0 s0_wf h _ M hcompat

/-- All parts of an `m`-way split exclude the `(h, t) = (3, 0)` cell. -/
theorem orderFortyNineTripleCellExcluded_three_zero_of_parts (m : Nat) (hm : 0 < m)
    (h : ∀ r, r < m → pairPart m r = true) :
    OrderFortyNineTripleCellExcluded 3 0 :=
  orderFortyNineTripleCellExcluded_three_of_canonical
    threeHighCanonicalGraphCover_zero
    (threeHighCanonicalRepresentativeExcluded_zero_of_parts m hm h)

end H3Pair
end Erdos85

#print axioms Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero_of_parts
