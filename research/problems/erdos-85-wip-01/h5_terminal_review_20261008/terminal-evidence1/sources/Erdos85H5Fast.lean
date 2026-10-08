import Proofs.Erdos85H5Bridge

/-!
# A faster phase 1 for the five-high engine

`dfs1G` visits the same search tree as `Erdos85.H5.dfs1` with the full
dead-clause list, but spends less per node:

* the dead-end test is per vertex (`vertDead`): the union of the rows of the
  neighbours of `u` is computed once, and a candidate `x` is admissible iff
  it is not full and its row is disjoint from that union;
* the clause list is an argument of the recursion, so clauses already
  closed are not scanned again.

The dead-end test is an abstract parameter of `dfs1G`; soundness needs only
that it never fires on a state with a compatible model.

No finite search is run in this file.
-/

namespace Erdos85
namespace H5

open H3Pair (V St M49 Compat and_bit_of_ne_zero and_no_bit_of_eq_zero)
open OrderFortyNineSmallHighCensus

variable {c : Fin 3}

/-- Union of the rows of the known neighbours of `u`. -/
def nbrUnion (s : St) (u : V) : Nat :=
  (s.nbr[u.val]).foldl (fun a y => a ||| s.rows[y.val]) 0

theorem foldl_or_testBit (rows : Vector Nat 49) (i : Nat) :
    ∀ (l : List V) (a : Nat),
      (l.foldl (fun a y => a ||| rows[y.val]) a).testBit i = true →
      a.testBit i = true ∨ ∃ y ∈ l, (rows[y.val]).testBit i = true := by
  intro l
  induction l with
  | nil =>
    intro a h
    exact Or.inl h
  | cons y l ih =>
    intro a h
    rw [List.foldl_cons] at h
    rcases ih _ h with h | ⟨z, hz, hzi⟩
    · rw [Nat.testBit_or, Bool.or_eq_true] at h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr ⟨y, List.mem_cons_self .., h⟩
    · exact Or.inr ⟨z, List.mem_cons_of_mem _ hz, hzi⟩

/-- Candidate test against a precomputed neighbour union `f`. -/
def okF (s : St) (f : Nat) (x : V) : Bool :=
  decide ((s.nbr[x.val]).length < capOf x) && (((s.rows[x.val] &&& f) &&& M49) == 0)

theorem okF_of_allowed {s : St} {u x : V} (h : allowed s u x = true) :
    okF s (nbrUnion s u) x = true ∧ (s.nbr[u.val]).length < capOf u := by
  unfold allowed at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hx, hu⟩, hall⟩ := h
  refine ⟨?_, hu⟩
  unfold okF
  rw [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hx, ?_⟩
  cases hbit : (((s.rows[x.val] &&& nbrUnion s u) &&& M49) == 0)
  · exfalso
    obtain ⟨i, hi, hxi, hfi⟩ := and_bit_of_ne_zero hbit
    unfold nbrUnion at hfi
    rcases foldl_or_testBit s.rows i _ _ hfi with h0 | ⟨y, hy, hyi⟩
    · rw [Nat.zero_testBit] at h0
      cases h0
    · have hy' := (List.all_eq_true.mp hall) y hy
      exact and_no_bit_of_eq_zero hy' i hi hyi hxi
  · rfl

/-- A low vertex with an open colour clause none of whose candidates can be
added. -/
def vertDead (c : Fin 3) (s : St) (u : V) : Bool :=
  decide (5 ≤ u.val) &&
    (let f := nbrUnion s u
     let full := decide (capOf u ≤ (s.nbr[u.val]).length)
     ([0, 1, 2, 3, 4] : List (Fin 5)).any fun w =>
       clauseOpen c s u w &&
         (full || (fiberList c w).all fun x => decide (x = u) || !okF s f x))

theorem vertDead_sound {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
    (hc : Compat s adj) {u : V} (h : vertDead c s u = true) : False := by
  unfold vertDead at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hu, hany⟩ := h
  obtain ⟨w, _, hw⟩ := List.any_eq_true.mp hany
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hw
  obtain ⟨hopen, hdead⟩ := hw
  obtain ⟨k, hk, hkw⟩ := M.colEx u hu w
  obtain ⟨hokF, hlt⟩ :=
    okF_of_allowed (allowed_sound hs M hc hk (clauseOpen_not_adj hopen hkw))
  rcases hdead with hfull | hall
  · omega
  · have hx := (List.all_eq_true.mp hall) k (mem_fiberList c k w hkw)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hx
    rcases hx with hx | hx
    · rw [hx, M.irrefl] at hk
      cases hk
    · rw [hokF] at hx
      cases hx

/-- Dead-end test over all core vertices of cell `c`. -/
def deadAll (c : Fin 3) (s : St) : Bool := (coreVerts c).any (vertDead c s)

theorem deadAll_sound {s : St} {adj : V → V → Bool} (hs : s.WF) (M : Model c adj)
    (hc : Compat s adj) (h : deadAll c s = true) : False := by
  obtain ⟨u, _, hu⟩ := List.any_eq_true.mp h
  exact vertDead_sound hs M hc hu

/-- Phase 1 with an abstract dead-end test and the clause list as a
recursion argument.  The clause list is arbitrary: the properties of a
chosen clause that soundness needs are re-checked at run time. -/
def dfs1G (c : Fin 3) (dead leaf : St → Bool) : Nat → List (V × Fin 5) → St → Bool
  | 0, _, _ => false
  | fuel + 1, cl, s =>
    dead s ||
      match cl.dropWhile (fun p => !clauseOpen c s p.1 p.2) with
      | [] => leaf s
      | (u, w) :: rest =>
        decide (5 ≤ u.val) && clauseOpen c s u w &&
          (fiberList c w).all fun x =>
            decide (x = u) || twinSkip c s u w x ||
              match tryAdd s u x with
              | none => true
              | some s' => dfs1G c dead leaf fuel rest s'

theorem dfs1G_succ (dead leaf : St → Bool) (fuel : Nat) (cl : List (V × Fin 5)) (s : St) :
    dfs1G c dead leaf (fuel + 1) cl s =
      (dead s ||
        match cl.dropWhile (fun p => !clauseOpen c s p.1 p.2) with
        | [] => leaf s
        | (u, w) :: rest =>
          decide (5 ≤ u.val) && clauseOpen c s u w &&
            (fiberList c w).all fun x =>
              decide (x = u) || twinSkip c s u w x ||
                match tryAdd s u x with
                | none => true
                | some s' => dfs1G c dead leaf fuel rest s') := by
  rfl

/-- Soundness of `dfs1G` for a family of leaf tests. -/
theorem dfs1G_sound_fam {ι : Type} (i0 : ι) (dead : St → Bool)
    (hdead : ∀ s : St, s.WF → dead s = true →
      ∀ adj, Model c adj → Compat s adj → False)
    (leaf : ι → St → Bool)
    (hleaf : ∀ s : St, s.WF → (∀ i, leaf i s = true) →
      ∀ adj, Model c adj → Compat s adj → False) :
    ∀ (fuel : Nat) (cl : List (V × Fin 5)) (s : St), s.WF →
      (∀ i, dfs1G c dead (leaf i) fuel cl s = true) →
      ∀ adj, Model c adj → Compat s adj → False := by
  intro fuel
  induction fuel with
  | zero =>
    intro cl s _ h
    have := h i0
    simp [dfs1G] at this
  | succ fuel ih =>
    intro cl s hs h adj M hc
    cases hd : dead s with
    | true => exact hdead s hs hd adj M hc
    | false =>
      cases hfc : cl.dropWhile (fun p => !clauseOpen c s p.1 p.2) with
      | nil =>
        refine hleaf s hs ?_ adj M hc
        intro i
        have hi := h i
        rw [dfs1G_succ, hd, hfc] at hi
        exact hi
      | cons p rest =>
        obtain ⟨u, w⟩ := p
        have hall : ∀ i, 5 ≤ u.val ∧ ∀ x ∈ fiberList c w,
            (decide (x = u) || twinSkip c s u w x ||
              match tryAdd s u x with
              | none => true
              | some s' => dfs1G c dead (leaf i) fuel rest s') = true := by
          intro i
          have hthis := h i
          rw [dfs1G_succ, hd, hfc] at hthis
          dsimp only at hthis
          try simp only [Bool.false_or] at hthis
          rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hthis
          exact ⟨hthis.1.1, List.all_eq_true.mp hthis.2⟩
        have hu : 5 ≤ u.val := (hall i0).1
        have key : ∀ (n : Nat) (k : V), k.val = n → ∀ adj, Model c adj → Compat s adj →
            adj u k = true → col c k w = true → False := by
          intro n
          induction n using Nat.strong_induction_on with
          | _ n ihn =>
            intro k hkn adj M hc huk hkw
            have hkmem : k ∈ fiberList c w := mem_fiberList c k w hkw
            have hku : k ≠ u := by
              intro h
              rw [h, M.irrefl] at huk
              cases huk
            cases hskipc : twinSkip c s u w k with
            | true =>
              unfold twinSkip at hskipc
              obtain ⟨y, hy, hcond⟩ := List.any_eq_true.mp hskipc
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
              obtain ⟨⟨⟨hlt, hyu⟩, hrows⟩, hmask⟩ := hcond
              have hyw : col c y w = true := fiberList_col c w y hy
              have hrow : ∀ b, s.adj y b = s.adj k b := by
                intro b
                unfold H3Pair.St.adj
                rw [hrows]
              obtain ⟨M', hc'⟩ := twin_transport hs M hc y k (col_low c y w hyw).1
                (col_low c k w hkw).1 hmask hrow
              refine ihn y.val (by omega) y rfl _ M' hc' ?_ hyw
              show adj (Equiv.swap y k u) (Equiv.swap y k y) = true
              rw [Equiv.swap_apply_left,
                Equiv.swap_apply_of_ne_of_ne (fun h => hyu h.symm) (fun h => hku h.symm)]
              exact huk
            | false =>
              cases htry : tryAdd s u k with
              | none =>
                have := tryAdd_none hs M hc htry
                rw [huk] at this
                cases this
              | some s' =>
                obtain ⟨hs', _, _, _, hcompat⟩ := tryAdd_some (c := c) hs htry
                refine ih rest s' hs' ?_ adj M (hcompat adj M hc huk)
                intro i
                have hk := (hall i).2 k hkmem
                rw [hskipc, htry] at hk
                dsimp only at hk
                simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.false_eq_true,
                  or_false] at hk
                rcases hk with hk | hk
                · exact absurd hk hku
                · exact hk
        obtain ⟨k, hk, hkw⟩ := M.colEx u hu w
        exact key k.val k rfl adj M hc hk hkw

/-! ## The composed search and its split -/

/-- The complete three-phase search with the faster phase 1. -/
def searchF (c : Fin 3) (fuel1 fuel2 fuel3 : Nat) (s : St) : Bool :=
  dfs1G c (deadAll c) (leaf1 c fuel2 fuel3) fuel1 (coreClauses c) s

theorem searchF_sound (fuel1 fuel2 fuel3 : Nat) (s : St) (hs : s.WF)
    (h : searchF c fuel1 fuel2 fuel3 s = true) :
    ∀ adj, Model c adj → Compat s adj → False :=
  dfs1G_sound_fam (ι := Unit) () (deadAll c)
    (fun _ hs hd _ M hc => deadAll_sound hs M hc hd)
    (fun _ => leaf1 c fuel2 fuel3)
    (fun s hs h => leaf1_sound fuel2 fuel3 s hs (h ())) fuel1 (coreClauses c) s hs
    (fun _ => h)

/-- Leaf test of part `r` of `m`: states with another key are accepted
without search; the others continue with the full search. -/
def leafPartF (c : Fin 3) (m r : Nat) (s : St) : Bool :=
  decide (stKey s % m ≠ r) || searchF c 170 20 20 s

/-- Part `r` of the `m`-way split: phase 1 on the clauses of the first `k`
core vertices, then the key test, then the full search. -/
def partF (c : Fin 3) (k m r : Nat) (s : St) : Bool :=
  dfs1G c (deadAll c) (leafPartF c m r) 170 ((coreClauses c).take (5 * k)) s

/-- If all `m` parts return `true`, no model is compatible with the state. -/
theorem partsF_sound (k m : Nat) (hm : 0 < m) (s : St) (hs : s.WF)
    (h : ∀ r, r < m → partF c k m r s = true) :
    ∀ adj, Model c adj → Compat s adj → False := by
  refine dfs1G_sound_fam (ι := Fin m) ⟨0, hm⟩ (deadAll c)
    (fun _ hs hd _ M hc => deadAll_sound hs M hc hd)
    (fun r => leafPartF c m r.val) ?_ 170 ((coreClauses c).take (5 * k)) s hs
    (fun r => h r.val r.isLt)
  intro s hs hall adj M hc
  have hr : leafPartF c m (stKey s % m) s = true := hall ⟨stKey s % m, Nat.mod_lt _ hm⟩
  unfold leafPartF at hr
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hr
  rcases hr with hr | hr
  · exact hr rfl
  · exact searchF_sound 170 20 20 s hs hr adj M hc

/-- Part `r` of the `m`-way split (prefix of `k` core vertices) of the fast
search for cell `c` from its initial state. -/
def cellPartF (c : Fin 3) (k m r : Nat) : Bool := partF c k m r (s0 c)

/-- If all parts of a split fast search return `true`, the canonical
five-high representative `c` is excluded. -/
theorem fiveHighCanonicalRepresentativeExcluded_of_partsF (c : Fin 3) (k m : Nat)
    (hm : 0 < m) (h : ∀ r, r < m → cellPartF c k m r = true) :
    FiveHighCanonicalRepresentativeExcluded c.val := by
  intro edges hc
  obtain ⟨M, hcompat⟩ := model_of_constraints c (adj := orderFortyNineBitAdj edges)
    (orderFortyNineBitAdj_comm edges)
    (fun a => by simp [orderFortyNineBitAdj]) hc
  exact partsF_sound k m hm (s0 c) (s0_wf c) h _ M hcompat

end H5
end Erdos85

#print axioms Erdos85.H5.searchF_sound
#print axioms Erdos85.H5.fiveHighCanonicalRepresentativeExcluded_of_partsF
