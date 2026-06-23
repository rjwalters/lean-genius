import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Proofs.KonigsbergOQ02

/-
  Aristotle companion for KonigsbergOQ02OQ01.lean
  Targets: nodup_circuit_exists_Aristotle and vertex_with_unused_arc_Aristotle

  These are key sub-lemmas for Hierholzer's algorithm:
  1. In a balanced digraph, any vertex with positive out-degree has a nodup circuit.
  2. In a balanced+strongly-connected digraph, if a nodup circuit doesn't cover all arcs,
     some vertex on the circuit has positive out-degree in the residual graph.
-/

namespace KonigsbergOQ02OQ01Aristotle

open KonigsbergOQ02

-- ============================================================
-- Path equation helpers (private in KonigsbergOQ02, reproduced here)
-- ============================================================

private theorem chain_tail_fst_eq_dropLast_snd_ari {α : Type*} :
    ∀ (L : List (α × α)), L.Chain' (fun a b => a.2 = b.1) →
    L.tail.map Prod.fst = L.dropLast.map Prod.snd
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: rest, hchain => by
    have hab := List.Chain'.rel_head hchain
    have ih := chain_tail_fst_eq_dropLast_snd_ari (b :: rest) (List.Chain'.tail hchain)
    simp only [List.tail_cons] at ih
    show (b :: rest).map Prod.fst = (a :: (b :: rest).dropLast).map Prod.snd
    rw [List.map_cons, List.map_cons, ← hab, ← ih]

private theorem path_fst_snd_eq_ari {α : Type*} [DecidableEq α]
    (L : List (α × α)) (hchain : L.Chain' (fun a b => a.2 = b.1))
    (hne : L ≠ []) :
    [(L.head hne).1] ++ L.map Prod.snd = L.map Prod.fst ++ [(L.getLast hne).2] := by
  have htail := chain_tail_fst_eq_dropLast_snd_ari L hchain
  have hfst : L.map Prod.fst = (L.head hne).1 :: L.tail.map Prod.fst := by
    cases L with | nil => exact absurd rfl hne | cons h t => simp
  have hsnd : L.map Prod.snd = L.dropLast.map Prod.snd ++ [(L.getLast hne).2] := by
    cases L with
    | nil => exact absurd rfl hne
    | cons h t =>
      conv_lhs => rw [show h :: t = (h :: t).dropLast ++ [(h :: t).getLast (by simp)] from
        ((h :: t).dropLast_append_getLast (by simp)).symm]
      simp [List.map_append]
  rw [hfst, htail, hsnd]
  simp [List.singleton_append, List.cons_append, List.append_assoc]

-- ============================================================
-- Infrastructure (reproduced from KonigsbergOQ02OQ01.lean)
-- ============================================================

def isStronglyConnected {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) : Prop :=
  ∀ u v : V, Nonempty (D.Walk u v)

def removeArcList {V : Type*} (D : Digraph V) (arcs : List (V × V)) :
    Digraph V where
  adj u v := D.adj u v ∧ (u, v) ∉ arcs
  loopless v h := D.loopless v h.1

instance {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.adj]
    (arcs : List (V × V)) : DecidableRel (removeArcList D arcs).adj :=
  fun u v => by unfold removeArcList; simp only; exact instDecidableAnd

theorem removeArcList_adj_iff {V : Type*} (D : Digraph V) (arcs : List (V × V))
    (u v : V) : (removeArcList D arcs).adj u v ↔ D.adj u v ∧ (u, v) ∉ arcs := Iff.rfl

private def emptyWalk_at {V : Type*} {D : Digraph V} (v : V) : D.Walk v v where
  arcs := []
  arcs_valid _ h := absurd h List.not_mem_nil
  starts_at h := (h rfl).elim
  ends_at h := (h rfl).elim
  consecutive := List.isChain_nil
  empty_at _ := rfl

private theorem maximal_balanced_trail_is_circuit_copy {V : Type*} [Fintype V] [DecidableEq V]
    {D : Digraph V} [DecidableRel D.adj]
    {u v₀ : V}
    (w : D.Walk u v₀)
    (hnodup : w.arcs.Nodup)
    (hstuck : ∀ x : V, D.adj v₀ x → (v₀, x) ∈ w.arcs)
    (hbal : ∀ v : V, D.isBalanced v) :
    u = v₀ := by
  have h_count : (w.arcs.map Prod.fst).count v₀ = D.outDegree v₀ := by
    have h_count : (w.arcs.filter (fun a => a.1 = v₀)).length = D.outDegree v₀ := by
      have h_out : (w.arcs.filter (fun a => a.1 = v₀)).toFinset = Finset.image (fun x => (v₀, x)) (Finset.filter (fun x => D.adj v₀ x) Finset.univ) := by
        ext ⟨x, y⟩; simp [hstuck];
        constructor <;> intro h <;> have := w.arcs_valid ( x, y ) <;> aesop;
      convert congr_arg Finset.card h_out using 1;
      · rw [ List.toFinset_card_of_nodup ];
        exact hnodup.filter _;
      · rw [ Finset.card_image_of_injective _ fun x y hxy => by injection hxy ] ; rfl;
    rw [ ← h_count, List.count ];
    rw [ List.countP_map ];
    rw [ List.countP_eq_length_filter ] ; aesop;
  have h_count_snd : (w.arcs.map Prod.snd).count v₀ ≤ D.inDegree v₀ := by
    have h_count_snd : (w.arcs.map Prod.snd).count v₀ ≤ (w.arcs.filter (fun a => a.snd = v₀)).length := by
      rw [ List.count ];
      rw [ List.countP_map ];
      rw [ List.countP_eq_length_filter ] ; aesop;
    have h_count_snd : (w.arcs.filter (fun a => a.snd = v₀)).toFinset.card ≤ (Finset.univ.filter (fun u => D.adj u v₀)).card := by
      have h_count_snd : (w.arcs.filter (fun a => a.snd = v₀)).toFinset.image Prod.fst ⊆ Finset.univ.filter (fun u => D.adj u v₀) := by
        simp +decide [ Finset.subset_iff ];
        exact fun x hx => w.arcs_valid _ hx;
      have := Finset.card_le_card h_count_snd;
      rwa [ Finset.card_image_of_injOn ] at this;
      intro x hx y hy; aesop;
    exact le_trans ‹_› ( by rw [ List.toFinset_card_of_nodup ( List.Nodup.filter _ hnodup ) ] at h_count_snd; exact h_count_snd );
  by_cases h : w.arcs = [] <;> simp_all +decide [ Digraph.isBalanced ];
  · exact w.empty_at h;
  · have h_count_eq : ([(w.arcs.head h).1] ++ w.arcs.map Prod.snd).count v₀ = (w.arcs.map Prod.fst ++ [(w.arcs.getLast h).2]).count v₀ := by
      rw [ path_fst_snd_eq_ari _ w.consecutive h ];
    simp_all +decide [ List.count_cons ];
    have := w.starts_at h; have := w.ends_at h; aesop;

/-
============================================================
TARGET 1: nodup_circuit_exists_Aristotle
============================================================
-/
theorem nodup_circuit_exists_Aristotle {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) [DecidableRel D.adj]
    (hbal : ∀ v : V, D.isBalanced v)
    (u : V) (hout : 0 < D.outDegree u) :
    ∃ (C : D.Walk u u), C.arcs.Nodup ∧ C.arcs ≠ [] := by
  -- Use a classical maximum-length argument.
  -- Consider S = {n : ℕ | ∃ v, ∃ w : D.Walk u v, w.arcs.Nodup ∧ w.arcs.length = n}.
  set S := {n : ℕ | ∃ v : V, ∃ w : D.Walk u v, w.arcs.Nodup ∧ w.arcs.length = n} with hS_def
  have hS_nonempty : S.Nonempty := by
    exact ⟨ _, ⟨ u, emptyWalk_at u, List.nodup_nil, rfl ⟩ ⟩
  have hS_bounded : BddAbove S := by
    refine' ⟨ Finset.card ( Finset.univ.filter fun p : V × V => D.adj p.1 p.2 ), fun n hn => _ ⟩;
    obtain ⟨ v, w, hn, rfl ⟩ := hn;
    exact le_trans ( List.toFinset_card_of_nodup hn ▸ Finset.card_le_card ( show _ ⊆ Finset.filter ( fun p : V × V => D.adj p.1 p.2 ) Finset.univ from fun p hp => by have := w.arcs_valid p ( List.mem_toFinset.mp hp ) ; aesop ) ) ( by simp +decide );
  -- Let m = Nat.find (max element). Take a maximal nodup walk W from u to some vertex v of length m.
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m ∈ S ∧ ∀ n ∈ S, n ≤ m := by
    exact ⟨ Finset.max' ( Set.Finite.toFinset ( Set.finite_iff_bddAbove.mpr hS_bounded ) ) ⟨ _, by simpa using hS_nonempty.choose_spec ⟩, by simpa using Finset.max'_mem ( Set.Finite.toFinset ( Set.finite_iff_bddAbove.mpr hS_bounded ) ) ⟨ _, by simpa using hS_nonempty.choose_spec ⟩, fun n hn => Finset.le_max' _ _ ( by simpa using hn ) ⟩
  obtain ⟨v, w, hw_nodup, hw_len⟩ : ∃ v : V, ∃ w : D.Walk u v, w.arcs.Nodup ∧ w.arcs.length = m := by
    exact hm.1;
  -- W is stuck at v: for any x with D.adj v x, the arc (v,x) must already be in W.arcs (otherwise we could extend W by appending (v,x), getting a nodup walk of length m+1, contradicting maximality).
  have hw_stuck : ∀ x : V, D.adj v x → (v, x) ∈ w.arcs := by
    intro x hx
    by_contra h_contra
    have h_extend : ∃ w' : D.Walk u x, w'.arcs.Nodup ∧ w'.arcs.length = m + 1 := by
      refine' ⟨ ⟨ w.arcs ++ [ ( v, x ) ], _, _, _, _, _ ⟩, _, _ ⟩ <;> simp_all +decide [ List.nodup_append ];
      · rintro a b ( h | ⟨ rfl, rfl ⟩ ) <;> [ exact w.arcs_valid _ h; exact hx ];
      · grind +splitImp;
      · refine' List.isChain_append.mpr ⟨ _, _, _ ⟩;
        · exact w.consecutive;
        · exact List.isChain_singleton _;
        · have := w.ends_at; simp_all +decide [ List.getLast?_eq_some_getLast ] ;
          grind +splitImp;
      · grind +locals;
    exact not_lt_of_ge ( hm.2 _ ⟨ x, h_extend.choose, h_extend.choose_spec.1, h_extend.choose_spec.2 ⟩ ) ( by linarith [ h_extend.choose_spec.2 ] );
  -- By maximal_balanced_trail_is_circuit_copy (with hbal and hstuck): u = v. So W is a circuit.
  have hw_circuit : u = v := by
    apply maximal_balanced_trail_is_circuit_copy w hw_nodup hw_stuck hbal;
  by_cases hw_empty : w.arcs = [] <;> simp_all +decide;
  · exact absurd hout ( by rw [ show D.outDegree v = 0 from by rw [ Digraph.outDegree ] ; exact Finset.card_eq_zero.mpr <| Finset.eq_empty_of_forall_notMem fun x hx => hw_stuck x <| Finset.mem_filter.mp hx |>.2 ] ; linarith );
  · bound

/-
============================================================
TARGET 2: vertex_with_unused_arc_Aristotle
============================================================

If a walk goes from a vertex in S to a vertex outside S, some arc exits S.
-/
private lemma walk_exits_set {V : Type*} [Fintype V] [DecidableEq V]
    {D : Digraph V} {u v : V}
    (w : D.Walk u v) (S : Finset V)
    (hu : u ∈ S) (hv : v ∉ S) :
    ∃ a ∈ w.arcs, a.1 ∈ S ∧ a.2 ∉ S := by
  rcases w with ⟨ arcs, _, starts_at, ends_at, consecutive, empty_at ⟩;
  induction' arcs with arc arcs ih generalizing u v;
  · grind;
  · by_cases h : arc.2 ∈ S;
    · rcases arcs <;> simp_all +decide;
      · grind;
      · cases consecutive ; aesop;
    · exact ⟨ arc, List.mem_cons_self, by aesop ⟩

/-
If all D-outDeg from V(C) are zero in the residual graph,
    then every D-arc from V(C) is in C.arcs.
-/
private lemma all_arcs_covered {V : Type*} [Fintype V] [DecidableEq V]
    {D : Digraph V} [DecidableRel D.adj]
    (carcs : List (V × V)) (S : Finset V)
    (h : ∀ u ∈ S, (removeArcList D carcs).outDegree u = 0) :
    ∀ u v : V, u ∈ S → D.adj u v → (u, v) ∈ carcs := by
  contrapose! h;
  obtain ⟨ u, v, hu, hv, huv ⟩ := h;
  refine' ⟨ u, hu, _ ⟩;
  refine' ne_of_gt ( Finset.card_pos.mpr ⟨ v, _ ⟩ );
  exact Finset.mem_filter.mpr ⟨ Finset.mem_univ _, hv, huv ⟩

/-
The snd of every arc in a circuit starting at v₀ is in {v₀} ∪ (arcs.map snd).toFinset
-/
private lemma arc_snd_in_VC {V : Type*} [DecidableEq V]
    (arcs : List (V × V)) (v₀ : V) :
    ∀ a ∈ arcs, a.2 ∈ ({v₀} : Finset V) ∪ (arcs.map Prod.snd).toFinset := by
  aesop

theorem vertex_with_unused_arc_Aristotle {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) [DecidableRel D.adj]
    (hbal : ∀ v : V, D.isBalanced v)
    (hconn : isStronglyConnected D)
    {v₀ : V} (C : D.Walk v₀ v₀) (hnodup : C.arcs.Nodup)
    (hextra : C.arcs.length < D.arcCount) :
    ∃ u ∈ ({v₀} : Finset V) ∪ (C.arcs.map Prod.snd).toFinset,
      0 < (removeArcList D C.arcs).outDegree u := by
  contrapose! hextra;
  -- By all_arcs_covered, every D-arc (u,v) with u ∈ VC is in C.arcs.
  have h_all_arcs_covered : ∀ u v : V, u ∈ ({v₀} : Finset V) ∪ (C.arcs.map Prod.snd).toFinset → D.adj u v → (u, v) ∈ C.arcs := by
    apply all_arcs_covered;
    exact fun u hu => le_antisymm ( hextra u hu ) ( Nat.zero_le _ );
  have h_VC_univ : ({v₀} : Finset V) ∪ (C.arcs.map Prod.snd).toFinset = Finset.univ := by
    by_contra h_contra;
    obtain ⟨w, hw⟩ : ∃ w, w ∉ ({v₀} : Finset V) ∪ (C.arcs.map Prod.snd).toFinset := by
      exact not_forall.mp fun h => h_contra <| Finset.eq_univ_of_forall h;
    obtain ⟨p, hp⟩ : ∃ p : D.Walk v₀ w, True := by
      exact ⟨ hconn v₀ w |> Classical.choice, trivial ⟩;
    obtain ⟨a, ha⟩ : ∃ a ∈ p.arcs, a.1 ∈ ({v₀} : Finset V) ∪ (C.arcs.map Prod.snd).toFinset ∧ a.2 ∉ ({v₀} : Finset V) ∪ (C.arcs.map Prod.snd).toFinset := by
      apply walk_exits_set;
      · simp +decide;
      · exact hw;
    have := h_all_arcs_covered _ _ ha.2.1 ( p.arcs_valid _ ha.1 ) ; aesop;
  have h_all_arcs_covered : Finset.univ.filter (fun p : V × V => D.adj p.1 p.2) ⊆ C.arcs.toFinset := by
    intro p hp; specialize h_all_arcs_covered p.1 p.2; aesop;
  exact le_trans ( Finset.card_le_card h_all_arcs_covered ) ( List.toFinset_card_le _ )

end KonigsbergOQ02OQ01Aristotle
