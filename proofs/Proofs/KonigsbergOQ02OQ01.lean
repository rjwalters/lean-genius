import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Proofs.KonigsbergOQ02

/-
  Konigsberg OQ-02-OQ-01: Corrected Directed Eulerian Circuit Theorem
  (Hierholzer's Algorithm)

  The axiom `directed_euler_circuit_sufficient` in KonigsbergOQ02.lean is
  MISSING the strong connectivity hypothesis:

    axiom directed_euler_circuit_sufficient ... (hbal : ∀ v, D.isBalanced v) :
        ∃ (v₀ : V) (w : D.Walk v₀ v₀), w.isEulerian

  Counterexample: Two disjoint directed triangles on V = {A, B, C, D, E, F}.
  Each triangle is balanced; no single trail can span both components.

  This file provides:
  1. `Digraph.isStronglyConnected`: the missing hypothesis definition
  2. `maximal_balanced_trail_is_circuit`: key sub-lemma (PROVED, 0 sorries)
     In a balanced digraph, any maximal Nodup trail ending at v₀ (where all
     out-arcs from v₀ are already in the trail) is a closed circuit.
  3. `Walk.splice`: concatenate two walks sharing a vertex (PROVED, 0 sorries)
  4. `Digraph.removeArcList`: subgraph removing a list of arcs (definition)
  5. `removeArcList_arcCount`: residual arcCount = D.arcCount - removed (PROVED)
  6. `removeArcList_balanced`: balance preserved when removing a circuit (PROVED)
  7. `directed_euler_circuit_sufficient_corrected`: corrected statement with
     `hconn : D.isStronglyConnected`; Hierholzer WF induction is sorry'd.

  The key sub-lemmas, splice constructor, and both residual lemmas form the
  complete mathematical infrastructure for Hierholzer's algorithm. The remaining
  sorry is purely the well-founded induction combining them.

  Parent: KonigsbergOQ02.lean (Digraph, Walk, isEulerian, degree definitions)
-/

set_option linter.unusedVariables false

namespace KonigsbergOQ02OQ01

open KonigsbergOQ02

-- ============================================================
-- PART I: Auxiliary List Lemmas
-- ============================================================

-- These are reproved here because `path_fst_snd_eq` and `circuit_fst_perm_snd`
-- are `private` in OQ02.

/-- For a chain walk, the tail's fst components equal the dropLast's snd components. -/
private theorem chain_tail_fst_eq_dropLast_snd {α : Type*} :
    ∀ (L : List (α × α)), L.Chain' (fun a b => a.2 = b.1) →
    L.tail.map Prod.fst = L.dropLast.map Prod.snd
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: rest, hchain => by
    have hab := List.Chain'.rel_head hchain
    have ih := chain_tail_fst_eq_dropLast_snd (b :: rest) (List.Chain'.tail hchain)
    simp only [List.tail_cons] at ih
    show (b :: rest).map Prod.fst = (a :: (b :: rest).dropLast).map Prod.snd
    rw [List.map_cons, List.map_cons, ← hab, ← ih]

/-- For a chain walk, `[start] ++ map snd = map fst ++ [end]`. -/
private theorem path_fst_snd_eq {α : Type*} [DecidableEq α]
    (L : List (α × α)) (hchain : L.Chain' (fun a b => a.2 = b.1))
    (hne : L ≠ []) :
    [(L.head hne).1] ++ L.map Prod.snd = L.map Prod.fst ++ [(L.getLast hne).2] := by
  have htail := chain_tail_fst_eq_dropLast_snd L hchain
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

/-- For a circuit walk (chain + starts at u, ends at u), the multiset of
    arc sources is a permutation of the multiset of arc targets. -/
private theorem circuit_fst_perm_snd {α : Type*} [DecidableEq α]
    (L : List (α × α)) (hchain : L.Chain' (fun a b => a.2 = b.1))
    (hne : L ≠ [])
    (hcirc : (L.head hne).1 = (L.getLast hne).2) :
    List.Perm (L.map Prod.fst) (L.map Prod.snd) := by
  have htail := chain_tail_fst_eq_dropLast_snd L hchain
  have hfst : L.map Prod.fst = (L.head hne).1 :: L.tail.map Prod.fst := by
    cases L with | nil => exact absurd rfl hne | cons h t => simp
  have hsnd : L.map Prod.snd = L.dropLast.map Prod.snd ++ [(L.getLast hne).2] := by
    cases L with
    | nil => exact absurd rfl hne
    | cons h t =>
      conv_lhs => rw [show h :: t = (h :: t).dropLast ++ [(h :: t).getLast (by simp)] from
        ((h :: t).dropLast_append_getLast (by simp)).symm]
      simp [List.map_append]
  rw [hfst, htail, hsnd, hcirc]
  rw [List.perm_iff_count]; intro x
  simp [List.count_cons, List.count_append, Nat.add_comm]

-- ============================================================
-- PART II: Strong Connectivity
-- ============================================================

/-- A digraph is **strongly connected** if every vertex is reachable from every
    other vertex via a directed walk.

    This is the hypothesis missing from `directed_euler_circuit_sufficient`
    in KonigsbergOQ02.lean. Without it, a disjoint union of two balanced
    digraphs satisfies `hbal` but has no Eulerian circuit spanning both
    components. -/
def isStronglyConnected {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) : Prop :=
  ∀ u v : V, Nonempty (D.Walk u v)

-- ============================================================
-- PART III: Helper Counting Lemmas
-- ============================================================

/-- If every out-arc from `v` appears in the trail (the "stuck" condition),
    and the trail is Nodup, then the count of arcs with source `v` equals
    `outDegree v`. -/
private theorem fst_count_eq_outDegree_stuck {V : Type*} [Fintype V] [DecidableEq V]
    {D : Digraph V} [DecidableRel D.adj] {u v₀ : V}
    (w : D.Walk u v₀) (hnodup : w.arcs.Nodup) (v : V)
    (hstuck : ∀ x : V, D.adj v x → (v, x) ∈ w.arcs) :
    (w.arcs.filter (fun a => decide (a.1 = v))).length = D.outDegree v := by
  unfold Digraph.outDegree Digraph.outNeighbors
  rw [show (w.arcs.filter (fun a => decide (a.1 = v))).length =
      (w.arcs.toFinset.filter (fun a : V × V => a.1 = v)).card from by
    rw [← List.toFinset_card_of_nodup (hnodup.filter _)]
    congr 1; ext ⟨a, b⟩
    simp [List.mem_toFinset, Finset.mem_filter, List.mem_filter, decide_eq_true_eq]]
  have heq : w.arcs.toFinset.filter (fun a : V × V => a.1 = v) =
      (Finset.univ.filter (D.adj v)).image (fun x => (v, x)) := by
    ext ⟨a, b⟩
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_image]
    constructor
    · rintro ⟨hmem, rfl⟩
      exact ⟨b, w.arcs_valid _ hmem, rfl⟩
    · rintro ⟨x, hadj, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ⟨hstuck x hadj, rfl⟩
  rw [heq, Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).2)]

/-- For a Nodup trail, the count of arcs with target `v` is at most `inDegree v`. -/
private theorem snd_count_le_inDegree {V : Type*} [Fintype V] [DecidableEq V]
    {D : Digraph V} [DecidableRel D.adj] {u v₀ : V}
    (w : D.Walk u v₀) (hnodup : w.arcs.Nodup) (v : V) :
    (w.arcs.filter (fun a => decide (a.2 = v))).length ≤ D.inDegree v := by
  unfold Digraph.inDegree Digraph.inNeighbors
  calc (w.arcs.filter (fun a => decide (a.2 = v))).length
      = (w.arcs.toFinset.filter (fun a : V × V => a.2 = v)).card := by
          rw [← List.toFinset_card_of_nodup (hnodup.filter _)]
          congr 1; ext ⟨a, b⟩
          simp [List.mem_toFinset, Finset.mem_filter, List.mem_filter, decide_eq_true_eq]
    _ ≤ ((Finset.univ.filter (fun u => D.adj u v)).image (fun a => (a, v))).card := by
          apply Finset.card_le_card
          intro ⟨a, b⟩
          simp only [Finset.mem_filter, List.mem_toFinset, Finset.mem_image,
                     Finset.mem_univ, true_and]
          rintro ⟨hmem, rfl⟩
          exact ⟨a, w.arcs_valid _ (List.mem_toFinset.mp hmem), rfl⟩
    _ = (Finset.univ.filter (fun u => D.adj u v)).card :=
          Finset.card_image_of_injective _ (fun _ _ h => (Prod.mk.inj h).1)

-- ============================================================
-- PART IV: Key Sub-Lemma — Maximal Trail is a Circuit
-- ============================================================

/-- **Key Lemma (Hierholzer's Algorithm)**: In a balanced digraph, any maximal
    Nodup trail is a closed circuit.

    A "maximal" trail is one that cannot be extended: all out-arcs from the
    endpoint `v₀` are already contained in the trail (`hstuck`). Balance then
    forces the trail to be closed, i.e., `u = v₀`. -/
theorem maximal_balanced_trail_is_circuit {V : Type*} [Fintype V] [DecidableEq V]
    {D : Digraph V} [DecidableRel D.adj]
    {u v₀ : V}
    (w : D.Walk u v₀)
    (hnodup : w.arcs.Nodup)
    (hstuck : ∀ x : V, D.adj v₀ x → (v₀, x) ∈ w.arcs)
    (hbal : ∀ v : V, D.isBalanced v) :
    u = v₀ := by
  by_cases hempty : w.arcs = []
  · exact w.empty_at hempty
  · have heq := path_fst_snd_eq w.arcs w.consecutive hempty
    rw [w.starts_at hempty, w.ends_at hempty] at heq
    have cmf : ∀ (f : (V × V) → V) (l : List (V × V)) (b : V),
        (l.map f).count b = (l.filter (fun a => decide (f a = b))).length := by
      intro f l b; induction l with
      | nil => simp
      | cons h t ih =>
        simp only [List.map_cons, List.count_cons, List.filter_cons]
        split <;> simp_all [List.count]
    have h := congr_arg (List.count v₀) heq
    simp only [List.count_append] at h
    rw [cmf Prod.snd, cmf Prod.fst] at h
    rw [fst_count_eq_outDegree_stuck w hnodup v₀ hstuck] at h
    have h1 : List.count v₀ [v₀] = 1 := by simp
    rw [h1] at h
    have hsnd := snd_count_le_inDegree w hnodup v₀
    have hbal_eq : D.inDegree v₀ = D.outDegree v₀ := hbal v₀
    by_contra hne
    have hcount0 : List.count v₀ [u] = 0 := by
      simp only [List.count_cons, List.count_nil]
      simp [show ¬(v₀ = u) from fun h => hne h.symm]
    rw [hcount0] at h
    omega

-- ============================================================
-- PART V: Walk Concatenation (Splice)
-- ============================================================

/-- **Walk concatenation (splice)**: Given walks `w1 : D.Walk u v` and
    `w2 : D.Walk v w`, construct `w1.splice w2 : D.Walk u w` by appending
    the arc lists.

    This is the fundamental operation needed for Hierholzer's algorithm:
    once we find a new circuit C' from a vertex u that lies on our current
    circuit C, we splice C' into C at u to get a longer circuit. -/
def Digraph.Walk.splice {V : Type*} {D : Digraph V} {u v w : V}
    (w1 : D.Walk u v) (w2 : D.Walk v w) : D.Walk u w where
  arcs := w1.arcs ++ w2.arcs
  arcs_valid a ha := by
    rw [List.mem_append] at ha
    exact ha.elim w1.arcs_valid w2.arcs_valid
  starts_at h := by
    by_cases h1 : w1.arcs = []
    · simp only [h1, List.nil_append] at h ⊢
      rw [← w1.empty_at h1]
      exact w2.starts_at h
    · -- w1.arcs = hd :: tl; head of concat is hd
      obtain ⟨hd, tl, hl⟩ : ∃ hd tl, w1.arcs = hd :: tl := by
        cases w1.arcs with
        | nil => exact absurd rfl h1
        | cons hd tl => exact ⟨hd, tl, rfl⟩
      rw [hl]
      simp only [List.cons_append, List.head_cons]
      have := w1.starts_at h1
      rw [hl] at this
      simpa using this
  ends_at h := by
    by_cases h2 : w2.arcs = []
    · have hne1 : w1.arcs ≠ [] := by
        intro h1; simp [h1, h2] at h
      rw [h2, List.append_nil] at h ⊢
      rw [← w2.empty_at h2]
      exact w1.ends_at hne1
    · rw [List.getLast_append_of_right_ne_nil w1.arcs w2.arcs h2]
      exact w2.ends_at h2
  consecutive := by
    rw [isChain_append]
    refine ⟨w1.consecutive, w2.consecutive, ?_⟩
    intro x hx y hy
    -- x ∈ w1.arcs.getLast? → ∃ h, x = w1.arcs.getLast h
    obtain ⟨hne1, hxeq⟩ := List.mem_getLast?_eq_getLast hx
    -- y ∈ w2.arcs.head? → w2.arcs = y :: w2.arcs.tail
    have hcons2 := List.eq_cons_of_mem_head? hy
    have hne2 : w2.arcs ≠ [] := by rw [hcons2]; exact List.cons_ne_nil _ _
    have hyhead : w2.arcs.head hne2 = y := by
      conv_lhs => rw [hcons2]; simp
    -- x.2 = v (w1 ends at v) and y.1 = v (w2 starts at v)
    rw [hxeq, ← hyhead]
    exact (w1.ends_at hne1).trans (w2.starts_at hne2).symm
  empty_at h := by
    rw [List.append_eq_nil] at h
    exact (w1.empty_at h.1).trans (w2.empty_at h.2)

/-- The arcs of a splice are the concatenation of the component arcs. -/
@[simp]
theorem Digraph.Walk.splice_arcs {V : Type*} {D : Digraph V} {u v w : V}
    (w1 : D.Walk u v) (w2 : D.Walk v w) :
    (w1.splice w2).arcs = w1.arcs ++ w2.arcs := rfl

/-- Splicing a nodup-disjoint pair of circuits yields a nodup walk. -/
theorem Digraph.Walk.splice_nodup {V : Type*} {D : Digraph V} {u v w : V}
    (w1 : D.Walk u v) (w2 : D.Walk v w)
    (h1 : w1.arcs.Nodup) (h2 : w2.arcs.Nodup)
    (hdisj : ∀ a, a ∈ w1.arcs → a ∉ w2.arcs) :
    (w1.splice w2).arcs.Nodup := by
  simp only [splice_arcs]
  exact List.nodup_append.mpr ⟨h1, h2, fun a ha1 ha2 => hdisj a ha1 ha2⟩

-- ============================================================
-- PART VI: Residual Subgraph
-- ============================================================

/-- Remove a list of arcs from a digraph, yielding the residual subgraph.

    Note: defined as a standalone function (not `Digraph.removeArcList`) to
    avoid namespace resolution issues with dot notation in theorem signatures. -/
def removeArcList {V : Type*} (D : Digraph V) (arcs : List (V × V)) :
    Digraph V where
  adj u v := D.adj u v ∧ (u, v) ∉ arcs
  loopless v h := D.loopless v h.1

instance {V : Type*} [Fintype V] [DecidableEq V] (D : Digraph V) [DecidableRel D.adj]
    (arcs : List (V × V)) : DecidableRel (removeArcList D arcs).adj :=
  fun u v => inferInstance

/-- Adjacency characterization in the residual. -/
theorem removeArcList_adj_iff {V : Type*} (D : Digraph V) (arcs : List (V × V))
    (u v : V) : (removeArcList D arcs).adj u v ↔ D.adj u v ∧ (u, v) ∉ arcs := Iff.rfl

/-- A walk in the residual `removeArcList D arcs` lifts to a walk in D. -/
def Digraph.Walk.ofRemoveArcList {V : Type*} {D : Digraph V}
    {arcs : List (V × V)} {u v : V}
    (w : (removeArcList D arcs).Walk u v) : D.Walk u v where
  arcs := w.arcs
  arcs_valid a ha := (w.arcs_valid a ha).1
  starts_at := w.starts_at
  ends_at := w.ends_at
  consecutive := w.consecutive
  empty_at := w.empty_at

/-- The arcCount of the residual is the arcCount minus removed arcs.

    More precisely: if `arcs_list` is a sublist of D's arcs with no duplicates,
    then `(removeArcList D arcs_list).arcCount = D.arcCount - arcs_list.length`. -/
theorem removeArcList_arcCount {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) [DecidableRel D.adj] (arcs_list : List (V × V))
    (hvalid : ∀ a ∈ arcs_list, D.adj a.1 a.2) (hnodup : arcs_list.Nodup) :
    (removeArcList D arcs_list).arcCount =
    D.arcCount - arcs_list.length := by
  -- The arc set of the residual is the arc set of D minus arcs_list.toFinset.
  -- Since arcs_list ⊆ D's arcs and arcs_list is nodup (so |arcs_list.toFinset| = arcs_list.length),
  -- the result follows from Finset.card_sdiff.
  unfold Digraph.arcCount
  -- S' = {p | D.adj p.1 p.2 ∧ p ∉ arcs_list} = S \ T where S = D's arcs, T = arcs_list.toFinset
  have hset_eq :
      Finset.univ.filter (fun p : V × V => (removeArcList D arcs_list).adj p.1 p.2) =
      Finset.univ.filter (fun p : V × V => D.adj p.1 p.2) \ arcs_list.toFinset := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_sdiff, List.mem_toFinset]
    exact removeArcList_adj_iff D arcs_list u v
  -- T ⊆ S (all listed arcs are D-arcs)
  have hT_sub : arcs_list.toFinset ⊆
      Finset.univ.filter (fun p : V × V => D.adj p.1 p.2) := by
    intro p hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_toFinset] at *
    exact hvalid p hmem
  rw [hset_eq, Finset.card_sdiff hT_sub, List.toFinset_card_of_nodup hnodup]

/-- Removing a circuit preserves balance at every vertex.

    **Proof sketch**: For any vertex v:
    - `outDeg(D') v = outDeg(D) v - |{(v,x) ∈ circuit}|`
    - `inDeg(D') v = inDeg(D) v - |{(x,v) ∈ circuit}|`
    - By `circuit_fst_perm_snd`, `|{(v,x) ∈ circuit}| = |{(x,v) ∈ circuit}|`
    - Since D is balanced, `outDeg(D) v = inDeg(D) v`
    - Therefore `outDeg(D') v = inDeg(D') v`. -/
theorem removeArcList_balanced {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) [DecidableRel D.adj]
    (arcs_list : List (V × V))
    (hchain : arcs_list.Chain' (fun a b => a.2 = b.1))
    (hnodup : arcs_list.Nodup)
    (hcirc_or_empty : arcs_list = [] ∨ ∃ hne : arcs_list ≠ [],
        (arcs_list.head hne).1 = (arcs_list.getLast hne).2)
    (hvalid : ∀ a ∈ arcs_list, D.adj a.1 a.2)
    (hbal : ∀ v : V, D.isBalanced v) :
    ∀ v : V, (removeArcList D arcs_list).isBalanced v := by
  -- For any v:
  --   outDeg(D') v = outDeg(D) v - |{x | (v,x) ∈ arcs_list}|
  --   inDeg(D') v  = inDeg(D) v  - |{x | (x,v) ∈ arcs_list}|
  -- By circuit_fst_perm_snd: these subtracted quantities are equal (count of v in fst = snd).
  -- By hbal: outDeg(D) v = inDeg(D) v.  Therefore outDeg(D') v = inDeg(D') v.
  intro v
  unfold Digraph.isBalanced Digraph.inDegree Digraph.outDegree
         Digraph.inNeighbors Digraph.outNeighbors
  -- A_src = {x | (v,x) ∈ arcs_list} as a Finset ⊆ outNeighbors D v
  -- A_tgt = {x | (x,v) ∈ arcs_list} as a Finset ⊆ inNeighbors D v
  -- Use Finset.image to avoid needing nodup of the mapped list
  set A_src : Finset V :=
    (arcs_list.toFinset.filter (fun a : V × V => a.1 = v)).image Prod.snd
  set A_tgt : Finset V :=
    (arcs_list.toFinset.filter (fun a : V × V => a.2 = v)).image Prod.fst
  -- outNeighbors D' v = outNeighbors D v \ A_src
  have hout_sdiff : Finset.univ.filter ((removeArcList D arcs_list).adj v) =
      Finset.univ.filter (D.adj v) \ A_src := by
    ext x
    simp only [A_src, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
               Finset.mem_image, Finset.mem_filter, List.mem_toFinset, removeArcList_adj_iff]
    constructor
    · rintro ⟨hadj, hnotin⟩
      exact ⟨hadj, fun ⟨⟨a1, a2⟩, ⟨hmem, ha1⟩, rfl⟩ => hnotin (ha1 ▸ hmem)⟩
    · rintro ⟨hadj, hnotin⟩
      exact ⟨hadj, fun hc => hnotin ⟨(v, x), ⟨hc, rfl⟩, rfl⟩⟩
  -- inNeighbors D' v = inNeighbors D v \ A_tgt
  have hin_sdiff : Finset.univ.filter (fun x => (removeArcList D arcs_list).adj x v) =
      Finset.univ.filter (D.adj · v) \ A_tgt := by
    ext x
    simp only [A_tgt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff,
               Finset.mem_image, Finset.mem_filter, List.mem_toFinset, removeArcList_adj_iff]
    constructor
    · rintro ⟨hadj, hnotin⟩
      exact ⟨hadj, fun ⟨⟨a1, a2⟩, ⟨hmem, ha2⟩, rfl⟩ => hnotin (ha2 ▸ hmem)⟩
    · rintro ⟨hadj, hnotin⟩
      exact ⟨hadj, fun hc => hnotin ⟨(x, v), ⟨hc, rfl⟩, rfl⟩⟩
  -- A_src ⊆ outNeighbors D v
  have hA_src_sub : A_src ⊆ Finset.univ.filter (D.adj v) := by
    intro x hx
    simp only [A_src, Finset.mem_image, Finset.mem_filter, List.mem_toFinset] at hx
    obtain ⟨⟨a1, a2⟩, ⟨hmem, ha1⟩, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := hvalid _ hmem; rwa [← ha1] at this
  -- A_tgt ⊆ inNeighbors D v
  have hA_tgt_sub : A_tgt ⊆ Finset.univ.filter (D.adj · v) := by
    intro x hx
    simp only [A_tgt, Finset.mem_image, Finset.mem_filter, List.mem_toFinset] at hx
    obtain ⟨⟨a1, a2⟩, ⟨hmem, ha2⟩, rfl⟩ := hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := hvalid _ hmem; rwa [← ha2] at this
  -- A_src.card = arcs_list.filter (·.1=v) length (injective Prod.snd on fst-filtered pairs)
  have hA_src_card : A_src.card = (arcs_list.filter (fun a => a.1 = v)).length := by
    rw [show A_src.card =
            (arcs_list.toFinset.filter (fun a : V × V => a.1 = v)).card from
          Finset.card_image_of_injOn (fun ⟨a1, b1⟩ ha1 ⟨a2, b2⟩ ha2 (h : b1 = b2) => by
            simp only [Finset.mem_filter, List.mem_toFinset] at ha1 ha2
            simp [ha1.2, ha2.2, h])]
    rw [show arcs_list.toFinset.filter (fun a : V × V => a.1 = v) =
            (arcs_list.filter (fun a => a.1 = v)).toFinset from by
          ext a; simp [List.mem_toFinset, List.mem_filter],
        List.toFinset_card_of_nodup (hnodup.sublist (List.filter_sublist _))]
  -- A_tgt.card = arcs_list.filter (·.2=v) length (injective Prod.fst on snd-filtered pairs)
  have hA_tgt_card : A_tgt.card = (arcs_list.filter (fun a => a.2 = v)).length := by
    rw [show A_tgt.card =
            (arcs_list.toFinset.filter (fun a : V × V => a.2 = v)).card from
          Finset.card_image_of_injOn (fun ⟨a1, b1⟩ ha1 ⟨a2, b2⟩ ha2 (h : a1 = a2) => by
            simp only [Finset.mem_filter, List.mem_toFinset] at ha1 ha2
            simp [ha1.2, ha2.2, h])]
    rw [show arcs_list.toFinset.filter (fun a : V × V => a.2 = v) =
            (arcs_list.filter (fun a => a.2 = v)).toFinset from by
          ext a; simp [List.mem_toFinset, List.mem_filter],
        List.toFinset_card_of_nodup (hnodup.sublist (List.filter_sublist _))]
  -- Count equality: filter(·.1=v).length = filter(·.2=v).length
  -- via circuit_fst_perm_snd + count bridge (same pattern as in KonigsbergOQ02.lean)
  have hcount_eq : (arcs_list.filter (fun a : V × V => a.1 = v)).length =
      (arcs_list.filter (fun a : V × V => a.2 = v)).length := by
    -- Bridge: (l.map f).count b = (l.filter (fun a => decide (f a = b))).length
    -- (proved by induction, same as `cmf` in KonigsbergOQ02.lean)
    have cmf : ∀ (f : (V × V) → V) (l : List (V × V)) (b : V),
        (l.map f).count b = (l.filter (fun a => decide (f a = b))).length := by
      intro f l b; induction l with
      | nil => simp
      | cons h t ih =>
        simp only [List.map_cons, List.count_cons, List.filter_cons]
        split <;> simp_all [List.count]
    cases hcirc_or_empty with
    | inl hempty => simp [hempty]
    | inr hne =>
      obtain ⟨hne, hcirc⟩ := hne
      have hperm := circuit_fst_perm_snd arcs_list hchain hne hcirc
      have hcount := hperm.count_eq v
      rw [cmf, cmf] at hcount
      exact hcount
  -- Combine everything
  rw [hout_sdiff, hin_sdiff,
      Finset.card_sdiff hA_src_sub, Finset.card_sdiff hA_tgt_sub,
      hA_src_card, hA_tgt_card, hcount_eq]
  -- Goal: inDeg D v - n = outDeg D v - n, from hbal
  have hbal_v := hbal v
  unfold Digraph.isBalanced Digraph.inDegree Digraph.outDegree
         Digraph.inNeighbors Digraph.outNeighbors at hbal_v
  omega

-- ============================================================
-- PART VII: Corrected Main Theorem
-- ============================================================

/-- **Corrected Directed Eulerian Circuit Sufficiency** (Hierholzer, 1873).

    The axiom `directed_euler_circuit_sufficient` in KonigsbergOQ02.lean
    (line 409) is INCORRECTLY STATED — it is missing `isStronglyConnected`.

    The corrected theorem: if D is strongly connected and every vertex is
    balanced (indeg = outdeg), then D has an Eulerian circuit.

    **Proof strategy** (Hierholzer's algorithm, WF induction on uncovered arcs):

    **Key Building Blocks** (all proved above):
    - `maximal_balanced_trail_is_circuit`: greedy trail from any v₀ in balanced D
      is always a circuit.
    - `Walk.splice`: concatenate two circuits at a shared vertex.
    - `removeArcList_balanced`: residual after removing circuit remains balanced.

    **Induction**:
    Let `C` be a circuit in D from v₀. We induct on `D.arcCount - C.arcs.length`.
    - Base: `D.arcCount = C.arcs.length` → C is Eulerian.
    - Step: Some vertex u on C has unused out-arcs (strong connectivity + balance).
      Build circuit C' from u in `removeArcList D C.arcs` (balanced by above).
      Splice C' into C via `Walk.splice`, increasing circuit length. Apply IH.

    **Remaining sorry**: The splice-based WF induction combining these lemmas. -/
theorem directed_euler_circuit_sufficient_corrected {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V]
    (D : Digraph V) [DecidableRel D.adj]
    (hbal : ∀ v : V, D.isBalanced v)
    (hconn : isStronglyConnected D) :
    ∃ (v₀ : V) (w : D.Walk v₀ v₀), w.isEulerian := by
  -- The remaining sorry is the WF induction combining:
  -- 1. maximal_balanced_trail_is_circuit (any greedy trail is a circuit)
  -- 2. Walk.splice (circuit extension at shared vertex)
  -- 3. removeArcList_balanced (residual remains balanced)
  -- The induction decreases on (D.arcCount - current_circuit_length).
  sorry

-- ============================================================
-- Summary
-- ============================================================

/-
### Results

**Proved (0 sorries)**:
- `maximal_balanced_trail_is_circuit`: In a balanced digraph, any maximal Nodup
  trail is a closed circuit. (Key sub-lemma of Hierholzer.)
- `Walk.splice`: Concatenate two walks sharing a vertex. (Infrastructure for
  Hierholzer's circuit extension step.)
- `Walk.splice_nodup`: Splice of arc-disjoint Nodup walks is Nodup.

**Helper Lemmas (proved)**:
- `fst_count_eq_outDegree_stuck`: count of arcs with source v = outDegree v
  (when the "stuck" condition holds)
- `snd_count_le_inDegree`: count of arcs with target v ≤ inDegree v
  (for any Nodup trail)
- `circuit_fst_perm_snd` (private): circuit's fst multiset ~ snd multiset

**Definitions**:
- `Digraph.isStronglyConnected`: ∀ u v, Nonempty (D.Walk u v)
- `Digraph.removeArcList`: subgraph removing specified arcs
- `Walk.ofRemoveArcList`: lift residual walk to parent graph

**Proved (this session)**:
- `removeArcList_arcCount`: arcCount of residual = D.arcCount - removed
  (Finset.card_sdiff argument: residual arcs = D_arcs \ listed_arcs)
- `removeArcList_balanced`: removing a circuit preserves balance at all vertices
  (circuit_fst_perm_snd → equal per-vertex fst/snd counts → equal subtraction from
   balanced inDeg/outDeg; Finset.card_image_of_injOn for count-via-image approach)

**Sorry'd (with structured proof roadmap)**:
- `directed_euler_circuit_sufficient_corrected`: WF induction combining all above

**Bug Found**:
- `directed_euler_circuit_sufficient` (KonigsbergOQ02.lean line 409) is an axiom
  with a MISSING hypothesis. The corrected version requires strong connectivity.
  Without it, two disjoint balanced directed graphs form a counterexample.
-/

#check @isStronglyConnected
#check @maximal_balanced_trail_is_circuit
#check @Digraph.Walk.splice
#check @directed_euler_circuit_sufficient_corrected

end KonigsbergOQ02OQ01
