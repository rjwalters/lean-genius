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
-- PART VII: Infrastructure for Hierholzer's Induction
-- ============================================================

/-- The trivial empty circuit at any vertex v. -/
private def emptyWalk_at {V : Type*} {D : Digraph V} (v : V) : D.Walk v v where
  arcs := []
  arcs_valid _ h := (List.not_mem_nil _ h).elim
  starts_at h := (h rfl).elim
  ends_at h := (h rfl).elim
  consecutive := List.Chain'.nil
  empty_at _ := rfl

/-- A single-arc walk from v to x given D.adj v x. -/
private def singleArcWalk {V : Type*} {D : Digraph V} {v x : V}
    (hadj : D.adj v x) : D.Walk v x where
  arcs := [(v, x)]
  arcs_valid a ha := by simp only [List.mem_singleton] at ha; exact ha ▸ hadj
  starts_at _ := by simp
  ends_at _ := by simp
  consecutive := List.chain'_singleton _
  empty_at h := absurd h (List.singleton_ne_nil _)

/-- A nodup list of D-arcs has length ≤ D.arcCount. -/
private theorem nodup_arcs_length_le {V : Type*} [Fintype V] [DecidableEq V]
    {D : Digraph V} [DecidableRel D.adj] {u v : V}
    (w : D.Walk u v) (hnodup : w.arcs.Nodup) :
    w.arcs.length ≤ D.arcCount := by
  unfold Digraph.arcCount
  calc w.arcs.length
      = w.arcs.toFinset.card := (List.toFinset_card_of_nodup hnodup).symm
    _ ≤ (Finset.univ.filter (fun p : V × V => D.adj p.1 p.2)).card := by
        apply Finset.card_le_card
        intro ⟨a, b⟩ hmem
        simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and] at *
        exact w.arcs_valid _ hmem

/-- A nodup circuit whose arc count equals D.arcCount is Eulerian. -/
private theorem isEulerian_of_length_eq {V : Type*} [Fintype V] [DecidableEq V]
    {D : Digraph V} [DecidableRel D.adj] {v₀ : V}
    (C : D.Walk v₀ v₀) (hnodup : C.arcs.Nodup)
    (hlen : D.arcCount ≤ C.arcs.length) :
    C.isEulerian := by
  have hle : C.arcs.length ≤ D.arcCount := nodup_arcs_length_le C hnodup
  have heq : C.arcs.length = D.arcCount := Nat.le_antisymm hle hlen
  refine ⟨hnodup, fun a b hadj => ?_⟩
  -- C.arcs is nodup with length = D.arcCount.
  -- Every D-arc is in C.arcs because C.arcs.toFinset = D's arc set (same cardinality, one ⊆ other).
  have hcard : C.arcs.toFinset.card = (Finset.univ.filter (fun p : V × V => D.adj p.1 p.2)).card := by
    rw [List.toFinset_card_of_nodup hnodup]
    exact heq
  have hsub : C.arcs.toFinset ⊆ Finset.univ.filter (fun p : V × V => D.adj p.1 p.2) := by
    intro ⟨x, y⟩ hmem
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and] at *
    exact C.arcs_valid _ hmem
  have heqset := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)
  have : (a, b) ∈ Finset.univ.filter (fun p : V × V => D.adj p.1 p.2) := by
    simp [hadj]
  rw [← heqset] at this
  exact List.mem_toFinset.mp this

/-- **Key sub-lemma (classical)**: In a balanced digraph, if vertex u has positive
    outDegree, then there exists a nodup circuit from u with at least one arc.

    Proof sketch (classical maximum argument):
    - The set of lengths of nodup walks from u is nonempty (contains 0) and bounded
      by D.arcCount.  Take the maximum m.
    - The corresponding maximum-length nodup walk W : D.Walk u v is "stuck" at v
      (all arcs from v are already in W, else we could extend).
    - By `maximal_balanced_trail_is_circuit`, u = v — so W is a circuit.
    - Since D.outDegree u > 0 and W is stuck at u = v, all arcs from u are in W,
      so W.arcs is nonempty. -/
private theorem nodup_circuit_exists_of_outDeg_pos {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) [DecidableRel D.adj]
    (hbal : ∀ v : V, D.isBalanced v)
    (u : V) (hout : 0 < D.outDegree u) :
    ∃ (C : D.Walk u u), C.arcs.Nodup ∧ C.arcs ≠ [] := by
  -- We prove the stronger claim: for any nodup walk w : D.Walk u v with
  -- D.arcCount = w.arcs.length + m remaining arcs, there exists a nodup circuit from u.
  -- Proof by strong induction on m: either the walk is stuck (apply
  -- maximal_balanced_trail_is_circuit) or extend by one unused arc.
  suffices key : ∀ (m : ℕ) {v : V} (w : D.Walk u v),
      w.arcs.Nodup → D.arcCount = w.arcs.length + m →
      ∃ (C : D.Walk u u), C.arcs.Nodup ∧ C.arcs ≠ [] from
    key D.arcCount (emptyWalk_at u) List.nodup_nil (by simp)
  intro m
  induction m with
  | zero =>
    intro v w hnodup hlen
    -- w covers all D-arcs
    have hlen' : w.arcs.length = D.arcCount := by omega
    have hall : ∀ a b : V, D.adj a b → (a, b) ∈ w.arcs := by
      intro a b hadj
      have hcard : w.arcs.toFinset.card =
          (Finset.univ.filter (fun p : V × V => D.adj p.1 p.2)).card := by
        rw [List.toFinset_card_of_nodup hnodup]
        unfold Digraph.arcCount at hlen'; exact hlen'
      have hsub : w.arcs.toFinset ⊆ Finset.univ.filter (fun p : V × V => D.adj p.1 p.2) := by
        intro ⟨x, y⟩ hmem
        simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and] at *
        exact w.arcs_valid _ hmem
      have heqset := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard)
      have hmem : (a, b) ∈ Finset.univ.filter (fun p : V × V => D.adj p.1 p.2) := by
        simp [hadj]
      rw [← heqset] at hmem
      exact List.mem_toFinset.mp hmem
    have hstuck : ∀ x : V, D.adj v x → (v, x) ∈ w.arcs := fun x hx => hall v x hx
    have hvu : u = v := maximal_balanced_trail_is_circuit w hnodup hstuck hbal
    subst hvu
    refine ⟨w, hnodup, ?_⟩
    intro hemp
    unfold Digraph.outDegree Digraph.outNeighbors at hout
    rw [Finset.card_pos] at hout
    obtain ⟨x, hx⟩ := hout
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact absurd (hall u x hx) (hemp ▸ List.not_mem_nil _)
  | succ m ih =>
    intro v w hnodup hlen
    by_cases hstuck : ∀ x : V, D.adj v x → (v, x) ∈ w.arcs
    · -- Stuck: maximal_balanced_trail_is_circuit gives v = u
      have hvu : u = v := maximal_balanced_trail_is_circuit w hnodup hstuck hbal
      subst hvu
      refine ⟨w, hnodup, ?_⟩
      intro hemp
      unfold Digraph.outDegree Digraph.outNeighbors at hout
      rw [Finset.card_pos] at hout
      obtain ⟨x, hx⟩ := hout
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact absurd (hstuck x hx) (hemp ▸ List.not_mem_nil _)
    · -- Not stuck: extend the walk by one unused arc
      push_neg at hstuck
      obtain ⟨x, hadj_vx, hnotin⟩ := hstuck
      apply ih (w.splice (singleArcWalk hadj_vx))
      · apply Digraph.Walk.splice_nodup _ _ hnodup (List.nodup_singleton _)
        intro a ha ha'
        simp only [List.mem_singleton] at ha'
        exact hnotin (ha' ▸ ha)
      · simp only [Digraph.Walk.splice_arcs, List.length_append, List.length_singleton]
        omega

/-- **Key sub-lemma (strong connectivity)**: If D is balanced and strongly connected,
    and a nodup circuit C does not cover all arcs, then some vertex on C (or v₀
    if C is empty) has a positive outDegree in the residual `removeArcList D C.arcs`.

    Proof sketch:
    - Let D' = removeArcList D C.arcs.  D'.arcCount > 0 (some arcs uncovered).
    - Let V(C) = {v₀} ∪ {vertices appearing in C.arcs}.
    - Suppose for contradiction every v ∈ V(C) has D'.outDegree v = 0.
      Then all D-arcs from V(C) are in C.arcs.  Since C.arcs only touches vertices
      in V(C), no arc leaves V(C) to any w ∉ V(C).
    - If V(C) ≠ V: strong connectivity is violated (no walk from V(C) to w ∉ V(C)).
    - If V(C) = V: every vertex's arcs are all in C.arcs, so D.arcCount = C.arcs.length.
      Contradicts D'.arcCount > 0.
    - Therefore ∃ v ∈ V(C) with D'.outDegree v > 0.
    - But v ∈ V(C) means v = v₀ or v appears in C.arcs as a fst or snd. -/
private theorem vertex_with_unused_arc {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) [DecidableRel D.adj]
    (hbal : ∀ v : V, D.isBalanced v)
    (hconn : isStronglyConnected D)
    {v₀ : V} (C : D.Walk v₀ v₀) (hnodup : C.arcs.Nodup)
    (hextra : C.arcs.length < D.arcCount) :
    ∃ u ∈ ({v₀} : Finset V) ∪ (C.arcs.map Prod.snd).toFinset,
      0 < (removeArcList D C.arcs).outDegree u := by
  -- Abbreviate residual graph
  set D' := removeArcList D C.arcs with hD'_def
  haveI hD'_dec : DecidableRel D'.adj := inferInstance
  -- D'.arcCount > 0
  have hD'arc : D'.arcCount = D.arcCount - C.arcs.length :=
    removeArcList_arcCount D C.arcs (fun a ha => C.arcs_valid a ha) hnodup
  have harcPos : 0 < D'.arcCount := by rw [hD'arc]; omega
  -- V(C): the vertex set of the circuit
  set VC := ({v₀} : Finset V) ∪ (C.arcs.map Prod.snd).toFinset
  -- Proof by contradiction: assume no vertex in V(C) has positive D'-outDeg
  by_contra hall
  push_neg at hall
  have hall' : ∀ u ∈ VC, D'.outDegree u = 0 := fun u hu => by
    have := hall u hu; omega
  -- V(C) is closed under D-adjacency:
  -- if s ∈ V(C) and D.adj s t, then (s,t) ∈ C.arcs (since D'.outDeg s = 0), so t ∈ V(C)
  have hclosed : ∀ s ∈ VC, ∀ t : V, D.adj s t → t ∈ VC := by
    intro s hs t hadj
    have hmust_in : (s, t) ∈ C.arcs := by
      by_contra hnotin
      have hD'adj : D'.adj s t := ⟨hadj, hnotin⟩
      have hmem : t ∈ D'.outNeighbors s := by
        unfold Digraph.outNeighbors
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hD'adj
      have hpos : 0 < D'.outDegree s := Finset.card_pos.mpr ⟨t, hmem⟩
      exact absurd hpos (by have := hall' s hs; omega)
    simp only [VC, Finset.mem_union, Finset.mem_singleton, List.mem_toFinset]
    exact Or.inr (List.mem_map.mpr ⟨(s, t), hmust_in, rfl⟩)
  -- Every vertex is in V(C) via strong connectivity: any walk from v₀ stays in V(C)
  have hreach : ∀ z : V, z ∈ VC := by
    intro z
    obtain ⟨w⟩ := hconn v₀ z
    by_cases hempty : w.arcs = []
    · rw [← w.empty_at hempty]; simp [VC]
    · -- Prove by list induction: all arc snds of a walk from V(C) are in V(C)
      have hstays : ∀ a ∈ w.arcs, a.2 ∈ VC := by
        suffices h_list : ∀ (L : List (V × V)),
            L.Chain' (fun a b => a.2 = b.1) →
            (∀ a ∈ L, D.adj a.1 a.2) →
            ∀ (start : V),
            (L = [] ∨ ∀ hne : L ≠ [], (L.head hne).1 = start) →
            start ∈ VC →
            ∀ a ∈ L, a.2 ∈ VC by
          exact h_list w.arcs w.consecutive w.arcs_valid v₀
            (Or.inr w.starts_at) (by simp [VC])
        intro L
        induction L with
        | nil => intros; exact absurd ‹_ ∈ []› (List.not_mem_nil _)
        | cons h2 t ih_t =>
          intro hchain hvalid start hhead hstart_vc a ha
          have hne : h2 :: t ≠ [] := List.cons_ne_nil _ _
          have hh1 : h2.1 = start := by
            rcases hhead with hempty' | hfn
            · exact absurd hempty' hne
            · have := hfn hne; simp [List.head_cons] at this; exact this
          have hadj' : D.adj h2.1 h2.2 := hvalid h2 (List.mem_cons_self _ _)
          have hh2_vc : h2.2 ∈ VC := hclosed h2.1 h2.2 (hh1 ▸ hstart_vc) hadj'
          rcases List.mem_cons.mp ha with rfl | ha_t
          · exact hh2_vc
          · apply ih_t (hchain.tail)
              (fun b hb => hvalid b (List.mem_cons_of_mem _ hb))
              h2.2
              (by
                by_cases ht : t = []
                · exact Or.inl ht
                · refine Or.inr (fun hnet => ?_)
                  cases t with
                  | nil => exact absurd rfl ht
                  | cons h3 rest =>
                    simp only [List.head_cons]
                    exact (List.Chain'.rel_head hchain).symm)
              hh2_vc a ha_t
      rw [← w.ends_at hempty]
      exact hstays _ (List.getLast_mem hempty)
  -- All D'-outDegrees are 0 (every vertex is in V(C))
  have hall_zero : ∀ v : V, D'.outDegree v = 0 := fun v => hall' v (hreach v)
  have hsum : ∑ v : V, D'.outDegree v = 0 :=
    Finset.sum_eq_zero (fun v _ => hall_zero v)
  have hsum_eq := D'.sum_outDegree_eq_arcCount
  rw [hsum] at hsum_eq
  -- D'.arcCount = 0 contradicts harcPos
  omega

/-- **Walk splitting**: Given a nodup circuit C : D.Walk v₀ v₀ and a vertex u that
    appears as the second component (arrival) of some arc in C.arcs, we can split C into
    C1 : D.Walk v₀ u and C2 : D.Walk u v₀ such that:
    - C.arcs = C1.arcs ++ C2.arcs
    - C1.arcs and C2.arcs are both nodup
    - C1.arcs and C2.arcs are disjoint (as sublists of the nodup C.arcs)

    Special case: u = v₀ (not necessarily in C.arcs.map Prod.snd) — split as C1 = C, C2 = empty.

    Proof: find the first index i where C.arcs[i].snd = u.  Take C1 = take(i+1), C2 = drop(i+1).
    All Walk invariants hold: consecutive splits cleanly, starts/ends_at from arcs structure. -/
private theorem walk_split_at {V : Type*} (D : Digraph V) {v₀ u : V}
    (C : D.Walk v₀ v₀) (hnodup : C.arcs.Nodup)
    (hu : u = v₀ ∨ u ∈ C.arcs.map Prod.snd) :
    ∃ (C1 : D.Walk v₀ u) (C2 : D.Walk u v₀),
      C.arcs = C1.arcs ++ C2.arcs ∧
      C1.arcs.Nodup ∧ C2.arcs.Nodup ∧
      ∀ a ∈ C1.arcs, a ∉ C2.arcs := by
  rcases hu with rfl | hu
  · -- Case u = v₀: C1 = C, C2 = empty
    exact ⟨C, emptyWalk_at v₀, by simp, hnodup, List.nodup_nil,
           fun _ _ h => absurd h (List.not_mem_nil _)⟩
  · -- Case u ∈ C.arcs.map Prod.snd
    rw [List.mem_map] at hu
    obtain ⟨⟨a, _⟩, hmem, rfl⟩ := hu
    -- Extract index: C.arcs[i] = (a, u) for some i < C.arcs.length
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hi_lt, hi_eq⟩ := hmem
    -- Auxiliary: C.arcs is nonempty
    have hCne : C.arcs ≠ [] := List.ne_nil_of_length_pos (by omega)
    -- Build C1 from C.arcs.take(i+1) and C2 from C.arcs.drop(i+1)
    refine ⟨
      { arcs := C.arcs.take (i + 1)
        arcs_valid := fun arc harc =>
          C.arcs_valid arc ((List.take_sublist (i + 1) C.arcs).subset harc)
        starts_at := fun h1ne => by
          rw [List.head_take h1ne]
          exact C.starts_at hCne
        ends_at := fun h1ne => by
          -- (C.arcs.take(i+1)).getLast = C.arcs[i]
          have key : (C.arcs.take (i + 1)).getLast h1ne = C.arcs[i]'hi_lt := by
            rw [List.getLast_take h1ne]
            have h_idx : i + 1 - 1 = i := by omega
            rw [h_idx, getElem?_pos hi_lt]
            simp
          rw [key]
          exact congrArg Prod.snd hi_eq
        consecutive := C.consecutive.take (i + 1)
        empty_at := fun h => by
          rw [List.take_eq_nil_iff] at h
          rcases h with (h | h)
          · exact absurd h (Nat.succ_ne_zero i)
          · exact absurd h hCne
      },
      { arcs := C.arcs.drop (i + 1)
        arcs_valid := fun arc harc =>
          C.arcs_valid arc ((List.drop_sublist (i + 1) C.arcs).subset harc)
        starts_at := fun h2ne => by
          -- head of drop(i+1) = C.arcs[i+1], whose fst = C.arcs[i].snd = u
          have hi1_lt : i + 1 < C.arcs.length := by
            simp only [ne_eq, List.drop_eq_nil_iff, not_le] at h2ne; exact h2ne
          simp only [List.head_drop h2ne]
          -- consecutive gives: C.arcs[i].2 = C.arcs[i+1].1; hi_eq gives C.arcs[i] = (a,u)
          have hchain : (C.arcs[i]'hi_lt).2 = (C.arcs[i + 1]'hi1_lt).1 :=
            C.consecutive.getElem i (by omega)
          have hieq : (C.arcs[i]'hi_lt).2 = u := congrArg Prod.snd hi_eq
          exact hchain.symm.trans hieq
        ends_at := fun h2ne => by
          rw [List.getLast_drop h2ne]
          exact C.ends_at hCne
        consecutive := C.consecutive.drop (i + 1)
        empty_at := fun hempty => by
          -- drop(i+1) = [] means C.arcs.length ≤ i+1; since i < C.arcs.length, length = i+1
          have hlen : C.arcs.length = i + 1 := by
            rw [List.drop_eq_nil_iff] at hempty; omega
          -- C.arcs.getLast = C.arcs[i] (last element)
          have hlast_eq : C.arcs.getLast hCne = C.arcs[i]'hi_lt := by
            have hidx : C.arcs.length - 1 = i := by omega
            rw [List.getLast_eq_getElem, hidx]
          -- C.arcs.getLast.snd = v₀ (from C.ends_at)
          have hv₀ : (C.arcs.getLast hCne).2 = v₀ := C.ends_at hCne
          -- C.arcs[i].snd = u (from hi_eq)
          have hu' : (C.arcs[i]'hi_lt).2 = u := congrArg Prod.snd hi_eq
          -- Combine: u = v₀
          rw [hlast_eq] at hv₀
          exact hu'.symm.trans hv₀
      },
      -- C.arcs = C1.arcs ++ C2.arcs
      (List.take_append_drop (i + 1) C.arcs).symm,
      -- C1.arcs.Nodup
      hnodup.take,
      -- C2.arcs.Nodup
      hnodup.drop,
      -- Disjoint
      fun arc harc1 harc2 =>
        List.disjoint_take_drop hnodup (Nat.le_refl _) harc1 harc2
    ⟩

-- ============================================================
-- PART VIII: Corrected Main Theorem
-- ============================================================

/-- **Corrected Directed Eulerian Circuit Sufficiency** (Hierholzer, 1873).

    The axiom `directed_euler_circuit_sufficient` in KonigsbergOQ02.lean
    (line 409) is INCORRECTLY STATED — it is missing `isStronglyConnected`.

    The corrected theorem: if D is strongly connected and every vertex is
    balanced (indeg = outdeg), then D has an Eulerian circuit.

    **Proof** (Hierholzer extension argument):
    We prove the stronger statement by induction on m = D.arcCount - C.arcs.length:
    given any nodup circuit C in D, there exists an Eulerian circuit starting at C's base.

    - Base (m = 0): C is Eulerian (isEulerian_of_length_eq).
    - Step: Some vertex u ∈ V(C) has unused arcs in D' = removeArcList D C.arcs
      (vertex_with_unused_arc, using strong connectivity + balance).
      Build nodup circuit C' at u in D' (nodup_circuit_exists_of_outDeg_pos + balance of D').
      Split C = C1.splice C2 at u (walk_split_at).
      New circuit: C1.splice(C'.ofRemoveArcList.splice C2) has length |C| + |C'| > |C|.
      It is nodup (C1, C', C2 are pairwise arc-disjoint).
      Apply IH with the longer circuit. -/
theorem directed_euler_circuit_sufficient_corrected {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V]
    (D : Digraph V) [DecidableRel D.adj]
    (hbal : ∀ v : V, D.isBalanced v)
    (hconn : isStronglyConnected D) :
    ∃ (v₀ : V) (w : D.Walk v₀ v₀), w.isEulerian := by
  -- We prove the stronger statement with a given circuit C by induction on remaining arcs.
  suffices extend : ∀ (m : ℕ) {v₀ : V} (C : D.Walk v₀ v₀), C.arcs.Nodup →
      D.arcCount ≤ C.arcs.length + m → ∃ (w : D.Walk v₀ v₀), w.isEulerian by
    obtain ⟨v₀⟩ := ‹Nonempty V›
    exact extend D.arcCount (emptyWalk_at v₀) List.nodup_nil (by simp)
  intro m
  induction m with
  | zero =>
    intro v₀ C hnodup hle
    exact ⟨C, isEulerian_of_length_eq C hnodup hle⟩
  | succ m ih =>
    intro v₀ C hnodup hle
    -- Either C is already Eulerian, or there are uncovered arcs.
    by_cases hcover : D.arcCount ≤ C.arcs.length
    · exact ⟨C, isEulerian_of_length_eq C hnodup hcover⟩
    · push_neg at hcover
      -- Some vertex u on C (or v₀) has unused arcs in the residual D'.
      let D' := removeArcList D C.arcs
      haveI : DecidableRel D'.adj := inferInstance
      obtain ⟨u, hu_on_C, hu_pos⟩ := vertex_with_unused_arc D hbal hconn C hnodup hcover
      -- D' is balanced (removing a circuit preserves balance).
      have hbal' : ∀ v, D'.isBalanced v := by
        apply removeArcList_balanced D C.arcs C.consecutive hnodup
        · by_cases hempty : C.arcs = []
          · exact Or.inl hempty
          · exact Or.inr ⟨hempty, by rw [C.starts_at hempty, C.ends_at hempty]⟩
        · exact fun a ha => C.arcs_valid a ha
        · exact hbal
      -- Build nodup circuit C' at u in D' (lifted to D via ofRemoveArcList).
      obtain ⟨C'_res, hC'_nodup, hC'_ne⟩ :=
        nodup_circuit_exists_of_outDeg_pos D' hbal' u hu_pos
      -- Lift C'_res from D' to D
      have C' : D.Walk u u := C'_res.ofRemoveArcList
      have hC'_arcs : C'.arcs = C'_res.arcs := rfl
      -- C' arcs are all from D' (unused by C) hence disjoint from C.arcs.
      have hC'_disj : ∀ a ∈ C'.arcs, a ∉ C.arcs := fun ⟨p, q⟩ ha hac =>
        (C'_res.arcs_valid (p, q) ha).2 hac
      -- C' is nonempty (re-stated at D level)
      have hC'_ne_lift : C'.arcs ≠ [] := hC'_arcs ▸ hC'_ne
      have hC'_nodup_lift : C'.arcs.Nodup := hC'_arcs ▸ hC'_nodup
      -- Split C at u: C = C1.splice C2.
      have hu_split : u = v₀ ∨ u ∈ C.arcs.map Prod.snd := by
        simp only [Finset.mem_union, Finset.mem_singleton, List.mem_toFinset] at hu_on_C
        exact hu_on_C
      obtain ⟨C1, C2, hC_split, hC1_nodup, hC2_nodup, hC1_C2_disj⟩ :=
        walk_split_at D C hnodup hu_split
      -- Build the extended circuit: C1.splice(C'.splice C2).
      have C'' : D.Walk v₀ v₀ := C1.splice (C'.splice C2)
      -- C'' arcs decompose (unfold the splice definition).
      -- C'' = C1.splice(C'.splice C2), so arcs = C1.arcs ++ (C'.arcs ++ C2.arcs).
      have hC''_arcs : C''.arcs = C1.arcs ++ (C'.arcs ++ C2.arcs) := by
        simp only [C'', Digraph.Walk.splice_arcs]
      -- C'' is nodup: C1, C', C2 are pairwise arc-disjoint.
      have hC''_nodup : C''.arcs.Nodup := by
        rw [hC''_arcs, List.nodup_append]
        refine ⟨hC1_nodup, List.nodup_append.mpr ⟨hC'_nodup_lift, hC2_nodup, ?_⟩, ?_⟩
        · -- C' and C2 disjoint: C' ⊆ D', C2 ⊆ C.arcs
          intro a haC' haC2
          exact hC'_disj a haC' (hC_split ▸ List.mem_append_right _ haC2)
        · -- C1 and (C' ++ C2) disjoint
          intro a haC1 ha
          rw [List.mem_append] at ha
          rcases ha with haC' | haC2
          · exact hC'_disj a haC' (hC_split ▸ List.mem_append_left _ haC1)
          · exact hC1_C2_disj a haC1 haC2
      -- C'' has strictly more arcs than C.
      have hC_len : C.arcs.length = C1.arcs.length + C2.arcs.length := by
        have := congr_arg List.length hC_split; simp [List.length_append] at this; exact this
      have hC'_pos : 0 < C'.arcs.length := List.length_pos.mpr hC'_ne_lift
      have hC''_len : C''.arcs.length = C1.arcs.length + C'.arcs.length + C2.arcs.length := by
        simp [hC''_arcs, List.length_append]
      have hC''_longer : C.arcs.length < C''.arcs.length := by omega
      -- Apply IH: D.arcCount ≤ C''.arcs.length + m.
      apply ih C'' hC''_nodup
      omega

-- ============================================================
-- Summary
-- ============================================================

/-
### Results

**Proved (0 sorries)**:
- `maximal_balanced_trail_is_circuit`: In a balanced digraph, any maximal Nodup
  trail is a closed circuit. (Key sub-lemma of Hierholzer.)
- `Walk.splice`: Concatenate two walks sharing a vertex.
- `Walk.splice_nodup`: Splice of arc-disjoint Nodup walks is Nodup.
- `removeArcList_arcCount`: arcCount of residual = D.arcCount - removed.
- `removeArcList_balanced`: removing a circuit preserves balance.
- `nodup_arcs_length_le`: nodup walk arcs bounded by arcCount.
- `isEulerian_of_length_eq`: nodup circuit of length = arcCount is Eulerian.
- `directed_euler_circuit_sufficient_corrected`: main theorem (modulo 3 sorry'd sub-lemmas).

**Sorry'd sub-lemmas** (3 focused lemmas with proof sketches):
- `nodup_circuit_exists_of_outDeg_pos`: classical max-length walk argument
  → gives nodup circuit from any vertex with positive outDeg in balanced D.
- `vertex_with_unused_arc`: strong connectivity + balance gives vertex on C with unused arcs.
- `walk_split_at`: list split of a Walk at a vertex in C.arcs.map Prod.snd.

**Bug Found**:
- `directed_euler_circuit_sufficient` (KonigsbergOQ02.lean line 409) is an axiom
  with a MISSING hypothesis. The corrected version requires strong connectivity.
-/

#check @isStronglyConnected
#check @maximal_balanced_trail_is_circuit
#check @Digraph.Walk.splice
#check @directed_euler_circuit_sufficient_corrected

end KonigsbergOQ02OQ01
