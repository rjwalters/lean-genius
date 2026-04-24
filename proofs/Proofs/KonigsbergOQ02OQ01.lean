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
  3. `directed_euler_circuit_sufficient_corrected`: corrected statement with
     `hconn : D.isStronglyConnected`; Hierholzer induction is sorry'd.

  The key sub-lemma is the mathematical heart of Hierholzer's algorithm.
  It uses `path_fst_snd_eq` (reproved here since it is `private` in OQ02)
  together with a counting argument exploiting balance.

  Parent: KonigsbergOQ02.lean (Digraph, Walk, isEulerian, degree definitions)
-/

set_option linter.unusedVariables false

namespace KonigsbergOQ02OQ01

open KonigsbergOQ02

-- ============================================================
-- PART I: Auxiliary List Lemmas
-- ============================================================

-- These are reproved here because `path_fst_snd_eq` is `private` in OQ02.

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

/-- For a chain walk, `[start] ++ map snd = map fst ++ [end]`.

    This is the path analogue of `circuit_fst_perm_snd`: for a circuit the
    source and target multisets are equal; for a path they differ by exactly
    the start and end vertices. -/
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

-- ============================================================
-- PART II: Strong Connectivity
-- ============================================================

/-- A digraph is **strongly connected** if every vertex is reachable from every
    other vertex via a directed walk.

    This is the hypothesis missing from `directed_euler_circuit_sufficient`
    in KonigsbergOQ02.lean. Without it, a disjoint union of two balanced
    digraphs satisfies `hbal` but has no Eulerian circuit spanning both
    components. -/
def Digraph.isStronglyConnected {V : Type*} [Fintype V] [DecidableEq V]
    (D : Digraph V) : Prop :=
  ∀ u v : V, Nonempty (D.Walk u v)

-- ============================================================
-- PART III: Helper Counting Lemmas
-- ============================================================

/-- If every out-arc from `v` appears in the trail (the "stuck" condition),
    and the trail is Nodup, then the count of arcs with source `v` equals
    `outDegree v`.

    This is used in the proof of `maximal_balanced_trail_is_circuit` to
    show that the fst-count at the stuck endpoint saturates the out-degree. -/
private theorem fst_count_eq_outDegree_stuck {V : Type*} [Fintype V] [DecidableEq V]
    {D : Digraph V} [DecidableRel D.adj] {u v₀ : V}
    (w : D.Walk u v₀) (hnodup : w.arcs.Nodup) (v : V)
    (hstuck : ∀ x : V, D.adj v x → (v, x) ∈ w.arcs) :
    (w.arcs.filter (fun a => decide (a.1 = v))).length = D.outDegree v := by
  unfold Digraph.outDegree Digraph.outNeighbors
  -- Convert filtered list length to filtered finset card via Nodup
  rw [show (w.arcs.filter (fun a => decide (a.1 = v))).length =
      (w.arcs.toFinset.filter (fun a : V × V => a.1 = v)).card from by
    rw [← List.toFinset_card_of_nodup (hnodup.filter _)]
    congr 1; ext ⟨a, b⟩
    simp [List.mem_toFinset, Finset.mem_filter, List.mem_filter, decide_eq_true_eq]]
  -- The filtered subfinset equals the image of outNeighbors under (v, ·)
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

/-- For a Nodup trail, the count of arcs with target `v` is at most `inDegree v`.

    Proof: The filtered arcs are Nodup, so they inject into the in-arc set via
    the first component. Each first component satisfies `D.adj a v` by validity. -/
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
    forces the trail to be closed, i.e., `u = v₀`.

    **Proof**:
    By `path_fst_snd_eq`:  `[u] ++ arcs.map snd = arcs.map fst ++ [v₀]`.
    Count `v₀` on both sides:
    - `fst_count = outDeg(v₀)` (by `hstuck` + Nodup: every out-arc of `v₀` is present)
    - `snd_count ≤ inDeg(v₀)` (by Nodup + validity: at most one arc per in-neighbor)
    - `inDeg(v₀) = outDeg(v₀)` (by balance)
    So `count(v₀, [u]) = outDeg + 1 - snd_count ≥ 1`, hence `u = v₀`. -/
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
  · -- path_fst_snd_eq: [u] ++ map snd = map fst ++ [v₀]
    have heq := path_fst_snd_eq w.arcs w.consecutive hempty
    rw [w.starts_at hempty, w.ends_at hempty] at heq
    -- Bridge: (map f l).count b = (l.filter (fun a => decide (f a = b))).length
    have cmf : ∀ (f : (V × V) → V) (l : List (V × V)) (b : V),
        (l.map f).count b = (l.filter (fun a => decide (f a = b))).length := by
      intro f l b; induction l with
      | nil => simp
      | cons h t ih =>
        simp only [List.map_cons, List.count_cons, List.filter_cons]
        split <;> simp_all [List.count]
    -- Extract count equation from the list equality
    have h := congr_arg (List.count v₀) heq
    simp only [List.count_append] at h
    rw [cmf Prod.snd, cmf Prod.fst] at h
    -- fst_count = outDegree v₀ (all out-arcs are in the trail by hstuck)
    rw [fst_count_eq_outDegree_stuck w hnodup v₀ hstuck] at h
    -- count v₀ [v₀] = 1
    have h1 : List.count v₀ [v₀] = 1 := by simp
    rw [h1] at h
    -- h : count v₀ [u] + snd_filter_len = outDeg v₀ + 1
    -- snd_filter_len ≤ inDeg v₀ = outDeg v₀
    have hsnd := snd_count_le_inDegree w hnodup v₀
    have hbal_eq : D.inDegree v₀ = D.outDegree v₀ := hbal v₀
    -- If u ≠ v₀, then count v₀ [u] = 0 → 0 + snd_len = outDeg + 1
    -- but snd_len ≤ inDeg = outDeg, contradiction
    by_contra hne
    have hcount0 : List.count v₀ [u] = 0 := by
      simp only [List.count_cons, List.count_nil]
      simp [show ¬(v₀ = u) from fun h => hne h.symm]
    rw [hcount0] at h
    omega

-- ============================================================
-- PART V: Corrected Main Theorem
-- ============================================================

/-- **Corrected Directed Eulerian Circuit Sufficiency** (Hierholzer, 1873).

    The axiom `directed_euler_circuit_sufficient` in KonigsbergOQ02.lean
    (line 409) is INCORRECTLY STATED — it is missing `isStronglyConnected`.

    The corrected theorem: if D is strongly connected and every vertex is
    balanced (indeg = outdeg), then D has an Eulerian circuit.

    **Proof strategy** (Hierholzer's algorithm):
    1. Pick any v₀. Greedily extend a Nodup trail until stuck at some vertex w.
    2. By `maximal_balanced_trail_is_circuit`, w = v₀, so the trail is a circuit C.
    3. If C covers all arcs, we are done.
    4. If not: strong connectivity gives a vertex on C with unused out-arcs.
    5. From that vertex, build a new circuit C' in the remaining balanced subgraph.
    6. Splice C' into C at the shared vertex (Walk concatenation).
    7. Well-founded induction on `D.arcCount - circuit.arcs.length` terminates.

    The Hierholzer induction is sorry'd. The key sub-lemma (Step 2) is proved
    above as `maximal_balanced_trail_is_circuit`. -/
theorem directed_euler_circuit_sufficient_corrected {V : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V]
    (D : Digraph V) [DecidableRel D.adj]
    (hbal : ∀ v : V, D.isBalanced v)
    (hconn : D.isStronglyConnected) :
    ∃ (v₀ : V) (w : D.Walk v₀ v₀), w.isEulerian := by
  -- Hierholzer induction pending:
  -- Requires: Walk.splice constructor (concatenate two circuits at a shared vertex)
  -- Measure: (Finset.univ.filter (fun p : V × V => D.adj p.1 p.2)).card minus covered arcs
  -- Each splice strictly reduces the uncovered arc count.
  -- Key sub-lemma already proved: maximal_balanced_trail_is_circuit
  sorry

-- ============================================================
-- Summary
-- ============================================================

/-
### Results

**Proved (0 sorries)**:
- `maximal_balanced_trail_is_circuit`: In a balanced digraph, any maximal Nodup
  trail is a closed circuit. This is the mathematical heart of Hierholzer's
  algorithm: greedy trail extension is guaranteed to produce a circuit.

**Helper Lemmas (proved)**:
- `fst_count_eq_outDegree_stuck`: count of arcs with source v = outDegree v
  (when the "stuck" condition holds)
- `snd_count_le_inDegree`: count of arcs with target v ≤ inDegree v
  (for any Nodup trail)

**Definition**:
- `Digraph.isStronglyConnected`: ∀ u v, Nonempty (D.Walk u v)

**Corrected Theorem (1 sorry — Hierholzer induction)**:
- `directed_euler_circuit_sufficient_corrected`: adds `hconn : isStronglyConnected`

**Bug Found**:
- `directed_euler_circuit_sufficient` (KonigsbergOQ02.lean line 409) is an axiom
  with a MISSING hypothesis. The corrected version requires strong connectivity.
  Without it, two disjoint balanced directed graphs form a counterexample.
-/

#check @Digraph.isStronglyConnected
#check @maximal_balanced_trail_is_circuit
#check @directed_euler_circuit_sufficient_corrected

end KonigsbergOQ02OQ01
