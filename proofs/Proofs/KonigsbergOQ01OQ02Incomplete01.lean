/-
  Königsberg OQ-01 OQ-02 (incomplete-01): Circuit Removal Preserves Balance

  This file completes — and corrects — the one remaining `sorry` in the parent
  formalization `KonigsbergOQ01OQ02.lean` (Eulerian paths in directed graphs).

  ## The gap in the parent file

  The parent develops Hierholzer's infrastructure for directed graphs. Step 5 of
  that development states (with a `sorry`):

      theorem remove_circuit_balanced (G : DiGraph V) (C : DirectedCircuit G) :
          IsEulerianBalanced (G.removeEdgeSet (walkEdges C.walk).toFinset)

  i.e. "removing the edges of a circuit from a directed graph yields a balanced
  graph". **This statement is false as written.** It has no hypothesis that `G`
  itself is balanced. A directed circuit `C` is itself balanced (it enters and
  leaves every vertex the same number of times), so deleting its edges changes
  in-degree and out-degree by the *same* amount at every vertex. Therefore the
  result graph `G \ C` is balanced **iff `G` was already balanced**. Removing a
  circuit cannot manufacture balance out of an unbalanced graph.

  ## What this file proves (all from first principles, 0 axioms, 0 sorries)

  1. `outDeg_sdiff` / `inDeg_sdiff` — deleting a sub-edge-set `S ⊆ E` decreases
     out/in-degree by exactly the out/in-degree of `S` (the Finset.sdiff
     distributivity step the parent's comment flagged as the blocker).

  2. `remove_circuitBalanced_preserves` — the **corrected** theorem: if every
     vertex of `E` is balanced and `S ⊆ E` is *circuit-balanced*
     (`outDeg S v = inDeg S v` for all `v`), then `E \ S` is balanced.
     This is exactly the lemma Hierholzer's sufficiency proof needs, stated with
     the hypothesis the parent omitted.

  3. `triangle_circuitBalanced` — a genuine directed circuit (the 3-cycle
     0→1→2→0) is circuit-balanced, witnessing that the abstract hypothesis is
     satisfied by real circuits (verified by `decide`).

  4. `parent_statement_false` — a concrete counterexample (over `Fin 4`)
     refuting the parent's *unconditional* statement: an unbalanced graph `G`
     containing a circuit `C` whose removal leaves an unbalanced graph. This
     proves the missing balance hypothesis is genuinely necessary.

  The file is deliberately standalone (it does not import the parent, which the
  parent's own metadata records as not building under current Mathlib). It uses
  only `Finset` reasoning and `decide`, so it is fully kernel-checked with no
  `axiom` declarations, no `sorry`, and no `native_decide`.

  References:
  - Hierholzer (1873): constructive proof of Eulerian circuit existence.
  - West (2001): Introduction to Graph Theory, §1.3.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace KonigsbergOQ01OQ02Incomplete01

open Finset

variable {V : Type*} [DecidableEq V]

/-
══════════════════════════════════════════════════════════════
PART I: DEGREES AS FILTERED EDGE-SET CARDINALITIES
══════════════════════════════════════════════════════════════ -/

/-- Out-degree of `v` in an edge set: number of edges with source `v`. -/
def outDeg (E : Finset (V × V)) (v : V) : ℕ :=
  (E.filter (fun e => e.1 = v)).card

/-- In-degree of `v` in an edge set: number of edges with target `v`. -/
def inDeg (E : Finset (V × V)) (v : V) : ℕ :=
  (E.filter (fun e => e.2 = v)).card

/-- A vertex is balanced in `E` if its in-degree equals its out-degree. -/
def Balanced (E : Finset (V × V)) (v : V) : Prop :=
  inDeg E v = outDeg E v

/-- An edge set is circuit-balanced if every vertex has equal in- and
    out-degree *within that set*. This is the abstract property shared by every
    directed circuit (and, more generally, every edge-disjoint union of
    circuits): it enters and leaves each vertex the same number of times. -/
def CircuitBalanced (S : Finset (V × V)) : Prop :=
  ∀ v, outDeg S v = inDeg S v

/-
══════════════════════════════════════════════════════════════
PART II: THE Finset.sdiff DISTRIBUTIVITY STEP
══════════════════════════════════════════════════════════════

  The parent file's comment recorded that `remove_circuit_balanced` was
  "blocked on a Finset.sdiff distributivity step". These two lemmas are exactly
  that step: filtering commutes with set difference, and for a sub-edge-set the
  resulting cardinality subtracts cleanly.
══════════════════════════════════════════════════════════════ -/

/-- Filtering distributes over set difference. -/
theorem filter_sdiff (E S : Finset (V × V)) (p : V × V → Prop) [DecidablePred p] :
    (E \ S).filter p = E.filter p \ S.filter p := by
  ext x
  simp only [mem_filter, mem_sdiff]
  tauto

/-- **Out-degree after deleting a sub-edge-set.** If `S ⊆ E` then removing `S`
    drops the out-degree of every vertex by exactly its out-degree in `S`. -/
theorem outDeg_sdiff (E S : Finset (V × V)) (hS : S ⊆ E) (v : V) :
    outDeg (E \ S) v = outDeg E v - outDeg S v := by
  unfold outDeg
  rw [filter_sdiff, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hS)]

/-- **In-degree after deleting a sub-edge-set.** Symmetric to `outDeg_sdiff`. -/
theorem inDeg_sdiff (E S : Finset (V × V)) (hS : S ⊆ E) (v : V) :
    inDeg (E \ S) v = inDeg E v - inDeg S v := by
  unfold inDeg
  rw [filter_sdiff, Finset.card_sdiff_of_subset (Finset.filter_subset_filter _ hS)]

/-
══════════════════════════════════════════════════════════════
PART III: THE CORRECTED CIRCUIT-REMOVAL THEOREM
══════════════════════════════════════════════════════════════ -/

/-- **Circuit removal preserves balance (corrected).**
    If every vertex of `E` is balanced and `S ⊆ E` is circuit-balanced, then
    every vertex of `E \ S` is balanced.

    This is the lemma Hierholzer's sufficiency argument requires. Compared with
    the parent file's `remove_circuit_balanced`, it adds the indispensable
    hypothesis `hEbal : ∀ v, Balanced E v` — see `parent_statement_false` below
    for why omitting it makes the claim false.

    Proof: by `outDeg_sdiff` / `inDeg_sdiff`, deleting `S` subtracts `outDeg S v`
    from the out-degree and `inDeg S v` from the in-degree. Circuit-balance of
    `S` makes those two equal, and balance of `E` makes the base degrees equal,
    so the differences agree. -/
theorem remove_circuitBalanced_preserves
    (E S : Finset (V × V)) (hS : S ⊆ E)
    (hSbal : CircuitBalanced S) (hEbal : ∀ v, Balanced E v) :
    ∀ v, Balanced (E \ S) v := by
  intro v
  unfold Balanced
  rw [outDeg_sdiff E S hS v, inDeg_sdiff E S hS v]
  have hE := hEbal v          -- inDeg E v = outDeg E v
  have hS' := hSbal v         -- outDeg S v = inDeg S v
  unfold Balanced at hE
  omega

/-- Convenience restatement: circuit-removal sends the global balance predicate
    `(∀ v, Balanced E v)` to `(∀ v, Balanced (E \ S) v)`. -/
theorem remove_circuit_balanced_correct
    (E S : Finset (V × V)) (hS : S ⊆ E)
    (hSbal : CircuitBalanced S) (hEbal : ∀ v, Balanced E v) :
    ∀ v, Balanced (E \ S) v :=
  remove_circuitBalanced_preserves E S hS hSbal hEbal

/-
══════════════════════════════════════════════════════════════
PART IV: A GENUINE CIRCUIT IS CIRCUIT-BALANCED
══════════════════════════════════════════════════════════════ -/

/-- The directed 3-cycle `0 → 1 → 2 → 0` as an edge set on `Fin 3`. -/
def triangle : Finset (Fin 3 × Fin 3) := {(0, 1), (1, 2), (2, 0)}

/-- The directed triangle is circuit-balanced: each vertex has in-degree =
    out-degree = 1 within the cycle. Witnesses that `CircuitBalanced` is a
    property real circuits satisfy. -/
theorem triangle_circuitBalanced : CircuitBalanced triangle := by
  intro v
  fin_cases v <;> decide

/-- Removing the whole circuit from itself leaves the empty (balanced) graph —
    the base case of Hierholzer's recursion. -/
theorem triangle_remove_self_balanced :
    ∀ v, Balanced (triangle \ triangle) v :=
  remove_circuitBalanced_preserves triangle triangle (Finset.Subset.refl _)
    triangle_circuitBalanced (by intro v; unfold Balanced; fin_cases v <;> decide)

/-
══════════════════════════════════════════════════════════════
PART V: REFUTATION OF THE PARENT'S UNCONDITIONAL STATEMENT
══════════════════════════════════════════════════════════════

  The parent's `remove_circuit_balanced` claims `G \ C` is balanced with no
  assumption on `G`. We exhibit an unbalanced `G` over `Fin 4` containing the
  directed triangle as a circuit `C`, such that `G \ C` is still unbalanced —
  refuting the unconditional claim and confirming that the balance hypothesis
  added in Part III is necessary.
══════════════════════════════════════════════════════════════ -/

/-- An unbalanced graph: the triangle `0→1→2→0` plus a pendant edge `0→3`.
    Vertex `0` has out-degree 2, in-degree 1; vertex `3` has in-degree 1,
    out-degree 0 — so `G` is unbalanced. -/
def unbalancedG : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 2), (2, 0), (0, 3)}

/-- The directed triangle, viewed inside `Fin 4`, is a circuit sitting in
    `unbalancedG`. -/
def triangle4 : Finset (Fin 4 × Fin 4) := {(0, 1), (1, 2), (2, 0)}

/-- `triangle4` is genuinely a sub-edge-set (circuit) of `unbalancedG`. -/
theorem triangle4_subset : triangle4 ⊆ unbalancedG := by decide

/-- `triangle4` is circuit-balanced (it is a directed cycle). -/
theorem triangle4_circuitBalanced : CircuitBalanced triangle4 := by
  intro v; fin_cases v <;> decide

/-- `unbalancedG` is **not** balanced (vertex `0` witnesses the imbalance:
    out-degree 2, in-degree 1). -/
theorem unbalancedG_not_balanced : ¬ (∀ v, Balanced unbalancedG v) := by
  intro h
  have h0 := h 0
  unfold Balanced inDeg outDeg at h0
  revert h0
  decide

/-- **Refutation.** Even though `triangle4 ⊆ unbalancedG` is a circuit
    (`triangle4_circuitBalanced`), the graph `unbalancedG \ triangle4` is still
    unbalanced. Hence the parent file's `remove_circuit_balanced`, which asserts
    balance of `G \ C` with no hypothesis on `G`, is false. The pendant edge
    `0→3` survives the deletion and keeps vertices `0` and `3` unbalanced. -/
theorem parent_statement_false :
    ¬ (∀ v, Balanced (unbalancedG \ triangle4) v) := by
  intro h
  have h3 := h 3
  unfold Balanced inDeg outDeg at h3
  revert h3
  decide

/-- Packaged statement of the refutation: there exist an edge set `E` and a
    circuit-balanced subset `S ⊆ E` (a genuine circuit) with `E \ S` unbalanced.
    Any theorem deriving balance of `E \ S` from `S` alone (no balance
    hypothesis on `E`) is therefore unprovable. -/
theorem circuit_removal_needs_base_balance :
    ∃ (E S : Finset (Fin 4 × Fin 4)),
      S ⊆ E ∧ CircuitBalanced S ∧ ¬ (∀ v, Balanced (E \ S) v) :=
  ⟨unbalancedG, triangle4, triangle4_subset, triangle4_circuitBalanced,
    parent_statement_false⟩

end KonigsbergOQ01OQ02Incomplete01
