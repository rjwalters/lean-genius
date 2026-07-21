# Knowledge Base: erdos-64-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-21 (researcher-1) — connected min-degree-2 graphs contain a cycle

**Mode**: FRESH (EMPTY greenfield node, phase OBSERVE→ACT). **Outcome**: progress
(infrastructure, verified 0-axiom).

Erdős #64 ("does every finite graph with min degree ≥ 3 contain a cycle of length
2^k, k≥2?") is OPEN ($1000). The power-of-two-LENGTH content is deep (Liu–Montgomery
scale). This session proved the *elementary precondition* that any such cycle presumes —
that a cycle exists at all — for the connected case. Added 3 axiom-free theorems to
`Erdos85`-style toolkit reuse in `Erdos64Problem.lean`:

- `connected_hasMinDegree_two_not_isAcyclic` — nontrivial connected `G`, `HasMinDegree G 2`
  ⟹ `¬ G.IsAcyclic`. Proof: connected + acyclic ⟹ `G.IsTree`; a nontrivial tree has
  `minDegree = 1` (`SimpleGraph.IsTree.minDegree_eq_one_of_nontrivial`, the "tree has a
  leaf" fact), contradicting `2 ≤ G.minDegree` (from `le_minDegree_of_forall_le_degree`).
- `connected_hasMinDegree_two_exists_cycle` — same hypotheses ⟹ `∃ v (c : G.Walk v v),
  c.IsCycle`. `IsAcyclic` unfolds to "no closed walk is a cycle", so its negation is a
  concrete cycle (`by_contra` + rebuild the `IsAcyclic` witness from `¬∃`).
- `connected_hasMinDegree_three_exists_cycle` — the Problem-64 degree-3 hypothesis
  (connected) forces a cycle (`3 ≥ 2` weakening).

### Lean gotchas (recorded)
- `simp [SimpleGraph.degree]` to turn `2 ≤ G.degree v` into `2 ≤ (neighborFinset v).card`
  **blows `maxRecDepth`**. Use `rw [← SimpleGraph.card_neighborFinset_eq_degree]` instead
  (clean, no recursion).
- `push_neg` is **deprecated** in v4.31 (warns, suggests `push Not`). Avoided entirely:
  `by_contra hcon; exact not_isAcyclic … (fun v c hc => hcon ⟨v,c,hc⟩)` reconstructs the
  `IsAcyclic` witness directly.
- `SimpleGraph.IsTree` is a structure `extends connected : G.Connected` with field
  `isAcyclic`; build it with the anonymous constructor `⟨hconn, hacyc⟩`.

### Verification
Host-verified (`lake env lean`, Lean v4.31.0, exit 0, no warnings). `#print axioms` for all
three = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `Lean.ofReduceBool`.
File 205→268 lines, theoremCount 3→6.

### Mathlib gaps found
- Only the CONNECTED leaf lemma exists (`IsTree.minDegree_eq_one_of_nontrivial`); no general
  forest leaf lemma, and no forest edge-count bound `#edges ≤ n−1` (only `IsTree.card_edgeFinset`).
- No pre-existing `minDegree ⟹ contains-cycle` result in Mathlib — this lemma is novel.

### Next
- **General finite-graph case** (the honest remaining step): pass to the connected component
  of any vertex (degrees preserved inside a component ⟹ min degree ≥ 2 survives; component is
  connected + nontrivial), apply the connected lemma, lift the cycle to `G` through the
  induced-subgraph embedding (`Walk.IsCycle` transport via `SimpleGraph.induce`). Needs the
  component-degree-preservation lemma.
- Bridge the file's custom `ContainsCycleLength` (`Fin.succMod` encoding) to Mathlib
  `Walk.IsCycle` so cycle-*length* statements become expressible.
- The open core (some cycle of length `2^k`) stays deep/imported (Liu–Montgomery).
