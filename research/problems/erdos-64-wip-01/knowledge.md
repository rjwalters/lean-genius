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

## Session 2026-07-21 (researcher-1-4) — bridge Walk.IsCycle → ContainsCycleLength

**Mode**: depth-first on a MODERATE node; elementary cycle-EXISTENCE layer (connected
`connected_hasMinDegree_two_exists_cycle` and disconnected `hasMinDegree_two_exists_cycle`)
was already SATURATED. **Outcome**: progress (infrastructure, verified 0-axiom).

Closed the honest "Next" gap those lemmas left: they produce a `SimpleGraph.Walk.IsCycle`
witness, but `erdos_64_conjecture` is stated with this file's own `ContainsCycleLength`
predicate (an injective `Fin k → V` with `Fin.succMod` cyclic adjacency). Added the bridge:

- `isCycle_containsCycleLength` — for any `c : G.Walk v v` with `c.IsCycle`,
  `ContainsCycleLength G c.length`. Take `vs i = c.getVert i.val` on `Fin c.length`:
  injective via `SimpleGraph.Walk.IsCycle.getVert_injOn'` (`InjOn getVert {i | i ≤ length-1}`);
  cyclic adjacency via `SimpleGraph.Walk.adj_getVert_succ`, the wrap edge `length-1 → 0`
  closing because `c.getVert c.length = v = c.getVert 0` (`getVert_length`, `getVert_zero`).
- `hasMinDegree_two_containsCycleLength` / `hasMinDegree_three_containsCycleLength` —
  min-degree ≥ 2 (resp. the Problem-64 degree-3 hypothesis) on a nonempty finite graph
  ⟹ `∃ k ≥ 3, ContainsCycleLength G k`. Just measures `c.length` of the cycle from
  `hasMinDegree_two_exists_cycle`. This restates the elementary precondition of Problem 64
  in the exact predicate the conjecture uses; the open content is that `k` can be taken a
  power of two `2^m`.

### Key Mathlib lemmas (getVert enumeration of a cycle)
- `IsCycle.getVert_injOn'` : `Set.InjOn p.getVert {i | i ≤ p.length - 1}` (the clean one for
  a `Fin p.length` index; `getVert_injOn` uses `1 ≤ i ≤ length`, off by the endpoint).
- `Walk.adj_getVert_succ (hi : i < p.length) : G.Adj (p.getVert i) (p.getVert (i+1))`.
- `Walk.getVert_zero`, `Walk.getVert_length` close the wrap-around edge.
- `Fin.succMod _ i |>.val` reduces definitionally to `(i.val + 1) % k`; a `show` with that
  RHS lets `Nat.mod_eq_of_lt` / `Nat.mod_self` split the interior vs wrap cases.

### Verification
Host-verified (`lake env lean`, Lean v4.31.0, exit 0, no warnings). `#print axioms` for all
three = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `Lean.ofReduceBool`.
File 316→379 lines.

### Next
- The open core (some cycle of length `2^k`) stays deep/imported (Liu–Montgomery). No
  elementary path remains for the *length = power-of-two* refinement.
- Optional: a girth/`egirth` restatement (`SimpleGraph.girth_le_length`) is now within reach
  but adds little beyond the existing `∃ k ≥ 3` bound.
