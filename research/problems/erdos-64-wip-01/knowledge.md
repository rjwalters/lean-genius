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

## Session 2026-07-22 (researcher-1): even-cycle parity layer

### Result
`hasMinDegree_three_exists_even_cycle` — every nonempty finite graph with min degree ≥ 3
contains a cycle of **even** length (explicit `Walk.IsCycle`), plus
`hasMinDegree_three_exists_even_containsCycleLength` (even `k ≥ 4` in the
`ContainsCycleLength` predicate). Parity part of the necessary condition of Problem 64:
a `2^k`-cycle is in particular even. Strictly between plain cycle existence (previous
sessions) and the open power-of-two core.

### Mechanism (classical longest-path parity argument)
Take a maximum-length path `p` starting at `v₀`. Maximality traps every neighbour of `v₀`
on `p.support` (else `Walk.cons` extends it). The ≥3 neighbours sit at distinct positive
indices (`takeUntil` lengths); if `a < b` are the two largest (so `a ≥ 2`), the closings
at index `a`, at index `b`, and around the segment `[a,b]` are three cycles of lengths
`a+1`, `b+1`, `b−a+2`, summing to `2b+4` (even) — one must be even.

### Lean idioms discovered
- **Maximal path**: `Nat.sSup_mem` on `{n | ∃ a b (q : G.Walk a b), q.IsPath ∧ q.length = n}`
  (nonempty via `Walk.nil`, `BddAbove` via `IsPath.length_lt`), maximality via `le_csSup`.
  Mathlib has NO dedicated longest-path API.
- **Neighbour → index**: `idx w := (p.takeUntil w hw).length` (dite-wrapped for totality);
  injective on neighbours via `Walk.getVert_length_takeUntil`; image finset + `max'`/`erase`
  extracts the two largest indices.
- **Closing a prefix into a cycle**: `Walk.cons_isCycle_iff` + `IsPath.eq_snd_of_mem_edges`
  (an edge of a path through its start must be the first edge; kills the `s(v₀,w) ∈ edges`
  obstruction when the index is ≥ 2).
- **Segment cycle**: `r := (p.dropUntil x _).takeUntil y _`; getVert bookkeeping via
  `dropUntil_eq_drop` + `drop_getVert` + `getVert_copy`, `length_takeUntil` (= support.idxOf),
  `IsPath.getVert_injOn` for exact length; close with `IsPath.concat` + `cons_isCycle_iff`.
- **Gotcha**: do NOT `set q := p.takeUntil w hw` before applying `getVert_injOn` — freshly
  elaborated membership goals use the unfolded spelling, so omega sees two different atoms
  and fails. Use the explicit spelling (or fold nothing).

### Next
- Dirac-type rung: min degree d ⇒ cycle length ≥ d+1 — same maximal-path engine, now in-file.
- The 2^k core stays blocked (Liu–Montgomery scale).

## Session 2026-07-22b (researcher-1) — Dirac-type rung: min degree d ⇒ cycle length ≥ d+1

**Mode**: cash in the recorded "Next" item (same maximal-path engine, now in-file).
**Outcome**: 2 theorems, axiom-free, host-verified `lake env lean` exit 0 first try,
zero warnings. File 607→732 lines, theorems 12→14 (public).

- `hasMinDegree_exists_cycle_length_ge` — min degree `d ≥ 2` forces
  `∃ v (c : G.Walk v v), c.IsCycle ∧ d + 1 ≤ c.length`. Engine identical to the
  even-cycle session: maximal path from `v₀`, all neighbours trapped at distinct
  positive `takeUntil`-length indices. NEW piece: the largest index `b = T.max'`
  satisfies `d ≤ b` because `T ⊆ Finset.Icc 1 b` (`hpos` + `le_max'`) and
  `Finset.card_le_card` + `Nat.card_Icc` give `d ≤ |T| ≤ b`. Close the prefix at
  index `b` (needs only `2 ≤ b`, from `d ≥ 2`) — cycle length `b + 1 ≥ d + 1`.
- `hasMinDegree_containsCycleLength_ge` — `ContainsCycleLength` restatement via
  `isCycle_containsCycleLength`.

### Lean notes
- The pigeonhole "d distinct positive integers have max ≥ d" is exactly
  `T ⊆ Icc 1 max'` + `Nat.card_Icc` (`|Icc 1 b| = b`), then omega. No induction.
- Single-index cycle closure needs NO segment machinery (no dropUntil) — the
  `hclose` sub-proof of the even-cycle theorem inlines cleanly with `y` at `max'`.

### Next
- Elementary layer now FULLY saturated: existence (min-deg 2), length-predicate
  bridge, parity (even cycle, min-deg 3), Dirac rung (length ≥ d+1). Every
  remaining gap is the deep 2^k-length core (Liu–Montgomery scale) — girth/BFS
  layering or structured expansion, no elementary path. STAND DOWN.

## Session 2026-07-23 (researcher-1) — Cycle-spectrum counting rung: min degree d ⇒ ≥ d−1 distinct cycle lengths

**Mode**: REVISIT of a "fully saturated" verdict — found a genuine counting gap the
verdict missed (precedent: the even-cycle layer was also found post-"SATURATED").
**Outcome**: 2 theorems, axiom-free, host-verified `lake env lean` exit 0 first try,
zero warnings. File 732→867 lines, theorems 14→16.

- `hasMinDegree_card_cycle_lengths` — min degree `d ≥ 2` forces
  `∃ S : Finset ℕ, d - 1 ≤ S.card ∧ ∀ k ∈ S, 3 ≤ k ∧ (explicit IsCycle of length k)`.
  The Dirac session closed the prefix only at the MAX trapped index; here EVERY
  index `n ≥ 2` closes (same sub-proof, parametrized), and distinct indices give
  distinct lengths `n+1`. Spectrum = `(T.filter (2 ≤ ·)).image (· + 1)`.
- `hasMinDegree_card_containsCycleLength` — restatement via
  `isCycle_containsCycleLength` + `hlen ▸`.

### New counting pieces (beyond the reused engine)
- "At most one trapped index equals 1": `T ⊆ insert 1 (T.filter (2 ≤ ·))`
  (from `hpos` + omega case split), then `Finset.card_insert_le` + omega gives
  `d ≤ |filter| + 1`. No erase/max' machinery needed.
- `Finset.card_image_of_injective _ (add_left_injective 1)` works on the nose for
  the `(· + 1)` image.
- The per-index closure sub-proof from the Dirac rung inlines verbatim with `b`
  replaced by an arbitrary filtered index `n` — its only requirement really is `2 ≤ n`.

### Relevance to Problem 64
This is the elementary end of the cycle-SPECTRUM view: Liu–Montgomery prove the
large-min-degree case by showing the spectrum is dense enough to contain a power
of two. The linear bound `|spectrum| ≥ d−1` is what elementary methods give; at
d = 3 it guarantees only 2 lengths, far from forcing a power of two.

### Next
- Elementary layer now: existence + bridge + parity + Dirac + spectrum count.
- Conceivable further rung: even-length spectrum counting (≥ ⌊(d−1)/2⌋ even lengths?)
  — the three-cycle parity trick doesn't parametrize as cleanly; assess before claiming.
- The 2^k core stays blocked (Liu–Montgomery scale) — genuinely new mechanism required.
