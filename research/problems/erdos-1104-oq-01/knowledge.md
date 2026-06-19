# erdos-1104-oq-01 — Mycielskian witnesses for triangle-free chromatic number

## Problem

Erdős #1104 asks for the growth of `f(n) = max χ(G)` over triangle-free graphs on `n`
vertices. The lower-bound side rests on the existence of triangle-free graphs of
arbitrarily large chromatic number. The classical constructive witness is **Mycielski's
construction** `M(G)`, which preserves triangle-freeness and raises the chromatic number
by exactly one. This sub-problem formalizes that construction (Mathlib has no Mycielskian)
and the witness machinery it powers.

## Summary

`proofs/Proofs/Erdos1104OQ01.lean` — 281 lines, **0 sorries, 0 axioms**, `verified`.
The **full Mycielski theorem**: construction, triangle-free preservation, the `(n+1)`
upper bound, the recolouring lower bound (`χ(M(G)) = χ(G)+1` pinned exactly), and the
iterated witness family.

The parent gallery entry `erdos-1104` posits a `mycielski_construction` *axiom*; this
entry supplies the genuine construction and proves its defining properties.

## Session 2026-06-19 (Session 1) — Build the Mycielskian, FRESH

**Mode**: FRESH · **Outcome**: progress (verified construction + two of the three core
properties; chromatic lower bound isolated as open crux)

### What I Did
- Defined the Mycielskian via `SimpleGraph.fromRel` on `Option (V ⊕ V)` (original /
  shadow / apex), letting `fromRel` discharge symmetry and looplessness.
- Proved nine adjacency-characterisation `@[simp]` lemmas (one per Option/Sum pair).
- `mycielskian_cliqueFree_three`: triangle-free preservation, by case analysis on the
  three triangle vertices, collapsing every surviving case to a `G`-triangle via
  `is3Clique_triple_iff`.
- `mycielskian_colorable_succ`: constructive `(n+1)`-colouring (`mycColor`: originals and
  shadows keep `C`'s colour via `Fin.castSucc`, apex takes `Fin.last n`).
- Iterated witness family: `mycVertexIter` / `mycielskianIter` (structural recursion on
  `k`), `mycielskianIter_cliqueFree_three`, `mycielskianIter_colorable`, and
  `mycielskian_witness_family` packaging both.

### Key Findings
- `SimpleGraph.fromRel r` (`Adj a b ↔ a ≠ b ∧ (r a b ∨ r b a)`) is the clean way to build
  a bespoke graph: the raw relation `mycRel` need not be symmetric.
- Triangle-free preservation hinges on: the apex is in no triangle (only adjacent to the
  independent shadow class), and a triangle uses ≤ 1 shadow, so it projects to `G`.
- The chromatic *upper* bound is fully constructive; the matching lower bound is the only
  hard ingredient.

### Files Modified
- `proofs/Proofs/Erdos1104OQ01.lean` (new)
- `proofs/Proofs.lean` (registered import)

### Next Steps
- Prove the chromatic lower bound `(mycielskian G).Colorable (n+1) → G.Colorable n`
  (Mycielski's recolouring argument) — the open crux; submit to Aristotle.
- With the lower bound, conclude `χ(mycielskianIter (cycleGraph 5) k) = k + 3`, giving
  explicit triangle-free graphs of every chromatic number ≥ 3.
- Optionally instantiate at a concrete base (`⊤ : SimpleGraph (Fin 2)` or `cycleGraph 5`)
  for a closed-form witness count.

## Session 2026-06-19 (Session 2) — Close the open crux: chromatic lower bound

**Mode**: CONTINUE · **Outcome**: progress (the previously-open chromatic lower bound is
now proven; the full Mycielski theorem is complete and machine-checked)

### What I Did
- Proved `mycielskian_colorable_of_succ`: `(M G).Colorable (n+1) → G.Colorable n`,
  Mycielski's recolouring argument — the half flagged as the open crux in Session 1.
- Given a proper `(n+1)`-colouring `C` of `M(G)` with apex colour `a := C none`, recolour
  `G` by `D u := if C (orig u) = a then C (shadow u) else C (orig u)`.
- Showed `D` never uses `a` (shadows are apex-adjacent, so `C (shadow u) ≠ a`) and is
  proper (adjacent originals differ in `C`, so cannot both equal `a`; the remaining three
  cases use the `u'~v`, `u~v'`, `u~v` edges of `M(G)`).
- Transported `D` into `Fin n` via `Fintype.equivFinOfCardEq` on the `n`-element
  complement `{x : Fin (n+1) // x ≠ a}` (`Fintype.card_subtype_compl`).

### Key Findings
- The recolouring needs no Aristotle: it is an elementary `by_cases` on whether each
  endpoint's original wears the apex colour, dispatched by the adjacency simp-lemmas.
- The only non-routine step is packaging "lands in an `n`-element set" as an
  `n`-colouring — done cleanly by the subtype-complement cardinality + `equivFinOfCardEq`.
- Combined with `mycielskian_colorable_succ`, this pins `χ(M(G)) = χ(G)+1` exactly.

### Files Modified
- `proofs/Proofs/Erdos1104OQ01.lean` (added `mycielskian_colorable_of_succ`, 217→281 lines)

### Next Steps
- Instantiate the witness tower at a concrete base (`cycleGraph 5` / `⊤ : SimpleGraph
  (Fin 2)`) and combine both bounds to conclude `χ(mycielskianIter base k) = k + base`.
- Discharge the parent `erdos-1104` `mycielski_construction` axiom against this proof.
- Consider upstreaming the Mycielskian to Mathlib.

## Mathlib Gaps
- No Mycielskian construction in Mathlib (`Combinatorics/SimpleGraph/*`) — built here.
- No `χ(M(G)) = χ(G)+1` theorem — both inequalities are proved in this file.
