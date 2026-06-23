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

## Session 2026-06-22 (Session 3) — Quantify the witness tower's size

**Mode**: CONTINUE (SOLVED → outward follow-up) · **Outcome**: progress (new theory-level
content: exact vertex count of the tower, addressing a documented open question)

### What I Did
The colourability theory was already complete (and Session-2's "next steps" — the concrete
K₂ witness and exact `iff` — were in fact already in the file). The file pinned the
*chromatic number* of the tower but said nothing about its *size*, which is precisely the
variable in Erdős #1104's `f(n)`. Added the size theory:
- `fintypeMycVertexIter`: recursive `Fintype` instance for the iterated vertex type.
- `card_mycVertex`: one Mycielski step doubles the vertex count, `|M(G)| = 2|G| + 1`.
- `card_mycVertexIter_succ`: the doubling recurrence for the tower.
- `card_mycVertexIter_add_one`: subtraction-free closed form `|tower_k| + 1 = (|V|+1)·2^k`.
- `card_mycVertexIter_fin_two`: over K₂, `|tower_k| + 1 = 3·2^k`.
- `exists_triangleFree_chromatic_with_card`: the quantified witness — a triangle-free graph
  on `N` vertices (`N+1 = 3·2^k`) of chromatic number exactly `k+2`, so `χ ≍ log₂ N`.

This directly addresses the meta.json open question "Quantify the construction's efficiency:
the tower's vertex count roughly doubles each step …", making explicit the exponential gap to
the true `f(n) = Θ(√(n/log n))`.

### Key Findings
- **`mycVertexIter V (k+1)` is *definitionally* `MycVertex (mycVertexIter V k)`, but the
  auto-derived `Fintype` instance and the `Option`/`Sum` instance are not syntactically
  defeq for `exact`.** Bridge with the instance-agnostic `Fintype.card_congr (Equiv.refl _)`:
  `have e : mycVertexIter V (k+1) ≃ MycVertex (mycVertexIter V k) := Equiv.refl _; rw [Fintype.card_congr e]`.
- **Refer to a recursive `instance` by expected type, not a named argument.** Section
  `variable {V}` is auto-bound, so `fintypeMycVertexIter (V := V) k` fails ("Invalid argument
  name V"); write `fintypeMycVertexIter k` and let the expected `Fintype (mycVertexIter V k)`
  pin `V`. As a global instance it is also found by TC automatically — no `haveI` needed (a
  named `haveI` even *causes* an inner-instance mismatch `this` vs `fintypeMycVertexIter k`).
- **Keep the closed form subtraction-free** (`card + 1 = (c+1)·2^k`) to avoid ℕ-subtraction;
  the succ step is `2·a + 1 + 1 = 2·(a+1)`, closed by `ring` after `rw [← ih]`.
- Base case `card (mycVertexIter V 0) = card V` is `rfl` (the instance reduces to ambient).

### Files Modified
- `proofs/Proofs/Erdos1104OQ01.lean` (added size section, 345→420 lines, 6 thm + 1 instance)
- `src/data/proofs/erdos-1104-oq-01/meta.json` (counts, contributions, section, open Qs)

### Next Steps
- Formalize the quantitative gap to `f(n) = Θ(√(n/log n))` and the sharper random/Kim R(3,k)
  constructions that achieve the optimal exponent (Mycielski's tower provably cannot).
- Discharge the parent `erdos-1104` `mycielski_construction` axiom against this construction.
