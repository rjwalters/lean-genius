# Knowledge: ramsey-r4k-oq-02

## Established Facts

- **R(4,3) ≥ 9** is now formalized: `RamseyR4kOQ02.r43_lower : ¬ RamseyR4k.RamseyProp 8 4 3`
  (file `proofs/Proofs/RamseyR4kOQ02.lean`). VERIFIED, 0-axiom (only
  propext/Classical.choice/Quot.sound; `decide`, not `native_decide`).
- The extremal witness is the **Wagner graph V₈** taken as the blue color:
  `wagnerColor i j = false` iff (i−j) mod 8 ∈ {0,1,4,7}. It is triangle-free
  (no blue K₃) and has independence number 3 (so its complement, the red graph,
  has no K₄).
- Both clique-freeness facts are decidable finite checks over subsets of Fin 8
  (`set_option maxRecDepth 4000` required for the kernel `decide`).

## Open Questions Within This Problem

- **Exact upper bound R(4,3) ≤ 9** (every 2-coloring of K₉ has a red K₄ or blue K₃).
  The parent only gives the binomial bound ≤ 10. This needs either an exhaustive/SAT
  argument over K₉ or a degree/parity combinatorial argument — not yet attempted.
- **R(4,4) = 18** and **R(4,5) = 25** — both halves still open; the lower bounds need
  17- and 24-vertex extremal colorings (Paley graph on 17 vertices for R(4,4)>17).

## Failed Approaches

- Plain `decide` on the clique-freeness existentials hits "maximum recursion depth";
  fixed by `set_option maxRecDepth 4000`.
- `native_decide` would also work but introduces the `Lean.ofReduceBool` axiom;
  avoided in favor of axiom-free `decide`.

## Promising Leads

- For R(4,3) ≤ 9: the standard combinatorial proof pivots on a vertex of K₉ — among
  its 8 edges, ≥6 red forces a red K₄ analysis, ≥3 blue forces a blue triangle unless
  the blue neighbors are mutually red; a degree/parity count finishes it. Formalizable
  without exhaustive search.
- For R(4,4) > 17: the Paley graph on F₁₇ (quadratic-residue connection set) is the
  extremal coloring; its clique/independence checks are larger but still decidable.
