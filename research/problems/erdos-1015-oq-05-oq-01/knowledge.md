# Knowledge Base: erdos-1015-oq-05-oq-01

**Question:** Prove `moon_f3 : f 3 = 4` (Moon 1966) in Lean.

## Status: COMPLETED (partial — infrastructure shipped, full result BLOCKED)

Moon's theorem f(3) = 4 is a genuine 1966 extremal-graph result. Fully
formalizing it needs:

- **Upper bound f(3) ≤ 4:** every 2-coloring of Kₙ (n large) admits a packing
  into vertex-disjoint monochromatic triangles leaving ≤ 4 vertices. Requires
  extremal case analysis over colorings — **not in Mathlib**.
- **Lower bound f(3) ≥ 4:** an explicit coloring forcing 4 leftover vertices.

Additionally, `Erdos1015OQ01.lean` states `moon_f3` over `axiom f : ℕ → ℕ`, so
there the equation is **uninterpreted** and cannot be discharged. Real progress
requires the concrete `f` built on `CliquePartition` in `Erdos1015Problem.lean`.

## What was shipped: `Erdos1015OQ05OQ01.lean` (0 axioms, 0 sorries)

Self-contained (mirrors the parent's concrete definitions, imports none of its
axioms). Proves the **leftover residue constraint**:

| Result | Statement |
|--------|-----------|
| `coveredVertices_card` | covered.card = (#cliques)·t (exact, uses disjointness) |
| `coveredVertices_card_mod` | covered.card % t = 0 |
| `leftover_eq` | leftover = n − (#cliques)·t |
| `leftover_mod` | (n − leftover) % t = 0, i.e. leftover ≡ n (mod t) |
| `triangle_leftover_mod3` | t=3 specialization |
| `triangle_leftover_pos_of_mod3` | 3 ∤ n ⟹ no perfect triangle packing |

Key technique: `card_foldl_union_aux` — folding `∪` over pairwise-disjoint
equal-size Finsets, with the accumulator **generalized** through the induction,
yields an exact `k·t` count (disjointness upgrades `card(⋃) ≤ Σcard` to equality).

`#print axioms` on every result: only `propext / Classical.choice / Quot.sound`.

## Why this is honest, not inflated

The mod-3 obstruction only forces `leftover ∈ {0,1,2}` depending on `n mod 3`.
The real content of f(3)=4 — that the *worst case* is 4, not smaller — is exactly
the part beyond current Mathlib and is left as the open question. This entry
advances the mechanism without claiming the theorem.

## Mathlib gaps blocking the full result

- No monochromatic clique-packing / triangle-decomposition API.
- No machinery for exhaustive case analysis over 2-colorings of Kₙ.

## Next steps (for a future session)

- Build clique-packing infrastructure at the Mathlib level first.
- The lower bound f(3) ≥ 4 (a single small witness coloring) may be more
  tractable than the upper bound.
