# Knowledge: erdos-548-incomplete-01 (Erdős–Sós Conjecture)

## Session 2026-07-23 (researcher-1): all 8 companion sorries filled

The problem.md target ("complete the 6 sorries") is DONE — both Aristotle
companion files are now sorry-free (8 sorries total at session start):

- `Erdos548Aristotle.lean` (5): pathGraph_adj_symm / starGraph_adj_symm
  (`⟨fun h => h.symm, fun h => h.symm⟩` — SimpleGraph.Adj.symm on both iff
  directions), starGraph_center_adj (`Or.inl ⟨rfl, hj⟩` — the Adj of a
  structure-literal graph unfolds definitionally), sum_degrees_twice_edges_ari
  (`G.sum_degrees_eq_twice_card_edges` verbatim), containsSubgraph_refl
  (`⟨id, Function.injective_id, fun _ _ h => h⟩`).
- `Erdos548ProblemAristotle.lean` (3): sum_degrees_eq_twice_edges (copy of the
  main file's proof: convert + congr!), starGraph_connected (verbatim copy of
  the main file's proof — identical local starGraph def), starGraph_adj_reachable
  (`h.reachable`).

Host-verified v4.31: parent `Erdos548Problem.lean` elaborated with
`lake env lean -o .lake/build/lib/lean/Proofs/Erdos548Problem.olean` (exit 0,
warnings only), then both companions `lake env lean` exit 0. All fills are
term-mode or copied tactic proofs — no new axioms, no native_decide.

## File inventory

- `Erdos548Problem.lean` (513 lines): 0 sorries, **8 axioms** — 7 are
  literature-named DEEP results (brandt_dobson, sacle_wozniak, wang_li_liu,
  path_extremal, komlos_sos_large_k, erdos_gallai_matching, turan_path_formula)
  plus `trivial_tree_bound` (generic-named, provable in principle, see below).
- Both companions: 0 sorries.
- Gallery meta (src/data/proofs/erdos-548/meta.json) tracks only the main file
  (additionalFiles: null); its `sorries = 0` was already accurate for the main
  file and is now accurate for the whole family.

## Next steps

1. **`trivial_tree_bound`** (n(k−1)+1 edges ⟹ contains every tree with k
   edges) is the one Mathlib-provable axiom (the incomplete-01 generic-named
   vein). Standard proof: (a) any G with e(G) > (k−1)n has a subgraph H with
   δ(H) ≥ k (delete low-degree vertices, ≤ (k−1)n edges removed); (b) δ(H) ≥ k
   ⟹ H ⊇ every k-edge tree (greedy leaf-order embedding — needs tree leaf
   induction). Substantial: needs min-degree subgraph extraction + tree
   induction; NOT obviously session-sized in SimpleGraph API. Check whether
   Mathlib has `SimpleGraph.exists_subgraph_minDegree` analogues first.
2. The other 7 axioms are genuine literature results — leave as axioms.
3. The conjecture itself (ErdosSosConjecture) is OPEN — never a target.
