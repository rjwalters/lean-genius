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

## 2026-07-23 (researcher-1) — min-degree extraction PROVED (half of trivial_tree_bound)

Part XI added to `Erdos548Problem.lean` (appended at end, 0 new axioms, host
`lake env lean` EXIT=0, lint-clean, `#print axioms` foundational only):

- `edgesInside G t` — edges with both endpoints in a `Finset t` (needed because
  a global-minDegree statement is FALSE — same isolated-vertex trap as the
  erdos-751 repair; internal-degree Finset form is the sound one).
- `edgesInside_erase_bound` — deleting `v` destroys ≤ deg_t(v) inside-edges
  (union-image counting; use `Sym2.other_spec`/`Sym2.other_mem`, NOT
  `rw [← other_spec]` which fails motive-typecheck).
- `exists_min_degree_subset` — strong induction: `(k−1)|t| + 1 ≤ e(t)` yields
  nonempty `s ⊆ t` with internal degree ≥ k everywhere. Nonlinear arithmetic
  handled by one `conv_lhs => rw [← Nat.sub_add_cancel]; ring` identity + omega.
- `edgeCount_eq_card_edgeFinset` — instance bridge (edgeCount was defined under
  `open scoped Classical`; ext + `mem_edgeFinset` closes the two-instance gap;
  `simpa [edgeCount]` FAILS with instance mismatch).
- `exists_min_degree_subset_of_edgeCount` — extraction from
  `(k−1)·|V| + 1 ≤ edgeCount G` (matches trivial_tree_bound's hypothesis up to
  `mul_comm`).

**Remaining to eliminate `trivial_tree_bound` (next session):** greedy tree
embedding — a Finset `s` with internal degree ≥ k contains every tree on k+1
vertices. Route: induction on `Fintype.card W` (T on W); remove a leaf
(`IsTree.exists_vert_degree_one_of_nontrivial` — needs Nontrivial;
singleton tree base case), embed the smaller tree
(`Connected.induce_compl_singleton_of_degree_eq_one` keeps it a tree — also
need acyclicity of induce: `IsAcyclic.induce`), then extend: image has ≤ k
vertices, the attachment vertex has ≥ k internal neighbours, so a fresh one
exists. Injectivity bookkeeping like `star_easier`'s `Fin.cases` embedding.
Then `trivial_tree_bound` = extraction + embedding + `ContainsSubgraph` via
the induced-subgraph inclusion.

Other axioms (brandt_dobson, sacle_wozniak, wang_li_liu, komlos_sos_large_k,
erdos_gallai_matching, path_extremal, turan_path_formula) are person/paper-named
DEEP results — leave axiomatized.
