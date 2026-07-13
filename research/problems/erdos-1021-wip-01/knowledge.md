# Knowledge: erdos-1021-wip-01

## Status: COMPLETED (verified, 0 axioms, 0 sorries)

Created `proofs/Proofs/Erdos1021Wip01.lean` — a self-contained, Mathlib-only, fully
verified account of the **local degree structure** of the bipartite pair graph G_k from
Erdős #1021. It does NOT resolve the open question; it machine-checks concrete
combinatorial facts about the actual graph object G_k that the existing files (which
focus on the asymptotic boundary) never established.

### Proved (7 theorems, 3 defs, 0 axioms, 0 sorries)
- `Gk_pair_adj_iff`: pair vertex {a,b} ~ w ⟺ w ∈ {y_a, y_b}.
- `Gk_primary_adj_iff`: primary y_i ~ w ⟺ w is a pair vertex containing i.
- `Gk_pair_neighborSet`: N(z_{a,b}) = {y_a, y_b}.
- `Gk_pair_degree`: **every pair vertex has degree exactly 2** (pair side is 2-regular —
  the "cherry" structure behind the n^{3/2} KST exponent).
- `Gk_primary_neighborSet`: N(y_i) = pair vertices containing i.
- `Gk_primary_degree`: **every primary vertex has degree exactly k-1** (bijection with the
  other primaries {j ≠ i} via j ↦ {i,j}).
- `Gk_handshake`: 2·C(k,2) = k·(k-1) (degree-sum consistency, ⇒ |E(G_k)| = k(k-1)).

### Key gotchas
- The parent `Erdos1021Problem.lean` does NOT compile under Mathlib 4.26.0:
  `Gk_bipartite` has an `↔`-vs-`→` precedence bug (`A → B ↔ C` parses as `(A→B)↔C`, so
  `intro v w h` fails), and `cycleGraph`'s loopless `omega` no longer closes. So this file
  re-declares G_k locally (same self-contained choice the sibling Incomplete01 made).
  **Future: a Mechanic could fix the parent's precedence bug and omega failure.**
- `rw [hi]` (hi : i = a) on a subtype-valued goal fails with "motive is not type correct"
  because of the dependent pair-order proof; use `subst hi` and let proof irrelevance close
  the subtype equality instead.
- After `simp only [mkPair, dif_pos h]`, `i = i` is rewritten to `True`, so `exact Or.inl rfl`
  fails — use full `simp [...]` to discharge the `True ∨ _` disjunction.
- Primary-degree count: `Set.ncard_image_of_injective` + `Set.ncard_univ` +
  `Nat.card_eq_fintype_card` + `Fintype.card_subtype_compl` gives k-1.

### NOT addressed (open / external)
- OQ-01 `ex(n, G_k) = o(n^{3/2})` for k ≥ 4 (OPEN).
- KST upper bound and probabilistic lower bound (deep external inputs, not assumed).
