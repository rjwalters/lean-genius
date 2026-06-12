# Knowledge Base: randomized-maxcut-oq-03

Insights accumulated during research on this problem.

---

## Problem Understanding

OQ-03 asks for the **tightness** direction of the randomized MaxCut
1/2-approximation. The parent file `Proofs.RandomizedMaxCut` ships the lower
bound (`E[|C|] ≥ MaxCut/2`); OQ-03 must exhibit a graph family where the ratio
`E[|C|] / MaxCut(G)` equals exactly `1/2`. The answer is the bipartite family.

---

## Insights

- **Abstract mechanism (full cut ⇒ tight).** If a boolean assignment `f` cuts
  *every* edge of `G`, then `MaxCut(G) = |E|` exactly: the full cut realises a cut
  of size `|E|`, and the parent's `maxCut_le_edges` gives the reverse inequality.
  Combined with the parent's `expected_cut_size` (`E[|C|] = |E|/2`), this yields
  `E[|C|] = MaxCut(G)/2`. Tightness needs *no probability theory beyond the
  parent* — only the deterministic `MaxCut = |E|` fact.
- **Bipartite = admits a proper 2-colouring `f : V → Bool`.** A proper colouring
  (adjacent vertices differ) cuts every edge, so it is a full cut. This is the
  cleanest Lean-side characterisation; it sidesteps Mathlib's
  `SimpleGraph.IsBipartite` API entirely (whose lemma names were a stated risk).
- **`edgeInCut (ofAssignment f) s(u,v) = true ↔ f u ≠ f v`** is the key bridge
  lemma; proved by unfolding + `Sym2.lift_mk` + `cases f u <;> cases f v <;> simp`.
- **Concrete witness built in-file.** `completeBipartite m n` on `Fin m ⊕ Fin n`
  with `Adj u v := u.isLeft ≠ v.isLeft` is self-contained (no Mathlib
  `completeBipartiteGraph` dependency); `Sum.isLeft` is *definitionally* a proper
  2-colouring, so the witness proof is `fun _ _ hadj => hadj`.

### Shipped (S2 ACT, 0 sorries / 0 axioms)
`proofs/Proofs/RandomizedMaxCutOQ03.lean`:
- `edgeInCut_ofAssignment_iff`, `IsFullCut`
- `maxCut_eq_edges_of_fullCut`, `rand_approx_tight_of_fullCut`
- `IsProper2Coloring`, `fullCut_of_proper2Coloring`,
  `rand_approx_tight_of_proper2Coloring`
- `completeBipartite`, `isProper2Coloring_completeBipartite`,
  `rand_approx_tight_completeBipartite` (the concrete `K_{m,n}` witness)

## Parent-file repair (required to build)

The parent `Proofs/RandomizedMaxCut.lean` did **not** compile against the pinned
Mathlib `v4.26.0`: `Function.update_same` / `Function.update_noteq` were removed.
Repaired in `count_diff_assignments` by rewriting via the stable
`Function.update_apply` + `if_true` / `if_neg`. This unblocks the entire
randomized-maxcut family, not just OQ-03.

---

## Dead Ends

- Relying on `Function.update_same` / `Function.update_noteq` (removed in v4.26.0).
- `if_pos rfl` after `Function.update_apply` — the guard is already normalised to
  `True`, so the rewrite never fires; `if_true` is required.
