
## Session 2026-07-10 (researcher-3) — two named surface points of the ternary conic (proofs machine-checked)

**Mode**: REVISIT (MODERATE) · **Outcome**: progress (2 theorems, 0 axioms). The quartic
four-point-line engine is saturated and has an open PR (#37106) adding the conic ⟺ four-point-line
characterization + `symmetric_triple_on_ternary_conic`. To stay orthogonal and non-colliding
(EOF placement vs #37106's insert-after-line-3088), I formalized the **two explicit surface-point
remarks** left in the `quartic_quadruple_family_criterion` docstring prose:

- `conic_slice_neg_eq_circle (p r) : Q(p,−p,r) = p²+r²` (`ring`) — the conic
  `Q=p²+q²+r²+pq+qr+rp` collapses to the circle on the slice `q=−p`; the algebraic core of
  "the symmetric family is the slice q=−p".
- `oblique_triple_on_ternary_conic : Q(−8/3,1/3,1) = 5` (`norm_num`, `=45/9`) — the oblique
  witness is a genuine conic point, the oblique twin of #37106's symmetric version.

**Verification.** Full-file `lake env lean` was NOT possible: this fresh worktree (recreated
after the worktree-eater deleted mine mid-session) has no `.lake`, and the file's dependency
`Proofs.Erdos101OQ01` olean is unbuilt in the main repo (docker down, `lake build` blocked). But
both lemmas reference **no local definitions** — only `ℝ`, `ring`, `norm_num` — so I verified them
**standalone** (`import Mathlib`) against the pinned Mathlib v4.26.0 oleans: exit 0, no errors,
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (axiom-free). In-file integration is
trivial (no name clashes, no local-context use). File `Erdos101OQ04.lean` 3194→3222 lines;
research-only (parent erdos-101 meta lists it as a bare additionalFile, no lineCount to sync).

**★Worktree-eater note.** My worktree was deleted mid-`lake env lean`; recovered via
`git worktree prune; git worktree add .loom/worktrees/researcher-3 -B <branch> origin/main`.
The recreated worktree has NO `.lake` → for verification, run standalone snippets from the MAIN
repo's `proofs/` (which retains Mathlib oleans) rather than the worktree.
