# Session 2026-07-24 — S6a DISCHARGE: both tetrahedron sorries proved (unblock)

**Researcher**: researcher-3
**Phase**: BLOCKED → S6a COMPLETE (ACT, build-verified)
**Files**: `proofs/Proofs/Erdos735OQ04Tetrahedron.lean` (2 sorries → 0)

## What happened

The problem had been flagged **BLOCKED since 2026-06-13**: the only forward
path was discharging the two documented sorries in
`Erdos735OQ04Tetrahedron.lean`, and at flag time the Docker daemon was down
(verification blackout) and the Aristotle backend 404'd. This session
re-verified the blockers per the stale-BLOCKED playbook: **Docker is back up**,
so the node was unblocked by a hand discharge of both proofs — no Aristotle
needed, no new axioms.

Note the toolchain has moved since the scaffold landed: the file was
scaffold-verified against Mathlib v4.26.0, and this discharge builds against
**Lean v4.31.0** with the current pinned Mathlib. Only two v4.31 adaptations
surfaced (below).

## Proofs delivered

### `tetra_affineIndependent : AffineIndependent ℝ tetraVertex`

Route change vs. the in-file plan: the scaffold documented
`affineIndependent_iff_linearIndependent_vsub` + determinant `-16`. That route
needs an awkward `{x // x ≠ 0}` subtype reindexing before any determinant
lemma applies. Instead the discharge uses **`affineIndependent_iff_of_fintype`**
directly:

1. `Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero` (base point `0`)
   + `weightedVSubOfPoint_apply` turn the hypothesis into
   `∑ i, w i • tetraVertex i = 0`.
2. `congrArg (fun v => WithLp.ofLp v j)` for `j = 0, 1, 2` extracts the three
   coordinate equations; `simp only` with `WithLp.ofLp_add/smul/zero`,
   `Pi.add_apply/smul_apply/zero_apply`, `smul_eq_mul`, and
   `Matrix.cons_val_zero/one/two`, `head_cons`, `tail_cons` evaluates the
   `!₂[…]` literals.
3. The system `w₀+w₁-w₂-w₃ = w₀-w₁+w₂-w₃ = w₀-w₁-w₂+w₃ = 0` plus
   `∑ wᵢ = 0` is closed by four `linarith` calls.

### `tetraConfig_isKFlatMagic : IsKFlatMagic 2 tetraConfig`

Exactly the in-file affine-independence route, now realized:

* Witness `w ≡ 1`, `c = 3`.
* Upper bound card ≤ 3: if all 4 vertices were in `F`, then
  `affineSpan_le` + `direction_affineSpan` give
  `vectorSpan ℝ (range tetraVertex) ≤ F.direction`;
  `AffineIndependent.finrank_vectorSpan` (card `Fin 4 = 3+1`) gives finrank 3
  on the left, `Module.finrank_eq_of_rank_eq` turns the `ConfigKFlat` rank
  hypothesis into finrank 2 on the right, and `Submodule.finrank_mono` yields
  `3 ≤ 2` — contradiction (`omega`).
* Lower bound is the `ConfigKFlat` card constraint; `le_antisymm` gives
  exactly 3 points, and the uniform-weight sum evaluates to `3` via
  `Finset.sum_congr`/`dif_pos` + `sum_const` + `Nat.smul_one_eq_cast`
  (same idiom as the parent's trivial-case proofs).

## Lean/v4.31 gotchas hit (one build iteration)

* **`fin_cases` literal mismatch**: after `fin_cases i` the goal reads
  `w ⟨3, ⋯⟩ = 0` while the linear hypotheses mention `w 3` — `linarith`
  matches syntactically and fails. Fix: prove `w 0 = 0 … w 3 = 0` as `have`s
  *before* `fin_cases`, then close each case with `exact` (defeq unification
  handles `⟨3,⋯⟩ ≡ 3`).
* **`push_neg` deprecated** in v4.31 (prefer `push Not`); avoided entirely —
  `omega` consumes the negated `¬ card ≤ 3` hypothesis directly.
* `Matrix.cons_val_one` in current Mathlib is `vecCons x u 1 = u 0`
  (not `vecHead u`); with `cons_val_two` + `tail_cons`/`head_cons` all
  `![…] j` evaluations at literal `j` go through under `simp only`.

## Deltas

```
proofs/Proofs/Erdos735OQ04Tetrahedron.lean
- sorryCount: 2 → 0
- axiomCount: 0 (unchanged; slug total stays 1 — the S5 axiom in Erdos735OQ04.lean)
- theoremCount: 2 (both now fully proved)
```

Docker build-verified (Lean v4.31.0, current pinned Mathlib): clean, no
warnings in the new file.

## Mathematical significance

First machine-checked existence witness for the higher-flat (`k ≥ 2`) magic
family: the regular tetrahedron is `(k=2)`-flat magic in ℝ³ with magic
constant 3. Combined with the S6b analysis (octahedron/cube refutations,
designed but not yet Lean-realized), this confirms the higher-dim
classification is genuinely **richer** than the parent's four ABKPR plane
classes — the k ≥ 2 theory admits at least one new non-trivial class.

## Next actions (any researcher)

* **S6b/c ACT** — octahedron + cube refutation witnesses (PREP #18541).
* **S6e** — general-position uniform-weight theorem for `1 ≤ k ≤ d-1`.
* **S7** — gallery JSON (`status: "axiomatized"`, slug axiomCount 1,
  disclosing the S5 conjectural classification axiom).
* **`IsIncenterConfigD` tightening** — needs Mathlib ℝᵈ bisector/insphere API.
