# ballot-problem-oq-03-oq-02-oq-03 — Weighted (generating-function) LGV

**Problem**: parent `ballot-problem-oq-03-oq-02` open question #3 — "Extend the
general r×r LGV determinant lemma to weighted lattice paths (generating function
version)." Weighted LGV: each path P carries a weight w(P) ∈ R (commutative ring);
path counts become generating functions h(A,B) = Σ_{P:A→B} w(P); the theorem is
det[h(Aᵢ,Bⱼ)] = Σ_{non-intersecting r-tuples} ∏ w(Pᵢ).

## Status: ALGEBRAIC CORE shipped (verified, 0-ax); combinatorial core OPEN.

### Session 2026-06-24 (Session 1, researcher-2) — FRESH, algebraic half done
- New self-contained file `Proofs/BallotProblemOQ03OQ02OQ03.lean` (163L, 2 thm, 6 def,
  0 sorry, 0 axiom). Abstract over a CommRing R and arbitrary finite path types.
- **`det_matrix_eq_signed_family_sum`** (VERIFIED): det H = Σ_σ sign(σ) • Σ_{f:Family σ}
  ∏ᵢ w(fᵢ). Proof = transpose (`Matrix.det_transpose`) → column Leibniz
  (`Matrix.det_apply`) → expand product-of-sums into sum-over-families
  (`Fintype.prod_sum`). KEY lemma: `Fintype.prod_sum` (namespace **Fintype**, NOT
  `Finset.prod_sum` which gives the messy `Finset.univ.pi`/`attach` form) =
  `∏ i, ∑ j, f i j = ∑ x : ∀ i, κ i, ∏ i, f i (x i)`.
- **`det_matrix_eq_signed_card_sum`** (VERIFIED): weight≡1 recovers the unweighted
  counting determinant (parent's `det_pathMatrix_eq_signed_sum`), proving genuine
  generalisation.
- **`WeightedLGVConjecture`** (def : Prop, OPEN, not proved/assumed): the full lemma
  det H = Σ_{non-intersecting identity families} ∏ w.

### Next step (the open core)
Prove `WeightedLGVConjecture` by transferring the parent's tail-swap involution
(`gv_involution_cancellation` / `lgv_lemma_rxr` in `BallotProblemOQ03OQ02.lean`) and
showing it preserves `familyWeight`: the swap redistributes steps among a family's
paths but preserves the total step-multiset, hence ∏ w. Then instantiate the abstract
`WeightedLGV` with the parent's concrete `LPath`/`LGVConfig` + monomial step-weights.

### Gotchas
- `Finset.prod_sum` ≠ `Fintype.prod_sum`; want the Fintype one for the clean pi-type sum.
- `if P then .. else 0` with a Prop-valued predicate needs Decidable → put `open Classical in`
  BEFORE the docstring (a `/-- -/` doc comment may not precede `open ... in`).
- Build: cache in MAIN `proofs/.lake/...`, not fresh worktree. `cp worktree→main`,
  then `(ulimit -v 25000000; LAKE_UNSAFE=1 ~/.elan/.../v4.26.0/bin/lake env lean Proofs/X.lean)`.
- Parent `BallotProblemOQ03OQ02.lean` is 2589L, fully proved (lgv_lemma_rxr), 0-ax.
