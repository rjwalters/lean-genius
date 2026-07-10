# Knowledge Base: bezout-identity-oq-01-oq-02-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-09 (Session 1) — Block reduction engine + n=2,3

**Mode**: FRESH · **Outcome**: progress (engine built, n=2,3 verified; general n open)

### What I did
- Built `embedOne` : general block embedding `SLₙ(ℤ) ↪ SL₍ₙ₊₁₎(ℤ)`, `M ↦ diag(1,M)`, in `proofs/Proofs/BezoutIdentityOQ01OQ02OQ02.lean` (namespace `BezoutIdentityOQ01OQ02OQ02`).
  - `det_embedOne` : `det(diag(1,M)) = det M` — `Matrix.det_succ_column_zero` (expand col 0, only top-left 1 survives), surviving minor `(embedOne M).submatrix Fin.succ Fin.succ` is definitionally `M` → close by `rfl`.
  - `embedOne_mulVec` : `diag(1,M) ·ᵥ (a ::ᵥ w) = a ::ᵥ (M ·ᵥ w)` — `funext` + `Fin.cases`, `simp [embedOne, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]`.
  - `embedOneSL` : packaged group map.
- `sl2_transitive` : base case, reuses grandparent `bezoutSL`.
- `sl3_transitive` : first new case, primitive `(a,b,c)` → `(1,0,0)` via `embedOne T` (tail reducer, identity when `gcd b c = 0`) then concrete `headBlock3` SL₂-in-SL₃ block; det via `det_mul`/`det_headBlock3`/`det_embedOne`.
- Gallery meta.json + problem knowledge updated. PR #36775.

### Key findings
- Transitivity is an **n ≥ 2** phenomenon: `SL₁(ℤ) = {1}` can't flip a sign.
- Two-step template: clear tail with `diag(1,M)` → `(v₀, gcd(tail), 0,…)`; then `gcd(v₀, gcd tail) = gcd(v) = 1` ⟹ one 2×2 Bézout step on coords {0,1} reaches `e₀`.
- Mathlib has `IsCoprime.exists_SL2_col` (n=2) but NO general-n transitivity, and no `fromBlocks`-into-`SpecialLinearGroup` helper.
- `![…]` is `Matrix.vecCons`; `rw` with `Fin.cons`-stated lemmas needs `rfl` conversions (`![a,b,c] = Fin.cons a ![b,c]`) to fire.
- `!!`-literal 3×3 det entries evaluate via `Matrix.det_fin_three` + `simp only [Matrix.of_apply, cons_val_zero, cons_val_one, cons_val_two, head_cons, tail_cons]` + `ring` (not `dsimp only [Matrix.cons_val]`).

### Next steps (general n)
1. SL₂-in-SL₍ₙ₊₁₎ head block for arbitrary `n`: block-diag(bezout, I₍ₙ₋₁₎) via `Matrix.fromBlocks` + `finSumFinEquiv` reindex; det via `det_fromBlocks_zero₂₁` + `det_submatrix_equiv_self`; mulVec via `submatrix_mulVec_equiv` + `fromBlocks_mulVec`.
2. `Finset.gcd` content bridge: `g = Finset.univ.gcd w` divides each `wᵢ` (`Finset.gcd_dvd`), `w = g • (w/g)`, and `w/g` primitive.
3. Induct on `n` with base `n=2` (grandparent) using 1+2.

### Files
- `proofs/Proofs/BezoutIdentityOQ01OQ02OQ02.lean` (192 lines, 11 thm, 3 def, 0 sorry/axiom)
- `src/data/proofs/bezout-identity-oq-01-oq-02-oq-02/meta.json`
