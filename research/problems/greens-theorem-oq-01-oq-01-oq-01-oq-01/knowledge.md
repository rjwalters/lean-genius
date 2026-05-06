# Knowledge Base: greens-theorem-oq-01-oq-01-oq-01-oq-01

**Problem**: Eliminate axiom `iteratedIntervalIntegral_order_independent` from parent proof
**Pool ID**: greens-theorem-oq-01-oq-01-oq-01-oq-01
**Status**: in-progress
**Phase**: ACT

## Summary

Prove that for continuous f on a compact n-dimensional box [a,b], any permutation σ
of the integration variables preserves the iterated interval integral:
```
  iteratedIntervalIntegral a b f
    = iteratedIntervalIntegral (a∘σ) (b∘σ) (fun x => f (x∘σ⁻¹))
```

The parent proof `greens-theorem-oq-01-oq-01-oq-01` axiomatizes this. This entry
proves the building blocks to eliminate that axiom.

---

## Session 2026-05-06 (Session 1) — Initial Formalization

**Mode**: FRESH
**Outcome**: progress

### What I Did

- Claimed the problem, branched `feature/researcher-6-schur2-proof` from origin/main
- Created `proofs/Proofs/GreensTheoremOQ01OQ01OQ01OQ01.lean` (333 lines, 3 sorries)
- Created gallery entry `src/data/proofs/greens-theorem-oq-01-oq-01-oq-01-oq-01/`
- Added entry to `src/data/proofs/listings.json`

### Key Findings

- **Core computation is pure Fin arithmetic**: `swap01_cons_eq` proves
  `f(cons x₁ (cons x₀ rest) ∘ swap 0 1) = f(cons x₀ (cons x₁ rest))` by
  case-splitting on Fin positions (0, 1, k+2). This is the mathematical heart.

- **Fubini via integral_integral_swap**: The swap_outer_two theorem uses exactly
  the same pattern as the 3D parent proof: expand, apply Fubini, contract.
  The G(x₀,x₁) = [remaining iterated integral] is the same on both sides.

- **Full 2D case proved**: order_independent_2d handles all σ ∈ Perm(Fin 2)
  by splitting on σ(0) ∈ {0, 1}.

- **Three sorrys remaining**:
  1. `integrable_swap_pair`: integrability of parameterized inner integral
  2. `iteratedIntervalIntegral_perm_tail`: inner permutation reduction
  3. Main theorem general case (induction + Equiv.Perm.induction_on')

### Files Modified

- `proofs/Proofs/GreensTheoremOQ01OQ01OQ01OQ01.lean` (new, 333 lines)
- `src/data/proofs/greens-theorem-oq-01-oq-01-oq-01-oq-01/` (new gallery entry)
- `src/data/proofs/listings.json` (entry added)

### Next Steps

1. **Resolve `integrable_swap_pair`**: Prove continuity of
   `fun p => iteratedIntervalIntegral ... (fun rest => f (Fin.cons p.1 (Fin.cons p.2 rest)))`
   by induction on n using `intervalIntegral.continuous_of_dominated`.
   Then apply `ContinuousOn.integrableOn_compact` on the compact Icc × Icc box.

2. **Resolve `iteratedIntervalIntegral_perm_tail`**: When σ(0) = 0:
   - `(a∘σ) 0 = a 0` so outer bound unchanged
   - Apply `intervalIntegral.integral_congr` to push σ inside
   - Apply IH to the inner (n-1)-dimensional integral
   - Key: σ restricted to Fin.tail is a valid permutation of Fin n

3. **Resolve main theorem**: Use `Equiv.Perm.induction_on'` (reduces to products of swaps)
   + compositionality: if holds for τ and for swap(i,j), holds for swap(i,j) ∘ τ.
   The swap(i,j) case: decompose into adjacent swaps using iterative swap_outer_two.

4. **Submit to Aristotle**: The `integrable_swap_pair` sorry is a candidate for
   Aristotle after resolving the proof outline (the integrability follows from
   continuity + compact domain via standard Mathlib infrastructure).


---

## Session 2026-05-06 (Session 2) — Prove perm_tail Building Block

**Mode**: REVISIT (in-progress problem)
**Outcome**: progress

### What I Did

- Proved `iteratedIntervalIntegral_perm_tail` using `Equiv.Perm.decomposeFin`
- Restructured `integrable_swap_pair` to use ContinuousOn.integrableOn_compact path
- Identified `continuous_of_dominated_interval` as the key Mathlib tool
- Pushed to PR #16248 branch (original PR was merged; new push creates continuation)

### Key Findings

- **decomposeFin decomposition**: `Equiv.Perm.decomposeFin σ = (σ 0, σ')` where σ'
  is the tail permutation. When σ 0 = 0: `decomposeFin_symm_apply_succ` gives
  `σ(i.succ) = swap 0 0 (σ' i).succ = (σ' i).succ`. This is the key computation.

- **Integrability path**: `Continuous G → ContinuousOn.integrableOn_compact (Icc×Icc) 
  → IntegrableOn (Ioc×Ioc) → Integrable w.r.t. (vol.restrict Ioc)×(vol.restrict Ioc)`
  via `Measure.prod_restrict`.

- **Remaining sorry for continuity**: Need `Continuous (fun p => iteratedIntervalIntegral
  ... (fun rest => f(cons p.1 (cons p.2 rest))))`. Fix: induction using
  `continuous_of_dominated_interval`, with bound = max of ‖f‖ on compact box.

- **Main theorem σ(0)≠0**: Write σ''=(swap 0 k)∘σ, then σ'' 0=0. Apply perm_tail
  to σ''. Need result for swap(0,k): k=1 by swap_outer_two, k>1 needs generalization.

### Files Modified

- `proofs/Proofs/GreensTheoremOQ01OQ01OQ01OQ01.lean` (341 lines, 2 sorries)
- `src/data/proofs/greens-theorem-oq-01-oq-01-oq-01-oq-01/meta.json` (sorries: 3→2)

### Next Steps

1. Prove continuity of G(p) using continuous_of_dominated_interval induction (1 sorry)
2. Prove main theorem case σ(0)≠0 using perm_tail + generalized swap(0,k) (1 sorry)
3. For swap(0,k): prove by induction on k using swap(0,k) = swap(k-1,k)∘swap(0,k-1)∘swap(k-1,k)
