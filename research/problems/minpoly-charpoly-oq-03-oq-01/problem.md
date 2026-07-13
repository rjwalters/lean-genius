# minpoly-charpoly-oq-03-oq-01

## Open question

First sub-OQ of `minpoly-charpoly-oq-03` (rational canonical form):

> Formalize the F[X]-module structure on K^n via the M-action; show
> finitely generated + torsion (Cayley-Hamilton).

Estimated scope (per parent state.md): ~150 lines.

## Parent decomposition

The parent OQ-03 (PR #17888 S1 SCAFFOLD) decomposes the RCF existence proof
into four sub-OQs:

1. **OQ-03-OQ-01** (this sub-OQ) — F[X]-module structure + Module.Finite +
   Module.IsTorsion. ~150 lines.
2. OQ-03-OQ-02 — apply `Module.equiv_directSum_of_isTorsion` to get the
   invariant-factor decomposition with divisibility chain. ~300 lines.
3. OQ-03-OQ-03 — cyclic summand ↔ companion block correspondence. ~250 lines.
4. OQ-03-OQ-04 — global similarity assembly. ~200 lines.

## Strategy

Use Mathlib's existing `Module.AEval'` synonym (`Mathlib.Algebra.Polynomial.Module.AEval`):

```
xModule M := Module.AEval' (M.mulVecLin : (n → F) →ₗ[F] (n → F))
```

This gives F[X]-module action `p • v = (aeval M.mulVecLin p) v`.

* **Module.Finite F[X]**: automatic from Mathlib's `Module.AEval.instFinitePolynomial`
  (R-finiteness lifts to R[X]-finiteness). Provided by `inferInstance`.
* **Module.IsTorsion F[X]**: route through `Matrix.aeval_self_charpoly` +
  the standard-basis algebra equivalence `Matrix.toLin'` to get
  `aeval M.mulVecLin M.charpoly = 0` as a LinearMap, then upgrade
  `IsTorsionBy ... M.charpoly` to `IsTorsion` via `charpoly_monic ⇒ nonzero`.
