# Knowledge Base: cauchy-schwarz-integral-oq-04

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

## RESOLVED — full Robertson relation (researcher-2, 2026-07-08)

The prior state had only the **Cauchy-Schwarz core** (`abs_im_inner_le_norm_mul_norm`,
`im_inner_sq_le`), deferring the operator statement. This session formalizes the full
**Robertson uncertainty relation** in `CauchySchwarzIntegralOQ04.lean` (VERIFIED, 0
axioms, 0 sorries, no `native_decide`):

- `inner_commutator_eq_sub (hA hB : IsSymmetric) (ψ) (a b : ℝ)`:
  `⟪ψ, (AB−BA)ψ⟫ = ⟪u,v⟫ − ⟪v,u⟫`  where `u=(A−a)ψ`, `v=(B−b)ψ`. The shifts `a,b` cancel.
- `robertson_uncertainty (hA hB : IsSymmetric) (ψ) (a b : ℝ)`:
  `¼·‖⟪ψ,(AB−BA)ψ⟫‖² ≤ ‖(A−a)ψ‖²·‖(B−b)ψ‖²`.

Setting `a=⟪ψ,Aψ⟫`, `b=⟪ψ,Bψ⟫` makes the RHS `Var(A)·Var(B)`, i.e. Heisenberg's
`Δx·Δp ≥ ℏ/2` with `[x,p]=iℏ`. Valid over any `RCLike` field (ℝ trivial, ℂ the content).

### Proof chain
1. `inner_commutator_eq_sub`: expand both inner products (`inner_sub_left/right`,
   `inner_smul_left/right`, `RCLike.conj_ofReal`), rewrite `⟪Aψ,ψ⟫=⟪ψ,Aψ⟫` etc. via
   symmetry, `ring`. Shift terms cancel.
2. `⟪v,u⟫ = conj⟪u,v⟫` (`inner_conj_symm`), so commutator `= ⟪u,v⟫−conj⟪u,v⟫
   = 2·i·Im⟪u,v⟫` (`RCLike.sub_conj`); norm `≤ 2|Im⟪u,v⟫|` using `‖I‖≤1`.
3. Square and apply the existing `im_inner_sq_le`.
