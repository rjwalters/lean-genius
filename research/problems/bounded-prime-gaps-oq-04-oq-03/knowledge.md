# bounded-prime-gaps-oq-04-oq-03 — Knowledge

## Problem

Sub-question of `bounded-prime-gaps-oq-04` (Bombieri–Vinogradov formalizability).
The sibling catalog `BoundedPrimeGapsOQ04OQ02` records **Addition 1** — `gaussSumBound`,
the Gauss-sum bound `|τ(χ)| = √q` for a nontrivial Dirichlet character — as an *axiom*,
and asks in its own open-questions list:

> "Can gaussSumBound be proved using only Mathlib's existing ZMod.gaussSum
> infrastructure, or does it require new character sum API?"

This session answers that question.

## Result (SHIPPED, VERIFIED, 0-axiom)

`proofs/Proofs/BoundedPrimeGapsOQ04OQ03.lean` (135 lines, 6 theorems, 0 defs, 0 axioms, 0 sorries).

**Main theorem** `norm_gaussSum_eq_sqrt`: for a prime `p` and `χ : DirichletCharacter ℂ p`
with `χ ≠ 1`,
```
‖gaussSum χ ZMod.stdAddChar‖ = Real.sqrt p
```
`#print axioms` = `[propext, Classical.choice, Quot.sound]` only (no `sorryAx`, no
`Lean.ofReduceBool`).

Supporting: `conj_stdAddChar`, `conj_gaussSum`, `gaussSum_mul_conj` (τ·τ̄ = p),
`normSq_gaussSum`, and corollary `gaussSum_ne_zero`.

## Proof architecture

1. `conj_stdAddChar` — `stdAddChar a = ↑(toCircle a)` is unit-circle valued, so
   `conj(stdAddChar a) = (stdAddChar a)⁻¹ = stdAddChar(-a) = stdAddChar⁻¹ a`
   (`Circle.coe_inv_eq_conj`, `AddChar.map_neg_eq_inv`, `Circle.coe_inv`). Modulus-agnostic.
2. `conj_gaussSum` — termwise via `map_sum`, `map_mul`, `MulChar.star_apply'`
   (`conj(χ a) = χ⁻¹ a`) and (1). Modulus-agnostic.
3. `gaussSum_mul_conj` — `gaussSum_mul_gaussSum_eq_card hχ (isPrimitive_stdAddChar p)`
   gives `τ(χ)·gaussSum χ⁻¹ ψ⁻¹ = #(ZMod p)`; rewrite by (2) and `ZMod.card`.
4. `normSq_gaussSum` — `Complex.normSq_eq_conj_mul_self` + cast; then
   `norm_gaussSum_eq_sqrt` via `Complex.norm_def` (`‖z‖ = √(normSq z)`).

## The gap for composite modulus (KEY finding)

The **only** obstruction to the general primitive-character bound is the `[Field R]`
hypothesis of `gaussSum_mul_gaussSum_eq_card`. `ZMod q` is a field **iff q is prime**.
Steps 1–2 (conjugation) hold for all moduli; step 3 is where primality is forced.
So the composite case is *not* blocked by a missing conjugation/orthogonality lemma —
it needs the **theory of primitive Dirichlet characters** and the reduction of an
imprimitive Gauss sum to its primitive inductor, which Mathlib v4.26.0 lacks.

## Follow-ups

- Extend to composite modulus via primitive-inductor reduction (needs new Mathlib API).
- Bridge Mathlib's `gaussSum`/`stdAddChar` form to the OQ04-OQ02 axiom's literal
  `∑_{t∈range q} χ(t)·exp(2πit/q)` form (reindex via `toCircle_natCast`).
- Feed `gaussSum_ne_zero` / the √p bound into a prime-modulus Pólya–Vinogradov (Addition 2).

## Build notes

- Docker build broken (containerd `meta.db` I/O error) → compiled with
  `LAKE_UNSAFE=1 lake env lean` against prebuilt Mathlib; olean via `-o
  .lake/build/lib/lean/Proofs/…olean`, then `#print axioms` in a scratch importer.
- Main repo checkout was on another agent's branch → committed from durable
  `$HOME/lean-genius-r1-oq0403` worktree cut from `origin/main`.
