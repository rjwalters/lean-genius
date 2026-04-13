# Problem: Cyclic Induction for ZMod n — Adapt Induction to Cyclic Structures

**Slug**: mathematical-induction-oq-03
**Created**: 2026-04-05T17:55:00-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall n \geq 1,\; \forall P : \mathbb{Z}/n\mathbb{Z} \to \text{Prop},\quad
P(0) \;\wedge\; \bigl(\forall k,\; P(k) \to P(k+1)\bigr) \;\implies\; \forall k,\; P(k)
$$

where $+1$ is addition in $\mathbb{Z}/n\mathbb{Z}$ (modular increment wrapping around at $n$).

### Plain Language

Standard mathematical induction works for natural numbers: prove P(0), prove P(n) → P(n+1), conclude ∀n, P(n). But ℤ/nℤ is a finite cyclic group — you can keep adding 1 and eventually wrap back to 0. Does an analogous "cyclic induction" principle hold?

Yes: to prove P(k) for all k : ZMod n, it suffices to prove:
1. P(0)  (base case)
2. ∀ k : ZMod n, P(k) → P(k + 1)  (step — the +1 wraps mod n automatically)

This holds because ZMod n has exactly n elements {0, 1, ..., n-1}, so any property that propagates along +1 starting from 0 covers all elements after at most n steps before wrapping.

### Why This Matters

- Formalizes a useful induction principle for ℤ/nℤ in Lean 4, filling a gap in the gallery's treatment of induction varieties.
- Shows the connection between structural induction (Nat.rec) and induction on finite types via the Fin ↔ ZMod bijection.
- Provides a reusable `ZMod.cyclicInduction` lemma for downstream modular arithmetic proofs.
- The gallery's mathematical-induction proof covers Nat induction; OQ-01 covers ordinal (transfinite) induction. OQ-03 completes the triad with finite cyclic induction.

## Known Results

### What's Already Proven

- `MathematicalInduction.induction_principle`: Standard weak induction for Nat
- `MathematicalInduction.strong_induction_principle`: Strong induction for Nat
- `MathematicalInductionOQ01`: Transfinite induction via well-founded recursion (ordinals)
- Mathlib `Fin.induction`: induction over `Fin n` (canonical finite induction principle)
- Mathlib `ZMod.val`: function ZMod n → ℕ giving representative in {0, ..., n-1}
- Mathlib `ZMod.natCast_val`: `(k.val : ZMod n) = k` for k : ZMod n (n ≥ 1)
- Mathlib `ZMod.val_natCast`: `(n : ZMod n).val = 0` (wrapping)
- Mathlib `ZMod.val_fin_lt`: `k.val < n` for k : ZMod n, n ≥ 1

### What's Still Open

- No `ZMod.cyclicInduction` lemma exists in Mathlib or the gallery.
- The proof of cyclic induction from Fin.induction via the ZMod ↔ Fin bijection is not formalized.

### Our Goal

1. Prove `ZMod.cyclicInduction`: P 0 ∧ (∀ k, P k → P (k+1)) → ∀ k : ZMod n, P k.
2. Apply to an example: prove a non-trivial ZMod n property using cyclic induction.
3. Formalize in `MathematicalInductionOQ03.lean`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `mathematical-induction` | Parent proof; base induction infrastructure | `Nat.rec`, `Nat.strong_induction_on` |
| `mathematical-induction-oq-01` | Transfinite induction (WellFounded) | `WellFounded.recursion`, ordinal cases |
| `bezout-identity-oq-03` | Uses ZMod arithmetic extensively | `ZMod.Basic`, coset representatives |
| `euler-totient-oq-02` | ZMod group structure | `ZMod.Basic`, `ZMod.Quotient` |

## Initial Thoughts

### Potential Approaches

1. **Fin-lifting approach** (most direct):
   - Restate as: ∀ i : Fin n, P (i.val : ZMod n)
   - Apply `Fin.induction`: base P (0 : ZMod n), step from i to i+1
   - Use `ZMod.natCast_val` to link `(k.val : ZMod n) = k`
   - Wrap-around case (i = Fin.last n-1): `((n : ℕ) : ZMod n) = 0 = ZMod.natCast_self`
   - Risk: casting ZMod ↔ Fin requires `[NeZero n]` and careful type coercions

2. **Fintype.induction approach**:
   - ZMod n is a Fintype; use induction on Finset.univ
   - Less direct but avoids manual Fin lifting
   - Risk: step structure doesn't naturally match "+1" order

3. **orderOf/zpow approach**:
   - In ZMod n, 1 generates the group with `orderOf 1 = n`
   - More algebraic; shows this is group-theoretic induction
   - Risk: heavier algebraic machinery

### Key Difficulties

- The wrap-around case: Fin.induction terminates at `Fin.last`, but ZMod wraps so the step at n-1 must give 0.
- Getting from k : ZMod n to a Fin n representative requires `[NeZero n]`.
- Reconstructing k = (k.val : ZMod n) via `ZMod.natCast_val` has a side condition n ≠ 0.

### What Would a Proof Need?

- `ZMod.natCast_val` : `(k.val : ZMod n) = k` (for [NeZero n])
- `Fin.induction` : base + step over all Fin n elements
- `ZMod.natCast_self` : `(n : ZMod n) = 0` (for the wrap-around step)
- `Fin.val_last` : `(Fin.last n).val = n` (for casting the last element)

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- Mathlib has `Fin.induction` and the full ZMod ↔ Fin bijection infrastructure
- The mathematical content is elementary: ZMod n has exactly n elements enumerable by +1
- Proof should be ~20-50 lines using existing Mathlib lemmas
- No new mathematics required — purely a formalization exercise

**Estimated Effort**:
- Exploration: 1-2 hours (reading Fin.induction signature and ZMod casting lemmas)
- If tractable: 2-4 hours (write theorem + example application)
- If casting issues arise: 4-8 hours debugging type coercions between ZMod and Fin

## References

### Mathlib
- `Mathlib.Data.ZMod.Basic` — ZMod n, ZMod.val, ZMod.natCast_val, ZMod.natCast_self
- `Mathlib.Data.Fin.Basic` — Fin.induction, Fin.val_fin_lt, Fin.last
- `Mathlib.Data.Fintype.Basic` — Fintype instance for ZMod n
- `Mathlib.GroupTheory.OrderOfElement` — orderOf for cyclic group perspective

### Gallery
- `proofs/Proofs/MathematicalInduction.lean` — parent proof
- `proofs/Proofs/MathematicalInductionOQ01.lean` — transfinite induction (OQ-01)

## Metadata

```yaml
tags:
  - foundations
  - induction
  - modular-arithmetic
  - ZMod
  - cyclic-groups
  - finite-types
related_proofs:
  - mathematical-induction
  - mathematical-induction-oq-01
  - euler-totient-oq-02
difficulty: low-medium
source: gallery-gap
created: 2026-04-05T17:55:00-07:00
```
