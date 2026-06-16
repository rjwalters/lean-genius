# chebyshev-bounds-oq-04-oq-01-oq-01 — Elementary PNT (Selberg–Erdős), Iter 5a-β-2

## Summary

Remove the axiom `chebyshevPsi_asymptotic` (ψ(n)/n → 1) from
`proofs/Proofs/ChebyshevBoundsOQ04.lean` by completing the elementary
Selberg–Erdős (1949) proof of the Prime Number Theorem.

## Grounded state of the chain (on `main`)

| File | sorries | axioms | role |
|------|---------|--------|------|
| `ChebyshevBoundsOQ04.lean` | 0 | **2** | ψ-bounds; carries `chebyshevPsi_asymptotic` (= PNT) and `pnt_equivalence` |
| `ChebyshevBoundsOQ04Aristotle.lean` | 0 | 0 | routine supporting lemmas |
| `ChebyshevBoundsOQ04OQ01.lean` | 0 | 0 | Selberg Λ₂ scaffold; **frozen at Iter 5a-β-1**, 18 theorems |

The two parent axioms are **deep** (not provable from Mathlib v4.26.0):
- `chebyshevPsi_asymptotic` IS the PNT for ψ; Mathlib core does not yet contain
  a full PNT (it lives in the separate PrimeNumberTheoremAnd project).
- `pnt_equivalence` (ψ~n ↔ π~n/log n) is the standard partial-summation
  equivalence — substantial but more tractable than the PNT itself.

`ChebyshevBoundsOQ04OQ01.lean` already proves Selberg's dual identity
`Σ_{d∣n} Λ₂(d) = (log n)²` and its Möbius-inverse form, plus routine Λ₂ lemmas
and the trivial Mertens bound `|M(N)| ≤ N`. Its documented next step is
**Iter 5a-β-2: the weak Mertens M₁ estimate** `|Σ_{d≤N} μ(d)/d| ≤ 1`.

## This session (2026-06-16, Researcher-8) — ORIENT, dual blackout

**Outcome**: progress (queued one verifiable target + persisted frontier).

Dual backend blackout: `docker run` hung (daemon down / 124), `proofs/.lake` is
a corrupt self-referential symlink (no local Mathlib oleans → builds infeasible),
and Aristotle `prove` returns 404. No verification possible this cycle.

### Keystone identified for Iter 5a-β-2

The cleanest entry point to the weak Mertens bound is the **Möbius–floor
identity** (integer-valued, fully elementary, reusable):

    Σ_{d=1}^{N} μ(d) · ⌊N/d⌋ = 1        (N ≥ 1)

From it, `|M₁(N)| ≤ 1` follows by writing `⌊N/d⌋ = N/d − {N/d}`:
`N·M₁(N) − Σ_{d≤N} μ(d){N/d} = 1`, and `|Σ μ(d){N/d}| ≤ N − 1`, so
`|N·M₁(N) − 1| ≤ N − 1`, giving `|M₁(N)| ≤ 1`.

**Why the floor identity is true (elementary):**
`⌊N/d⌋ = #{m ≥ 1 : d·m ≤ N}`, so the double sum reindexes (Fubini / hyperbola)
to `Σ_{n=1}^{N} Σ_{d∣n} μ(d) = Σ_{n=1}^{N} [n=1] = 1`, using `μ ∗ ζ = δ`.

### Queued artifact

`proofs/Proofs/ChebyshevBoundsOQ04OQ01OQ01WeakMertensStatementOnly.lean`
— single theorem `moebius_mul_floor_sum_eq_one` (integer form), unregistered
orphan (NOT in `Proofs.lean`, so CI-safe), ready for the batch pipeline /
Aristotle `prove` once a backend recovers. Expected glue:
`ArithmeticFunction.moebius`, `coe_moebius_mul_coe_zeta` (μ ∗ ζ = δ), and a
`Finset.Icc 1 N` hyperbola reindexing.

### Mathlib search to do on recovery (could not grep — `.lake` corrupt)

- Does Mathlib already have `Σ_{d≤N} μ(d)⌊N/d⌋ = 1`? Search
  `ArithmeticFunction.sum_moebius_mul`, `Nat.sum_div`, hyperbola lemmas.
- Möbius indicator: `ArithmeticFunction.sum_moebius_eq_...` /
  `coe_moebius_mul_coe_zeta` for `Σ_{d∣n} μ(d) = δ_{n,1}`.

### Next Steps

1. On backend recovery: submit
   `ChebyshevBoundsOQ04OQ01OQ01WeakMertensStatementOnly.lean` via Aristotle
   `prove` / batch; integrate.
2. Derive `|M₁(N)| ≤ 1` from the floor identity (fractional-part split).
3. Then Selberg's symmetry formula `S₂(N) = 2N·log N + O(N)` (Iter 5b), the
   Tauberian self-reference, and Erdős's combinatorial lemma (Iter 5c–5d).
4. Do NOT add new axioms; do NOT touch the frozen `ChebyshevBoundsOQ04OQ01.lean`.
