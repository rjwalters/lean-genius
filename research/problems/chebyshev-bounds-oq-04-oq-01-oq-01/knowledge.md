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

## This session (2026-06-16, Researcher-5) — Mathlib searches RESOLVED

Dual blackout persists (`.lake` literal self-symlink → builds re-clone Mathlib;
Aristotle `prove` → 404). But the `/private/tmp/mathlib-grep` v4.26.0 mirror was
readable, so I resolved every "search to do on recovery" the prior session left.

**No, Mathlib does NOT have `Σ_{d≤N} μ(d)⌊N/d⌋ = 1` directly** (only
`sum_moebius_mul_log_eq` in VonMangoldt.lean). But all four building blocks exist:

| # | Lemma | Location | Role |
|---|-------|----------|------|
| 1 | `Nat.Ioc_filter_dvd_card_eq_div (n p) : #{x∈Ioc 0 n \| p∣x} = n/p` | `Data/Nat/Factorization/Basic.lean:475` | ⌊N/d⌋ = #multiples |
| 2 | `coe_mul_zeta_apply : (f*ζ) x = ∑ i∈x.divisors, f i` | `NumberTheory/ArithmeticFunction/Zeta.lean:81` | divisor sum ← (μ*ζ) x |
| 3 | `moebius_mul_coe_zeta : (μ*ζ : ArithmeticFunction ℤ) = 1` | `…/Moebius.lean:157` | μ∗ζ = δ |
| 4 | `one_apply : (1:ArithmeticFunction R) x = ite (x=1) 1 0` | `…/Defs.lean:96` | δ as if-then-else |

**Full grounded proof chain** (now embedded as a paste-ready attempt in the
orphan file's docstring, kept behind `sorry` since BUILD-UNVERIFIED):

```
Σ_{d∈Icc 1 N} μ d·(N/d)
 = Σ_{d∈Icc 1 N} Σ_{x∈Ioc 0 N, d∣x} μ d     [1: sum_const + Ioc_filter_dvd_card_eq_div + nsmul_eq_mul]
 = Σ_{x∈Ioc 0 N} Σ_{d∈Icc 1 N, d∣x} μ d     [Finset.sum_filter then Finset.sum_comm]
 = Σ_{x∈Ioc 0 N} Σ_{d∈x.divisors} μ d        [for x≤N: {d∈Icc 1 N : d∣x} = x.divisors]
 = Σ_{x∈Ioc 0 N} (μ*ζ) x                       [2: coe_mul_zeta_apply]
 = Σ_{x∈Ioc 0 N} ite(x=1) 1 0                  [3+4: moebius_mul_coe_zeta, one_apply]
 = 1                                            [Finset.sum_ite_eq'; 1∈Ioc 0 N as N≥1]
```

**Residual compile risks** (what the next build slot must check): the
`Finset.sum_comm` order swap producing the exact double-sum shape; the
`filter = divisors` `ext` (binder order, `Nat.pos_of_dvd_of_pos`); and the
`show … from coe_mul_zeta_apply.symm` typeclass elaboration (`μ` as
`ArithmeticFunction ℤ`). The mathematics is fully grounded; only Lean
bookkeeping remains.

### Next Steps

1. On backend recovery: submit
   `ChebyshevBoundsOQ04OQ01OQ01WeakMertensStatementOnly.lean` via Aristotle
   `prove` / batch; integrate.
2. Derive `|M₁(N)| ≤ 1` from the floor identity (fractional-part split).
3. Then Selberg's symmetry formula `S₂(N) = 2N·log N + O(N)` (Iter 5b), the
   Tauberian self-reference, and Erdős's combinatorial lemma (Iter 5c–5d).
4. Do NOT add new axioms; do NOT touch the frozen `ChebyshevBoundsOQ04OQ01.lean`.

## This session (2026-06-16, Researcher-3) — ACT, Iter 5a-β-2 keystone PROVEN

**Outcome**: progress (discharged the queued sorry; build-verified).

Aristotle MCP loaded this session but `prove` still returns "Resource not
found" (backend down) — proved manually instead.

### Result

`moebius_mul_floor_sum_eq_one` in
`proofs/Proofs/ChebyshevBoundsOQ04OQ01OQ01WeakMertensStatementOnly.lean` is now
**fully proven** (0 sorries, 0 axioms), build-verified `✔ [7743/7743]` (97s)
and registered in `Proofs.lean`.

Statement: `∑ d ∈ Finset.Icc 1 N, μ d * ↑(N / d) = 1` for `N ≥ 1`.

### Proof recipe (elementary hyperbola swap)

1. `Finset.Icc 1 N = Finset.Ioc 0 N` (ext + omega) to match the counting lemma.
2. `⌊N/d⌋ = #{k ∈ Icc 1 N : d ∣ k}` via `Nat.Ioc_filter_dvd_card_eq_div`.
3. Rewrite each term `μ d * ↑(N/d)` as `∑ k ∈ Icc 1 N, (if d ∣ k then μ d else 0)`
   (`Finset.sum_ite` + `sum_const_zero` + `sum_const` + `nsmul_eq_mul`).
4. Swap the double sum with the basic `Finset.sum_comm` (both indices over
   `Icc 1 N`; avoids the fiddlier `sum_comm'`).
5. Collapse the inner guarded sum to `∑ d ∈ k.divisors, μ d` (filter = divisors
   for `1 ≤ k ≤ N`, via `Nat.mem_divisors` + `Nat.le_of_dvd`).
6. `∑ d ∈ k.divisors, μ d = if k = 1 then 1 else 0` via
   `ArithmeticFunction.coe_mul_zeta_apply` + `moebius_mul_coe_zeta` (μ ∗ ζ = 1)
   + `one_apply`.
7. `Finset.sum_ite_eq'` picks out the `k = 1` term ⇒ `1`.

### GOTCHA (recorded for reuse)

The `μ` notation is `scoped[ArithmeticFunction.Moebius]` — `open ArithmeticFunction`
is NOT enough; you must add `open scoped ArithmeticFunction.Moebius`. First build
failed with `Unknown identifier μ`. (`ζ` is `scoped[ArithmeticFunction.zeta]`,
not needed here since we only reference it through lemma names.)

### Next Steps (unchanged downstream)

1. Derive `|M₁(N)| = |∑_{d≤N} μ(d)/d| ≤ 1` from this floor identity via the
   fractional-part split `⌊N/d⌋ = N/d − {N/d}`.
2. Then Selberg's symmetry formula (Iter 5b), the Tauberian self-reference,
   Erdős's combinatorial lemma (Iter 5c–5d).
3. The two parent axioms in `ChebyshevBoundsOQ04.lean` remain (deep PNT);
   do NOT touch the frozen `ChebyshevBoundsOQ04OQ01.lean`.
