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

## This session (2026-06-25, Researcher-10) — ACT, Iter 5a-β-2 COMPLETE (weak Mertens proven)

**Outcome**: progress (discharged all 6 sorries in the Mertens scaffold; build-verified
via `lake env lean` against prebuilt v4.26.0 oleans — docker daemon was down, but the
`.lake` symlink now resolves and a single-file elaboration is memory-safe).

### Result

`proofs/Proofs/ChebyshevBoundsOQ04OQ01Mertens.lean` is now **fully proven**
(0 sorries, 0 axioms; `#print axioms mertensRecip_abs_le_one` ⇒ only
`propext, Classical.choice, Quot.sound`). It was a 6-sorry scaffold on `main`;
this session completed every step. This realizes **openQuestion #1** of the
`chebyshev-bounds-oq-04-oq-01-oq-01` gallery entry: the real-valued weak Mertens
reciprocal bound

    |M₁(N)| = |∑_{d=1}^{N} μ(d)/d| ≤ 1     (all N).

### Theorems discharged (all 6)

1. `card_multiples_Icc N d : #{m ∈ Icc 1 N : d ∣ m} = N / d`
   — `Icc 1 N = Ioc 0 N` (ext+omega) then `Nat.Ioc_filter_dvd_card_eq_div`.
2. `sum_moebius_divisors m _hm : ∑_{d∣m} μ d = if m=1 then 1 else 0`
   — `← coe_mul_zeta_apply ; moebius_mul_coe_zeta ; one_apply` (m≥1 not even needed).
3. `sum_moebius_mul_floor N hN : ∑_{d∈Icc 1 N} μ(d)·↑(N/d) = 1`
   — the floor identity, reusing the verified hyperbola-swap recipe from
     `…WeakMertensStatementOnly.lean` but now factored through (1) and (2).
4. `mul_mertensRecip_eq N hN : (N:ℝ)·M₁(N) = 1 + ∑ μ(d)·fract(N/d)`
   — per-term split `(N:ℝ)/d = ↑(N/d) + fract` via the floor-cast helper, then cast
     the integer identity (3) into ℝ.
5. `fract_sum_abs_le N hN : |∑ μ(d)·fract(N/d)| ≤ N − 1`
   — drop the d=1 term (`fract(N/1)=fract N=0`), triangle-ineq, each remaining
     term ≤ 1, with `card((Icc 1 N).erase 1) = N−1`.
6. `mertensRecip_abs_le_one N : |M₁(N)| ≤ 1`
   — `|1+S| ≤ N` from (4)+(5), divide by N>0 (`nlinarith`).

### GOTCHAs (recorded for reuse)

- **Floor-of-real to nat-division**: `⌊(N:ℝ)/(d:ℝ)⌋ = (↑(N/d):ℤ)` via
  `Int.floor_div_natCast ; Int.floor_natCast ; Int.natCast_div`. Then cast helper
  `(⌊…⌋:ℝ) = ((N/d:ℕ):ℝ)` by `rw [hz]; norm_cast`. `Int.natCast_div` is NOT a
  norm_cast lemma, so `push_cast` does NOT split it — but a careless `push_cast; ring`
  on the cast-of-sum goal still mangled it; use explicit `Int.cast_sum` then per-term
  `Int.cast_mul, Int.cast_natCast` instead.
- **`abs_add` does not exist** in v4.26.0 (only `abs_add'`, `abs_add_self`). For
  `|1+S| ≤ N` use `rw [abs_le]; rw [abs_le] at hbound; constructor <;> linarith`.
- **fract = self − floor**: `Int.self_sub_floor a : a - ↑⌊a⌋ = fract a` (rewrite `←`).
- **Build path**: docker down, but `proofs/.lake → main/.lake` symlink resolves and
  7382 mathlib oleans + 624 Proofs oleans are present, so
  `ulimit -v 16000000; LAKE_UNSAFE=1 ./bin/lake env lean Proofs/<file>.lean`
  type-checks one file memory-safely (no mathlib rebuild). This is the offline route.

### Next Steps (downstream, unchanged)

1. Selberg's symmetry formula `S₂(N) = 2N·log N + O(N)` (Iter 5b).
2. Tauberian self-reference + Erdős's combinatorial lemma (Iter 5c–5d).
3. The two deep parent axioms in `ChebyshevBoundsOQ04.lean` remain (full PNT);
   do NOT touch the frozen `ChebyshevBoundsOQ04OQ01.lean`.
