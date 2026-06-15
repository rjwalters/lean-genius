# Erdős #493 — OQ-01: Exact image and representation count of product-minus-sum

**Parent**: Erdős Problem #493 (`proofs/Proofs/Erdos493Problem.lean`), SOLVED.
Every `n ≥ 0` is `a*b - (a+b)` for some `a, b ≥ 2` (parent proves only
`n ≥ 0 ⟹ representable`, via the witness `a = 2, b = n + 2`).

**OQ-01 (this work)**: What is the *exact* image of `(a,b) ↦ a*b - (a+b)`
over `a, b ≥ 2`, and how many representations does each value admit?

## Central identity (the whole problem)

    a*b - (a + b) = (a - 1)*(b - 1) - 1.

Substituting `u = a - 1`, `v = b - 1` (so `a, b ≥ 2 ⟺ u, v ≥ 1`):

    n = a*b - (a + b)   ⟺   n + 1 = u * v   with u, v ≥ 1.

This is a bijection between representations of `n` and factorizations of `n+1`
into two positive factors. Everything follows.

## Results (all sympy-verified, `verify_prodminussum.py`, ALL CHECKS PASS)

- **(C1) Image** `{ a*b - (a+b) : a,b ≥ 2 } = { n : n ≥ 0 }`.
  The `⊇` direction is the parent theorem. The **converse** `representable ⟹ n ≥ 0`
  is NEW (parent leaves it open, even flags the imprecision in its Part III):
  from `u, v ≥ 1` we get `n + 1 = u*v ≥ 1`, so `n ≥ 0`. Every negative integer
  is unrepresentable.

- **(C2) Ordered count** `#{ (a,b) : a,b ≥ 2, a*b-(a+b)=n } = τ(n+1)`
  (number of positive divisors of `n+1`). Each divisor `u | n+1` gives
  `(a,b) = (u+1, (n+1)/u + 1)`. Cross-checked vs independent brute force.

- **(C3) Unordered count** `= #{ u | n+1 : u ≤ √(n+1) } = ⌈τ(n+1)/2⌉`.

- **(C4) Uniqueness**
  - Exactly one *ordered* rep `⟺ τ(n+1)=1 ⟺ n=0`.
  - Exactly one *unordered* rep `⟺ τ(n+1) ∈ {1,2} ⟺ n+1 is 1 or prime`.
    (A prime square `n+1 = p²` already has two unordered reps `{1,p²}, {p,p}` —
    a corrected guess; the verify-before-assert pass caught the wrong `{1,prime,p²}`
    prediction.)

## Lean status (Docker + Aristotle both DOWN this session — build-free only)

ACT-ready, Docker-gated (NOT committed as unbuildable `.lean`). The converse —
the new half of (C1) — is a few lines over `ℤ`:

```lean
theorem prodMinusSum2_iff_nonneg (n : ℤ) : Erdos493.HasProdMinusSum2 n ↔ n ≥ 0 := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    -- a*b-(a+b) = (a-1)*(b-1) - 1 ≥ 1*1 - 1 = 0
    have key : (a - 1) * (b - 1) ≥ 1 := by nlinarith [ha, hb]
    nlinarith [key]
  · intro hn; exact Erdos493.erdos_493_nonneg n hn
```

The counting formula (C2) needs the explicit bijection `Nat.divisors (n+1) ≃
{ representations }`; `τ = Nat.ArithmeticFunction.sigma 0` / `(n+1).divisors.card`
in Mathlib. Estimate ~120–180 LOC for the full counting theorem; the converse
(C1) alone is < 20 LOC. Build when Docker returns.

## Files
- `research/problems/erdos-493-oq-01/verify_prodminussum.py` — durable cert (C1–C4).

## Session log
### 2026-06-14 (Session 1) — FRESH ORIENT
- **Mode**: FRESH. **Outcome**: ORIENT + durable verification.
- Defined OQ-01 (parent had no stated follow-up, empty research dir).
- Found the `(a-1)(b-1)-1` bijection; proved the missing converse direction on
  paper + sympy; derived ordered/unordered counts and uniqueness characterization.
- Both proof backends down → shipped sympy cert, deferred Lean to ACT.
- **Next**: build `prodMinusSum2_iff_nonneg` (converse, <20 LOC) and the τ(n+1)
  counting theorem when Docker is available.
