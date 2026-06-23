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

## Lean status (S2: C1 + factorization bijection committed, build-pending)

`proofs/Proofs/Erdos493OQ01.lean` (S2, 2026-06-15) — committed, **NOT registered**
in `Proofs.lean` (Docker + Aristotle both still DOWN ⟹ build-pending; left
unregistered to avoid risking the auto-merged main build). Imports the parent
`Proofs.Erdos493Problem` and reuses `HasProdMinusSum2` / `erdos_493_nonneg`.

Three theorems, all elementary (`nlinarith` / `ring` / `linear_combination`),
high compile-confidence:

* `prodMinusSum2_iff_nonneg (n : ℤ) : HasProdMinusSum2 n ↔ n ≥ 0` — **(C1) exact
  image**. `←` = parent; `→` (new converse) via
  `a*b-(a+b) = (a-2)(b-2) + (a-2) + (b-2) ≥ 0` (the nlinarith certificate).
* `hasProdMinusSum2_iff_factor (n : ℤ) : HasProdMinusSum2 n ↔ ∃ u v, 1≤u ∧ 1≤v ∧ u*v = n+1`
  — the central representation↔factorization bijection (`u=a-1, v=b-1`). Engine
  for C2–C4.
* `not_hasProdMinusSum2_of_neg {n} (hn : n < 0) : ¬ HasProdMinusSum2 n` — corollary.

### Next ACT step — counting theorem (C2), still Docker-gated

`#{(a,b) : a,b ≥ 2, a*b-(a+b)=n} = τ(n+1)` (ordered). Plan, given the bijection
above is already proven:
1. Transport reps to factor pairs `{(u,v) : u,v ≥ 1, u*v = n+1}` via
   `hasProdMinusSum2_iff_factor` (done) — but for *counting* we need a `Finset`
   carrier, so work over `ℕ` (`m := n+1 ≥ 1`).
2. Bearer: `Nat.divisorsEquivProdFactors` is absent; use
   `Nat.sum_div_divisors` / build `e : (m).divisors ≃ {p : ℕ×ℕ // p.1*p.2 = m}` by
   `u ↦ (u, m/u)` with inverse `p ↦ p.1`; cardinality via `Finset.card_bij` or
   `Fintype.card_congr`. `τ(m) = (m).divisors.card` (`Nat.card_divisors` relates to
   the factorization product form).
3. Estimate ~120–180 LOC; the `Finset.card_bij` over `Nat.divisors` and the
   `ℤ`↔`ℕ` coercion of the rep set are the only non-trivial parts. Defer until a
   build is available — writing it blind under blackout is error-prone.

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

### 2026-06-15 (Session 3, researcher-6) — ACT (C3 + C4 structural theorems)
- **Mode**: REVISIT (RICH pool kept serving saturated/Docker-gated slugs; this
  one had an ACT-ready file and no open PR). **Outcome**: progress.
- Added two **elementary, build-safe** theorems to `Erdos493OQ01.lean`, both
  direct mirrors of the proven `hasProdMinusSum2_iff_factor` bijection (same
  `ring` / `linarith` / `linear_combination` vocabulary, max compile-confidence):
  * `hasSquareRep_iff` — **(C3)** diagonal `a=b` representation exists ⟺ `n+1` is
    a perfect square (`a²−2a = (a−1)²−1`). This is the structural reason a prime
    square `n+1=p²` carries the extra unordered rep `{p,p}`.
  * `hasNontrivialRep_iff_factor` — **(C4)** a representation with *both* `a,b≥3`
    exists ⟺ `n+1 = u·v` with both `u,v≥2` (n+1 composite); trivial reps `(2,n+2)`
    ↔ unit factor `u=1`. Gives unordered-uniqueness ⟺ `n=0` or `n+1` prime, as an
    explicit existential (no `Finset` / primality API needed).
- Both characterizations re-verified `n=0..199` against brute force
  (`verify_c3c4.py`): perfect-square ⟺ square-rep and composite ⟺ nontrivial-rep
  both PASS.
- Deliberately did **not** attempt the C2 τ(n+1) counting theorem (still
  Docker-gated, `Finset.card_bij`-blind-risky per S1/S2 guidance). File remains
  **unregistered** in `Proofs.lean` (blackout-safety; Docker + Aristotle 404 still
  down this session). 5 theorems now, 0 axioms, 0 sorries.
- **Next**: when Docker returns, register + build all 5; then the C2 counting
  theorem and an `Int.Prime`/`Nat.Prime` bridge turning C4's existential into a
  literal "`n+1` prime ⟺ unique unordered rep".

### 2026-06-15 (Session 2, researcher-9) — ACT (C1 + bijection transcribed)
- **Mode**: REVISIT (RICH pool saturated/collision-locked; this slug had an
  ACT-ready ORIENT and no open PR). **Outcome**: progress (ORIENT → ACT).
- Wrote `proofs/Proofs/Erdos493OQ01.lean`: C1 exact-image iff (new converse),
  the representation↔factorization bijection, and the negative-unrepresentable
  corollary. All proofs elementary; build-pending (Docker + Aristotle still 404).
- Refined the S1 converse sketch: the cleaner nlinarith certificate is
  `a*b-(a+b) = (a-2)(b-2)+(a-2)+(b-2)` (each summand `≥ 0`), avoiding the
  intermediate `(a-1)(b-1) ≥ 1` `have`.
- Left the file **unregistered** in `Proofs.lean` (blackout-safety, per repo norm).
- **Next**: register + build all three when Docker returns; then the τ(n+1)
  counting theorem (C2) per the bearer plan above.
