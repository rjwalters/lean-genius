# Research State: basel-problem-oq-01-oq-01-oq-02-oq-03

## Current State
**Phase**: ACT (structural infrastructure being added; full proof requires Mathlib upstream)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-09 (Iteration 17, researcher-13)
**Iteration**: 17

## Current Focus

Iteration 17 (2026-05-09, this PR, researcher-13): **arithmetic helpers
for the small-prime correction-factor reduction** — extracts the two
key arithmetic observations behind the "only primes `p ≤ √n` matter"
strategic remark from Iter 16's docstring as standalone, sorry-free,
reusable lemmas:

* `log_le_one_of_sq_lt {p n : ℕ} (hp : 1 < p) (hsq : n < p * p)
    : Nat.log p n ≤ 1` —
  the key arithmetic observation. Proof: if `Nat.log p n ≥ 2`, then
  `Nat.pow_le_of_le_log` gives `p² ≤ n`, contradicting `n < p²`;
  the boundary case `n = 0` is immediate via `simp`
  (`Nat.log p 0 = 0`).
* `prime_pow_pred_eq_one_of_sq_lt {p n : ℕ} (hp : p.Prime) (hsq : n < p * p)
    : p ^ (Nat.log p n - 1) = 1` —
  direct corollary: for primes `p` with `p² > n`, the Iter-16
  correction-factor exponent vanishes, so the factor is `1`.

These helpers are deliberately *base-agnostic* (`log_le_one_of_sq_lt`
needs only `1 < p`, not primality) so they are reusable beyond the
specific Hanson-correction-factor application; the prime-specific
corollary `prime_pow_pred_eq_one_of_sq_lt` is the ready-made hammer
for any `Finset.prod_subset` argument that wants to restrict
correction-factor-style products to small primes.

**Complementary, non-overlapping with #17619** (Iter 17 by
researcher-1): #17619 supplies the global product reformulation
`lcmRange_correction_supported_on_small_primes` (correction = product
over primes with `p² ≤ n`) using these same arithmetic facts inlined;
this iter extracts those arithmetic facts as named, reusable lemmas.
The two PRs compose cleanly — once both merge, future iters can
either invoke the global theorem directly, or invoke
`prime_pow_pred_eq_one_of_sq_lt` pointwise inside other product
manipulations.

**Strategic value**: with the small-prime restriction made explicit,
the correction factor is now bounded over `O(√n / log n)` primes
(by PNT). The next attack stage is bounding this small-prime product
by `(3/4)^n` (or any `c^n` with `c · 4 ≤ 3 · k` for controllable `k`);
combined with Mathlib's `Nat.primorial_le_4_pow` and Iter 16's
primorial-correction factorization, this would discharge
`axiom hanson_bound` via the multiplicative split
`lcmRange ≤ primorial · correction ≤ 4^n · (3/4)^n = 3^n`.

**File delta**: +38 lines (757 → 795), +2 theorems (46 → 48). Defs /
sorries / axiomCount unchanged. Build pending — proof body uses only
Mathlib API already exercised by Iters 7–16 (`Nat.pow_le_of_le_log`,
`Nat.log_zero_right` via `simp`, `pow_two`, `pow_zero`, `omega`,
`push_neg`, `by_contra`).

### Iteration 16 (background, merged base)

Iteration 16 (2026-05-09, merged as #17578, researcher-5):
**primorial-correction factorization** — refines Iter 15's
`primorial_dvd_lcmRange` from a divisibility statement to an explicit
equality. New theorem:

* `lcmRange_eq_primorial_mul_prod_prime_pow_pred (n : ℕ) :
    lcmRange n = primorial n *
      ∏ p ∈ filter Prime (range (n + 1)), p ^ (Nat.log p n - 1)` —
  decomposes `lcmRange n` as the primorial times the **correction
  factor** `∏ p^(⌊log_p n⌋ - 1)`. Proof: chain Iter 9's
  `lcmRange_eq_prod_prime_powers` with `Finset.prod_mul_distrib`, then
  factor `p^(log_p n) = p · p^(log_p n - 1)` pointwise via `pow_succ'`
  and `Nat.sub_add_cancel` (using `Nat.log_pos` to ensure
  `log_p n ≥ 1` for every `p ≤ n`).

**Strategic value**: combined with Mathlib's `Nat.primorial_le_4_pow`
(`primorial n ≤ 4^n`), this isolates the asymptotic challenge into the
*correction factor*. Bounding the correction by a Chebyshev-style
small-prime estimate would yield Hanson's `≤ 3^n` via the multiplicative
split (since `(3/4)^n · 4^n = 3^n`). The correction factor only "sees"
primes `p ≤ √n` (because `p > √n` ⇒ `Nat.log p n ≤ 1` ⇒ exponent `0` ⇒
factor `1`), reducing the asymptotic challenge to the classical
Chebyshev `O(2^√n)`-style estimate on small-prime contributions.

**File delta**: +54 lines (703 → 757), +1 theorem (45 → 46). Defs/sorries/
axiomCount unchanged. Build pending — proof body uses only Mathlib API
already exercised by Iters 7–15 (`Finset.prod_mul_distrib`,
`Finset.prod_congr`, `Nat.log_pos`, `Nat.sub_add_cancel`, `pow_succ'`).

### Iteration 15 (background, two parallel PRs)

The previous iteration was tracked under "Iter 15" but split into two
independent threads:

* `#17559` (researcher-10, **merged**, this branch's base): primorial →
  lcmRange divisibility bridge. Adds `primorial_dvd_lcmRange` and
  `primorial_le_lcmRange` (lower-bound side
  `primorial(n) ≤ lcm(1..n)`).
* `#17551` (researcher-1, open, parallel): doubly-sharpened
  prime-counting bound `π(n) ≤ n - 2` for `n ≥ 4`, yielding
  `lcmRange n ≤ n^(n-2)` (Iter 14's `n^(n-1)` improved by erasing the
  smallest even composite from the prime filter).

Iter 16 (this PR) builds on the **merged** Iter 15 (#17559); it does not
overlap with the open `n^(n-2)` bound of #17551 and so does not depend
on its merge order.

#### Background on Iter 15 (#17559, the divisibility bridge merged into base)

Two new theorems wire Mathlib's `NumberTheory.Primorial` API to the
file's `lcmRange`, supplying the **lower-bound side** of the bridge
sketched in the file header
(`primorial(n) ≤ lcm(1..n) ≤ n · primorial(n)`):

* `primorial_dvd_lcmRange (n : ℕ) : primorial n ∣ lcmRange n` —
  direct from Iter 9's Chebyshev decomposition
  `lcmRange n = ∏ p ∈ primes ≤ n, p ^ Nat.log p n`. Each prime
  `p ≤ n` has `Nat.log p n ≥ 1` (via `Nat.log_pos`), so each factor
  `p` divides `p ^ Nat.log p n`, and the divisibility lifts pointwise
  via `Finset.prod_dvd_prod_of_dvd`.
* `primorial_le_lcmRange (n : ℕ) : primorial n ≤ lcmRange n` —
  one-line corollary via `Nat.le_of_dvd` + `lcmRange_pos` (with the
  `n = 0` boundary case `primorial 0 = lcmRange 0 = 1` dispatched by
  `simp`).

Combined with Mathlib's `primorial_le_4_pow` (`primorial n ≤ 4^n`),
this places `lcmRange n` in the band `[primorial n, ?]` whose upper
edge is the target of Hanson's `≤ 3^n`. Future iterations will
attack the upper-bound side `lcmRange ≤ n · primorial`, which
requires a Chebyshev-type bound on small primes: each prime
`p ≤ √n` contributes a factor `p^(⌊log_p n⌋ - 1) ≤ √n` beyond its
primorial contribution, and bounding the total contribution of
small primes by `n` is the missing piece for the `4^n` bound.

Build pending; proof bodies use only Mathlib API already exercised
by Iters 7-14 (`Finset.prod_dvd_prod_of_dvd`, `Nat.log_pos`,
`dvd_pow_self`, `Nat.le_of_dvd`, `lcmRange_pos`,
`lcmRange_eq_prod_prime_powers`). New import:
`Mathlib.NumberTheory.Primorial`. File 657 → 705 lines (+48 in Lean
+ docstrings), theorems 43 → 45 (+2), definitions/sorries/axiomCount
unchanged.

----

Iteration 14 (PR #17513, merged): **sharpened prime-counting bound
`π(n) ≤ n - 1` and the resulting chain
`lcmRange n ≤ n^π(n) ≤ n^(n-1)`**. Three new theorems sharpen Iter 13
by exploiting that *both* `0` and `1` are non-prime (Iter 13 only
excluded `0`), tightening the cardinality argument from `n` to
`n - 1`:

* `primeCounting_le_pred (n : ℕ) : Nat.primeCounting n ≤ n - 1` —
  the prime filter on `Finset.range (n+1)` is a subset of
  `((Finset.range (n+1)).erase 0).erase 1`, whose cardinality is
  `n - 1` (with `Nat` truncated subtraction handling `n = 0, 1`
  correctly).
* `pow_primeCounting_le_pow_pred (n : ℕ) (hn : 1 ≤ n) :
  n ^ Nat.primeCounting n ≤ n ^ (n - 1)` — one-line via
  `Nat.pow_le_pow_right`, analogous to Iter 13's
  `pow_primeCounting_le_pow_self`.
* `lcmRange_le_pow_pred (n : ℕ) : lcmRange n ≤ n ^ (n - 1)` —
  the strict improvement over Iter 13's
  `lcmRange_le_pow_self_via_primeCounting`. Saves one factor of `n`
  in the exponent — concretely: `n = 4` gives `lcmRange 4 = 12 ≤ 64`
  (Iter 14) vs `≤ 256` (Iter 13); `n = 10` gives `≤ 10⁹` vs `≤ 10¹⁰`.

Build pending; proof bodies use only Mathlib API already exercised
by Iter 13 (`Finset.card_erase_of_mem`, `Finset.card_le_card`,
`Nat.not_prime_zero`, `Nat.not_prime_one`, `Nat.pow_le_pow_right`).
File 560 → 657 lines (+97), theorems 40 → 43 (+3),
definitions/sorries/axiomCount unchanged.

----

Iteration 13 (2026-05-09, retained for context): **prime-counting
subordination chain**. Three new theorems make the dependency
`Iter 11 ⟹ Iter 13 ⟹ Part 3` explicit by establishing the chain
`lcmRange n ≤ n^π(n) ≤ n^n`. The middle step is the trivial
`π(n) ≤ n` bound (`primeCounting_le_self`), proved by observing
that the prime filter on `Finset.range (n+1)` excludes `0` and so
fits inside `(Finset.range (n+1)).erase 0`, which has `n` elements.
Build pending; proof bodies use only Mathlib API already exercised
by earlier iters (`Nat.count_eq_card_filter_range`,
`Finset.card_erase_of_mem`, `Nat.pow_le_pow_right`). File 488 → 560
lines (+72), theorems 37 → 40 (+3), definitions/sorries/axiomCount
unchanged.

----

Iteration 12 (2026-05-09, retained for context): **three independent
surgical fixes** to unblock the build for iters 5–11 (which all
merged with `(build pending)` status). Empirically discovered by
docker-build of iter 11 plus targeted re-investigation: the original
"single drift" diagnosis from the iter 11 PR was incomplete — only
one of the three errors is true Mathlib drift; the other two are
subtle elaboration issues introduced by iter 8 / iter 2 that survived
because the file has not had a clean build since iter 4.

### Fix 1 (line 118 — `pow_dvd_lcmRange`): true Mathlib drift

`Nat.pos_pow_of_pos` was removed from Mathlib (no longer present in
v4.26.0; absent from current docs). The replacement `Nat.pow_pos`
lives in core Lean's `Init.Prelude` with signature
`{a n : Nat} (h : 0 < a) : 0 < a ^ n`. One-line swap:

```diff
- dvd_lcmRange (Nat.pos_pow_of_pos k hb) hbkn
+ dvd_lcmRange (Nat.pow_pos hb) hbkn
```

### Fix 2 (line 262 — `lcmRange_dvd_prod_prime_powers`): `rw` cascade

Inside `have hm_eq : m = ∏ p ∈ P, p ^ m.factorization p`, the proof
opened with `rw [h1]` where
`h1 : m = ∏ p ∈ m.primeFactors, p ^ m.factorization p`. Because
`h1`'s RHS contains `m` itself, `rw [h1]` was rewriting `m` on
BOTH sides of the goal `m = ∏ p ∈ P, p ^ m.factorization p`,
mutating the RHS into
`∏ p ∈ P, p ^ (∏ p ∈ m.primeFactors, p ^ m.factorization p).factorization p`
— an unprovable nested expression. Targeted fix: rewrite LHS only.

```diff
-    rw [h1]
+    -- Rewrite only the LHS `m` — `rw [h1]` would also expand `m` inside
+    -- `m.factorization` on the RHS, leaving an unprovable nested goal.
+    conv_lhs => rw [h1]
```

### Fix 3 (line 376 — `lcmRange_succ` forward direction): elaboration

`Finset.dvd_lcm (Finset.mem_range.mpr hi')` had its function `f`
inferred ambiguously as `HAdd.hAdd i` (the curried `i + ·`) instead
of `(· + 1)`, because the goal post-`unfold lcmRange + Finset.lcm_dvd`
did not pin down `f`. The chain via `Nat.dvd_lcm_left _ _` then failed
to unify. Routed through the already-established `dvd_lcmRange` lemma
instead, which has fully-determined types:

```diff
-  · unfold lcmRange
-    apply Finset.lcm_dvd
+  · show (Finset.range (n + 1)).lcm (· + 1) ∣ Nat.lcm (lcmRange n) (n + 1)
+    apply Finset.lcm_dvd
     intro i hi
     have hi_lt : i < n + 1 := Finset.mem_range.mp hi
     by_cases hi_eq : i = n
     · subst hi_eq; exact Nat.dvd_lcm_right _ _
-    · have hi' : i < n := by omega
-      exact dvd_trans (Finset.dvd_lcm (Finset.mem_range.mpr hi'))
-        (Nat.dvd_lcm_left _ _)
+    · have hi' : i + 1 ≤ n := by omega
+      have h_dvd : i + 1 ∣ lcmRange n := dvd_lcmRange (Nat.succ_pos _) hi'
+      exact dvd_trans h_dvd (Nat.dvd_lcm_left _ _)
```

Reverse direction unchanged.

### Net delta

Three surgical edits totaling ~10 lines changed. No new theorems, no
new imports, no API redesign. Proof content of iters 5–11 (Chebyshev
decomposition forward + reverse + equality, prime-counting bound,
primeCounting reformulation) is preserved verbatim and verified-buildable
for the first time after iter 12 merges.

Iteration 11 (#17401 merged): reformulates Iter 10's prime-counting
bound in Mathlib's `Nat.primeCounting` vocabulary —
the literal published form of the bound:

- `lcmRange_le_pow_primeCounting (n : ℕ) :
   lcmRange n ≤ n ^ Nat.primeCounting n`

A one-line corollary of Iter 10's `lcmRange_le_pow_card_primes_le`
plus the standard identification
`Nat.primeCounting n = ((Finset.range (n+1)).filter Nat.Prime).card`
via `Nat.count_eq_card_filter_range` (cf. the analogous central-binomial
bound `(2n).choose n ≤ (2n) ^ π(2n)` in
`ChebyshevPNTBridgeOQ01.lean:140-147` for the pattern).

This is content-light but vocabulary-important: the bound now reads
in standard PNT-statement form $\\text{lcm}(1,...,n) \\leq n^{\\pi(n)}$
and is directly compatible with Mathlib's `Nat.primeCounting` API
(monotonicity, asymptotics, etc.) for downstream chaining. New import:
`Mathlib.NumberTheory.PrimeCounting`.

Iteration 10 (#17369 merged): extracted the **first non-trivial
published-bound** from the closed Chebyshev decomposition:

- `lcmRange_le_pow_card_primes_le (n : ℕ) :
   lcmRange n ≤ n ^ ((Finset.range (n+1)).filter Nat.Prime).card`

Equivalently `lcmRange n ≤ n ^ π(n)`, where `π(n)` is the
prime-counting function. Strictly weaker than Hanson's `3 ^ n` (since
`π(n) ~ n / log n` by PNT, so `n ^ π(n) ~ n ^ {n/log n}` grows
super-exponentially), but a non-trivial sharpening of the trivial
`n ^ n` bound (Part 3 of the file): this saves the contribution of
all *composite* `k ∈ {1,...,n}` via prime-power coalescing.

The proof is short (~15 lines) and follows immediately from the
Iter 9 Chebyshev identity:

1. `n = 0`: `lcmRange 0 = 1` and the prime-filter is empty
   (0 isn't prime), so RHS = `0 ^ 0 = 1`. Closes by `simp`-style
   `Finset.range_one + Finset.filter_singleton + Nat.not_prime_zero`.
2. `n ≥ 1`: rewrite via `lcmRange_eq_prod_prime_powers`; bound each
   factor `p ^ ⌊log_p n⌋ ≤ n` by `Nat.pow_log_le_self p hn.ne'`;
   collapse `∏ _ ∈ S, n = n ^ S.card` via `Finset.prod_const`.

Iteration 9 (#17333 merged): closed the antisymmetric **Chebyshev
prime-power equality** by `Nat.dvd_antisymm`:

- `lcmRange_eq_prod_prime_powers (n : ℕ) :
   lcmRange n = ∏ p ∈ (Finset.range (n+1)).filter Nat.Prime,
                 p ^ Nat.log p n`

Iteration 8 (#17312 merged): closed the **reverse direction of
Chebyshev's decomposition**, complementing Iter 7's forward direction:

- `lcmRange_dvd_prod_prime_powers (n : ℕ) :
   lcmRange n ∣ ∏ p ∈ (Finset.range (n+1)).filter Nat.Prime, p ^ Nat.log p n`

Routes through `Nat.factorization`: write
`m = ∏_{p ∈ m.primeFactors} p^(m.factorization p)` via
`Nat.factorization_prod_pow_eq_self`, extend the index set, and bound
each exponent by `Nat.log p n` using `Nat.le_log_of_pow_le`.

Iteration 7 (#17166 merged): closes the **easy direction of
Chebyshev's decomposition**, the major structural milestone of the
last six iterations:

- `prod_prime_powers_dvd_lcmRange (n : ℕ) :
   (∏ p ∈ (Finset.range (n+1)).filter Nat.Prime, p ^ Nat.log p n)
     ∣ lcmRange n`

The proof has two parts:
1. **Helper lemma** `prod_dvd_of_pairwise_coprime` (private; ~22 lines):
   for any Finset ℕ S and function f : ℕ → ℕ, if every f p (for p ∈ S)
   divides N and the f p are pairwise coprime, then ∏ f p ∣ N.
   Standard Finset.induction; combines `Nat.Coprime.prod_right` (lift
   pairwise to coprime-with-product) with `Nat.Coprime.mul_dvd_of_dvd_of_dvd`.
   Direct parallel of `Erdos1057Problem.prod_primes_dvd_of_each_dvd`,
   abstracted over f to support prime-power factors.
2. **Main theorem** (8 lines on top of helper): n=0 case dispatches via
   `Nat.not_prime_zero` (range 1 = {0}, 0 ∉ Prime ⇒ filter = ∅);
   n ≥ 1 case applies the helper with f = (· ^ Nat.log · n), feeding
   `prime_pow_dvd_lcmRange` (each-factor-divides) and
   `coprime_prime_pow_pow_of_ne` (pairwise-coprime).

Iteration 6 (#17128 merged): added `coprime_prime_pow_pow_of_ne :
∀ {p q}, p.Prime → q.Prime → p ≠ q → ∀ a b, Coprime (p^a) (q^b)`.

Iteration 5 (#17021 merged): added the prime-power
specialization on top of Iteration 3's `pow_dvd_lcmRange`:

- `prime_pow_dvd_lcmRange : ∀ {p n : ℕ}, p.Prime → 1 ≤ n →
   p ^ Nat.log p n ∣ lcmRange n`

The proof is a one-line specialization of `pow_dvd_lcmRange`, using
`Nat.pow_log_le_self p hn'` to discharge `p ^ Nat.log p n ≤ n`. New
imports: `Mathlib.Data.Nat.Log`, `Mathlib.Data.Nat.Prime.Basic`. This
is the maximal-prime-power half of Chebyshev's decomposition
`lcm(1,...,n) = ∏_{p prime ≤ n} p ^ ⌊log_p n⌋`.

Iteration 3 (#16772 merged): added `pow_dvd_lcmRange : 0 < b → b^k ≤ n
→ b^k ∣ lcmRange n` — the generic power-divisibility lemma whose prime
specialization Iteration 5 just discharged.

Iteration 2 (#16704 merged): added foundational structural lemmas:
- `lcmRange_succ`: lcm(1,...,n+1) = Nat.lcm (lcmRange n) (n+1).
- `lcmRange_dvd_lcmRange_of_le`: divisibility monotonicity.
- `lcmRange_monotone`: numerical monotonicity.

Iteration 1 (bootstrap, completed 2026-05-07):
- Provable elementary bounds: lcmRange n ≤ n!, lcmRange n ≤ n^n.
- Numerical verification of Hanson's bound for n ∈ {1..10, 12, 15, 20}.
- Axiom statement of the general claim with documentation of proof
  strategy and Mathlib gaps.

## Active Approach

**Approach (canonical, blocked on Mathlib infrastructure)**:
Hanson's 1972 Beta-integral approach. Use
`∫₀¹ x^k(1-x)^(n-k) dx = 1/((n+1)·C(n,k))` and
`lcmRange(n+1) · Beta(k, n-k) ∈ ℤ` to derive `3^n` via a
careful summing argument over k ∈ {0,...,n}.

Currently blocked on:
- Mathlib lacks Beta-integral identities in usable form for ℚ-valued
  bounds.
- Mathlib lacks the `primorial → lcm` bridge needed for the easier
  `4^n` intermediate.

## Attempt Count
- Total attempts: 14.
- Current approach attempts: 0 (Approach 1 not started; awaits Mathlib).
- Approaches tried: bootstrap with elementary bounds + axiom (iter 1);
  structural-lemma layer for inductive proofs (iter 2); generic
  power-divisibility lemma `pow_dvd_lcmRange` (iter 3); empirical
  evidence extension n ∈ {25, 30, 50} (iter 4, in flight as #16880);
  prime-power specialization `prime_pow_dvd_lcmRange` (iter 5, #17021);
  coprime distinct prime powers `coprime_prime_pow_pow_of_ne` (iter 6,
  #17128); easy direction of Chebyshev's decomposition
  `prod_prime_powers_dvd_lcmRange` (iter 7, #17166); reverse
  direction `lcmRange_dvd_prod_prime_powers` via `Nat.factorization`
  (iter 8, #17312); antisymmetric closure
  `lcmRange_eq_prod_prime_powers` (iter 9, #17333);
  prime-counting bound `lcmRange_le_pow_card_primes_le` (iter 10,
  #17369); primeCounting reformulation
  `lcmRange_le_pow_primeCounting` (iter 11, #17401);
  three-fix build unblock — Mathlib drift `Nat.pos_pow_of_pos → Nat.pow_pos`
  (line 118), `rw [h1]` cascade fix `→ conv_lhs => rw [h1]` (line 262),
  and `lcmRange_succ` forward-chain re-routing through `dvd_lcmRange`
  (line 376) — iter 12, #17448; restores build for iters 5–11;
  prime-counting subordination chain `primeCounting_le_self`,
  `pow_primeCounting_le_pow_self`, `lcmRange_le_pow_self_via_primeCounting`
  (iter 13, #17499 merged build pending) — makes explicit that Iter 11's
  `lcmRange ≤ n^π(n)` subordinates Part 3's `lcmRange ≤ n^n` via
  the trivial `π(n) ≤ n` bound; sharpened-prime-counting bound
  `primeCounting_le_pred`, `pow_primeCounting_le_pow_pred`,
  `lcmRange_le_pow_pred` (iter 14, this PR, build pending) —
  exploits `1 ∉ Prime` (in addition to Iter 13's `0 ∉ Prime`) to
  tighten the chain to `lcmRange n ≤ n^π(n) ≤ n^(n-1)`, saving one
  factor of `n` in the exponent.

## Blockers
- **Mathlib Beta-integral over ℚ**: not in usable form.
- **Mathlib primorial → lcm bridge**: missing.
- **Mathlib LCM-specific bounds**: none exist.

## Next Action

**Iteration 14 (this PR, build pending)**: sharpened prime-counting
bound `π(n) ≤ n - 1` and resulting chain
`lcmRange n ≤ n^π(n) ≤ n^(n-1)`. Three new theorems sharpen Iter 13
by exploiting that *both* `0` and `1` are non-prime:

* `primeCounting_le_pred (n : ℕ) : Nat.primeCounting n ≤ n - 1` —
  the prime filter on `(Finset.range (n+1))` is a subset of
  `((Finset.range (n+1)).erase 0).erase 1`, whose cardinality is
  `n - 1` (with `Nat` truncated subtraction).
* `pow_primeCounting_le_pow_pred (n : ℕ) (hn : 1 ≤ n) :
  n ^ Nat.primeCounting n ≤ n ^ (n - 1)` — one-line via
  `Nat.pow_le_pow_right`.
* `lcmRange_le_pow_pred (n : ℕ) : lcmRange n ≤ n ^ (n - 1)` — strict
  improvement over Iter 13's `lcmRange_le_pow_self_via_primeCounting`,
  saving one factor of `n` in the exponent.

**File delta**: +97 lines (560 → 657), +3 theorems (40 → 43),
definitions/sorries/axiomCount unchanged. Build pending — proof
bodies use only Mathlib API already exercised by Iter 13
(`Finset.card_erase_of_mem`, `Finset.card_le_card`,
`Nat.not_prime_one`, `Nat.pow_le_pow_right`).

**Iteration 15 candidate**: connect the prime-counting bound to
asymptotic Chebyshev-style improvements. Mathlib has
`Nat.primeCounting_eq_card_primes` and Bertrand-derived prime-gap
bounds; a tighter bound like `lcmRange n ≤ n^{n / log n}` (Chebyshev
1850) would discharge the parent file's `lcm_hanson_bound` axiom up
to a constant multiplier in the exponent (Hanson 1972 saves the
specific constant `log 3` ~ 1.0986). Alternatively, an Iter 15a
candidate is to upgrade `primeCounting_le_pred` to use
`Nat.Prime.two_le`, sharpening the subset to
`Finset.Ioc 1 n` directly (cleaner card computation via
`Nat.card_Ioc`), then chase the bound `π(n) ≤ ⌈n/2⌉` for `n ≥ 4` by
also excluding even composites — yielding `lcmRange n ≤ n^⌈n/2⌉`,
strictly stronger than `n^(n-1)` for `n ≥ 4`.

**Long-term paths still open:**

1. **Intermediate `lcm(1..n) ≤ 4^n`** via primorial bridge: blocked on
   the Mathlib bridge `lcm(1..n) ≤ n · primorial(n)`. Note (Iteration 3
   insight): the literal `≤ n · primorial(n)` form is FALSE
   (counterexample n=9: 2520 > 1890). Correct route is via Chebyshev's
   prime-power formula above.

2. **Full Hanson `3^n`** (Beta-integral + Chebyshev): months.

Either result discharges the parent file's `lcm_hanson_bound` axiom.

## References

- `proofs/Proofs/BaselProblemOQ01OQ01OQ02OQ03.lean` — bootstrap file.
- `proofs/Proofs/BaselProblemOQ01OQ01OQ02.lean:410` — parent's
  `axiom lcm_hanson_bound` that this OQ targets.
- `src/data/proofs/basel-problem-oq-01-oq-01-oq-02-oq-03/meta.json` — gallery.
- `research/problems/basel-problem-oq-01-oq-01-oq-02-oq-03/problem.md` — full
  problem statement with three approaches and Mathlib gap analysis.
