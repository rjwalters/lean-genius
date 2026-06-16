# Knowledge Base: binomial-theorem-oq-02-oq-01-oq-04

Multinomial distribution moments via the moment-generating function. Work for this
slug lands in the **registered parent** `proofs/Proofs/BinomialTheoremOQ02OQ01.lean`
(0 sorry / 0 axiom) and the gallery entry `binomial-theorem-oq-02-oq-01`; there is no
dedicated `OQ04` Lean file.

---

## Current state (verified, on `origin/main`)

| Moment | Theorem | Location | Status |
|---|---|---|---|
| Mean `E[Xi]=n·pi` | `multinomial_mean` (1st MGF derivative) | `BinomialTheoremOQ02OQ01.lean:192` | ✅ merged #24983 |
| Cross moment `E[Xi·Xj]=n(n-1)pi·pj`, `i≠j` | `multinomial_cross_moment` | `BinomialTheoremOQ02OQ01OQ03.lean:150` | ✅ verified |
| Covariance `Cov(Xi,Xj)=-n·pi·pj`, `i≠j` | `multinomial_covariance` | `BinomialTheoremOQ02OQ01OQ03.lean:346` | ✅ verified |

So mean and the **off-diagonal** (i≠j) second moments are done.

## The one remaining standard second moment: VARIANCE (the i=j diagonal)

`multinomial_cross_moment` carries an explicit `hij : i ≠ j`, so the diagonal
`E[Xi²]` — and hence `Var(Xi) = n·pi·(1−pi)` — is **not** yet in Lean. This is the
natural next target and is **not new mathematics**: it is the single-variable
specialization of the already-verified cross-moment proof.

### Session 2026-06-16 (researcher-1) — variance route pinned + certified (build-free)

**Mode:** build-free de-risk (dual blackout this cycle: Aristotle `prove` → 404;
Docker `proofs/.lake` is a self-symlink that re-clones Mathlib + 4 `lean-build`
containers on a 7.65 GiB VM, so no safe build). No Lean written — blind-writing the
finicky `HasDerivAt` bookkeeping onto the green registered file is the documented
anti-pattern; build-iterate it instead.

**Certificate `verify_variance.py`** (exact rational arithmetic, 30 `(p,n)` cases incl.
2/3/4-category, `n=0..8`) confirms the route:

```
Single-var MGF (the i=j specialization of cross_moment's bivariate hmgf at b=0):
    G(a) := Σ_k P(k)·(1+a)^{k_i} = (1 + p_i·a)^n
  G'(0)  = Σ_k P(k)·k_i          = E[Xi]        = n·p_i        (= multinomial_mean)
  G''(0) = Σ_k P(k)·k_i·(k_i−1)  = E[Xi(Xi−1)]  = n(n−1)·p_i²   ← the TODO Lean lemma
Then  E[Xi²] = n(n−1)p_i² + n·p_i,  Var(Xi) = E[Xi²] − (n·p_i)² = n·p_i·(1 − p_i).
```

**Exact Lean obligations (mirror `multinomial_cross_moment`, single-variable):**
1. MGF identity `Σ_k multinomialProb s p n k · (1+a)^{k i} = (1 + p i · a)^n` — same
   `Finset.piAntidiag` product/sum bookkeeping as `cross_moment`'s `hmgf`, with
   `g_l = if l = i then 1+a else 1` (drop the second variable).
2. Second-factorial-moment extraction `Σ_k P(k)·(k i)·(k i − 1) = n(n−1)·p_i²`: a
   `deriv_add_pow_two` analog of `cross_moment`'s `deriv_add_pow` — the 2nd derivative
   of `a ↦ (1+a)^m` at 0 is `m(m−1)` (compose `hasDerivAt_pow` twice / `iteratedDeriv`),
   matched to the sum via `HasDerivAt.sum` + `HasDerivAt.unique`, exactly as cross_moment
   matches the bivariate mixed partial.
3. Assemble: add `multinomial_mean` (parent), then `ring`/`field_simp` for
   `Var = E[Xi²] − (E[Xi])²`.

**Honesty.** Variance is a routine diagonal of merged machinery — not a breakthrough.
Value of this session is purely the de-risk artifact (formula + exact derivation route
+ bearer list) so the next live window transcribes the single-variable copy quickly.

## Next action

Next live backend window (Docker ≤2 containers + non-self-symlink `.lake`, or Aristotle
non-404): add `multinomial_variance` (and the helper `E[Xi(Xi−1)] = n(n−1)pi²`) to
`BinomialTheoremOQ02OQ01.lean` following the obligations above; build-verify; update the
gallery `binomial-theorem-oq-02-oq-01` meta openQuestions (the `Var(Xi)` follow-up). Do
NOT blind-write — it is finicky `HasDerivAt` analysis on a fully-verified registered file.
