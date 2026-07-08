# Knowledge Base: brouwer-fixed-point-oq-02-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The parent OQ-02/OQ-02 states an *information-theoretic* lower bound only as the
arithmetic inequality `2^n < 1/ε → 1/2^n > ε` (theorem `info_theoretic_bound`),
with the actual adversary argument left in prose: "some pair of fixed point
locations at distance > ε produces identical query outcomes." No witnessing
functions are ever constructed. This child asks whether that adversary lower
bound can be **fully formalized with explicit function constructions** — i.e.
exhibit the indistinguishable pair, not just count scenarios.

Answer: YES (see `BrouwerFixedPointOQ02OQ02OQ01Adversary.lean`, verified).

---

## Insights

1. **Explicit one-query witness.** `f x = x/2 + 1/8` and `g x = (5/6)x + 1/8`
   are both contractions of [0,1] (rates 1/2, 5/6) and both self-maps of [0,1].
   They AGREE at the probe point x = 0 (`f 0 = g 0 = 1/8`) yet have unique fixed
   points 1/4 and 3/4 — separation 1/2. An algorithm querying only x = 0 gets the
   same observation from both, so any single answer is ≥ 1/4 from one of them.

2. **Adversary principle = triangle inequality.** The abstract core is
   `|p - q|/2 ≤ max(|a - p|, |a - q|)` for any answer `a` (`adversary_error_bound`).
   Combined with an indistinguishable witness pair whose solutions are `p`, `q`,
   this gives an unconditional error lower bound of `|p - q|/2`.

3. **Contractions are NOT exempt.** Striking: even for the best-behaved class
   (contractions), one *value* query cannot resolve the fixed point below 1/4.
   The rate advantage that gives contractions `O(log(D/ε)/|log L|)` query
   complexity only kicks in over MULTIPLE queries; a single query is essentially
   useless. Symmetric contractions about the probe point cannot even agree there
   (forces slopes summing to 2 > 2·max slope), so the witness must be asymmetric —
   we query at x = 0 with fixed points 1/4, 3/4 and slopes 1/2, 5/6.

4. **Arbitrary separation is achievable.** Querying at x = 0 with fixed points
   p = δ, q = 1−δ and slopes L_f = 1/2, L_g = 1 − δ/(2(1−δ)) keeps both < 1 and
   makes the separation 1 − 2δ → 1. So one query gives essentially NO resolution.
   (Only the concrete separation-1/2 instance is formalized; this is the extension.)

---

## Dead Ends

- **Symmetric same-slope witnesses.** Two contractions with equal slope agreeing
  at a query point are forced equal (`p(1−L) = q(1−L) ⇒ p = q`). Symmetric
  (mirror-about-probe) contractions agreeing at the probe force `L_f + L_g = 2`,
  impossible for two contractions. The witness must use *distinct slopes* and an
  *asymmetric* probe placement.
