# Knowledge Base: legendre-partial-oq-04

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session 2026-07-04 (researcher-11) — the Brocard mechanism (0-axiom)

The base entry was already `completed` (statement + Oppermann⟹Legendre +
Oppermann⟹≥2 primes + π-counting form + native_decide n=2..20 + axiom). This
session added new **0-axiom** structural content on top:

- **`oppermann_at_four_primes_two_gaps`**: `OppermannAt n → OppermannAt (n+1) →
  4 ≤ #{primes in (n²,(n+2)²)}`. Four explicit half-interval primes `p<q<r<s`,
  kept pairwise distinct by the composite separators `n²+n`, `(n+1)²`,
  `(n+1)²+(n+1)`; `{p,q,r,s} ⊆ prime-filter` gives card ≥ 4. This is the
  elementary combinatorial core of **Oppermann ⟹ Brocard**.
- **`oppermann_at_pi_total`**: `OppermannAt n → π((n+1)²)−π(n²) ≥ 2`, the total
  π-count form of `oppermann_at_two_primes` (no monotonicity lemma needed —
  transport through `card_primes_Ioc` + the composite endpoint `(n+1)²`).
- Conjecture-level corollaries and a `four_primes_2` sanity instance.

### Technical notes
- **omega + nonlinear terms**: `(n+1+1)²` and `(n+2)²` are DISTINCT terms to
  omega (it does not do nonlinear reasoning), so when `OppermannAt (n+1)`
  unfolds its upper bound to `s < (n+1+1)²` you must supply BOTH `ring`
  expansions `(n+1+1)² = n²+4n+4` and `(n+2)² = n²+4n+4` for omega to link them.
- `Finset.card_insert_of_not_mem` is deprecated → use
  `Finset.card_insert_of_notMem` (the `not_mem`→`notMem` rename).
- Verified 0-axiom: `#print axioms` on both new structural theorems reports only
  `propext, Classical.choice, Quot.sound`.

### Frontier
Full Brocard (over consecutive primes) = package this mechanism: consecutive
primes `p<q≥3` are both odd so `q ≥ p+2`, then sum the adjacent-gap bound over
`p..q-1` to reach `π(q²)−π(p²) ≥ 4`. Recorded in nextSteps.
