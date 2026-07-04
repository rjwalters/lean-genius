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

---

## Session 2026-07-04 (researcher-6) — faithfulness to Oppermann's 1882 form (0-axiom)

The file defines `OppermannConjecture` via the *split-interval* form (a prime in
each half of `(n²,(n+1)²)`, split at the composite midpoint `n²+n`). Oppermann's
**original 1882 statement** is instead two-sided about each square `n²`: for
`n > 1`, a prime in `(n²−n, n²)` AND a prime in `(n², n²+n)`. The problem.md notes
these "coincide after re-indexing"; this session turns that informal remark into a
machine-checked equivalence.

- **`OppermannClassicalAt n`** / **`OppermannClassical`** — the 1882 two-sided form.
- **`classical_first_succ_iff_upper n`**: the lower interval of the classical form
  at `n+1`, `((n+1)²−(n+1), (n+1)²)`, is *literally* the upper half `(n²+n,(n+1)²)`
  of the split gap at `n`. Proof is a one-line `rw` after the Nat identity
  `(n+1)²−(n+1) = n²+n` (get it from `ring`-expanding `(n+1)²` then `omega`; omega
  handles the truncated subtraction). Both sides become α-equal, so `rw` closes it.
- **`oppermann_conjecture_iff_classical`**: `OppermannConjecture ⟺ OppermannClassical`.

### Key subtlety — the index boundary
The two forms are NOT term-for-term identical at the edge. Writing `H` for
"prime in the upper half of the split gap at m" and `L` for "prime in the lower
half at m":
- `OppermannConjecture` = `∀ m≥2, L(m) ∧ H(m)`.
- `OppermannClassical`  = `∀ n≥2, H(n−1) ∧ L(n)` = `(∀ m≥1, H(m)) ∧ (∀ m≥2, L(m))`.
So Classical additionally demands `H(1)` = a prime in `(2,4)`. It's not handed to
you by the split conjecture (which starts at m≥2), so the forward direction must
prove `H(1)` outright — **`upper_half_one`** := `⟨3, norm_num, norm_num, norm_num⟩`
(0-axiom, no `native_decide`). Handle the `m<2` case with `interval_cases m`; the
`m=0` branch is killed by `absurd hn (by omega)`.

### Verified
`docker-build.sh Proofs.LegendrePartialOQ04` → exit 0, 7744 jobs.
`#print axioms oppermann_conjecture_iff_classical` → `propext, Classical.choice,
Quot.sound` only (genuinely 0-axiom).
