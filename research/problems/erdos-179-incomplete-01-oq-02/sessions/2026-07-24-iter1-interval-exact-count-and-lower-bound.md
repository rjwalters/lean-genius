# Session 2026-07-24 — Iteration 1 (researcher-2): Interval exact count + quadratic lower bound

## Phase: OBSERVE → ORIENT → ACT (single-session resolution)

## Question

Can a quantitative lower bound on `countAPs` for structured sets (e.g. intervals)
be formalized as a counterpoint to the upper bound (`countAPs_le_choose` in the
parent entry `erdos-179-incomplete-01`)?

## Answer: YES — resolved affirmatively, 0 axioms / 0 sorries

New file `proofs/Proofs/Erdos179Incomplete01OQ02.lean` (imports the parent
`Proofs.Erdos179Incomplete01`, works in the same `Erdos179Combinatorics`
namespace so all lemmas interoperate).

### Results proved

1. **Endpoint lemmas** — every element of `arithmeticProgression a d k` lies in
   `[a, a + (k-1)*d]`, and both endpoints are members (for `0 < k`).
2. **Rigidity** (`arithmeticProgression_inj`) — for `k ≥ 2`, `d, d' > 0`, equal
   AP finsets force equal first terms and equal differences. Proof recovers `a`
   as the minimum and `a + (k-1)d` as the maximum, then cancels `k-1`.
   This is the crux: it legitimizes counting AP *sets* by parameter *pairs*.
3. **Exact formula** (`countAPs_range_eq_sum`) — for `k ≥ 2`:
   `countAPs (range N) k = Σ_{d=1}^{⌊(N-1)/(k-1)⌋} (N - (k-1)d)`.
   Mechanism: the AP finsets in `range N` are the injective image of the
   parameter sigma-set `(Icc 1 ⌊(N-1)/(k-1)⌋).sigma (fun d => range (N-(k-1)d))`,
   and `Finset.card_sigma` turns the card into the sum.
4. **Quadratic lower bound** (`countAPs_range_lower_bound`) — the open question:
   `N/(2(k-1)) * (N/2) ≤ countAPs (range N) k` — order `N²/(4(k-1))`.
   Every difference `d ≤ N/(2(k-1))` admits ≥ `⌊N/2⌋` first terms.
5. **Matching upper bound** (`countAPs_range_upper_bound`) — `≤ N * N`, so the
   interval count is Θ(N²) for fixed k: intervals achieve the quadratic
   supersaturation order that the parent's `F_k(N,ℓ) = N^{2-o(1)}` concerns.
6. **Existence complement** (`containsAP_range_iff`) — `ContainsAP (range N) k ↔ k ≤ N`.
7. **Consistency checks** — `countAPs_range_two : countAPs (range N) 2 = C(N,2)`
   (via parent's `countAPs_two`) and `countAPs_range_sum_two`: the exact formula
   collapses to the triangular sum `Σ_{d=1}^{N-1} (N-d) = C(N,2)` at k = 2.

## Key Lean techniques

- Sigma-set parameterization (`Finset.sigma` + `Finset.card_sigma`) for counting
  a set of finsets with fiber-dependent parameter ranges.
- `Set.InjOn` + `Finset.card_image_of_injOn` driven by the rigidity lemma.
- Nat-division bookkeeping: `Nat.div_div_eq_div_mul` to rewrite
  `N/(2(k-1)) = (N/2)/(k-1)`, `Nat.le_div_iff_mul_le` for the index-range
  membership, `Nat.div_mul_le_self` for `(k-1)·⌊N/2/(k-1)⌋ ≤ N/2`; `omega`
  closes all linear goals treating `(k-1)*d`-style products as atoms
  (kept orientation `(k-1) * d` consistent so atoms unify).

## Build

`./proofs/scripts/docker-build.sh Proofs.Erdos179Incomplete01OQ02` — see PR for result.

## Status

Question RESOLVED affirmatively (exact count, not merely a lower bound).
Thread can be marked completed.
