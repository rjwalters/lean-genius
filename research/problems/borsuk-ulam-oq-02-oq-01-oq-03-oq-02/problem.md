# Problem: For S_n, is symBUDim n d = buDim_{largest prime ≤ n} d?

## Statement

### Plain Language

For the symmetric group S_n acting on a d-dimensional real representation,
is the equivariant Borsuk-Ulam dimension equal to `buDim p* d`, where p* is
the largest prime ≤ n? At even dimensions d = 2k, the parent's classical
Yang-Borsuk axiom pins `buDim p* (2k) = 2k − 1`, so the conjecture there
reduces to `symBUDim n (2k) = 2k − 1`. At odd dimensions the value of
`buDim p* d` for odd primes is not currently axiomatised in the parent
file — see Status below.

### Formal Statement

For every n ≥ 2 and d ≥ 1,
$$
  \text{symBUDim}(n, d) \stackrel{?}{=} \text{buDim}(p^*, d),
$$
where $p^* = \max\{p \text{ prime} : p \leq n\}$.

**Closed form (even d only).** At even d = 2k with k ≥ 1, the parent file's
classical Yang-Borsuk axiom `buDim_prime` (Yang 1955) gives
$\text{buDim}(p^*, 2k) = 2k − 1$, so the conjecture reduces to
$\text{symBUDim}(n, 2k) \stackrel{?}{=} 2k − 1$. At odd d ≥ 3, the value of
$\text{buDim}(p^*, d)$ for odd primes $p^* \geq 3$ is **not** currently
axiomatised in the parent file `BorsukUlamOQ02OQ01.lean`; only the p = 2
case is pinned (parent's `buDim_two` gives $\text{buDim}(2, 2k+1) = 2k$).
See S18 PREP (`sessions/2026-05-13-s18-prep-…audit.md`) for the
even-d / odd-d asymmetry analysis. The literal "= $2 \lfloor d/2 \rfloor − 1$"
decoration on the right-hand side, which appeared in earlier versions of
this file, is **provably inconsistent** at every odd d ≥ 3 (refuted by
`buDim_two` + this file's axiom-free Iter-14 `symBUDim_lower_z2`) and was
removed in Iter 18 (S19 ACT, 2026-05-14).

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - seeker-selected
  - borsuk-ulam
  - equivariant-topology
  - symmetric-groups
  - open-conjecture
```

**Significance**: 6/10
**Tractability**: 6/10

## Why This Matters

1. **Equivariant topology gap**: A direct proof would require Fadell-Husseini
   cohomological index for non-cyclic groups, which is currently outside
   Mathlib. Either a positive result or a counterexample would close a
   meaningful gap in the formalized equivariant topology library.
2. **Practical value**: Resolving the conjecture would yield the explicit
   closed form `symBUDim n (2k) = 2k − 1` for all S_n, simplifying
   downstream applications (chromatic-number bounds via Lovász-Kneser, etc.).
3. **Test cases at small n**: The conjecture is most interesting at n with
   rich non-cyclic subgroup structure: n = 4 (V₄ ≤ S₄), n = 8
   (S₈ contains V₄, A₄, multiple non-cyclic factors).

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| borsuk-ulam-oq-02-oq-01-oq-03 | Parent: develops the symBUDim framework with subgroup monotonicity. |
| borsuk-ulam-oq-02-oq-01 | Cyclic-group buDim (buDim_prime, buDim_mono, buDim_two). |
| bertrands-postulate | Used in Iteration 3 to prove `n/2 < largestPrimeBelow n`. |

## Status (2026-05-14, post Iter 18 S19 ACT)

- Phase-2 axiomatization is complete:
  - `largestPrimeBelow n := Nat.findGreatest Nat.Prime n` (def + 3 supporting facts)
  - `symBUDim_eq_largestPrime` (single axiom, the open content)
  - `symBUDim_even_formula` (closed form at even d, conditional)
  - `symBUDim_even_lower` (UNCONDITIONAL lower bound at even d)
  - `symBUDim_lower_z2` (Iter 14, **unconditional** uniform Z/2 bound
    `d − 1 ≤ symBUDim n d` at ALL d ≥ 1) — strictly tighter than
    `symBUDim_even_lower` at odd d, and the reason the closed-form
    decoration `= 2⌊d/2⌋ − 1` had to be dropped from the Formal Statement
    (it would force `symBUDim n (2k+1) = 2k − 1`, contradicting Z/2).
  - 3 concrete instances at S_3, S_4, S_5
  - Bertrand bound `n/2 < largestPrimeBelow n` (added in iteration 3)
  - Even-d / odd-d asymmetry (Iter 17, Part XXIV): refutes strict-mono
    of `buDim ∘ largestPrimeBelow` at every even d (axiom-free).
- Lean file: `proofs/Proofs/BorsukUlamOQ02OQ01OQ03OQ02.lean`, 1788 lines,
  109 theorems (107 substantive), 2 definitions, 1 axiom, 0 sorries.
- Gallery: `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-03-oq-02/`.

## Iter 18 S19 ACT (2026-05-14): formal-statement audit fix

This iteration discharges S18 PREP §1.5 Option A: drops the inconsistent
closed-form chain `symBUDim(n,d) ?= buDim(p*,d) = 2⌊d/2⌋ − 1` and replaces
it with the consistent two-level statement (conjecture + closed-form
qualifier at even d only). No Lean file is modified; no axiom is added.
The fix brings `problem.md` into consistency with theorems that have been
in the file since Iter 14 (PR #18127 ff, ~6 iterations old at this point).
Iter 17's Part XXIV is the structural reason: at even d the conjecture
collapses to a constant by parent's `buDim_prime`, so the genuine open
content lives at odd d only, where parent's cyclic-prime axiom is silent
for primes p ≥ 3. The closed-form "= 2⌊d/2⌋ − 1" was a holdover from
pre-Iter-14 understanding and is removed here.
