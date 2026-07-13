## Session 2026-06-04 (Session 4) — S3 ACT: discharge both strategic sorries

**Mode**: FRESH (claimed problem from available pool)
**Outcome**: completed
**Agent**: researcher-4

### What I Did

Discharged both strategic sorries left by S2 SCAFFOLD (2026-05-14), producing
a fully verified Möbius indicator identity (`Σ_{d|n} μ(d) = [n=1]`) with
0 sorries and 0 axioms.

1. `moebius_prod_squarefree (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
       μ (∏ p ∈ s, p) = (-1 : ℤ) ^ s.card`

   Discharged in 2 lines via the multiplicativity route, **not** the
   squarefreeness route anticipated in the S2 plan:

   ```lean
   rw [isMultiplicative_moebius.map_prod_of_prime s hs]
   exact Finset.prod_eq_pow_card (fun p hp => moebius_apply_prime (hs p hp))
   ```

   `isMultiplicative_moebius.map_prod_of_prime` (Mathlib's
   `NumberTheory.ArithmeticFunction.Defs`) directly turns
   `μ (∏ p ∈ s, p)` into `∏ p ∈ s, μ p` when the elements of `s` are
   primes (uses `coprime_primes` under the hood for pairwise coprimality).
   Then `moebius_apply_prime` gives `μ p = -1` for each prime, and
   `Finset.prod_eq_pow_card` collapses the constant product to `(-1)^s.card`.

   This bypasses entirely the `Squarefree.prod` + `cardFactors_mul` +
   `moebius_apply_of_squarefree` chain envisioned in S2/S3 plan.

2. `sum_filter_squarefree_moebius_eq_powerset (n : ℕ) (hn : n ≠ 0) :
       (∑ d ∈ n.divisors with Squarefree d, μ d : ℤ)
         = ∑ S ∈ n.primeFactors.powerset, (-1 : ℤ) ^ S.card`

   Discharged in 6 lines following S2 plan exactly, with one extra step
   needed: `Finset.prod_val` to bridge `S.val.prod` (multiset product
   from `Nat.sum_divisors_filter_squarefree`) to `∏ p ∈ S, p` (Finset
   product expected by `moebius_prod_squarefree`).

   ```lean
   rw [Nat.sum_divisors_filter_squarefree hn, normalizedFactors_toFinset_eq n hn]
   refine Finset.sum_congr rfl fun S hS => ?_
   rw [Finset.mem_powerset] at hS
   rw [Finset.prod_val]
   exact moebius_prod_squarefree S (fun p hp => Nat.prime_of_mem_primeFactors (hS hp))
   ```

3. Updated file header docstring: `S2 SCAFFOLD` → `Verified` with
   updated bullet list of key building blocks.

### Key Findings

- **`isMultiplicative_moebius.map_prod_of_prime` is the right tool** for
  `μ (∏ s)` when `s` is a Finset of distinct primes. The squarefree
  route (compute `cardFactors` of the product) is unnecessarily indirect.
  This shortcut may apply to other multiplicative arithmetic functions:
  whenever the target is `f (∏ p ∈ s, p)` for `f` multiplicative and
  `s` distinct primes, prefer the multiplicativity route.

- **`Finset.prod_val` is the missing bridge** between Mathlib's
  `Nat.sum_divisors_filter_squarefree` (which yields `f i.val.prod` in
  the powerset index) and the Finset-product form expected by
  multiplicativity lemmas. Without it, you can't directly apply
  `moebius_prod_squarefree` to the per-S goal.

- **Total discharge size (8 lines) << anticipated (S2 plan estimated
  30-50 lines)**. The Mathlib v4.26.0 API for multiplicative arithmetic
  functions is much more direct than the squarefree-cardFactors chain
  the S2 OBSERVE phase identified.

### Files Modified

- `proofs/Proofs/EulerTotientOQ04OQ01.lean`: 158 → 164 LOC; 2 sorries → 0;
  0 axioms unchanged.
- `research/problems/euler-totient-oq-04-oq-01/state.md`: phase
  SCAFFOLD → COMPLETED, iter 3 → 4.

### Next Steps

- (follow-up, lower priority): create
  `src/data/proofs/euler-totient-oq-04-oq-01/` gallery entry with
  `status: verified` and `badge: original`. Parent file
  `EulerTotientOQ04.lean` already lists this in `additionalFiles`,
  so the basic linkage is there.
- (technique propagation): consider documenting
  `isMultiplicative_moebius.map_prod_of_prime` as the canonical
  approach for `μ ∘ prod-of-distinct-primes` in the technique index.
