# Problem: erdos-1059-oq-01
# Natural Density of Factorial-Avoiding Primes

**Question**: What is the natural density of primes p satisfying AllFactorialSubtractionsComposite(p)?

**Status**: AXIOMATIZED — 0 sorries, 1 axiom (density_one_conjecture)

## Problem Summary

For a prime p ∈ (l!, (l+1)!], exactly l+1 conditions must check p - k! is composite.
The density-1 conjecture says lim C(x)/π(x) = 1. Proof requires PNT + Brun-Titchmarsh
+ Selberg sieve, none of which are in Mathlib.

---

## Session 2026-04-04 (Session 1) - Logarithmic Check Count Bound + Level-6 Witness

**Mode**: FRESH
**Outcome**: progress

### What I Did

1. **Added p = 769 as first level-6 witness**: p = 769 ∈ (720, 5040) = (6!, 7!].
   Verified: 767 = 13·59, 763 = 7·109, 745 = 5·149, 649 = 11·59, 49 = 7². All composite.
   Check count = 7 (k = 0, ..., 6).

2. **Proved `factorialCheckCount_le_log`** (0 sorries): For n ≥ 2,
   `factorialCheckCount n ≤ Nat.log 2 n + 2`.

   This is the formal version of the density heuristic's key claim: each prime requires
   only O(log n) conditions, not O(n). The proof uses:
   - Helper `two_pow_pred_le_factorial`: 2^(k-1) ≤ k! for k ≥ 1 (induction)
   - Helper `le_log_of_pow_lt`: 2^m < n → m ≤ Nat.log 2 n (via Nat.lt_pow_succ_log_self)
   - Main: factorialCheckSet n ⊆ Finset.range(Nat.log 2 n + 2), so card ≤ Nat.log 2 n + 2

3. **Updated six_prime_witnesses**: packages all 6 witnesses (101, 211, 461, 557, 673, 769)

4. **Updated qualifyingPrimeCount_ge_six**: C(769) ≥ 6

### Key Findings
- 769 is the first level-6 prime witness for Erdős 1059
- The bound factorialCheckCount(n) ≤ ⌊log₂ n⌋ + 2 is tight at n=3 (count=3, log=1, bound=3)
  and n=7 (count=4, log=2, bound=4)
- Proof requires only elementary tools: induction on factorial bound + Nat.log API

### Files Modified
- `proofs/Proofs/Erdos1059OQ01.lean`: 239 → 340 lines, 4 new theorems, 3 new private lemmas
- `src/data/proofs/erdos-1059-oq-01/meta.json`: updated description, originalContributions, leanFile
- `research/problems/erdos-1059-oq-01/knowledge.md`: created this file

### Next Steps
- Prove density_one_conjecture from selberg_density_axiom (OQ-02) once PNT/Brun-Titchmarsh available
- Find more level-6 witnesses in (720, 5040) — next candidates: check primes after 769
- The tighter asymptotic factorialCheckCount(n) = O(log n / log log n) would require Stirling

---

## Session 2026-04-04 (Session 2) - Exact Count Formula + Lint Cleanup

**Mode**: REVISIT
**Outcome**: progress

### What I Did

1. **Proved `factorialCheckCount_eq_of_interval`**: When l! < n ≤ (l+1)!, factorialCheckCount n = l+1.
   This is the exact formula (not just a bound). Proof: show factorialCheckSet n = Finset.range(l+1)
   by double inclusion using Nat.factorial_le and Nat.self_le_factorial.

2. **Proved `factorialCheckCount_const_on_interval`**: The check count is constant within each
   factorial level — if m and n both lie in (l!, (l+1)!], then factorialCheckCount m = factorialCheckCount n.

3. **Removed unused hypothesis `hn : 2 ≤ n`** from `le_log_of_pow_lt` and
   `factorialCheckCount_le_log`. The bound holds for all n (vacuously correct for n ≤ 1 since
   factorialCheckSet is empty). This eliminates a lint warning and strengthens the theorem.

4. Build: 0 sorries, 0 warnings, 1 axiom (density_one_conjecture).

### Key Findings
- The exact formula `factorialCheckCount n = l+1` (where l is the level of n) makes the
  "level structure" of the problem explicit in Lean
- The bound theorem `factorialCheckCount_le_log` holds for ALL n, not just n ≥ 2
- `factorialCheckCount_const_on_interval` confirms checks are level-uniform — different primes
  at the same level have identical check counts (e.g., 461, 557, 673 all = 6)

### Files Modified
- `proofs/Proofs/Erdos1059OQ01.lean`: 340 → 396 lines, 2 new theorems, strengthened 2 existing

### Next Steps
- Prove density_one_conjecture from selberg_density_axiom (OQ-02) once PNT/Brun-Titchmarsh available
- The tighter asymptotic factorialCheckCount(n) = Θ(log n / log log n) would require Stirling
- Cross-namespace: connect OQ-01 density conjecture to OQ-02 Selberg axiom via quantitative sieve
