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

---

## Session 2026-04-04 (Session 3) - Density Gap and Sandwich Theorems

**Mode**: REVISIT
**Outcome**: progress

### What I Did

1. **Proved `three_not_qualifying`** (native_decide): p = 3 fails AllFactorialSubtractionsComposite.
   Witness: 3 - 0! = 2 is prime. Simplest non-qualifying prime.

2. **Proved `qualifyingPrimeCount_lt_primeCount`**: For all x ≥ 3, C(x) < π(x).
   Uses `Finset.ssubset_def`: qualifying-prime finset ⊊ prime finset, as 3 ∈ π(x) \ C(x).
   **Significance**: Density is strictly < 1 at every finite stage.

3. **Proved `qualifyingPrimeCount_pos`**: For x ≥ 101, 0 < C(x).
   native_decide for C(101) = 1 > 0; monotonicity for x ≥ 101.

4. **Proved `density_strictly_between`**: For x ≥ 101, 0 < C(x) < π(x).
   Combined density sandwich: density strictly between 0 and 1 at every finite stage ≥ 101.

5. Build: 0 sorries, 0 warnings, 1 axiom. 396 → 456 lines.

### Key Findings
- Gap theorem uses only that 3 is prime and 3 - 0! = 2 is prime — completely elementary
- 48 level-6 witnesses in (720, 5040): 769, 937, 967, 1009, 1201, ... (Python-computed)
- density_one_conjecture and selberg_density_axiom are genuinely independent without PNT

### Files Modified
- `proofs/Proofs/Erdos1059OQ01.lean`: 396 → 456 lines, 4 new theorems
- `src/data/proofs/erdos-1059-oq-01/meta.json`: updated description, counts, contributions
- `research/problems/erdos-1059-oq-01/knowledge.md`: this session

### Next Steps
- Brun-Titchmarsh + PNT (both missing from Mathlib) needed to eliminate density_one_conjecture
- Tighter check count: factorialCheckCount(n) ≤ log n / log log n (Stirling-free approach feasible)
- Add more level-6 witnesses only if concrete density bounds are needed

---

## Session 2026-04-04 (Session 4) - OQ-04: density_one_conjecture → ErdosProblem1059

**Mode**: REVISIT
**Outcome**: completed (new OQ-04 file)

### What I Did

1. **Created `Erdos1059OQ04.lean`** (new file, 0 sorries, 1 axiom via import):
   Proves `density_one_conjecture → ErdosProblem1059` (infinitely many qualifying primes).

   Key lemmas:
   - `primeCount_mono`: π(x) ≤ π(y) for x ≤ y. Direct Finset.card_le_card argument on the
     `(Finset.range (x+1)).filter Nat.Prime` filter.
   - `primeCount_unbounded`: ∀ n, ∃ x, π(x) ≥ n. Proved by induction: inductive step finds
     prime p > x via `Nat.exists_infinite_primes`, shows the filter for primeCount p strictly
     contains filter for primeCount x (p ∈ former, p ∉ latter), so π(p) > π(x) ≥ k.
   - `density_implies_unbounded`: If all qualifying primes ≤ N, then C(x) = C(N) for x ≥ N.
     `density_one_conjecture 1` gives X with 2·C(x) ≥ π(x) for x ≥ X. For x ≥ max(X,N):
     π(x) ≤ 2·C(N) = 2B. But `primeCount_unbounded (2B+1)` gives y with π(y) ≥ 2B+1.
     Taking max(y, max(X,N)) gives π ≤ 2B and π ≥ 2B+1. Contradiction via omega.
   - `density_implies_infinite`: Set.infinite_iff_exists_gt + density_implies_unbounded.

2. **Fixed `qualifyingPrimeCount_ge_eight`** in OQ-01: the previous proof used a 3-component
   constructor `⟨by simp; norm_num, by decide, by native_decide⟩` for `Finset.mem_filter.mpr`.
   `by decide` was closing the entire `Prime ∧ AFSC` goal, leaving no goal for `by native_decide`.
   Fixed by writing explicit `have h101 : 101 ∈ ...`, `have h211 : 211 ∈ ...`, etc. for all 8
   witnesses, then using `rcases hx with rfl | rfl | ...` to dispatch.

### Key Findings
- OQ-04 proves a second independent route to ErdosProblem1059 beyond OQ-02 (Selberg sieve)
- The induction proof of `primeCount_unbounded` avoids `Nat.nth` and `Nat.count` entirely —
  simpler and more robust than the Nat.count approach
- `Nat.count` in Lean 4 Mathlib is defined via `List.countP` (not `Finset.card ∘ filter`),
  making bridging to our Finset-based `primeCount` non-trivial; direct induction avoided this

### Files Modified
- `proofs/Proofs/Erdos1059OQ04.lean`: created (191 lines, 4 theorems, 0 sorries, 1 axiom)
- `proofs/Proofs/Erdos1059OQ01.lean`: fixed qualifyingPrimeCount_ge_eight (2 lines changed)

### Next Steps
- Prove density_one_conjecture from selberg_density_axiom (requires PNT/Brun-Titchmarsh)
- Add gallery data for OQ-04 in `src/data/proofs/erdos-1059-oq-04/`
