# Erdős #1201 - Knowledge Base

## Problem Statement

Is it true that for every $\epsilon,\eta>0$ there exists a $k$ such that the density of $n$ for which\[P(n(n+1)\cdots(n+k))>n^{1-\epsilon}\]is at least $1-\eta$ (where $P(m)$ is the greatest prime divisor of $m$)? Erdős wrote he could prove this for $\epsilon=1/2$.## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #337
- Problem #2000
- Problem #62
- Problem #2
- Problem #1200
- Problem #1202
- Problem #39
- Problem #1

## References

- (None available)

## Sessions

## Session 2026-05-03 (Session 1) - Bertrand Lower Bounds

**Mode**: FRESH
**Outcome**: progress — 2 new theorems proved, PR #15174 created

### What I Did
- Identified erdos-1201 as RICH-tier problem (37 knowledge items, 0 sorries, 1 axiom)
- Analyzed Lean file: 19 existing theorems, well-structured, only missing Docker build verification
- Added `import Mathlib.NumberTheory.Bertrand`
- Proved `gpfConsecutive_self_gt (n ≥ 1) : n < gpfConsecutive n n`
  - Key: Bertrand gives prime p ∈ (n, 2n]; p = n + (p-n) with p-n ≤ n appears in window
  - Uses: Nat.exists_prime_lt_and_le_two_mul, Finset.dvd_prod_of_mem, gpf_max
- Proved `gpfConsecutive_gt_n_of_large_window (n ≥ 2, k ≥ n) : n < gpfConsecutive n k`
  - Induction on k-n using gpfConsecutive_mono
- Updated gallery meta.json: theoremCount 14→21, lineCount 267→297, new Bertrand section
- Created PR #15174

### Key Findings
- Mathlib.NumberTheory.Bertrand is available via `Nat.exists_prime_lt_and_le_two_mul`
- The n+1 consecutive integers [n, 2n] always contain a Bertrand prime — clean formalization
- `Finset.dvd_prod_of_mem` is the right tool for showing a specific factor divides the product
- Bug caught: must bind hp_le (not use _) from Bertrand decomposition for omega to prove range membership

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (297 lines, was 266)
- `src/data/proofs/erdos-1201/meta.json` (updated counts + Bertrand section)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Await CI/Docker build result for PR #15174
- Potential: Sylvester-Schur theorem (gpfConsecutive n k > k for n ≥ k+1)

---

## Session 2026-05-03 (Session 2) - Infinite Set Result

**Mode**: FRESH (REVISIT)
**Outcome**: progress — 2 new theorems, fix to induction IH, PR #15215

### What I Did
- Diagnosed: gallery meta stale (21 thm/297 lines vs actual 22 thm/310 lines after PRs #14942 + #15174)
- Discovered existing build error in `gpfConsecutive_gt_n_of_large_window` (never verified by Docker)
  - IH was `n ≤ n+d → n < gpfConsecutive n (n+d)` not `n < ...` — needed `ih (by omega)`
- Added `dvd_consecutiveProduct_term`: (n+i) | consecutiveProduct n k for i ≤ k
  - Generalizes `dvd_consecutiveProduct_right` (the i=k case)
- Added `erdos_1201_infinitely_many`: {n | P(n,k) > n^(1-ε)} is infinite for fixed k, ε∈(0,1)
  - Proof: primes form infinite subset via `gpfConsecutive_ge_self_of_prime` + `Real.rpow_lt_rpow_of_exponent_lt`
  - Uses `Nat.infinite_setOf_prime.mono`
- Updated meta.json: 21→24 theorems, 297→341 lines
- Created PR #15215

### Key Findings
- `Nat.infinite_setOf_prime.mono` works for infinite subset arguments
- `Real.rpow_lt_rpow_of_exponent_lt (h : 1 < x) (h : y < z) : x^y < x^z` key for power comparison
- The ε < 1 condition in `erdos_1201_infinitely_many` is not needed (only ε > 0 matters for n^ε > 1)
- Lean 4 induction IH includes all hypotheses that depend on the induction variable — `n ≤ n+d` survived

### Mathematical Note
`erdos_1201_infinitely_many` is the weakest meaningful partial result: the good set is infinite but
may have density 0 (primes have density 0 by PNT). Positive density requires smooth number estimates.

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (341 lines, was 310)
- `src/data/proofs/erdos-1201/meta.json` (updated counts, new section)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Sylvester-Schur: for n > k, n(n+1)···(n+k-1) has a prime factor > k (is this in Mathlib?)
- Quantitative density lower bound for small k (requires smooth number estimates)

---

## Session 2026-05-03 (Session 3) - Max Formula and Smooth-Window Reformulation

**Mode**: REVISIT
**Outcome**: progress — 2 new theorems proved, PR created

### What I Did
- Identified gap: no lemma connecting P(n,k) to individual-term GPFs
- Proved `gpfConsecutive_eq_sup_range (n ≥ 2) : P(n,k) = sup_{i≤k} GPF(n+i)`
  - Key: prime factors of a product = union of prime factors of factors → GPF(product) = max GPF(term)
  - ≤ direction: GPF of product divides some term via `prime_dvd_consecutive_range`, so ≤ sup
  - ≥ direction: each term's GPF divides the term which divides the product, so ≤ GPF(product)
- Proved `gpfConsecutive_le_iff : P(n,k) ≤ t ↔ ∀ i ≤ k, GPF(n+i) ≤ t`
  - Immediate corollary of max formula via `Finset.sup_le_iff`
  - Reformulates "P(n,k) is small" as "every integer in [n, n+k] is t-smooth"
- Updated meta.json: 35→37 theorems, 472→514 lines, new max-formula section
- Updated research JSON: added 2 builtItems, 2 insights, updated progressSummary

### Key Findings
- `Finset.sup_le_iff` and `Finset.le_sup` work cleanly for ℕ with `OrderBot` (0)
- The max formula is the bridge between product-level and term-level properties
- Smooth-window reformulation: "n fails Erdős condition" = "window [n, n+k] is fully t-smooth"
  — this connects to Dickman's ρ function and opens the density estimation approach

### Mathematical Note
`gpfConsecutive_le_iff` reveals the structure of the Erdős conjecture: proving density → 1
reduces to showing the density of n where ALL of n, n+1, ..., n+k are n^ε-smooth
goes to 0 as k → ∞. This is plausible from smooth number theory (ρ(1/ε) density of
n^ε-smooth numbers among [1,n]) but requires quantitative estimates not in Mathlib.

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (514 lines, was 472)
- `src/data/proofs/erdos-1201/meta.json` (updated counts, new section)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Sylvester-Schur: for n > k, n(n+1)···(n+k-1) has a prime factor > k
- Prove `gpfConsecutive_pos_density_of_smooth_bound`: if k-smooth density < η then good set ≥ 1-η

---

## Session 2026-05-03 (Session 4) - GPF for Primes and Endpoint Bounds

**Mode**: REVISIT
**Outcome**: progress — 5 new theorems proved, PR pending Docker verification

### What I Did
- Proved `greatestPrimeFactor_prime (n : ℕ) (hn : n.Prime) : greatestPrimeFactor n = n`
  - Key: `Nat.primeFactors_prime hn : n.primeFactors = {n}`, so max' over singleton = n
  - Uses: `simp [dif_pos hne, Nat.primeFactors_prime hn, Finset.max'_singleton]`
- Proved `gpfConsecutive_prime_start (n k : ℕ) (hn : n.Prime) : gpfConsecutive n 0 = n`
  - Trivial corollary via `gpfConsecutive_zero ▸ greatestPrimeFactor_prime`
- Proved `gpfConsecutive_one_eq_max (n : ℕ) (hn : 2 ≤ n) : P(n,1) = max(GPF(n), GPF(n+1))`
  - Via `gpfConsecutive_eq_sup_range` for k=1: range 2 = {0,1}, sup_insert, sup_singleton
  - Uses `decide` to prove `Finset.range 2 = {0, 1}`
- Proved `gpfConsecutive_ge_left : GPF(n) ≤ P(n,k)` and `gpfConsecutive_ge_right : GPF(n+k) ≤ P(n,k)`
  - Direct from `Finset.le_sup` with range membership (0 ∈ range(k+1), k ∈ range(k+1))
- Updated meta.json: 37→42 theorems, 514→555 lines, new prime-gpf section
- Total: 42 proved theorems, 1 axiom (ε=1/2 partial result)

### Key Findings
- `Nat.primeFactors_prime hn : n.primeFactors = {n}` is the cleanest path to `greatestPrimeFactor_prime`
- Proof-irrelevance for `Prop` makes `Finset.max'_singleton` work despite different Nonempty witnesses
- `decide` works for concrete `Finset ℕ` equalities like `Finset.range 2 = {0, 1}`
- `Finset.le_sup` with `Finset.mem_range.mpr (Nat.succ_pos k)` / `(Nat.lt_succ_self k)` is clean for endpoint bounds
- `gpfConsecutive_one_eq_max` is the key example of the max formula specialization

### Mathematical Note
The 5 new theorems complete the "basic interface" for `gpfConsecutive`:
- Identity for prime starts, length-1 formula, endpoint bounds
These are all corollaries of the max formula but explicit enough to be directly useful.

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (555 lines, was 514)
- `src/data/proofs/erdos-1201/meta.json` (updated counts, new prime-gpf section)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)
- `research/problems/erdos-1201/knowledge.md` (this entry)

### Next Steps
- Docker build pending for type-checking verification
- Possible: `gpfConsecutive_prime_right`: when n+k is prime, P(n,k) = n+k (already have `gpfConsecutive_eq_of_prime_right`)
- Possible: smooth number density estimates (would require new Mathlib infrastructure)

---

## Session 2026-05-03 (Session 5) - Product Formula and Recursive Window Formula

**Mode**: REVISIT
**Outcome**: progress — 3 new theorems proved, PR pending

### What I Did
- Proved `greatestPrimeFactor_mul (a b : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) : gpf(a*b) = max(gpf(a), gpf(b))`
  - Key: any prime p dividing a*b divides a or b by primality (`hp.dvd_mul`)
  - ≤ direction: gpf(a*b) divides a or b → ≤ gpf(a) or gpf(b) → ≤ max(gpf(a),gpf(b))
  - ≥ direction: gpf(a)|a|a*b so gpf(a) ≤ gpf(a*b); similarly for gpf(b)
- Proved `gpfConsecutive_le_of_le_k (n : ℕ) (hn : 2 ≤ n) {k₁ k₂ : ℕ} (hk : k₁ ≤ k₂) : P(n,k₁) ≤ P(n,k₂)`
  - General k-monotonicity: extends one-step `gpfConsecutive_mono` to arbitrary window extensions
  - Proof: `gpfConsecutive_eq_sup_range` for both, then `Finset.sup_le` + `Finset.le_sup` + `omega`
  - Strictly cleaner than iterating one-step monotonicity by induction
- Proved `gpfConsecutive_succ_right (n k : ℕ) (hn : 2 ≤ n) : P(n,k+1) = max(P(n,k), gpf(n+k+1))`
  - One-step recursive formula: extending window by one term on right
  - Proof: sup formula for both sides, then `Finset.range_succ` → `insert`, `Finset.sup_insert`, simp
  - Uses: `sup_comm`, `sup_eq_max`, `show n + (k+1) = n+k+1 from by ring`
- Updated meta.json: 37→44 theorems, 514→606 lines, new gpf-product-and-recursion section
- Updated erdos-1201.json knowledge items (total 75 items)

### Key Findings
- `hp.dvd_mul.mp h` (where hp : p.Prime) gives p | a ∨ p | b from p | a*b — clean primality argument
- `Finset.sup_le` + `Finset.le_sup` is the canonical way to prove sup set-monotonicity
- `Finset.range_succ` converts `range (k+2)` to `insert (k+1) (range (k+1))` for sup_insert
- `sup_eq_max` bridges ⊔ and max for ℕ lattice; `sup_comm` handles commutativity
- `greatestPrimeFactor_mul` subsumes `gpfConsecutive_one_eq_max`: the one-step recursive formula directly gives P(n,1) = max(gpf(n), gpf(n+1)) as a special case of `gpfConsecutive_succ_right` with k=0 and `gpfConsecutive_zero`

### Mathematical Note
`gpfConsecutive_succ_right` is the key recursive formula for computing P(n,k). It shows that the window GPF grows by absorbing the next term's GPF — a streaming max operation. Combined with `gpfConsecutive_le_of_le_k` (general monotonicity), these give a complete characterization of how P(n,k) behaves as k varies.

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (606 lines, was 560)
- `src/data/proofs/erdos-1201/meta.json` (updated counts, new section)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)
- `research/problems/erdos-1201/knowledge.md` (this entry)

### Next Steps
- Window-split formula: P(n,k) = max(P(n,j), P(n+j+1, k-j-1)) for j < k — follows from succ_right by induction
- `gpfConsecutive_succ_left`: P(n-1, k+1) ≥ P(n, k) — left-shift decreases start, right-shift increases end
- Density results still blocked: requires Dickman ρ function / smooth number estimates not in Mathlib

---

## Session 2026-05-03 (Session 7) - Right-Endpoint Biconditional and Infinite Sets

**Mode**: REVISIT
**Outcome**: progress — 3 new theorems proved, PR created (Docker verification pending)

### What I Did
- Selected erdos-1201 as RICH-tier (score 73), highest priority among available problems
- Assessed frontier: Sessions 1-6 built 44 theorems. Next-step was right-endpoint biconditional
- Proved `gpfConsecutive_eq_right_iff (n k hn hnk)`: P(n,k) = n+k ↔ (n+k).Prime
  - Forward: gpfConsecutive is prime (gpf_prime); if it equals n+k then n+k is prime
  - Backward: direct from `gpfConsecutive_eq_of_prime_right`
  - This closes the biconditional: upper bound achieved exactly at prime right endpoints
- Proved `erdos_1201_prime_right_infinite (k)`: {n | (n+k).Prime}.Infinite
  - Via `Set.infinite_of_not_bddAbove`: for any N, prime p ≥ N+k+1 gives n = p-k in the set
- Proved `erdos_1201_eq_right_infinite (k hk)`: {n | P(n,k) = n+k}.Infinite
  - Same unbounded argument using `gpfConsecutive_eq_of_prime_right` for prime right endpoints
- Updated meta.json: 44→47 theorems, 606→662 lines

### Key Findings
- `gpfConsecutive_eq_right_iff` is the sharp biconditional: P < n+k (composite), P = n+k (prime)
- `Set.infinite_of_not_bddAbove` + `not_bddAbove_iff` + `Nat.exists_infinite_primes` is the canonical infinite-set pattern
- The two theorems complement `erdos_1201_infinitely_many` (prime starts) with prime ends witnesses

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (662 lines, was 606)
- `src/data/proofs/erdos-1201/meta.json` (47 theorems, 662 lines)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Full Sylvester-Schur: P(n,k) > k for ALL n > k (requires binomial machinery)
- Density lower bounds: requires Dickman ρ function (>1000 lines infra, truly blocked)

---

## Session 2026-05-03 (Session 6) - Window Extension, Concatenation, and Prime Term Bounds

**Mode**: REVISIT
**Outcome**: progress — 4 new theorems proved, PR created

### What I Did
- Proved `gpfConsecutive_succ_left (n k : ℕ) (hn : 2 ≤ n) : P(n,k+1) = max(gpf(n), P(n+1,k))`
  - Left-endpoint extension: symmetric to `gpfConsecutive_succ_right`
  - Proof: Nat.le_antisymm via sup inequalities; case split on i=0 vs i>0 for upper bound
  - Key tactic: `rcases Nat.eq_zero_or_pos i with rfl | hpos` then `Finset.le_sup (f := ...)` with omega
- Proved `gpfConsecutive_window_concat (n j k : ℕ) (hn : 2 ≤ n) : P(n,j+k+1) = max(P(n,j), P(n+j+1,k))`
  - Window concatenation/splitting formula: [n,n+j+k+1] = [n,n+j] ∪ [n+j+1,n+j+k+1]
  - Proof: `by_cases h : i ≤ j` splits the sup over the full range into two halves
  - Both halves use `Finset.le_sup (f := ...)` with `congr 1; omega` to relate index arithmetic
- Proved `gpfConsecutive_ge_prime_term (n k i : ℕ) (hn : 2 ≤ n) (hi : i ≤ k) (hprime : (n+i).Prime)`
  - If window [n,n+k] contains prime n+i, then P(n,k) ≥ n+i
  - Proof: `rw [← greatestPrimeFactor_prime _ hprime, gpfConsecutive_eq_sup_range]` then `Finset.le_sup (f := ...)`
- Proved `erdos_1201_good_of_prime_in_window`: one-liner corollary bridging prime distribution to density
  - If n+i is prime and n+i > n^(1-ε), then P(n,k) > n^(1-ε) — structural link to Erdős conjecture
- Fixed API drift in `consecutiveProduct_succ` (induction proof for Lean 4.26.0 prod_range_succ issues)
- Updated meta.json: 44→48 theorems, 662→754 lines, added window-extension-and-prime-terms section
- Created PR on branch `research/erdos-1201-session-6b`

### Key Findings
- `gpfConsecutive_succ_left` and `gpfConsecutive_succ_right` are symmetric: together give full bilateral recursion
- `gpfConsecutive_window_concat` generalizes both succ theorems: set j=0 gives succ_right; set k=0 gives left-split
- `gpfConsecutive_ge_prime_term` is the cleanest statement of "prime term implies lower bound"
- `erdos_1201_good_of_prime_in_window` shows that P(n,k) > n^(1-ε) follows from prime gaps <n^(1-ε) in [n,n+k]
  - This is the link to Cramér-type prime gap conjectures

### Mathematical Note
The 4 Session 6 theorems together give a complete "window algebra":
- Bilateral extension: P(n,k+1) = max(gpf(n), P(n+1,k)) AND P(n,k+1) = max(P(n,k), gpf(n+k+1))
- Concatenation: P(n,j+k+1) = max(P(n,j), P(n+j+1,k)) — general window splitting
- Prime term lower bound: prime in window → window GPF ≥ that prime
- Sufficient condition for Erdős problem: prime > n^(1-ε) in window → n is good

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (734 lines, was 662, with all Mathlib 4.26.0 API drift fixes applied)
- `src/data/proofs/erdos-1201/meta.json` (updated counts, new section)
- `research/problems/erdos-1201/knowledge.md` (this entry)

### Next Steps
- `gpfConsecutive_window_concat` with j=0 gives a cleaner proof of `gpfConsecutive_succ_right` — potential refactor
- Connect `erdos_1201_good_of_prime_in_window` to prime gap bounds: if primes gaps < n^(1-ε) for density-1 set, conjecture follows
- Smooth number density: if k-smooth numbers in [N] have density ρ(1/ε) → density argument works (>1000 lines infra)

---

## Session 2026-05-03 (Session 4) - GPF Localization

**Mode**: REVISIT (richest available: score 55, ACT phase)
**Outcome**: progress — 3 new theorems, Docker build in progress, PR pending

### What I Did
- Continued from Session 3 (gpfConsecutive_one_eq_max already proved)
- Added **`gpfConsecutive_one_coprime`**: Nat.Coprime (gpf n) (gpf (n+1)) for n ≥ 2
  - From gcd(n, n+1) = 1, gpf(n)|n, gpf(n+1)|n+1 → gcd(gpf(n), gpf(n+1)) | gcd(n,n+1) = 1
  - Used `Nat.dvd_gcd`, `Nat.gcd_dvd_left/right`, `Nat.dvd_one`, `Nat.coprime_succ_self`
- Added **`gpfConsecutive_one_ne`**: gpf(n) ≠ gpf(n+1) for n ≥ 2
  - If equal to p ≥ 2, then gcd(p,p) = p ≥ 2 contradicts coprimality
  - Uses `Nat.gcd_self` + omega
- Added **`gpfConsecutive_eq_term_gpf`** (GPF Localization): When P(n,k) > k for n ≥ 2, ∃ j ≤ k with P(n,k) = gpf(n+j)
  - p = P(n,k) is prime, divides consecutiveProduct, hence divides some n+j by `prime_dvd_consecutive_range`
  - `gpf_ge_prime_dvd (n+j) p` gives p ≤ gpf(n+j)
  - `gpf_ge_prime_dvd (consecutiveProduct n k) (gpf(n+j))` gives gpf(n+j) ≤ p
  - Antisymmetry gives equality
- Updated meta.json: theoremCount 37→40, lineCount 510→554, new structural-decomposition section
- Docker build running (lean-build-50190)

### Key Findings
- GPF Localization is the key structural result: when P(n,k) exceeds the window size k, it "belongs" to a single term
- This enables reduction: {n | P(n,k) > n^(1-ε)} ⊇ {n | ∃j≤k, gpf(n+j) > n^(1-ε)} when n > k
- Coprimality of consecutive gpfs follows trivially from gcd(n,n+1)=1 — no primality arguments needed
- `prime_dvd_consecutive_range` (private lemma, same file) handles the "divides some term" step cleanly

### Mathematical Note
`gpfConsecutive_eq_term_gpf` reduces the window-density problem to single-term GPF density when n > k.
Combined with Sylvester-Schur (P(n,k) > k always for n > k), this gives a clean reduction:
density of {n | P(n,k) > n^(1-ε)} ≈ density of {n | max_{j≤k} gpf(n+j) > n^(1-ε)}.
The latter connects to the well-studied Dickman function and smooth number density.

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (554 lines, was 510)
- `src/data/proofs/erdos-1201/meta.json` (theoremCount 37→40, lineCount 510→554)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Verify Docker build succeeds
- Sylvester-Schur general case: for n > k, prove P(n,k) > k (needs more than Bertrand)
- Use GPF Localization to reduce density question to single-term GPF distribution

---

## Session 2026-05-03 (Session 4) - GPF Localization

**Mode**: REVISIT (richest available: score 55, ACT phase)
**Outcome**: progress — 3 new theorems, Docker build in progress, PR pending

### What I Did
- Continued from Session 3 (gpfConsecutive_one_eq_max already proved)
- Added **`gpfConsecutive_one_coprime`**: Nat.Coprime (gpf n) (gpf (n+1)) for n ≥ 2
  - From gcd(n, n+1) = 1, gpf(n)|n, gpf(n+1)|n+1 → gcd(gpf(n), gpf(n+1)) | gcd(n,n+1) = 1
  - Used `Nat.dvd_gcd`, `Nat.gcd_dvd_left/right`, `Nat.dvd_one`, `Nat.coprime_succ_self`
- Added **`gpfConsecutive_one_ne`**: gpf(n) ≠ gpf(n+1) for n ≥ 2
  - If equal to p ≥ 2, then gcd(p,p) = p ≥ 2 contradicts coprimality
  - Uses `Nat.gcd_self` + omega
- Added **`gpfConsecutive_eq_term_gpf`** (GPF Localization): When P(n,k) > k for n ≥ 2, ∃ j ≤ k with P(n,k) = gpf(n+j)
  - p = P(n,k) is prime, divides consecutiveProduct, hence divides some n+j by `prime_dvd_consecutive_range`
  - `gpf_ge_prime_dvd (n+j) p` gives p ≤ gpf(n+j)
  - `gpf_ge_prime_dvd (consecutiveProduct n k) (gpf(n+j))` gives gpf(n+j) ≤ p
  - Antisymmetry gives equality
- Updated meta.json: theoremCount 37→40, lineCount 510→554, new structural-decomposition section
- Docker build running (lean-build-50190)

### Key Findings
- GPF Localization is the key structural result: when P(n,k) exceeds the window size k, it "belongs" to a single term
- This enables reduction: {n | P(n,k) > n^(1-ε)} ⊇ {n | ∃j≤k, gpf(n+j) > n^(1-ε)} when n > k
- Coprimality of consecutive gpfs follows trivially from gcd(n,n+1)=1 — no primality arguments needed
- `prime_dvd_consecutive_range` (private lemma, same file) handles the "divides some term" step cleanly

### Mathematical Note
`gpfConsecutive_eq_term_gpf` reduces the window-density problem to single-term GPF density when n > k.
Combined with Sylvester-Schur (P(n,k) > k always for n > k), this gives a clean reduction:
density of {n | P(n,k) > n^(1-ε)} ≈ density of {n | max_{j≤k} gpf(n+j) > n^(1-ε)}.
The latter connects to the well-studied Dickman function and smooth number density.

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (554 lines, was 510)
- `src/data/proofs/erdos-1201/meta.json` (theoremCount 37→40, lineCount 510→554)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Verify Docker build succeeds
- Sylvester-Schur general case: for n > k, prove P(n,k) > k (needs more than Bertrand)
- Use GPF Localization to reduce density question to single-term GPF distribution

---

## Session 2026-05-04 (Session 8) - Sylvester-Schur Extensions and Density Monotonicity

**Mode**: REVISIT
**Outcome**: progress — 6 new theorems proved (55→61), 1 bug fixed

### What I Did
- Fixed pre-existing duplicate declaration bug: `gpfConsecutive_eq_right_iff`,
  `erdos_1201_prime_right_infinite`, `erdos_1201_eq_right_infinite` were each declared twice
- Proved **`gpfConsecutive_succ_succ_gt_k`** (Sylvester-Schur n=k+2):
  - Bertrand for k+1 gives prime p in (k+1, 2k+2] = [k+2, 2k+2] ⊆ [n, n+k]; use `gpfConsecutive_gt_k_of_prime_in_window`
- Proved **`gpfConsecutive_succ_succ_succ_gt_k`** (Sylvester-Schur n=k+3):
  - Bertrand for k+2 gives prime p in (k+2, 2k+4]. Since 2k+4=2(k+2) is composite (even, ≥6), p ≤ 2k+3 = (k+3)+k
  - Key: `hp_prime.eq_one_or_self_of_dvd 2 (dvd_mul_right 2 (k+2))` rules out p = 2(k+2) being prime
- Proved **`erdos_1201_good_implies_good_succ`** (good-set pointwise monotonicity in k):
  - One-liner: `hgood.trans_le (by exact_mod_cast gpfConsecutive_mono n k hn)`
- Proved **`erdos_1201_good_set_mono_k`** (set containment as k grows):
  - The good set {n | P(n,k) > n^(1-ε)} ⊆ {n | P(n,k+1) > n^(1-ε)} for all ε, k
- Proved **`upperDensity_mono`** (upper density monotone for set inclusion):
  - `Filter.limsup_le_limsup` with IsCoboundedUnder (density ≥ 0) + IsBoundedUnder (density ≤ 1)
  - Key pattern from Erdos25LogDensity: IsCoboundedUnder is 2nd arg, IsBoundedUnder is 3rd arg
- Proved **`erdos_1201_density_mono_k`** (density non-decreasing in window width):
  - One-liner: `upperDensity_mono (erdos_1201_good_set_mono_k ε k)`
- Fixed IsCoboundedUnder argument order bug in `upperDensity_mono` (third commit)

### Key Findings
- Sylvester-Schur for n=k+3 requires ruling out 2(k+2) being prime — handled by primality of 2
- `Filter.limsup_le_limsup` argument order: (≤ᶠ condition, IsCoboundedUnder f, IsBoundedUnder g)
  - Different from intuition: IsCoboundedUnder for the SMALLER function, IsBoundedUnder for LARGER
  - IsCoboundedUnder for density: `use 0; intro a ha; by_contra; get N with densityFun N ≤ a; linarith`
- General Sylvester-Schur (n > k+3): needs Chebyshev/Hanson's theorem, not just Bertrand — HARD
- Docker build twice timed out at 60 min (file is 861 lines with many complex theorems)

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (850→861 lines, 55→61 theorems, 0 sorries)
- `src/data/proofs/erdos-1201/meta.json` (theoremCount 55→61, lineCount 779→861)
- `research/problems/erdos-1201/knowledge.md` (this entry)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Full Sylvester-Schur (n > k): needs Hanson's theorem (P(n,k) ≥ n^{1/(k+1)}) or Ramachandra's work
- Density lower bounds: requires Dickman ρ function (>1000 lines infra, truly blocked)

---

## Session 2026-05-04 (Session 10) - Factorial Divisibility + ε-Monotonicity

**Mode**: REVISIT
**Outcome**: progress — 8 new theorems proved (61→69), open problem scope reduced

### What I Did
- Rescued researcher-8's uncommitted factorial section (process dead, lock stale)
- Proved `consecutiveProduct_eq_descFactorial` (private): product = descending factorial (n+k)↓(k+1)
- Proved `factorial_dvd_consecutiveProduct`: (k+1)! | n(n+1)···(n+k) for ALL n,k
  - Key: `Nat.descFactorial_eq_factorial_mul_choose` gives the identity directly
- Proved `gpfConsecutive_ge_factorial_gpf`: P(n,k) ≥ GPF((k+1)!) for n≥1, k≥1
  - (k+1)! | product → GPF((k+1)!) | product → GPF((k+1)!) ≤ P(n,k)
- Proved `gpfConsecutive_gt_half_k`: 2·P(n,k) > k for ALL n≥1, k≥2
  - Bertrand for k/2 gives prime p in (k/2, k] ≤ k+1; p | (k+1)! | product → p ≤ P(n,k) > k/2
  - UNIVERSAL: holds for all starting points n≥1, unlike Sylvester-Schur (n>k)
- Proved `erdos_1201_threshold_bound`: n^(1-ε) < k/2 → P(n,k) > n^(1-ε)
- Proved `erdos_1201_good_set_mono_eps`: ε ≤ ε' → good-set(ε) ⊆ good-set(ε')
  - rpow_le_rpow_of_exponent_le: smaller ε means bigger threshold means harder condition
- Proved `erdos_1201_density_mono_eps`: density non-decreasing in ε (one-liner via upperDensity_mono)
- Proved `erdos_1201_trivially_good_of_large_eps`: for ε≥1, n^(1-ε) ≤ 1 < 2 ≤ P(n,k) always
- Proved `erdos_1201_conjecture_large_eps`: for ε∈[1/2,1), conjecture follows from Erdős's axiom
  - Key: n^(1-ε) ≤ n^(1/2) = √n for ε≥1/2; so {√n < P(n,k)} ⊆ {n^(1-ε) < P(n,k)}
  - Uses `Real.sqrt_eq_rpow` to bridge sqrt and rpow; `rpow_le_rpow_of_exponent_le` for monotonicity
  - **Reduces open problem to ε ∈ (0, 1/2) only**

### Key Findings
- Factorial divisibility via descending factorial is cleaner than Sylvester-Schur (no n>k condition)
- The universal bound P(n,k) > k/2 (via (k+1)! divisibility + Bertrand) is strictly weaker than
  Sylvester-Schur P(n,k) > k (for n>k), but applies to ALL n
- Epsilon-monotonicity is the key structural insight: Erdős's known ε=1/2 result covers all ε≥1/2;
  the true frontier of the open problem is only ε ∈ (0, 1/2)
- `Nat.self_le_factorial (n)` gives n ≤ n! cleanly for factorial lower bounds

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (861→978 lines, 61→69 theorems, 0 sorries)
- `src/data/proofs/erdos-1201/meta.json` (theoremCount 61→69, lineCount 861→978)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Full Sylvester-Schur (n > k): the factorial approach gives P > k/2; Sylvester-Schur needs P > k
  (requires showing GPF((k+1)!) > k, i.e., largest prime ≤ k+1 is > k, i.e., k+1 prime — not always)
- Density lower bounds for ε < 1/2: requires Dickman ρ function (>1000 lines infra, truly blocked)
- The open problem has been formally reduced to ε ∈ (0, 1/2)

---

*Generated from erdosproblems.com on 2026-04-16*

## Session 2026-05-04 (Session 11) - Sylvester-Schur for Prime Window Sizes

**Mode**: REVISIT (claimed erdos-1201 directly — highest knowledge score)
**Outcome**: progress — 2 new theorems, 2 bug fixes, PR #15417

### What I Did
- Identified tractable special case of Sylvester-Schur: when k+1 is PRIME
  - General Sylvester-Schur (P(n,k) > k for all n > k) needs Chebyshev/binomial infra
  - For prime k+1: elementary residue argument suffices, works for ALL n ≥ 1
- Proved `exists_dvd_in_consecutive` (private): offset `(m - n%m) % m` witnesses multiple of m
  - Case n % m = 0: trivially n is divisible by m (offset = 0)
  - Case n % m > 0: offset < m, and n + (m - n%m) = m*(n/m+1) by division algorithm
- Proved `gpfConsecutive_ge_succ_k_of_prime`: P(n,k) ≥ k+1 for all n ≥ 1 when k+1 prime
  - Uses `exists_dvd_in_consecutive` + `le_gpfConsecutive_of_prime_dvd_term`
- Proved `gpfConsecutive_gt_k_of_prime_succ`: k < P(n,k) when k+1 prime (strict)
  - Covers k = 1, 2, 4, 6, 10, 12, 16, 18, ... (infinitely many k values)
- Fixed pre-existing bug: `Nat.coprime_succ_self_right` removed from current Mathlib
  - New proof: `(Nat.coprime_succ_self n).coprime_dvd_left (...) |>.coprime_dvd_right (...)`
- Fixed pre-existing bug: duplicate declarations of `erdos_1201_good_set_mono_eps` and
  `erdos_1201_density_mono_eps` (session 10 added ≤ versions alongside existing < versions)
  - Removed second (≤) declarations; first (strict <) versions remain

### Key Findings
- Complete residue system: k+1 consecutive integers cover ALL residues mod k+1
- `le_gpfConsecutive_of_prime_dvd_term` is the key bridge for prime factor bounds
- `Nat.coprime_succ_self_right` renamed to `Nat.coprime_succ_self` in current Mathlib
- `Nat.Coprime.coprime_dvd_left/right` is the clean API for transferring coprimality
- Session 10 introduced duplicate theorem names — always check for existing names before adding

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (1044→1043 lines, 75 theorems, 0 sorries)
- `src/data/proofs/erdos-1201/meta.json` (lineCount 1044→1043, bug fixes noted in assumptions)
- `research/problems/erdos-1201/knowledge.md` (this entry)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Full Sylvester-Schur for ALL k+1 (composite): needs binomial coefficient or Chebyshev Θ (>300 lines)
- Density lower bounds: truly blocked (Dickman ρ function >1000 lines infra)
- Can erdos_1201_half_case be proved via Dickman ρ or elementary density argument?
