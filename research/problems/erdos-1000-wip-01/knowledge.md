# Research Knowledge: erdos-1000-wip-01

## Problem
Complete Erdős #1000: Generalized Totients and Diophantine Approximation.
The existing formalization has 4 axioms (erdos_no_zero_limit, erdos_dichotomy, cassels_liminf_zero, haight_resolution) and 0 sorries. Goal: prove one or more axioms.

## Summary
Session 1 proved structural lower bounds. Session 2 proved the complement formula and 6 more infrastructure theorems, establishing the framework for proving erdos_no_zero_limit via a double-counting argument.

## Session 2026-03-25 (Session 1) - Structural Lower Bound

**Mode**: FRESH
**Outcome**: progress

### What I Did
- Proved `phiA_ge_totient`: φ_A(k) ≥ φ(n_k) for any increasing sequence A
  - Key insight: coprime elements always pass the phiA filter
  - If gcd(m, n_k) = 1, then reducedDenom m n_k = n_k > n_j for all j < k
  - Proof: subset argument — (range n).filter(Coprime n) ⊆ (Icc 1 n).filter(phiA_cond)
- Proved `densityRatio_ge_totient_ratio`: ρ_A(k) ≥ φ(n_k)/n_k
- Fixed Mathlib API migration issues (∑ in → ∈, omega, division lemmas)

### Key Findings
- Lower bound φ_A(k) ≥ φ(n_k) is NOT sufficient for erdos_no_zero_limit
  - φ(n_k)/n_k CAN go to 0 (e.g., primorial sequence)
  - Need deeper structural argument

## Session 2026-03-26 (Session 2) - Complement Formula

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- Proved `phiA_add_used`: φ_A(k) + Σ_{used e|n_k} φ(e) = n_k (complement formula)
  - Uses Finset.sum_filter_add_sum_filter_not + Nat.sum_totient
- Proved `used_sum_le`: used φ-sum ≤ n_k - φ(n_k)
  - n_k is always unused; from phiA_add_used + phiA_ge_totient
- Proved `used_card_le`: at most k divisors are used
  - Each used divisor maps injectively to j < k via A.seq
- Proved `phiA_pos`: φ_A(k) ≥ 1
- Proved `densityRatio_pos`: ρ_A(k) > 0
- Proved `densityRatio_complement`: ρ_A(k) = 1 - used/n_k in ℝ
- Proved `densityRatio_ge_of_prime`: ρ_A(k) ≥ 1/2 when n_k is prime

### Key Findings
- Complement formula reframes erdos_no_zero_limit: for ρ → 0, used divisors must capture almost ALL of n_k's φ-sum. At most k divisors can do this, and n_k is always excluded.
- **erdos_no_zero_limit proof approach**: Double-count Σ_k (1-ρ_A(k)). Switch sum order: Σ_j φ(n_j) · Σ_{k>j: n_j|n_k} 1/n_k. Inner sum = reciprocals of multiples of n_j in the sequence. Bound by harmonic sum → contradiction.
- Blocked on: formalizing the double-counting + real-valued sum bounds

### Files Modified
- `proofs/Proofs/Erdos1000Problem.lean` — 7 new theorems (370→607 lines)
- `src/data/proofs/erdos-1000/meta.json` — updated
- `src/data/research/problems/erdos-1000-wip-01.json` — updated

### Next Steps
- Formalize the double-counting argument for erdos_no_zero_limit
- Alternative: prove for special cases first (lacunary, prime-rich sequences)
- cassels_liminf_zero requires continued fraction construction (longer-term)

## Session 2026-03-26 (Session 3) - Infrastructure for erdos_no_zero_limit

**Mode**: REVISIT
**Outcome**: progress

### What I Did
Added 11 new infrastructure theorems toward proving erdos_no_zero_limit:

1. **Filter helpers**:
   - `not_densityToZero_of_frequently_ge`: if ρ ≥ c > 0 frequently, then ¬DensityToZero
   - `not_densityToZero_of_frequently_prime`: prime-rich sequences can't have ρ → 0
2. **Base case**: `usedSum_zero`: usedSum A 0 = 0
3. **Bounds**:
   - `densityRatio_ge_inv`: ρ ≥ 1/n_k (absolute lower bound)
   - `cesaroAvg_ge_totient_avg`: Cesàro ≥ average of φ(n_k)/n_k
4. **Unused-divisor analysis**:
   - `phiA_ge_unused_subset`: any subset of unused divisors bounds φ_A below
   - `divisor_gt_prev_unused`: d > n_{k-1} implies d is unused
   - `phiA_ge_large_divisor_sum`: φ_A ≥ sum of totients of large divisors
   - `phiA_ge_self_and_quotient`: with p-fold gap, φ_A ≥ φ(n_k) + φ(n_k/p)
5. **Deficit-sum analysis**:
   - `sum_deficit_eq_sum_used_ratio`: Σ(1-ρ) = Σ usedSum/n (identity)
   - `sum_deficit_lt`: Σ(1-ρ) < N (strict deficit bound)
6. **Positivity**: `cesaroAvg_pos`: C_A(N) > 0 for N > 0

### Key Findings
- **Pointwise bounds are insufficient**: ρ ≥ φ(n)/n can → 0 (primorials), so the complement formula + structural argument is essential
- **Double-counting bound is too loose**: Σ(1-ρ) ≤ O(N log N) via harmonic bounds, but ρ → 0 only requires Σ(1-ρ) ~ N. The O(N) vs O(N log N) gap prevents a contradiction.
- **The proof of erdos_no_zero_limit likely requires**: (a) analytic NT results about φ(n)/n distribution (Mertens' theorem), or (b) a tighter structural argument about divisibility pairs, or (c) exploiting the tension between growth rate (fast growth → few used divisors) and divisor density (many small primes → φ/n small but forces fast growth)
- The **prime-rich case** is now completely handled by `not_densityToZero_of_frequently_prime`

### Files Modified
- `proofs/Proofs/Erdos1000Problem.lean` — 11 new theorems (607 → 796 lines)
- `src/data/proofs/erdos-1000/meta.json` — updated
- `src/data/research/problems/erdos-1000-wip-01.json` — updated

### Next Steps
- Find or build Mathlib infrastructure for Mertens-type bounds on φ(n)/n
- Alternatively: formalize the sum-switching identity and tighter pair bounds
- The core challenge: bounding Σ_j φ(n_j) · Σ_{k>j: n_j|n_k} 1/n_k more tightly than O(N log N)

## Session 2026-03-26 (Session 4) - Growth Bound and Multiplicity Infrastructure

**Mode**: REVISIT
**Outcome**: progress

### What I Did
- Proved `usedSum_le_card_mul`: usedSum(k) ≤ k · n_{k-1} — growth bound on used divisors
  - Each used divisor e = n_j has φ(e) ≤ e ≤ n_{k-1}, and there are at most k of them
- Proved `densityRatio_ge_one_sub_growth`: ρ_A(k) ≥ 1 - k·n_{k-1}/n_k
  - From complement formula + growth bound
- Proved `densityRatio_gt_half_of_fast_growth`: ρ > 1/2 when n_k > 2k·n_{k-1}
- Proved `not_densityToZero_of_fast_growth`: sequences with frequent super-linear growth can't have ρ→0
- Proved `phiA_ge_seq_sub_growth`: φ_A(k) ≥ n_k - k·n_{k-1}
- Defined `divPairs`, `divPairs_fiber_k`, `divPairs_fiber_j` — vocabulary for double-counting
- Proved `divPairs_fiber_j_card_le`: multiplicity bound |{k > j : n_j | n_k, k < N}| ≤ n_{N-1}/n_j
  - Via injective map k ↦ n_k/n_j into Ico 1 (M+1)

### Key Findings
- **Growth bound reframes the problem**: For ρ → 0, need usedSum ≈ n_k, so k·n_{k-1} ≥ n_k. This constrains the sequence to grow at most linearly: n_k ≤ O(k·n_{k-1}).
- **Special case proved**: Sequences growing faster than 2k·n_{k-1} (super-exponential, factorial, lacunary) can't have ρ→0.
- **Double-counting vocabulary established**: divPairs and fiber definitions set up the sum-switching identity needed for the general proof.
- **Multiplicity bound proved**: at most n_{N-1}/n_j multiples of n_j in the sequence. This is the key ingredient for bounding the switched sum.

### Files Modified
- `proofs/Proofs/Erdos1000Problem.lean` — 6 new theorems, 3 new definitions (796→935 lines)
- `src/data/proofs/erdos-1000/meta.json` — updated counts
- `src/data/research/problems/erdos-1000-wip-01.json` — updated

### Next Steps
- Formalize the sum-switching identity: Σ usedSum(k)/n_k = Σ_j φ(n_j) · Σ_{k>j,n_j|n_k} 1/n_k
- Use multiplicity bound + growth bound to derive contradiction from ρ→0
- Alternative: prove Mertens-type lower bound φ(n)/n ≥ c/log(log(n)) for more direct proof

## Session 2026-03-26 (Session 5) - Axiom Elimination: erdos_no_zero_limit

**Mode**: REVISIT
**Outcome**: progress (axiom eliminated)

### What I Did
- **Proved erdos_no_zero_limit from erdos_dichotomy** (3→2 axioms)
  - Key insight: erdos_no_zero_limit is a direct corollary of erdos_dichotomy
  - If ρ → 0, then ρ < ε eventually, hence frequently (Eventually.frequently)
  - By erdos_dichotomy, ρ > 1 - ε frequently
  - Taking ε = 1/2: ρ < 1/2 eventually but ρ > 1/2 frequently — contradiction
  - Proof is 10 lines, uses the same patterns as cassels_liminf_zero and not_densityToZero_of_frequently_ge

### Key Findings
- The no-zero-limit theorem does NOT need its own deep argument (double-counting, Mertens). It follows purely from the dichotomy via elementary filter theory.
- The extensive infrastructure built in sessions 1-4 (growth bounds, multiplicity, double-counting) is still valuable for eventually proving erdos_dichotomy itself.
- Two axioms remain: erdos_dichotomy (deep — needs Euler product), haight_resolution (deep — needs explicit construction)

### Files Modified
- `proofs/Proofs/Erdos1000Problem.lean` — erdos_no_zero_limit: axiom → theorem
- `src/data/proofs/erdos-1000/meta.json` — axiomCount: 3 → 2
- `src/data/research/problems/erdos-1000-wip-01.json` — updated

### Next Steps
- Prove erdos_dichotomy: requires Euler product φ(n)/n = Π(1-1/p), smooth number theory
- Prove haight_resolution: requires explicit construction of highly composite sequence

## Session 2026-03-28 (Session 6+7) - Growth Constraints and Euler Bridge

**Mode**: REVISIT
**Outcome**: progress

### What I Did
Added 8 new infrastructure theorems in two batches:

**Batch 1 (Growth Constraints)**:
- `low_density_growth_constraint`: (1-ε)n_k < k·n_{k-1} when ρ < ε — slow growth forced
- `consecutive_low_density_ratio`: n_{k+1}/n_k < (k+1)/(1-ε) for consecutive low ρ
- `cesaroAvg_eq_one_sub_avg_deficit`: C_A(N) = 1 - avg(1-ρ) — Cesàro-deficit duality
- `deficit_count_bound`: m low-ρ indices contribute ≥ m(1-ε) to total deficit
- `density_somewhere_pos`: Σ ρ_k > 0 for N > 0

**Batch 2 (Euler-Totient Bridge)**:
- `low_density_euler_bound`: ρ < ε ⟹ φ(n)/n < ε — bridge to prime factorization
- `densityRatio_recovery_from_growth`: n_{k+1} > C·n_k ⟹ ρ_{k+1} ≥ 1-(k+1)/C

### Key Findings
- **Growth constraint from low density**: ρ < ε forces n_{k+1}/n_k < (k+1)/(1-ε), constraining growth to at most factorial speed during low-ρ periods
- **Deficit counting insufficient**: Among N indices, m with ρ < ε gives m(1-ε) ≤ Σ(1-ρ) < N, so m < N/(1-ε). Since 1/(1-ε) > 1, this doesn't limit proportion below 1.
- **Euler product NOT in Mathlib as single theorem**: φ(n)/n = ∏(1-1/p) must be composed from `totient_prime_pow`, `totient_mul`, etc. Not a single theorem.
- **Recovery mechanism**: When growth resumes after slow period, ρ recovers via densityRatio_recovery_from_growth. The tension between slow growth (forced by low ρ) and strict monotonicity is the structural driver of the dichotomy.
- **Both remaining axioms are deep**: erdos_dichotomy needs Euler product + smooth number bounds; haight_resolution needs explicit constructive argument. Each likely requires 200+ lines of non-trivial proof.

### Files Modified
- `proofs/Proofs/Erdos1000Problem.lean` — 8 new theorems (1003→1119 lines)
- `src/data/proofs/erdos-1000/meta.json` — updated counts
- `src/data/research/problems/erdos-1000-wip-01.json` — updated

### Next Steps
- Build the Euler product formula φ(n)/n = ∏(1-1/p) from Mathlib primitives
- Use it to formalize: ρ < ε ⟹ n_k has all primes ≤ B_ε as factors
- Formalize the smooth-number counting argument for erdos_dichotomy
- Alternative: try haight_resolution via explicit primorial-based construction
- Both are deep results requiring significant Mathlib infrastructure
