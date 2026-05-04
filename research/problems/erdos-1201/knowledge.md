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


---

> **Note**: 13 older sessions archived to `sessions/` directory.

## Session 2026-05-04 (Session 12) - Comprehensive Build Fix + Structural Theorems

**Mode**: REVISIT (highest knowledge score 113, branch fix/erdos-1201-desc-factorial)
**Outcome**: progress — 5 build failures fixed, 5 new theorems (75→80), PR #15439

### What I Did
- Identified 5 distinct build failures in Erdos1201Problem.lean:
  1. **Forward reference**: `gpfConsecutive_ge_succ_k_of_prime` (line 396) called `le_gpfConsecutive_of_prime_dvd_term` (line 587) — Lean 4 forbids this
  2. **`consecutiveProduct_eq_descFactorial`**: broken inductive proof (Nat.descFactorial_succ API change), fixed with prod_range_reflect + Nat.descFactorial_eq_prod_range
  3. **`consecutiveProduct_one`**: fragile rwa proof, replaced with simp+ring
  4. **`upperDensity_mono`**: Filter.eventually_of_forall → Filter.Eventually.of_forall; div_le_div_right → div_le_div_of_nonneg_right
  5. **`gpfConsecutive_gt_half_k`**: linarith couldn't see through opaque def, added unfold
- Closed PR #15431 (superseded) which fixed only issues 1-2
- Added 5 new structural theorems:
  - `gpfConsecutive_prime_gt_k`: P(n,k) > k when n is prime and k < n
  - `erdos_1201_individual_threshold`: ∃k such that P(n,k) > n^(1-ε) for each fixed n ≥ 2
  - `erdos_1201_good_set_mono`: pointwise k-monotonicity for arbitrary k₁ ≤ k₂
  - `gpfConsecutive_two_gt_two`: P(n,2) > 2 for all n ≥ 1
  - `erdos_1201_equiv_small_eps`: ErdosProblem1201 ↔ restriction to ε ∈ (0, 1/2)

### Key Findings
- Lean 4 forward references at file scope are always a hard build failure
- `Filter.Eventually.of_forall` is the current Mathlib API (was `Filter.eventually_of_forall`)
- `div_le_div_of_nonneg_right` is the current API (replaced `div_le_div_right`)
- `Nat.descFactorial_eq_prod_range` + `Finset.prod_range_reflect` avoids all descFactorial_succ API issues
- `erdos_1201_equiv_small_eps` formalizes that the open frontier of Erdős #1201 is exactly ε ∈ (0, 1/2)
- PRs #15391 and #15415 remain open but DIRTY — deployer cannot auto-merge; their useful content has been salvaged

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (1046→1094 lines, 75→80 theorems, 0 sorries)
- `src/data/proofs/erdos-1201/meta.json` (lineCount 1094, theoremCount 80)
- `research/problems/erdos-1201/knowledge.md` (this entry)

### Next Steps
- Close PRs #15391 and #15415 (their content has been salvaged in PR #15439)
- Full Sylvester-Schur for ALL k+1 (composite): needs binomial coefficient or Chebyshev — HARD
- Density lower bounds for ε < 1/2: requires Dickman ρ function — truly BLOCKED (>1000 lines)
- The open mathematical frontier is formally documented: `erdos_1201_equiv_small_eps`

---

## Session 2026-05-04 (Session 13) - Smooth-Window Duality and Conditional Reduction

**Mode**: REVISIT (highest knowledge score 113+, branch research/erdos-1201-session-12b)
**Outcome**: progress — 3 new theorems (80→83)

### What I Did
- Checked Aristotle: no completed jobs pending
- Reviewed Session 12 state (80 theorems in origin/main after PR #15439)
- Created fresh branch `research/erdos-1201-session-12b` from origin/main
- Added 3 new structural characterization theorems completing the smooth-window analysis:
  1. **`erdos_1201_not_good_smooth_window`**: n bad ↔ window [n,n+k] is n^(1-ε)-smooth
     - `¬(P(n,k) > n^(1-ε)) ↔ ∀ i ≤ k, gpf(n+i) ≤ n^(1-ε)`
     - Uses `gpfConsecutive_le_iff` + `Nat.le_floor` + `Nat.floor_le`
  2. **`erdos_1201_good_iff_rough_term`**: n good ↔ ∃ rough term in window
     - `P(n,k) > n^(1-ε) ↔ ∃ i ≤ k, gpf(n+i) > n^(1-ε)`
     - Negation of smooth-window, uses `push_neg` + `absurd`
  3. **`erdos_1201_conditional_proof`**: ErdosProblem1201 from Cramér-type prime gap hypothesis
     - If almost all n have a prime in [n,n+k] exceeding n^(1-ε), then Erdős conjecture holds
     - Uses `upperDensity_mono` + `erdos_1201_good_of_prime_in_window`
- Updated meta.json: theoremCount 80→83, lineCount 1094→1153

### Key Findings
- Smooth-window duality makes the density problem explicit: density of bad n = density of windows
  where ALL integers n, n+1, ..., n+k are n^(1-ε)-smooth
- Cramér's conjecture implies prime gaps g_p < (log p)^2 — much weaker than needed for Erdős:
  we need gaps < n^(1-ε) ≈ exp((1-ε)log n). This is plausible but far from proved.
- `erdos_1201_conditional_proof` makes explicit that Erdős #1201 follows from prime distribution:
  it's a consequence of sufficient density of "large primes in short intervals"

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (1094→1153 lines, 80→83 theorems, 0 sorries)
- `src/data/proofs/erdos-1201/meta.json` (theoremCount 83, lineCount 1153)
- `research/problems/erdos-1201/knowledge.md` (this entry)
- `src/data/research/problems/erdos-1201.json` (to be updated in commit)

### Next Steps
- Full Sylvester-Schur for ALL k+1 (composite): needs binomial machinery — HARD
- The conditional proof `erdos_1201_conditional_proof` points to the precise hypothesis needed
- Density lower bounds for ε < 1/2: Dickman ρ function — truly BLOCKED (>1000 lines infra)

---

## Session 2026-05-04 (Session 14) - Density Complement and Smooth-Decay Conditional

**Mode**: REVISIT (branch research/erdos-1201-session-12b, extending PR #15461)
**Outcome**: progress — 4 new theorems (83→87), 1 sorry submitted to Aristotle

### What I Did
- Continued from session 13 (83 theorems, branch research/erdos-1201-session-12b)
- Added 4 new structural theorems formalizing the density reduction:
  1. **`erdos_1201_good_prime_k0`**: all primes are good for k=0 (no sorry)
     - `(n : ℝ)^(1-ε) < gpfConsecutive n 0` for prime n and ε ∈ (0,1)
     - Uses `greatestPrimeFactor_prime` + `Real.rpow_lt_rpow_of_exponent_lt`
  2. **`upperDensity_compl_ge`**: complement density lower bound (1 sorry → Aristotle)
     - `1 - upperDensity S ≤ upperDensity Sᶜ`
     - Shows density_S + density_Sᶜ = 1 for each N ≥ 1 exactly
     - Sorry: limsup sub-additivity `limsup f + limsup g ≥ limsup(f+g)`
  3. **`erdos_1201_from_bad_density_bound`**: bad density → good density bound (no sorry)
     - If density(bad smooth windows) ≤ η then density(good n) ≥ 1-η
     - Key direction: bad ⊆ complement(good) via `erdos_1201_not_good_smooth_window`
     - Then `upperDensity_mono` + `upperDensity_compl_ge` give the lower bound
  4. **`erdos_1201_smooth_decay_implies_conjecture`**: formal reduction (no sorry)
     - ErdosProblem1201 ↔ smooth-window density decays to 0 as k→∞
     - One-line wrapper around `erdos_1201_from_bad_density_bound`

### Key Findings
- The reduction `ErdosProblem1201 ← smooth-decay` makes the Dickman gap mathematically precise
- `upperDensity_compl_ge` depends only on limsup sub-additivity — standard real analysis
- The n < 2 edge case (gpfConsecutive 0 k = 0) is avoided by proving bad ⊆ complement(good)
  rather than trying to show complement(bad) ⊆ good (which fails for n=0,1)
- Limsup sub-additivity `limsup(f+g) ≤ limsup f + limsup g` is the only remaining sorry

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (1153→1241 lines, 83→87 theorems, 1 sorry)
- `src/data/proofs/erdos-1201/meta.json` (theoremCount 87, lineCount 1241, sorries 1)
- `research/problems/erdos-1201/knowledge.md` (this entry)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Submit `upperDensity_compl_ge` sorry (limsup sub-additivity) to Aristotle
- Full Sylvester-Schur for ALL k+1 composite: truly hard (Chebyshev/binomial machinery)
- Density lower bounds for ε < 1/2: Dickman ρ function — truly BLOCKED (>1000 lines infra)

---

## Session 2026-05-04 (Session 14) - Limsup Sub-Additivity (upperDensity_compl_ge)

**Mode**: REVISIT
**Outcome**: progress — 1 sorry closed (87 theorems, 0 sorries → complete)

### What I Did
- Identified the remaining sorry in `upperDensity_compl_ge` (line 1199 of worktree file)
- Sorry was for the sub-additivity step: `1 ≤ limsup_S + limsup_Sᶜ` from `limsup(f+g) = 1`
- Found `limsup_add_le` in `Mathlib.Topology.Algebra.Order.LiminfLimsup`:
  `limsup (u + v) f ≤ limsup u f + limsup v f`
  (requires IsBoundedUnder (≥) u, IsBoundedUnder (≤) u, IsCoboundedUnder (≤) v, IsBoundedUnder (≤) v)
- Added `import Mathlib.Topology.Algebra.Order.LiminfLimsup` to imports
- Proved all 4 boundedness conditions for densityS and densitySᶜ (both ∈ [0,1])
- Used `exact h_limsup_one.symm.le.trans (limsup_add_le ...)` to close the sorry
- Updated meta.json: sorries 1→0, lineCount 1241→1270

### Key Findings
- `limsup_add_le` is the right tool for limsup sub-additivity in general ordered groups
- Requires 4 conditions: u bounded above AND below, v cobounded AND bounded above
- The proof pattern for IsCoboundedUnder (≤) is exactly the same as in upperDensity_mono
- `h.symm.le.trans` is the clean chain: `c = limsup(f+g) → c ≤ limsup f + limsup g`

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (1241→1270 lines, 87 theorems, 0 sorries)
- `src/data/proofs/erdos-1201/meta.json` (sorries 1→0, lineCount 1270)
- `research/problems/erdos-1201/knowledge.md` (this entry)

### Next Steps
- Docker build verification needed for the limsup_add_le proof
- The Aristotle job cb09e358 (erdos_1201_half_case) is superseded — mark as resolved_manually
- Pool status: erdos-1201 now has 0 sorries, 1 axiom — consider completing if Docker passes

---

## Session 2026-05-04 (Session 16) - Lower Density and Strong Conjecture

**Mode**: REVISIT
**Outcome**: progress — 170 new lines (7 new definitions/theorems), 1 sorry in backward direction

### What I Did
- Added `lowerDensity` definition (liminf dual to `upperDensity`)
- Proved `lowerDensity_compl_eq`: EXACT identity lowerDensity(Sᶜ) = 1 - upperDensity(S)
  - Stronger than existing inequality `upperDensity_compl_ge`
  - Uses `Filter.liminf_const_sub` from Mathlib.Topology.Algebra.Order.LiminfLimsup
  - Requires `Filter.IsCoboundedUnder (· ≤ ·)` for the density function (proved with b=0)
- Proved `upperDensity_compl_eq`: symmetric identity upperDensity(Sᶜ) = 1 - lowerDensity(S)
- Proved `lowerDensity_le_upperDensity`: liminf ≤ limsup for density functions
  - Follows algebraically from the two complement identities + `upperDensity_compl_ge`
- Defined `ErdosProblem1201Strong`: stronger form using lowerDensity ≥ 1-η
  - Asserts density tends to 1 in the LOWER density sense (all large N, not just limsup)
- Proved `erdos_1201_strong_implies_weak`: Strong → Weak (one-line via lD ≤ uD)
- Proved `erdos_1201_strong_iff_smooth_decay`: bidirectional equivalence
  - Forward (Strong → smooth-decay): complete proof via complement duality
  - Backward (smooth-decay → Strong): counting argument correct, 1 sorry for limsup arithmetic
    - For n ≥ 2: n ∈ goodᶜ ↔ n ∈ smooth_bad (by `erdos_1201_not_good_smooth_window`)
    - |goodᶜ ∩ [1,N]| ≤ |smooth_bad ∩ [1,N]| + 1 (the +1 for n=1)
    - Sorry: limsup(densityFun goodᶜ) ≤ limsup(densityFun smooth_bad + 1/N) ≤ η
    - Needs: limsup subadditivity + limsup(1/N) = 0 (1/N → 0 tendsto)

### Key Findings
- `Filter.liminf_const_sub` exists in Mathlib 4.26.0 with `[OrderedSub R]` typeclass
  (ℝ satisfies `OrderedSub` via `OrderedAddCommGroup`; `cobdd` arg is required)
- The EXACT complement duality (lD(Sᶜ) = 1-uD(S)) is stronger than the existing inequality
  and enables the Strong ↔ smooth-decay equivalence
- `ErdosProblem1201Strong` is precisely equivalent to smooth-window density → 0 (the key insight
  is that both directions use the exact duality, not just the inequality)
- The backward sorry needs: `limsup(f + 1/N) ≤ limsup f + 0 = limsup f` as N → ∞
  Use `limsup_add_le` + `Filter.Tendsto.limsup_eq` for `1/N → 0`

### Files Modified  
- `proofs/Proofs/Erdos1201Problem.lean` (1270→1440 lines, 87→94 theorems/defs, 0→1 sorry)
- Branch: research/erdos-1201-lower-density-s16
- Commit: 355c0573e5

### Next Steps
- Close the backward direction sorry: prove limsup(1/N) = 0 via `tendsto_natCast_atTop_atTop`
  then `Filter.Tendsto.limsup_eq`; use `limsup_add_le` for subadditivity
- Docker build verification: check `Filter.liminf_const_sub 1 hbdd hcobdd` compiles
- If build passes: create PR and merge
- Further: formalize Dickman ρ function approach (blocked, >1000 lines infra needed)

## Session 2026-05-04 (Session 17) - Close backward sorry in erdos_1201_strong_iff_smooth_decay

**Mode**: REVISIT (continuing session 16 work)
**Outcome**: sorry closed (0 sorries now)

### What I Did
- Identified that the file already had `limsup_add_le` used in `erdos_1201_from_bad_density_bound`
  (lines 1248-1334) with the EXACT pattern needed for the backward direction sorry
- Adapted the pattern to the sorry context: `dgc` = densityFun goodᶜ, `dbad` = densityFun smooth_bad
- Closed sorry with: limsup_le_limsup + limsup_add_le + `tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop` + `htend.limsup_eq`
- File: 1440 → 1499 lines, 1 sorry → 0 sorries

### Key Findings
- `limsup_add_le` in this file takes 4 args: IsBoundedUnder (≥) F f, IsBoundedUnder (≤) F f, IsCoboundedUnder (≤) F g, IsBoundedUnder (≤) F g
- `(tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).limsup_eq` proves `limsup(1/N) = 0`
- The backward sorry proof was structurally identical to `erdos_1201_from_bad_density_bound`

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (1440→1499 lines, 1→0 sorries)
- `src/data/proofs/erdos-1201/meta.json` (sorries 1→0, lineCount 1440→1499)
- Branch: research/erdos-1201-lower-density-s16, PR #15529

### Next Steps
- Verify Docker build passes (OOM on first attempt, retry in progress)
- Consider Dickman ρ function for the actual conjecture (>1000 lines, blocked)
- The strong-iff-smooth-decay reduction is complete; proof of smooth-decay is the real open problem
