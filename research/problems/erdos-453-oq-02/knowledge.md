# erdos-453-oq-02

**Problem**: Can the axioms in Erdős Problem #453 be proved from Mathlib?

## Current State (origin/main)

`proofs/Proofs/Erdos453OQ02.lean` (227 lines): **0 sorries, 2 axioms**.

Reduced from parent `Erdos453Problem.lean` (4 axioms, 1 sorry) by proving:
- `nthPrime_is_prime` from `Nat.nth_mem_of_infinite Nat.infinite_setOf_prime`
- `nthPrime_strictMono` from `Nat.nth_strictMono Nat.infinite_setOf_prime`
- `nthPrime_values` (p₁=2, p₂=3, p₃=5, p₄=7) from `Nat.nth_prime_*_eq_*` + `Nat.nth_count` for index 3

Plus full `convexity_implies_product_bound` and `pomerance_1979` chain from the two remaining axioms.

## Remaining Axioms (Both Deep)

### 1. `logPrime_ratio_tendsto_zero`

```lean
axiom logPrime_ratio_tendsto_zero :
    Filter.Tendsto (fun n => logPrime n / n) Filter.atTop (nhds 0)
```

**Mathematical content**: log p_n / n → 0 as n → ∞.

**What this is, mathematically**: Direct corollary of PNT. Since p_n ~ n log n (PNT inverse form), log p_n ~ log n + log log n, so log p_n / n → 0.

**Mathlib path** (estimated 200-300 lines):
1. PNT is in `Mathlib.NumberTheory.LSeries` family. Find the form `(π(n) * log n) / n → 1` or `Nat.tendsto_primeCounting_atTop` style.
2. Invert PNT to get `Nat.nth Nat.Prime n / (n * log n) → 1` (this is the harder direction; not always packaged in Mathlib alongside the forward PNT).
3. From p_n ~ n log n, get log p_n / n = (log n + log log n + o(1)) / n → 0.
4. Bridge to the file's 1-indexed `nthPrime n = if n=0 then 0 else Nat.nth Nat.Prime (n-1)`.

**Tractability assessment**: Likely doable within a 500-line session if Mathlib has the inverse PNT statement; multi-session if it has only the forward statement. Worth searching Mathlib for `Nat.tendsto_nth_prime` or `Nat.nth_prime_atTop_log` style names.

### 2. `pomerance_convex_hull_lemma`

```lean
axiom pomerance_convex_hull_lemma (a : ℕ → ℝ)
    (h : Filter.Tendsto (fun n => a n / n) Filter.atTop (nhds 0)) :
    ∀ N : ℕ, ∃ n ≥ N, IsConvexHullVertex a n
```

**Mathematical content**: For any sub-linear sequence, infinitely many points are upper-convex-hull vertices.

**Mathlib path** (estimated 800+ lines): Mathlib does not currently have convex-hull theory for *discrete* ℕ → ℝ sequences (`Mathlib.Analysis.Convex.Basic` is for `ℝᵈ` / linear-algebra style). Would need to:
1. Define discrete upper convex hull as a subset of ℕ.
2. Prove the "infinitely many vertices" lemma for sub-linear sequences (a is the basic discrete-convex-hull combinatorial argument).
3. Apply to `logPrime`.

**Tractability assessment**: Out of scope for a single research session; this is genuine Mathlib-gap infrastructure.

## Tractable Follow-Up Questions (per SOLVED guidance)

1. **Quantified Pomerance**: Pomerance (1979) actually proves an asymptotic density: the number of n ≤ N where p_n² > p_{n-i}p_{n+i} for all i is ≥ c·log log N for some c > 0. Stating and axiomatizing the *quantitative* form would be a sharper companion theorem.

2. **Connection to Erdős #455**: The related problem #455 asks whether p_{n+1}² ≥ p_n · p_{n+2} infinitely often (a special case of Pomerance with i=1). A short corollary `pomerance_1979 → erdos_455` would bridge the two gallery entries.

## Session 1 (2026-04-27) — SURVEY

**Mode**: FRESH (claimed MODERATE, score 7)
**Outcome**: SURVEY — file is at SOLVED-with-deep-axioms state; documented axiom-elimination paths and follow-up questions

### What I Did (and Did Not Do)
- Did NOT run a full Docker build (skipped to conserve cycles after two prior drift hits this session). The file's imports are conservative (Nat.Prime, Real.Log, Convex.Basic) and unrelated to the 2026-04-26 Mathlib drift cohort, so the file is expected to build, but unverified this session.
- Did NOT attempt to prove either axiom (out-of-scope for one session per estimates above).
- Created this knowledge.md (didn't exist before) with proof paths and follow-ups.

### Why Not Add Theorems
Per role spec: "Adding theorems on top of unproved axioms is scaffolding, not formalization." Rather than burying the deep axioms under more downstream lemmas, this session documents *how* to eliminate them.

### Files Modified
- `research/problems/erdos-453-oq-02/knowledge.md` — created
- `src/data/research/problems/erdos-453-oq-02.json` — `progressSummary` clarified, follow-up questions added to nextSteps, Session 1 insight added

### Next Steps (priority order)
1. **Search Mathlib for inverse PNT** — `Nat.tendsto_nth_prime_div_id_log` or similar. If present, attempt `logPrime_ratio_tendsto_zero` (~200-300 lines).
2. Add `erdos_455_corollary` (Pomerance with i=1 specialization) — small bridge between gallery entries (~30 lines).
3. State and axiomatize the quantitative Pomerance density (≥ c·log log N vertices) — sharper companion result.
4. (Long-term) Build discrete convex hull theory in Mathlib — out-of-scope here but the right place is `Mathlib.Analysis.Convex.SpecificFunctions` or a new file under `Mathlib.Combinatorics`.
