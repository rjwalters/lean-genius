# Knowledge Base: erdos-1-oq-02-incomplete-01

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

## Session 2026-06-28 (researcher-3) — SURVEY: probability-free discharge route for `anticoncentration_bound`

**Mode**: SURVEY. **Outcome**: no code change (axiom discharge is a multi-session BUILD); documented a
cleaner, measure-theory-free proof path for the one remaining axiom.

### State
`Erdos1OQ02.lean` is complete except for the single axiom
`anticoncentration_bound : 2^|A| ≤ 3·√(Σaᵢ²) + 2` (for distinct-subset-sums A). 0 sorries.

### Recommended discharge: discrete second moment (NO probability theory)
The in-file note suggests Mathlib's Chebyshev (`ProbabilityTheory.meas_ge_le_variance_div_sq`),
which drags in a probability space / measure. A fully **combinatorial** route is cleaner and
strictly elementary:

1. **Second-moment identity** (pure `Finset.powerset` algebra, 0 probability):
   with `S = Σaᵢ`, `Q = Σaᵢ²`, for `χ_T(i) = +1 if i∈T else −1`,
   `2·(T.sum id) − S = ∑_i χ_T(i) aᵢ`, so
   `∑_{T ∈ A.powerset} (2·T.sum id − S)² = 2^n · Q`.
   Proof: expand the square to `∑_i aᵢ² + ∑_{i≠j} χ(i)χ(j)aᵢaⱼ`; sum over T. The diagonal gives
   `2^n·Q`; each off-diagonal `∑_T χ_T(i)χ_T(j) = 0` (pair-up subsets by toggling membership of i).
2. **Distinct-integer spread bound** (elementary, no analysis): the `2^n` subset sums are
   `2^n` *distinct integers*, so `{2·T.sum − S}` are `2^n` distinct integers of one parity;
   for any `M` distinct integers `v_j` and any center `c`, `∑(v_j − c)² ≥ (M³ − M)/12`
   (minimised by `M` consecutive integers; provable by an exchange/rearrangement induction).
   With `M = 2^n`, `c = 0`: `2^n·Q = ∑(2T.sum−S)² ≥ ((2^n)³ − 2^n)/12`, hence
   `Q ≥ ((2^n)² − 1)/12`, giving `2^n ≤ √(12Q + 1) ≤ 3√Q + 2` (loosen constants to absorb +1).

This avoids `MeasureTheory`/`ProbabilityTheory` entirely; both steps are `Finset`/`Int` algebra +
one rearrangement induction. Estimated ~150–220 lines. Step 1 (the identity) is a self-contained
verified lemma worth landing first; step 2's distinct-integer-spread lemma is reusable elsewhere.

### Next steps (revised)
1. Land the second-moment identity `∑_{T∈A.powerset}(2·T.sum id − S)² = 2^|A|·Σaᵢ²` as a standalone
   0-axiom lemma (powerset sum + off-diagonal cancellation via membership-toggle bijection).
2. Prove the distinct-integer spread `∑(v_j − c)² ≥ (M³−M)/12` for M distinct integers.
3. Combine to discharge `anticoncentration_bound`, eliminating the file's last axiom.

## Session 2026-06-28 (researcher-2) — BUILD: landed step 1 + the Chebyshev tail (0-axiom)

Added to `Erdos1OQ02.lean` (241→322 lines, +2 theorems, all 0-axiom; verified via
`lake env lean`), in a new "Verified ingredients toward discharging" section right
after the axiom:

- **`second_moment_identity`** (step 1, DONE): `∑_{T∈A.powerset} (2·(∑_{i∈T} i) − S)²
  = 2^|A| · Σaᵢ²` over `ℤ` (S = A.sum). Proof: `Finset.induction` + `Finset.sum_powerset_insert`;
  inserting `a` sends each drop `d` to the pair `d±a`, and `(d−a)²+(d+a)² = 2d²+2a²`
  gives the recurrence `f(A∪{a}) = 2f(A) + 2^{|A|+1}a²` matching `2^{|A|}Q`. Cleaner
  than the survey's "expand + off-diagonal cancellation" — no bijection bookkeeping.
- **`card_mul_le_second_moment`** (the discrete Chebyshev/Markov tail): for nonneg `g`,
  `#{i : t ≤ g i}·t ≤ ∑ g i`. Elementary (`Finset.sum_le_sum_of_subset_of_nonneg`).

### CORRECTION to the survey's combine step (IMPORTANT for the next BUILD)
The survey's *pure second-moment* route (step 2: spread `∑(v−c)² ≥ (M³−M)/12`) only
yields `2ⁿ ≤ √(12Q+1) ≈ 3.46√Q`, which is **WEAKER** than the axiom's `3√Q + 2`
(for large Q, `√(12Q+1) − 3√Q = (√12−3)√Q → ∞`). To recover the sharp constant `3`
you must instead use the **central-interval count**: the `2ⁿ` doubled drops
`2·Σ_T − S` are distinct integers of one fixed parity (`≡ S mod 2`), so at most
`t+1` of them lie in `(−t, t)`; with `t = 2√Q`, the Chebyshev tail
(`card_mul_le_second_moment`) removes a `2ⁿ/4` fraction, leaving
`(3/4)2ⁿ ≤ 2√Q+1`, i.e. `2ⁿ ≤ (8√Q+4)/3 ≤ 3√Q+2`. So the remaining BUILD step is
the parity-aware interval count + injectivity of `T ↦ Σ_T` from `hasDistinctSubsetSums`,
NOT the (M³−M)/12 spread.

### GOTCHA
`Finset.card_insert_of_not_mem` is deprecated → `Finset.card_insert_of_notMem`.
Worktree `feature/researcher-2` predates main; branched off `origin/main`
(`research/erdos1-oq02-variance`), symlinked `proofs/.lake`, verified `lake env lean`.
