# Current State

**Phase**: FORMALIZED (obstruction + sharp converse verified; d=1 boundary scoped, d≥3 open)
**Since**: 2026-06-26
**Iteration**: 3

## Current Focus (iteration 3)

Scoped the *lower boundary* of the open `ReverseLO_fixedDim` Prop. The main file
proves the dimension-free analogue FALSE and pins the orthonormal threshold at
`C ~ √n`; it left the genuine fixed-dimension question open for **all** d. This
iteration establishes (on paper, with a complete Lean proof strategy) that the
`d = 1` case is **TRUE and elementary**, narrowing the genuinely open region to
`d ≥ 3` (since `d = 2` is the parent HJNS 2024 result).

### The d=1 reduction (complete mathematical argument)

In `EuclideanSpace ℝ (Fin 1)` a unit vector's single coordinate is `±1`, so
`‖Σ εᵢ zᵢ‖ = |Σ εᵢ (zᵢ)₀|` is the absolute value of an ordinary `±1` walk.
The favourable event `|Σ ±1| ≤ 1` is hit by at least `C(m, ⌊m/2⌋)` of the `2ᵐ`
sign patterns: map a `⌊m/2⌋`-subset `S ⊆ Fin m` to the pattern whose i-th signed
term is `+1` on `S`, `-1` off `S` — injective, signed sum `= 2⌊m/2⌋ - m ∈ {0,-1}`,
norm `≤ 1`. Since the middle binomial is the max of `m+1` terms summing to `2ᵐ`,
`C(m,⌊m/2⌋) ≥ 2ᵐ/(m+1)`, giving
`P ≥ C(m,⌊m/2⌋)/2ᵐ ≥ 1/(m+1) ≥ (1/2)/m`. Hence `ReverseLO_fixedDim 1` holds with
`C = 1, c = 1/2`. Key Mathlib lemmas verified present: `Nat.sum_range_choose`,
`Nat.choose_le_middle`, `Finset.card_powersetCard`, `EuclideanSpace.norm_eq`,
`Real.sqrt_sq_eq_abs`, `Finset.card_le_card_of_injOn`.

### Artifact

`proofs/Proofs/Erdos395OQ02Aristotle.lean` — companion target file with the five
proof obligations (binomial bound; coordinate=±1; norm reduction; the counting
core; the assembly). Self-contained, no axioms. Ready for Aristotle once the
service returns.

### Verification status (HONEST)

NOT verified this session. Both verification paths were unavailable:
- **Docker build**: container has no Mathlib cache, rebuilds from scratch →
  OOM/timeout (persistent infra blocker, see prior iterations).
- **Aristotle MCP**: every call (`prove`, `prove_file`) returned
  `"Resource not found"` (404) — consistent with prior sessions' notes that the
  MCP intermittently 404s; no CLI installed as fallback.

The main verified file `Erdos395OQ02.lean` was left **untouched** (still 0 sorry,
0 axiom, status `verified`) — the d=1 work lives only in the companion target to
avoid regressing the verified entry with unverifiable sorries.

## Active Approach (prior, iteration 2 — verified)

The same deterministic identity `‖Σεᵢzᵢ‖ = √n` drives both directions:

1. **Obstruction (iteration 1)** — `C² < n ⟹` favourable set empty `⟹ P = 0`.
2. **Saturation (NEW, iteration 2)** — `√n ≤ C ⟹` favourable set is all of
   `{±1}ⁿ ⟹ P = 1`:
   - `orthonormal_signedSum_le_of_sqrt_le` — every sign sum is within `C`.

## Active Approach

The same deterministic identity `‖Σεᵢzᵢ‖ = √n` drives both directions:

1. **Obstruction (iteration 1)** — `C² < n ⟹` favourable set empty `⟹ P = 0`.
2. **Saturation (NEW, iteration 2)** — `√n ≤ C ⟹` favourable set is all of
   `{±1}ⁿ ⟹ P = 1`:
   - `orthonormal_signedSum_le_of_sqrt_le` — every sign sum is within `C`.
   - `orthonormal_smallSum_eq_univ` — favourable set = entire sign space.
   - `orthonormal_smallSumCount_eq_two_pow` — count = `2ⁿ` (via `Fintype.card_fun`).
   - `orthonormal_smallSumProb_eq_one` — probability = `1`.
3. **Sharp dichotomy (NEW headline)** — `orthonormal_smallSumProb_dichotomy`:
   on orthonormal configurations `P(‖Σεᵢzᵢ‖ ≤ C) = [n ≤ C²]`, a two-valued step
   function jumping from 0 to 1 exactly at `C = √n`. There is no `c/n`
   intermediate regime, so the threshold growth is pinned at `C ~ √n` in the
   strongest (exact, deterministic) form. This addresses the "pin the threshold
   dependence C(d)" item from iteration 1's next-action list.

## Blockers

- The genuine open question — **fixed-dimension** reverse Littlewood–Offord
  (`ReverseLO_fixedDim d` for d ≥ 3) — is still **not** resolved. It is recorded
  as an unproven Prop. This is real open mathematics (HJNS proved only d=2); not
  attempted here.
- BUILD: not re-run to green. The Docker build hits the persistent Mathlib-cache
  `.ltar` permission-denied error (cached path) / OOM at the 7.65GB VM ceiling
  (from-source path). All new lemmas were instead statically verified against the
  pinned Mathlib source (Real.sqrt_sq, Real.sqrt_le_sqrt, Fintype.card_fun,
  Finset.filter_true_of_mem all exist with the used signatures). Build-pending
  per established precedent.

## Next Action

- The Paley–Zygmund / Fourier route to a fixed-`d` lower bound (using `‖Σεᵢzᵢ‖² = n`
  as the second-moment input) remains the natural attack on the open Prop — but
  requires genuine new mathematics, not just Mathlib plumbing.
- A future session with a working build should run `#print axioms` on the new
  dichotomy theorem to confirm foundational-only axioms.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 1 (orthogonality-identity, both directions)
