# Knowledge Base: shannon-channel-coding-awgn-oq-03-oq-01

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

---

## Session 2026-07-09 (Session 1) — Water-filling formalized (FRESH)

**Mode**: FRESH · **Outcome**: progress (all three open items formalized; build verification via decoupled self-contained file)

### What I did
- Created `proofs/Proofs/ShannonChannelCodingAWGNOQ03OQ01.lean` (namespace `ShannonWaterFilling`).
- Proved the full finite-dimensional water-filling theorem, all axiom-free / sorry-free:
  1. `add_waterAlloc`: `Nᵢ + (μ−Nᵢ)₊ = max μ Nᵢ` — the identity that drives everything.
  2. `perUseCapacity_sub_le`: per-channel tangent bound (first-order condition in elementary form).
  3. `waterfilling_optimal`: **KKT optimality** — `Pᵢ⋆ = (μ−Nᵢ)₊` maximises `∑ ½log(1+Pᵢ/Nᵢ)` over all feasible allocations.
  4. `waterAlloc_rate_closedForm`: `R(P⋆) = ∑ ½ log(max μ Nᵢ / Nᵢ)`.
  5. `exists_waterLevel` (IVT) + `waterLevel_unique` (strict monotonicity) + `continuous_/monotone_waterBudget`.

### Key findings
- **The optimality proof needs no calculus.** The first-order/KKT condition is replaced by the
  scalar tangent inequality `log u ≤ u − 1` (`Real.log_le_sub_one_of_pos`) applied per channel with
  `u = (Nᵢ+xᵢ)/(Nᵢ+Pᵢ⋆)`. Summing gives
  `R(x) − R(P⋆) ≤ ∑ (xᵢ−Pᵢ⋆)/(2·max(μ,Nᵢ)) ≤ (∑xᵢ − P)/(2μ) ≤ 0`.
- The denominator collapse `max(μ,Nᵢ) → μ` is a two-case split: **active** channels (`Nᵢ<μ`) give
  equality since `Nᵢ+Pᵢ⋆ = μ`; **inactive** channels (`Nᵢ≥μ`) have `Pᵢ⋆=0`, `xᵢ≥0`, so
  `xᵢ/Nᵢ ≤ xᵢ/μ` (`div_le_div_of_nonneg_left`). A naive termwise bound fails on inactive channels
  when `xᵢ<x⋆ᵢ`, so the case split is essential.
- Water level existence = IVT on continuous monotone `g(μ)=∑(μ−Nᵢ)₊` between `g(0)=0` and
  `g(N_{i₀}+P) ≥ P` (single active channel `i₀` already supplies `P`). Uniqueness (for `P>0`) = strict
  monotonicity of `g` wherever `g>0` (`Finset.sum_lt_sum` with one strictly-increasing active term).

### Infrastructure / environment
- `ShannonEntropyOQ01` (transitively imported by the parent `ShannonChannelCodingAWGN`) is currently
  **SIGBUS-135 crashing at olean-write** in the Docker build — a pre-existing/environmental crash, not
  a code error (PR #36590 built through the same chain earlier). To get independent verification I
  **decoupled**: inlined `perUseCapacity P N = ½ log(1+P/N)` (definitionally identical to the gallery
  `awgnCapacity`) so the file imports only `Mathlib`.

### Files modified
- `proofs/Proofs/ShannonChannelCodingAWGNOQ03OQ01.lean` (new)
- `src/data/research/problems/shannon-channel-coding-awgn-oq-03-oq-01.json` (knowledge)

### Next steps
- Operational coding theorem (random Gaussian codebooks) tying capacity to achievable rates (→ oq-04).
- Continuous infinite-band (integral) water-filling limit.
- Equal-noise corollary: `μ = (P + ∑Nᵢ)/n`, `C = (n/2) log(1 + P/∑Nᵢ)`.
