# Knowledge Base: szemeredi-full-oq-02

**Problem**: Szemerédi's Theorem: Uniform Sets Not Containing k-AP Are o(N) Dense

---

## Problem Understanding

The problem asks for the **density formulation** of Szemerédi's theorem:
- k-AP-free subsets of {0,...,N-1} have vanishing density |A|/N → 0
- Formal statement: Filter.Tendsto (fun N => (A N).card / N) atTop (nhds 0)

"Uniform" in the title likely refers to arbitrary (not specifically Gowers-uniform) k-AP-free sets.

---

## Session 2026-04-26 — COMPLETED

**Mode**: FRESH (claimed from pool)
**Outcome**: Proof built, 0 sorries, 1 axiom inherited, PR created

### What I Did

1. Surveyed existing Szemerédi infrastructure: `SzemerediTheorem.lean` already has `ap_free_density_bound` (ε-N₀ form for all k)
2. Discovered `rothNumberNat_isLittleO_id` in Mathlib's `Corner/Roth.lean` — the k=3 density statement as IsLittleO
3. Built `SzemerediFullOQ02.lean` (118 lines, 0 sorries) with:
   - `szemeredi_vanishing_density`: Filter.Tendsto for all k ≥ 1
   - `roth_density_isLittleO`: alias for Mathlib's `rothNumberNat_isLittleO_id`
   - `ap_free_density_isLittleO_k3`: IsLittleO for k=3 via `isLittleO_iff_tendsto`
   - `szemeredi_density_full`: main theorem alias

### Key API Discoveries

- **`div_lt_iff`**: Renamed to `div_lt_iff₀` in Lean 4 Mathlib
- **`rothNumberNat_isLittleO_id`**: In `Mathlib.Combinatorics.Additive.Corner.Roth` — proves the maximum density of 3-AP-free sets is o(N)
- **`isLittleO_iff_tendsto`**: Converts `IsLittleO` ↔ `Tendsto (f/g)` (requires zero case: g x = 0 → f x = 0)
- **Zero case**: When N=0, A 0 ⊆ Finset.range 0 = ∅, so (A 0).card = 0
- **`Metric.tendsto_atTop`**: Standard way to prove Filter.Tendsto via ε-N₀

### Files Created

- `proofs/Proofs/SzemerediFullOQ02.lean` (118 lines, 0 sorries, 1 axiom inherited)
- `src/data/proofs/szemeredi-full-oq-02/meta.json`
- `src/data/proofs/szemeredi-full-oq-02/index.ts`
- `src/data/proofs/szemeredi-full-oq-02/annotations.json`

---

## Insights

- `rothNumberNat_isLittleO_id` is already in Mathlib — the o(N) density bound for k=3 requires no new work
- The ε-N₀ → Tendsto conversion needs `max N₀ 1` to guarantee N > 0 for `div_lt_iff₀`
- Gowers U^{k-1} norm formulation (stronger version) is BLOCKED — Gowers norms not in Mathlib 4.26

## Dead Ends

- Gowers-uniformity interpretation: if "uniform" means Gowers-uniform (U^k norm small), this is ~1000 lines of work and BLOCKED
- `div_lt_iff` (without ₀ suffix): doesn't exist in Lean 4 Mathlib
- `Real.norm_natCast` in `simp` context: doesn't simplify `|(A N).card : ℝ|` reliably — use `isLittleO_iff_tendsto` instead of `isLittleO_iff`
