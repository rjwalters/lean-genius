# Knowledge: roth-theorem-k3

## Session 1 (2026-03-22, researcher-2)

### Mathlib Infrastructure Survey
- **ZMod.dft** (`Analysis/Fourier/ZMod.lean`): Full DFT as LinearEquiv, notation 𝓕
- **ZMod.stdAddChar**: Standard additive character j ↦ exp(2πij/N), primitive
- **ThreeAPFree** (`Combinatorics/Additive/AP/Three/Defs.lean`): Mathlib's AP-free predicate
- **roth_3ap_theorem** (`Combinatorics/Additive/Corner/Roth.lean`): May have quantitative Roth via regularity — UNVERIFIED, could not read Mathlib source (symlink issue in worktree)
- **Additive energy** (`Combinatorics/Additive/Energy.lean`): E[s,t] counting
- **Behrend bound** (`Combinatorics/Additive/AP/Three/Behrend.lean`): Lower bound construction
- Parseval/Plancherel for finite groups: NOT FOUND in Mathlib

### What Was Done
1. **Restructured proof from 4 to 6 parts** (92→233 lines)
2. **Added tripleCount definition** + proved APFree ↔ tripleCount = 0
3. **Added card_le_nat, card_le_nat_real** — cardinality bounds (proved)
4. **Fixed density_increment_lemma** — added `0 < M` and `APFree B` to conclusion
5. **Proved density_increment_step** — one-step wrapper
6. **Proved density_iteration** — k steps boost density by k·δ²/100 (key iteration!)
7. **Added Fourier infrastructure** — norm bound, Parseval, AP-Fourier identity (sorry)
8. **Created RothTheoremAristotle.lean** — companion file for proof search

### Proof Architecture Insight
The iteration argument (roth_density_bound from density_increment_lemma) works as follows:
- `density_iteration` shows k applications boost density to ≥ δ + k·δ²/100
- Key inequality: current density d ≥ δ implies d² ≥ δ², so increment ≥ δ²/100
- After K = ⌈100·(1-δ)/δ²⌉ + 1 steps, density > 1, contradicting |A| ≤ N
- Type challenge: each step produces ∃(M)(B : Finset (ZMod M)), changing the type
- N₀ can be 1 since each step preserves M > 0 (from Nat.sqrt N ≥ 1 when N ≥ 1)

### Critical Finding: Our APFree ≡ Mathlib's ThreeAPFree
Our: ∀ a d, d ≠ 0 → a ∈ A → a+d ∈ A → a+2d ∉ A
Mathlib: ∀ a d, a ∈ A → a+d ∈ A → a+2d ∈ A → d = 0
These are contrapositives. An equivalence lemma would unlock Mathlib's additive combinatorics.

### Sorry Classification (Updated Session 2)
| Sorry | Difficulty | Aristotle? | Status |
|-------|-----------|------------|--------|
| fourierCoeff_norm_le | Easy | YES | **PROVED** (Session 2) |
| parseval_on_zmod | Medium | MAYBE | Needs orthogonality of characters |
| triple_count_fourier | Hard | NO | Deep identity connecting APs to Fourier |
| fourier_large_coefficient | Hard | NO | Key analytic step, needs Parseval + counting |
| density_increment_lemma | Hard | NO | Needs fourier_large_coefficient + pigeonhole |
| roth_density_bound | Medium | NO | **PROVED** (Session 2) |

## Session 2 (2026-03-22, researcher-4)

### What Was Done
1. **Proved fourierCoeff_norm_le** (triangle inequality + |exp(iθ)|=1)
   - Key technique: rewrite exponent to `↑θ * I` form via `push_cast; ring`
   - Show `(↑θ * I).re = 0` via `Complex.mul_re` + `Complex.I_re/I_im`
   - Then `Real.exp_zero` gives norm = 1
   - Triangle inequality via `norm_sum_le` + `Finset.sum_le_sum`
2. **Proved roth_density_bound** (main theorem of the file!)
   - Iterate `density_iteration` by induction on k: after k steps, get density ≥ δ+k·δ²/100
   - Cast unification: `push_cast` normalizes `↑(k+1)` to `↑k+1`
   - Choose K > 100/δ² via `exists_nat_gt`, clear denominator with `field_simp`
   - Density > 1 implies |B| > M, contradicting `card_le_nat_real`
3. **Updated Aristotle companion file** — removed proved lemmas, kept parseval and basic lemmas
4. **Reduced sorry count**: 6 → 4

### Proof Architecture
The main theorem `roth_density_bound` is now fully proved from `density_increment_lemma` (sorry):
```
density_increment_lemma (sorry)
  → density_increment_step (proved, session 1)
  → density_iteration (proved, session 1)
  → roth_density_bound (proved, session 2)
```

### Remaining Sorry Dependency Chain
```
parseval_on_zmod (sorry) ──────────────────────────┐
triple_count_fourier (sorry) ──────────────────────┤
                                                    ├→ fourier_large_coefficient (sorry)
                                                    │    └→ density_increment_lemma (sorry)
                                                    │         └→ roth_density_bound (PROVED)
```

### Technical Notes
- `div_lt_iff` does NOT exist as a bare identifier in current Mathlib — use `field_simp` or `mul_lt_mul_of_pos_right` to clear denominators
- `mul_lt_mul_of_pos_right` works for `a < b → 0 < c → a*c < b*c`
- `NeZero M` instance from `0 < M`: `⟨by omega⟩`
