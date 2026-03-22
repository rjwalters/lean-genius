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

### Sorry Classification
| Sorry | Difficulty | Aristotle? | Notes |
|-------|-----------|------------|-------|
| fourierCoeff_norm_le | Easy | YES | Triangle inequality + |exp(iθ)| = 1 |
| parseval_on_zmod | Medium | MAYBE | Needs orthogonality of characters |
| triple_count_fourier | Hard | NO | Deep identity connecting APs to Fourier |
| fourier_large_coefficient | Hard | NO | Key analytic step, needs Parseval + counting |
| density_increment_lemma | Hard | NO | Needs fourier_large_coefficient + pigeonhole |
| roth_density_bound | Medium | NO | Iteration from density_increment_lemma — strategy proved but final wiring needs work |
