# Knowledge: erdos-27

**Problem**: Erdős #27 — Almost Covering Systems
**Status**: COMPLETED — stable axiomatized
**Last session**: 2026-04-27

## Stable Axiomatized Status (Session 2026-04-27)

**Mode**: REVISIT (stale OBSERVE state)
**Outcome**: completed (no eliminable axioms)

### Actual file state (vs problem.md claim of "12 sorries")

- `proofs/Proofs/Erdos27Problem.lean` — 329 lines, **0 sorries, 4 axioms**
- `proofs/Proofs/Stubs/Erdos27Aristotle.lean` — 148 lines, **0 sorries**, 5 routine lemmas all proved
- Gallery `src/data/proofs/erdos-27/meta.json` correctly reports `status: axiomatized`, `axiomCount: 4`, `sorries: 0`

The previous problem.md described 12 sorries to eliminate; that was based on an outdated snapshot. The file evolved into a clean axiomatized formulation before this researcher claim.

### The 4 axioms encode deep published theorems

| Axiom | Source | Plausibility of elimination |
|-------|--------|----------------------------|
| `erdos_27_ffkpy` | FFKPY 2007 (JAMS Theorem 1.1) | Multi-paper sieve-theoretic argument; no |
| `growing_C_achieves` | FFKPY 2007 (Theorem 1.2) | Same paper, positive direction; no |
| `averaging_bound_exists` | Probabilistic averaging | Most plausible single-session target, but still needs density / CRT infrastructure beyond current Mathlib |
| `bbmst_2024` | BBMST 2024 (Bloom–Briggs–Maynard–Smith–Tao) | Self-contained research thread; no |

### What is internally proved (no axioms used)

- `perfect_is_zero_almost` — perfect covering ⇒ 0-almost covering (telescoping argument over `liminf`)
- `naturalDensity_eq_inv` — `∏_{n=2}^k (1 − 1/n) = 1/k` (telescoping product, induction on k)
- `naturalDensity_vanishes` — natural density → 0 as k grows
- `conjecture_dichotomy` — `ErdosConjecture ↔ ¬ErdosConjectureNegation` (pure logic)
- All 5 lemmas in the Aristotle companion: `conjecture_dichotomy`, `uncoveredCount_le`, `asymptoticUncoveredDensity_le_one`, `perfect_is_zero_almost`, `almostCovering_mono`

### Why mark COMPLETED rather than continue

Following the precedent of `erdos-1022` (commit `e1c45e2b1ee`, "research(erdos-1022): mark COMPLETED — stable axiomatized status"), Erdős problems whose Lean formalization is in a clean axiomatized state — all derived theorems proved, all Aristotle-tractable lemmas proved, axioms exclusively encoding deep theorems beyond current Mathlib reach — are marked COMPLETED.

Continuing work in this state would amount to either:
- Rederiving theorems that already exist (low value)
- Adding theorems built on top of unproved axioms (anti-pattern per CLAUDE.md axiom-hunt priority)
- A multi-session axiom-elimination effort targeting one of the 4 axioms — out of scope for a single research session

### Next steps (if axiom elimination is later attempted)

1. **`averaging_bound_exists`** is the most plausible single-thread target: it is essentially a statement about random congruence assignments and the Chinese Remainder Theorem density. It would need a Mathlib-friendly probabilistic / measure-theoretic framework; nontrivial but plausible.
2. The two FFKPY axioms require sieve theory (Brun, Selberg) and density bounds beyond current Mathlib coverage.
3. The BBMST axiom is its own multi-paper research thread (Hough 2015 → BBMST 2024).

### Files modified this session

- `src/data/research/problems/erdos-27.json` (insights, builtItems, progressSummary, phase=COMPLETED)
- `research/problems/erdos-27/problem.md` (rewritten to reflect 0-sorry / 4-axiom state)
- `research/problems/erdos-27/knowledge.md` (this file)
- `research/problems/erdos-27/state.md` (phase=COMPLETED)
