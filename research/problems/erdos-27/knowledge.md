# Knowledge Base: erdos-27

Insights accumulated during research on this problem.

---

## Problem Understanding

Erdős #27 (almost covering systems with bounded moduli) was DISPROVED by
Filaseta-Ford-Konyagin-Pomerance-Yu (JAMS 2007). The active Lean file
`proofs/Proofs/Erdos27Problem.lean` (330 lines, 0 sorries, 4 axioms) encodes
the structural result with the four deep results axiomatized:

- `erdos_27_ffkpy` — main FFKPY disproof (deep, JAMS 2007)
- `growing_C_achieves` — positive direction, FFKPY Theorem 1.2 (probabilistic)
- `averaging_bound_exists` — existence via averaging argument (combinatorial,
  derivable via probabilistic method on Finset but a 1000+ line development)
- `bbmst_2024` — Bloom-Briggs-Maynard-Smith-Tao 2024 minimum modulus < 616,000
  (deep, computational; not realistically formalizable)

A companion stub `proofs/Proofs/Stubs/Erdos27Aristotle.lean` proves four
routine corollaries (uncoveredCount_le, asymptoticUncoveredDensity_le_one,
perfect_is_zero_almost, almostCovering_mono) that are NOT in the main file.

---

## Insights

### 2026-04-27 (researcher-4)

**Pre-Work Assessment:**

1. *Axiom Question*: 4 axioms in main file. All four are deep, named-paper
   results — none are routine Mathlib facts. Axiom elimination is not
   tractable in a single session.
2. *Value Question*: Adding routine corollaries from the Aristotle stub
   (uncoveredCount_le, asymptoticUncoveredDensity_le_one, almostCovering_mono,
   isAlmostCovering_one) gives genuine verified content without inflating the
   axiom count. These are direct adaptations of already-working proofs.
3. *Strategy*: BUILD — port four routine theorems from the companion stub
   into the main file.

**Build Outcome:**

The Docker build failed with API drift:
`import Mathlib.Topology.Instances.Real` (line 38) is no longer available in
current Mathlib (rev 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67). The same drift
affects 20+ files in `proofs/Proofs/`. The build container reverted my worktree
edits, so the drafted additions were lost.

**Mathematical Note:**

For future axiom-reduction sessions, the most tractable target is
`averaging_bound_exists`. Mathematical content: choose residues `aₙ`
uniformly at random for each `n ∈ [m₁, m₂]`; by CRT (distinct moduli give
relatively-prime cycle lengths), the expected fraction of uncovered integers
in any large window equals `∏(1 - 1/n)`. Linearity of expectation +
probabilistic existence give the conclusion. Mathlib has measure-theoretic
infrastructure but the discrete combinatorial CRT-style averaging would
require a substantial development.

The other three axioms (`erdos_27_ffkpy`, `growing_C_achieves`, `bbmst_2024`)
are deep results from named papers and are not realistic targets.

---

## Dead Ends

- *Adding new theorems on top of broken imports*: The Docker build cannot
  verify additions until the import drift is repaired. Don't draft additional
  proofs in this file until Mechanic fixes `Mathlib.Topology.Instances.Real`.
- *Naive axiom elimination*: The 4 axioms here are not "routine that can be
  proved from Mathlib" — they encode FFKPY 2007 and BBMST 2024 results. Don't
  attempt to inline-prove them; they are correctly axiomatized.
