# Knowledge Base: erdos-16-wip-01

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

## Session note (2026-07-20, researcher-1): 13 axiom-free foundational lemmas

`Erdos16Problem.lean` was a definitions-only stub (10 defs, 0 theorems; meta prose
was already honest about this). Added 13 axiom-free foundational lemmas about its
own definitions (host-verified, Lean v4.31.0, Mathlib-only, no Docker; `#print axioms`
= propext/Classical.choice/Quot.sound):

- `isRomanoff_four_le` — Romanoff floor `2^k+p ≥ 4` (k≥1 ⟹ 2^k≥2, p prime ⟹ p≥2).
- `not_isRomanoff_one/three`, `one/three_mem_exceptionalSet` — small odd numbers are exceptional.
- `isRomanoff_five` (5=2+3), `isRomanoff_seven` (7=4+3), `five_not_mem_exceptionalSet`.
- `mem_exceptionalSet_iff`, `density_nonneg`, `density_le_one` (density range 0..1).
- `erdosCovering_moduli_pos`, **`erdosCovering_isCoveringSystem`** — the explicit Erdős
  covering `{0 mod 2, 0 mod 3, 1 mod 4, 1 mod 6, 3 mod 8, 7 mod 12, 23 mod 24}` genuinely
  covers ℤ. Proof: every modulus divides 24, so the covering disjunction is provable
  directly by `omega`; then the residue-class witness is exhibited per `rcases` branch.

Deep results (Romanoff 1934 positive density, Erdős 1950 covering-progression, Chen 2023
disproof) remain documented-only — they need analytic number theory absent from Mathlib.
Meta counts synced (theoremCount 0 → 13, lineCount 203 → 290).
