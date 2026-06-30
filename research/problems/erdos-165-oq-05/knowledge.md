# Knowledge Base: erdos-165-oq-05

---

## Problem Understanding

The slug maps to erdos-165 openQuestions[5] = "Complete the sorry-marked proof
in R3_asymptotic_order". That task is STALE: the current
`proofs/Proofs/Erdos165Problem.lean` has no such sorry (0 sorries).

The real, honest gap: the gallery entry advertises "PGM Conjecture Disproved"
as a key insight and lists "disprove the PGM conjecture (c = 1/4)" as a proof
step, but the Lean file only refuted it in a PROSE COMMENT — `¬ pgmConjecture`
was never a theorem.

---

## Insights

- The erdos-165 file on origin/main did NOT compile: `erdos_165` failed at
  `linarith` (could not widen the constant 5/4 to 2 without `k²/log k ≥ 0`).
  Latent Mathlib-drift breakage despite meta claiming "0 sorries / axiomatized".
- Fix: take `k₀' = max k₀ 2` so `k ≥ 2 ⟹ log k > 0 ⟹ k²/log k ≥ 0`, and use
  `mul_div_assoc` so `linarith` sees `k²/log k` as one atom it can scale.
- The mathematical core is `asymptotic_constant_le`: an axiom-free real-analysis
  lemma stating two strictly ordered asymptotic constants cannot both bound the
  same `k²/log k`-scale sequence. The only Ramsey input to the refutation is
  `hhkp_bound`.

## Deliverables (this session)

- `asymptotic_constant_le` — axiom-free incompatibility lemma.
- `R3_upper_constant_ge_half` — any valid first-order upper constant for R(3,k)
  is ≥ 1/2 (HHKP obstruction).
- `pgm_conjecture_refuted : ¬ pgmConjecture` — machine-checked.
- Repaired `erdos_165` (Mathlib-drift fix).

0 new axioms. File still has its 10 deep-Ramsey axioms (Kim/Shearer/HHKP/AKS),
none provable from Mathlib.

---

## Dead Ends

- Axiom elimination is infeasible here: all 10 axioms are deep Ramsey-theory
  theorems (Kim 1995, Shearer 1983, HHKP 2025, AKS 1980) with no Mathlib proof.
