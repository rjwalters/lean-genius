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

---

## Follow-up: symmetric Shearer obstruction (researcher-1, 2026-07-08)

The prior session refuted PGM (c=1/4) from *below* via HHKP (`R3_upper_constant_ge_half`).
Added the *above* mirror using Shearer (upper constant 1):

- `R3_lower_constant_le_one (a) (ha : ∀ε>0 eventually (a-ε)k²/log k ≤ R3 k) : a ≤ 1` —
  any valid first-order LOWER constant is ≤ 1. Reuses the axiom-free `asymptotic_constant_le`
  with (lower = ha, upper = shearer_upper_bound, b = 1).
- `constantConjecture c` (general def, the common shape of mainConjecture c=1/2 and
  pgmConjecture c=1/4).
- `constantConjecture_refuted_of_one_lt (c) (1<c) : ¬ constantConjecture c` — its lower
  half would assert a valid lower constant > 1, contradicting `R3_lower_constant_le_one`.

**Net structural payoff**: `asymptotic_constant_le` is two-sided infrastructure. HHKP pins
the constant ≥ 1/2 from below; Shearer pins it ≤ 1 from above. Together they bracket the
(open) exact constant to **[1/2, 1]** using only the two Ramsey axioms. 0 new axioms;
still 10 deep-Ramsey axioms (Kim/Shearer/HHKP/AKS), none Mathlib-eliminable. VERIFIED build.

## Session 2026-07-09 (researcher-1) — symmetric completion of the [1/2,1] bracket (VERIFIED)

Completed the two-sided obstruction into a single headline. The prior sessions refuted
constantConjecture from below only at the specific PGM value 1/4 (`pgm_conjecture_refuted`)
and from above for c>1 (`constantConjecture_refuted_of_one_lt`). Added (8→10 thm):
- `constantConjecture_refuted_of_lt_half (c) (hc : c < 1/2) : ¬ constantConjecture c` — the
  GENERAL lower refutation (PGM 1/4 is the c=1/4 instance); its upper half asserts a valid
  upper constant c<1/2, contradicting `R3_upper_constant_ge_half` (HHKP). Mirrors `_of_one_lt`.
- `constantConjecture_forces_bracket (c) (h) : 1/2 ≤ c ∧ c ≤ 1` — unifying headline: any
  conjectured exact first-order constant for R(3,k)/(k²/log k) MUST lie in [1/2,1]. Lower
  fence = HHKP, upper fence = Shearer; Erdős's conjectured 1/2 sits on the lower fence (survives),
  PGM 1/4 excluded. by_contra + push_neg dispatches each fence to the two refutation lemmas.

0 new axioms (still 10 deep-Ramsey axioms Kim/Shearer/HHKP/AKS, none Mathlib-eliminable).
VERIFIED `Built Proofs.Erdos165Problem (2.3s)` at LEAN_MEMORY_LIMIT=8192. meta synced 7→10 thm
/ 363→396 lines (also corrected a pre-existing -1 drift).

**Terminus note.** The exact-constant question is genuinely open (the [1/2,1] gap is the real
Ramsey frontier); the formal side is now saturated — the bracket is as tight as the two
available Ramsey axioms allow, and narrowing it needs new deep Ramsey input, not Lean work.
