# Knowledge Base: erdos-61-wip-01

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

## Session 2026-07-20 (researcher-1) — bare stub → axiom-free structural lemmas

**Mode**: FRESH (score 0). **Outcome**: progress (2 theorems, axiom-free), host-verified v4.31.
**Problem is OPEN** (Erdős–Hajnal polynomial bound) — no attempt to prove the conjecture.

Same flavor-(b) pathology: `Erdos61Problem.lean` had defs + `ErdosHajnalConjecture` Prop but **zero
theorems**, while meta claimed the bounds were "stated as axioms" (`axiomCount=0`) and "All results
proved from Lean primitives".

**Added (0-axiom, `#print axioms` = propext/Classical.choice/Quot.sound):**
- `isErdosHajnalLowerBound_zero` — the constant `0` is always an EH lower bound (`indepNum ≥ 0`);
  `Filter.Eventually.of_forall … Or.inl (by simp only [ge_iff_le]; positivity)`.
- `IsErdosHajnalLowerBound.mono` — downward closed: `f ≤ g` pointwise + `H`-bound-`g` ⟹ `H`-bound-`f`
  (`filter_upwards [hg]` then `le_trans (hfg n)` into each disjunct).

Conceptual point isolated: the conjecture is entirely about the growth *rate* (exponent `c>0`), not
existence of a bound. **Meta synced**: theoremCount 0→2, lineCount→169, honest assumptions/proofStrategy.
**Still open**: the conjecture itself + partial bounds (1989 exp(c√log n), BNSS 2023) — probabilistic
combinatorics well beyond Mathlib v4.31.
