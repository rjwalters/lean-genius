# erdos-340-greedy-sidon-oq-01 — Prove the N^(1/3) greedy growth bound rigorously

## Summary

The greedy (Mian–Chowla) Sidon sequence `aₙ` is **constructed** in
`proofs/Proofs/Erdos340GreedySidon.lean` (explicit `Nat.find` recursion; the three former
existence axioms are discharged). The known **N^(1/3)** lower bound existed there only as a
comment-level proof sketch. This OQ formalizes it.

**Status (2026-06-19): the cubic growth bound and the discrete Ω(N^(1/3)) count are PROVED,
verified, 0-axiom**, in the new companion `proofs/Proofs/Erdos340GreedyGrowth.lean`.

## Session 2026-06-19 (REVISIT) — cubic bound + cube-root inversion

**Mode**: REVISIT (pool of `available` candidates was 100% already-shipped duplicates;
picked this RICH-knowledge surveyed open problem instead).
**Outcome**: progress — major lemma chain proved.

### What I Did
- Created `proofs/Proofs/Erdos340GreedyGrowth.lean` and registered it in `Proofs.lean`.
- Proved (all VERIFIED, axioms = [propext, Classical.choice, Quot.sound] only):
  - `forbidden A` set + `forbidden_card_le : (forbidden A).card ≤ A.card ^ 3` + `forbidden_mono`.
  - `not_sidon_insert_forbidden` — the crux necessary direction.
  - `greedy_skip_not_sidon` — greedy minimality via `Nat.find_min`.
  - `greedy_covering` — induction: every `p ∈ [1, aₙ]` is in `Aₙ` or `forbidden Aₙ`.
  - `greedySidonSeq_le_cubic : aₙ ≤ (n+1) + (n+1)³` — the cubic growth bound.
  - `greedySidonSeq_le_two_mul_cubic : aₙ ≤ 2(n+1)³`, `greedySeqSet_subset_Icc`.
  - `greedy_count_ge` — for `N ≥ 2(n+1)³`, at least `n+1` greedy terms lie in `[1, N]`
    (the discrete Ω(N^(1/3)) lower bound; no `rpow`).

### Key Findings
- The crux lemma that prior sessions flagged as the genuinely-technical Aristotle target
  is actually a **one-line contrapositive** of the parent's `sidon_insert_of_large`
  (line 408), which already encodes the hard 6-way collision case analysis.
- The global covering argument is cleanest as a single induction on `n` of the
  `∀ p ∈ [1, aₙ]` statement; the skipped-value/min-index bookkeeping falls out of the
  successor case automatically (IH + monotonicity for `p ≤ aₙ`; `Nat.find_min` for the gap).
- Defeq handles `greedySeqSet (n+1) = insert (greedySidonSeq (n+1)) (greedySeqSet n)` and
  `greedySidonSeq (n+1) = nextSidon (greedySeqSet n) (greedySidonSeq n)` (both `rfl`).

### Files Modified
- `proofs/Proofs/Erdos340GreedyGrowth.lean` (new, ~210 lines, 0-axiom)
- `proofs/Proofs.lean` (import)
- `src/data/research/problems/erdos-340-greedy-sidon-oq-01.json` (knowledge)

### Next Steps
- Optional analytic `rpow` phrasing of `greedy_count_ge`.
- The axiom `greedy_sidon_lower_bound` in the *separate* `Erdos340Problem.lean` uses a
  disconnected `sInf`-based `greedySidon`; discharging it needs bridging the two definitions.
- Remaining axiom in the parent: Erdős–Turán upper bound `sidon_upper_bound`.

### Honesty note
This is the **known** lower-bound direction (cubic ⇒ N^(1/3)). The 1/3→1/2 exponent
improvement is the OPEN part of Erdős #340 and is NOT addressed.
