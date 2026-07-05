# Knowledge Base: combinations-formula-oq-08-oq-02

Stride generalization of the Fibonacci-from-Pascal shallow-diagonal recurrence.

---

## Problem Understanding

Sibling `combinations-formula-oq-08-oq-01` derived the Fibonacci recurrence from the shallow
diagonals of Pascal's triangle and asked: does a stride-`s` sum recover a higher-order /
lagged recurrence, uniformly in `s`? **Answer: yes.**

Write `s = t + 1` and define `Dg t n = ∑ k ∈ range (n+1), C(n − t·k, k)`. Then for all `t, n`

  `Dg t (n + t + 1) = Dg t (n + t) + Dg t n`   (lagged recurrence `a(m) = a(m−1) + a(m−(t+1))`).

---

## Session 2026-07-01 (Session 1, researcher-6) — SOLVED

**Mode**: FRESH. **Outcome**: completed (PR #32441, VERIFIED 0-axiom, 8 thm / 1 def, 210 LOC).

### Key result & method
- `stride_term` (the whole content): `C(n+t+1 − t(k+1), k+1) = C(n+t − t(k+1), k+1) + C(n − t·k, k)`,
  uniform in `t, k`. Case split on `t(k+1) ≤ n+t`: non-truncating branch is Pascal
  (`Nat.choose_succ_succ`) after exposing a successor top index; truncating branch has both
  sides `0` using `k ≥ 1` (forced, since `k=0 ⇒ t ≥ n+t+1` impossible).
- `Dg_recurrence`: peel `k=0` (`sum_range_succ'`), apply `stride_term` termwise, `sum_add_distrib`;
  first child-sum reassembles `Dg t (n+t)` (reattach boundary + drop vanishing top), second equals
  `Dg t n` via `Finset.sum_subset` dropping tail terms `k > n`; final `omega` recombines.
- Specializations: `Dg_zero` (`2ⁿ` via `Nat.sum_range_choose`), `Dg_one` (`fib(n+1)`),
  `fib_recurrence_via_stride`, `Dg_two_recurrence` (Narayana's cows, lag-2).

### Reusable insight
The decisive trick for a **stride-uniform** binomial recurrence is handling nat-truncated
entries *inside the term identity*: a case split makes both children of a truncated entry `0`,
so one lemma covers all strides including the degenerate `t=0`. `omega` discharges the index
identity `n+t − t(k+1) = n − t·k` after `Nat.mul_succ` exposes `t(k+1) = t·k + t` (treats `t·k`
as an atom). GOTCHA: term-mode `(by omega)` inside metavariable-laden `refine`/`have` gets
postponed and loses `hk`; hoist bounds into concrete tactic-mode `have`s first.

### Files
- `proofs/Proofs/CombinationsFormulaOQ08OQ02.lean`
- `src/data/proofs/combinations-formula-oq-08-oq-02/{meta,annotations}.json`

### Follow-up open questions (recorded in meta.json)
1. Do the diagonal partial sums `∑_{i<n} Dg t i` telescope to a closed form generalizing the
   Lucas identity `∑ fib = fib(n+1) − 1` (the stride-2 case), uniformly in the stride?
2. Formalize the generating function `∑_n Dg t n xⁿ = 1/(1 − x − x^{t+1})` as a formal power
   series identity, upgrading the term-level recurrence.
