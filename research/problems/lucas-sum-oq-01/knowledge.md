# Knowledge Base: lucas-sum-oq-01

Partial sums of the Lucas numbers: ∑_{k=1}^{n} L_k = L_{n+2} − 3.

---

## Problem Understanding

Lucas numbers L_0 = 2, L_1 = 1, L_{n+2} = L_n + L_{n+1} (2, 1, 3, 4, 7, 11, 18, …).
The partial-sum identity is the Lucas analogue of ∑ F_k = F_{n+2} − 1; the additive
constant is 3 = L_0 + L_1 instead of 1. Mathlib has Nat.fib but no Lucas sequence and
no packaged Lucas partial-sum lemma.

---

## Insights

- **Subtraction-free engine.** Over ℕ, prove (∑_{k=1}^{n} L_k) + 3 = L_{n+2} first by
  induction; the headline subtraction form follows by omega since L_{n+2} ≥ 3. Same ℕ
  trick as factorial-telescoping-sum-oq-01.
- **omega + opaque atoms.** omega does NOT normalize indices inside an opaque function
  application: in the inductive step the goal's RHS is `lucas (n+1+2)`, so the recurrence
  must be stated as `lucas (n+1+2) = lucas (n+1) + lucas (n+2)` (via `lucas_add_two (n+1)`)
  for the atoms to unify. Stating it as `lucas (n+3) = …` leaves omega with two distinct
  atoms and it fails. In the fib bridge, eliminate every `lucas` by `rw` so only aligned
  `fib` atoms remain before calling omega.
- **Bridge to Nat.fib.** L_{n+1} = F_n + F_{n+2} by Nat.twoStepInduction; keeps the entry
  self-contained while anchoring the local Lucas definition to Mathlib (reuses the pattern
  from FibonacciIdentitiesOQ03OQ03).

---

## Dead Ends

- Stating the recurrence as `lucas (n+3) = …` and calling `omega` in the inductive step
  fails: omega sees `lucas (n+1+2)` (goal) and `lucas (n+3)` (hypothesis) as distinct
  atoms. Use the goal's exact index form.

---

## Outcome

**SOLVED (verified, 0 sorry, 0 axiom).** `proofs/Proofs/LucasSumOQ01.lean` — 114 lines,
6 theorems, 1 definition. `#print axioms` reports only [propext, Classical.choice,
Quot.sound] for the sum theorems (no sorryAx, no native_decide). Gallery entry at
`src/data/proofs/lucas-sum-oq-01/`. Compiled offline with `lake env lean` against
Mathlib v4.26.0 (Docker unavailable this session).
