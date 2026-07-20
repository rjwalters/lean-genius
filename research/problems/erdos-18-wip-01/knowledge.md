# Knowledge Base: erdos-18-wip-01

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

## Session 2026-07-20 (researcher-1) — decidability + foundations for the def-only stub

**Mode**: FRESH (knowledge score 0). **Outcome**: progress — 13 axiom-free lemmas + 2
Decidable instances, **host-verified v4.31** (`lake env lean`, exit 0; `#print axioms`
spot-check = `[propext, Classical.choice, Quot.sound]`, no `native_decide`).

Erdős Problem 18 (practical numbers, $250): `m` is practical if every `1 ≤ k < m` is a
sum of distinct divisors of `m`; the open questions concern the growth of `h(m)`.
`Erdos18Problem.lean` held only defs + `one_practical`/`two_practical`. Added:

- **decidableIsRepresentable** — `IsRepresentable k m` (`∃ S ⊆ divisors m, S.sum id = k`)
  is decidable by searching `(divisors m).powerset` (`decidable_of_iff`, the iff is
  `Finset.mem_powerset`).
- **decidableIsPractical** — reorders the two implications of the bounded `∀ k` so
  `Nat.decidableBallLT` fires, giving a full decision procedure.
- Worked examples by plain kernel `decide`: `four_practical`, `six_practical`,
  `eight_practical`, `not_practical_three`, `not_practical_five` — **axiom-free**
  (no `Lean.ofReduceBool`; confirmed via `#print axioms`).
- Witnesses/bounds: `zero_isRepresentable` (∅), `one_isRepresentable`,
  `isRepresentable_self`, `isRepresentable_le_sigma` (`k ≤ Σ divisors` via
  `Finset.sum_le_sum_of_subset`), `mem_divisors_le` (`Nat.divisor_le`),
  `isPractical_pos`, `not_isPractical_zero`, `mem_practicalNumbers_iff`.

### Notes / gotchas
- The bounded quantifier in `IsPractical` is `∀ k, 1 ≤ k → k < m → …`; `Nat.decidableBallLT`
  needs the `k < m` bound outermost, so the decidability iff swaps the two hypotheses.
- Plain `decide` (kernel) keeps the examples axiom-free; `native_decide` would pull in
  `Lean.ofReduceBool` and must be avoided for a clean status.

### Still open
`h(m)` and its growth (`conjecture_part1`, `conjecture_part2_weak/strong`, the $250
`h(n!) < n^{o(1)}` question) are deep and unformalized — this session builds only the
elementary decidable scaffolding around the definitions.
