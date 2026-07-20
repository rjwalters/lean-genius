# Knowledge Base: abundant-number-oq-03-oq-03

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

## Session 2026-07-20 (researcher-1) — base witness: 945 is odd primitive abundant [VERIFIED, axiom-free]

**Mode**: FRESH (score 0) · **Outcome**: progress (base witness pinned; infinitude still OPEN)

### What I did
Created `proofs/Proofs/AbundantNumberOQ03OQ03.lean` (self-contained, imports only
`Mathlib`; host-verified via `lake env lean`, EXIT 0). All theorems axiom-free —
`#print axioms` = `[propext, Classical.choice, Quot.sound]` (no `Lean.ofReduceBool`).

- `IsPrimitiveAbundant n := n.Abundant ∧ ∀ d ∈ n.properDivisors, d.Deficient` — the
  OEIS A006038 predicate (abundant, *every* proper divisor deficient).
- `OddPrimitiveAbundant := {n | Odd n ∧ IsPrimitiveAbundant n}` — the target set.
- `abundant_945`, `odd_945`, `primitive_945`, `mem_oddPrimitiveAbundant_945` — the
  smallest odd abundant number 945 = 3³·5·7 is in fact odd primitive abundant; all
  15 proper divisors (1,3,5,7,9,15,21,27,35,45,63,105,135,189,315) are deficient.
- `not_deficient_of_abundant`, `not_primitive_of_abundant_properDivisor` — the
  divisibility-minimality obstruction (an abundant proper divisor kills primitivity).

### Key findings
- **Verified, not axiomatized.** The finite checks (one number 945 + its 15
  divisors, all ≤ 315) are small enough for the Lean *kernel* via `decide` with
  `set_option maxRecDepth 4000` — no `native_decide`. This is strictly stronger
  than the sibling `abundant-number-oq-02` (945-range minimality) which needs
  `native_decide`/`pdSum` because it evaluates the whole `∀ n<945` window.
- Mathlib already has the *parent* `Nat.infinite_odd_abundant`
  (`NumberTheory.FactorisationProperties`), plus `Prime.deficient` /
  `IsPrimePow.deficient` — so among the proper divisors of 945 only the composite
  ones (15,21,35,45,63,105,135,189,315) carry non-trivial deficiency content.

### Next steps (infinitude OPEN)
- Route 1: odd analogue of the even `2^k·p` primitive construction — odd base `m`
  with `σ(m)/m` just below 2, times an odd prime `p` in a Bertrand-type window.
- Route 2: primitive-part extraction from `Nat.infinite_odd_abundant` — show the
  primitive abundant divisors of an infinite odd abundant family are odd and
  unbounded (pigeonhole).
- Intermediate lemma: `σ(m·p) = σ(m)(p+1)` for odd prime `p ∤ m`, and a reusable
  proper-divisor-deficiency criterion for `m·p`.
