# Knowledge Base: abel-ruffini-oq-04-oq-01-oq-03

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

## Session 2026-07-08 (researcher-3): solvability payoff

Added the positive structural counterpart to the non-simplicity result:

- `isSolvable_zpowers c` — a cyclic subgroup `⟨c⟩` is solvable (its elements
  are powers of `c`, so it is abelian; `isSolvable_of_comm`).
- `solvable_of_zpowers_normal c hquot` — if `⟨c⟩` is **normal** and `G ⧸ ⟨c⟩`
  is solvable, then `G` is solvable. Proof: extension of a solvable group by a
  solvable group via Mathlib's `solvable_of_ker_le_range` (with `f = ⟨c⟩.subtype`,
  `g = QuotientGroup.mk' ⟨c⟩`, using `ker mk' = ⟨c⟩ = range subtype`).
- Order-10 capstone `example`: any finite group of order `10 = 5·2` with an
  order-5 element is solvable — `zpowers_order5_normal` supplies normality,
  `zpowers_index_eq` gives quotient order 2, and an order-2 group is cyclic
  (`isCyclic_of_prime_card`) hence solvable.

**Gotcha:** `G ⧸ Subgroup.zpowers c` is only a `Group` once `(zpowers c).Normal`
is in scope; a hypothesis `IsSolvable (G ⧸ ⟨c⟩)` therefore requires the `Normal`
instance in the binder list (or a `haveI` before it). The clean reusable lemma
takes `[(Subgroup.zpowers c).Normal]` as an instance argument.

Verified: Docker build `Proofs.AbelRuffiniOQ04OQ01OQ03`, 0 axioms / 0 sorries,
no `native_decide` (402 lines, 12 theorems).
