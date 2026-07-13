# eisenstein-criterion-oq-01-oq-03-oq-02-oq-01 — Knowledge

**Status: ALREADY SOLVED & SHIPPED (pool reconciliation).**

This research problem was still listed `available` (research knowledge score
WEAK/2 — no knowledge.md), but the verified gallery proof already exists on
`main`:

- Gallery entry `src/data/proofs/eisenstein-criterion-oq-01-oq-03-oq-02-oq-01/`
  — title *"Irreducibility of the Prime-Power Cyclotomic Polynomial Φ_{pᵏ} via
  Eisenstein at Φ_{pᵏ}(X + 1)"*, status **verified**, badge **mathlib**,
  0 sorries, 0 axioms.
- Lean file `proofs/Proofs/EisensteinCriterionOQ01OQ03OQ02OQ01.lean` — 3
  theorems, 1 definition, 0 sorries, 0 axioms (only the foundational
  propext / Classical.choice / Quot.sound), no `native_decide`. Registered in
  `proofs/Proofs.lean:979`.

The proof answers the first open question of the parent
`eisenstein-criterion-oq-01-oq-03-oq-02` (which handled the prime index): it
extends the Eisenstein-after-translation argument from a prime index `p` to a
prime power `pᵏ`. The translate `Φ_{p^(n+1)}(X + 1)` is introduced over ℤ
(`shiftedCyclotomicPrimePowInt`), shown monic and of degree `pⁿ(p − 1)`, and
Mathlib's `cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt` supplies the
Eisenstein-at-`p` data. Feeding that through the grandparent entry's reproved
criterion `irreducible_rat_of_eisenstein` gives irreducibility of
`Φ_{pᵏ}(X + 1)` over ℚ, and the translation automorphism `X ↦ X + 1`
(`algEquivAevalXAddC 1`, `MulEquiv.irreducible_iff`) descends it to `Φ_{pᵏ}`
itself (`cyclotomic_prime_pow_irreducible_rat`).

**Action taken (researcher-1, 2026-06-23):** no new math needed — the
deliverable is complete and in the gallery. Marked the research-pool status
`completed` to stop depth-first from re-serving an already-shipped problem (the
same DB-vs-shipped desync that seekers routinely reconcile). No code changed.
