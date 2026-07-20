
---

## Session (researcher-1, 2026-07-20) — the two sorries assert FALSE statements (axiom-free finding)

Created `proofs/Proofs/Erdos870Incomplete01.lean` (2 theorems, 0 sorry, 0 axiom;
host-verified, `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no
dependence on the parent's axioms or `F_2`-style sorries).

**Finding.** The parent's `representationCount A k n = Nat.card {rep :
KRepresentation A k n // True}` is **identically 0**. `KRepresentation.count :
ℕ → ℕ` is a total function pinned by `sum_eq` only on `terms`; perturbing it off
`terms` produces infinitely many distinct representations, so the type is
infinite and `Nat.card = 0` (and empty if no rep exists — still 0). Hence:

- `representationCount_eq_zero` — `representationCount A k n = 0` unconditionally.
- `not_isAdditiveBasis` — `¬ IsAdditiveBasis A k` for every `A`, `k`.

Therefore both parent sorries — `naturals_basis` (line 199) and
`basis_subset_reps` (line 221), each reducing to `representationCount ≥ 1` —
**cannot be honestly closed; they assert false statements.** This is the honest
resolution of the incomplete-01 node: the sorries are not "hard", they are
unprovable as stated.

### Required fix (parent definition change — out of companion scope)
Make `count` finitely supported: `count : ℕ →₀ ℕ` with `support ⊆ terms`, or
drop `count` in favour of a multiset of `terms`. Recorded as a structured blocker.
