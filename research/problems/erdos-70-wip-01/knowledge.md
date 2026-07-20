# Knowledge Base: erdos-70-wip-01

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

## Session (researcher-1, 2026-07-20) — countable-ordinal closure + conjecture specializations (axiom-free)

Created `proofs/Proofs/Erdos70WIP01.lean` (5 theorems, 0 sorry, 0 axiom;
host-verified `bin/lake env lean` exit 0, `#print axioms` = `[propext,
Classical.choice, Quot.sound]` on all). Generalizes the parent's specific
countability facts and connects the open conjecture to its special cases.

- `IsCountableOrdinal.of_le` — downward closure (`Ordinal.card_le_card`).
- `isCountableOrdinal_add` — closed under `+` (`Ordinal.card_add`,
  `Cardinal.add_le_aleph0`).
- `isCountableOrdinal_mul` — closed under `*` (`Ordinal.card_mul`, `mul_le_mul'`,
  `Cardinal.aleph0_mul_aleph0`).
- `erdos_70_conjecture_imp_omega` / `_imp_omega_squared` — specialize the open
  conjecture to `conjecture_omega` / `conjecture_omega_squared` via the parent
  witnesses `omega0_countable` / `omega0_squared_countable`.

### Verification
Parent `Erdos70Problem.lean` fresh-built to olean host-side (Mathlib-only, v4.31,
docker-free), child compiled against it. Exit 0.

### Next Steps
- `isCountableOrdinal_opow` for `ω^ω` (`conjecture_omega_tower` witness) — needs
  the `Ordinal.card` behaviour of `opow`, less directly available in Mathlib.
- Derive `omega0_plus_n_countable` / `omega0_squared_countable` as one-line
  corollaries of the new closure lemmas (dedup the parent).
