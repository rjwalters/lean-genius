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

---

## Session 2026-07-20 (researcher-1): closure toolkit + conjecture specializations

Batch 2 of axiom-free lemmas in `Proofs/Erdos70Problem.lean` (theorem count
9 → 18, still 0 axioms, 0 sorries). Host-verified with `lake env lean` (imports
`Mathlib`); `#print axioms` on all six new theorems yields only
`[propext, Classical.choice, Quot.sound]`.

- **Countability closure toolkit**: `zero_countable`, `one_countable`,
  `IsCountableOrdinal.mono` (β ≤ α), `IsCountableOrdinal.add`,
  `IsCountableOrdinal.mul`. The existing `omega0_plus_n_countable` /
  `omega0_squared_countable` are now instances of this general principle
  (`Ordinal.card_add/_mul` + `Cardinal.aleph0_add_aleph0/_mul_aleph0`).
- **Conjecture ⇒ specialization theorems**: `erdos_70_conjecture_omega`,
  `erdos_70_conjecture_omega_squared` derive the β=ω and β=ω·ω named cases
  (previously only `def`s) from `erdos_70_conjecture` via countability of the
  ordinal + `2 ≤ n`.
- **PartitionArrow boundary cases**: `partition_arrow_ordinal_zero` (α=0, empty
  set vacuously homogeneous with order type ≥ 0) and `partition_arrow_size_zero`
  (m=0, empty finset).

### Next targets
- Countability of `ω^ω` (`Ordinal.omega0 ^ Ordinal.omega0`), referenced by
  `conjecture_omega_tower` but not yet proven countable — needs a countable-sup
  argument (no direct `Ordinal.card_opow` in Mathlib), left as follow-up.
- Erdős Problem 70 itself (general countable β) is OPEN; the Erdős–Rado positive
  result 𝔠 → (ω+n, 4)₂³ needs partition-calculus machinery absent from Mathlib.

## Session 2026-07-20 (researcher-1): closure under finite exponentiation

Added 2 axiom-free theorems to `Proofs/Erdos70WIP01.lean` (theoremCount 5→7,
0 axioms, 0 sorries; `#print axioms` = propext/Classical.choice/Quot.sound only,
host-verified via parent-olean + `lake env lean`):

- **`isCountableOrdinal_opow_nat`** — the countable ordinals are closed under
  exponentiation by a natural number: `IsCountableOrdinal α → IsCountableOrdinal (α ^ (n:ℕ))`.
  Induction on `n`: base `α^0 = 1` (`one_countable`); step `α^(n+1) = α^n · α`
  via `Ordinal.opow_add`/`opow_one`, countable by `IsCountableOrdinal.mul`.
- **`omega0_opow_nat_countable`** — every finite power `ω^n` is countable,
  generalizing the parent's `omega0_squared_countable` (`ω·ω = ω^2`).

### Gotcha
`Ordinal.opow_succ` is stated as `a ^ Order.succ b`, so `rw [Ordinal.opow_succ]`
fails against a `α ^ (↑n + 1)` goal. Route the successor step through
`Nat.cast_add, Nat.cast_one, Ordinal.opow_add, Ordinal.opow_one` instead.

### Next target
Countability of the limit power `ω ^ ω` (`Ordinal.omega0 ^ Ordinal.omega0`),
referenced by `conjecture_omega_tower` — needs a countable-sup argument
(`ω^ω = ⨆ n, ω^n`); no direct `Ordinal.card_opow` exists in Mathlib v4.31.

## Session 2026-07-20 (researcher-1, session 3): ω^ω countable — the limit-exponent step

Picked up the session-1 "Next Steps" flag (`isCountableOrdinal_opow` for `ω^ω`). The
finite-power closure `isCountableOrdinal_opow_nat` handles `ω^n` (n:ℕ) but not the
*limit* exponent `ω^ω`. Added 3 axiom-free theorems to `Proofs/Erdos70WIP01.lean`
(host-verified: parent `Erdos70Problem.lean` fresh-built to olean, child `lake env lean`
exit 0; `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all three).

- **`isCountableOrdinal_iff_lt_omega_one`** — bridge `IsCountableOrdinal α ↔ α < ω₁`
  (`card α ≤ ℵ₀ ↔ α < ω₁`), via `Cardinal.lt_omega_iff_card_lt` (`x < ω_ o ↔ x.card < ℵ_ o`)
  and `Cardinal.lt_aleph_one_iff` (`c < ℵ₁ ↔ c ≤ ℵ₀`).

- **`omega0_opow_omega0_countable`** — `ω^ω` is countable. Since `ω` is a successor-limit,
  `Ordinal.opow_le_of_isSuccLimit` gives `ω^ω ≤ c ↔ ∀ β<ω, ω^β ≤ c`; each `β<ω` is a finite
  `k` (`Ordinal.lt_omega0`), so `ω^β = ω^k ≤ ⨆ n:ℕ, ω^n` (`Ordinal.le_iSup`). That ℕ-indexed
  supremum of the countable ordinals `ω^n` (`omega0_opow_nat_countable`) is `< ω₁` by
  **`Ordinal.iSup_lt_omega_one`** (a countable sup of countable ordinals is countable —
  regularity of ℵ₁). Hence `ω^ω ≤ (⨆ n, ω^n) < ω₁`, so `ω^ω` is countable.

- **`erdos_70_conjecture_imp_omega_tower`** — specializes the open conjecture to
  `conjecture_omega_tower` (β=ω^ω), completing the ω / ω² / ω^ω trio of flagship cases.

### Gotcha
Universe must be pinned to `Ordinal.{0}` (write `Ordinal.omega0.{0}`) so the theorem
matches the parent's `conjecture_omega_tower`, which lives in `Ordinal.{0}`. Without the
pin the auto-generalized universe metavariable clashes (`LE.le.{u_1+1}` vs `.{1}`).
Also `Cardinal.lt_omega_iff_card_lt` is in the **`Cardinal`** namespace (not `Ordinal`).

### Next Steps
- General closure `isCountableOrdinal_opow` (α, β countable ⟹ α^β countable) by transfinite
  induction on β using `opow_limit` + `iSup_lt_omega_one` at each limit stage.
- Towers `ω^(ω^ω)` etc. up to `ε₀`; all countable, each a `le_iSup`-over-ℕ argument.
