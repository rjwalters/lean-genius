# Knowledge Base: erdos-30-wip-01

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

## Session 2026-07-22 (researcher-1-3) — Erdős–Turán counting UPPER bound (0-axiom)

**Mode**: FRESH (EMPTY → ACT) · **Outcome**: progress — converted the classical
Erdős–Turán (1941) upper bound from parent-file comments/axioms into 6 axiom-free
theorems in a new companion `proofs/Proofs/Erdos30WIP01.lean` (Docker-verified
v4.31.0; `#print axioms` on all six = `[propext, Classical.choice, Quot.sound]`).

**Mechanism** (difference-map counting, the clean route — avoids the fiddly
sum-over-{2,…,2N} bookkeeping):
- For a Sidon set `A`, the map `diffMap (a,b) = (a:ℤ) − b` is **injective on the
  off-diagonal** (`diffMap_injOn`): `a − b = c − d` rewrites to `a + d = c + b`,
  and `HasDistinctSums` forces `{a,d} = {c,b}`; the branch `a = b` is killed by
  off-diagonality. Uses the parent's `sidon_iff_distinct_sums`.
- The image lands in the `2N` nonzero integers of `Icc (−N) N` (via
  `Int.card_Icc` + `Finset.card_erase_of_mem`), so
  `A.offDiag.card ≤ 2N` (`sidon_offDiag_card_le`), and
  `Finset.offDiag_card : |A.offDiag| = |A|² − |A|` gives `|A|² ≤ 2N + |A|`
  (`sidon_card_sq_le`).
- Squeeze `(|A|−1)² ≤ |A|(|A|−1) ≤ 2N` then `Nat.le_sqrt` ⟹
  `|A| ≤ ⌊√(2N)⌋ + 1` (`sidon_card_le_sqrt`).
- `Finset.sup_le` passes the per-set bound to the supremum:
  `sidonNumber N ≤ ⌊√(2N)⌋ + 1` (`sidonNumber_le_sqrt`), and a `Real.sqrt_sq` /
  `Real.sqrt_le_sqrt` cast gives `(sidonNumber N : ℝ) ≤ √(2N) + 1`
  (`sidonNumber_le_real`) — the `√N` shape of Erdős–Turán.

**Reusable idioms (v4.31)**:
- `obtain ⟨m, rfl⟩ : ∃ m, A.card = m + 1` FAILS (`subst` on a non-variable
  `A.card`); use `obtain ⟨m, hm⟩ … ; rw [hm] at hcard ⊢` instead.
- `Nat.le_sqrt : m ≤ Nat.sqrt n ↔ m * m ≤ n`; `Nat.sqrt_le' n : Nat.sqrt n ^ 2 ≤ n`.
- `Int.card_Icc : #(Icc a b) = (b + 1 − a).toNat` — `omega` closes the `.toNat`
  arithmetic after `Finset.card_erase_of_mem`.
- `(Nat.sqrt n : ℝ) ≤ Real.sqrt n` via `rw [← Real.sqrt_sq (positivity)]` then
  `Real.sqrt_le_sqrt` + `exact_mod_cast (Nat.sqrt_le' n)`.

**Mathlib gap**: no Sidon/B₂-set API, no roots-of-unity/Vandermonde discriminant
product — build the counting bound from `Finset.offDiag_card` / `Int.card_Icc` /
`Nat.le_sqrt`.

**STILL OPEN / out of scope** (untouched, honest): the `N^{1/4}` constant
refinement (Erdős–Turán exact form `√N + N^{1/4} + 1`, and Lindström/BFR/CHO
improvements), Singer's projective-plane LOWER bound `h(N) ≥ (1−o(1))√N` (deep
finite geometry), and the OPEN `$1000` Erdős–Turán conjecture (error `≤ N^ε` for
all `ε > 0`) which stays a `Prop`.
