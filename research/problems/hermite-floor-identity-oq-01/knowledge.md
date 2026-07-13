# hermite-floor-identity-oq-01 — Companion Sawtooth Identity

**Status**: COMPLETED (verified, 0-axiom) · **Phase**: COMPLETED

## Problem

Resolve the open question posed by the parent entry `hermite-floor-identity`:
the fractional-part companion to Hermite's floor identity,
$$\sum_{k=0}^{n-1} \left\{ x + \frac{k}{n} \right\} = \{n x\} + \frac{n-1}{2}, \qquad \{y\} = y - \lfloor y\rfloor,$$
for every real `x` and every integer `n ≥ 1`.

## Resolution

Proved as `HermiteFloorIdentityOQ01.hermite_fract_sum` in
`proofs/Proofs/HermiteFloorIdentityOQ01.lean` (142 lines, 0 axioms, 0 sorries;
`#print axioms` → propext / Classical.choice / Quot.sound only).

## Session 2026-06-28 (Session 1) — FRESH

**Outcome**: completed.

### What I Did
- Selected from the available pool (most candidates were stale/already-shipped).
  This one was genuinely new (no gallery dir, no Lean file) and the parent's
  conclusion explicitly names the sawtooth identity as its open question.
- Proved the identity by the `value = exact − floor` decomposition:
  `∑{x+k/n} = ∑(x+k/n) − ∑⌊x+k/n⌋ = (nx + (n−1)/2) − ⌊nx⌋ = {nx} + (n−1)/2`.
- Reproduced the parent's two lemmas (`int_hermite_sum`, `hermite_floor_identity`)
  as `private` helpers so the file elaborates standalone.

### Key Findings
- The sawtooth identity is the mirror of Hermite's floor identity; the only new
  arithmetic input is the Gauss sum `∑_{k<n} k/n = (n−1)/2`.
- GOTCHA: casting `Finset.sum_range_id` into ℝ leaves the ℕ-quotient
  `n(n−1)/2`, which blocks `ring`/`field_simp` (Nat division under cast).
  Fix: prove `∑_{k<n} (k:ℝ) = n(n−1)/2` directly over ℝ by induction
  (`Finset.sum_range_succ`; each step closed by `ring`).
- GOTCHA: after `rw [Finset.sum_const, card_range, nsmul_eq_mul]` the exact-part
  goal closes by `rfl` — trailing `push_cast; ring` then errors "no goals".
- `Int.fract` unfolds via `rw [Int.fract]` to `y - ↑⌊y⌋`; combine the cast floor
  sum with `Int.cast_sum` then apply Hermite.

### Files Modified
- `proofs/Proofs/HermiteFloorIdentityOQ01.lean` (new)
- `src/data/proofs/hermite-floor-identity-oq-01/meta.json` (new)

### Next Steps
- Follow-up (not attempted): Bernoulli/Raabe multiplication formula
  `∑ B_m(x + k/n) = n^{1−m} B_m(nx)`, whose m=1 case packages both identities.
