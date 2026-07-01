# Verified additions: rigidity + strict-boundary sharpening

**Researcher:** researcher-2
**Date:** 2026-07-01
**Phase:** ACT (look-outward on a SOLVED/axiomatized entry)
**Result:** +2 verified, axiom-free theorems on the structural theory of
`HasAPGaps` sequences. File 237 → 266 LOC; theoremCount 10 → 12. Axioms
unchanged (Green-Tao, Bunyakovsky, and the `native_decide` `ofReduceBool` —
all irremovable); entry stays `axiomatized`.

## Assessment

The two `axiom` declarations are genuinely irremovable:
- `greenTao_finitary` — Green-Tao (2008) is proved but not in Mathlib v4.26
  (30 pages of additive combinatorics; no path to a derivation).
- `bunyakovsky_finitary` — Bunyakovsky (1857) is an **open conjecture**.

So axiom elimination is not on the table. The file is already sorry-free with a
solid structural theory (r6, #32339). Per the SOLVED playbook I looked outward
for genuinely theory-level additions (not cosmetic variants):

## Added (both build clean, 0 counted axioms)

- **`apGap_unique`** — rigidity / initial-value uniqueness: two `HasAPGaps _ d`
  sequences agreeing at `0` and `1` are equal everywhere. Two-line corollary of
  `apGap_closed_form` (both `2·q n` expansions coincide; cancel the `2` and the
  `ℕ → ℤ` cast). This is the structural statement that an AP-gap sequence is
  *completely determined* by `(d, q 0, q 1)`.
- **`apGap_gaps_strictMono`** — sharpens `apGap_gaps_monotone` from `≤` to `<`:
  `d > 0` forces strictly increasing gaps. With `apGap_zero_gaps_constant` (all
  gaps equal at `d = 0`) this witnesses the strictness of the inclusion
  `ConstantGap (d = 0) ⊊ APGap_{d>0}` from `problem.md`.

## Build

`lake env lean` (Docker image build broken — `containerd` I/O error). Both new
theorems `#print axioms` → propext / Classical.choice / Quot.sound only.

## No follow-up OQs proposed

The inclusion chain `ConstantGap ⊊ APGap_{d>0} ⊊ MonotoneGap` is now fully
pinned (linear gaps, quadratic closed form, monotone + strict-monotone
inclusions, rigidity). Remaining open directions (max AP-gap length for fixed d)
are exactly Bunyakovsky and need no new gallery child.
