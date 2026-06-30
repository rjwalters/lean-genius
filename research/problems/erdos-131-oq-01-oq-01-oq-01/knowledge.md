# Erdős #131 — Davenport sharpening of the non-dividing size bound

**Slug:** `erdos-131-oq-01-oq-01-oq-01`
**Lean file:** `proofs/Proofs/Erdos131DavenportBound.lean`
**Status:** verified, 0-axiom (propext / Classical.choice / Quot.sound only)

## Summary

For a non-dividing set `A ⊆ ℕ` (no `a ∈ A` divides the sum of any `≥2`-element
subset of `A \ {a}`) and any `a ∈ A` with `a ≥ 2`:

    |A| ≤ a + 1            (davenport_nondividing_card_bound)

This **sharpens** the EGZ follow-up (`erdos-131-oq-01-oq-01`) bound `|A| ≤ 2a − 1`.

**Why the improvement is possible.** The EGZ argument applies
`Int.erdos_ginzburg_ziv` and only consumes the *size-exactly-`a`* zero-sum
subset (the EGZ constant `s(ℤ/aℤ) = 2a − 1`). But non-dividing forbids a zero-sum
subset of **every** size `≥ 2`. The right invariant is therefore the **Davenport
constant** `D(ℤ/aℤ) = a` (max zero-sum-free length is `a − 1`), which is smaller.

## Mechanism

Inside `B := A \ {a}` (|B| = |A| − 1):
1. At most one element of `B` is `≡ 0 (mod a)` — two would be a size-2 zero-sum.
2. The remaining `≥ a` elements have nonzero residue mod `a`.
3. Davenport (`exists_nonempty_subset_sum_dvd`) gives a nonempty zero-sum subset;
   since every element is nonzero mod `a`, it has size `≥ 2` → contradiction.

So `|B| ≤ a`, i.e. `|A| ≤ a + 1`.

## Built infrastructure

- `exists_nonempty_subset_sum_dvd (a) (1 ≤ a) (s) (a ≤ |s|) : ∃ t ⊆ s, t.Nonempty ∧ a ∣ t.sum id`
  — the cyclic Davenport bound `D(ℤ/aℤ) ≤ a`, **built from scratch** (Mathlib has
  no Davenport constant / zero-sum-free sequences). Proof = prefix-sum pigeonhole:
  sort `s` to a nodup list `L`; the `|L|+1` prefix sums reduced mod `a` collide in
  `ZMod a` (`Fintype.exists_ne_map_eq_of_card_lt`); the block between the colliding
  indices is a nonempty nodup sublist whose `toFinset` sum is `≡ 0`.
- Corollaries: `davenport_card_le_min_succ` (|A| ≤ min(A)+1), `davenport_le_egz`
  (a+1 ≤ 2a−1), `davenport_strictly_sharper` (a+1 < 2a−1 for a ≥ 3),
  `two_in_card_le_three` (a=2 recovery), `not_nondividing_of_card_gt`,
  `davenport_bound_sharp_at_two` ({2,4,5}).

## Mathlib gaps found

- No cyclic **Davenport constant** / zero-sum-free sequence bound. EGZ is present
  (`Int.erdos_ginzburg_ziv`) but it is the *stronger-hypothesis / weaker-conclusion*
  constant (`2n−1`, fixed subset size `n`), not the Davenport `n`. This file's
  `exists_nonempty_subset_sum_dvd` fills the gap for the cyclic case and is reusable.

## Lean gotchas (v4.26.0)

- `<+` (List.Sublist) notation is NOT in scope under `open Finset`; write
  `List.Sublist a b` explicitly.
- `Finset.sum_pair` not found — use `Finset.dvd_sum` for `a ∣ {x,y}.sum`.
- `self_eq_add_right.mp` failed to resolve; `linear_combination -h2` is robust in
  `ZMod a` (CommRing) to get `b = 0` from `c = c + b`.
- `({x}).sum id = x` is NOT closed by `Finset.sum_singleton` alone (leaves
  `id x = x`); use `simp`.
- A multi-line `have h : T :=` with a leading `+` on a continuation line fails to
  parse; put the binary op's LHS and the `=`/operator on the same line.
- `ZMod.natCast_zmod_eq_zero_iff_dvd` is **deprecated** → `ZMod.natCast_eq_zero_iff`.

## Next steps / open questions

- (`-oq-01`) Is `|A| ≤ a + 1` sharp for `a ≥ 3`? Needs a non-dividing set with
  one `≡0` element + `a−1` equal-nonzero-residue elements, all distinct AND
  non-dividing at every element (cross-element constraint may force smaller).
- (`-oq-02`) Aggregate `|A| ≤ min(A)+1` over residue classes / truncations to get
  an elementary global `F(N)` bound toward Pham–Zakharov `N^{1/4+o(1)}`.

## Session log

### 2026-06-21 (Session 1) — FRESH follow-up, COMPLETED
- **Mode:** REVISIT (pool empty) → built a strong follow-up to my own merged
  EGZ entry (`erdos-131-oq-01-oq-01`, PR #27277).
- Identified the EGZ→Davenport gap, confirmed Mathlib lacks Davenport, built the
  prefix-sum pigeonhole Davenport bound, proved `|A| ≤ a+1`, 0-axiom verified.
- Docker build `Proofs.Erdos131DavenportBound` GREEN (7743/7743).
