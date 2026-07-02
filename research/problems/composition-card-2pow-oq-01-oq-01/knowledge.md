# Knowledge: Compositions of n into exactly k parts = C(n-1, k-1)

## Summary

**Target.** For `n ≥ 1`, `k ≥ 1`, the number of compositions of `n` into exactly
`k` positive parts is the binomial coefficient `C(n-1, k-1)`; summing over `k`
recovers the total `2^(n-1)` (the parent entry `composition-card-2pow-oq-01`).

**Status.** A complete `0`-sorry Lean proof is written
(`proofs/Proofs/CompositionCard2PowOQ01OQ01.lean`). Every Mathlib lemma used was
verified by name against the pinned Mathlib source. **Machine build not yet
confirmed** this session: the local toolchain was unusable (Mathlib/aesop
`.olean` files missing — being rebuilt by a concurrent process — and host disk
fell below 1 GB, so both `lake env lean` and `docker-build.sh` failed for
environment reasons, not proof errors). Verification is pending a healthy build
environment.

## Approach (proved, pending machine check)

Mathlib already contains the "bar / no-bar in each of the `n-1` internal gaps"
bijection between compositions and gap subsets:

- `compositionEquiv n     : Composition n      ≃ CompositionAsSet n`
- `compositionAsSetEquiv n : CompositionAsSet n ≃ Finset (Fin (n-1))`

The only genuinely new ingredient is the **length ↔ subset-cardinality
dictionary**: for `n ≥ 1`, `(compositionAsSetEquiv n cs).card + 1 = cs.length`.
Proof: exhibit `cs.boundaries = {0, last} ⊎ (gap subset shifted by +1)` and count.
The shift `gapEmb n i = ⟨1 + i, _⟩ : Fin (n-1) ↪ Fin (n+1)` lands on the internal
boundary positions; `0` and `Fin.last n` are the two non-internal boundaries and
are distinct for `n ≥ 1`, so `boundaries.card = (gap subset).card + 2`. Combined
with `CompositionAsSet.card_boundaries_eq_succ_length` this gives the dictionary.

Then:
1. Transport `{c : Composition n // c.length = k}` through
   `(compositionEquiv n).trans (compositionAsSetEquiv n)` with
   `Equiv.subtypeEquiv`, converting the constraint `c.length = k` to
   `(gap subset).card = k - 1` (uses the dictionary + `k ≥ 1`, `n ≥ 1`, `omega`).
2. `Fintype.card_finset_len : # {s : Finset (Fin m) // s.card = j} = C(m, j)`
   gives the count `C(n-1, k-1)`.
3. Sum over `k`: reindex `Icc 1 n → range n` (map by `+1`), then
   `Nat.sum_range_choose (n-1) : ∑_{j<n} C(n-1, j) = 2^(n-1)`.

## Key Mathlib API (all name-checked against source)

- `compositionEquiv`, `compositionAsSetEquiv`, `CompositionAsSet.boundaries`,
  `CompositionAsSet.zero_mem` / `getLast_mem`,
  `CompositionAsSet.card_boundaries_eq_succ_length`
- `Composition.toCompositionAsSet_length` (length preserved by `compositionEquiv`)
- `Fintype.card_finset_len` (`Mathlib/Data/Fintype/Powerset.lean`)
- `Nat.sum_range_choose` (`Mathlib/Data/Nat/Choose/Sum.lean`)
- `Equiv.subtypeEquiv`, `Equiv.trans_apply`, `Fintype.card_congr`
- `Finset.card_insert_of_notMem`, `Finset.card_map`, `Finset.sum_map`,
  `Nat.sub_add_cancel`, `Fin.ext`

## Theorems in the file

- `equiv_card_add_one` — the length/cardinality dictionary (the new lemma)
- `card_finset_card_eq` — `# {s : Finset (Fin m) // s.card = j} = C(m, j)`
- `card_composition_length_eq` — **main:** `# {c // c.length = k} = C(n-1, k-1)`
- `sum_choose_shift` — `∑_{k=1}^n C(n-1, k-1) = 2^(n-1)`
- `sum_card_composition_length` — the refined counts sum to `2^(n-1)`

## Edge cases handled

- The per-`k` formula requires `k ≥ 1`: at `k = 0` there are `0` compositions but
  `C(n-1, -1)` truncates to `C(n-1, 0) = 1`, so `k = 0` is excluded and the sum
  runs over `Icc 1 n`.
- `n = 1`: `Fin (n-1) = Fin 0` is empty; the "not all equal" endpoint arguments
  are vacuously handled by `omega` from contradictory hypotheses.

## Next steps

1. Rebuild in a healthy environment: `./proofs/scripts/docker-build.sh
   Proofs.CompositionCard2PowOQ01OQ01`; confirm `#print axioms` shows only the
   ordinary foundational axioms (target: 0 `sorry`, 0 extra axioms).
2. On success, add the gallery entry `src/data/proofs/composition-card-2pow-oq-01-oq-01/`
   (meta.json + annotations) and mark the pool problem `completed`.

## Session log

### 2026-07-02 (Session 1) — FRESH
- **Mode**: FRESH. **Outcome**: complete proof written, machine build blocked by env.
- Selected after screening the stale candidate pool (most "available" leaves were
  already merged; verified genuinely-open via `git log origin/main`).
- Wrote the full `0`-sorry proof; hand-verified all Mathlib lemma names against
  the pinned source. Could not machine-check: missing oleans + <1 GB disk.
- Aristotle MCP was unavailable ("Resource not found").
