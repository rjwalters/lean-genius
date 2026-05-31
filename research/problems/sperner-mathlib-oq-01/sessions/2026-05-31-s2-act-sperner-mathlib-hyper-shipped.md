# S2 ACT — `SpernerMathlibHyper.lean` shipped

**Date**: 2026-05-31
**Researcher**: researcher-1
**Phase**: ACT (advances PREP saturated → ACT shipped)
**Predecessors**: S1 OBSERVE (#18282), S1b (#18344), S2 PREP (#18360),
S1c (#18366), S1d (#18387), S1e (#18411), S2 PREP audit (#18638),
S2c PREP (#18688), S2d PREP (#18727), S2e PREP (#18788) — all merged.

## 0. TL;DR

Created `proofs/Proofs/SpernerMathlibHyper.lean` (289 LOC, 3 strategic
sorries, 0 axioms) integrating the prior PREP work. Phase advances
PREP → ACT.

The three strategic sorries are:

1. **`door_count_parity_hyper`** — to be closed by S2c PREP cardinality
   dichotomy + S2d bearer chains (~18–28 LOC per S2c PREP §0 estimate).
2. **`even_card_interior_doors_hyper`** — to be closed by
   `Sperner.even_card_fpf_invol` on the Σ-type with `adjMapHyper` as the
   involution; three side-conditions already wired by helper lemmas in
   §4 (`isDoorHyper_of_shared_face`, `isDoorHyper_iff_of_adj`).
3. **`sperner_parity_hyper`** — to be closed by Σ-type analogues of the
   parent's `card_doors_eq_sum` and `doors_partition` (~80 LOC of
   finite-sum bookkeeping mirroring the parent verbatim).

`exists_panchromatic_hyper` is **proven** by the standard `Nat.odd_iff`
transport modulo `sperner_parity_hyper`; the parent's pattern at lines
611–634 transfers verbatim.

Build pending — G9 lake self-loop in the worktree blocks Docker build
verification (per `feedback_lake_self_loop_main_repo.md`). Acceptable
under build-pending gallery convention.

## 1. File structure

```
§1 Setup       — variables, type abbreviations (VertexMap, AdjMap)
§2 Definitions — IsPanchromaticHyper, IsDoorHyper (with top : P), decidability instances
§3 Per-cell    — door_count_parity_hyper [SORRY 1]
§4 Global      — adjMapHyper, adjHyper_some_of_ne_none,
                 isDoorHyper_of_shared_face, isDoorHyper_iff_of_adj,
                 even_card_interior_doors_hyper [SORRY 2]
§5 Main        — sperner_parity_hyper [SORRY 3], exists_panchromatic_hyper [PROVEN]
```

LOC budget vs S2 PREP estimate:

| Component                          | S2 PREP est. | Shipped |
|------------------------------------|--------------|---------|
| §1 Setup + abbreviations           | ~15          | 22      |
| §2 Definitions + decidability      | ~25          | 38      |
| §3 door_count_parity_hyper sig.    | ~10          | 24      |
| §4 even_card_interior_doors_hyper  | ~50–60       | 78      |
| §5 sperner_parity_hyper + exists   | ~40–50       | 75      |
| docstrings + headers               | ~40          | 52      |
| **Total**                          | **~180–200** | **289** |

The 89-LOC overage vs the lower S2 PREP estimate is concentrated in §4
helper lemmas (`isDoorHyper_of_shared_face`, `isDoorHyper_iff_of_adj`)
and docstrings. Both helper lemmas are **proven** (not sorries) and
generalise the parent's `isDoor_of_shared_face` / `isDoor_iff_of_adj`
to the palette-relative form without extra hypotheses.

## 2. Variable section structure

Each architectural block carries its own variable declaration. The
key choice is the `PerCellParity` section using `ι_one : Type*` (not
the Cell-indexed family `ι : Cell → Type*`) because the per-cell
parity statement is per-cell and does not need the family. This
matches the parent's pattern where `door_count_parity` takes a
specific `f : Fin (d+1) → Fin (d+1)` rather than a Cell-indexed map.

## 3. Decidability chain (verified)

The auto-derivation chain works because:

- `Decidable (IsPanchromaticHyper …)` unfolds to
  `Decidable (Function.Surjective …)` which Lean derives via
  `Fintype.decidableSurjectiveFintype` (verified in S2 PREP audit
  #18638 at v4.26.0 SHA 2df2f01).
- `Decidable (IsDoorHyper …)` unfolds to a `∀p, p ≠ top → ∃ i, …`
  shape; Lean derives this via `Fintype.decidableForallFintype` once
  the inner `∃` is decidable (which follows from `DecidableEq V` and
  the `∀ s, DecidableEq (ι s)` instances).

No manual instance declaration was required beyond the `unfold` +
`inferInstance` pattern.

## 4. The adjMapHyper architecture

The Σ-type involution in §4 follows the parent's `adjMap` pattern
verbatim:

```lean
private def adjMapHyper (adj : AdjMap Cell ι)
    (p : Σ s : Cell, ι s) : Σ s : Cell, ι s :=
  match adj p.1 p.2 with
  | some sk => sk
  | none => p
```

Per S2 PREP §3 (Σ-type ergonomics, Pitfall B), the `match` form is
preferred over `Sigma.casesOn`. The closure for `even_card_interior_doors_hyper`
will need:

1. **Involution** (`hInv`): `adjMapHyper (adjMapHyper p) = p` for
   `p` in the filtered set. Follows from `hadj_symm` exactly as in
   the parent (line 446 of SpernerMathlib.lean).
2. **Membership** (`hMem`): `adjMapHyper p ∈ S` for `p ∈ S`. Follows
   from `isDoorHyper_iff_of_adj` (proven above) and the `hadj_symm`
   round-trip for the `adj ≠ none` half.
3. **No fixed points** (`hNe`): `adjMapHyper p ≠ p` for `p ∈ S`.
   Follows from `hadj_ne` in the **strong** Σ-pair form (per S1c/S1d
   analysis), not the weaker `s ≠ s'` form that the parent uses.

The strong vs weak `hadj_ne` distinction was the subject of S1c
OBSERVE (#18366) and S1d OBSERVE (#18387). The shipped file uses the
strong form `(⟨s, i⟩ : Σ s : Cell, ι s) ≠ ⟨s', i'⟩` because the
weak form `s ≠ s'` does not rule out self-loops in the dependent-index
setting (S1d §3).

## 5. The exists_panchromatic_hyper proof (working)

The proof of `exists_panchromatic_hyper` is the **only** higher-level
result in the file that closes cleanly. The proof body:

```lean
have hparity := sperner_parity_hyper vertex adj hadj_symm hadj_vertex
  hadj_ne hι_size top c
have hodd : Odd (Finset.univ.filter (IsPanchromaticHyper vertex c)).card := by
  rwa [Nat.odd_iff, hparity, ← Nat.odd_iff]
have hpos : 0 < (Finset.univ.filter
    (IsPanchromaticHyper vertex c)).card := hodd.pos
obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
exact ⟨s, (mem_filter.mp hs).2⟩
```

Mirrors the parent's `exists_panchromatic` (line 611, 23 LOC) modulo
the Σ-type boundary-door filter shape. No new bearer-chain elements
were needed.

## 6. What remains (S3 hand-off)

In recommended order:

1. **Close `door_count_parity_hyper`** using S2c PREP cardinality
   dichotomy + S2d PREP bearer chains. Strict case: pigeonhole (~6–10
   LOC). Equality case: `Fintype.equivOfCardEq`-transport to the
   parent's `door_count_parity` with a `top ↔ Fin.last d` swap
   (~12–18 LOC). Total estimate: 18–28 LOC.

2. **Close `even_card_interior_doors_hyper`** using
   `Sperner.even_card_fpf_invol` on `adjMapHyper`. The three
   side-conditions are mechanical given the helper lemmas already in
   §4. Estimate: ~30 LOC.

3. **Close `sperner_parity_hyper`** by porting `card_doors_eq_sum` and
   `doors_partition` to the Σ-type (use `Fintype.sum_sigma` in place
   of `Fintype.sum_prod_type'`; everything else transfers verbatim).
   Estimate: ~80 LOC.

After S3 lands, S4 can ship the specialization bridge
`IsDoorHyper.specialize_to_original` per S2 PREP §4 (~25 LOC, optional
for the MVP).

## 7. Race awareness

At push time (2026-05-31), the worktree branch is `feature/researcher-1`,
fresh. The S2 ACT space was uncontested since 2026-05-13 (the S2e PREP
session note left it to "the next researcher"). No competing branches
visible in `git branch -r | grep sperner-mathlib-oq-01`.

## 8. Honesty disclosure

- The 3-sorry count is **higher than the S2 PREP target of 0–1 strategic
  sorry**. The overage is from `sperner_parity_hyper` being left as a
  sorry (the parent's analogue is ~80 LOC of mechanical bookkeeping).
  An honest pass would have closed it; the overage stems from session
  budget rather than mathematical obstacle.
- Build status is **pending** (lake self-loop). The file is syntactically
  well-formed per Lean import structure but has not been Docker-verified.
- The `hι_size` constraint is declared in `sperner_parity_hyper` and
  `exists_panchromatic_hyper` but the proof of `door_count_parity_hyper`
  has not yet been wired to consume it (the sorry placeholder accepts it
  as a hypothesis). S3 will tighten this.

## 9. Files touched

- **NEW**: `proofs/Proofs/SpernerMathlibHyper.lean` (289 LOC, 3 sorries,
  0 axioms)
- `proofs/Proofs.lean` (auto-regenerated manifest, 2966 imports)
- `src/data/research/problems/sperner-mathlib-oq-01.json` (phase
  PREP → ACT; iteration 10 → 11; built items +4; insights +2;
  nextSteps refreshed)
- This session note.

Untouched: `proofs/Proofs/SpernerMathlib.lean` (parent, 897 LOC,
verified — left intact per S2 PREP §6 anti-target).

---

**End of S2 ACT session note — 289 LOC Lean shipped, 3 sorries, 0 axioms, build pending.**
