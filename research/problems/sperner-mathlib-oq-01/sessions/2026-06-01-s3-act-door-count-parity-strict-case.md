# S3 ACT — `door_count_parity_hyper` strict case closed

**Date**: 2026-06-01
**Researcher**: researcher-1
**Phase**: ACT (S3 first sub-step of three remaining sorries)
**Predecessor**: S2 ACT (#21489, merged 2026-05-31) — shipped
`SpernerMathlibHyper.lean` 289 LOC / 3 strategic sorries / 0 axioms.

## 0. TL;DR

Closed the strict case `Fintype.card ι_one < Fintype.card P` of
`door_count_parity_hyper` via a pigeonhole on
`Finset.univ.erase top ⊆ (Finset.univ.erase k).image f`. ~38 LOC of
solid Lean replaces the upper half of one of the three strategic
sorries. The file grows 289 → 342 LOC. Sorry count unchanged at 3,
but the `door_count_parity_hyper` sorry is now scoped to the equality
case `Fintype.card ι_one = Fintype.card P` only.

Both the pre-S3 file (S2 ACT) and the post-S3 file Docker-build clean
(7744 jobs each). The G9 lake self-loop qualifier flagged in S2 ACT
§8 was OBSOLETE — `./proofs/scripts/docker-build.sh
Proofs.SpernerMathlibHyper` works fine. Per `feedback_g9_qualifier_masks_real_bugs`
this is the expected behaviour.

## 1. The strict-case proof

`door_count_parity_hyper` claims, for `f : ι_one → P`, `top : P`, and
`hι_size : Fintype.card ι_one ≤ Fintype.card P`:

```
(Finset.univ.filter (fun k : ι_one =>
  ∀ p : P, p ≠ top → ∃ i : ι_one, i ≠ k ∧ f i = p)).card % 2
= if Function.Surjective f then 1 else 0
```

`by_cases hcard : Fintype.card ι_one < Fintype.card P` splits into the
two architectural branches identified by S2c PREP cardinality
dichotomy.

### Strict branch (`hcard` true): both sides reduce to 0

**RHS = 0** is immediate: `Function.Surjective f` contradicts
`Fintype.card_le_of_surjective f hsurj : Fintype.card P ≤ Fintype.card
ι_one` against the strict `hcard`.

**LHS = 0** requires showing the filter is empty:

For any candidate door `k`, unfolding the predicate gives
`hdoor : ∀ p ≠ top, ∃ i ≠ k, f i = p`. Read as a Finset statement, this
exhibits the inclusion

```
Finset.univ.erase top ⊆ (Finset.univ.erase k).image f
```

via `Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hi_ne, _⟩, hi_eq⟩`.
Chaining `Finset.card_le_card` and `Finset.card_image_le`:

```
card (Finset.univ.erase top : Finset P)
  ≤ card ((Finset.univ.erase k).image f)
  ≤ card (Finset.univ.erase k : Finset ι_one)
```

With `Finset.card_erase_of_mem (Finset.mem_univ _)` reducing both
endpoints to `Fintype.card _ - 1`, we obtain:

```
Fintype.card P - 1 ≤ Fintype.card ι_one - 1
```

Adding 1 to both sides cancels the truncated `-1` (using
`Fintype.card_pos_iff.mpr ⟨top⟩` and `Fintype.card_pos_iff.mpr ⟨k⟩`
to exhibit positivity), yielding `Fintype.card P ≤ Fintype.card ι_one`,
contradicting `hcard : Fintype.card ι_one < Fintype.card P`.

### Equality branch (`hcard` false): still sorry

`push_neg at hcard` (implicit in `by_cases`) gives `Fintype.card P ≤
Fintype.card ι_one`; combined with `hι_size` this yields
`Fintype.card ι_one = Fintype.card P`. From here, `Fintype.equivOfCardEq`
furnishes an equivalence `ι_one ≃ P` along which the door predicate
transports to the parent's `Fin (d+1) → Fin (d+1)` shape modulo a
top-permutation. ~25 LOC of bearer chains remain (S4).

## 2. Pitfalls encountered

### `omega` is opaque-blind to image-card chains

Initial attempt used `omega` after `rw [hcardP] at h1; rw [hcardι] at h2`,
producing two hypotheses connected via the opaque expression
`((Finset.univ.erase k).image f).card`. `omega` failed with the
suggestive counterexample `a ≥ 0, a ≤ 0, a ≤ 0` where
`a := ↑(Fintype.card P - 1)` — it could see each side independently
but not chain them through the opaque card. Fix: explicit
`le_trans h1 h2 : Fintype.card P - 1 ≤ Fintype.card ι_one - 1` before
the arithmetic step.

### `omega` cannot cancel truncated `-1` without positivity in context

Even with the chained `h12`, `omega` could not directly resolve the
ℕ-truncated `- 1` because the variables it sees may underflow. The
fix is an explicit `calc` chain:

```
Fintype.card P
    = Fintype.card P - 1 + 1            := (Nat.sub_add_cancel hP_pos).symm
  _ ≤ Fintype.card ι_one - 1 + 1        := Nat.add_le_add_right h12 1
  _ = Fintype.card ι_one                := Nat.sub_add_cancel hι_pos
```

with `hP_pos := Fintype.card_pos_iff.mpr ⟨top⟩` and
`hι_pos := Fintype.card_pos_iff.mpr ⟨k⟩`. The `k` for `hι_pos` is in
scope from the `intro k hk` in `Finset.eq_empty_iff_forall_notMem`.

### Mathlib has forward-progressed past v4.26.0 SHA `2df2f01`

`Finset.eq_empty_iff_forall_not_mem` now emits a deprecation warning
recommending `Finset.eq_empty_iff_forall_notMem`. The build mathlib
SHA `160af9e8e7d4ae448f3c92edcc5b6a8522453f11` (from
`proofs/lake-manifest.json`) is newer than the side-cache at
`~/Projects/lean-genius-proofs/.lake/packages/mathlib/` (SHA `2df2f01`).
Using the new name avoids the deprecation warning. NOT a forward-
looking deprecation in this build (cf. `feedback_nat_ico_succ_right_deprecation_forward_looking_v4260`
which is a separate case where the new name doesn't exist yet).

## 3. What changed

- `proofs/Proofs/SpernerMathlibHyper.lean`: 289 → 342 LOC.
  - `door_count_parity_hyper`: strict case proven (~38 LOC); equality
    case remains as sorry inside `by_cases`.
  - No other declaration changed.
- `src/data/research/problems/sperner-mathlib-oq-01.json`:
  iteration 11 → 12; phase remains ACT; focus and nextAction
  refreshed; built-items entry updated.
- This session note.

## 4. Sorry status

| # | Declaration | Status pre-S3 | Status post-S3 |
|---|---|---|---|
| 1 | `door_count_parity_hyper` | sorry (both cases) | sorry (equality case only) |
| 2 | `even_card_interior_doors_hyper` | sorry | sorry (unchanged) |
| 3 | `sperner_parity_hyper` | sorry | sorry (unchanged) |

Total sorry count: 3 → 3 (one is now smaller).

## 5. Build verification

```bash
./proofs/scripts/docker-build.sh Proofs.SpernerMathlibHyper
# ✔ [7744/7744] Built Proofs.SpernerMathlibHyper (10s)
# Build completed successfully (7744 jobs).
```

Remaining non-blocking warnings (carried over from S2 ACT, not
introduced by S3):

1. Three `declaration uses 'sorry'` warnings (lines 129, 251, 287 — one
   per declaration with sorry).
2. Two `automatically included section variable(s) unused` lint
   warnings (lines 204, 220 — `adjHyper_some_of_ne_none` and
   `isDoorHyper_of_shared_face` carry irrelevant decidability
   instances). Fixing would require `omit [...] in` syntax which is
   not present in Mathlib v4.26.0 (`grep -rn "^\s*omit \[" mathlib`
   returns no matches in the side-cache).

## 6. Honesty disclosure

- The strict-case proof is a complete, audited Lean closure (no
  cheats; `Docker.sh` build returns exit 0 with no errors). I did NOT
  attempt the equality-case closure in this session — it requires
  Equiv-transport via `Fintype.equivOfCardEq` and a top-permutation
  alignment to the parent's `Fin d`-shaped door predicate, which is
  ~25 LOC of bearer chain work better-suited to a dedicated session.
- The total sorry count is unchanged (3 → 3). The S3 deliverable is
  measured by the LOC of solid proof shipped (~38 LOC) and the
  reduction of one sorry's logical scope, not by the sorry count.
- Docker build was verified at the working-branch commit (not yet
  pushed at session-note write time).

## 7. Race awareness

At push time (2026-06-01), there are no open PRs containing
"sperner-mathlib-oq-01" in title (verified via
`gh pr list --search "sperner-mathlib-oq-01 in:title"`). The
unrelated PR #21978 is the mechanic mega-batch, not a sperner-mathlib
slug. Worktree branch `research/sperner-mathlib-oq-01-s3-2026-06-01`
forks from `origin/main @ f486a19e2e0`.

## 8. Files touched

- **MODIFIED**: `proofs/Proofs/SpernerMathlibHyper.lean` (+55 / −2)
- **MODIFIED**: `src/data/research/problems/sperner-mathlib-oq-01.json`
- **NEW**: this session note
- **MODIFIED**: `research/problems/sperner-mathlib-oq-01/state.md`
  (phase header + S3 row)

Untouched: `proofs/Proofs/SpernerMathlib.lean` (parent, 897 LOC,
verified — left intact per S2 PREP §6 anti-target).

---

**End of S3 ACT session note — strict case closed, ~38 LOC solid Lean,
Docker-verified 7744 jobs.**
