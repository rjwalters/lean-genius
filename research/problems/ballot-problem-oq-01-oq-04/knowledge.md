# Problem: ballot-problem-oq-01-oq-04

## Summary

**Problem**: Prove the Chung-Feller theorem — that among all $\binom{2n}{n}$ balanced lattice paths, exactly $C_n$ have each fixed number $k \in \{0,\ldots,n\}$ of upsteps above the $x$-axis — via an explicit bijection using the cycle lemma.

**Status**: COMPLETED with axiom eliminated (Session 7, 2026-04-28)

**Key files (three-file architecture)**:
- `proofs/Proofs/BallotProblemOQ01OQ04Core.lean` — definitions and cycle-lemma bridge (0 axioms, 0 sorries)
- `proofs/Proofs/BallotProblemOQ01OQ04OQ01.lean` — explicit bijection proof (0 sorries, 0 axiom uses)
- `proofs/Proofs/BallotProblemOQ01OQ04.lean` — gallery face: re-exports `chung_feller_uniform'` as `chung_feller_uniform` (0 axioms, 0 sorries)

**Net effect**: gallery axiomCount 1 → 0; status `axiomatized` → `verified`.

---

## Session 2026-04-28 (Session 7) — Eliminate the chung_feller_uniform axiom

**Mode**: FRESH (continuation; refactor only, no new math)
**Outcome**: completed

### What I Did

Refactored the proof family into three files so that the gallery face can
re-export the bijection-proved theorem instead of axiomatizing it:

1. Created `BallotProblemOQ01OQ04Core.lean` containing all definitions and
   cycle-lemma bridge lemmas previously in the parent: `IsBalancedPath`,
   `balanced_length`, `balanced_sum_zero`, `prepend_mem_kCountedSequence`,
   `prepend_one_good_rotation`, `prepend_unique_good_rotation`,
   `prepend_length`, `prepend_sum`, `balanced_path_total`, `pathHeight`,
   `upstepsAboveAxis`, `upstepsAboveAxisC`, `balancedPathsOfType`,
   `isBalancedPath_nil`, `balanced_zero_eq_nil`, plus the Catalan and
   `native_decide` examples. Same `ChungFeller` namespace.
2. Switched `BallotProblemOQ01OQ04OQ01.lean`'s import from
   `Proofs.BallotProblemOQ01OQ04` to `Proofs.BallotProblemOQ01OQ04Core`.
   No changes to the bijection proof itself.
3. Reduced `BallotProblemOQ01OQ04.lean` to a thin gallery face: imports the
   companion (which transitively imports Core) and proves
   `chung_feller_uniform := ChungFellerBijection.chung_feller_uniform'`.

### Why This Was Needed

The companion proved `chung_feller_uniform'` (with 0 sorries, 0 axiom uses)
in Session 5, but the parent kept its own `axiom chung_feller_uniform`
because the import direction was companion → parent. Reversing the
direction required moving the parent's definitions out of its way (into a
new Core file) so the companion could depend on Core instead, freeing the
parent to consume the companion's proof.

### Files Modified

- `proofs/Proofs/BallotProblemOQ01OQ04Core.lean` (new, 178 lines)
- `proofs/Proofs/BallotProblemOQ01OQ04OQ01.lean` (1-line import change)
- `proofs/Proofs/BallotProblemOQ01OQ04.lean` (rewrote to 73-line re-export)

### Result

- `BallotProblemOQ01OQ04.lean`: 0 sorries, 0 axioms.
- `BallotProblemOQ01OQ04OQ01.lean`: 0 sorries, 0 axiom uses (unchanged).
- `BallotProblemOQ01OQ04Core.lean`: 0 sorries, 0 axioms.
- Gallery `meta.json` updated: `status: axiomatized → verified`,
  `badge: axiom → verified`, `axiomCount: 1 → 0`.

---

## Session 2026-04-22 (Session 6) — Fix BallotProblemOQ03 pre-existing build failures

**Mode**: FRESH (continuation)
**Outcome**: completed

### What I Did

- Fixed all pre-existing build failures in `BallotProblemOQ03.lean` that were blocking the full build
- Key fixes applied:
  - `hfst_north_eq` (line 2269): nat subtraction `n₁' = n₂ + a₂ - a₁` — changed `rw [h_n₁']` to `omega` since `n₂ + (a₂ - a₁) ≠ (n₂ + a₂) - a₁` definitionally in Nat
  - `swapAtPoint_fst_take_prefix` (line 2376): `List.take_left` requires explicit list arguments
  - `swapAtPoint_snd_take_prefix` (line 2389): same `List.take_left` fix
  - `h_min_orig` (line 2452): simplified `hcp_idx.symm ▸ rfl` to just `hcp_idx.symm`
- Verified with Docker build: `BallotProblemOQ03.lean` compiles with 0 errors, 0 sorries

### Files Modified

- `proofs/Proofs/BallotProblemOQ03.lean` — 4 targeted fixes to remove all build errors

---

## Session 2026-04-22 (Session 5) — Complete the bijection proof

**Mode**: FRESH (continued from Sessions 1–4)
**Outcome**: completed

### What I Did

- Replaced the trivial `chung_feller_uniform' := chung_feller_uniform n j k hj hk` (axiom call) with a direct proof using `Set.ncard_congr` and the bijection `chung_feller_bijection_exists`
- Added `rfl` to close the n=0 case after `subst` substitutions
- The new proof constructs an explicit bijection between type-j and type-k balanced paths by "swapping the type component" of the Equiv from `chung_feller_bijection_exists`
- Successfully ran docker build to verify the proof compiles

### Key Findings

- `chung_feller_bijection_exists n hn : Function.Bijective (chungFellerMap n hn)` was already proved with 0 sorries in Session 4
- `Equiv.ofBijective _ (chung_feller_bijection_exists n hn')` gives a Type Equiv from balanced paths to Dyck paths × Fin(n+1)
- The type-swapping map `l ↦ e.symm((e ⟨l, hbal⟩).1, k)` is the key bijection between type-j and type-k sets
- `Set.ncard_congr` requires membership, injectivity, and surjectivity — all proved

### Files Modified

- `proofs/Proofs/BallotProblemOQ01OQ04OQ01.lean` (lines 1012–1099) — replaced axiom call with full proof

### Result

`chung_feller_uniform'` is now proved with:
- 0 `sorry`s
- 0 calls to `axiom chung_feller_uniform` (or any other axiom introduced in this file)
- The proof is constructive: explicit bijection via cycle lemma + Dyck path correspondence

---

## Session History (Sessions 1–4, prior to this session)

### Session 1 (established chungFellerRot properties)
Proved: head = 1, tail has nonneg prefix sums, tail upsteps all above axis, upstepsAboveAxis_of_all_nonneg, chungFellerRot_tail_type_eq_n (rotation maps to Dyck paths).

### Session 2 (completed IsDyckPath proof)
Proved: upstepsAboveAxis_le_n, chungFellerRot_tail_is_balanced, chungFellerRot_tail_is_dyck, chungFellerMap is fully well-typed.

### Session 3 (orbit structure)
Proved: cyclicRotation_compose_wrap, orbit_same_dyck (key lemma — all balanced paths in the same orbit have the same Dyck image). Also proved chung_feller_uniform' by calling the parent axiom (placeholder).

### Session 4 (bijection bijectivity)
Proved: chungFellerRot_dyck_self, cyclicRotation_get?_zero, chung_feller_bijection_exists (full bijectivity with 0 sorries).

---

## Mathematical Content

The bijection `chungFellerMap n hn` sends a balanced path `l` to:
- **Dyck image**: `(chungFellerRot l).tail` — the tail of the unique good rotation of `1::l`
- **Type component**: `upstepsAboveAxis l` — the number of upsteps at non-negative height, as `Fin(n+1)`

Key facts:
1. `chungFellerRot l` = cyclicRotation of `1::l` at the rightmost minimum position
2. By the cycle lemma, exactly 1 rotation of `1::l` has all positive prefix sums — this is the Dyck-starting rotation
3. Two balanced paths with the same Dyck image are in the same rotation orbit (`orbit_same_dyck`)
4. All n+1 balanced paths in an orbit have distinct types 0..n (`rotation_types_all_distinct`)
5. So the map `l ↦ (DyckImage(l), Type(l))` is bijective

The Chung-Feller uniformity follows: `|type-j paths| = |type-k paths|` by swapping type components via the bijection.

---

## Next Steps (for future exploration)

1. ~~Can `BallotProblemOQ01OQ04.lean`'s axiom `chung_feller_uniform` be replaced by importing `chung_feller_uniform'` from OQ04OQ01?~~ **Resolved in Session 7 (2026-04-28)** via the three-file refactor (Core / Bijection / GalleryFace).
2. q-analog: can a q-Chung-Feller theorem be formalized, tracking path area?
3. The bijection connects to RSK correspondence: does `chungFellerMap` have a nice description in terms of RSK?
