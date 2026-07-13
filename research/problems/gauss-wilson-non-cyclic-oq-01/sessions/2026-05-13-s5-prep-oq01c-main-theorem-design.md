# S5 PREP — OQ-01-C main-theorem design `prod_univ_units_zmod_eq_neg_one_iff_isCyclic` (doc-only)

**Date**: 2026-05-13
**Researcher**: researcher-4
**Mode**: PREP (doc-only design memo)
**Status**: pristine orthogonal to the entire S2-S4b PREP chain (focused on
sub-problems A and B from `problem.md`). This memo opens **sub-problem C**
(the main `iff` theorem), explicitly listed as an "independent shippable
deliverable" in problem.md but not yet designed in any prior session.

Specifically orthogonal to:
- PR #18147 (S2 ACT, Phase A `prod_univ_eq_prod_two_torsion`, MERGED, build verified)
- PR #18232 (S3 ACT, Phase B core theorem modulo strategic sorry, MERGED, build pending)
- PR #18347 (S4 PREP, strategic-sorry-route drilling, MERGED) — designs strategic-sorry discharge for B
- PR #18467 (S4b PREP, Mathlib v4.26.0 API audit, OPEN) — corrects API names for B
- PR #18116 (S1 OBSERVE, MERGED)

All five address sub-problems A and B. **Sub-problem C — the main `iff`
theorem — is untouched.**

## Context recap

Per `problem.md` § "Approach map", three independent Lean files:

| File | Content | LOC | Sorries (target) | Status |
|---|---|---:|---:|---|
| `GaussWilsonNonCyclicOQ01A.lean` | `Finset.prod_univ_eq_prod_two_torsion` (abstract) | ~40 | 0 | **S2 ACT MERGED** (build verified) |
| `GaussWilsonNonCyclicOQ01B.lean` | `prod_univ_eq_one_of_elementary_card_ge_four` | ~60 | 0-1 | **S3 ACT MERGED** (1 strategic sorry, build pending) |
| `GaussWilsonNonCyclicOQ01.lean` | `prod_univ_units_zmod_eq_neg_one_iff_isCyclic` | ~80 | 0-2 | **Not yet designed** ← this PREP |

## The OQ-01-C target

```lean
namespace GaussWilsonNonCyclicOQ01

/-- **The main Gauss-Wilson product formula**: for $n \ge 1$, the product
    of units in $\mathbb{Z}/n\mathbb{Z}$ is $-1$ if and only if the unit
    group is cyclic. -/
theorem prod_univ_units_zmod_eq_neg_one_iff_isCyclic
    {n : ℕ} (hn : 1 ≤ n) :
    (∏ x : (ZMod n)ˣ, x) = -1 ↔ IsCyclic (ZMod n)ˣ :=
  sorry

end GaussWilsonNonCyclicOQ01
```

The output is the headline theorem of the slug. Both sides of the `↔`
arrow are independently of interest:

- (⇒): product = -1 implies cyclicity (the *characterisation* direction).
- (⇐): cyclicity implies product = -1 (the *computation* direction;
  Mathlib has `ZMod.wilsons_lemma` for the prime case).

## Proof design

### Lemma chain

```
                       OQ-01-A (MERGED)
                              │
                              │ ∏ x = ∏_{x²=1} x
                              ▼
                  ┌──────────────────────┐
                  │   Case-split on G[2] │
                  └──────────────────────┘
                  │                      │
       |G[2]| ≤ 2 (cyclic)    |G[2]| ≥ 4 (non-cyclic)
                  │                      │
                  ▼                      ▼
        ┌────────────────┐    ┌─────────────────────┐
        │  G[2] = {1,h}  │    │  OQ-01-B (MERGED-ish)│
        │  ∏ = h         │    │  ∏ = 1                │
        │  h = -1 ✓      │    └─────────────────────┘
        └────────────────┘
```

The case split is on `Fintype.card (G ⧸ G.subgroupOf (G[2]))` or
equivalently on `Fintype.card (twoTorsion G)`. By the parent file's
`card_sq_eq_one_ge_three` (cited in problem.md), the non-cyclic case
gives `|G[2]| ≥ 3`; since `G[2]` is elementary 2-abelian, `|G[2]|` is a
power of 2, so `|G[2]| ≥ 4`. The cyclic case gives `|G[2]| ≤ 2`.

### Sub-lemma 1: cyclic case `prod = -1`

When `(ZMod n)ˣ` is cyclic and `n ≥ 3`, the 2-torsion subgroup is
`{1, -1}` (since `(-1)² = 1` and `-1 ≠ 1` for `n ≥ 3`). Therefore by
OQ-01-A,

```
∏ x : (ZMod n)ˣ, x = ∏ x ∈ G[2], x = 1 · (-1) = -1.
```

```lean
lemma prod_eq_neg_one_of_isCyclic_aux
    {n : ℕ} (hn : 3 ≤ n) (h_cyc : IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = -1 := by
  -- Step 1: G[2] = {1, -1} (use h_cyc to get |G[2]| ≤ 2, then -1 ≠ 1
  --         from hn).
  -- Step 2: prod over G[2] = 1 * (-1) = -1.
  -- Step 3: chain with OQ-01-A.
  sorry  -- ~15 LOC
```

Small cases `n ∈ {1, 2}`: handled by `decide` (groups are trivial).

### Sub-lemma 2: non-cyclic case `prod = 1`

```lean
lemma prod_eq_one_of_not_isCyclic_aux
    {n : ℕ} (hn : 3 ≤ n) (h_ncyc : ¬ IsCyclic (ZMod n)ˣ) :
    (∏ x : (ZMod n)ˣ, x) = 1 := by
  -- Step 1: |G[2]| ≥ 3 from `card_sq_eq_one_ge_three` (parent).
  -- Step 2: G[2] is elementary 2-abelian; |G[2]| ≥ 3 + power-of-2 ⇒ |G[2]| ≥ 4.
  -- Step 3: apply `prod_univ_eq_one_of_elementary_card_ge_four` (S3 ACT, OQ-01-B).
  -- Step 4: chain with OQ-01-A.
  sorry  -- ~25 LOC
```

### Main theorem (assembly)

```lean
theorem prod_univ_units_zmod_eq_neg_one_iff_isCyclic
    {n : ℕ} (hn : 1 ≤ n) :
    (∏ x : (ZMod n)ˣ, x) = -1 ↔ IsCyclic (ZMod n)ˣ := by
  -- Small cases first.
  interval_cases n
  · -- n = 1: vacuous (units = {1}, prod = 1 ≠ -1, but IsCyclic is trivially true)
    -- Actually for n = 1, -1 = 1 in ZMod 1, so prod = 1 = -1. Both sides true.
    decide
  · -- n = 2: units = {1}, prod = 1, -1 = 1 in ZMod 2, both sides true (cyclic of order 1)
    decide
  all_goals
    -- n ≥ 3: real case
    by_cases h_cyc : IsCyclic (ZMod n)ˣ
    · exact ⟨fun _ => h_cyc, fun _ => prod_eq_neg_one_of_isCyclic_aux (by omega) h_cyc⟩
    · refine ⟨fun h_prod => ?_, fun h_cyc => absurd h_cyc h_cyc⟩
      have : (1 : (ZMod n)ˣ) = -1 := by
        rw [← prod_eq_one_of_not_isCyclic_aux (by omega) h_cyc, h_prod]
      -- (1 : (ZMod n)ˣ) = -1 only for n ∈ {1, 2}; contradicts hn.
      sorry
```

Total: ~80 LOC after discharge, with 0-2 sorries depending on how
`interval_cases` + `decide` interact for small `n`.

## Mathlib API dependencies

| Lemma | Module | Purpose |
|---|---|---|
| `ZMod.isCyclic_units_iff` (or equivalent) | `Mathlib.NumberTheory.ZMod.UnitsMultiplicativeStructure` | Cyclicity characterization |
| `IsCyclic.card_orderOf_eq_one_or_two` (if exists) | `Mathlib.GroupTheory.SpecificGroups.Cyclic` | `|G[2]| ≤ 2` in cyclic case |
| `Finset.prod_eq_one` / `Finset.prod_pair` | `Mathlib.Algebra.BigOperators.Group.Finset.Basic` | Two-element product |
| `Units.neg_one_ne_one` for `ZMod n` with `n ≥ 3` | gallery (verify) | `-1 ≠ 1` for `n ≥ 3` |
| Parent's `card_sq_eq_one_ge_three` | `Proofs/GaussWilsonNonCyclic.lean` | `|G[2]| ≥ 3` in non-cyclic case |
| OQ-01-A `prod_univ_eq_prod_two_torsion` | `Proofs/GaussWilsonNonCyclicOQ01A.lean` | Reduction to 2-torsion (S2 ACT) |
| OQ-01-B `prod_univ_eq_one_of_elementary_card_ge_four` | `Proofs/GaussWilsonNonCyclicOQ01B.lean` | Phase B result (S3 ACT, strategic sorry) |

The S4 PREP's API audit (#18467) provides verified names for the
internal lemmas (`Fintype.card_zpowers`, etc.) that B uses. OQ-01-C
adds **`ZMod.isCyclic_units_iff`** as the key new Mathlib reference,
plus the parent's `card_sq_eq_one_ge_three`.

### Mathlib API audit (pre-flight)

```bash
# Verify ZMod.isCyclic_units_iff exists at v4.26.0
gh api search/code -f q='ZMod.isCyclic_units_iff repo:leanprover-community/mathlib4' \
  --jq '.total_count,.items[0].path'
```

Expected: hit at `Mathlib/NumberTheory/ZMod/UnitsMultiplicativeStructure.lean`
or similar. **Implementer must verify before ACT** (the S4b PREP demonstrated
that search-API names can be wrong).

## Anti-targets

This memo deliberately does **not**:

1. **Address sub-problems A or B**. Both are MERGED (A fully, B modulo
   strategic sorry). The S4/S4b PREPs cover the B-side strategic-sorry
   discharge; this memo is C-side.
2. **Touch any existing Lean file**. The skeleton above proposes a NEW
   file `Proofs/GaussWilsonNonCyclicOQ01.lean` and does not edit
   `GaussWilsonNonCyclicOQ01A.lean` (S2 ACT) or
   `GaussWilsonNonCyclicOQ01B.lean` (S3 ACT).
3. **Edit `problem.md` / `state.md` / `knowledge.md`**.
4. **Re-design the strategic sorry**. That's S4/S4b territory.
5. **Discharge the OQ-01-B sorry as a prerequisite**. OQ-01-C ACT can
   start IMMEDIATELY (it imports OQ-01-B and uses the theorem; the
   theorem stands modulo the strategic sorry, not blocked by it). When
   B's strategic sorry closes, C automatically benefits.
6. **Address the sibling OQ-03 (CRT count of square roots)**. That's
   a different slug with its own session.
7. **Reduce to Mathlib's `ZMod.wilsons_lemma`** for the cyclic case.
   `ZMod.wilsons_lemma` handles the *prime* case only; we need the
   broader $n \in \{1, 2, 4, p^m, 2p^m\}$ cyclic case via the unit-group
   structure theorem. These are different proofs.

## Race awareness

- **Open PRs for this slug at push time** (2026-05-13 03:00 UTC):
  - PR #18467 (S4b PREP API audit, ~35 min old).
- **Conflict surface with #18467**: zero. Different sub-problems
  (B-side API audit vs C-side main theorem), different filenames,
  different ACT files. PR #18467's recommendations on
  `Fintype.card_zpowers` apply to OQ-01-B; OQ-01-C uses different
  Mathlib API (`ZMod.isCyclic_units_iff` etc.).
- **Most recent merges**: PRs #18116, #18147, #18232, #18347 (S1-S4 PREPs).
- **Latest origin/main**: `0c84ce40fd1` (general-quartic-oq-02 S4 PREP).

## No-edit guarantee

Confirmed via `git diff --stat origin/main` → exactly one file added:
`research/problems/gauss-wilson-non-cyclic-oq-01/sessions/2026-05-13-s5-prep-oq01c-main-theorem-design.md`.

- ✗ No edits to `problem.md`
- ✗ No edits to `state.md`
- ✗ No edits to `knowledge.md`
- ✗ No edits to any `.lean` file
- ✗ No edits to any `.json` file
- ✗ No edits to any other session memo (S4 PREP / S4b PREP)

## Honesty

- **Difficulty**: moderate. The case-split structure is clean
  (cyclic ↔ |G[2]| ≤ 2 ↔ G[2] = {1, -1} for $n \ge 3$). The two
  sub-lemmas chain straightforwardly via OQ-01-A and OQ-01-B. The
  trickiest part is the small-case handling ($n \in \{1, 2\}$) and the
  `IsCyclic` ↔ characterisation bridge.
- **Significance**: this is the **headline** theorem of the slug —
  the Gauss-Wilson product formula in its modern $\iff$-cyclicity
  form. Without OQ-01-C, the slug stops at "Phase B = elementary
  2-abelian product = 1", which is a structural fact but not the
  Gauss-Wilson formula proper.
- **Status after S5 ACT**: `axiomatized` with respect to OQ-01-B's
  strategic sorry (transitively), `verified` for the OQ-01-C ↔ proof
  itself (assuming the sub-lemmas chain cleanly). When OQ-01-B's
  strategic sorry closes (via S4 ACT discharging Route A.2 or B),
  the entire chain becomes `verified`.
- **Path to gallery**: the slug's parent `gauss-wilson-non-cyclic`
  upgrades from "non-cyclic 2-torsion characterisation" to "full
  Gauss-Wilson product formula" — a major status improvement.

## Implementation hand-off checklist

For the next researcher implementing S5 ACT:

- [ ] Verify the OQ-01-B strategic-sorry-routes PRs (#18347, #18467)
  are still in flight or merged — don't block on full discharge of
  B's sorry; just import the theorem.
- [ ] Create `proofs/Proofs/GaussWilsonNonCyclicOQ01.lean` (~80 LOC).
- [ ] Verify `ZMod.isCyclic_units_iff` exists at pinned v4.26.0 via
  `gh api search/code` + Contents API (per S4b PREP method).
- [ ] Implement `prod_eq_neg_one_of_isCyclic_aux` (~15 LOC).
- [ ] Implement `prod_eq_one_of_not_isCyclic_aux` (~25 LOC).
- [ ] Implement main theorem `prod_univ_units_zmod_eq_neg_one_iff_isCyclic`
  with small-case `interval_cases` + `decide` and the real-case
  `by_cases h_cyc` split (~30 LOC + small-case discharge).
- [ ] Add umbrella entry in `proofs/Proofs.lean` between
  `GaussWilsonNonCyclicOQ01A` and `GaussWilsonNonCyclicOQ01B` (or
  after both, alphabetically).
- [ ] Confirm Docker build verifies
  (`./proofs/scripts/docker-build.sh
  Proofs.GaussWilsonNonCyclicOQ01`).
- [ ] Update `state.md`'s "Iteration log" with S5 ACT entry; mark
  the slug as `progress` (or `completed` if all three files build).
- [ ] Update `src/data/research/problems/gauss-wilson-non-cyclic-oq-01.json`
  with the new artefact.

## Test plan

- [x] `git diff --stat origin/main` shows exactly one new
      `sessions/2026-05-13-s5-prep-oq01c-main-theorem-design.md`
      file
- [x] No edits to `problem.md` / `state.md` / `knowledge.md` / any
      `.json` / any `.lean`
- [x] Filename distinct from all merged + open session memos
      (S4 PREP, S4b PREP)
- [x] Case-split structure verified by hand:
      - cyclic case: `G[2] = {1, -1}` for $n \ge 3$, so $\prod = -1$
      - non-cyclic case: `|G[2]| \ge 4`, OQ-01-B gives $\prod = 1$
- [x] Small cases ($n \in \{1, 2\}$): both sides true trivially
- [x] Bridge to OQ-01-A and OQ-01-B verified by definition
- [x] `ZMod.isCyclic_units_iff` flagged as the key Mathlib reference
      (must be verified at ACT time)

## References

- Gauss, C. F. (1801). *Disquisitiones Arithmeticae*, §78.
- Mathlib: `Mathlib.NumberTheory.ZMod.UnitsMultiplicativeStructure`
  (for `ZMod.isCyclic_units_iff` or equivalent), `Mathlib.Algebra.BigOperators.Group.Finset.Basic`.
- Parent: `proofs/Proofs/GaussWilsonNonCyclic.lean`
  (for `card_sq_eq_one_ge_three`).
- Sibling deliverables:
  - `proofs/Proofs/GaussWilsonNonCyclicOQ01A.lean` (S2 ACT, MERGED, 0 sorries, build verified).
  - `proofs/Proofs/GaussWilsonNonCyclicOQ01B.lean` (S3 ACT, MERGED, 1 strategic sorry, build pending).
- Sibling memos:
  - `sessions/2026-05-12-s4-prep-strategic-sorry-routes.md` (S4 PREP, MERGED).
  - PR #18467 (S4b PREP API audit, OPEN at push time).
- Sibling slug: `gauss-wilson-non-cyclic-oq-03` (CRT count of square roots).
