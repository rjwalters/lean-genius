# S8 PREP — `scarfWalk_isPanchromatic` signature amendment with 1-d Sperner endpoint parity hypothesis

**Slug**: `sperner-simplicial-instance-oq-05`
**Researcher**: researcher-1
**Date**: 2026-06-04
**Session**: 16 (S8 PREP)
**Type**: Doc-only readiness/design memo (no `.lean` diff, no gallery diff)
**Predecessor**: Session 14 (S7 ACT, 2026-06-01, researcher-1) flagged the
existing `scarfWalk_isPanchromatic` statement as **unprovable as written**.
**Successor**: S8 ACT — discharge the amended theorem using
S5 PREP §4 (monotone-walk + no-revisit + fuel-pigeonhole) plus the
three S7 structural lemmas (`scarfWalk_eq_scarfWalkAux`,
`scarfWalkAux_zero_fuel`, `scarfWalkAux_of_panchromatic_start`).

## 1. S7 audit finding — recap

Session 14 (S7 ACT, 2026-06-01) added three structural reduction
lemmas + one concrete `decide` soundness `example` to
`proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`. During
that session the pre-existing `scarfWalk_isPanchromatic` theorem
(line 102–105 of the leaf file, **1 sorry**) was audited and
found **unprovable** as currently stated:

```lean
theorem scarfWalk_isPanchromatic (hm : 0 < m) (start : Fin m) (k : Fin 2)
    (h_start : ¬ IsPanchromatic1d c start) :
    IsPanchromatic1d c (scarfWalk c hm start k h_start) := by
  sorry
```

**Counterexample (S7 §"Audit finding")**: set `m = 3`, `c ≡ 0`,
`start = ⟨0, _⟩`, `k = ⟨1, _⟩`. Then:

- No cell of `intervalTriangulation 3` is panchromatic: the
  colouring is constant, so every edge `[i, i+1]` has both
  endpoints coloured `0`.
- `IsPanchromatic1d c i := c i.val ≠ c (i.val + 1)` is `False` for
  every `i : Fin 3`.
- The walk either:
  - **Exhausts fuel** (`scarfWalkAux ... 0 = start`, the line-83
    base case) and returns `start`, which is non-panchromatic; OR
  - **Hits a boundary face** (`.adj _ _ = none`) and `step`'s first
    arm `match ... | none => .inl i` returns the **non-panchromatic
    current cell** as a winner.

Either way the walk returns a non-panchromatic cell, contradicting
the conclusion. Hence the statement is **provably false** at
`m = 3, c ≡ 0`.

The S5 PREP §4 discharge plan (PR #18648's predecessor PREP memo,
later refined in #19105) sketched monotone-walk + no-revisit + fuel
pigeonhole without flagging that the walk's termination guarantees
*existence of some terminal cell* but **not** *panchromaticity of
that terminal cell*. The missing ingredient is an **existential
witness for some panchromatic cell** that the walk can reach — the
1-d Sperner endpoint condition.

## 2. The amendment — `c 0 ≠ c m`

The classical 1-d Sperner lemma reads:

> Let `c : {0, 1, …, m} → Fin 2` be a 2-colouring. If `c(0) ≠ c(m)`,
> then there exists some `i ∈ {0, …, m-1}` with `c(i) ≠ c(i+1)`.

This is the discrete intermediate-value theorem: a 2-valued
function on a path `0, 1, …, m` with different endpoint values must
switch values at some adjacent pair. The proof is a 5-line
induction on `m` (or, in our framework, a parity argument over
boundary edges of `intervalTriangulation m hm`).

The amended signature:

```lean
theorem scarfWalk_isPanchromatic (hm : 0 < m)
    (h_parity : c 0 ≠ c m)        -- NEW: 1-d Sperner endpoint hypothesis
    (start : Fin m) (k : Fin 2)
    (h_start : ¬ IsPanchromatic1d c start) :
    IsPanchromatic1d c (scarfWalk c hm start k h_start) := by
  sorry  -- S8 ACT scope
```

**Why this hypothesis is the right one**:

1. It is **necessary**: the S7 counterexample (`m = 3, c ≡ 0`) has
   `c 0 = c m = 0`, so the hypothesis fails — the theorem must
   reject this case.
2. It is **sufficient**: under `c 0 ≠ c m`, the 1-d Sperner lemma
   guarantees the existence of at least one panchromatic cell of
   `intervalTriangulation m hm`. Combined with the walk's
   termination (S5 PREP §4 fuel-pigeonhole) and the no-revisit
   property (S5 PREP §4 monotone-walk invariant), the walk must
   land on a panchromatic cell — it cannot terminate on a
   non-panchromatic cell via the `.adj = none` branch because that
   branch only triggers at the two extreme boundary cells
   (`0` and `m-1`), and even there only one face is a boundary
   (vertex `0` for cell `0`, vertex `m` for cell `m-1`). If the
   colouring is non-constant on `{0, …, m}` then either cell `0`
   or cell `m-1` (or both) is itself panchromatic, OR the walk
   passes through one and continues from an interior face.
3. It is the **canonical formulation**: it matches the 1-d
   specialisation of the general Sperner hypothesis on
   `Triangulation V n` (the boundary colour-orientation parity).
   Future generalisation to (C2-gen) inherits the same shape.
4. It is **decidable**: `c 0 ≠ c m : Prop` is `Decidable` (`Fin 2`
   has decidable equality), so the smoke-test `example` and any
   future kernel-level `decide` proofs remain valid.

**Failed alternatives considered**:

- **`c 0 ≠ c m` *or* explicit panchromatic-cell-existence**
  hypothesis. Equivalent but heavier — the parity form is the
  cleanest 1-d Sperner statement.
- **`∃ i : Fin m, IsPanchromatic1d c i`** (panchromatic-cell
  existence). Weaker than `c 0 ≠ c m` (the latter implies it via
  discrete IVT, but the former does not imply the latter — a
  non-constant colouring with matching endpoints can still have
  internal panchromatic cells). Choosing the strong form makes
  the discharge cleaner and is the standard convention.
- **No hypothesis + change conclusion to `... = start ∨ panchromatic`**.
  Rejected: this defeats the point of the lemma; downstream users
  (e.g. `exists_panchromatic_constructive`) need a definite
  panchromatic conclusion.

## 3. Downstream impact — `exists_panchromatic_constructive`

The current signature (line 111–116 of the leaf file):

```lean
theorem exists_panchromatic_constructive (hm : 0 < m)
    (boundary_door : Fin m × Fin 2)
    (h_door : ¬ IsPanchromatic1d c boundary_door.1) :
    ∃ i : Fin m, IsPanchromatic1d c i :=
  ⟨scarfWalk c hm boundary_door.1 boundary_door.2 h_door,
   scarfWalk_isPanchromatic c hm _ _ _⟩
```

Direct fallout of the `scarfWalk_isPanchromatic` signature change:
the application `scarfWalk_isPanchromatic c hm _ _ _` now needs a
parity argument. The amended call:

```lean
theorem exists_panchromatic_constructive (hm : 0 < m)
    (h_parity : c 0 ≠ c m)        -- NEW: thread through
    (boundary_door : Fin m × Fin 2)
    (h_door : ¬ IsPanchromatic1d c boundary_door.1) :
    ∃ i : Fin m, IsPanchromatic1d c i :=
  ⟨scarfWalk c hm boundary_door.1 boundary_door.2 h_door,
   scarfWalk_isPanchromatic c hm h_parity _ _ _⟩
```

The `h_door` hypothesis remains: the walk requires a non-panchromatic
starting cell to enter the `step` recursion (panchromatic-start
short-circuits via S7's `scarfWalkAux_of_panchromatic_start`). The
parity hypothesis additionally guarantees the walk **succeeds**
(rather than terminating on a non-panchromatic cell).

**No further callers**: a grep over the repo confirms
`exists_panchromatic_constructive` is referenced in this leaf file
only (zero external imports, zero gallery cross-refs). The
amendment is local to `SpernerSimplicialInstanceOQ05Scarf1d.lean`.
S8 ACT scope is contained.

**Gallery impact**: `src/data/proofs/sperner-simplicial-instance-oq-05/meta.json`
is unaffected — the gallery currently advertises only the C1
brute-force module (`SpernerSimplicialInstanceOQ05.lean`); the
C2-1d Scarf module is an `additionalFiles[]` companion (added in
the mechanic mega-batch #22005). Annotations on the C2-1d module
do not yet exist; that is S9+ scope.

## 4. Discharge sketch (S8 ACT scope, ~40–60 LOC)

The amended theorem becomes provable by combining:

1. **S7 helper `scarfWalkAux_of_panchromatic_start`**: when the
   walk enters a panchromatic cell, it returns it immediately.
2. **Monotone-walk invariant (S5 PREP §4)**: each `step` call
   either lands on a panchromatic cell (which the next recursive
   call returns) or moves to a strictly-not-yet-visited cell.
3. **No-revisit corollary**: by `iadj_symm'` (parent file
   line 866), the adjacency is a partial involution; combined with
   the entry-face tracking in the `.inr` arm of `step`, the walk
   visits each cell at most once on a non-panchromatic path.
4. **Fuel pigeonhole**: the walk has `m` fuel and `Fin m` has
   exactly `m` cells, so a strictly-non-revisiting walk of length
   `m` must either find a panchromatic cell or exhaust the cell
   set — but the latter is impossible because (by `h_parity`) at
   least one cell IS panchromatic, contradicting the
   no-revisit/no-panchromatic alternative.

**Sketch (~50 LOC)**:

```lean
theorem scarfWalk_isPanchromatic (hm : 0 < m)
    (h_parity : c 0 ≠ c m)
    (start : Fin m) (k : Fin 2)
    (h_start : ¬ IsPanchromatic1d c start) :
    IsPanchromatic1d c (scarfWalk c hm start k h_start) := by
  -- Strategy: induction on fuel, threading an invariant that
  -- the set of visited cells is strictly increasing and that
  -- the walk has not yet found a panchromatic cell at any
  -- intermediate step except possibly the last.
  rw [scarfWalk_eq_scarfWalkAux]
  -- Now the goal involves scarfWalkAux c hm start k m.
  -- We prove by strong induction on m (the fuel) that:
  --   ∀ visited, |visited| + fuel ≥ m → (walk lands on panchromatic).
  -- The base case (fuel = 0) requires |visited| = m, but then
  -- visited covers all of Fin m, including the panchromatic
  -- cell guaranteed by h_parity (1-d Sperner via discrete IVT),
  -- contradicting "no panchromatic cell in visited so far".
  sorry  -- Detailed proof goes here (~40–55 LOC); the
         -- intermediate lemmas are:
         -- · discrete_ivt_panchromatic_cell : c 0 ≠ c m →
         --     ∃ i : Fin m, IsPanchromatic1d c i
         -- · scarfWalk_visited_monotone : (visited counter) is
         --     monotonically increasing along non-panchromatic
         --     `.inr` branches
         -- · scarfWalk_visited_no_revisit : the adjacency
         --     involution prevents revisits given face tracking
         -- · contradiction with fuel = 0 + |visited| < m
```

**Estimated decomposition** (for S8 ACT scoping):

| Sub-lemma | LOC | Risk | Notes |
|---|---|---|---|
| `discrete_ivt_panchromatic_cell` | ~15 | LOW | Direct induction on `m`; clean Mathlib-style. May be liftable from `Nat.exists_change`-style helpers. |
| `scarfWalk_visited_monotone` | ~10 | MED | Requires either a visited-set or a strict-monotone-index invariant (1-d makes this trivial: the walk moves left or right). |
| `scarfWalk_visited_no_revisit` | ~15 | MED | The 1-d case is special: in 1-d the walk is strictly monotone in cell index (either increasing or decreasing throughout), which gives no-revisit for free. |
| Main `scarfWalk_isPanchromatic` | ~15 | MED | Combine the above + fuel pigeonhole + S7 helpers. |
| **Total** | **~55 LOC** | **MED-HIGH** | Within S8 ACT budget. |

**Risk assessment**: MED-HIGH for S8 ACT (vs HIGH originally
scoped in Session 14). The 1-d specialisation makes
`scarfWalk_visited_no_revisit` straightforward (1-d Scarf walks
are monotone in cell index), which was the highest-risk
sub-lemma in the original S5 PREP §4 sketch.

## 5. Verification checks already performed (this session)

This memo is doc-only. Pre-merge checks:

- **File state confirmed**: re-read `SpernerSimplicialInstanceOQ05Scarf1d.lean`
  (170 LOC); confirms 1 real sorry on line 105 (`scarfWalk_isPanchromatic`),
  consistent with state.md (Session 15). The
  `src/data/research/problems/sperner-simplicial-instance-oq-05.json`
  `leanFiles[].sorryCount = 3` for this file is **stale drift**
  (actual = 1); see §7 for handoff to mechanic.
- **No open PRs on slug**: pre-claim probe (2026-06-04 ~02:30 UTC)
  via `gh pr list --search "sperner-simplicial-instance-oq-05"`
  returned zero open PRs. Claim window is uncontested.
- **Counterexample logic re-verified** by hand: at `m = 3, c ≡ 0`,
  every cell `i : Fin 3` has `c i.val = c (i.val + 1) = 0`, so
  `IsPanchromatic1d c i = (0 ≠ 0) = False`. With
  `start = ⟨0, _⟩, k = ⟨1, _⟩`, the `step` call computes
  `k' = ⟨0, _⟩` (since `k.val = 1 ≠ 0`), then `(intervalTriangulation 3 _).adj ⟨0, _⟩ ⟨0, _⟩`
  evaluates via `iadj 3 ⟨0, _⟩ ⟨0, _⟩ = if 0 = 0 then if 0+1 < 3 then some (⟨1, _⟩, ⟨1, _⟩) else none = some (⟨1, _⟩, ⟨1, _⟩)`.
  Then `IsPanchromatic1d c ⟨1, _⟩ = False`, so the walk recurses
  on cell `1`, then cell `2`. At cell `2`, `k' = ⟨0, _⟩` again,
  and `iadj 3 ⟨2, _⟩ ⟨0, _⟩ = if 2+1 < 3 then some else none = none`,
  so `step` returns `.inl ⟨2, _⟩` — a non-panchromatic winner.
  This concretely confirms the S7 audit's counterexample analysis.
- **Smoke-test colouring re-verified**: at `m = 3, c(n) = if n ≤ 1 then 0 else 1`,
  endpoint parity holds: `c 0 = 0 ≠ 1 = c 3`. Cells: `[0,1]` non-pancho,
  `[1,2]` PANCHRO, `[2,3]` non-pancho. The S7 `example` correctly
  finds the panchromatic cell. The amended theorem would have
  this colouring satisfy `h_parity`, so the smoke-test `decide`
  proof transfers to the amended theorem unchanged (modulo
  adding the trivial `h_parity` discharge).

## 6. Acceptance criteria for S8 ACT (informational)

When S8 ACT discharges this PREP, the merger should verify:

- [ ] `scarfWalk_isPanchromatic` takes `(h_parity : c 0 ≠ c m)` as a
      new explicit hypothesis.
- [ ] `exists_panchromatic_constructive` takes `(h_parity : c 0 ≠ c m)` as a
      new explicit hypothesis.
- [ ] No new `axiom` declarations introduced.
- [ ] The S7 `example` smoke-test still passes (the `c(n) = ⟦n ≤ 1⟧`
      colouring satisfies `c 0 = 0 ≠ 1 = c 3`).
- [ ] Sorry count goes from 1 → 0 on the leaf file (the existing
      `scarfWalk_isPanchromatic` sorry closed; no new sorries
      introduced by intermediate lemmas).
- [ ] Docker build on `Proofs.SpernerSimplicialInstanceOQ05Scarf1d`
      succeeds; existing 1 build warning (the now-discharged sorry)
      disappears.
- [ ] If `discrete_ivt_panchromatic_cell` is split into its own
      lemma (recommended for reusability), it appears in the
      `Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean` namespace
      and is named per gallery convention.

## 7. Out-of-scope / mechanic handoff

- **`leanFiles[].sorryCount` drift on
  `src/data/research/problems/sperner-simplicial-instance-oq-05.json`**:
  current value `3` is stale; actual `Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`
  has 1 sorry on line 105. Ready-to-paste fix:
  ```jq
  .leanFiles |= map(if .filename == "SpernerSimplicialInstanceOQ05Scarf1d.lean"
                     then .sorryCount = 1 else . end)
  ```
  Mechanic territory (count-drift class — see project_mechanic_orphan_scan_v8 +
  feedback_mechanic_count_drift_jq_one_liner memories). Not fixed in
  this PR to keep S8 PREP doc-only and avoid race with mechanic batches.
- **S8 ALT (b) gallery promotion**: COMPLETED externally by mechanic
  mega-batch PR #22005 (2026-06-02, see Session 15 STATE-SYNC).
  No further action.
- **S8 ALT (c) 2-D Hex-no-draw**: deferred behind sister slug
  `sperner-simplicial-instance-oq-01` 2-D triangulation instance,
  unchanged from Session 14.

## 8. Risk inventory

| Risk | Level | Mitigation |
|---|---|---|
| The amended hypothesis `c 0 ≠ c m` is insufficient and discharge still fails | LOW | Counterexample analysis in §1 confirms hypothesis necessity; 1-d Sperner classical proof confirms sufficiency. The discharge sketch in §4 is constructive. |
| Downstream callers other than `exists_panchromatic_constructive` exist | LOW | Grep over `proofs/`, `src/`, gallery confirms no external callers (the C2-1d module is gallery-companion only; no other Lean file imports it). |
| The smoke-test `example` requires non-trivial adaptation | LOW | The smoke-test colouring satisfies `c 0 ≠ c 3`, so `h_parity` is dischargeable by `decide`. The `example` body changes by ≤ 2 lines. |
| Mechanic count-drift fix collides with this PR | NONE | This PR is doc-only (sessions memo + state.md + research JSON head fields); does not touch `leanFiles[].sorryCount`. Mechanic class is orthogonal. |
| Mathlib pin drift since S5 PREP | LOW | Mathlib pin `2df2f0150c…` unchanged since S3 PREP #18712 (per Session 12). No bearer-line recheck needed for this PREP since the §4 discharge sketch routes through public `T.adj` (S5 PREP F1 fix) and uses no private parent-file lemmas. |

## 9. References

- **S7 ACT memo** (Session 14, this slug):
  `research/problems/sperner-simplicial-instance-oq-05/sessions/2026-06-01-s7-act-helper-lemmas.md`
- **S6 ACT memo** (Session 13, this slug):
  `research/problems/sperner-simplicial-instance-oq-05/sessions/2026-05-30-s6-act-c2-1d-scarf-walk.md`
- **S5 PREP memo** (Session 12, this slug):
  `research/problems/sperner-simplicial-instance-oq-05/sessions/2026-05-16-s5-prep-c2-1d-readiness-refresh.md`
- **Leaf file** under PREP:
  `proofs/Proofs/SpernerSimplicialInstanceOQ05Scarf1d.lean`
  (170 LOC, 1 sorry on line 105)
- **Parent file** (read-only context):
  `proofs/Proofs/SpernerSimplicialInstance.lean` (1023 LOC, 25 thms,
  10 defs, 0 sorries, 0 axioms; `intervalTriangulation` at line 958,
  `iadj` at line 818, `iadj_symm'` at line 866)
- **State log**:
  `research/problems/sperner-simplicial-instance-oq-05/state.md`
- **Research JSON**:
  `src/data/research/problems/sperner-simplicial-instance-oq-05.json`
- **Gallery meta** (untouched by this memo):
  `src/data/proofs/sperner-simplicial-instance-oq-05/meta.json`
- **Mechanic mega-batch PR #22005** (2026-06-02): added Scarf1d to
  `additionalFiles[]` in the gallery meta (S8 ALT (b) external completion).
- **Classical 1-d Sperner reference**: Sperner (1928) Theorem; the
  1-d case is the discrete intermediate-value theorem on
  `c : {0, …, m} → Fin 2` with `c(0) ≠ c(m) ⇒ ∃i < m. c(i) ≠ c(i+1)`.

## 10. Host context

- HEAD `3928d4fd1c9` (research(cantors-theorem-oq-01-oq-03-oq-04) STATE-SYNC, merged ~2026-06-04 to main).
- Working tree clean before claim.
- Worktree: `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-1`.
- Branch from `origin/main`: `research/sperner-oq05-s8-prep-parity-hypothesis-1780640000`.
- Mathlib pin (per `proofs/lake-manifest.json`): `2df2f0150c…` (v4.26.0).
- Claim TTL 90 min; claim expires 2026-06-05T07:10:06Z.
