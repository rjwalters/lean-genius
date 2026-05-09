# S20 Spec — `walkEdges'_hcov_list_of_nodup`

**Status**: Analysis-only specification. Lean implementation deferred
to a follow-up `S20-implement` session.

**Date**: 2026-05-09 (researcher-3, parallel to S17 #17596 and S18 #17623).

## Goal

Discharge the **uniqueness half** of the `hcov_list` hypothesis required
by S15's `circuit_edge_balance_list'` template, automatically for the
`walkEdges'`-style `L`. After S20-implement, the only outstanding obligation in
the eventual in-place refactor's call to `circuit_edge_balance_list'`
is the standard `walk.length = n + 1` and `walk[0]? = walk[n]?`
hypotheses (both trivially derivable from any `DirectedCircuit`).

## Statement

```lean
lemma walkEdges'_hcov_list_of_nodup (walk : List V) (n : ℕ)
    (hlen : walk.length = n + 1)
    (hnodup : (walkEdges' walk).Nodup) :
    ∀ e ∈ walkEdges' walk, ∃! i : ℕ, i < n ∧
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2
```

This is the **`hcov_list` hypothesis** of `circuit_edge_balance_list'`
(see Recipe §S15) — a `walk[i]?`-keyed unique-position witness for
each edge. S17's `walkEdges'_hsteps_list` already supplies the
companion `hsteps_list` hypothesis (existence half, no `Nodup`
required). S20-implement closes the uniqueness gap, giving the **packaged
`hcov_list`** for `walkEdges'`-style `L`.

## Why `Nodup` is necessary

The `∃!` (unique-existence) statement requires a distinctness
hypothesis on the walk's edges. Without `Nodup`, a walk that revisits
an edge has multiple `i`'s producing the same `(walk[i], walk[i+1])`
pair, so the predicate `walk[i]? = some e.1 ∧ walk[i+1]? = some e.2`
holds at multiple positions — uniqueness fails.

For `DirectedCircuit` (the closed-walk case in `remove_circuit_balanced`),
a sufficient distinctness hypothesis is `Nodup` on the **edge** list
`walkEdges' walk` itself. The vertex list `walk` may revisit vertices
(closed circuits start and end at the same vertex), but a directed
*Eulerian* circuit traverses each edge exactly once — equivalent to
`(walkEdges' walk).Nodup`.

## Proof structure

The proof needs a **structural fact** about `walkEdges'` that connects
walk-indices `i ∈ range n` to list-positions in `walkEdges' walk`:

```
For walk.length = n + 1 and i < n:
  (walkEdges' walk)[i]'_ = (walk[i]'_, walk[i+1]'_)
```

This structural fact then combines with Mathlib's
`List.Nodup.getElem_inj_iff` (in `Mathlib/Data/List/Nodup.lean`):

```lean
theorem List.Nodup.getElem_inj_iff {l : List α} (h : Nodup l)
    {i j : ℕ} {hi : i < l.length} {hj : j < l.length} :
    l[i] = l[j] ↔ i = j
```

to discharge uniqueness: from `(walk[j], walk[j+1]) = e = (walk[i₀], walk[i₀+1])`
applied at the corresponding list-positions, `Nodup` forces
`i₀ = j` (provided both indices are `< n`).

### Required structural sub-lemmas (S20a–S20c)

The structural fact decomposes into three Recipe-level lemmas:

#### S20a. `walkEdges'_eq_map_of_pos`

Convert the `filterMap` definition to an explicit `map` over
`range (walk.length - 1)`. Requires a `walk[0]'h0` default for the
out-of-bounds case to thread `g : ℕ → V × V` through Mathlib's
`List.filterMap_eq_map_iff_forall_eq_some`:

```lean
lemma walkEdges'_eq_map_of_pos (walk : List V) (h0 : 0 < walk.length) :
    walkEdges' walk = (List.range (walk.length - 1)).map (fun i =>
      (walk[i]?.getD (walk[0]'h0), walk[i+1]?.getD (walk[0]'h0))) := by
  unfold walkEdges'
  apply (List.filterMap_eq_map_iff_forall_eq_some).mpr
  intro i hi
  simp only [List.mem_range] at hi
  have h_i1_lt : i + 1 < walk.length := by omega
  have h_i_lt : i < walk.length := by omega
  rw [dif_pos h_i1_lt]
  congr 1
  · simp [List.getElem?_eq_getElem h_i_lt]
  · simp [List.getElem?_eq_getElem h_i1_lt]
```

**Mathlib API used**: `List.filterMap_eq_map_iff_forall_eq_some`
(verified at the v4.26 pin in
`Mathlib/Data/List/Basic.lean:2142`),
`List.mem_range`, `List.getElem?_eq_getElem`, `dif_pos`.

**Build risk**: low. The `congr 1` + `simp` closure may need a
`Prod.mk.injEq` rewrite or explicit `ext`-on-Prod step depending on
Mathlib's current `simp`-set behaviour around `getD ∘ getElem?`.

#### S20b. `walkEdges'_length_of_pos`

Direct corollary of S20a + `List.length_map` + `List.length_range`:

```lean
lemma walkEdges'_length_of_pos (walk : List V) (h0 : 0 < walk.length) :
    (walkEdges' walk).length = walk.length - 1 := by
  rw [walkEdges'_eq_map_of_pos walk h0, List.length_map, List.length_range]
```

#### S20c. `walkEdges'_getElem_of_pos`

The structural fact itself, derived from S20a via `List.getElem_map` and
`List.getElem_range`:

```lean
lemma walkEdges'_getElem_of_pos (walk : List V) (h0 : 0 < walk.length)
    (i : ℕ) (hi : i + 1 < walk.length) :
    (walkEdges' walk)[i]'(by
      rw [walkEdges'_length_of_pos walk h0]; omega) =
      (walk[i]'(by omega), walk[i + 1]'hi) := by
  rw [walkEdges'_eq_map_of_pos walk h0]
  -- Now: ((range (walk.length - 1)).map _)[i] = ...
  rw [List.getElem_map, List.getElem_range]
  -- Goal: (walk[i]?.getD _, walk[i+1]?.getD _) = (walk[i]'_, walk[i+1]'_)
  have h_i_lt : i < walk.length := by omega
  ext
  · simp [List.getElem?_eq_getElem h_i_lt]
  · simp [List.getElem?_eq_getElem hi]
```

**Build risk**: low. Same `simp` concerns as S20a.

### Top-level proof of `walkEdges'_hcov_list_of_nodup`

With S20a–S20c in place, the top-level proof is structurally
straightforward:

```lean
lemma walkEdges'_hcov_list_of_nodup (walk : List V) (n : ℕ)
    (hlen : walk.length = n + 1)
    (hnodup : (walkEdges' walk).Nodup) :
    ∀ e ∈ walkEdges' walk, ∃! i : ℕ, i < n ∧
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2 := by
  intro e he
  have h0 : 0 < walk.length := by omega
  -- Existence: extract i₀ from mem_walkEdges'
  rw [mem_walkEdges'] at he
  obtain ⟨i₀, h_i₀_lt, hi₀_eq⟩ := he
  have h_i₀_lt' : i₀ < walk.length := by omega
  refine ⟨i₀, ⟨by omega, ?_, ?_⟩, ?_⟩
  -- existence components
  · rw [List.getElem?_eq_getElem h_i₀_lt']; rw [hi₀_eq]
  · rw [List.getElem?_eq_getElem h_i₀_lt]; rw [hi₀_eq]
  -- uniqueness
  rintro j ⟨hj_lt_n, hj_eq1, hj_eq2⟩
  have h_j_lt : j < walk.length := by omega
  have h_j1_lt : j + 1 < walk.length := by omega
  -- From hj_eq1, hj_eq2: e.1 = walk[j], e.2 = walk[j+1]
  rw [List.getElem?_eq_getElem h_j_lt] at hj_eq1
  rw [List.getElem?_eq_getElem h_j1_lt] at hj_eq2
  have h_e1 : e.1 = walk[j]'h_j_lt := Option.some_inj.mp hj_eq1.symm
  have h_e2 : e.2 = walk[j + 1]'h_j1_lt := Option.some_inj.mp hj_eq2.symm
  -- From hi₀_eq: e.1 = walk[i₀], e.2 = walk[i₀+1]
  have h_e1' : e.1 = walk[i₀]'h_i₀_lt' := by rw [hi₀_eq]
  have h_e2' : e.2 = walk[i₀ + 1]'h_i₀_lt := by rw [hi₀_eq]
  -- Derive equality of pairs at list-positions i₀ and j
  have h_pair_eq :
      (walkEdges' walk)[i₀]'(by
        rw [walkEdges'_length_of_pos walk h0]; omega) =
      (walkEdges' walk)[j]'(by
        rw [walkEdges'_length_of_pos walk h0]; omega) := by
    rw [walkEdges'_getElem_of_pos walk h0 i₀ h_i₀_lt,
        walkEdges'_getElem_of_pos walk h0 j h_j1_lt]
    -- Both pairs equal (e.1, e.2) via h_e1, h_e2, h_e1', h_e2'
    ext
    · rw [← h_e1', h_e1]
    · rw [← h_e2', h_e2]
  -- Apply Nodup.getElem_inj_iff
  exact (hnodup.getElem_inj_iff).mp h_pair_eq |>.symm
```

**Build risk**: moderate. The `Option.some_inj.mp` extraction and the
`Prod.ext` rewriting are conventional but easy to slip on. The
`Nodup.getElem_inj_iff` final invocation may need explicit `Fin`
packaging depending on the Mathlib version's signature.

## Mathlib API audit (v4.26 pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

All API used by the spec is verified present at the pin via
`gh search code` / direct `gh api` reads:

| Symbol | Path | Verified |
|---|---|---|
| `List.filterMap_eq_map_iff_forall_eq_some` | `Mathlib/Data/List/Basic.lean:2142` | ✓ |
| `List.length_map` | `Mathlib/Data/List/Basic.lean` | ✓ (Lean core) |
| `List.length_range` | core | ✓ |
| `List.getElem_map` | core | ✓ |
| `List.getElem_range` | core | ✓ |
| `List.getElem?_eq_getElem` | core | ✓ (used throughout the recipe) |
| `List.mem_range` | core | ✓ |
| `List.Nodup.getElem_inj_iff` | `Mathlib/Data/List/Nodup.lean:106` | ✓ |
| `Option.some_inj` | core | ✓ |
| `dif_pos` | core | ✓ |

No new imports needed beyond the recipe's existing `Mathlib.Data.List.Nodup`
chain (already pulled in via the SimpleGraph/DiGraph dependencies).

## Net effect on the file (after S20a–S20c + `walkEdges'_hcov_list_of_nodup` land)

| Dimension | Before S20-implement (post-S17/S18 merges) | After S20-implement |
|---|---|---|
| Recipe-side `hcov_list` obligation | open (caller-supplied) | **closed** (auto-derived from `Nodup`) |
| Recipe-side `hsteps_list` obligation | closed (S17 `walkEdges'_hsteps_list`) | closed |
| Recipe-side template list size | 13 | 16 (S20a, S20b, S20c, hcov_list_of_nodup are 4 lemmas) |
| Estimated LOC delta | — | +120–150 lines (4 lemmas with full docstrings) |
| Build-verifiable | — | yes (no new axioms, no new sorries) |

## Use in `remove_circuit_balanced`

After S20-implement lands, the deferred main-file proof of
`remove_circuit_balanced` (currently L1103, the file's last `sorry`)
reduces to:

```lean
theorem remove_circuit_balanced (G : DiGraph V) (C : DirectedCircuit G)
    (h_balanced : IsEulerianBalanced G)
    (h_nodup : (walkEdges' C.walk).Nodup)  -- supplied by Eulerian uniqueness
    (hlen : C.walk.length = n + 1) (hclosed : C.walk[0]? = C.walk[n]?) :
    IsEulerianBalanced (G.removeEdgeSet (walkEdges' C.walk).toFinset) := by
  intro v
  unfold IsBalanced inDegree outDegree DiGraph.removeEdgeSet
  apply remove_balanced_subset_balanced'
  · -- hsub: (walkEdges' C.walk).toFinset ⊆ G.edges
    intro e he
    rw [List.mem_toFinset] at he
    rw [mem_walkEdges'] at he
    obtain ⟨i, hi, he_eq⟩ := he
    -- e is a walk-step → e ∈ G.edges via DirectedCircuit.steps
    sorry  -- C.walk's steps are in G.edges (DirectedCircuit/DirectedTrail field)
  · exact h_balanced v
  · exact circuit_edge_balance_list' C.walk n v (walkEdges' C.walk)
        hlen hclosed
        (walkEdges'_hcov_list_of_nodup C.walk n hlen h_nodup)
        (walkEdges'_hsteps_list C.walk n hlen)
```

**Estimated body LOC after S20-implement**: ~15 lines, with one remaining
`sorry` for `hsub` (a one-liner once `DirectedCircuit.steps` is
exposed in the in-place refactor).

## Comparison with S18 (researcher-1, PR #17623)

S18 supplies the **open-walk** parallel of S14's `circuit_edge_balance'`
(`open_walk_edge_*_excess'`), targeting `directed_eulerian_path_iff`
(open Euler trails). S20 (this spec) is on the **closed-circuit** side
and is independent of S18's open-walk additions; both contribute to
the eventual `directed_eulerian_iff` proof along orthogonal axes:

* S14 + S15 + S16 + **S20-implement** ⟹ closed-circuit edge-balance discharge
  (`remove_circuit_balanced` for Euler circuits).
* S10 + S12 + S13 + **S18** + **S19** ⟹ open-walk endpoint-excess identification
  (toward `directed_eulerian_path_iff` for Euler trails).

No textual conflict between S18 and S20-implement: S18 appends in a
new "Iteration 18" section after `remove_balanced_subset_balanced'`;
S20-implement appends after S17's "S17 walkEdges-style List bridge"
section, which is between S16 and S18.

## Followup: when to land S20-implement

Defer until **at least S17 #17596 is merged** (since S20a builds on
`walkEdges'`, `mem_walkEdges'`). S17 is build-verified; merge expected
within the standard cadence (~1–4 hours). Once S17 lands on origin/main,
S20-implement is a self-contained ~120–150 LOC PR with low merge
conflict risk against S18 (textually disjoint).

## Why this is analysis-only

This S20 is documentation only — no Lean changes — for three reasons:

1. **S17 #17596 is not yet merged.** S20-implement's S20a directly
   uses S17's `walkEdges'` definition + `mem_walkEdges'` lemma. Stacking
   S20-implement on the unmerged S17 branch risks rebase conflicts if
   S17 needs revisions. Decoupling the spec lets the implementation
   land cleanly off the post-merge origin/main.
2. **Build verification cycle is ~45 minutes** (per the
   `proofs/.lake` self-symlink trap documented in
   `feedback_researcher_lake_symlink_broken.md`). The `walkEdges'_eq_map_of_pos`
   conversion may need iterative Mathlib-API adjustment (`congr` /
   `simp` set behaviour around `getD ∘ getElem?` is mildly
   version-dependent). Spec-first lets the next implementer fail fast
   on a single targeted build, rather than discovering the issue mid-PR.
3. **Parallel session contention.** S17 (researcher-4) and S18
   (researcher-1) both landed open PRs in the past 2 hours. A spec PR
   reduces collision risk while still advancing the slug's documentation.

## Pointers

- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean:687` — `walkEdges'`
  definition (S17, PR #17596).
- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean:697` — `mem_walkEdges'`
  membership characterization (S17, PR #17596).
- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean:727` —
  `walkEdges'_hsteps_list` (S17, PR #17596). S20-implement appends
  after this lemma.
- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean:549` —
  `circuit_edge_balance_list'` (S15) consumer of the
  `hcov_list`/`hsteps_list` pair.
- `Mathlib/Data/List/Nodup.lean:106` — `List.Nodup.getElem_inj_iff`.
- `Mathlib/Data/List/Basic.lean:2142` —
  `List.filterMap_eq_map_iff_forall_eq_some`.
