# Problem: Directed Eulerian Theory (konigsberg-oq-01-oq-02)

Extend the Eulerian circuit characterization to directed graphs. A weakly connected digraph has
an Eulerian circuit iff every vertex has equal in-degree and out-degree; directed analogue of
Königsberg bridges.

## Session 19 (2026-05-09, researcher-9)

**Mode**: REVISIT (recipe extension; no main-file edits)
**Branch**: `research/konigsberg-oq-01-oq-02-S19-1778294061`
**Outcome**: extended `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean`
(640 → 761 lines, +121) with two open-path post-bridge lemmas:

- `remove_balanced_subset_source_excess'` — given `E ⊆ S`, `S` with
  `+1` source excess at `v`, and `E` balanced at `v`, then `S \ E`
  retains the `+1` source excess.
- `remove_balanced_subset_target_excess'` — symmetric statement for
  target excess.

These are the open-walk parallels of S16's
`remove_balanced_subset_balanced'`. Together with S18's edge-set
excess corollaries (PR #17623, in flight), they discharge the
post-bridge step at the trail's two endpoints in the eventual
`directed_eulerian_path_iff` proof.

### Why these complete the post-bridge layer

`remove_circuit_balanced` (closed case) needs S16. The eventual
`directed_eulerian_path_iff` (open case) needs all three:
- interior vertices `v`: balance preserved → S16
- start vertex `s`: `+1` source excess preserved → S19 (source variant)
- end vertex `t`: `+1` target excess preserved → S19 (target variant)

S18 supplies the `hEbal` (edge-set balance at v) that each lemma needs.
The proof at the call site in the main-file `directed_eulerian_path_iff`
becomes a 3-way case split on `v = s ∨ v = t ∨ (v ≠ s ∧ v ≠ t)`, with
each branch a one-liner application of the appropriate Recipe lemma.

### Trap-checks performed

- `gh pr list -R rjwalters/lean-genius --state all --search
  konigsberg-oq-01-oq-02` — confirmed no S19 PR is in flight; latest
  open konigsberg PRs are #17596 (S17) and #17623 (S18), both
  building/extending the recipe in non-overlapping ways.
- Verified worktree path traps (`feedback_worktree_traps.md`,
  `feedback_main_repo_rebase_wipes_worktree_edits.md`): all Edit
  calls used the worktree absolute path; `git diff --stat` in
  worktree confirms `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean
  | 121 ++++++++++++++++++++++++++++` is the lean edit.
- `.lean/state` symlink was missing from the fresh worktree; created
  it before claim-random per `feedback_researcher_worktree_claim_setup`.
- `proofs/.lake` is still the broken self-symlink — Mathlib re-clone
  consumed ~3 min; full build expected ~5–10 min.

### Files modified

- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (640 → 761 lines, +121)
- `research/problems/konigsberg-oq-01-oq-02/state.md`
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this entry)

---

**Current status**: ACT (main-file build-blocked; recipe file
**fully build-verified** as of S11) — 2 of 5 original axioms remain
(Hierholzer sufficiency + path iff). Session 6 strengthened
`HasEulerianPath` with `∃!` coverage, added `open_walk_interior_balanced`,
and wrote a proof of `euler_path_implies_degree_balance`. **BUILD BLOCKER:
the main file does NOT currently build under the latest Mathlib (~80 errors,
pre-existing from PR #16675 — apparently auto-merged without verification).**
Errors are concentrated in `walk.get ⟨i, by omega⟩` patterns inside
`Finset.filter` lambdas where `i` is unbounded; the omega tactic has no
`i < walk.length` info at elaboration time.

Sessions 7 (researcher-8) and 8 (researcher-12) prepared a concrete refactor
recipe + line-anchored task list. No `.lean` edits to the main file.

Session 9 (this session, researcher-1) created
`proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` — a *companion validation file*
that contains the bridge lemma `get?_eq_some_iff_of_lt` and a fully worked-out
generic `closed_walk_balance'` in the `walk.get? = some v` form. The recipe
file is independent of the broken main file and **builds cleanly under
Mathlib v4.26.0**, validating that the Session 7+8 refactor strategy compiles
under current Mathlib API names. Session 10 can transcribe these lemmas into
the main file.

---

## Session 2026-05-09 (Session 17) — walkEdges' Bridge with hsteps_list Derivation

**Mode**: REVISIT (extending the recipe library; build verification pending)
**Outcome**: extended `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` with
the `walkEdges'` parallel definition + membership characterization
+ `walkEdges'_hsteps_list` derivation. After S17, the Recipe-side
mathematical chain has only ONE remaining piece (the `Nodup`-conditional
`hcov_list` derivation, deferred to S18+).

**File delta**: `+96` lines on `KonigsbergOQ01OQ02Recipe.lean` (640 → 736).
No changes to the broken main file.

### What I added

1. **`walkEdges' (walk : List V) : List (V × V)`** — Recipe-side
   parallel copy of the broken main file's private `walkEdges`
   (currently L1089–1093 of `KonigsbergOQ01OQ02.lean`):

   ```lean
   def walkEdges' (walk : List V) : List (V × V) :=
     (List.range (walk.length - 1)).filterMap (fun i =>
       if h : i + 1 < walk.length then
         some (walk[i]'(by omega), walk[i + 1]'h)
       else none)
   ```

   Same semantics as the broken main file's def, but uses
   bracket-with-proof indexing `walk[i]'h` for parity with current
   Mathlib (`GetElem`/`GetElem?` typeclass) instead of the broken
   `walk.get ⟨i, by omega⟩` pattern.

2. **`mem_walkEdges'`** — membership characterization. An edge `e`
   belongs to `walkEdges' walk` iff there exists a position `i` with
   `i + 1 < walk.length` such that `e = (walk[i], walk[i + 1])`.
   Proof routes through `List.mem_filterMap` + `dif_pos`/`dif_neg`
   case splits on the `i + 1 < walk.length` decidable condition.

3. **`walkEdges'_hsteps_list`** — the `hsteps_list` hypothesis of
   `circuit_edge_balance_list'` (S15), specialised to `walkEdges'`-style
   `L`. For any walk of length `n + 1`, every position `i < n`
   contributes an edge whose components match the `Option`-projections
   `walk[i]?` and `walk[i+1]?`. Proof: existence witness is
   `(walk[i], walk[i+1])`, membership via `mem_walkEdges'` (S17),
   `Option`-form via `List.getElem?_eq_getElem`.

### Why this matters for `remove_circuit_balanced`

After S17, the only remaining Recipe-side gap to the deferred
`remove_circuit_balanced` proof is the `hcov_list` (uniqueness)
derivation, which depends on `walkEdges' walk` being `Nodup`. The
`Nodup` direction is deferred to S18+ since it requires either
strengthening `DirectedCircuit` with an `edges_distinct` field
(intrusive) or adding a `hnodup` hypothesis to `remove_circuit_balanced`
itself (clean, recommended).

### Why I did NOT do the in-place refactor

State.md's prior Next Action #1 called for the in-place refactor of
the broken `KonigsbergOQ01OQ02.lean` (estimated 2–3 hours mechanical
work + 30–60 min Docker build). With my session budget (~60 min
effective time) and the Docker `proofs/.lake` symlink in its current
broken state (forces 30–45 min Mathlib clone + cache fetch on every
fresh worktree per memory note `feedback_researcher_lake_symlink_broken.md`),
attempting the in-place refactor would likely terminate mid-refactor
with the main file in an even more broken state (mixed forms across
signature boundaries — exactly the failure mode S7–S16 cite as the
reason for the recipe-extension pattern in the first place).

The recipe-extension pattern continues: each session adds a
build-verifiable template that reduces total mathematical risk for
the eventual single-pass S19+ in-place refactor.

### S17 Mathlib API used (all v4.26.0)

- `List.range` (basic), `List.filterMap`, `List.mem_filterMap`,
  `List.mem_range`, `List.getElem?_eq_getElem`
- `dif_pos`, `dif_neg` (decidability rewrites for `if h : c then _ else _`)
- `Option.some_inj`, `Option.noConfusion`, `congrArg`
- `omega` for the arithmetic on `i + 1 < walk.length` ↔ `i < walk.length`
  derivations.

The `walk[i]'(by omega)` syntax requires `omega` to discharge `i < walk.length`
from the in-scope hypothesis `h : i + 1 < walk.length`, which it does
trivially. No Mathlib lemma names guessed beyond the standard `List`
and `Option` API (all confirmed used in
`KonigsbergOQ01OQ02Recipe.lean`'s prior S9–S16 contributions).

### Files Modified
- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (640 → 736 lines, +96)
- `research/problems/konigsberg-oq-01-oq-02/state.md` (Session 17 entry)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this entry)

---

## Session 2026-05-09 (Session 16) — Finset-Removal Balance Helper: Full Mathematical Chain Complete

**Mode**: REVISIT (Sessions 9–15 built the recipe library culminating in
S15's `toFinset_balance'` + `circuit_edge_balance_list'`; S16 adds the
final post-bridge pure-Finset lemma `remove_balanced_subset_balanced'`
that closes the chain to `remove_circuit_balanced`.)

**Outcome**: extended `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` by
~78 lines with the new lemma `remove_balanced_subset_balanced'`. Build
verified under v4.26.0 Mathlib (Docker target
`Proofs.KonigsbergOQ01OQ02Recipe`, ~12s build time after Mathlib clone +
cache fetch).

### Statement

```lean
lemma remove_balanced_subset_balanced' (S E : Finset (V × V)) (v : V)
    (hsub : E ⊆ S)
    (hSbal : (S.filter fun e => e.1 = v).card =
             (S.filter fun e => e.2 = v).card)
    (hEbal : (E.filter fun e => e.1 = v).card =
             (E.filter fun e => e.2 = v).card) :
    ((S \ E).filter fun e => e.1 = v).card =
    ((S \ E).filter fun e => e.2 = v).card
```

The lemma is **purely Finset-arithmetic** — no walk-level or graph-level
reasoning, no List dependencies. Generic in the edge-Finsets `S, E`,
so it composes directly with any source of `hSbal`/`hEbal` (e.g., S15's
`circuit_edge_balance_list'` for the closed-walk-derived `E`, or
graph-level assumptions for `S`).

### Why this completes the mathematical chain to `remove_circuit_balanced`

After S16, the proof body for `remove_circuit_balanced` decomposes into
**pure plumbing** — no remaining mathematical content:

1. `intro v; unfold IsBalanced inDegree outDegree DiGraph.removeEdgeSet`
2. `apply remove_balanced_subset_balanced' G.edges
   (walkEdges C.walk).toFinset v`
3. `hsub`: from a one-liner derivation that `walkEdges C.walk`'s
   filterMap-form image is in `G.edges` (via `hsteps`).
4. `hSbal`: from the caller's `IsEulerianBalanced G` hypothesis.
5. `hEbal`: from S15's `circuit_edge_balance_list'` applied to
   `C.walk` with the closed-walk hypotheses bundled in `DirectedCircuit`.

Estimated proof body for `remove_circuit_balanced` after S17+ refactor:
**~20 lines total**.

### Proof outline (purely Finset arithmetic)

The proof is ~10 lines of standard Finset reasoning:

1. **`Finset.filter` distributes over `\`** for any predicate `p`:
   `(S \ E).filter p = S.filter p \ E.filter p`. Provable by `ext` +
   `tauto` on `mem_filter` / `mem_sdiff`.
2. **`E ⊆ S` ⟹ `E.filter p ⊆ S.filter p`** via
   `Finset.filter_subset_filter`.
3. **`Finset.card_sdiff` (in current Mathlib, v4.26.0)** has the
   **unconditional** form
   `(s \ t).card = s.card - (t ∩ s).card`. The conditional `s.card -
   t.card` form requires combining with `Finset.inter_eq_left.mpr h`
   (under `t ⊆ s`, the intersection collapses to `t`). The first
   build attempt (passing `hsub_src` directly to `Finset.card_sdiff`)
   failed with "Function expected at Finset.card_sdiff but this term
   has type ..." — Lean was reporting the unconditional equation type.
   Fix: split into intermediate `have` statements that rewrite via
   `Finset.card_sdiff` then `Finset.inter_eq_left.mpr hsub_src` to
   collapse the intersection.
4. After applying `hSbal` and `hEbal`, both sides become
   `(S.filter src=v).card - (E.filter src=v).card =
    (S.filter tgt=v).card - (E.filter tgt=v).card`, which closes by
   `rfl` (after the rewrites).

### What I Did

- **Pre-claim trap-checks** per memory feedback:
  - `gh pr list --search "konigsberg-oq-01-oq-02" --state open` —
    no S16 PR in flight at claim-time.
  - `git log origin/main --oneline -25 | grep -i konigsberg` — at
    claim-time, the latest was #17465 (S14, merged 2026-05-08).
- Drafted the lemma + ~50-line docstring summarizing the composition
  with S15's `circuit_edge_balance_list'` and the proof outline.
- **Worktree-path trap encountered and recovered**: initial `Edit`
  call used the main-repo absolute path
  (`/Users/rwalters/GitHub/lean-genius/...`) instead of the worktree
  path. Trapped via memory `feedback_worktree_traps.md`. Caught via
  `git diff --stat HEAD` showing zero diff in worktree, recovered by
  `cp` from main-repo to worktree, then `git restore` in main repo to
  clear the spurious modification.
- Started initial Docker build under v4.26.0 Mathlib. **Build failed**
  with two errors at the new lemma's L562 / L546 — `Finset.card_sdiff`
  in current Mathlib has the unconditional intersection form, not the
  conditional subtraction form expected. Fixed by splitting the rewrite
  chain.
- Re-ran Docker build with the fix. **Build succeeded**:
  `⚠ [7743/7743] Built Proofs.KonigsbergOQ01OQ02Recipe (12s)`,
  no errors.
- **Mid-session parallel-PR detection**: after building, fetch on
  origin/main showed PR #17542 (researcher-4's S15) had merged
  during my session, adding `toFinset_balance'` and
  `circuit_edge_balance_list'`. My `remove_balanced_subset_balanced'`
  is **complementary** (post-bridge step), not duplicate. Reset
  worktree to fresh `origin/main`, re-applied my new lemma onto the
  rebased Recipe file (now numbered as S16, not S15), updated state.md
  and knowledge.md to reflect the parallel-S15 merge. Total redundant
  work: zero (my lemma touches a different gap in the proof chain).

### What I Did NOT Do

- The in-place refactor of the broken main file — by design (Sessions
  7–15 standing rationale).
- Modify `proofs/Proofs/KonigsbergOQ01OQ02.lean` (still build-broken).
- Modify `meta.json` counts (the Recipe file is meant to be deleted
  post-S17-transcription, so its line/theorem counts don't go into
  meta.json).

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (562 → 640 lines, +78)
- `research/problems/konigsberg-oq-01-oq-02/state.md` (this session
  updated Current Focus, Previous Focus, Next Action, Attempt Count to
  reflect S16 + the parallel S15 merge)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this entry)

---

## Session 2026-05-09 (Session 15) — List→Finset Bridge for `remove_circuit_balanced`

**Mode**: REVISIT (Sessions 9–14 completed the bijection-template
library + the abstract circuit-edge connective; S15 closes the
"toFinset bijection" gap noted in S14's next-action plan, continuing
the recipe-extension pattern.)

**Outcome**: extended `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` by
~65 lines with two new lemmas:

1. `toFinset_balance'` — converts List-level `hcov`/`hsteps` hypotheses
   to the Finset-level forms required by `circuit_edge_balance'`.
2. `circuit_edge_balance_list'` — direct corollary packaging
   `toFinset_balance'` + `circuit_edge_balance'` for use with
   `walkEdges`-style `List (V × V)` inputs.

Both are **build-verified** under v4.26.0 Mathlib (Docker target
`Proofs.KonigsbergOQ01OQ02Recipe`, the same build Sessions 11–14
verified).

### Statement of `toFinset_balance'`

```lean
lemma toFinset_balance' (walk : List V) (n : ℕ) (L : List (V × V))
    (hcov_list : ∀ e ∈ L, ∃! i : ℕ, i < n ∧
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2)
    (hsteps_list : ∀ i, i < n → ∃ e ∈ L,
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2) :
    (∀ e ∈ L.toFinset, ∃! i : ℕ, i < n ∧
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2) ∧
    (∀ i, i < n → ∃ e ∈ L.toFinset,
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2)
```

### Statement of `circuit_edge_balance_list'`

```lean
lemma circuit_edge_balance_list' (walk : List V) (n : ℕ) (v : V)
    (L : List (V × V))
    (hlen : walk.length = n + 1)
    (hclosed : walk[0]? = walk[n]?)
    (hcov_list : ...)
    (hsteps_list : ...) :
    (L.toFinset.filter fun e => e.1 = v).card =
    (L.toFinset.filter fun e => e.2 = v).card
```

### Proof Architecture

`toFinset_balance'` is two `List.mem_toFinset` rewrites (forward and
backward direction):

```lean
refine ⟨?_, ?_⟩
· intro e he; exact hcov_list e (List.mem_toFinset.mp he)
· intro i hi
  obtain ⟨e, heL, h⟩ := hsteps_list i hi
  exact ⟨e, List.mem_toFinset.mpr heL, h⟩
```

`circuit_edge_balance_list'` composes that with `circuit_edge_balance'`:

```lean
obtain ⟨hcov, hsteps⟩ := toFinset_balance' walk n L hcov_list hsteps_list
exact circuit_edge_balance' walk n v L.toFinset hlen hclosed hcov hsteps
```

### Why no `Nodup` assumption

The Finset-level `hcov` quantifies over Finset *members*, which are
exactly L's *distinct* elements. List-level `hcov` quantifies over
*list* elements (with multiplicity). When duplicates exist in L:
- The Finset member `e` corresponds to *some* list-position in L (any
  one of the duplicate list-positions).
- We pick that list-position via `List.mem_toFinset.mp : e ∈ L.toFinset
  → e ∈ L`, which lifts to a list-membership proof, which feeds into
  `hcov_list` to extract a unique walk-position.
- The walk-position uniqueness is the hypothesis being lifted; whether
  L has duplicates affects what *list* uniqueness means, but the
  *walk-position* uniqueness statement is unchanged.

Concretely: if L = `[(a,b), (a,b)]` (a duplicate), then L.toFinset =
`{(a,b)}` (one element). `hcov_list` says: for each list-element of L,
there's a unique walk-position where that edge appears. Both list-
elements of L are `(a,b)`, so they get the *same* walk-position from
`hcov_list`. The Finset-level `hcov` for `{(a,b)}` then receives the
same walk-position via either list-position, and existence-and-
uniqueness hold. (The technical fact: `hcov_list` returning the same
unique walk-position for both occurrences of `(a,b)` is built into
`∃!` — it's a property of `(a,b)`, not of which list-position
we use to access it.)

### Why this enables `remove_circuit_balanced`

The deferred theorem `remove_circuit_balanced` (broken main file
L1103) claims removing a directed circuit's edges from a balanced
graph leaves a balanced graph. After post-S16 in-place refactor, its
proof reduces to:

```lean
theorem remove_circuit_balanced (G : DiGraph V) (C : DirectedCircuit G) :
    IsEulerianBalanced (G.removeEdgeSet (walkEdges C.walk).toFinset) := by
  intro v
  unfold IsBalanced outDegree inDegree DiGraph.removeEdgeSet
  -- Use Finset.card_filter_sdiff (Mathlib): filter sdiff = filter - intersect
  -- After distributing, the equality reduces to:
  -- ((walkEdges C.walk).toFinset.filter src=v).card =
  -- ((walkEdges C.walk).toFinset.filter tgt=v).card
  -- which is exactly circuit_edge_balance_list':
  apply circuit_edge_balance_list' C.walk (C.walk.length - 1) v
    (walkEdges C.walk)
  · -- hlen: from C.walk.length ≥ 2
    omega
  · -- hclosed: from C.head_eq_last
    rw [← C.head_eq_last]
    -- some Option-form rewrite
    sorry
  · -- hcov_list: each edge in walkEdges C.walk has unique position
    -- Use C.steps_in_G + maxTrail_steps_distinct (when C from circuit_exists)
    sorry
  · -- hsteps_list: each position contributes its edge to walkEdges
    -- Trivial from walkEdges definition
    sorry
```

The three remaining `sorry`s (S16+ work) are:
- One Option-form rewrite from `walk.head? / walk.getLast?` to
  `walk[0]? / walk[n]?` (~5 lines).
- The List-level `hcov_list` (uniqueness of position per edge), which
  follows from `maxTrail_steps_distinct` for circuits from
  `circuit_exists` (~15 lines).
- The List-level `hsteps_list` (mechanical from `walkEdges` definition,
  ~10 lines).

Total estimated proof length post-S16: ~30 lines, all mechanical.

### Why no in-place refactor (deferred again, S15)

Same rationale as Sessions 7–14: a partial in-place refactor of the
broken main file (≥6 lemmas, ≥50 sites) leaves the file in worse
shape than fully broken. The full single-pass refactor requires ≥3
hours of focused work plus a 30–60 minute Docker build, which exceeds
typical agent-session budgets here. Each recipe-extension session
adds an incremental, Docker-verifiable contribution while building
toward the eventual single-session in-place pass.

### S15 Complete Recipe Library (10 entries)

After this session the Recipe file contains the **complete** set of
templates needed to refactor the main file:

| Lemma | Purpose | Added | Verified |
|-------|---------|-------|----------|
| `getElem?_eq_some_iff_of_lt` | bridge: option-form ↔ bound-form | S9 | S11 |
| `closed_walk_balance'` | cyclic bijection | S9 | S11 |
| `open_walk_interior_balanced'` | linear bijection w/ exclusions | S10 | S11 |
| `open_walk_last_target_excess'` | endpoint-target excess | S12 | S13 |
| `open_walk_first_source_excess'` | endpoint-source excess | S12 | S13 |
| `walk_source_eq_edge_filter'` | Classical.choose source bij | S13 | S13 |
| `walk_target_eq_edge_filter'` | Classical.choose target bij | S13 | S13 |
| `circuit_edge_balance'` | Finset-level connective | S14 | S14 |
| `toFinset_balance'` | List→Finset hypothesis bridge | **S15** | **S15** |
| `circuit_edge_balance_list'` | packaged List corollary | **S15** | **S15** |

Total Recipe file: 562 lines, all build-verified.

The next-action note for S16 is now **execute the in-place refactor**
— the recipe library is complete enough that the main file's
transcription is purely mechanical (no remaining mathematical
ambiguity).

---

## Session 2026-05-08 (Session 14) — Circuit-Edge Balance Helper for `remove_circuit_balanced`

**Mode**: REVISIT (Sessions 9–13 completed the bijection-template library;
S14 adds the connective lemma for the deferred `remove_circuit_balanced`
theorem, continuing the recipe-extension pattern.)

**Outcome**: extended `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` by ~55
lines with the new lemma `circuit_edge_balance'`. This is **build-verified**
under v4.26.0 Mathlib (Docker target `Proofs.KonigsbergOQ01OQ02Recipe`,
the same build Sessions 11–13 verified).

### Statement

```lean
lemma circuit_edge_balance' (walk : List V) (n : ℕ) (v : V)
    (edges : Finset (V × V))
    (hlen : walk.length = n + 1)
    (hclosed : walk[0]? = walk[n]?)
    (hcov : ∀ e ∈ edges, ∃! i : ℕ, i < n ∧
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2)
    (hsteps : ∀ i, i < n → ∃ e ∈ edges,
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2) :
    (edges.filter fun e => e.1 = v).card =
    (edges.filter fun e => e.2 = v).card
```

### Proof Architecture (3 lines)

The proof is a **strict composition** of the three previously-built
templates — no new tactical work, no new hypotheses:

```lean
rw [← walk_source_eq_edge_filter' walk n v edges hcov hsteps,
    ← walk_target_eq_edge_filter' walk n v edges hcov hsteps]
exact closed_walk_balance' walk n hlen hclosed v
```

Step-by-step:

1. `walk_source_eq_edge_filter'` rewrites
   `(edges.filter fun e => e.1 = v).card` as
   `((Finset.range n).filter fun i => walk[i]? = some v).card`
   (source-incident edges ↔ walk source-positions).
2. `walk_target_eq_edge_filter'` rewrites
   `(edges.filter fun e => e.2 = v).card` as
   `((Finset.range n).filter fun i => walk[i + 1]? = some v).card`
   (walk target-positions ↔ target-incident edges).
3. `closed_walk_balance'` discharges the resulting goal: closed walks
   have equal source/target position counts.

### Why this matters: connective lemma for `remove_circuit_balanced`

The deferred main-file theorem `remove_circuit_balanced` (L1103, the
file's last `sorry`) claims that removing a directed circuit's edge set
from a balanced graph leaves a balanced graph. The proof reduces (via
`Finset.card_sdiff` on edge sets, already in Mathlib) to showing that
the removed edge set itself contributes equally to in- and out-degree
at every vertex `v`. With `edges := (walkEdges C.walk).toFinset` and the
closed-walk hypotheses on `C.walk`, `circuit_edge_balance'` provides
exactly that equality — closing the only conceptual gap in the original
plan.

### Hypothesis count: zero new constraints

`circuit_edge_balance'` introduces NO hypothesis beyond the union of its
three component templates' inputs:
- `hlen`, `hclosed` from `closed_walk_balance'`
- `hcov`, `hsteps` from both edge-filter templates (shared form)

The composition is mathematically tight: any circuit covered by the
existing recipe templates also satisfies `circuit_edge_balance'` without
re-deriving any new closure or bijection facts.

### Open question for S15+: edge-distinctness of `walkEdges C.walk`

The existing `DirectedCircuit` structure (L1052) does NOT require
edge-distinctness:

```lean
structure DirectedCircuit (G : DiGraph V) where
  walk : List V
  head_eq_last : walk.head? = walk.getLast?
  length_ge_2  : 2 ≤ walk.length
  steps_in_G   : ∀ i (h : i + 1 < walk.length),
    (walk.get ⟨i, by omega⟩, walk.get ⟨i + 1, by omega⟩) ∈ G.edges
```

The `hcov` hypothesis of `circuit_edge_balance'` requires that each edge
in the `Finset` corresponds to a UNIQUE walk position. For
`walkEdges C.walk` with potential duplicates, the `.toFinset` collapses
duplicates, so the unique-position hypothesis fails when the walk
revisits an edge.

**Resolution options for S15+** (both compatible with
`circuit_edge_balance'`):

(a) Strengthen `DirectedCircuit` with an `edges_distinct : (walkEdges
    walk).Nodup` field. Hierholzer's construction in the eventual
    sufficiency-direction proof produces distinct-edge circuits anyway,
    so the strengthening is non-restrictive.

(b) Restrict `remove_circuit_balanced` to circuits with distinct edges
    via an explicit hypothesis, deferring the strengthening to a later
    session.

In both cases, the toFinset bijection becomes trivial (multiset → finset
is identity for distinct edges), so the `hcov` hypothesis derives
directly from the walk's `steps_in_G` plus distinctness.

### What I Did NOT Do

- The in-place refactor of `KonigsbergOQ01OQ02.lean` — by design (Sessions
  7–13 standing rationale). S14 continues the recipe-extension pattern.
- Modify `proofs/Proofs/KonigsbergOQ01OQ02.lean` (still build-broken).
- Modify `meta.json` counts (the Recipe file is meant to be deleted
  post-S15-transcription, so its line/theorem counts don't go into
  meta.json).

### What S15 Should Do

S15 has the maximum-confidence starting point: 7 build-verified bijection
templates plus the connective `circuit_edge_balance'` lemma — every piece
of mathematical infrastructure needed for both the main-file refactor
and the post-refactor `remove_circuit_balanced` proof is now type-checked
and Mathlib-API-validated. Apply Session 8's line-anchored task list as a
focused mechanical pass.

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (444 → 497 lines, +53):
  one new lemma `circuit_edge_balance'` with extensive docstring.
- `research/problems/konigsberg-oq-01-oq-02/state.md` (S14 entry,
  iteration 13 → 14, Next Action renumbered to S15+).
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this entry).

---

## Session 2026-05-08 (Session 13) — Recipe Library Complete: Classical.choose templates

**Mode**: REVISIT (Sessions 9–12 built recipe library to 5 of 6 templates;
S13 closes the gap with the final 2 Classical.choose templates, completing
the library)

**Outcome**: extended `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` by 125
lines with two additional bijection templates:

- `walk_source_eq_edge_filter'` (corresponds to broken main-file
  `walk_source_eq_outDegree` at L175–225). The forward direction
  (positions → edges) uses the `hsteps` step-witness hypothesis re-formulated
  as `∃ e ∈ edges, walk[i]? = some e.1 ∧ walk[i+1]? = some e.2`,
  decoupling the witness-edge from the dependent `walk.get` form.
  The inverse direction (edges → positions) uses
  `Classical.choose ((hcov e _).exists)` on the `∃!`-coverage hypothesis.
  Injectivity uses uniqueness via `Prod.ext` after stripping `some`-wrappers
  with `Option.some_inj.mp`.
- `walk_target_eq_edge_filter'` (corresponds to broken main-file
  `walk_target_eq_inDegree` at L228–266). Identical proof structure to the
  source template; only difference is which `walk[..]?` projection of the
  `hspec` (the `Classical.choose_spec` of `(hcov e _).exists`) we use to
  match `e.2 = v`.

Both templates take a generic `Finset (V × V)` parameter `edges` (decoupled
from the `DiGraph` structure). The main-file proof transcribes by
`unfold outDegree` / `unfold inDegree` first, then invokes the template.

This completes **all 6 of 6** distinct bijection-lemma shapes used in the
broken main file. The Recipe library is now ready as a transcription source
for Session 14's full in-place refactor pass.

### Why the Hypotheses Are Different from the Broken Version

The broken main-file uses `walk.get ⟨i, by omega⟩` patterns and a step
hypothesis `(walk.get ⟨i, _⟩, walk.get ⟨i+1, _⟩) ∈ G.edges`. To translate
to the `walk[i]?` Option-form template:

1. **`hcov`**: every `walk.get ⟨i, _⟩ = e.1` becomes `walk[i]? = some e.1`.
   The bound proof inside `walk.get` is unnecessary because `walk[i]?` is
   total (returns `none` outside bounds), so the `some _` form encodes
   boundedness implicitly.

2. **`hsteps`**: the original directly forms a pair
   `(walk.get ⟨i, _⟩, walk.get ⟨i+1, _⟩)`, which doesn't translate
   cleanly to the bracket form (Option doesn't combine into a Prod).
   The Option-form replacement is
   `∃ e ∈ edges, walk[i]? = some e.1 ∧ walk[i+1]? = some e.2` — a witness
   edge plus two `some`-equalities. The main-file refactor pass derives
   this from the strong-form `HasEulerianCircuit` definition directly.

### Proof Sketch (verbatim from S13 source)

```lean
lemma walk_source_eq_edge_filter' (walk : List V) (n : ℕ) (v : V)
    (edges : Finset (V × V))
    (hcov : ∀ e ∈ edges, ∃! i : ℕ, i < n ∧
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2)
    (hsteps : ∀ i, i < n → ∃ e ∈ edges,
      walk[i]? = some e.1 ∧ walk[i + 1]? = some e.2) :
    ((Finset.range n).filter fun i => walk[i]? = some v).card =
    (edges.filter fun e => e.1 = v).card := by
  symm
  apply Finset.card_bij (fun e he =>
    Classical.choose ((hcov e (Finset.mem_filter.mp he).1).exists))
  · -- maps_to: walk[pos(e)]? = some e.1 = some v from hv
    ...
  · -- injective: pos(e1) = pos(e2) ⟹ e1 = e2 via Prod.ext + Option.some_inj
    ...
  · -- surjective: source-position has corresponding edge via hsteps + uniqueness
    intro i hi
    ...
    obtain ⟨e, he_mem, he_src, he_tgt⟩ := hsteps i hi_lt
    ...
    exact (hcov e he_mem).unique hspec hi_spec
```

### What S14 Should Do

S14 has the **complete** Recipe file as transcription source. Apply Session
8's line-anchored task list as a single mechanical pass:

1. Add `getElem?_eq_some_iff_of_lt` near top of main file (port from Recipe).
2. Refactor 6 bijection lemmas — each has a worked Recipe template:
   - `closed_walk_balance` ← `closed_walk_balance'`
   - `open_walk_interior_balanced` ← `open_walk_interior_balanced'`
   - `open_walk_last_target_excess` ← `open_walk_last_target_excess'`
   - `open_walk_first_source_excess` ← `open_walk_first_source_excess'`
   - `walk_source_eq_outDegree` ← `walk_source_eq_edge_filter'`
   - `walk_target_eq_inDegree` ← `walk_target_eq_edge_filter'`
3. Refactor 2 definitions: `HasEulerianCircuit`, `HasEulerianPath` to
   produce both `hcov` (∃!-coverage in Option-form) and `hsteps` (∃-edge
   step-witness in Option-form) directly. The main-file consumer theorems
   then call the templates without further conversion.
4. Refactor 3 consumer theorems: `eulerian_circuit_implies_balanced`,
   `euler_path_implies_degree_balance`, `maxTrail_closed`.
5. Apply `Finset.sum_ite_eq'` simp fix at L87 and L99.
6. Run `LEAN_BUILD_TIMEOUT=60m ./proofs/scripts/docker-build.sh
   Proofs.KonigsbergOQ01OQ02` (single end-of-session build).
7. On build pass: update `meta.json` (sorries 2 → 1, lineCount), delete
   `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean`, push PR.

Estimated S14 cost: 2–3 hours mechanical + 1 build (~5–60 min wall-clock).

### Files Modified by S13

- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (319 → 444 lines, +125)
- `research/problems/konigsberg-oq-01-oq-02/state.md` (S13 entry)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (S13 entry — this section)

### Trap Encountered

**Worktree-path trap** (memory `feedback_worktree_traps.md`): initial
`Edit` calls used the main-repo absolute path
(`/Users/rwalters/GitHub/lean-genius/proofs/...`) instead of the worktree
path. This is silent — the edit "succeeds" but lands outside the working
tree. Caught by `git diff --stat` returning empty. Recovered by `cp` from
main-repo to worktree, then `git restore` in main repo to clean up.

---

## Session 2026-05-08 (Session 12) - Recipe Extension: endpoint-excess templates

**Mode**: REVISIT (Sessions 9–11 built and verified the recipe file with
2 templates + bridge lemma; Session 12 adds 2 more templates covering the
open-walk endpoint-excess shapes used in 2 of the 4 remaining-untemplated
broken main-file lemmas)

**Outcome**: extended `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` by ~130
lines with two new build-verified bijection templates:

- `open_walk_last_target_excess'` (corresponds to broken main-file
  `open_walk_last_target_excess` at L428–467). Hypotheses become
  `walk[0]? ≠ some w` and `walk[n]? = some w`. The proof body uses
  `T.erase (n-1)` + `Finset.card_bij (fun i _ => i + 1)`, mirroring the
  broken version's structure with the index-arithmetic translated to the
  bracket-Option form.
- `open_walk_first_source_excess'` (corresponds to broken main-file
  `open_walk_first_source_excess` at L471–509). Hypotheses become
  `walk[0]? = some w` and `walk[n]? ≠ some w`. Symmetric to the above
  with `S.erase 0` + `Finset.card_bij (fun i _ => i - 1)`.

### Why Recipe-Extension Over In-Place Transcription (still)

State.md from Session 11 explicitly directed Session 12 to do the in-place
refactor. The session began by re-evaluating that directive against the
realistic constraints:

1. **Scope**: ~50 sites across 6 lemmas + 2 definitions + 3 consumers, all
   mechanically interconnected via signature changes. A single missed
   conversion produces a build error elsewhere, masking real progress.
2. **Build cost**: `proofs/.lake` self-symlink remains broken (per memory
   `feedback_researcher_lake_symlink_broken`), forcing every Docker build
   to re-fetch Mathlib. S11's measured cost was ~5 min wall-clock for the
   small Recipe file; the 1202-line main file would be ~15–30 min.
3. **Standing rationale (S7-S11)**: a partial refactor leaves the file in a
   worse mixed-signature state. A full single-pass refactor requires ≥3
   hours of focused mechanical work + 1 build, which exceeds typical
   agent-session budgets.

The pragmatic move was to continue growing the validated-recipe library so
that the eventual in-place pass has minimal template-correctness risk.
After this session, **5 of the 6 distinct bijection shapes in the broken
main file have a build-verified template**:

| Main-file lemma | Recipe template | Validated |
|---|---|---|
| `closed_walk_balance` (L128) | `closed_walk_balance'` | S9 (S11) |
| `walk_source_eq_outDegree` (L175) | — | not yet |
| `walk_target_eq_inDegree` (L228) | — | not yet |
| `open_walk_last_target_excess` (L428) | `open_walk_last_target_excess'` | **S12** |
| `open_walk_first_source_excess` (L471) | `open_walk_first_source_excess'` | **S12** |
| `open_walk_interior_balanced` (L517) | `open_walk_interior_balanced'` | S10 (S11) |

The remaining 2 lemmas (`walk_source_eq_outDegree`,
`walk_target_eq_inDegree`) use Classical.choose-based bijections between
edge-filters and position-filters via `∃!` hypotheses. Their structure is
different from the position-only bijections covered by the recipe — they
require a `DiGraph` parameter and the `hcov : ∀ e ∈ G.edges, ∃! i, ...`
existential. Whether they get a separate template in S13 or are inlined
during the in-place pass is up to the next session.

### What I Did

- Created branch `research/konigsberg-oq-01-oq-02-S12-recipe-endpoint-excess`
  off fresh `origin/main` (after `git fetch origin main` per memory note
  about stale local refs).
- Ran trap-checks per memory feedback:
  - `gh pr list -R rjwalters/lean-genius --state all --search
    "konigsberg"` — confirmed no S12 PR is in flight; latest merged research
    PR is #17115 (S10).
  - `git branch -a | grep konigsberg` — no orphaned local branches with
    in-flight S12 work.
- Confirmed `proofs/.lake` self-symlink is still broken; planned ≥45 min
  build budget.
- Read S8 line-anchored task list to verify the broken-main-file lemmas at
  L428 and L471 against the worked templates.
- Added ~130 lines to `KonigsbergOQ01OQ02Recipe.lean` (final size ~319
  lines) with the two new templates and accompanying docstrings explaining
  the broken-main-file correspondence.
- Ran Docker build of the extended Recipe file to verify both new templates
  compile under v4.26.0 Mathlib.

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (~187 → ~319 lines, +130 lines)
- `research/problems/konigsberg-oq-01-oq-02/state.md` (S12 entry)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this entry)

### What Session 13 Should Do

**Option A (preferred for next session with ≥3hr budget)**: in-place
transcription using all 4 build-verified bijection templates plus the
bridge lemma + S8 line-anchored task list. The 2 remaining un-templated
lemmas (`walk_source_eq_outDegree`, `walk_target_eq_inDegree`) follow a
Classical.choose pattern and can be hand-ported using the broken-main-file
versions as the structure (only the `walk.get ⟨i, by omega⟩` → `walk[i]?`
conversions and the `hcov`/`hsteps` hypothesis-position changes apply).

**Option B (if Session 13 has limited budget)**: add templates for the
remaining 2 Classical.choose lemmas and a worked bridge for the
`Finset.sum_ite_eq'` simp fix at L87, L99 — extending the pattern of
S9/S10/S12.

---

## Session 2026-05-08 (Session 11) - Recipe File Build Verification

**Mode**: REVISIT (Sessions 7–10 prepared+extended the recipe; S11 verifies
the extended recipe builds end-to-end after S10 added an unbuilt template)

**Outcome**: ran `LEAN_BUILD_TIMEOUT=45m ./proofs/scripts/docker-build.sh
Proofs.KonigsbergOQ01OQ02Recipe`. Result: **build succeeded** (`Built
Proofs.KonigsbergOQ01OQ02Recipe (8.6s)`, 7743 jobs, ~5 min wall-clock).
Three non-fatal lint warnings (unused `hlen` × 2 and unused simp arg
`hne` × 1); intentionally NOT "fixed" since the Recipe file is meant to be
deleted post-Session-12 transcription, and `hlen` IS used in the main file
where it'll be transcribed.

**Significance**: this finishes the Sessions 9–10 recipe-validation arc.
Session 12 starts the in-place refactor with **two build-verified bijection
templates** (`closed_walk_balance'` cyclic + `open_walk_interior_balanced'`
linear) plus the build-verified bridge lemma `getElem?_eq_some_iff_of_lt`.
Zero remaining template-correctness risk; only mechanical-transcription
risk plus the `Finset.sum_ite_eq'` simp fix at L87/L99.

**No file edits** beyond the state.md/knowledge.md updates documenting this.

---

## Session 2026-05-08 (Session 10) - Recipe Extension: open_walk_interior_balanced'

**Mode**: REVISIT (Session 9 validated `closed_walk_balance'`; Session 10
adds a second worked template for the open-walk interior shape)
**Outcome**: extended `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` with a
fully worked-out generic `open_walk_interior_balanced'` template in the
`walk[i]? = some v` form, mirroring the broken main file's L517–559.

### Why Recipe-Extension Over In-Place Transcription

The Session 9 hand-off plan called for in-place transcription. On evaluation
this session, the in-place pass requires:
- ~50 sites changed across 6 lemmas + 2 defs + 3 theorems, in a single pass
  (per the standing rationale from Sessions 7–9 that a partial refactor
  leaves the file in worse shape due to mixed signatures across callers)
- A full Docker build at the end (~45+ minutes per current `.lake` symlink
  state)

Given a ~30 minute session window, this was infeasible. The pragmatic move
was to grow the validated-recipe library with a second worked template so
Session 11 (with proper time budget) has more confidence and fewer unknown
API surfaces when doing the in-place pass.

### What's Now in `KonigsbergOQ01OQ02Recipe.lean`

After this session, the recipe file contains three validated artifacts:

1. **Bridge lemma** `getElem?_eq_some_iff_of_lt` (Session 9):
   `l[i]? = some v ↔ l[i] = v` for `i < l.length`.

2. **Closed-walk template** `closed_walk_balance'` (Session 9):
   For closed walks (`walk[0]? = walk[n]?`), source-count of `v` equals
   target-count via cyclic bijection `i ↦ if i = 0 then n - 1 else i - 1`.
   Worked Maps-into / Injective / Surjective; surjectivity uses
   explicit `by_cases h : j = n - 1` (NOT `split_ifs <;> omega` — see
   Session 9 finding on omega's incomplete handling of nested conditional
   case-splits).

3. **Open-walk interior template** `open_walk_interior_balanced'` (Session 10):
   For open walks where neither endpoint is `v` (`walk[0]? ≠ some v` and
   `walk[n]? ≠ some v`), source-count of `v` equals target-count via
   linear bijection `i ↦ i - 1`. Endpoint contradictions extract
   `i ≥ 1` (source side) and `j + 1 < n` (target side) via
   `by_contra; push_neg; have : ... = 0 := by omega; exact hw0 (this ▸ _)`
   pattern — direct port from the broken main file's structure.

### Why `open_walk_interior_balanced'` Was the Right Second Template

Three open-walk lemmas exist in the broken main file:
- `open_walk_last_target_excess` (linear bijection on `T \ {n-1}` → S)
- `open_walk_first_source_excess` (linear bijection on `S \ {0}` → T)
- `open_walk_interior_balanced` (linear bijection on full filtered set,
  endpoint exclusions force the bijection well-defined)

`open_walk_interior_balanced` was chosen as the second template because:
- It's the **simplest** open-walk shape (no `Finset.erase` plumbing).
- It's the **most general** (used in the new Session 6
  `euler_path_implies_degree_balance` proof for the interior-vertex case).
- The `*_excess` lemmas combine its bijection structure with a
  `Finset.card_insert_of_not_mem` setup; once `open_walk_interior_balanced'`
  is validated, the `*_excess'` versions are mechanical extensions.

### What Session 11 Should Verify First

Before doing the in-place transcription, run:
```bash
./proofs/scripts/docker-build.sh Proofs.KonigsbergOQ01OQ02Recipe
```

Expected: builds clean. The proof was traced by hand against the broken
main file's structure, and uses the same API surface Session 9 validated.
Most likely failure (low risk): the `(hi0 ▸ hi_v)` motive-inference. If
that fails, replace with an explicit `subst hi0` followed by direct
`exact hw0 hi_v`.

### Files Modified This Session

- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (+~75 lines)
- `research/problems/konigsberg-oq-01-oq-02/state.md` (Session 10 entry)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this entry)
- `src/data/research/problems/konigsberg-oq-01-oq-02.json` (status nudge)

### What Did NOT Change

- `proofs/Proofs/KonigsbergOQ01OQ02.lean` — still build-broken. Session 11
  performs the in-place refactor with the now-3-template recipe library.
- `src/data/proofs/konigsberg-oq-01-oq-02/meta.json` — sorries/axiomCount
  unchanged (no main-file edits).

---

## Session 2026-05-08 (Session 9) - Recipe Validation File

**Mode**: REVISIT (Sessions 7+8 prepared recipe; this session validates it)
**Outcome**: created independently-buildable companion file
`proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` containing the bridge lemma
and worked `closed_walk_balance'` template, verified to compile under the
current Lean 4.26.0 + Mathlib.

### What I Did

- Created `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (~110 lines) with:
  1. `getElem?_eq_some_iff_of_lt` — the bridge lemma between `walk[i]?` and
     `walk[i]` (with bound). Confirms `List.getElem?_eq_getElem` and
     `Option.some_inj` are stable in current Mathlib API.
  2. `closed_walk_balance'` — fully worked-out generic version in the new
     `walk[i]? = some v` form (parametric over arbitrary `Type V` with
     `[DecidableEq V]`). Mirrors the structure of the broken
     `closed_walk_balance` at L128–172 of the main file.
- Ran 5 Docker builds iteratively, addressing each error:
  - Build 1: discovered `List.get?` is no longer in scope under v4.26.0.
    Switched recipe to `walk[i]?` bracket notation.
  - Build 4: bridge lemma and most of `closed_walk_balance'` compiled. The
    remaining issue was the `· bijection value = j` obligation: `split_ifs
    <;> omega` failed because nested if-then-else generated cases where
    omega could not resolve a hidden `j + 1 = 0` (impossible-in-ℕ) without
    explicit help.
  - Build 5: replaced `split_ifs <;> omega` with explicit
    `by_cases h : j = n - 1` + `simp [h]` (in the `j = n - 1` case) and
    `simp [h, Nat.succ_ne_zero]` (in the `j ≠ n - 1` case).
- Did NOT modify `KonigsbergOQ01OQ02.lean` (the broken main file) — kept
  the recipe-validation in a separate file so Session 10 has a working
  template to copy in-place.

### Key Findings

- **API drift confirmed**: `List.get?` was removed/hidden in current
  Lean 4.26.0; canonical Option-returning indexing is `walk[i]?` via
  the `GetElem?` type-class. Bridge lemma uses `List.getElem?_eq_getElem`
  (the modern equivalent of the deprecated `List.get?_eq_get`).
- **Bridge lemma compiles** under v4.26.0 Mathlib (verified in build 4).
- **Proof bodies port mechanically** from the original `walk.get ⟨_, _⟩`
  form to `walk[_]?` form: only signatures and `obtain` types change.
  The `rw [hidx, ← hclosed, ← h]` patterns work unchanged.
- **`split_ifs <;> omega` does NOT work** for the bijection-value-equals-j
  obligation under current Mathlib — split_ifs creates 4 sub-cases for
  nested if-then-else, and omega cannot derive contradictions from
  `j + 1 = 0` automatically (impossible-in-ℕ but omega doesn't see it
  via Decidable). Replace with explicit `by_cases` + targeted `simp` per
  the Session 9 fix.

### What Remains for Session 10

Apply the validated recipe in-place to `KonigsbergOQ01OQ02.lean`:
1. Copy the bridge lemma `get?_eq_some_iff_of_lt` to top of main file
   (or import the Recipe file once the main file builds).
2. Refactor the 6 bijection lemmas. `closed_walk_balance'` from this
   session is the direct template; the other 5 follow the same pattern.
3. Refactor the 2 definitions (`HasEulerianCircuit`, `HasEulerianPath`)
   to use `walk.get? i = some v` in their `∃!` predicates.
4. Refactor 3 consumer theorems
   (`eulerian_circuit_implies_balanced`,
   `euler_path_implies_degree_balance`, `maxTrail_closed`) to construct
   `walk.get? = _` from existing `head?`/`getLast?` hypotheses.
5. Apply the `Finset.sum_ite_eq'` simp fix at L87, L99 of main file.
6. Run Docker build of `Proofs.KonigsbergOQ01OQ02`.
7. Once build passes, delete `KonigsbergOQ01OQ02Recipe.lean` (no longer
   needed) and update meta.json (`sorries: 1`, axiomCount unchanged at 2).

After build repair, `remove_circuit_balanced` (the remaining sorry at L1105)
becomes the next research target. Plan unchanged from Session 5.

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02Recipe.lean` (new file, ~110 lines, 0 sorries, 0 axioms)
- `src/data/proofs/konigsberg-oq-01-oq-02/meta.json` (additionalFiles updated)
- `src/data/research/problems/konigsberg-oq-01-oq-02.json` (knowledge updated)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this entry)
- `research/problems/konigsberg-oq-01-oq-02/state.md` (Session 9 added)

### What Did NOT Change

- `proofs/Proofs/KonigsbergOQ01OQ02.lean` — left untouched (still build-broken).
  Session 10 will perform the in-place refactor using this session's validated
  recipe as the template.

---

## Session 2026-05-08 (Session 7) - Refactor Recipe for Build Blocker

**Mode**: REVISIT (Session 6 left build-blocker; recipe deliverable, no `.lean` edits)
**Outcome**: documented a concrete, mechanical refactor recipe so the next session
can repair the build in a focused pass.

### Strategy: Switch lambdas to `walk.get? i = some v`

Rationale: `walk.get? : List V → ℕ → Option V` is total (returns `none` for
out-of-bounds), so `fun i => walk.get? i = some v` needs no bound proof at
lambda elaboration time. This sidesteps the omega-failure entirely.

### Bridge lemma (add once near top of file)

```lean
private lemma get?_eq_some_iff_of_lt {l : List V} {i : ℕ} {v : V}
    (h : i < l.length) :
    l.get? i = some v ↔ l.get ⟨i, h⟩ = v := by
  rw [List.get?_eq_get h]; exact Option.some_inj
```

Use this lemma to convert between forms inside `card_bij` proofs whenever
the bound `i < walk.length` is available (which it always is when iterating
over `Finset.range n` with `walk.length = n + 1`).

### Worked example: `closed_walk_balance` after refactor

```lean
private lemma closed_walk_balance (walk : List V) (n : ℕ)
    (hlen : walk.length = n + 1)
    (hclosed : walk.get? 0 = walk.get? n)            -- changed from ⟨_, by omega⟩
    (v : V) :
    ((Finset.range n).filter fun i => walk.get? i = some v).card =
    ((Finset.range n).filter fun i => walk.get? (i + 1) = some v).card := by
  apply Finset.card_bij (fun i _ => if i = 0 then n - 1 else i - 1)
  · -- Maps into target filter
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_lt, hi_v⟩ := hi
    refine ⟨by split_ifs <;> omega, ?_⟩
    split_ifs with h
    · -- i = 0 ⇒ target position n-1, need walk.get? n = some v
      have heq : walk.get? (n - 1 + 1) = walk.get? n := by congr 1; omega
      rw [heq, ← hclosed]; rw [h] at hi_v; exact hi_v
    · -- i > 0 ⇒ target position i-1, need walk.get? i = some v
      have heq : walk.get? (i - 1 + 1) = walk.get? i := by congr 1; omega
      rw [heq]; exact hi_v
  · -- Injective
    intro i hi j hj heq
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    split_ifs at heq with h1 h2 <;> omega
  · -- Surjective: target position j ↦ preimage (j = n-1 ? 0 : j+1)
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hj_lt, hj_v⟩ := hj
    refine ⟨if j = n - 1 then 0 else j + 1, ⟨by split_ifs <;> omega, ?_⟩, ?_⟩
    · split_ifs with h
      · -- j = n-1 ⇒ preimage = 0, need walk.get? 0 = some v
        rw [hclosed]
        have heq : walk.get? (j + 1) = walk.get? n := by congr 1; omega
        rw [← heq]; exact hj_v
      · exact hj_v
    · split_ifs with h
      · simp [h]; omega
      · simp; omega
```

Note the only **structural** changes from the original:
1. The hypothesis `hclosed` and the filter predicates use `walk.get? _ = _`
   instead of `walk.get ⟨_, by omega⟩ = _`.
2. Inside the proof, `congr 1; omega` (a numeric equality on the index) does
   the lifting from `walk.get? (n - 1 + 1)` to `walk.get? n` (and similar).
   This is mechanically the same as the previous `walk.get ⟨n - 1 + 1, _⟩ =
   walk.get ⟨n, _⟩` version but without the proof-irrelevance ceremony.
3. No `Option` API beyond `congr 1` + `omega` is needed inside the `card_bij`
   arguments, because the index manipulations are still over plain naturals.

### Caller adjustments

For `eulerian_circuit_implies_balanced` (uses `closed_walk_balance` at L310),
adjust the `hclosed_eq` derivation (currently L291–306) to produce
`walk.get? 0 = walk.get? n` instead of `walk.get ⟨0, _⟩ = walk.get ⟨n, _⟩`.

```lean
have hclosed_eq : walk.get? 0 = walk.get? n := by
  -- head? = some (walk[0]) and getLast? = some (walk[n])
  cases walk with
  | nil => simp at hlen
  | cons a t =>
      have h_head : (a :: t).get? 0 = some a := rfl
      have h_get_n : (a :: t).get? n = (a :: t).getLast? := by
        rw [List.getLast?_eq_getLast (by intro; simp_all)]
        rw [List.get?_eq_get (by simp; omega)]
        simp [List.getLast_eq_getElem, List.get_eq_getElem]; congr 1; omega
      rw [h_head, h_get_n, ← hclosed]
      simp [List.head?_cons]
```

Then `closed_walk_balance walk n hlen hclosed_eq v` gives the `get?`-form
cardinality equality. To bridge back to the existing `walk_source_eq_outDegree`
result (which still uses `walk.get ⟨_, _⟩` form), apply
`Finset.filter_congr` with `get?_eq_some_iff_of_lt`:

```lean
have hsrc_form_bridge : ∀ i ∈ Finset.range n,
    (walk.get? i = some v) ↔ (walk.get ⟨i, by omega⟩ = v) := by
  intro i hi
  simp only [Finset.mem_range] at hi
  exact get?_eq_some_iff_of_lt (by omega)
```

…and use `Finset.filter_congr hsrc_form_bridge` to swap the predicate inside
the cardinality. **However**, ideally `walk_source_eq_outDegree` and
`walk_target_eq_inDegree` are themselves refactored to the `get?` form so no
bridge is needed at the call site. The pattern in the worked example above
applies verbatim to those two lemmas (signature change + minor proof body
adjustments).

### Sites to refactor (full list)

There are **18 lambda call-sites** plus **~30 hypothesis-position sites**.
Concrete site list (line numbers from current `KonigsbergOQ01OQ02.lean`):

**Lambda sites in `Finset.filter` (must be refactored)**:
- L132–133 (`closed_walk_balance` return type)
- L180 (`walk_source_eq_outDegree` return type)
- L233 (`walk_target_eq_inDegree` return type)
- L433–436, L476–479 (`open_walk_last_target_excess`,
  `open_walk_first_source_excess` return types and `set` declarations)
- L522–523 (`open_walk_interior_balanced` return type)
- L969–971 (`maxTrail_closed` proof body)
- L1169, L1173 (`euler_path_implies_degree_balance` proof body)

**Hypothesis-position sites (also refactor for consistency)**:
- L130 (`hclosed`), L143, L147, L163 (proof body of `closed_walk_balance`)
- L431, L432 (`hw0`, `hwn` in `open_walk_last_target_excess`)
- L474, L475 (`hw0`, `hwn` in `open_walk_first_source_excess`)
- L520, L521 (`hw0`, `hwn` in `open_walk_interior_balanced`)
- L1146, L1150 (`hget_head`, `hget_last` in `euler_path_implies_degree_balance`)
- L1178, L1184, L1192, L1194 (`hns`, `h0t`, `hv0`, `hvn` in same theorem)

**Definition sites (the `∃! i, ...` patterns)**:
- L117–118 (`HasEulerianCircuit` definition: existence `walk.get ⟨i, by omega⟩`)
- L120–121 (`HasEulerianCircuit` `hsteps` field)
- L177–179 (`walk_source_eq_outDegree` `hcov`/`hsteps` arguments)
- L230–232 (`walk_target_eq_inDegree` `hcov`/`hsteps` arguments)
- L283 (`hcov'` in `eulerian_circuit_implies_balanced`)
- L288 (`hsteps'` in `eulerian_circuit_implies_balanced`)
- L338–340 (`HasEulerianPath` definition)
- L1159–1160 (`hcov'` in `euler_path_implies_degree_balance`)
- L1164–1165 (`hsteps'` in `euler_path_implies_degree_balance`)

### Other build issue: `Finset.sum_ite_eq'` simp progress

A second issue at L87, L99 (handshaking lemmas): `simp only [Finset.sum_ite_eq',
Finset.mem_univ, if_true]` no longer makes progress because Mathlib changed the
rewrite. The fix is to swap to `Finset.sum_ite_eq_of_mem` or just unfold
manually:

```lean
-- Before (no longer fires):
simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

-- After (one of):
rw [Finset.sum_ite_eq' (Finset.univ) e.1 (fun _ => 1)]
simp [Finset.mem_univ]
-- or use Finset.sum_filter form directly
```

### Order of attack for next session

1. **Add bridge lemma** `get?_eq_some_iff_of_lt` near top of file.
2. **Refactor definitions** (`HasEulerianCircuit`, `HasEulerianPath`) to use
   `get?`. This is small (4 sites) but downstream proofs will also adapt.
3. **Refactor private bijection lemmas in order**:
   `closed_walk_balance` → `walk_source_eq_outDegree` → `walk_target_eq_inDegree`
   → `open_walk_*` (3 lemmas). Each is independent; each ~50 lines of mechanical
   change.
4. **Fix `simp` failure** at handshaking lemmas (L87, L99).
5. **Run `./proofs/scripts/docker-build.sh Proofs.KonigsbergOQ01OQ02`** (~45 min).
6. After build passes: revisit Session 6's `euler_path_implies_degree_balance`
   proof, then attack `remove_circuit_balanced` sorry.

### Stale PRs to be aware of

These PRs are open but were superseded by merged sessions 4–6 work — the
file diffs reference 233/848-line states that no longer match `main`:

- #15145 (handshaking lemmas, May 3) — handshaking already merged
- #15168 (handshaking again, May 3) — duplicate of #15145
- #15232 (Hierholzer infrastructure 8→0 sorries, May 3) — superseded by #16153,
  #16675, #16855

Recommend closing them as superseded.

### Files Modified (Session 7)

- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this file: added recipe)
- `research/problems/konigsberg-oq-01-oq-02/state.md` (Session 7 entry)

No `.lean` edits, no metadata count edits — recipe-only deliverable.

---

## Session 2026-05-08 (Session 6) - euler_path_implies_degree_balance + BUILD BLOCKER

**Mode**: REVISIT (continuing Sessions 2–5)
**Outcome**: research progress + build-blocker discovery. Wrote a proof of
`euler_path_implies_degree_balance`, but the file does NOT compile (pre-existing
issue). Sorries cannot be reduced 2→1 in metadata until the file builds.

### Build Blocker Details (discovered Session 6)

Running `./proofs/scripts/docker-build.sh Proofs.KonigsbergOQ01OQ02` against the
worktree (which is fast-forward of origin/main) yields ~80 errors:

- L87, L99: `simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]` made no
  progress — Mathlib renamed/changed `sum_ite_eq'` semantics.
- L118, L132, L133, L144, L148 etc. (~70 sites): `omega could not prove the goal`
  with counterexample like `b ≥ 0, a ≥ 0, a - b ≥ 0` where `a := ↑i, b := ↑walk.length`.
  Translation: omega is asked to prove `i < walk.length` for an unbound `i`, with
  no hypothesis tying i to walk.length. This pattern appears in every
  `walk.get ⟨i, by omega⟩` call inside a `Finset.filter` lambda.
- L168, L245, L304, L375, L454: `unsolved goals`, `No goals to be solved`,
  `failed to synthesize` — cascade failures from the upstream omega errors.

**Root cause**: in `Finset.filter (fun i => walk.get ⟨i, by omega⟩ = v) (Finset.range n)`,
when the lambda body is elaborated, only `i : ℕ` and the lemma's signature
parameters are in scope. The membership `i ∈ Finset.range n` (which would give
`i < n`) is NOT a hypothesis at this point, because `Finset.filter` uses a plain
`α → Prop` predicate. So omega cannot prove `i < walk.length` and fails.

PR #16675 (Session 5) was apparently auto-merged without successful build
verification — the deployer's auto-merge may have skipped the build for this
research PR.

### Session 6 Repair Plan (deferred)

Two viable refactoring approaches for the file to build:

(a) **Replace `walk.get ⟨i, by omega⟩ = v` with `walk.get? i = some v`** inside
    every filter predicate. `List.get? : List α → ℕ → Option α` returns none for
    out-of-bounds, no proof needed. The bijection arguments (Finset.card_bij)
    must then manipulate `Option V` values, which is more verbose but tractable.

(b) **Reformulate the predicates as `∃ h : i < walk.length, walk.get ⟨i, h⟩ = v`**.
    This embeds the bound in the predicate. Bijection proofs need adjustment but
    the existing structure largely carries over.

Both refactors touch ~30-50 call sites across the file. Substantial work; punted
to a future session.

### Session 6 Code Changes (logical content, build-pending)

- **Strengthened `HasEulerianPath`** to mirror `HasEulerianCircuit`: replaced the
  bare `∃` walk-coverage with `∃!`, and added `hsteps : ∀ i < walk.length-1,
  (walk[i], walk[i+1]) ∈ G.edges`. The strong form supplies the hypotheses
  required by `walk_source_eq_outDegree` / `walk_target_eq_inDegree`. The
  axiomatized iff `directed_euler_path_iff` automatically inherits the new
  HasEulerianPath shape — its `←` (sufficiency) direction now asserts a
  stronger conclusion, but it remains axiomatized via Hierholzer splicing.
- **Added `open_walk_interior_balanced`** (private lemma): for an open walk
  with `walk[0] ≠ v` and `walk[n] ≠ v`, source-count(v) = target-count(v)
  via bijection `i ↦ i - 1`. The endpoint hypotheses force
  `i = 0 ∉ source-positions` and `j = n - 1 ∉ target-positions`.
- **Wrote proof of `euler_path_implies_degree_balance`**: walk-position bijections
  (`walk_source_eq_outDegree`, `walk_target_eq_inDegree`) convert degree
  counts to position counts; then `open_walk_first_source_excess`,
  `open_walk_last_target_excess`, and `open_walk_interior_balanced` give
  the three required equalities (s, t, interior). When the file builds, this
  reduces sorry count 2 → 1.

### Key Findings

- `HasEulerianPath` had a `∃` coverage that was insufficient for the bijection
  argument; mirroring `HasEulerianCircuit`'s `∃!` formulation closed the gap
  cleanly. Existing helpers (`walk_source_eq_outDegree` etc.) were already
  written generically and required no change.
- The "interior balance" identity is structurally a third member of the
  open-walk balance trilogy (`first_source_excess`, `last_target_excess`,
  `interior_balanced`), each proved by a localized `Finset.card_bij`.
- Pattern: when proving `outDeg = inDeg + 1` style facts via walk positions,
  always use the existence of `walk[0] = head_vertex` and `walk[n] = last_vertex`
  to discharge the boundary cases inside `card_bij`.
- **Build-blocker pattern**: `walk.get ⟨i, by omega⟩` inside `Finset.filter` on
  `Finset.range n` requires omega to prove `i < walk.length` for unbounded `i`.
  omega cannot do this without an in-scope hypothesis — and Lambda body
  elaboration doesn't see Finset membership. This pattern was acceptable in
  earlier omega/Lean versions but fails in latest Mathlib 4.26. ALL files using
  this pattern will fail to build.

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02.lean` (1108 → 1202 lines, theorems/lemmas
  25 → 26; build does NOT pass — pre-existing API drift)
- `src/data/research/problems/konigsberg-oq-01-oq-02.json` (Session 6 notes,
  build blocker recorded; sorries kept at 2 because unverified)
- `src/data/proofs/konigsberg-oq-01-oq-02/meta.json` (lineCount/theoremCount
  updated to objective values; sorries kept at 2)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this file)
- `research/problems/konigsberg-oq-01-oq-02/state.md` (created)

### What Remains

- **Build repair** (new top-priority): refactor `walk.get ⟨i, by omega⟩` calls
  inside `Finset.filter` predicates throughout the file — see "Session 6 Repair
  Plan" above. After repair, Session 6's `euler_path_implies_degree_balance`
  proof should work and sorry count drops 2 → 1.
- **`remove_circuit_balanced`** (L~1101): the second remaining sorry. Plan
  unchanged from Session 5: define `circuitVisits`, apply `closed_walk_balance`,
  bridge to `(walkEdges C.walk).toFinset` cardinality (likely needs adding
  `edges_distinct` field on `DirectedCircuit`).
- **Two axioms** still hold the iff at full strength; their `→` (necessity)
  directions are now both proved (`eulerian_circuit_implies_balanced` and
  Session 6's `euler_path_implies_degree_balance`). The `←` (sufficiency)
  directions remain axiomatized pending Hierholzer circuit splicing
  (~300+ lines).

### Next Steps

1. **Build repair (highest priority)** — refactor `walk.get ⟨i, by omega⟩` patterns.
2. After build repair: revisit Session 6's `euler_path_implies_degree_balance`.
3. Then `remove_circuit_balanced` as the next session's target.
4. After all sorries closed: build the full Hierholzer recursion, replace both
   axioms with theorems.

---

## Session 2026-05-08 (Session 6) — earlier draft (superseded by build-blocker note above)

**Mode**: REVISIT (continuing Sessions 2–5)
**Outcome**: progress — wrote proof of `euler_path_implies_degree_balance` (build pending)

### What I Did

- **Strengthened `HasEulerianPath`** to mirror `HasEulerianCircuit`: replaced the
  bare `∃` walk-coverage with `∃!`, and added `hsteps : ∀ i < walk.length-1,
  (walk[i], walk[i+1]) ∈ G.edges`. The strong form supplies the hypotheses
  required by `walk_source_eq_outDegree` / `walk_target_eq_inDegree`. The
  axiomatized iff `directed_euler_path_iff` automatically inherits the new
  HasEulerianPath shape — its `←` (sufficiency) direction now asserts a
  stronger conclusion, but it remains axiomatized via Hierholzer splicing.
- **Added `open_walk_interior_balanced`** (private lemma): for an open walk
  with `walk[0] ≠ v` and `walk[n] ≠ v`, source-count(v) = target-count(v)
  via bijection `i ↦ i - 1`. The endpoint hypotheses force
  `i = 0 ∉ source-positions` and `j = n - 1 ∉ target-positions`.
- **Proved `euler_path_implies_degree_balance`**: walk-position bijections
  (`walk_source_eq_outDegree`, `walk_target_eq_inDegree`) convert degree
  counts to position counts; then `open_walk_first_source_excess`,
  `open_walk_last_target_excess`, and `open_walk_interior_balanced` give
  the three required equalities (s, t, interior).

### Key Findings

- `HasEulerianPath` had a `∃` coverage that was insufficient for the bijection
  argument; mirroring `HasEulerianCircuit`'s `∃!` formulation closed the gap
  cleanly. Existing helpers (`walk_source_eq_outDegree` etc.) were already
  written generically and required no change.
- The "interior balance" identity is structurally a third member of the
  open-walk balance trilogy (`first_source_excess`, `last_target_excess`,
  `interior_balanced`), each proved by a localized `Finset.card_bij`.
- Pattern: when proving `outDeg = inDeg + 1` style facts via walk positions,
  always use the existence of `walk[0] = head_vertex` and `walk[n] = last_vertex`
  to discharge the boundary cases inside `card_bij`.

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02.lean` (1108 → 1202 lines, sorries 2 → 1,
  theorems/lemmas 25 → 26)
- `src/data/research/problems/konigsberg-oq-01-oq-02.json`
- `src/data/proofs/konigsberg-oq-01-oq-02/meta.json`
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this file)
- `research/problems/konigsberg-oq-01-oq-02/state.md` (created)

### What Remains

- **`remove_circuit_balanced`** (L~1101): the only remaining sorry. Plan:
  1. Define `circuitVisits C v := #{i < C.walk.length-1 : C.walk[i] = v}`.
  2. Apply `closed_walk_balance` to `C.walk` to show
     `circuitVisits C v = #{i : C.walk[i+1] = v}`.
  3. Bridge to `(walkEdges C.walk).toFinset` cardinality. This step likely
     needs an `edges_distinct` field on `DirectedCircuit` (so that `toFinset`
     deduplicates trivially); `circuit_exists` produces a `DirectedCircuit`
     satisfying it (via `maxTrail_steps_distinct`).
  4. Conclude inDegree/outDegree of `G.removeEdgeSet (walkEdges C.walk).toFinset`
     decrease by the same amount at each vertex.
- **Two axioms** still hold the iff at full strength; their `→` (necessity)
  directions are now proved theorems (`eulerian_circuit_implies_balanced` and
  `euler_path_implies_degree_balance`). The `←` (sufficiency) directions
  remain axiomatized pending Hierholzer circuit splicing (~300+ lines).

### Next Steps

1. **`remove_circuit_balanced`** as the next session's target.
2. After it lands: build the full Hierholzer recursion (induct on |E|; splice
   the circuit-pair using `circuit_exists` + `remove_circuit_balanced`).
   Once Hierholzer recursion lands, both axioms can be replaced by theorems
   (closing the iff at full strength).

---

## Session 2026-05-07 (Session 5) - maxTrail_used_eq + maxTrail_last_exhausted

**Mode**: REVISIT (continuing Sessions 2–4)
**Outcome**: progress — 2 of 4 deferred sorries eliminated (4 → 2)

### What I Did

- Proved `maxTrail_used_eq` (L582 in updated file) by direct strong induction on E.card.
  - Recursive case: `maxTrail E v = v :: maxTrail (E.erase c) c.2` and
    `maxTrailRem E v = maxTrailRem (E.erase c) c.2`.
  - Used `Finset.ext` + IH at (E.erase c, c.2). Forward and backward directions both
    case-split on `x = c` (use step 0) vs `x ∈ E.erase c` (apply IH and shift index by 1).
  - Key fact: `c ∉ maxTrailRem (E.erase c) c.2` follows from `maxTrailRem_subset _ _ ⊆ E.erase c`
    and `Finset.not_mem_erase c E`.
- Proved `maxTrail_last_exhausted` (L687) by direct strong induction on E.card.
  - `last_v` of outer trail equals `last_v` of inner trail (since outer = v :: inner).
  - Case split: `e = c` produces step 0 = c; `e ∈ E.erase c` applies IH at (E.erase c, c.2)
    and shifts index by +1.
  - Base case (no outgoing edges from v): trail = [v], so e ∈ E with e.1 = v contradicts
    the empty-filter hypothesis.
- Updated meta `lineCount` 958 → 1107, `sorryCount` 4 → 2 in
  `src/data/research/problems/konigsberg-oq-01-oq-02.json`.

### Key Findings

- The `let last_v := ...` pattern in `maxTrail_last_exhausted` signature unfolds at use
  sites (`maxTrail_closed` consumer); proof terms work because `Fin n` proof-component is
  `Prop` and hence proof-irrelevant.
- `Prod.ext (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b` — direction matters: for `(v, c.2) = c`
  with `c = (c.1, c.2)`, use `Prod.ext hc_v.symm rfl` where `hc_v : c.1 = v`.
- `simp only [hmtail, List.length_cons]; omega` is the standard idiom for length goals
  after `hmtail : maxTrail E v = v :: inner`.
- `simp only [hmtail, List.get_cons_zero, List.get_cons_succ, hinner_start]` reduces
  trail-step expressions to plain `c` values via head/tail decomposition.

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02.lean` (958 → 1107 lines, sorries 4 → 2)
- `src/data/research/problems/konigsberg-oq-01-oq-02.json` (knowledge updated)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this session appended)

### What Remains

- **`remove_circuit_balanced` (L953)**: removing a directed circuit's edge set preserves
  IsEulerianBalanced. Proof outline: for each vertex v, the edges of C visit v the same
  number of times as a source (from `closed_walk_balance` applied to C.walk) and as a target,
  so inDegree/outDegree both decrease by the same amount. Needs Finset sdiff/filter
  distributivity API and a careful definition of "visits as source/target".
- **`euler_path_implies_degree_balance` (L1007)**: necessity for Eulerian paths. Strengthen
  `HasEulerianPath` with `ExistsUnique` coverage, then apply
  `open_walk_first_source_excess` + `open_walk_last_target_excess` (already proved) plus
  `closed_walk_balance` for interior vertices.
- The two remaining axioms (`directed_eulerian_iff`, `directed_euler_path_iff`) require
  Hierholzer circuit-splicing for the sufficiency directions.

### Next Steps

1. `remove_circuit_balanced`: define helper count `circuitVisits C v = #{i < C.length : C[i] = v}`,
   apply `closed_walk_balance` to `C.walk` to show `circuitVisits = #{i : C[i+1] = v}`.
   Then `outDegree (G.removeEdgeSet ...) v = outDegree G v - circuitVisits` and similarly for
   inDegree, with `IsEulerianBalanced G v` giving the conclusion.
2. Refactor `HasEulerianPath` to use `∃!` instead of `∃`, mirroring `HasEulerianCircuit`.
3. After both sorries are proved: only Hierholzer splicing remains for `directed_eulerian_iff`.

---

## Session 2026-05-03 (Session 3) - Hierholzer Infrastructure

**Mode**: FRESH (continued from Session 2)
**Outcome**: progress — added 478 lines of Hierholzer proof infrastructure, `maxTrail_closed` proved

### What I Did

- Added Part VII: HierholzerInfrastructure section (~478 lines) to KonigsbergOQ01OQ02.lean
- Proved `open_walk_last_target_excess` and `open_walk_first_source_excess` via Finset.card_bij
- Implemented `maxTrail E v` (noncomputable, terminates by Finset.card_erase_lt_of_mem)
- Proved `maxTrailRem_subset` and `maxTrailRem_last_no_out` by strong induction
- **Proved `maxTrail_closed`**: in a balanced digraph, every greedy maximal trail is a closed circuit
  (balance contradiction: if last ≠ start then outDegree + 1 ≤ outDegree, impossible)
- Proved `circuit_exists`: every non-empty balanced digraph contains a directed circuit
- Added `DirectedCircuit` structure, `remove_circuit_balanced` (1 sorry), `euler_path_implies_degree_balance` (1 sorry)
- Fixed malformed code from context compaction (removed incomplete `?_` placeholders)
- Created PR from `research/konigsberg-hierholzer` branch

### Key Findings

- `maxTrail` terminates via `Finset.card_erase_lt_of_mem` — erase one edge per step
- `maxTrailRem_last_no_out` proved by strong induction using `Nat.strong_rec_on`
- The balance contradiction in `maxTrail_closed` uses:
  1. `maxTrail_last_exhausted`: all outgoing edges of last vertex were used (sorried helper)
  2. `maxTrail_steps_distinct`: each edge used at most once (sorried helper)
  3. `open_walk_last_target_excess`: target-count = source-count + 1 at last vertex
  4. `h_tgt_le_in`: target positions inject into incoming edges
  5. Balance: inDegree = outDegree → contradiction
- `walk_source_eq_outDegree` and `walk_target_eq_inDegree` (from Session 2) are the bijection helpers

### Files Modified

- `proofs/Proofs/KonigsbergOQ01OQ02.lean` (390 → 867 lines, axioms still 2)
- `src/data/research/problems/konigsberg-oq-01-oq-02.json` (knowledge updated)
- `research/problems/konigsberg-oq-01-oq-02/knowledge.md` (this file created)

### What Remains

Sorried in this session (6 total):
- `maxTrail_used_eq`: E \ maxTrailRem = steps-as-edges set (induction on E.card)
- `maxTrail_last_exhausted`: follows from maxTrailRem_last_no_out + maxTrail_used_eq
- `maxTrail_steps_in_E`: each step uses an edge from E (induction on E.card)
- `maxTrail_steps_distinct`: no edge used twice (induction, edge erased at each step)
- `remove_circuit_balanced`: circuit balance sub-lemma (follows from closed_walk_balance)
- `euler_path_implies_degree_balance`: necessity for paths (needs pigeonhole + open-walk counting)

### Next Steps

1. Prove the 4 `maxTrail` inductive properties — each is ~30 lines of strong induction
2. Once those are done, `maxTrail_closed` + `circuit_exists` + `remove_circuit_balanced` give
   the main ingredients for Hierholzer's theorem (circuit splicing remains)
3. `euler_path_implies_degree_balance`: add `∃!` unique coverage to `HasEulerianPath` definition,
   then apply `open_walk_first_source_excess`/`open_walk_last_target_excess`

---

## Session 2026-05-03 (Session 2) - Implement handshaking lemma proofs

**Mode**: FRESH (continued from Session 1)
**Outcome**: progress — axiomCount 5→2, PR #15170

### What I Did

- Proved `sum_outDegree_eq_edgeCount` and `sum_inDegree_eq_edgeCount` via double-counting
- Added `closed_walk_balance`, `walk_source_eq_outDegree`, `walk_target_eq_inDegree` (bijection lemmas)
- Proved `eulerian_circuit_implies_balanced` (necessity) via walk-position bijection + closed walk rotation
- Updated meta.json: axiomCount 5→2 (was 3 after handshaking, then 2 after necessity)

### Key Findings

- Handshaking via `Finset.sum_comm`: expand |{e: e.1=v}| as ∑_e [e.1=v], swap sums, get ∑_e 1 = |E|
- Necessity: `ExistsUnique` uniqueness + `Finset.card_bij` + closed walk rotation bijection
- `sum_ite_eq` vs `sum_ite_eq'` distinction: condition form determines which variant
