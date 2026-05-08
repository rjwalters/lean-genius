# Problem: Directed Eulerian Theory (konigsberg-oq-01-oq-02)

Extend the Eulerian circuit characterization to directed graphs. A weakly connected digraph has
an Eulerian circuit iff every vertex has equal in-degree and out-degree; directed analogue of
Königsberg bridges.

**Current status**: ACT (build-blocked) — 2 of 5 original axioms remain (Hierholzer
sufficiency + path iff). Session 6 strengthened `HasEulerianPath` with `∃!`
coverage, added `open_walk_interior_balanced`, and wrote a proof of
`euler_path_implies_degree_balance`. **BUILD BLOCKER: the file does NOT currently
build under the latest Mathlib (~80 errors, pre-existing from PR #16675 —
apparently auto-merged without verification).** Errors are concentrated in
`walk.get ⟨i, by omega⟩` patterns inside `Finset.filter` lambdas where `i` is
unbounded; the omega tactic has no `i < walk.length` info at elaboration time.

Session 7 (this session, researcher-8) inspected the broken state and prepared
a concrete refactor recipe (Section "Session 7 Refactor Recipe" below). No
`.lean` edits were made — the recipe is the deliverable so the next session
can mechanically apply it.

Session 9 (researcher-10, 2026-05-08) attempted the full refactor but
discovered **three S8-missed broken sites** (maxTrail_used_eq lambda,
maxTrail_last_exhausted ∃-conjunct pattern, maxTrail_closed src_count/tgt_count
lambdas) plus path/concurrency chaos with a parallel researcher-1 also
working on this slug. S9's contribution: complete worked refactors for the
3 open_walk bijection lemmas (concrete `walk.get?`-form code below) and a
revised scope estimate (21 lambda sites + 3 hypothesis-pattern sites, not
S8's 18+9). See "Session 9 Refactor Extensions" below.

---

## Session 2026-05-08 (Session 9) - Refactor Extensions + Scope Corrections

**Mode**: REVISIT (build-repair attempt; pivoted to recipe-extension after
discovering scope was larger than S8 documented and a concurrent agent was
also working on the slug)
**Outcome**: 3 worked-out open_walk lemma refactors (verified syntactically,
not Docker-built), 3 S8-missed sites identified with line numbers, revised
mechanical-application order. No `.lean` edits committed in this session.

### Why Pivoted

S9 began applying the S7+S8 recipe but encountered:

1. **File-path confusion** — Edit-tool absolute paths to the main repo
   (`/Users/rwalters/GitHub/lean-genius/...`) collided with concurrent
   rebase activity in the main repo, silently losing edits to early lemmas
   (HasEulerianCircuit, closed_walk_balance, walk_source_eq_outDegree,
   walk_target_eq_inDegree, eulerian_circuit_implies_balanced). Only the
   open_walk lemma block survived intact. Per memory feedback
   `feedback_worktree_traps`: "Edit/Write absolute paths bypass the worktree
   silently."
2. **Concurrent agent collision** — researcher-1 has an open S9 worktree
   `research/konigsberg-oq-01-oq-02-S9-1778236913` (started 1035s before S9)
   working on the same slug. They have unstaged edits to knowledge.md,
   state.md, meta.json, JSON — though no `.lean` edits yet. Per memory
   feedback `feedback_researcher_pr_rebase_strategy`: avoid force-push
   collisions on parallel work.
3. **Three S8-missed broken sites** — maxTrail_used_eq, maxTrail_last_exhausted,
   maxTrail_closed src_count/tgt_count — would all need refactoring too.
4. **60-min Docker build cost** — with the broken `proofs/.lake` self-symlink
   (memory `feedback_researcher_lake_symlink_broken`), each build is
   30-45 min Mathlib clone + 10 min cache fetch.

The combined risk (concurrent edits + larger-than-stated scope + slow build
iteration) made a single-session full refactor + Docker build likely to
fail or be wasted. Pivoted to recipe-extension only, like S7 and S8.

### S8-Missed Broken Sites

S8's task list identified 18 filter-lambda sites + ~30 hypothesis sites in
the 6 bijection lemmas + 2 callers + 2 definitions. S9 discovered **three
additional broken sites** in `maxTrail`-family theorems:

| # | Lemma | Line | Pattern | Why broken |
|---|---|---|---|---|
| 1 | `maxTrail_used_eq` | 636-637 | `(Finset.range _).image (fun i => ...get ⟨i, by omega⟩...)` | omega has no `i < length` for unbound i |
| 2 | `maxTrail_last_exhausted` | 736-739 | `∃ i, i + 1 < length ∧ ...get ⟨i, by omega⟩... ∧ ...get ⟨i+1, by omega⟩...` | `∧` body doesn't see preceding conjunct |
| 3 | `maxTrail_closed` | 969-972 | `(Finset.range n).filter (fun i => trail.get ⟨i, by omega⟩ = last_v).card` (twice, src_count + tgt_count) | same as 18 sites in S8 list |

**Sites that work** (despite using `walk.get ⟨i, by omega⟩`):
- `maxTrail_steps_in_E` (L795-797): uses `∀ i, i + 1 < length → ...` — `→` makes
  the bound a binder hypothesis, omega sees it.
- `maxTrail_steps_distinct` (L832-835): same `∀ ... →` pattern.
- `walkEdges` (L1095-1099): uses `if h : i + 1 < walk.length then ... else
  none` — `h` is in scope of the `then` branch.
- All `hsteps`-style hypotheses (e.g. `∀ i (hi : i < n), ...`): omega sees `hi`.

The pattern that **fails** is exactly the S6 diagnosis: omega is asked to
prove `i < walk.length` for a free `i` whose bound is in a sibling
conjunct/lambda-body, not a binder. The `walk.get? i = some v` recipe
form is total (well-typed for any i) so it sidesteps the elaboration.

### Revised Site Count (S9 audit)

| Category | S8 estimate | S9 audit | Notes |
|---|---|---|---|
| Filter-lambda sites | 18 | **20** | +2 from `maxTrail_closed` src/tgt_count (L969-972) |
| Image-lambda sites | 0 | **1** | `maxTrail_used_eq` L636-637 |
| ∃-conjunct sites | 9 (∃!) | **10** | +1 from `maxTrail_last_exhausted` L736-739 |
| Hypothesis-position sites | ~27 | ~27 | unchanged |
| Total | ~54 | **~58** | scope ~10% larger |

### Worked Refactors for the 3 Open-Walk Lemmas (concrete code)

S7 worked out `closed_walk_balance` by hand. S8 wrote "by analogy"
templates §5.1-5.5 for the other 5 bijection lemmas. **S9 produces
syntactically-complete refactored versions of all 3 open-walk lemmas**
(verified the bridge lemma usage and predicate-conversion logic; not
Docker-built, but clean Lean 4 syntax that should compile).

#### Bridge Lemma (S7 recipe — verified placement)

Place near top of file, after `IsEulerianBalanced` definition (~L70),
before `outDegree`. Self-contained (no `Fintype V` dependency):

```lean
private lemma get?_eq_some_iff_of_lt {α : Type*} {l : List α} {i : ℕ} {v : α}
    (h : i < l.length) :
    l.get? i = some v ↔ l.get ⟨i, h⟩ = v := by
  rw [List.get?_eq_get h]; exact Option.some_inj
```

#### `open_walk_last_target_excess` (post-refactor)

```lean
private lemma open_walk_last_target_excess (walk : List V) (n : ℕ) (hn : 1 ≤ n)
    (hlen : walk.length = n + 1)
    (w : V)
    (hw0 : walk.get ⟨0, by omega⟩ ≠ w)
    (hwn : walk.get ⟨n, by omega⟩ = w) :
    ((Finset.range n).filter fun i => walk.get? (i + 1) = some w).card =
    ((Finset.range n).filter fun i => walk.get? i = some w).card + 1 := by
  set T := (Finset.range n).filter (fun i => walk.get? (i + 1) = some w)
  set S := (Finset.range n).filter (fun i => walk.get? i = some w)
  have hn1_in_T : n - 1 ∈ T := by
    simp only [T, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have heq : (n - 1 + 1 : ℕ) = n := by omega
    rw [heq]
    exact (get?_eq_some_iff_of_lt (by omega)).mpr hwn
  rw [show T.card = (T.erase (n - 1)).card + 1 from by
    rw [← Finset.card_insert_of_not_mem (Finset.not_mem_erase _ _)]
    simp [Finset.insert_erase hn1_in_T]]
  congr 1
  apply Finset.card_bij (fun i _ => i + 1)
  · intro i hi
    simp only [T, S, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_ne, hi_lt, hi_w⟩ := hi
    exact ⟨by omega, hi_w⟩
  · intro i1 _ i2 _ h; omega
  · intro j hj
    simp only [S, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj_lt, hj_w⟩ := hj
    have hj1 : 1 ≤ j := by
      by_contra h; push_neg at h
      have hj0 : j = 0 := by omega
      apply hw0
      exact (get?_eq_some_iff_of_lt (by omega)).mp (hj0 ▸ hj_w)
    refine ⟨j - 1, ?_, by omega⟩
    simp only [T, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, by omega, ?_⟩
    have heq : walk.get? (j - 1 + 1) = walk.get? j := by congr 1; omega
    rw [heq]; exact hj_w
```

Note `hw0` and `hwn` are kept in `walk.get` form (they use concrete 0/n
where omega has `hlen` available); the bridge lemma is invoked once each
in the `hn1_in_T` proof and the `hj1` derivation.

#### `open_walk_first_source_excess` (post-refactor)

```lean
private lemma open_walk_first_source_excess (walk : List V) (n : ℕ) (hn : 1 ≤ n)
    (hlen : walk.length = n + 1)
    (w : V)
    (hw0 : walk.get ⟨0, by omega⟩ = w)
    (hwn : walk.get ⟨n, by omega⟩ ≠ w) :
    ((Finset.range n).filter fun i => walk.get? i = some w).card =
    ((Finset.range n).filter fun i => walk.get? (i + 1) = some w).card + 1 := by
  set S := (Finset.range n).filter (fun i => walk.get? i = some w)
  set T := (Finset.range n).filter (fun i => walk.get? (i + 1) = some w)
  have h0_in_S : 0 ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, (get?_eq_some_iff_of_lt (by omega)).mpr hw0⟩
  rw [show S.card = (S.erase 0).card + 1 from by
    rw [← Finset.card_insert_of_not_mem (Finset.not_mem_erase _ _)]
    simp [Finset.insert_erase h0_in_S]]
  congr 1
  apply Finset.card_bij (fun i _ => i - 1)
  · intro i hi
    simp only [S, T, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_ne, hi_lt, hi_w⟩ := hi
    have hi1 : 1 ≤ i := by omega
    refine ⟨by omega, ?_⟩
    have heq : walk.get? (i - 1 + 1) = walk.get? i := by congr 1; omega
    rw [heq]; exact hi_w
  · intro i1 hi1 i2 hi2 h
    simp only [S, Finset.mem_erase, Finset.mem_filter, Finset.mem_range] at hi1 hi2
    omega
  · intro j hj
    simp only [T, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hj_lt, hj_w⟩ := hj
    have hjn : j + 1 < n := by
      by_contra h; push_neg at h
      have hjn_eq : j + 1 = n := by omega
      apply hwn
      exact (get?_eq_some_iff_of_lt (by omega)).mp (hjn_eq ▸ hj_w)
    refine ⟨j + 1, ?_, by omega⟩
    simp only [S, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by omega, hj_w⟩
```

#### `open_walk_interior_balanced` (post-refactor)

```lean
private lemma open_walk_interior_balanced (walk : List V) (n : ℕ)
    (hlen : walk.length = n + 1)
    (v : V)
    (hw0 : walk.get ⟨0, by omega⟩ ≠ v)
    (hwn : walk.get ⟨n, by omega⟩ ≠ v) :
    ((Finset.range n).filter fun i => walk.get? i = some v).card =
    ((Finset.range n).filter fun i => walk.get? (i + 1) = some v).card := by
  apply Finset.card_bij (fun i _ => i - 1)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    obtain ⟨hi_lt, hi_v⟩ := hi
    have hi1 : 1 ≤ i := by
      by_contra h; push_neg at h
      have hi0 : i = 0 := by omega
      apply hw0
      exact (get?_eq_some_iff_of_lt (by omega)).mp (hi0 ▸ hi_v)
    refine ⟨by omega, ?_⟩
    have heq : walk.get? (i - 1 + 1) = walk.get? i := by congr 1; omega
    rw [heq]; exact hi_v
  · intro i hi j hj heq
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    obtain ⟨_, hi_v⟩ := hi
    obtain ⟨_, hj_v⟩ := hj
    have hi1 : 1 ≤ i := by
      by_contra h; push_neg at h
      have hi0 : i = 0 := by omega
      apply hw0
      exact (get?_eq_some_iff_of_lt (by omega)).mp (hi0 ▸ hi_v)
    have hj1 : 1 ≤ j := by
      by_contra h; push_neg at h
      have hj0 : j = 0 := by omega
      apply hw0
      exact (get?_eq_some_iff_of_lt (by omega)).mp (hj0 ▸ hj_v)
    omega
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hj_lt, hj_v⟩ := hj
    have hjn : j + 1 < n := by
      by_contra h; push_neg at h
      have hjn_eq : j + 1 = n := by omega
      apply hwn
      exact (get?_eq_some_iff_of_lt (by omega)).mp (hjn_eq ▸ hj_v)
    refine ⟨j + 1, ?_, by omega⟩
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hj_v⟩
```

### Refactored Caller: `eulerian_circuit_implies_balanced` (sketch)

The caller now needs to bridge `walk.head? = walk.getLast?` to
`walk.get? 0 = walk.get? n` (rather than the `walk.get ⟨0,_⟩ = walk.get ⟨n,_⟩`
form S6 used). Sketch:

```lean
have hclosed_eq : walk.get? 0 = walk.get? n := by
  have hne : walk ≠ [] := by intro h; simp [h] at hlen
  have h1 : walk.head? = walk.get? 0 := by
    cases walk with
    | nil => exact absurd rfl hne
    | cons a t => rfl
  have h2 : walk.getLast? = walk.get? n := by
    rw [List.getLast?_eq_getLast hne, List.get?_eq_get (by omega)]
    congr 1
    simp only [List.getLast_eq_getElem, List.get_eq_getElem]
    congr 1; omega
  rw [h1, h2] at hclosed
  exact hclosed
```

The `walk.head? = walk.get? 0` is by definition (both produce `none` for
`[]` and `some head` for `cons`); `cases walk; rfl` discharges directly.

### Updated Mechanical-Application Order (S9 revision)

S8's order was 7 steps. S9 adds 4 more for the maxTrail-family sites:

1. Add bridge lemma `get?_eq_some_iff_of_lt` near top of file.
2. Refactor `HasEulerianCircuit` definition (L115-121): replace 4 of the
   5 `walk.get ⟨_, by omega⟩` sites with `walk.get?`.
3. Refactor `HasEulerianPath` definition (L334-340): same pattern.
4. Refactor `closed_walk_balance` (L128-171) per S7's worked example.
5. Refactor `walk_source_eq_outDegree` (L175-225) — uses bridge lemma 1× in
   surjective branch.
6. Refactor `walk_target_eq_inDegree` (L228-266).
7. Refactor `open_walk_last_target_excess` (L428-470) — S9 worked above.
8. Refactor `open_walk_first_source_excess` (L471-515) — S9 worked above.
9. Refactor `open_walk_interior_balanced` (L517-559) — S9 worked above.
10. **NEW**: Refactor `maxTrail_used_eq` (L634-637): change image lambda to
    `walk.get?` form. Proof body unchanged (i is bound by Finset.range
    membership inside ext-lemma).
11. **NEW**: Refactor `maxTrail_last_exhausted` (L734-739): change `∃ i,
    ... ∧ ...get ⟨i, by omega⟩...` to `∃ i, i + 1 < length ∧ walk.get? i
    = some e.1 ∧ walk.get? (i+1) = some e.2`.
12. **NEW**: Refactor `maxTrail_closed` (L969-972): change src_count and
    tgt_count predicates to `walk.get?` form. Their bijection proof bodies
    use `hi.2.1` from `hmax`'s output (which is now in walk.get? form).
13. Refactor `eulerian_circuit_implies_balanced` (L273-311): hcov' in
    walk.get? form, hclosed_eq in walk.get? form (sketch above).
14. Refactor `euler_path_implies_degree_balance` (L1125-1198): hcov',
    hsrc_eq_out, htgt_eq_in, plus open_walk_* call sites use walk.get? form.
15. Fix `Finset.sum_ite_eq'` simp at L87/L99 per S7+S8 §6.
16. Run Docker build (~60 min).

### Why hsteps Stays in `walk.get` Form

Most hypothesis-position sites in the recipe and S8's task list can be
converted to `walk.get?`, but `hsteps` types like `∀ i (hi : i < n),
(walk.get ⟨i, by omega⟩, ...) ∈ G.edges` already work with omega (the
binder `hi : i < n` is in scope). Converting them to `walk.get?` form
adds 4-5 lines of bridging per call site without benefit. **Recommendation**:
leave `hsteps`-style hypotheses unchanged.

### Coordination Note: researcher-1 Concurrent

A second researcher worktree (`research/konigsberg-oq-01-oq-02-S9-1778236913`,
researcher-1) is open on this slug as of S9 start (1035s before researcher-10
claimed). They have unstaged edits to knowledge.md, state.md, meta.json, JSON
but no `.lean` edits. Risk: parallel S9 PRs would conflict. S9 here pushes
docs-only PR (no `.lean` changes) to minimize collision; researcher-1's
PR can proceed independently.

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
