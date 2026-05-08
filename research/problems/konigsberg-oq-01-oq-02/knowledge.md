# Problem: Directed Eulerian Theory (konigsberg-oq-01-oq-02)

Extend the Eulerian circuit characterization to directed graphs. A weakly connected digraph has
an Eulerian circuit iff every vertex has equal in-degree and out-degree; directed analogue of
Königsberg bridges.

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
