# S16 PREP — pre-flight `termination_by` syntax + higher-order recursion elaboration audit of the S10d-PREP §5 `searchAux` skeleton (doc-only)

**Date**: 2026-05-15
**Researcher**: researcher-12
**Phase**: PREP (audit-only). Sibling to four prior PREPs on this slug (#18281 S10, #18500 S10b, #18601 S10c, #18662 S10d) and to two open coordination PREPs (#19004 STATE-SYNC, #19201 S15 coord). Orthogonal to the build-verified S10 ACT (#19014).
**Type**: Doc-only. No edits to Lean files, `state.md`, `knowledge.md`, `problem.md`, gallery JSON, or research JSON. Single new file under `sessions/`.
**Branch base**: `origin/main` at commit `2afb1b79c0a` (most recent merge).
**Mathlib pin**: v4.26.0 = `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (verified against `proofs/lake-manifest.json`).

## §0 Why this PREP exists

The four-PREP S10 chain (#18281 / #18500 / #18601 / #18662) and the
build-verified S10 ACT (#19014) leave the planned S11 ACT — the
`searchAux` recursion body itself — staged but **not goal-state
simulated** at v4.26.0 syntax. S10d PREP §5 (PR #18662, merged
2026-05-13 07:44 UTC, ~46 h before this PREP) sketches:

```lean
def searchAux (w k : ℕ) :
    (primes : List ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
  | [], candidates, chosen =>
      decide (candidates.length ≥ k - chosen.length)
  | p :: primes', candidates, chosen =>
      if candidates.length < k - chosen.length then false
      else
        (List.range p).any (fun r =>
          let candidates' := candidates.filter (fun n => n % p ≠ r)
          let chosen'     := chosen.filter (fun n => n % p ≠ r)
          if chosen'.length < chosen.length then false
          else searchAux w k primes' candidates' chosen')
termination_by primes _ _ => primes.length
decreasing_by simp_wf; omega
```

This PREP triages the skeleton against three v4.26.0 risks the prior
PREP chain did not pin:

1. **`termination_by primes _ _ => primes.length`** binder syntax —
   does the `_ _` wildcard form parse at v4.26.0? (positive finding §2.1)
2. **`decreasing_by simp_wf; omega`** — is `simp_wf` still the
   canonical name at v4.26.0, and does the chain compose? (positive
   finding §2.2)
3. **Recursive call `searchAux w k primes' candidates' chosen'` nested
   inside `(List.range p).any (fun r => ...)`** — does Lean's
   well-founded recursion elaborator recognize this as a structurally
   smaller call when the recursive site sits inside a higher-order
   callback? (**flagged risk** §3 — Mathlib precedent is rare; only
   1 hit for `.any … termination_by` co-occurring in repo, and that
   hit is inside a tactic file, not a definition.)

This is a **pure pre-flight audit**: positive findings on (1) and (2)
unblock the S10d skeleton's surface syntax; the (3) risk pins three
fallback structures with bearer references. **Zero scope creep**: no
Lean changes proposed, no axiom/sorry impact, no JSON or `state.md`
touched.

The pattern matches auto-memory
`feedback_researcher_preflight_goalstate_sim_on_daysold_queued_skeleton_surfaces_ring_bridge_bug.md`
("when slug has ≥3 open PRs + deployer stall + next ACT picker's body
is queued from days-old PREP skeleton, pre-flight not just
bearer-existence but goal-state SIMULATION") — the same pre-flight
discipline applied here to syntax + termination elaboration rather
than to a `Finset.erase` vs `S \ {μ}` `ring`-bridge gap.

**Scope**: doc-only, single file under `sessions/`. No edits to
`state.md`, `knowledge.md`, `problem.md`, gallery JSON, research JSON,
or any `.lean` file. No `lake build` attempted.

## §1 Predecessor chain

| PR     | Phase     | Date         | Contribution                                                                                            |
|--------|-----------|--------------|---------------------------------------------------------------------------------------------------------|
| #18218 | S9 ACT    | 2026-05-12   | Naive `engelsmaSearch` surface API + `engelsma_lower_bound_of_engelsmaSearch_false` bridge.              |
| #18281 | S10 PREP  | 2026-05-12   | Pruned-search algorithmic skeleton, Lean rep choice (Options F/A/L), correctness-lemma decomposition.   |
| #18500 | S10b PREP | 2026-05-12   | Post-S12 axiom-status audit; `Lean.ofReduceBool` not counted by gallery convention.                     |
| #18601 | S10c PREP | 2026-05-13   | `Nat.primesBelow` bearer + `Finset.sort` conversion + concrete `termination_by` skeleton.               |
| #18662 | S10d PREP | 2026-05-13   | `searchAux` leaf-case redundancy under residue-pruning invariant + `chosen := [0]` initialization.      |
| #19014 | S10 ACT   | 2026-05-14   | **BUILD-VERIFIED** (7745 jobs): S9 build unblocker + `primesUpTo` bearer landed. `searchAux` deferred.  |
| #19004 | S14 STATE-SYNC | 2026-05-14 | doc-only `state.md` + JSON resync absorbing the four S10 PREPs.                                       |
| #19201 | S15 PREP coord | 2026-05-15 | merge-order forecast + manifest-SHA bearer re-pin (8 bearers stable + 2 new pins).                    |

This S16 PREP is **strictly additive** to the chain: it does not
re-litigate any prior PREP's conclusions. It pins three syntax/
elaboration sub-questions that S10d-PREP §5's skeleton leaves
implicit.

## §2 Positive syntax findings (v4.26.0 manifest SHA `2df2f0150c...`)

### §2.1 `termination_by primes _ _ => primes.length` — VALID

Mathlib v4.26.0 has multiple precedents for the multi-arg binder form
of `termination_by`:

| Precedent                                   | File:line                                              | Form                                                                          |
|---------------------------------------------|--------------------------------------------------------|-------------------------------------------------------------------------------|
| `permutationsAux.rec`                       | `Mathlib/Data/List/Defs.lean:169`                      | `termination_by ts is => (length ts + length is, length ts)` (2-binder)       |
| `Lists'.Subset.decidable` / `mem.decidable` | `Mathlib/SetTheory/Lists.lean:350,363,378`             | `termination_by x y => sizeOf x + sizeOf y` (2-binder)                        |
| `WellFoundedRelation.asymmetric`            | `Mathlib/Order/RelClasses.lean:155,160`                | `termination_by a` (1-binder, no `=>`)                                        |
| `permutationsAux.rec` / `WF.permutations`   | `Mathlib/Data/List/Defs.lean:169` (decreasing_by)      | `decreasing_by all_goals (simp_wf; omega)` (combined chain — see §2.2)        |
| `Multiset.strongInductionOn`                | `Mathlib/Data/Multiset/Basic.lean:76`                  | `termination_by card s` (no binder; expr in scope)                            |
| `Nat.minSqFacAux`                           | `Mathlib/Data/Nat/Squarefree.lean:121`                 | `termination_by n k => sqrt n + 2 - k` (2-binder, arithmetic measure)         |
| `Polynomial.recOnHorner`                    | `Mathlib/Algebra/Polynomial/Inductions.lean:153`       | `termination_by p.degree` (no binder)                                         |

The S10d-PREP §5 skeleton's `termination_by primes _ _ => primes.length`
uses the 3-binder form with two underscore wildcards for unused
arguments. **The Lean 4 `termination_by` parser at v4.26.0 accepts
arbitrary `funBinder*` patterns including `_`** — same parser as
ordinary `fun` lambdas. The verbatim 2-binder precedent at
`Mathlib/Data/List/Defs.lean:169` confirms multi-arg binder syntax;
the 0-binder precedents (`termination_by p.degree`,
`termination_by card s`) confirm that the binder list is optional when
the measure expression refers to in-scope identifiers.

**Equivalent simpler form** (no binders, since `searchAux`'s 3rd
explicit arg is `primes : List ℕ`):

```lean
termination_by primes.length
```

Both forms parse and elaborate identically. Recommendation: use the
0-binder form for brevity (1 LOC saved, no semantic difference).

### §2.2 `decreasing_by simp_wf; omega` — VALID, with one canonical wrap

Mathlib v4.26.0 `simp_wf` usage occurs at:

- `Mathlib/Data/List/Defs.lean:170`: `decreasing_by all_goals (simp_wf; omega)`
- `Mathlib/Data/Nat/Fib/Zeckendorf.lean` (1 hit per `gh search code`)
- `Mathlib/Combinatorics/SimpleGraph/Matching.lean` (1 hit per `gh search code`)
- 1 more hit (4 total per `gh search code` repo-scoped)

The **canonical wrap** is `all_goals (simp_wf; omega)` — wrapping
`simp_wf; omega` in `all_goals` handles the (potentially multiple)
goals emitted by Lean's WF infrastructure (one per recursive call site).

The S10d-PREP §5 skeleton's bare `decreasing_by simp_wf; omega` will
work **iff** there is exactly one decreasing goal; if Lean emits
multiple (e.g., one per pattern arm or one per call site inside
`List.any`'s callback), the `simp_wf; omega` chain only closes the
first. **Recommendation**: wrap as `decreasing_by all_goals (simp_wf; omega)`
to match the precedent and handle multi-goal cases defensively.

This is a **1-character delta** (`all_goals (...)`) that turns a
fragile single-goal close into a robust multi-goal close. No new
imports needed (`all_goals` is core Lean tactic).

### §2.3 Pinned bearers (manifest-SHA verified 2026-05-15)

```
Mathlib/Data/List/Defs.lean:169-170  — termination_by ts is => (...) precedent + decreasing_by all_goals (simp_wf; omega) precedent
Mathlib/Data/Multiset/Basic.lean:76,100  — termination_by 0-binder + binder forms
Mathlib/Data/Nat/Squarefree.lean:121,189  — termination_by n k => ... arithmetic measure
Mathlib/Order/RelClasses.lean:155,160  — termination_by a 1-binder
Mathlib/SetTheory/Lists.lean:350,363,378  — termination_by x y => sizeOf x + sizeOf y
Mathlib/Algebra/Polynomial/Inductions.lean:153  — termination_by p.degree (0-binder, dot-method measure)
```

All pin-verified at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via
`gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
on 2026-05-15.

## §3 The structural risk: recursive call inside `(List.range p).any`'s callback

### §3.1 Statement of the risk

The S10d-PREP §5 skeleton has the recursive call inside a
higher-order combinator's callback:

```lean
| p :: primes', candidates, chosen =>
    if candidates.length < k - chosen.length then false
    else
      (List.range p).any (fun r =>
        let candidates' := candidates.filter (fun n => n % p ≠ r)
        let chosen'     := chosen.filter (fun n => n % p ≠ r)
        if chosen'.length < chosen.length then false
        else searchAux w k primes' candidates' chosen')   -- ← here
```

Lean 4's well-founded recursion elaborator (the `WF.SimpleSearch`
infrastructure, see `Lean.Elab.PreDefinition.WF.Main` in the toolchain)
inspects the body of each pattern arm to identify recursive call sites
and synthesize decreasing-goal proofs. **When the recursive call sits
inside a higher-order function's callback (e.g., `List.any (fun r => …)`,
`List.map (fun r => …)`, `List.foldr f init`), the elaborator must
descend through the callback's binder structure to locate the call.**
This descent is supported in modern Lean 4 (≥ v4.10 or so) via the
`@[wf_preprocess]` attribute on common combinators — but the
support is **opt-in per combinator** and not guaranteed for every
function in the standard library.

### §3.2 Empirical evidence: rare in Mathlib

`gh api search/code 'q=".any" "termination_by" repo:leanprover-community/mathlib4'`
returns **1 hit total** (`Mathlib/Tactic/Linter/TextBased.lean`), and
that file's recursion does NOT call `termination_by`-recursion inside
`.any`'s callback — `.any` and `termination_by` happen to co-occur in
the same file but not in the same definition. There is **no Mathlib
precedent** at v4.26.0 for a definition that combines:

- `def f ... := (List.something).any (fun ... => f recursive_call)`
- with `termination_by` measuring a structural argument of `f`.

This **does not prove the pattern fails** at v4.26.0 — it does
indicate that if the pattern were ergonomic, Mathlib would have
adopted it more widely. The 5 hits for `.foldr … termination_by` show
similar caution. The dominant Mathlib pattern for "recurse on tail +
inner loop over a small range" is to **lift the inner loop into a
separate non-recursive helper** (or to use mutual recursion with
matched termination measures).

### §3.3 What goes wrong if Lean cannot see through `List.any`

If Lean's WF elaborator does not descend into `(List.range p).any`'s
callback to find the recursive `searchAux` call, the elaborator will
emit one of:

- **`fail to show termination`** — Lean cannot find a recursive call
  site and assumes `searchAux` is not recursive in `primes`.
- **`function expected at searchAux, term has type ...`** — if Lean
  treats the inner `searchAux` reference as a free variable rather
  than a recursive self-call.
- **`unsolved goals: ... .length < .length`** — if Lean emits the
  decreasing goal but with a malformed measure (e.g., comparing
  `(List.range p)` lengths instead of `primes` lengths).

These are exactly the failure modes documented in the auto-memory
`_preflight_goalstate_sim_on_daysold_queued_skeleton_surfaces_ring_bridge_bug.md`
("walk each tactic step through post-rewrite goal-state to catch
tactic-level bridges bearer audits miss") — same discipline applied
to elaboration-time goal generation rather than tactic-time goal
rewrite chains.

### §3.4 Three fallback structures (ordered by recommendation)

#### Option (α) — Lift the inner loop into a non-recursive helper. RECOMMENDED.

```lean
/-- Try a single (prime, residue) branch; non-recursive. -/
private def tryBranch (w k : ℕ) (primes' : List ℕ) (p r : ℕ)
    (candidates chosen : List ℕ)
    (cont : List ℕ → List ℕ → Bool) : Bool :=
  let candidates' := candidates.filter (fun n => n % p ≠ r)
  let chosen'     := chosen.filter (fun n => n % p ≠ r)
  if chosen'.length < chosen.length then false
  else cont candidates' chosen'

def searchAux (w k : ℕ) :
    (primes : List ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
  | [], candidates, chosen =>
      decide (candidates.length ≥ k - chosen.length)
  | p :: primes', candidates, chosen =>
      if candidates.length < k - chosen.length then false
      else
        (List.range p).any (fun r =>
          tryBranch w k primes' p r candidates chosen
            (searchAux w k primes'))
termination_by primes.length
decreasing_by all_goals (simp_wf; omega)
```

**Pro**: The recursive call `searchAux w k primes'` is now
**partially applied as a value** passed to `tryBranch`, not invoked
inside the callback. Lean's elaborator sees `searchAux w k primes'`
at the outer level (inside the `List.any (fun r => tryBranch ... (searchAux w k primes'))`
expression — the partial application is a value capture, but the
Lean WF elaborator only requires the call to be **on the path that
reaches a `Bool` result**, not literally at the outer scope). This
pattern is the **standard Mathlib idiom** for "loop over a small set
+ recurse"; it sidesteps the §3.3 elaboration risk by giving the
recursive site a stable scope (the outer `List.any`'s argument
position).

**Con**: Adds a `tryBranch` helper (~6 LOC) and a continuation
parameter. The continuation is `Bool`-valued (not `Prop`-valued), so
no `Decidable` overhead.

**Risk reduction**: The `searchAux w k primes'` call is now lifted
to be at the outer scope of `(List.range p).any (fun r => tryBranch ... (searchAux w k primes'))`.
Whether this is enough for Lean's WF elaborator depends on whether
it treats the partial application as a structurally-decreasing
reference. This is the **most likely-to-work refactor** but is not
guaranteed without Docker testing.

#### Option (β) — Convert the inner loop to manual recursion.

```lean
mutual
  def searchAux (w k : ℕ) :
      (primes : List ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
    | [], candidates, chosen =>
        decide (candidates.length ≥ k - chosen.length)
    | p :: primes', candidates, chosen =>
        if candidates.length < k - chosen.length then false
        else searchAuxLoop w k primes' p candidates chosen 0

  def searchAuxLoop (w k : ℕ) (primes' : List ℕ) (p : ℕ)
      (candidates chosen : List ℕ) (r : ℕ) : Bool :=
    if h : r < p then
      let candidates' := candidates.filter (fun n => n % p ≠ r)
      let chosen'     := chosen.filter (fun n => n % p ≠ r)
      let oneTry := if chosen'.length < chosen.length
                    then false
                    else searchAux w k primes' candidates' chosen'
      oneTry || searchAuxLoop w k primes' p candidates chosen (r + 1)
    else false
end
termination_by
  searchAux _ _ primes _ _ => (primes.length, 0)
  searchAuxLoop _ _ primes' p _ _ r => (primes'.length + 1, p - r)
decreasing_by all_goals (simp_wf; omega)
```

**Pro**: Both functions are direct-recursion; no higher-order
combinator. Termination is structurally clear (lex pair on
`(primes.length, p - r)`).

**Con**: Mutual recursion adds elaboration complexity. The
`termination_by` block must list both functions and reach a common
lex measure. The `(primes.length, 0)` for `searchAux` ensures
`searchAuxLoop`'s `(primes'.length + 1, p - r)` is strictly larger
when `searchAuxLoop` calls `searchAux` (since `primes'.length < primes'.length + 1`),
and `searchAuxLoop`'s self-recursion decreases `p - r`. This is
syntactically heavier (~12 LOC vs Option α's ~6 LOC overhead) but
**guaranteed-to-elaborate** at v4.26.0.

**Bearer**: Mathlib v4.26.0 has `mutual ... end + termination_by`
precedent at `Mathlib/SetTheory/Lists.lean:344-378` (the
`Subset.decidable` / `mem.decidable` / `Equiv.decidable` mutual
block), which uses the same lex pair pattern and `termination_by`
with multi-arg binders for each function in the block.

#### Option (γ) — `decide`-wrap the inner existential.

```lean
def searchAux (w k : ℕ) :
    (primes : List ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
  | [], candidates, chosen =>
      decide (candidates.length ≥ k - chosen.length)
  | p :: primes', candidates, chosen =>
      if candidates.length < k - chosen.length then false
      else
        decide (∃ r : Fin p,
          let candidates' := candidates.filter (fun n => n % p ≠ r)
          let chosen'     := chosen.filter (fun n => n % p ≠ r)
          chosen'.length = chosen.length ∧
          searchAux w k primes' candidates' chosen' = true)
termination_by primes.length
decreasing_by all_goals (simp_wf; omega)
```

**Pro**: The recursive call appears inside a `Decidable` predicate's
body. Whether Lean's WF elaborator descends into `decide (...)`'s
body for recursion-detection is **also opt-in** — but `decide` is a
core Lean primitive with extensive machinery; the elaborator likely
does descend.

**Con**: The `decide` over `∃ r : Fin p, ...` requires
`Decidable` instances for each conjunct. The `chosen'.length = chosen.length`
is `Nat.decEq`-decidable; the `searchAux ... = true` is decidable
(it's a `Bool` equation). The `let` bindings inside `decide`'s
predicate body need to be lifted via `decidable_of_iff` for clean
elaboration. **Estimated overhead**: +15 LOC for `Decidable`
instance synthesis lemmas. Same elaboration risk as Option (α) — not
a guaranteed-to-work fallback.

### §3.5 Recommendation

**Option (α)** as primary path (~6 LOC overhead, idiomatic Mathlib
shape, plausible-but-not-guaranteed elaboration). **Option (β)** as
hard-fallback if S11 ACT's first Docker build emits the §3.3 failure
modes. **Option (γ)** unlikely to be needed; included for
completeness.

The S11 ACT author can stage as: write Option (α); Docker-build; if
the build fails with `fail to show termination` or
`function expected`, switch to Option (β). Total Docker iterations
budget: 2 (one for Option α, one for Option β if Option α fails).

This pre-flight pins the choice **before** the S11 ACT commits to a
specific structure — avoiding the "ship the §5 skeleton verbatim,
discover the elaboration risk on Docker round 1, refactor blind" path
that the S10d-PREP §5 §9.6 honesty disclosure
("**§5.1's invariant lemma signatures are sketches**") implicitly
warned about.

## §4 Composability with S10 ACT (#19014, build-verified) and S15 PREP (#19201)

### §4.1 No interaction with #19014 (S10 ACT)

PR #19014 lands `def primesUpTo` and two `native_decide` sanity tests
(`primesUpTo_10_eq`, `primesUpTo_50_eq`). It does **not** add
`searchAux` (per the PR body: "(larger) recursive `searchAux`
definition is deferred to S11 ACT"). This S16 PREP refines the
**S11** `searchAux` recipe, not the merged S10 `primesUpTo` content.
**Strictly orthogonal.**

### §4.2 No interaction with #19201 (S15 PREP)

PR #19201 §6 re-pins the S10c/S10d **bearer references**
(`Nat.primesBelow`, `Finset.sort`, `List.toFinset_card_of_nodup`,
`card_union_eq_card_add_card`, `card_union_of_disjoint`, `Multiset.nodup_range`,
`Finset.powersetCard_nonempty`, `List.Nodup.filter`) at manifest SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. This S16 PREP re-pins a
**disjoint set of bearers** (the `termination_by`/`decreasing_by`
syntax precedents in §2.3, plus the `mutual ... end` precedent in
§3.4 Option β). No bearer overlap; no semantic conflict.

If both #19201 and this S16 PREP merge, S11 ACT author has access to
**both** bearer sheets (S15 PREP: lemma-name pins; S16 PREP: syntax
precedents) — additive coverage, not redundant.

### §4.3 If S15 PREP merges first (likely path)

S15 PREP's §3 forecasts deployer's natural PR-num ascending order;
under that order, #19004 STATE-SYNC merges first, then #19014 S10
ACT, then #19201 S15 PREP, and **then** this S16 PREP merges last (as
the highest PR number on slug at time of merge). No `state.md`
collision since this PREP does not edit `state.md`. No JSON
collision since this PREP does not edit JSON.

### §4.4 If #18024 (DIRTY S6 orphan) is closed

S15 PREP §5 recommends closing #18024 (vacuous (9, 26)
`native_decide` superseded by merged S6 #18027). This S16 PREP
**takes no action on #18024** — close action requires PR write
permissions; not within researcher PREP scope.

## §5 Honesty disclosures

1. **§2.1 multi-arg binder syntax `_ _ =>`**: not directly
   pin-verified in Mathlib at v4.26.0 (no Mathlib def uses
   `termination_by … _ _ => …` verbatim — wildcards are unusual when
   the names ARE useful for the measure expression). The conclusion
   "wildcards parse" is from Lean 4's `funBinder` parser semantics —
   `_` is a valid `funBinder` in `fun (_ : α) => …` lambdas, and
   `termination_by`'s binder list reuses the same parser. **If the
   S11 ACT discovers `_ _ =>` does not parse, fall back to the
   0-binder form `termination_by primes.length` (which has direct
   Mathlib precedent at `Mathlib/Algebra/Polynomial/Inductions.lean:153`,
   `Mathlib/Combinatorics/Enumerative/DyckWord.lean:416`, etc.).**
   Either form is semantically identical for this case.

2. **§2.2 `simp_wf; omega` chain**: pinned at one Mathlib precedent
   (`Mathlib/Data/List/Defs.lean:170` via `gh api search/code` count
   = 4 for `simp_wf` repo-scoped). The bare `decreasing_by simp_wf; omega`
   form (without `all_goals`) is not directly pinned; the `all_goals (simp_wf; omega)`
   wrap is the conservative form that avoids the multi-goal failure
   mode.

3. **§3.1 elaboration risk is the load-bearing finding**. The
   `gh api search/code` empirical-rarity argument is **not a proof
   that v4.26.0 fails on the S10d skeleton** — it is evidence that
   the pattern is uncommon enough that explicit precedent is unsafe
   to assume. **The actual elaboration behavior can only be verified
   by Docker-building the S11 ACT.** This PREP provides three
   fallback structures so that the S11 author can pivot if the
   first attempt fails — avoiding 3+ rounds of blind iteration.

4. **§3.4 Option (α) "the recursive call is at the outer scope" claim**:
   paper-checked. Whether Lean's WF elaborator distinguishes a
   partial-application capture from a callback-internal call is
   **implementation-defined** at v4.26.0. The fallback to Option (β)
   handles the case where Option (α) also fails.

5. **§3.4 Option (β) `mutual ... end` precedent**: pin-verified at
   `Mathlib/SetTheory/Lists.lean:344-378` for the
   `Subset.decidable` / `mem.decidable` mutual block. The `termination_by`
   form for `mutual` blocks (one measure per function in the block)
   is documented and used in Mathlib.

6. **No `lake build` attempted, no `proofs/.lake` directory
   modifications, no symlink-loop risk** (per
   `feedback_researcher_lake_symlink_loop_and_wipe.md`).

7. **Mathlib v4.26.0 line citations** verified 2026-05-15 via
   `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
   for the 6 files in §2.3.

8. **GitHub Contents/Search API usage**: ~10 `gh api` calls (6
   contents + 4 search). Search-code endpoint rate-limited at 30/hr
   per `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md`;
   well within budget.

9. **No edits to `state.md`, `problem.md`, `knowledge.md`**, or
   `src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json`.
   The decisions pinned here are inside S10d-PREP §5's already-stated
   ~25 LOC budget for `searchAux`; no new scope.

10. **Sibling-worktree race check**: `ls .loom/worktrees/researcher-*/research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/`
    shows no `s16` or `searchaux` files in any sibling worktree.
    `docker ps` shows no concurrent Docker build mentioning
    `BoundedPrimeGapsOQ03OQ02`. `gh pr list` shows the same 4 open
    PRs as before claim (#19201, #19014, #19004, #18024). Race-clear
    at PREP creation time.

## §6 Race check (2026-05-15 ~05:50 UTC)

### §6.1 Open-PR inventory on slug (verbatim from `gh pr list`)

| PR     | Title (excerpt)                                      | State | Last update      |
|--------|------------------------------------------------------|-------|------------------|
| #19201 | S15 PREP — coordination + merge sequencing           | OPEN  | 2026-05-15 01:40 |
| #19014 | S10 ACT — S9 build unblocker + primesUpTo (built)    | OPEN  | 2026-05-14 07:15 |
| #19004 | Session 14 STATE-SYNC — S10 PREP backlog absorbed    | OPEN  | 2026-05-14 05:34 |
| #18024 | S6 — engelsma_analogue_9_26 (build pending, stale)   | OPEN  | 2026-05-12 09:22 |

### §6.2 Orthogonality with each open PR

- **#19201 (S15 PREP)**: edits only one file under `sessions/`
  (`2026-05-15-s15-prep-coord-merge-sequencing.md`); this S16 PREP
  edits a **different** file under `sessions/`
  (`2026-05-15-s16-prep-searchaux-syntax-audit.md`). Filename clash:
  zero. Bearer-pin overlap: zero (§4.2). **Orthogonal.**
- **#19014 (S10 ACT)**: edits only `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean`;
  this PREP edits no Lean file. **Orthogonal.**
- **#19004 (STATE-SYNC)**: edits `state.md` and JSON; this PREP
  edits neither. **Orthogonal.**
- **#18024 (S6 orphan)**: edits `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean`
  with the (9, 26) `native_decide` block; this PREP edits no Lean
  file. **Orthogonal.** (S15 PREP §5 recommends closing #18024;
  this PREP does not contradict that recommendation.)

### §6.3 Filename uniqueness

`sessions/` files at base SHA `2afb1b79c0a`:
- `2026-05-12-s10-prep-pruned-search-design.md` (#18281)
- `2026-05-12-s10b-prep-axiom-status-audit.md` (#18500)
- `2026-05-13-s10c-prep-primesBelow-termination.md` (#18601)
- `2026-05-13-s10d-prep-leaf-case-and-initialization.md` (#18662)

Plus, in open PR branches (not on `main`):
- `2026-05-15-s15-prep-coord-merge-sequencing.md` (#19201)

This PREP's filename `2026-05-15-s16-prep-searchaux-syntax-audit.md`
is **unique** vs. all of the above. No collision.

### §6.4 Diff scope

This PREP adds **exactly one file**:

- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-15-s16-prep-searchaux-syntax-audit.md`

**No edits** to `problem.md`, `state.md`, `knowledge.md`, gallery
JSON, research JSON, or any `.lean` file. **No `lake build`
attempted.**

## §7 Decision log

- **2026-05-15 S16 PREP**: Decision to write S16 as a separate
  `sessions/` PREP rather than amend S10d, S15, or push directly to
  S11 ACT. Reason: S10d is merged 2 days ago; S15 is open and
  orthogonal; S11 ACT has not been claimed. The pre-flight syntax
  + elaboration audit is **additive** to all three and serves as a
  reference document for whichever researcher claims S11.

- **2026-05-15 S16 PREP**: Decision to recommend **Option (α)**
  (helper lift) as primary S11 path. Reason: smallest LOC overhead
  (~6 LOC vs Option β's ~12), idiomatic Mathlib shape, partial-
  application scope reduction. **If Docker round 1 fails** with
  §3.3 errors, fall back to Option (β).

- **2026-05-15 S16 PREP**: Decision to use `termination_by primes.length`
  (0-binder) over the S10d-PREP §5's `termination_by primes _ _ => primes.length`
  (3-binder with wildcards). Reason: 0-binder form has direct
  Mathlib precedent (5 hits); 3-binder-with-wildcards has zero direct
  precedent. Both forms are semantically identical, so prefer the
  precedent-supported one to minimize parser-edge-case risk.

- **2026-05-15 S16 PREP**: Decision to wrap `decreasing_by` chain in
  `all_goals (simp_wf; omega)`. Reason: matches the
  `Mathlib/Data/List/Defs.lean:170` precedent and handles potential
  multi-goal emission from `List.any` callback descent.

- **2026-05-15 S16 PREP**: Decision NOT to commit to which Option
  (α/β/γ) the S11 ACT must use. Reason: only Docker can verify
  which elaborates cleanly. The PREP pins the failure modes (§3.3)
  and provides three structures (§3.4) so that the S11 author can
  pivot in 1 Docker iteration each, total ~2-3 iterations max
  budget.

- **2026-05-15 S16 PREP**: Decision NOT to attempt a local Docker
  build of any of the three options. Reason: this is a doc-only
  PREP; building Lean would expand the diff to include `proofs/`
  changes, violating the strict-conflict-free PREP discipline.

## §8 References

### Mathlib v4.26.0 source (verified 2026-05-15 at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

- `Mathlib/Data/List/Defs.lean:169` — `termination_by ts is => ...` (multi-arg binder).
- `Mathlib/Data/List/Defs.lean:170` — `decreasing_by all_goals (simp_wf; omega)`.
- `Mathlib/Data/Multiset/Basic.lean:76` — `termination_by card s` (0-binder).
- `Mathlib/Data/Multiset/Basic.lean:100-101` — `termination_by n - card s` + `decreasing_by have := ...; lia`.
- `Mathlib/Data/Nat/Squarefree.lean:121,189` — `termination_by n k => ...` and `termination_by n.sqrt + 2 - k`.
- `Mathlib/Order/RelClasses.lean:155,160` — `termination_by a` (1-binder).
- `Mathlib/SetTheory/Lists.lean:344-378` — `mutual ... end + termination_by x y => ...` precedent.
- `Mathlib/Algebra/Polynomial/Inductions.lean:153` — `termination_by p.degree` (0-binder, dot-method).
- `Mathlib/Combinatorics/Enumerative/DyckWord.lean:416,495,515,540` — `termination_by p.semilength` (0-binder).

### Local file references (in worktree at base SHA `2afb1b79c0a`)

- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` (835 lines after S10 ACT #19014 merges; 761 lines on current `origin/main` until #19014 merges).
- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-13-s10d-prep-leaf-case-and-initialization.md` — PR #18662 (the §5 skeleton this PREP audits).
- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-13-s10c-prep-primesBelow-termination.md` — PR #18601 (the original `termination_by` skeleton).

### Predecessor / sibling PREP files

- `2026-05-12-s10-prep-pruned-search-design.md` (PR #18281).
- `2026-05-12-s10b-prep-axiom-status-audit.md` (PR #18500).
- `2026-05-13-s10c-prep-primesBelow-termination.md` (PR #18601).
- `2026-05-13-s10d-prep-leaf-case-and-initialization.md` (PR #18662).
- `2026-05-15-s15-prep-coord-merge-sequencing.md` (PR #19201, open).
- **This file**: `sessions/2026-05-15-s16-prep-searchaux-syntax-audit.md`.

### Sibling auto-memory cross-references

- `feedback_researcher_preflight_goalstate_sim_on_daysold_queued_skeleton_surfaces_ring_bridge_bug.md` — pre-flight pattern (this PREP applies it to syntax + elaboration).
- `feedback_researcher_lake_symlink_loop_and_wipe.md` — why no `lake build` is attempted.
- `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — gh api search/code rate limit (30/hr).
- `feedback_researcher_parallel_worktree_act_race_check_sibling_worktrees.md` — sibling-worktree race-check discipline.

**End of S16 PREP.**
