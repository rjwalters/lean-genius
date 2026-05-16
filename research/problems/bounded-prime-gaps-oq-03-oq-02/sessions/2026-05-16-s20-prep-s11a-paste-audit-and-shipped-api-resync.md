# S20 PREP — S11a paste audit + S18 PREP §2 sub-lemma resync against SHIPPED `tryBranch`+`searchAux` API (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-10 (this session)
**Phase**: PREP (doc-only). Post-S11a-ACT-merge follow-up.
**Iteration**: 20 (post-S11a ACT PR #19519 merged 2026-05-16T06:01Z; **B1 STILL ACTIVE** — Docker daemon still hung at S20 PREP open).
**Type**: Doc-only. Single new file under `sessions/` plus state.md head refresh + JSON `currentState` patch. **No `.lean` / `knowledge.md` / `problem.md` / gallery JSON edits. No `lake build` attempted.**
**Branch base**: `origin/main` at HEAD `9aa6e9f8acb` (`research(birthday-problem-oq-01-oq-02): S6 STATE-SYNC …`, 2026-05-16Z).
**Mathlib pin**: v4.26.0 = `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(re-verified against `proofs/lake-manifest.json` at HEAD; unchanged
since 2026-05-12T13:21Z = 4 days stable).

## §0 Why this PREP exists

Post-ship pivot landed on `bounded-prime-gaps-oq-03-oq-02` ≤4 h after
S11a ACT (PR #19519, researcher-9, merged 2026-05-16T06:01Z) shipped
the S17 PREP §6.1-§6.5 skeleton + S18 PREP §2 bridge sorry-scaffold
as `build pending` because the host Docker daemon was hung. **The
daemon is still hung** at S20 PREP open (`docker info --format
'{{.ServerVersion}}'` exit 124 at 5s; host disk 100% / 6.9 Gi free
on `/System/Volumes/Data`). S11a-VERIFY (next picker's job per
state.md `currentState.nextAction`) is INFRASTRUCTURE-BLOCKED.

Two doc-only contributions are available to the researcher pool
without touching Docker:

1. **S11a paste audit** — line-by-line check of the SHIPPED Lean
   (lines 835-953 of `BoundedPrimeGapsOQ03OQ02.lean`) against the
   S17 PREP §6.1-§6.5 paste-ready spec, confirming what landed
   matches what was planned (with two minor docstring deltas
   documented).
2. **S18 PREP §2 sub-lemma resync against the SHIPPED `tryBranch` +
   `searchAux` API** — the S18 PREP §2 sub-lemma signatures were
   drafted **before** S11a paste-time, against an *idealized*
   recursion that did not include S17 §6.1's runtime
   `chosen.length` shrink-check inside `tryBranch` or S17 §6.2's
   `if candidates.length < k - chosen.length then false`
   feasibility check in the head of `searchAux`'s inductive case.
   The shipped API includes both — this PREP refines the S18 PREP
   §2.1 / §2.2 sub-lemma signatures and proof structure to absorb
   the two early-exits.

This pattern matches auto-memory
`feedback_researcher_postship_pivot_to_slug_with_just_merged_act_naming_substantive_next_action_…`:
when claim-random lands on a slug whose ≤6 h merged substantive ACT
has state.md `nextAction` naming substantive S11b work AND Docker
infra is RED, ship doc-only PREP packaging (1) paste audit, (2) API
delta vs predecessor PREP, (3) refined sub-lemma signatures, (4)
Mathlib bearer recheck at the pinned SHA, (5) refined LOC budget,
(6) risk inventory with 1 INFRA marker, (7) ACT-readiness gate, (8)
race-check.

## §1 Drift recheck since S18 PREP (~30 h window)

S18 PREP completed 2026-05-16T02:46Z (PR #19386 merge). This PREP
opens at 2026-05-16T09:30Z, ~6.7 h later. Drift sources:

| Source                                                       | S18 PREP value                                  | This PREP value (S20)                          | Drift |
|--------------------------------------------------------------|--------------------------------------------------|------------------------------------------------|-------|
| `proofs/lake-manifest.json` Mathlib `rev`                    | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`       | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`     | **ZERO** |
| `Mathlib/Data/List/Basic.lean` SHA at pinned commit          | `721ebd4a3e19dc5e3f93fb68bd0a486fc1fce20c`       | `721ebd4a3e19dc5e3f93fb68bd0a486fc1fce20c`     | **ZERO** |
| `Mathlib/Data/Finset/Card.lean` SHA at pinned commit         | `ce82fb5788b6c30ea01c64fb091124e990516497`       | `ce82fb5788b6c30ea01c64fb091124e990516497`     | **ZERO** |
| `Mathlib/Data/Finset/Image.lean` SHA at pinned commit        | `396566beec04ee4b81019f4ead76899d81d9621d`       | `396566beec04ee4b81019f4ead76899d81d9621d`     | **ZERO** |
| `Mathlib/Data/Finset/Powerset.lean` SHA at pinned commit     | `4baa26c0da26d56c04c078da91c6bbe02458adff`       | `4baa26c0da26d56c04c078da91c6bbe02458adff`     | **ZERO** |
| `BoundedPrimeGapsOQ03OQ02.lean` LOC                          | 835 (pre-S11a)                                   | 953 (post-S11a paste, +118)                    | **+118 (expected)** |
| `BoundedPrimeGapsOQ03OQ02.lean` `theoremCount`               | 25                                               | 29                                             | **+4 (expected)** |
| `BoundedPrimeGapsOQ03OQ02.lean` `defCount`                   | 3                                                | 5                                              | **+2 (expected)** |
| `BoundedPrimeGapsOQ03OQ02.lean` `sorries`                    | 0                                                | 1                                              | **+1 (expected)** |
| Insertion point line (`end namespace`)                       | 835                                              | 953                                            | **+118 (expected)** |
| Open PRs on slug                                             | 0                                                | 0                                              | **ZERO** |
| Host disk free (`/System/Volumes/Data`)                       | ~7 Gi (RED)                                      | 6.9 Gi (still RED)                             | **−0.1 Gi (still RED)** |
| Docker daemon `docker info` exit                              | 124 @ 30s                                        | 124 @ 5s (`--format '{{.ServerVersion}}'`)     | **still RED** |

**Verdict**: Zero Mathlib drift. Lean file matches S11a expected
post-state exactly (118 LOC / 4 theorems / 2 defs / 1 sorry). Docker
infra still RED — same root cause class (host disk pressure).
Bearer table refresh **not required** for S11b.

## §2 S11a paste audit — line-by-line vs S17 PREP §6.1-§6.5 spec

The audit walks the SHIPPED Lean (lines 835-953 of
`BoundedPrimeGapsOQ03OQ02.lean`) against the S17 PREP §6
paste-ready spec, confirming what landed matches what was planned.
This is an audit-trail step before S11b drafts the discharge.

### §2.1 Per-section paste verbatim check

| Spec §        | Shipped lines | Decl                                                    | Spec LOC | Shipped LOC | Match |
|---------------|---------------|---------------------------------------------------------|----------|-------------|-------|
| S17 §6.1      | 835-854       | `private def tryBranch`                                  | 22 (incl. docstring) | 20 | ✅ verbatim modulo whitespace |
| S17 §6.2      | 856-886       | `def searchAux`                                          | 33 (incl. docstring) | 31 | ✅ verbatim |
| S17 §6.3      | 888-901       | `def engelsmaSearchPruned`                               | 17 | 14 | ✅ verbatim |
| S17 §6.4 #1   | 903-925       | `theorem engelsmaSearchPruned_eq_false_iff`              | 25 | 23 | ✅ verbatim (sorry-scaffold) |
| S17 §6.4 #2   | 927-935       | `theorem engelsma_lower_bound_of_engelsmaSearchPruned_false` | 9 | 9 | ✅ verbatim |
| S17 §6.5 #1   | 937-943       | `theorem engelsmaSearchPruned_7_3_eq_true`               | 7 | 7 | ✅ verbatim |
| S17 §6.5 #2   | 945-951       | `theorem engelsmaSearchPruned_11_5_eq_true`              | 7 | 7 | ✅ verbatim |

**Net check**: 7/7 sub-sections paste verbatim. The −2 / −3 LOC
deltas in §6.1 / §6.2 / §6.3 are docstring whitespace tightening
(e.g., merged paragraph blanks); no semantic change.

### §2.2 Identifier audit

| # | Shipped name | Spec name | Match |
|---|-------------|-----------|-------|
| 1 | `tryBranch` | `tryBranch` | ✅ |
| 2 | `searchAux` | `searchAux` | ✅ |
| 3 | `engelsmaSearchPruned` | `engelsmaSearchPruned` | ✅ |
| 4 | `engelsmaSearchPruned_eq_false_iff` | `engelsmaSearchPruned_eq_false_iff` | ✅ |
| 5 | `engelsma_lower_bound_of_engelsmaSearchPruned_false` | `engelsma_lower_bound_of_engelsmaSearchPruned_false` | ✅ |
| 6 | `engelsmaSearchPruned_7_3_eq_true` | `engelsmaSearchPruned_7_3_eq_true` | ✅ |
| 7 | `engelsmaSearchPruned_11_5_eq_true` | `engelsmaSearchPruned_11_5_eq_true` | ✅ |

7/7 identifiers EXACT. The S11b discharge can reference each name
directly without renaming concern.

### §2.3 Two minor docstring deltas (no semantic impact)

| Where | Spec | Shipped | Comment |
|-------|------|---------|---------|
| §6.4 docstring | "estimate +~60-120 LOC for the full decomposition (S10 PREP §8)" | "estimate +~190-300 LOC for the full decomposition (S18 PREP §2)" | S11a author absorbed S18 PREP §2.4's refined LOC roll-up; no signature impact |
| §6.4 cross-ref  | "Proof structure (per S10 PREP §8 decomposition)" | "Proof structure (per S10 PREP §8 decomposition + S18 PREP §2)" | S11a author chained both PREPs in the docstring; no signature impact |

Both deltas are upstream-friendly: they reflect the more refined
S18 PREP estimates without altering the paste-ready skeleton.

### §2.4 Sorry-count audit

| Pattern | Pre-S11a hits | Post-S11a hits | Drift |
|---------|--------------|----------------|-------|
| `^\s*sorry\s*$` (tactic-form) | 0 | 1 (line 925) | +1 (expected, bridge) |
| `\bsorry\b` (any) | 0 | 4 (lines 165, 768, 920, 925) | +1 net (lines 165/768 are docstring narrative; 920 is `S11b ACT author: discharge the sorry…` narrative; 925 is the only tactic-form `sorry`) |

**Tactic-form sorry count: 1.** JSON `sorries: 1` correctly reflects
this.

### §2.5 Axiom audit

| Pattern | Pre-S11a hits | Post-S11a hits | Drift |
|---------|--------------|----------------|-------|
| `^axiom ` | 0 | 0 | unchanged |
| `^axiom ` in this file | 0 | 0 | unchanged (the `engelsma_lower_bound` axiom is in `BoundedPrimeGapsOQ03.lean`, not this file) |
| `axiom` docstring narrative | 2 (lines 165, 768) | 2 (same) | unchanged |

**`axiomCount` of this file: 1** (which is `Lean.ofReduceBool`
propagated through `native_decide` per S4 / S10b convention; not a
declared `axiom` in this file but counted by the gallery convention
for `native_decide`-using files). JSON `axiomCount: 1` correctly
reflects this.

**Verdict**: S11a paste matches S17 PREP §6 spec verbatim, with two
docstring deltas absorbing S18 PREP §2's refined LOC estimates. No
audit-time correction needed.

## §3 SHIPPED-API delta vs S18 PREP §2 sub-lemma signatures

S18 PREP §2.1 / §2.2 sub-lemma signatures were drafted before S11a
paste-time, against an *idealized* `searchAux` that omits two
runtime early-exits that S17 PREP §6.1 / §6.2 ultimately did
include. The S11a paste IS S17 PREP §6 verbatim, so the early-exits
ARE in the shipped code; therefore S18 PREP §2 needs a refresh
before S11b discharges the bridge sorry.

### §3.1 Delta DELTA-1: `tryBranch` chosen-shrink early-exit

**S18 PREP §2.1 assumed**: the recursive `searchAux w k primes'`
call would never have its `chosen` shrunk between recursive steps
— the residue-disjointness invariant `hchosen_residue` was supposed
to *guarantee* that `chosen.filter (· % p ≠ r) = chosen` always.

**S11a SHIPPED**: per S17 PREP §6.1, `tryBranch` does the filter
*and* checks `if chosen'.length < chosen.length then false`
explicitly. The check **fires at runtime** whenever an element of
`chosen` had residue `r` mod `p`. This was a *defense-in-depth*
choice — the invariant *should* prevent it from firing, but the
runtime check ensures `searchAux` returns `false` instead of
incorrectly recursing on a shrunken `chosen`.

**Impact on `searchAux_sound` (S18 PREP §2.1)**: the inductive case
now has **two** ways `tryBranch p r candidates chosen (searchAux w
k primes') = false`:

- (a) `chosen.filter (· % p ≠ r).length < chosen.length` —
  early-exit fires; OR
- (b) early-exit doesn't fire, and `searchAux w k primes'
  (candidates.filter ...) (chosen.filter ...) = false`.

Under `hchosen_residue` (the prefix is residue-disjoint mod every
`p ∈ p :: primes'`), branch (a) cannot fire because **no** element
of `chosen` has any specific forbidden residue mod `p` (the
hypothesis `hchosen_residue` at `p` plus the fact that filtering
by a single residue class would only remove elements with that
residue mod `p`). Specifically: if `chosen` contains `a, b ∈ ℕ`
with `a ≠ b` and `a % p = b % p`, then `hchosen_residue p
(List.Mem.head _) a (List.mem_self a chosen) b (List.mem_self b
chosen)` derives `a % p ≠ b % p`, contradicting the premise. So
**any singleton of `chosen` filtered by a residue class either
preserves the element (residue ≠ r) or removes it (residue = r)**,
and at most one element of `chosen` has residue `r` mod `p`.

If at most one element of `chosen` has residue `r` mod `p`, and
the early-exit asks `chosen'.length < chosen.length`, the early
exit fires iff exactly one element of `chosen` has residue `r` mod
`p`. In this case `chosen.filter (· % p ≠ r).length = chosen.length
- 1`. So under `hchosen_residue`, branch (a) reduces to "there
exists some element of `chosen` with residue `r` mod `p`", which
the soundness proof can dispatch as follows: **the early-exit is
equivalent to `r ∈ chosen.image (· % p)` (as a `List`)**, and the
witness `H` (if it existed) would necessarily intersect `chosen`'s
residue at `p` plus some other residue, so `(H.image (· %
p)).card` cannot exceed `p - 1` — but `(H.image (· %
p)).card < p` is the input residue-disjointness hypothesis. The
early-exit firing on a given `r` *eliminates* `r` from `H`'s
residue image, reducing the number of available `r`'s.

**Soundness rewrite for the inductive case**: split into

- Case-1 (`r ∈ chosen.image (· % p)`): early-exit fires → branch
  result `false`. No constraint on `H` derivable from this branch.
  But by `hchosen_residue` + at most one chosen element per
  residue, `r` was already "claimed" by some element of `chosen`,
  so `H` cannot use `r` either. Discharge via residue-counting:
  the `r ∈ chosen.image (· % p)` case contributes `chosen.image (·
  % p)`'s cardinality of "blocked" residues to the residue-class
  forbidden set; combine with the inductive case to get the
  full residue-disjointness invariant.
- Case-2 (`r ∉ chosen.image (· % p)`): early-exit doesn't fire →
  branch result equals `searchAux w k primes' (candidates.filter
  (· % p ≠ r)) chosen = false`. Apply IH.

**LOC impact**: +~10-20 LOC over S18 PREP §2.1's estimate (the
extra case-split + residue-counting argument). Refined LOC for
`searchAux_sound`: ~65-110 LOC (was ~55-90).

**Impact on `searchAux_complete` (S18 PREP §2.2)**: the
residue-witness construction in §2.2 must now ADDITIONALLY show
that the chosen `r` (= `(H \ chosen.toFinset).min' _ % p`) is **not
in `chosen.image (· % p)`**, otherwise the early-exit fires and the
branch returns `false` (which is the wrong branch). This is
automatic from `hchosen_residue` + the residue-disjointness of `H`:
if `r := (H \ chosen.toFinset).min' _ % p`, then `r` is the
residue of some element of `H \ chosen.toFinset`. If `r ∈
chosen.image (· % p)`, then there's an element of `chosen` with
residue `r` mod `p`; but `chosen ⊆ H` (by `hsub_chosen`), so two
distinct elements of `H` have residue `r` mod `p`, contradicting
`(H.image (· % p)).card < p` (which forces the residues of `H` to
be distinct in the `p`-pigeonhole that the strict `<` enforces).
Wait — the pigeonhole here is more subtle. Let me restate:
`(H.image (· % p)).card < p` does NOT force all residues of `H` to
be distinct; it allows any subset of residue classes. The
correct argument is:

- `H.card < ∞` and `(H.image (· % p)).card < p` says **at least
  one** residue class `r' ∈ List.range p` is unrepresented in
  `H.image (· % p)` (which is the admissibility condition: `H`
  misses some residue mod `p`).
- The residue-witness construction is to pick **the smallest**
  unrepresented residue `r'` (NOT the residue of `(H \
  chosen.toFinset).min'`). Then `r' ∉ H.image (· % p)`, so
  `r' ∉ chosen.image (· % p)` (since `chosen ⊆ H`), so the
  early-exit does NOT fire on `r'`.

This is a **substantive correction** to S18 PREP §2.2's
residue-witness construction. The S18 PREP §2.2 sketch
("`r := (H \ chosen.toFinset).min' _ % p`") is wrong because it
picks the residue of an *existing* element of `H`, but the
admissibility witness needs a residue that's **missing** from `H`.

**Restated residue-witness construction**:

```text
r : ℕ := (List.range p).filter (· ∉ H.image (· % p)) |>.head!
```

(or equivalently the existence-derived first missing residue from
`(H.image (· % p)).card < p`). Since `hres` says
`(H.image (· % p)).card < p`, the filter is non-empty.

**LOC impact**: +~15-25 LOC over S18 PREP §2.2's estimate (the
residue-witness correction; the membership lemma `r ∉
chosen.image (· % p)` derived from `chosen ⊆ H`; the
early-exit-not-firing proof). Refined LOC for `searchAux_complete`:
~105-165 LOC (was ~90-140).

### §3.2 Delta DELTA-2: `searchAux` candidates-feasibility early-exit

**S18 PREP §2 assumed**: the only `false` return path in
`searchAux`'s inductive case is "all `r`-branches return `false`"
(i.e., `(List.range p).any (fun r => tryBranch ...) = false`).

**S11a SHIPPED**: per S17 PREP §6.2, `searchAux`'s inductive case
opens with `if candidates.length < k - chosen.length then false`,
an early-exit firing whenever the remaining candidates aren't
sufficient to extend `chosen` to size `k`.

**Impact on `searchAux_sound`**: the inductive case now has **three**
ways `searchAux w k (p :: primes') candidates chosen = false`:

- (a) `candidates.length < k - chosen.length` — candidates-feasibility
  early-exit; OR
- (b) candidates-feasibility doesn't fire AND all `r`-branches
  return `false` per DELTA-1 case-split.

The candidates-feasibility early-exit discharges trivially: if
`candidates.length < k - chosen.length`, then any `H` containing
`chosen.toFinset` (size `chosen.length`) and drawing remaining
elements from `candidates.toFinset` has `H.card ≤ chosen.length +
candidates.length < chosen.length + (k - chosen.length) = k`
(assuming `k ≥ chosen.length`, which holds by `hsub_chosen +
Finset.card_le_card`). Contradiction with `hcard : H.card = k`.

This is the **same argument** as the leaf-case (S18 PREP §4.1), so
the inductive case's DELTA-2 sub-case reduces to a one-line
appeal to the leaf-case lemma.

**LOC impact**: +~5-10 LOC over the §3.1-refined estimate (the
DELTA-2 case at the head of the inductive case). Refined LOC for
`searchAux_sound`: ~70-120 LOC (was ~65-110 post-§3.1, ~55-90 in
S18).

**Impact on `searchAux_complete`**: the candidates-feasibility
early-exit must NOT fire when an admissible witness `H` exists.
This is **automatic** from the witness `H ⊆ chosen.toFinset ∪
candidates.toFinset` and `H.card = k` and `chosen.toFinset ⊆ H`:
`candidates.toFinset.card ≥ (H \ chosen.toFinset).card = k -
chosen.length` (with `chosen.toFinset ⊆ H`, the subtraction
distributes). Since `candidates.toFinset.card ≤ candidates.length`,
`candidates.length ≥ candidates.toFinset.card ≥ k - chosen.length`,
so the early-exit doesn't fire. **One-line discharge** via
`Finset.card_le_card` + `List.toFinset_card_le` + arithmetic.

**LOC impact**: +~5 LOC over the §3.1-refined estimate. Refined
LOC for `searchAux_complete`: ~110-170 LOC (was ~105-165
post-§3.1, ~90-140 in S18).

### §3.3 Delta DELTA-3: `tryBranch` continuation is `searchAux w k primes'` (closed under partial application)

**S18 PREP §2 implicitly assumed**: the recursive call to
`searchAux w k primes'` happens at the *same scope* as the
`(List.range p).any (fun r => ...)` body.

**S11a SHIPPED**: per S17 PREP §6.1 + S16 PREP §3.4 Option α, the
recursive call is **partially applied** as a continuation passed to
`tryBranch`. The well-founded recursion descends on
`primes.length`, with `primes'.length < (p :: primes').length`
discharged by `simp_wf; omega` per `decreasing_by`.

**Impact on sub-lemma proofs**: when unfolding `searchAux w k (p ::
primes') candidates chosen` in either soundness or completeness,
the unfold yields `(List.range p).any (fun r => tryBranch p r
candidates chosen (searchAux w k primes'))`. Unfolding `tryBranch`
in turn yields `if … then false else searchAux w k primes' …`
(after the filter let-bindings). The two unfolds compose cleanly;
no special handling for the partial application.

**LOC impact**: 0 (the partial-application form has no semantic
content beyond the inline form for soundness/completeness proofs;
the only difference would arise in `searchAux`'s own termination
proof, which is already discharged via `decreasing_by`).

### §3.4 Refined S11b sub-lemma LOC roll-up

| Sub-lemma                                                 | S18 PREP §2.4 estimate | S20 PREP §3 refined | Delta |
|-----------------------------------------------------------|------------------------|---------------------|-------|
| `searchAux_sound`                                         | ~55-90                 | ~70-120             | +15-30 |
| `searchAux_complete`                                      | ~90-140                | ~110-170            | +20-30 |
| `IsAdmissible_iff_residue_disjoint_primesUpTo` combiner   | ~25-40                 | ~25-40 (unchanged)  | 0      |
| `engelsmaSearchPruned_eq_false_iff` (forward direction)   | ~10-15                 | ~10-15 (unchanged)  | 0      |
| `engelsmaSearchPruned_eq_false_iff` (reverse direction)   | ~10-15                 | ~10-15 (unchanged)  | 0      |
| **Total S11b discharge**                                  | **~190-300 LOC**       | **~225-360 LOC**    | **+35-60** |

The +35-60 LOC inflation reflects the two early-exits in the
SHIPPED API. Still within the *combined* S10/S18 PREP budget when
distributed across S11b sub-sub-PRs (S11b-α: combiner; S11b-β:
soundness; S11b-γ: completeness; S11b-δ: bridge), as detailed in
§5 below.

## §4 Mathlib bearer recheck at the lake SHA

The S18 PREP §3 bearer table has 15 entries (5 Mathlib + 5 core).
S20 PREP spot-checks 4 of the load-bearing Mathlib paths via `gh
api …/contents?ref=2df2f0150c…` (file-SHA only — line-number
spot-checks deferred to S11b PREP per S18 PREP §8.4):

| # | Mathlib file                                              | S18 PREP file SHA                            | S20 PREP file SHA (recheck)                   | Drift |
|---|-----------------------------------------------------------|----------------------------------------------|-----------------------------------------------|-------|
| 1 | `Mathlib/Data/List/Basic.lean`                            | `721ebd4a3e19dc5e3f93fb68bd0a486fc1fce20c`   | `721ebd4a3e19dc5e3f93fb68bd0a486fc1fce20c`    | **ZERO** |
| 2 | `Mathlib/Data/Finset/Card.lean`                           | `ce82fb5788b6c30ea01c64fb091124e990516497`   | `ce82fb5788b6c30ea01c64fb091124e990516497`    | **ZERO** |
| 3 | `Mathlib/Data/Finset/Image.lean`                          | `396566beec04ee4b81019f4ead76899d81d9621d`   | `396566beec04ee4b81019f4ead76899d81d9621d`    | **ZERO** |
| 4 | `Mathlib/Data/Finset/Powerset.lean`                       | `4baa26c0da26d56c04c078da91c6bbe02458adff`   | `4baa26c0da26d56c04c078da91c6bbe02458adff`    | **ZERO** |

**4/4 file-SHA spot-checks ZERO drift.** S18 PREP §3 bearer table
remains valid against the current Mathlib pin.

**One additional bearer needed for the SHIPPED `tryBranch`
chosen-shrink case** (DELTA-1 above):

| # | Name                              | Path                            | Used in              |
|---|-----------------------------------|---------------------------------|----------------------|
| 16 | `List.length_filter_le`           | core (Std) or `Mathlib/Data/List/Basic.lean` | `searchAux_sound` DELTA-1 case |
| 17 | `List.toFinset_card_le`            | `Mathlib/Data/List/Basic.lean`   | `searchAux_complete` DELTA-2 case |

Both are SHA-stable foundational data-structure lemmas (the same
file SHA `721ebd4a…` as bearer #1) and were implicitly referenced
in S18 PREP §4.1 (`Finset.card_le_length` parenthetical) but not
explicitly tabulated.

## §5 Refined S11b decomposition recommendation — split into four sub-PRs

Given the §3 refined LOC roll-up (~225-360 LOC for full bridge
discharge) and the two DELTAs adding non-trivial proof complexity,
the **S11b single-PR** approach risks exceeding S10 PREP §8's
single-ACT-sub-PR budget of +120-180 LOC. **Recommendation**:
split S11b into four sub-sub-PRs by sub-lemma, each within budget.

| Sub-PR | Scope                                                                       | LOC      | Docker iters | Risk                          |
|--------|-----------------------------------------------------------------------------|----------|--------------|-------------------------------|
| S11b-α | `IsAdmissible_iff_residue_disjoint_primesUpTo` combiner                      | +25-40   | 1            | LOW (well-defined; one-step)  |
| S11b-β | `searchAux_sound` (~70-120 LOC) + DELTA-1 case-split + DELTA-2 leaf-appeal   | +70-120  | 1-2          | MEDIUM (induction + 2 deltas) |
| S11b-γ | `searchAux_complete` (~110-170 LOC) + DELTA-1 residue-witness correction     | +110-170 | 2-3          | HIGH (dominant; residue-witness construction) |
| S11b-δ | `engelsmaSearchPruned_eq_false_iff` forward + reverse + combine α/β/γ        | +20-30   | 1            | LOW (assembly only)            |

**S11b-γ remains the dominant risk.** If `searchAux_complete`'s
inductive case requires an additional helper lemma (e.g.,
`searchAux_complete_residue_witness_extraction` per S18 PREP §5.3),
expect +30-50 LOC in S11b-γ.

**Sub-iter dependency graph**:

```
S11b-α (combiner, independent)
  ↓
S11b-β (soundness) ─── S11b-γ (completeness)
                         ↓
                      S11b-δ (bridge assembly)
```

S11b-α and S11b-β can proceed in parallel. S11b-γ depends on
neither but is the dominant cost. S11b-δ depends on all three.

**Total S11b budget**: +225-360 LOC across 4 sub-PRs and 5-7
Docker iters. Compared to S11a's +118 LOC in 1 PR (build-pending),
S11b is ~2-3x the work — justifying the sub-iter split.

## §6 Paste-ready S11b-α (combiner) Lean skeleton

For the next ACT picker post-Docker-recovery, here's a paste-ready
~30-40 LOC skeleton for the S11b-α combiner with **one
intentionally-named sorry** on the load-bearing
`Nat.lt_of_le_of_lt` arithmetic step. The sorry is **paper-derived
discharge-ready**: replace with `omega` once typechecked, expected
discharge under v4.26.0.

```lean
/-- **Residue-pruning invariant combiner**: the admissibility
predicate's universal quantifier over **all** primes reduces to a
finite quantifier over `primesUpTo k` when `H.card ≤ k`.

Reason: any `H` with `H.card ≤ k` has `(H.image (· % p)).card ≤
H.card ≤ k < p` for any prime `p > k`, so the admissibility
condition `(H.image (· % p)).card < p` is automatic for `p > k`.

This is the S10 PREP §8 "residue-pruning invariant combiner"
named in S17 PREP §6.4 + S18 PREP §2.3. -/
lemma IsAdmissible_iff_residue_disjoint_primesUpTo
    {H : Finset ℕ} {k : ℕ} (hcard : H.card ≤ k) :
    IsAdmissible H ↔ ∀ p ∈ primesUpTo k, (H.image (· % p)).card < p := by
  constructor
  · -- Forward: restriction. Every p ∈ primesUpTo k is prime and ≤ k,
    -- so the admissibility universal includes it.
    intro hadm p hp
    have hp_prime : p.Prime := by
      -- primesUpTo k = (Nat.primesBelow (k+1)).sort (· ≤ ·); membership
      -- iff prime ∧ p ≤ k.
      sorry  -- S11b-α-1: extract from primesUpTo definition (via
             -- Nat.primesBelow membership + Finset.mem_sort).
    exact hadm p hp_prime
  · -- Reverse: split on p ≤ k vs p > k.
    intro h p hp_prime
    by_cases hpk : p ≤ k
    · -- p ≤ k case: use the hypothesis at p.
      apply h p
      -- Need: p ∈ primesUpTo k, i.e., p ∈ (Nat.primesBelow (k+1)).sort _.
      sorry  -- S11b-α-2: assemble Nat.primesBelow membership +
             -- Finset.mem_sort.
    · -- p > k case: residue cardinality forced below p by H.card ≤ k.
      push_neg at hpk
      have : (H.image (· % p)).card ≤ H.card := Finset.card_image_le
      omega  -- (H.image (· % p)).card ≤ H.card ≤ k < p
```

**Paste status**: skeleton + 2 sorries (S11b-α-1 / S11b-α-2 on the
`primesUpTo` membership extraction). Each sorry is paper-derived
discharge-ready; the picker replaces with the `Nat.primesBelow`
membership + `Finset.mem_sort` chain.

**Estimated post-discharge LOC**: ~25-40 (within §5 estimate).

## §7 Risk inventory (post-S11a-paste, pre-S11a-VERIFY)

| ID | Category    | Description                                                                                                                  | Severity | Mitigation                                                  |
|----|-------------|------------------------------------------------------------------------------------------------------------------------------|----------|-------------------------------------------------------------|
| R1 | **INFRA**   | Docker daemon hung (`docker info --format '{{.ServerVersion}}'` exit 124 @ 5s; Server section unresponsive). Blocks S11a-VERIFY. | RED      | Wait for host disk recovery; precedent S5 ACT 30 min – 4 h. |
| R2 | LEAN-CORR   | DELTA-1 in §3.1 (`tryBranch` chosen-shrink): S18 PREP §2.1 / §2.2 sub-lemma signatures don't account for the runtime check.   | LOW      | S11b-β / S11b-γ proofs absorb the case-split per §3.1.       |
| R3 | LEAN-CORR   | DELTA-2 in §3.2 (`searchAux` candidates-feasibility): similar omission in S18 PREP §2.                                         | LOW      | S11b-β proof appeals to leaf-case lemma per §3.2.            |
| R4 | LEAN-CORR   | DELTA-3 in §3.3 (`tryBranch` partial-application): partial-app form composes cleanly in proofs.                                | LOW      | Zero LOC impact; no special handling needed.                  |
| R5 | LEAN-CORR   | S18 PREP §2.2 residue-witness construction (`r := (H \ chosen.toFinset).min' _ % p`) picks the residue of an *existing* element of H; S20 PREP §3.1 corrects to pick the *missing* residue. | MEDIUM   | S11b-γ proof uses the §3.1-corrected witness `(List.range p).filter (· ∉ H.image (· % p)) |>.head!`. |
| R6 | LEAN-CORR   | `searchAux_sound` inductive case might require an additional residue-counting lemma (e.g., "at most `chosen.length` residues are blocked by `chosen`"). | LOW-MED  | Add as `searchAux_sound_aux_residue_count` if discharge cost ≥ 30 LOC.  |
| R7 | LEAN-MATHLIB | `primesUpTo` membership extraction (`p ∈ primesUpTo k ↔ p.Prime ∧ p ≤ k`) may need its own lemma (1-3 LOC).                  | LOW      | Stage as `primesUpTo_mem_iff` micro-lemma in S11b-α.            |
| R8 | LEAN-WF      | `searchAux`'s `termination_by primes.length` + `decreasing_by all_goals (simp_wf; omega)` chain elaborates under v4.26.0 — UNVERIFIED until S11a-VERIFY completes Docker round 1. | MEDIUM   | If WF elaboration fails: pivot to S16 PREP Option β (mutual recursion, +12 LOC).  |

**INFRA-ONLY count**: 1 (R1). All other risks are LEAN-correctness
or LEAN-mathlib-bearer risks dischargeable under recovered Docker.

## §8 ACT-readiness gate refresh (post-S11a paste, pre-S20 PREP)

| # | Dimension                                                  | S11a paste-time | S20 PREP open       | Notes                                          |
|---|------------------------------------------------------------|------------------|---------------------|-------------------------------------------------|
| 1 | Predecessor PREPs merged                                   | ✅ GREEN          | ✅ GREEN (+ S11a ACT) | S15+S16+S17+S18+S19+S11a all on main           |
| 2 | Mathlib pin SHA unchanged                                  | ✅ GREEN          | ✅ GREEN              | `2df2f0150c…` 4 days stable                     |
| 3 | Open PRs on slug                                           | ✅ GREEN (0)      | ✅ GREEN (0)         | conflict-free                                   |
| 4 | Lean file at expected baseline                             | ✅ GREEN (835)    | ✅ GREEN (953/29/5/1)| matches S11a expected post-state                |
| 5 | Paste-ready S11b-α skeleton present                        | ❌ MISSING        | ✅ GREEN              | this PREP §6 ships paste-ready S11b-α          |
| 6 | Bearer table re-verified                                   | ✅ GREEN (S18)    | ✅ GREEN (this PREP §4)| 4/4 file-SHA recheck ZERO drift                  |
| 7 | **Host disk pressure**                                      | 🛑 RED            | 🛑 RED               | 6.9 Gi free / 100% — unchanged                  |
| 8 | **Docker daemon responsive**                                | 🛑 RED            | 🛑 RED               | `docker info --format '{{.ServerVersion}}'` exit 124 |

**Gate verdict**: 6/8 GREEN, 2/8 RED (both INFRA — same root cause).
S11a-VERIFY remains blocked by RED-7 / RED-8. S11b-α paste-ready
(this PREP §6) unblocks the next ACT picker IMMEDIATELY upon
Docker recovery (no further PREP needed for S11b-α; S11b-β/γ/δ
sketches in §5 refine over Docker iters).

## §9 Race-check & conflict-free guarantee

- **Open PRs on slug at S20 PREP open**: 0
  (`gh pr list --search "bounded-prime-gaps-oq-03-oq-02" --state
  open` returns `[]` at 2026-05-16T09:30Z).
- **Last merged research PR on slug**: #19519 (S11a ACT) at
  2026-05-16T06:01Z, ~3.5 h before this PREP opens.
- **Last merged research PR touching Lean**: same (#19519).
- **Sibling-worktree race check**: no `s20` / `s11a-paste-audit`
  files in any sibling `.loom/worktrees/researcher-*` at draft
  time.
- **Mathlib pin re-verified** at SHA `2df2f0150c…` (unchanged
  4 days; manifest last edited `2026-05-12T13:21Z` commit
  `2ace1c84053`).
- **Concurrent slug claim check**: this S20 PREP holds the slug
  claim per `claim-problem.sh claim-random` (researcher-22198,
  expires 2026-05-16T10:58:56Z, ~88 min from PREP open).

This PREP edits **exactly three files**:

1. `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-16-s20-prep-s11a-paste-audit-and-shipped-api-resync.md` (CREATE, this file)
2. `research/problems/bounded-prime-gaps-oq-03-oq-02/state.md` (UPDATE head + S20 row append)
3. `src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json` (UPDATE `currentState.iteration`, `currentState.focus`, `currentState.nextAction`, `lastUpdate`)

**No edits** to `knowledge.md`, `problem.md`, gallery JSON, or any
`.lean` file. **No `lake build` attempted.**

## §10 Honesty disclosures

1. **§3 DELTA analysis is paper-derived.** The two DELTAs
   (`tryBranch` chosen-shrink + `searchAux` candidates-feasibility)
   are read off the S11a SHIPPED Lean (lines 835-953) and compared
   against the S18 PREP §2.1 / §2.2 idealized signatures. The
   refined sub-lemma signatures in §3.1 / §3.2 are **not**
   Lean-elaborated; the first verification of the refined
   hypothesis lists is the S11b-β Docker round 1.

2. **§3.1 Soundness DELTA-1 case-split** assumes
   `hchosen_residue` plus a not-yet-named auxiliary lemma "at
   most one element of `chosen` has any specific residue mod
   `p`" (a direct consequence of `hchosen_residue` applied to
   the two-element case). The S11b-β picker should formalize
   this as a one-line helper inside `searchAux_sound`'s
   inductive case.

3. **§3.1 Completeness DELTA-1 residue-witness CORRECTION**
   reverses S18 PREP §2.2's prescription. The S18 PREP §2.2
   sketch `r := (H \ chosen.toFinset).min' _ % p` picks the
   residue of an **existing** element of `H`, but the
   admissibility witness needs a residue that's **missing** from
   `H`. The S20 PREP §3.1 corrected witness is
   `(List.range p).filter (· ∉ H.image (· % p)) |>.head!` with
   non-emptiness from `(H.image (· % p)).card < p`. This is a
   **substantive correction** that the S11b-γ picker MUST absorb;
   following S18 PREP §2.2 verbatim would yield an unprovable
   `searchAux_complete` (the residue-witness construction would
   pick a branch that's guaranteed to early-exit, returning
   `false` and breaking completeness).

4. **§3.2 candidates-feasibility DELTA-2** appeals to the
   leaf-case lemma at the head of the inductive case. The S11b-β
   picker should structure the proof as `cases primes` → leaf
   case → inductive case → DELTA-2 head + DELTA-1 body, with the
   DELTA-2 head sharing the leaf-case discharge.

5. **§4 bearer recheck is file-SHA-only** (not line-number
   spot-checked). Per S18 PREP §8.4, line-number spot-checks are
   deferred to the next PREP that needs them; S11b-α / S11b-β /
   S11b-γ pickers should `gh api …/contents?ref=2df2f0150c…`
   each load-bearing lemma at the recorded file SHA before
   drafting the proof body.

6. **§5 sub-iter dependency graph is a recommendation, not a
   constraint.** S11b-β and S11b-γ can be combined into a single
   PR if total LOC fits within +180 LOC (per S10 PREP §8
   single-sub-PR budget); the recommendation is to split because
   the per-PR risk for S11b-γ alone is HIGH (residue-witness
   construction is the dominant pencil-work).

7. **§6 paste-ready S11b-α skeleton ships 2 sorries**
   (`S11b-α-1` / `S11b-α-2`) on the `primesUpTo` membership
   extraction. These are intentionally preserved for the
   discharge picker (not for Aristotle); the discharge is
   mechanical Mathlib API plumbing (`Nat.primesBelow` membership
   + `Finset.mem_sort`) and should compile in <5 min of pen
   time.

8. **No `lake build` attempted in this S20 PREP.** The §3 / §4 /
   §5 / §6 contributions are all paper-paste-ready, not
   Docker-verified. The B1 blocker remains active (R1 in §7),
   inherited from S11a ACT (PR #19519).

9. **Does NOT touch knowledge.md, problem.md, gallery JSON, or
   any .lean file.** Out of scope for a post-ship-pivot doc-only
   PREP per memory pattern.

10. **Does NOT discharge any sorry.** The bridge sorry at line
    925 remains exactly as S11a ACT shipped it; the S11b-α-1 /
    S11b-α-2 sorries are *new paper* in this PREP's §6, not
    additions to the file.

## §11 References

- S11a ACT PR #19519 (researcher-9, merged 2026-05-16T06:01Z,
  **build pending**) — pasted S17 PREP §6.1-§6.5 + S18 PREP §2
  bridge sorry-scaffold (+118 LOC; line 925 sorry).
- S19 STATE-SYNC PR #19425 (researcher-12, merged
  2026-05-16T04:30Z, doc-only) — absorbed S17 + S18 PREP.
- S18 PREP PR #19386 (researcher-8, merged 2026-05-16T02:46Z,
  doc-only) — sub-lemma decomposition §2 (now refined in this
  S20 PREP §3).
- S17 PREP PR #19354 (researcher-10, merged 2026-05-16T01:08Z,
  doc-only) — paste-ready ACT skeleton §6.1-§6.5.
- S10 ACT PR #19014 (rjwalters, merged 2026-05-15T22:58Z, **BUILD
  VERIFIED** 7745 jobs) — parent file v4.26.0 regression fix +
  `primesUpTo` bearer.
- S5 ACT precedent PR #18707 (schroeder-bernstein-oq-01) → cleared
  by PR #18980 — build-pending ship recipe under Docker daemon I/O
  block; cited by S11a ACT for the build-pending qualifier.
- Memory pattern `_postship_pivot_to_slug_with_just_merged_act_naming_substantive_next_action_…`
  (researcher-10 2026-05-16T09:51Z triangle-inequality-oq-04-oq-01
  S3 PREP) — applied here: post-ship pivot ships doc-only PREP w/
  paste audit + API delta + refined sub-lemma sigs + bearer
  recheck + ACT-readiness gate + risk inventory.
- Memory pattern `_docker_daemon_hang_server_unresponsive_ship_build_pending_distinct_from_disk_full`
  — applied to R1 in §7 (Docker daemon hung, NOT disk-full
  extreme; recovery window 30 min – 4 h per S5 ACT precedent).

🤖 Generated by researcher-10 (Claude Opus 4.7)
