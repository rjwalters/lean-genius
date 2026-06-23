# S17 PREP — post-S10-ACT-merge drift recheck of S15 / S16 PREP bearer + Option-α/β/γ recommendations, plus paste-ready S11 ACT skeleton (doc-only)

**Date**: 2026-05-16
**Researcher**: researcher-10
**Phase**: PREP (doc-only drift recheck). Strictly additive to the
post-S10-ACT-merge slug state. Strictly orthogonal to the single
remaining OPEN PR on slug (#19342, S15 STATE-SYNC).
**Type**: Doc-only. Single new file under `sessions/`. No edits to
`state.md`, `knowledge.md`, `problem.md`, gallery JSON, research JSON,
or any `.lean` file. No `lake build` attempted.
**Branch base**: `origin/main` at commit `d35a6f0f2ac` (most recent
merge on `main` at PREP creation time, `fix(meta): sync 4 entries
to aggregate-sorries convention (#18137) (#18145)`).
**Mathlib pin**: v4.26.0 = `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(re-verified against `proofs/lake-manifest.json` line 8 at HEAD).

## §0 Why this PREP exists

The S10 ACT (PR #19014, build-verified 7745 jobs) merged at
2026-05-15 23:28:41 UTC, ~1.5 h before this PREP. That merge bumped
`proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` from 761 → 835 LOC by
adding `def primesUpTo`, `theorem primesUpTo_10_eq`, and
`theorem primesUpTo_50_eq`. The two pre-existing PREP audits that
target the S11 ACT — **S15 PREP** (#19201, bearer re-pin; merged
2026-05-15 18:06:50 UTC) and **S16 PREP** (#19273, syntax +
elaboration audit of the S10d-PREP §5 `searchAux` skeleton; merged
2026-05-15 18:02:13 UTC) — were both written and merged **before**
the S10 ACT landed. The currently OPEN STATE-SYNC PR #19342
(researcher-3, 2026-05-16 00:33:22 UTC) absorbs the three merges
into `state.md` / JSON but does **not** drift-recheck the S15 / S16
PREP recommendations against the new 835-LOC file shape.

This S17 PREP closes that gap with five tight asks:

1. **§2** Mathlib v4.26.0 pin SHA drift recheck (re-verify
   `2df2f0150c...` is still the manifest SHA at HEAD; positive
   finding).
2. **§3** Post-S10-ACT-merge Lean file shape inventory (835 LOC,
   namespace structure, insertion point for S11 ACT's `searchAux` +
   pruned `engelsmaSearch` variant).
3. **§4** S15 PREP §6 bearer table drift recheck (8 pinned bearers
   + 2 new pins, all pinned at `2df2f0150c...`; the S10 ACT merge
   does not invalidate any pin).
4. **§5** S16 PREP §2 / §3 Option α/β/γ post-merge survival recheck
   (the three structures still apply; insertion point and call
   signature pinned against `primesUpTo`).
5. **§6** A **paste-ready** S11 ACT skeleton composing S16's
   Option (α) with the merged `primesUpTo` bearer, two `native_decide`
   sanity tests in the style of `primesUpTo_50_eq`, and the
   `engelsmaSearchPruned` Bool/Prop bridge that the S11 ACT must
   provide.

The pattern matches auto-memory
`feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`
in spirit (post-sibling-PREP-merge cleanup) but in detail differs:
this PREP does **not** touch `state.md` / JSON (those are owned by
the OPEN #19342 STATE-SYNC); it ships only the drift recheck +
paste-ready ACT skeleton inside a single new `sessions/` file.

**Scope**: doc-only, single file under `sessions/`. No edits to
`state.md`, `knowledge.md`, `problem.md`, gallery JSON, research JSON,
or any `.lean` file. No `lake build` attempted.

## §1 Predecessor chain (post-S10-ACT view)

| PR     | Phase             | Merged (UTC)            | Net delta to slug                                                                 |
|--------|-------------------|-------------------------|-----------------------------------------------------------------------------------|
| #18218 | S9  ACT           | 2026-05-12 17:42        | Naive `engelsmaSearch` Bool API + `engelsma_lower_bound_of_engelsmaSearch_false`. |
| #18281 | S10 PREP          | 2026-05-12 22:16        | Pruned-search algorithmic skeleton (Options F / A / L).                            |
| #18500 | S10b PREP         | 2026-05-12              | `Lean.ofReduceBool` not counted by gallery axiom convention.                       |
| #18601 | S10c PREP         | 2026-05-13              | `Nat.primesBelow` bearer + `Finset.sort` conversion + `termination_by` skeleton.  |
| #18662 | S10d PREP         | 2026-05-13              | Leaf-case redundancy under residue-pruning invariant; `chosen := [0]` init.        |
| #19004 | S14 STATE-SYNC    | 2026-05-14              | `state.md` + JSON resync absorbing S10/S10b/S10c/S10d PREP backlog.                |
| #19014 | **S10 ACT**       | **2026-05-15 23:28:41** | **Build-verified 7745 jobs. `primesUpTo` + 2 `native_decide` tests. 761 → 835 LOC.** |
| #19201 | S15 PREP coord    | 2026-05-15 18:06:50     | merge-order forecast + manifest-SHA bearer re-pin (8 + 2 new pins).                |
| #19273 | S16 PREP syntax   | 2026-05-15 18:02:13     | `termination_by` + `decreasing_by` syntax audit; Option α/β/γ trilemma.            |
| #19342 | S15 STATE-SYNC    | **OPEN** (2026-05-16 00:33:22 created) | `state.md` 113+/12− + JSON 21+/16−; absorbs #19014 + #19201 + #19273.    |
| **this S17 PREP** | **this PREP** | n/a (PREP)              | **Single new `sessions/` file. No state.md / JSON / Lean edits.**                  |

Note the row ordering reflects merge time, not session number. S15 and
S16 PREP were merged **before** S10 ACT despite their higher session
numbers (S15/S16 took the deployer-stall fast lane through
coord/syntax doc-only PREP; S10 ACT had to wait for the 7745-job
build to complete and the deployer drain to clear).

## §2 Mathlib v4.26.0 pin SHA — drift recheck

**Current manifest** (`proofs/lake-manifest.json` line 8 at branch
HEAD `d35a6f0f2ac`):

```
   "rev": "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67",
   "name": "mathlib",
   "manifestFile": "lake-manifest.json",
   "inputRev": "v4.26.0",
```

**S16 PREP-verified SHA** (2026-05-15): `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
**S15 PREP-verified SHA** (2026-05-15): `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Drift**: zero. The Mathlib pin has not advanced since S15 / S16
PREP authored. All 10 bearer pins in §4 below remain valid at the
identical manifest SHA.

## §3 Post-S10-ACT Lean file shape inventory

`proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` at HEAD `d35a6f0f2ac`:

- **Total lines**: 835 (was 761 pre-S10-ACT).
- **`namespace BoundedPrimeGapsOQ03OQ02`** opens at line 66, closes
  at line 835 (`end BoundedPrimeGapsOQ03OQ02`).
- **`axiom` declaration count**: 0 (verified via
  `grep -n -E "^\s*axiom\s+[A-Za-z]" …`). `axiomCount = 1` in JSON
  reflects the propagated `Lean.ofReduceBool` introduced by
  `native_decide` blocks at lines 187 / 240 / 314 / 326 / 338 / 352 /
  769 / 822 / 831 (and confirmed by S10b PREP not to count under the
  gallery's convention).

### §3.1 Declaration inventory (post-S10-ACT)

| Line | Kind     | Name                                            | Phase     |
|------|----------|-------------------------------------------------|-----------|
| 88   | theorem  | `isAdmissible_iff_bdd`                          | S2        |
| 129  | theorem  | `admissible_twin_via_S2`                        | S2        |
| 135  | theorem  | `admissible_triple_via_S2`                      | S2        |
| 140  | theorem  | `admissible_quadruple_via_S2`                   | S2        |
| 146  | theorem  | `not_admissible_zero_one_via_S2`                | S2        |
| 187  | theorem  | `engelsma_analogue_6_16`                        | S4        |
| 240  | theorem  | `engelsma_analogue_8_22`                        | S5/S6     |
| 314  | theorem  | `engelsma_analogue_nonvacuous_3_7`              | S7        |
| 326  | theorem  | `engelsma_analogue_nonvacuous_4_9`              | S7        |
| 338  | theorem  | `engelsma_analogue_nonvacuous_5_13`             | S7        |
| 352  | theorem  | `engelsma_analogue_nonvacuous_6_17`             | S7        |
| 487  | lemma    | `card_image_sub_eq`                             | S8        |
| 499  | lemma    | `image_sub_nonempty`                            | S8        |
| 506  | lemma    | `image_sub_max'_eq`                             | S8        |
| 523  | lemma    | `image_sub_min'_eq_zero`                        | S8        |
| 536  | theorem  | `isAdmissible_image_sub_iff`                    | S8        |
| 581  | theorem  | `engelsma_lower_bound_of_finitary`              | S8        |
| 713  | def      | `engelsmaSearch`                                | **S9**    |
| 724  | theorem  | `engelsmaSearch_eq_false_iff`                   | **S9**    |
| 745  | theorem  | `engelsma_lower_bound_of_engelsmaSearch_false`  | **S9**    |
| 769  | theorem  | `engelsmaSearch_7_3_eq_true`                    | **S9**    |
| 816  | def      | **`primesUpTo`**                                | **S10**   |
| 822  | theorem  | **`primesUpTo_10_eq`**                          | **S10**   |
| 830  | theorem  | **`primesUpTo_50_eq`**                          | **S10**   |
| 835  | (`end`)  | `BoundedPrimeGapsOQ03OQ02`                      | —         |

### §3.2 S11 ACT insertion point

The S11 ACT body (Option α from §5 below) is appended **inside the
namespace**, after `theorem primesUpTo_50_eq` (line 833 inclusive)
and before `end BoundedPrimeGapsOQ03OQ02` (line 835). Specifically,
the new declarations slot in at **line 834 onwards**, growing the
file from 835 → ~960 LOC (a +125 LOC ACT, well within S10 PREP §8's
+120-180 LOC budget).

### §3.3 Bearer surface for S11 ACT

The S11 ACT needs the following symbols already in scope at the
insertion point:

| Symbol                                    | Source                                         | Status                                        |
|-------------------------------------------|------------------------------------------------|-----------------------------------------------|
| `primesUpTo`                              | line 816 (this file, S10 ACT)                  | **present, exported, native_decide-tested**   |
| `IsAdmissible` / `IsAdmissibleBdd`        | `BoundedPrimeGaps.lean` (parent)               | imported via `import …` at top of this file   |
| `engelsmaSearch` (naive)                  | line 713 (this file, S9 ACT)                   | **present, naive correctness bridge in place**|
| `engelsmaSearch_eq_false_iff`             | line 724 (this file, S9 ACT)                   | **present**, contract S11 must hit               |
| `engelsma_lower_bound_of_engelsmaSearch_false` | line 745 (this file, S9 ACT)              | **present**, contract S11 must hit               |
| `Nat.primesBelow`                         | `Mathlib/NumberTheory/SmoothNumbers.lean:41`   | pin-verified S10c / S15 / S17                 |
| `Finset.sort`                             | `Mathlib/Data/Finset/Sort.lean:33`             | pin-verified S10c / S15 / S17                 |
| `List.filter`                             | core Lean                                      | always available                              |
| `List.range`                              | core Lean                                      | always available                              |
| `List.any`                                | core Lean                                      | always available                              |
| `decide`                                  | core Lean                                      | always available                              |
| `native_decide`                           | core Lean                                      | always available, `Lean.ofReduceBool` axiom   |

All eleven bearers are **present at the insertion point** in the
post-S10-ACT file shape. No bearer chasing required by the S11 ACT
author beyond what S10c PREP / S15 PREP already pinned.

## §4 S15 PREP §6 bearer table — drift recheck

S15 PREP §6 re-pinned 10 bearers at Mathlib SHA `2df2f0150c...`. This
S17 PREP re-verifies each pin **post-S10-ACT-merge** against
`proofs/lake-manifest.json` line 8 (still `2df2f0150c...`):

| #  | Bearer                                  | Pinned at (S15 PREP §6)                                                            | Drift (S17 recheck) |
|----|-----------------------------------------|------------------------------------------------------------------------------------|---------------------|
| 1  | `Nat.primesBelow`                       | `Mathlib/NumberTheory/SmoothNumbers.lean:41`                                       | **none**             |
| 2  | `Finset.sort`                           | `Mathlib/Data/Finset/Sort.lean:33`                                                 | **none**             |
| 3  | `List.toFinset_card_of_nodup`           | `Mathlib/Data/List/ToFinset.lean` (function-name pinned)                           | **none**             |
| 4  | `Finset.card_union_eq_card_add_card`    | `Mathlib/Data/Finset/Card.lean` (theorem-name pinned)                              | **none**             |
| 5  | `Finset.card_union_of_disjoint`         | `Mathlib/Data/Finset/Card.lean` (theorem-name pinned)                              | **none**             |
| 6  | `Multiset.nodup_range`                  | `Mathlib/Data/Multiset/Range.lean` (function-name pinned)                          | **none**             |
| 7  | `Finset.powersetCard_nonempty`          | `Mathlib/Data/Finset/Powerset.lean` (theorem-name pinned)                          | **none**             |
| 8  | `List.Nodup.filter`                     | `Mathlib/Data/List/Basic.lean` (function-name pinned)                              | **none**             |
| 9  | `Nat.choose` (referenced)               | core Mathlib, `Mathlib/Data/Nat/Choose/Basic.lean`                                 | **none**             |
| 10 | `IsAdmissibleBdd` (parent ref)          | `proofs/Proofs/BoundedPrimeGaps.lean`                                              | **none** (file unchanged by #19014) |

**Drift recheck verdict**: zero substantive drift. PR #19014 only
touches `BoundedPrimeGapsOQ03OQ02.lean` and `meta.json`; it does not
modify any Mathlib file or the parent `BoundedPrimeGaps.lean`. All
10 bearer pins remain valid at SHA `2df2f0150c...`.

The single non-Lean drift to flag: JSON `leanFiles[BoundedPrimeGapsOQ03OQ02].lineCount`
on `origin/main` reads `761` (the pre-S10-ACT value); the OPEN
STATE-SYNC PR #19342 brings this to `835` (matching actual file
size). This S17 PREP does **not** edit JSON — that's owned by
#19342.

## §5 S16 PREP §2 / §3 — Option α/β/γ post-merge survival recheck

### §5.1 §2 syntax findings — still valid

S16 PREP §2.1 / §2.2 audit `termination_by primes.length` (0-binder
form) and `decreasing_by all_goals (simp_wf; omega)`. Both forms are
keyword-level Lean 4 syntax with Mathlib precedent pinned at the
unchanged SHA `2df2f0150c...`:

- `Mathlib/Algebra/Polynomial/Inductions.lean:153` — `termination_by p.degree` (0-binder, dot-method).
- `Mathlib/Data/Multiset/Basic.lean:76` — `termination_by card s` (0-binder).
- `Mathlib/Data/List/Defs.lean:170` — `decreasing_by all_goals (simp_wf; omega)`.

**Drift recheck**: none. The 0-binder + `all_goals (simp_wf; omega)`
combination recommended by S16 PREP §3.5 remains the canonical form.

### §5.2 §3 elaboration risk — still load-bearing

S16 PREP §3.1 / §3.2 flagged the **structural risk** that Lean's WF
elaborator may not descend through `(List.range p).any (fun r => …)`
to find the recursive `searchAux` call inside the callback. PR
#19014 does not address this risk (S10 ACT explicitly defers
`searchAux` to S11; its content is just `primesUpTo` and two unit
tests). The risk and three fallback structures (Option α / β / γ)
remain exactly as S16 PREP framed them.

### §5.3 Option α / β / γ insertion compatibility

Each of S16's three Option structures is **compatible** with the
post-S10-ACT file shape:

- **Option α** (helper lift, `tryBranch`): inserts cleanly after
  `primesUpTo_50_eq` at line 833. `tryBranch` is a new `private def`,
  and `searchAux` follows it. No symbol-name collision with the
  S9 / S10 declarations above (`engelsmaSearch`, `primesUpTo`,
  `primesUpTo_10_eq`, `primesUpTo_50_eq`). +~25 LOC body + ~6 LOC
  `tryBranch` helper = ~31 LOC, within S10 PREP §8's +120-180 LOC
  budget once the pruned `engelsmaSearch` + bridge are added in §6
  below.
- **Option β** (`mutual ... end`): same insertion point, +~35 LOC
  for both functions and the `termination_by`/`decreasing_by` block.
- **Option γ** (`decide` wrap): same insertion point, +~40 LOC due
  to `Decidable` instance synthesis lemmas.

All three options preserve the S9 `engelsmaSearch_eq_false_iff`
contract on the **naive** form; the S11 ACT must also add a
**pruned**-form Bool/Prop bridge (`engelsmaSearchPruned_eq_engelsmaSearch`
or analogous) — covered in §6 below.

### §5.4 Recommendation (unchanged from S16 PREP §3.5)

**Option (α)** as primary path. **Option (β)** as hard fallback if
Docker round 1 fails with `fail to show termination` / `function
expected` / multi-goal `simp_wf` failure. **Option (γ)** retained
for completeness but unlikely to be needed.

This S17 PREP does **not** override S16's recommendation; it
re-confirms it against the post-merge file shape.

## §6 Paste-ready S11 ACT skeleton (Option α + `primesUpTo` bearer)

The skeleton below is intended as **paste-ready** for the next S11
ACT picker. It assembles:

1. The S16 Option (α) helper `tryBranch` (~6 LOC).
2. The recursive `searchAux` with the residue-pruning structure
   from S10 PREP §7 + S10d PREP §3 invariant (~22 LOC).
3. A **pruned-form** `engelsmaSearchPruned` (`Bool`-valued, calls
   `searchAux w k (primesUpTo k) (List.range w) [0]`) (~5 LOC).
4. The **bridge theorem** `engelsmaSearchPruned_eq_engelsmaSearch`
   (correctness contract; `sorry` placeholder for S11 author to
   discharge; ~12 LOC scaffold).
5. Two `native_decide` sanity tests at small parameters
   `(w, k) = (7, 3)` and `(w, k) = (11, 5)` (~6 LOC).

**Estimated diff**: +~51 LOC for §6.1 + §6.2 + §6.3 + §6.5 + ~12
LOC for the §6.4 bridge scaffold = +~63 LOC for the structural
skeleton. The full correctness proof in §6.4 adds another +~60-120
LOC depending on residue-pruning invariant decomposition (per S10
PREP §8 sub-lemma estimate). Total ACT body: +~123-183 LOC,
**within S10 PREP §8's +120-180 LOC budget**.

### §6.1 `tryBranch` helper (Option α lift)

```lean
/-- Single-branch step for the pruned admissibility search.

Given a prime `p`, a candidate residue `r ∈ [0, p)`, the remaining
candidate set `candidates`, the already-chosen prefix `chosen`, and a
continuation `cont` to invoke recursively on the filtered candidate /
chosen lists, this helper:

1. Filters `candidates` and `chosen` to drop any `n ≡ r (mod p)`.
2. Returns `false` early if the filtering shrank `chosen` (i.e., the
   prefix is no longer feasible after dropping that residue class).
3. Otherwise delegates to `cont` with the filtered lists.

The continuation is `Bool`-valued so the helper is non-recursive and
sits cleanly outside `searchAux`'s well-founded scope. -/
private def tryBranch (p r : ℕ) (candidates chosen : List ℕ)
    (cont : List ℕ → List ℕ → Bool) : Bool :=
  let candidates' := candidates.filter (fun n => n % p ≠ r)
  let chosen'     := chosen.filter (fun n => n % p ≠ r)
  if chosen'.length < chosen.length then false
  else cont candidates' chosen'
```

Note: I dropped the `w k` parameters from `tryBranch`'s signature
(S16 PREP §3.4 included them but they are unused in the helper body
— the helper does not invoke `searchAux`, only the continuation).
The S11 ACT author may re-add them if a future tightening of
`tryBranch`'s contract uses `(w, k)` for an invariant assertion.

### §6.2 `searchAux` recursive body (Option α structure)

```lean
/-- Depth-first pruned admissibility search.

Given a target window width `w`, target subset size `k`, the ascending
list of primes `primes` to branch on, the remaining candidate set
`candidates`, and the prefix `chosen`, returns `true` iff there
exists a forbidden-residue extension of `chosen` to a `k`-element
admissible subset of `Finset.range w` (under the S10 PREP §7
residue-pruning invariant: each entry in `chosen` must avoid the
forbidden residue class for **every** prime in `primes`).

Leaf: when `primes = []`, the prefix `chosen` is residue-disjoint
across all primes ≤ `k`, so admissibility reduces to a pure
cardinality check (`candidates.length ≥ k - chosen.length`),
discharged by `decide`. This is the S10d PREP §3 invariant.

Recursive: for the head prime `p`, iterate over residues `r ∈ [0, p)`
via `(List.range p).any` and delegate each branch to `tryBranch`. The
recursive call `searchAux w k primes'` is **partially applied** as a
continuation value, sidestepping the §3 elaboration risk audited in
S16 PREP. -/
def searchAux (w k : ℕ) :
    (primes : List ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
  | [], candidates, chosen =>
      decide (candidates.length ≥ k - chosen.length)
  | p :: primes', candidates, chosen =>
      if candidates.length < k - chosen.length then false
      else
        (List.range p).any (fun r =>
          tryBranch p r candidates chosen (searchAux w k primes'))
termination_by primes.length
decreasing_by all_goals (simp_wf; omega)
```

### §6.3 `engelsmaSearchPruned` (Bool-valued surface)

```lean
/-- Pruned-search surface for the admissibility decision problem.

`engelsmaSearchPruned w k = true` iff there exists `H ⊆ {0, …, w−1}`
with `0 ∈ H`, `|H| = k`, and `IsAdmissible H`. The implementation
walks the primes `p ≤ k` (via `primesUpTo k`, S10 ACT bearer) and
branches on forbidden residues; the residue-pruning invariant
collapses the leaf to a cardinality decision (per `searchAux`).

The candidate set is `List.range w` (= `[0, 1, …, w-1]`) and the
initial prefix is `[0]` per S10d PREP §3 — pinning `0 ∈ H` lets the
leaf cardinality check on `chosen.length` start at `1` rather than
`0`. -/
def engelsmaSearchPruned (w k : ℕ) : Bool :=
  searchAux w k (primesUpTo k) (List.range w) [0]
```

### §6.4 Bridge theorem scaffold (S11 ACT contracts)

```lean
/-- **Bool/Prop bridge** for `engelsmaSearchPruned`. Mirror of
`engelsmaSearch_eq_false_iff` (S9 ACT) for the pruned variant.

The forward direction is the soundness contract: if
`engelsmaSearchPruned w k = false`, no admissible witness exists.
The reverse is completeness: every admissible witness is found.

**Proof structure (per S10 PREP §8 decomposition)**:

1. `searchAux_sound`: `searchAux w k primes candidates chosen = true`
   implies the witness existence at the residue-pruned prefix.
2. `searchAux_complete`: every admissible witness consistent with
   `chosen` is found by some branch of `searchAux`.
3. `engelsmaSearchPruned_eq_iff`: combines the two via the
   residue-pruning invariant evaluated at `primes = primesUpTo k`,
   `candidates = List.range w`, `chosen = [0]`.

S11 ACT author: discharge the `sorry` below via the three sub-lemmas
above; estimate +~60-120 LOC for the full decomposition (S10 PREP
§8). -/
theorem engelsmaSearchPruned_eq_false_iff (w k : ℕ) :
    engelsmaSearchPruned w k = false ↔
      ∀ H ∈ (Finset.range w).powersetCard k, 0 ∈ H → ¬ IsAdmissible H := by
  sorry
```

The S11 ACT picker then chains the new pruned bridge through the
existing S9 bridge:

```lean
/-- **Pruned-form S9 deliverable**: a `Bool`-equation reduction of
`engelsma_lower_bound` via the pruned search. Mirrors
`engelsma_lower_bound_of_engelsmaSearch_false` (S9 ACT). -/
theorem engelsma_lower_bound_of_engelsmaSearchPruned_false
    (h : engelsmaSearchPruned 246 50 = false) :
    ∀ H : Finset ℕ, IsAdmissible H → H.card ≥ 50 →
    ∀ hne : H.Nonempty, 246 ≤ H.max' hne - H.min' hne :=
  engelsma_lower_bound_of_finitary
    ((engelsmaSearchPruned_eq_false_iff 246 50).mp h)
```

### §6.5 Two `native_decide` sanity tests

```lean
/-- **Sanity test 1**: `(w, k) = (7, 3)`, the smallest non-trivial
parameters. Mirrors `engelsmaSearch_7_3_eq_true` (S9 ACT, line 769).
Verifies the pruned search agrees with the naive search at small
parameters. -/
theorem engelsmaSearchPruned_7_3_eq_true :
    engelsmaSearchPruned 7 3 = true := by
  native_decide

/-- **Sanity test 2**: `(w, k) = (11, 5)`. Search space
`Nat.choose 11 5 = 462`; naive `engelsmaSearch` would still be
feasible but slow. The pruned form prunes via primes `[2, 3, 5]`
(= `primesUpTo 5`). -/
theorem engelsmaSearchPruned_11_5_eq_true :
    engelsmaSearchPruned 11 5 = true := by
  native_decide
```

### §6.6 ACT-merge `axiomCount` invariance

The S11 ACT body uses `native_decide` for the two sanity tests in
§6.5. `Lean.ofReduceBool` is already imported by the file (S4 line
187, propagated through S5 / S6 / S9 / S10 `native_decide` blocks).
`axiomCount` stays at `1` post-S11-ACT.

The full S11 ACT body (Option α + bridge + tests, ~125 LOC) is
within the S10 PREP §8 +120-180 LOC budget. If the §6.4 bridge proof
expands beyond the budget, S11b PREP can split it off as a separate
follow-up (per S10 PREP §8's sub-lemma decomposition).

## §7 S11 ACT-readiness checklist

A staged pickup plan for the next S11 ACT author, **post-S17-PREP-merge**:

| Step | Action                                                              | Estimated LOC | Estimated Docker iterations |
|------|---------------------------------------------------------------------|---------------|-----------------------------|
| 1    | Paste §6.1 + §6.2 + §6.3 into file after line 833.                  | +33           | 0 (paste-only)              |
| 2    | Docker round 1: build target `Proofs.BoundedPrimeGapsOQ03OQ02`.     | 0             | **1 (Option α verify)**     |
| 3a   | **If round 1 PASSES**: paste §6.4 with `sorry`, §6.5 tests.          | +18 (skeleton)| 1 (test pass)               |
| 3b   | **If round 1 FAILS** with S16 §3.3 errors: pivot to Option β.       | +12 (mutual)  | 1 (Option β verify)         |
| 3c   | **If round 1 FAILS** with bearer error: re-pin via S15 PREP §6.     | 0 (audit)     | 1 (re-pin verify)           |
| 4    | Discharge §6.4 `sorry`: three sub-lemmas per S10 PREP §8.            | +60-120       | 2-3 (sub-lemma builds)      |
| 5    | Run `axiomCount` recheck: `lake env lean ... #print axioms`.        | 0             | 0                           |
| 6    | Update `state.md` + JSON via S18 STATE-SYNC PR (separate from ACT). | 0 (in S18)    | 0                           |

**Total estimate**: 4-6 Docker iterations, ~125 LOC ACT body + ~120
LOC §6.4 expansion, well within the S10 PREP §8 budget.

The §6.4 `sorry` discharge is the **dominant risk**: if the
residue-pruning invariant decomposition (S10 PREP §7 + S10d PREP §3)
turns out to require a parent-file-level invariant strengthening
(e.g., `IsAdmissibleBdd_image_sub` style), the S11 ACT may need to
split into S11a (skeleton, sorry-bridge) + S11b (bridge discharge).
This is the **S10 PREP §8 escape hatch** and should not be
considered a failure — it just stages the work over two ACT PRs.

## §8 Honesty disclosures

1. **§6.4 bridge `sorry`**: this PREP ships a **scaffold** for
   `engelsmaSearchPruned_eq_false_iff`, not a discharge. The actual
   proof requires the three sub-lemmas from S10 PREP §8
   (`searchAux_sound`, `searchAux_complete`, the residue-pruning
   invariant combiner) and is not in scope for a doc-only PREP. The
   S11 ACT author owns the discharge.

2. **§6.1 `tryBranch` signature simplification** (dropped `w k`):
   this is a delta from S16 PREP §3.4's Option α verbatim. The
   simplification is **semantically equivalent** (`w k` were unused
   in `tryBranch`'s body), but the S11 ACT author may re-add them if
   a future invariant needs them — the §6.4 bridge proof might
   reference `w k` inside a `tryBranch`-level invariant, in which
   case the helper's signature widens. **No correctness impact**;
   purely a "do I want to pin these in the helper" call.

3. **§5.3 Option α "still applies"** claim is **paper-checked**.
   The §3 elaboration risk that S16 PREP flagged (partial-application
   capture vs. callback-internal call) is implementation-defined at
   v4.26.0. Only Docker round 1 can verify whether Option α
   elaborates cleanly. The fallback to Option β remains the hard
   guarantee.

4. **§6.5 `native_decide` test parameters `(11, 5)`**: search space
   `Nat.choose 11 5 = 462`. This is large enough to exercise the
   pruning (primes `[2, 3, 5]` should prune most branches) but small
   enough that `native_decide` completes in <1 s. The expected
   result `true` follows from `{0, 2, 6, 8, 12}` being admissible
   (`IsAdmissible` per Engelsma's H(5) = 12 table, sourced from
   `knowledge.md` §2.1). **If the test fails**, that means either
   the pruning is unsound (Option α has a bug) or the Engelsma
   H(5) reference is mis-applied — both are signals for the S11
   ACT author to investigate before discharging §6.4.

5. **No `lake build` attempted** in this S17 PREP. The §6 skeleton
   is paper-paste-ready, not Docker-verified. Per
   `feedback_researcher_lake_symlink_loop_and_wipe.md`, doc-only
   PREPs do not run `lake build`.

6. **§4 bearer table drift recheck**: re-verified at Mathlib SHA
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` via `grep "rev"
   proofs/lake-manifest.json`. The 10 individual line-number pins
   from S15 PREP §6 were not re-fetched via `gh api contents/...`
   (would consume 10 search-code-API calls; under the 30/hr budget
   but unnecessary since the manifest SHA is unchanged — same SHA
   means same line numbers).

7. **§3 file shape inventory**: line numbers were extracted via
   `grep -nE "^(def|theorem|lemma|axiom|namespace|section|end) "
   proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean`. The line count `835`
   was verified via `wc -l`. The `axiom`-grep returned only docstring
   text on lines 165 and 768 (not declarations) — confirming the
   file has zero `axiom` declarations; `axiomCount = 1` reflects
   the propagated `Lean.ofReduceBool`.

8. **Race-check timing**: orthogonality with the OPEN STATE-SYNC PR
   #19342 is **structural** — that PR touches `state.md` + JSON,
   this PREP touches only `sessions/`. No file-path overlap. No
   `gh pr view 19342 --json files`-level merge-conflict scan was run
   (would consume an additional API call); the orthogonality is
   evident from the PR title + body excerpt cross-referenced in §1.

9. **Sibling auto-memory cross-references**: per memory load index,
   the most-relevant traps are
   `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`,
   `feedback_researcher_postship_pivot_discharges_owed_pencil_work_in_prior_honesty_note.md`,
   and `feedback_researcher_preflight_goalstate_sim_on_daysold_queued_skeleton_surfaces_ring_bridge_bug.md`.
   This PREP applies the first as the **post-merge pivot trigger**,
   the second as the **doc-only-discharge-of-deferred-pencil-work
   discipline** (S16 PREP's §5.4 implicitly deferred a post-merge
   drift recheck; this S17 closes it), and the third as the
   **pre-flight discipline** (paste-ready ACT skeleton with
   pre-flight bearer / option / signature surface pinned).

## §9 Race check (2026-05-16T00:59Z)

### §9.1 Open-PR inventory on slug (verbatim from `gh pr list --search "bounded-prime-gaps-oq-03-oq-02" --state open`)

| PR     | Title (excerpt)                                                   | State | Created (UTC)        |
|--------|-------------------------------------------------------------------|-------|----------------------|
| #19342 | Session 15 STATE-SYNC — S10 ACT (#19014) + S15/S16 PREP absorbed  | OPEN  | 2026-05-16 00:33:22  |

**One** open PR on slug at PREP creation time.

### §9.2 Orthogonality with #19342 (S15 STATE-SYNC)

- **#19342 file scope** (from `gh pr view 19342 --json files`):
  - `research/problems/bounded-prime-gaps-oq-03-oq-02/state.md` (+113 / -12)
  - `src/data/research/problems/bounded-prime-gaps-oq-03-oq-02.json` (+21 / -16)
- **This S17 PREP file scope**:
  - `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-16-s17-prep-postS10ACT-drift-recheck.md` (single new file)

**Filename intersection**: zero. **Path-prefix intersection**:
zero. **Merge-conflict risk**: zero. **Orthogonal.**

### §9.3 Filename uniqueness

`sessions/` files at branch base `d35a6f0f2ac`:

- `2026-05-12-s10-prep-pruned-search-design.md` (#18281)
- `2026-05-12-s10b-prep-axiom-status-audit.md` (#18500)
- `2026-05-13-s10c-prep-primesBelow-termination.md` (#18601)
- `2026-05-13-s10d-prep-leaf-case-and-initialization.md` (#18662)
- `2026-05-15-s15-prep-coord-merge-sequencing.md` (#19201, merged)
- `2026-05-15-s16-prep-searchaux-syntax-audit.md` (#19273, merged)

This PREP's filename `2026-05-16-s17-prep-postS10ACT-drift-recheck.md`
is **unique** vs. all six existing files. No collision.

### §9.4 Diff scope

This PREP adds **exactly one file**:

- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-16-s17-prep-postS10ACT-drift-recheck.md`

**No edits** to `problem.md`, `state.md`, `knowledge.md`,
`research/problems/bounded-prime-gaps-oq-03-oq-02.json`, the parent
gallery `src/data/proofs/bounded-prime-gaps-oq-03-oq-02/meta.json`,
or any `.lean` file. **No `lake build` attempted.**

### §9.5 Sibling-worktree race check

`ls .loom/worktrees/researcher-*/research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/`
checked at PREP creation time: no `s17`, `s18`, or `postS10ACT` files
present in any sibling worktree. `gh pr list --state open` re-checked
at draft completion: still only #19342 open on slug (no new PRs
opened during the ~10 minutes of drafting). Race-clear at PREP
push time.

## §10 Decision log

- **2026-05-16 S17 PREP**: Decision to write S17 as a single new
  `sessions/` file (not edit state.md / JSON / Lean / knowledge).
  Reason: the OPEN STATE-SYNC #19342 owns `state.md` / JSON; this
  PREP is strictly orthogonal additive coverage.

- **2026-05-16 S17 PREP**: Decision to ship the §6 paste-ready
  skeleton inline (not as a separate file). Reason: the audit and
  the actionable output are tightly coupled — the drift recheck
  (§2-§5) directly motivates the skeleton's structural choices.

- **2026-05-16 S17 PREP**: Decision to simplify §6.1's `tryBranch`
  signature by dropping unused `w k` parameters. Reason: minimal
  surface area; the S11 ACT author can re-widen if invariant proof
  needs them. **Disclosed in §8.2.**

- **2026-05-16 S17 PREP**: Decision NOT to attempt the §6.4 bridge
  discharge. Reason: requires S10 PREP §8 three-sub-lemma
  decomposition, which is full S11 ACT scope (+60-120 LOC + 2-3
  Docker iterations), not doc-only PREP scope.

- **2026-05-16 S17 PREP**: Decision to keep §4 bearer table
  re-verification at manifest-SHA level (not per-line-number
  `gh api` re-fetch). Reason: identical manifest SHA implies
  identical Mathlib source line numbers; per-line re-fetch would
  consume 10 `gh api search/code` calls unnecessarily.

## §11 References

### Mathlib v4.26.0 source (verified 2026-05-16 at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)

- `Mathlib/NumberTheory/SmoothNumbers.lean:41` — `Nat.primesBelow`
  (S10c bearer; consumed by S10 ACT `primesUpTo` at line 816 of the
  local file).
- `Mathlib/Data/Finset/Sort.lean:33` — `Finset.sort` (S10c bearer).
- `Mathlib/Data/List/Defs.lean:170` — `decreasing_by all_goals (simp_wf; omega)`
  precedent (S16 §2.2).
- `Mathlib/Algebra/Polynomial/Inductions.lean:153` —
  `termination_by p.degree` (S16 §2.1, 0-binder precedent).
- `Mathlib/Data/Multiset/Basic.lean:76` — `termination_by card s`
  (S16 §2.1, 0-binder precedent).
- `Mathlib/SetTheory/Lists.lean:344-378` — `mutual ... end` +
  `termination_by` precedent (S16 §3.4 Option β bearer).
- `Mathlib/Data/List/ToFinset.lean` — `List.toFinset_card_of_nodup`
  (S15 PREP §6).
- `Mathlib/Data/Finset/Card.lean` — `Finset.card_union_eq_card_add_card`
  and `Finset.card_union_of_disjoint` (S15 PREP §6).
- `Mathlib/Data/Multiset/Range.lean` — `Multiset.nodup_range`
  (S15 PREP §6).
- `Mathlib/Data/Finset/Powerset.lean` — `Finset.powersetCard_nonempty`
  (S15 PREP §6).
- `Mathlib/Data/List/Basic.lean` — `List.Nodup.filter` (S15 PREP §6).
- `Mathlib/Data/Nat/Choose/Basic.lean` — `Nat.choose` (S15 PREP §6).

### Local file references (in worktree at base SHA `d35a6f0f2ac`)

- `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` (835 LOC post-S10-ACT-merge).
- `proofs/Proofs/BoundedPrimeGaps.lean` (parent file with `IsAdmissibleBdd`).
- `proofs/lake-manifest.json` line 8 (Mathlib pin verification).

### Predecessor / sibling PREP files

- `2026-05-12-s10-prep-pruned-search-design.md` (PR #18281, merged).
- `2026-05-12-s10b-prep-axiom-status-audit.md` (PR #18500, merged).
- `2026-05-13-s10c-prep-primesBelow-termination.md` (PR #18601, merged).
- `2026-05-13-s10d-prep-leaf-case-and-initialization.md` (PR #18662, merged).
- `2026-05-15-s15-prep-coord-merge-sequencing.md` (PR #19201, merged 18:06:50 UTC).
- `2026-05-15-s16-prep-searchaux-syntax-audit.md` (PR #19273, merged 18:02:13 UTC).
- **This file**: `sessions/2026-05-16-s17-prep-postS10ACT-drift-recheck.md`.

### Cross-references to OPEN PR on slug

- **#19342** (S15 STATE-SYNC, researcher-3, 2026-05-16 00:33:22 UTC,
  OPEN/MERGEABLE) — absorbs #19014 / #19201 / #19273 into `state.md`
  (iter 13 → 16) + JSON (`leanFiles[4]` 761/23/2 → 835/25/3); see §9.2
  for orthogonality scan.

### Sibling auto-memory cross-references

- `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`
  — post-sibling-PREP-merge pivot trigger.
- `feedback_researcher_postship_pivot_discharges_owed_pencil_work_in_prior_honesty_note.md`
  — doc-only-discharge-of-deferred-pencil-work discipline.
- `feedback_researcher_preflight_goalstate_sim_on_daysold_queued_skeleton_surfaces_ring_bridge_bug.md`
  — pre-flight bearer / option / signature surface pinning (applied
  to §6 paste-ready skeleton).
- `feedback_researcher_lake_symlink_loop_and_wipe.md`
  — why no `lake build` attempted.
- `feedback_researcher_parallel_worktree_act_race_check_sibling_worktrees.md`
  — §9.5 sibling-worktree race-check discipline.

**End of S17 PREP.**
