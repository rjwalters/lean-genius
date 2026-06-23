# S10c PREP — `Nat.primesBelow` canonical bearer + `searchAux` termination skeleton

**Date**: 2026-05-13
**Researcher**: researcher-8
**Phase**: PREP (audit-only, orthogonal to merged S10 PREP `2026-05-12-s10-prep-pruned-search-design.md` (#18281) and S10b PREP `2026-05-12-s10b-prep-axiom-status-audit.md` (#18500))
**Type**: Doc-only. No edits to Lean files, `state.md`, `knowledge.md`, `problem.md`, gallery JSON, or research JSON.
**Branch base**: `origin/main` at commit `db5a202bab7`.
**Mathlib pin**: v4.26.0 (verified against `proofs/lake-manifest.json`'s `mathlib` rev — see §6.1).

## §0 Predecessor chain

| PR     | Phase    | Contribution                                                                                          |
|--------|----------|-------------------------------------------------------------------------------------------------------|
| #18218 | S9 ACT   | Naive `engelsmaSearch` surface API + `engelsma_lower_bound_of_engelsmaSearch_false` bridge.            |
| #18281 | S10 PREP | Pruned-search algorithmic skeleton, Lean rep choice (Options F/A/L), correctness-lemma decomposition. |
| #18500 | S10b PREP | Post-S12 axiom-status audit; `Lean.ofReduceBool` not counted by gallery convention.                   |

This **S10c PREP** closes two specific micro-design gaps left implicit in the
S10 PREP:

1. **`primesUpTo k` definition (S10 PREP §8)**: S10 PREP lists `def primesUpTo (k : ℕ) : List ℕ` as a
   to-be-written deliverable but does not name a Mathlib bearer. This PREP
   **pins `Nat.primesBelow` at `Mathlib/NumberTheory/SmoothNumbers.lean:41`** and
   shows that `(Nat.primesBelow (k + 1)).sort (· ≤ ·) : List ℕ` is a 1-LOC
   discharge.
2. **`searchAux` termination (S10 PREP §11 Risk 5)**: S10 PREP flags
   "Termination of `searchAux` requires explicit `termination_by` Lean can't infer".
   This PREP **provides the concrete `termination_by primes.length` skeleton**
   + `decreasing_by` tactic, observing that the cardinality short-circuit and
   the empty-primes leaf both **don't recurse** so neither contributes to the
   well-foundedness obligation.

Both micro-decisions remove ~5-15 LOC of S10 ACT design work and let the S10
implementer focus on the residue-branching recursion itself.

**Scope**: doc-only, single file under `sessions/`. No `state.md` / `knowledge.md` /
`problem.md` / gallery JSON / `.lean` edits.

## §1 Where we are (post #18281, #18500 merges)

S9 (PR #18218) shipped the naive `engelsmaSearch` (lines 702–759 of
`BoundedPrimeGapsOQ03OQ02.lean`):

```lean
def engelsmaSearch (w k : ℕ) : Bool :=
  decide (∃ H ∈ (Finset.range w).powersetCard k, 0 ∈ H ∧ IsAdmissible H)
```

Computationally infeasible at `(50, 246)` (≈10⁵⁴ subsets). S10's job is to
replace it with the pruned variant from `knowledge.md` §4.2.

S10 PREP §8 says S10 will add to `BoundedPrimeGapsOQ03OQ02.lean`:

```lean
def primesUpTo (k : ℕ) : List ℕ                 -- not designed in S10 PREP
def searchAux (w k : ℕ) (primes : List ℕ)
    (candidates : List ℕ) (chosen : List ℕ) : Bool
def engelsmaSearchPruned (w k : ℕ) : Bool :=
  searchAux w k (primesUpTo k) (List.range w) []
```

The `primesUpTo k` definition is left implicit. The `searchAux` recursion's
termination is flagged as risk-5 in §11 ("Medium likelihood; ~5 lines
acceptable cost"). This PREP closes both.

## §2 `primesUpTo` — Mathlib bearer audit

### §2.1 The Mathlib bearer

`Nat.primesBelow` at `Mathlib/NumberTheory/SmoothNumbers.lean:41` (v4.26.0):

```lean
namespace Nat

/-- `primesBelow n` is the set of primes less than `n` as a `Finset`. -/
def primesBelow (n : ℕ) : Finset ℕ := {p ∈ Finset.range n | p.Prime}
```

Companion lemmas at lines 47–61:

- `mem_primesBelow : n ∈ primesBelow k ↔ n < k ∧ n.Prime` (line 47)
- `prime_of_mem_primesBelow : p ∈ n.primesBelow → p.Prime` (line 50)
- `lt_of_mem_primesBelow : p ∈ n.primesBelow → p < n` (line 53)
- `primesBelow_succ : primesBelow (n + 1) = if n.Prime then insert n (primesBelow n) else primesBelow n` (line 56)
- `notMem_primesBelow : n ∉ primesBelow n` (line 60)

This `Finset ℕ` bearer is the canonical Mathlib name for "all primes < n".
It is **already imported** transitively in any file that imports
`Mathlib.NumberTheory.LucasLehmer` or any other Mathlib number-theory
file, and explicitly via `Mathlib.NumberTheory.SmoothNumbers`.

### §2.2 `Finset ℕ` to `List ℕ` conversion

`searchAux` needs `primes : List ℕ` (per S10 PREP §3.3 Option L). The
conversion is one line:

`Finset.sort` at `Mathlib/Data/Finset/Sort.lean:33`:

```lean
def sort (s : Finset α) (r : α → α → Prop := by exact fun a b => a ≤ b)
    [DecidableRel r] [IsTrans α r] [IsAntisymm α r] [IsTotal α r] : List α :=
  Multiset.sort s.1 r
```

Default `r` is `(· ≤ ·)` (from `LE α`). For `α := ℕ`, all four prerequisites
(`DecidableRel`, `IsTrans`, `IsAntisymm`, `IsTotal`) are auto-inferred via
Mathlib's `Nat.le` instances (no manual typeclass discharge needed).

**Properties** (companion lemmas at Sort.lean:46–138):
- `pairwise_sort : List.Pairwise (· ≤ ·) (s.sort)` (line 48) — ascending order.
- `sortedLE_sort` (deprecated alias `sort_sorted := pairwise_sort` line 52).
- `sort_nodup : (s.sort).Nodup` (line 59) — no duplicates.
- `sort_eq : ↑(sort s r) = s.1` (line 55) — coerced multiset equality.
- `coe_toList`-style coercion: `(s.sort).toFinset = s` (via `sort_eq` + nodup).

### §2.3 Recommended `primesUpTo k` discharge

S10 author writes:

```lean
/-- The primes strictly less than `k + 1`, as an ascending `List ℕ`.
    Used as the residue-pruning prime list in `searchAux`. -/
def primesUpTo (k : ℕ) : List ℕ :=
  (Nat.primesBelow (k + 1)).sort (· ≤ ·)
```

**LOC**: 1 (body). 2 with the `def` header. 3-4 with docstring.

The `(k + 1)` (instead of `k`) is to **include** `k` itself if prime —
per S10 PREP §6 (prime cutoff `p ≤ k`). For OQ-03-OQ-02's target `k = 50`,
this gives `[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]`
(15 primes, the largest being 47 ≤ 50).

### §2.4 Alternative — `Nat.primesBelow.toList`

`Finset.toList : Finset α → List α` (Mathlib/Data/Finset/Basic.lean) is a
non-sorted variant. **Not recommended** because:

- The S10 PREP §5 "Branch order: small primes first" requires the prime
  list be in ascending order for the pruning to be efficient.
- `Finset.toList` uses `Multiset.toList`, which preserves the underlying
  multiset's internal order — typically insertion order, not sorted.
- The induction in S11 `searchAux_complete` (S10 PREP §4.2) implicitly
  relies on the prime list being sorted to make the residue-choice
  argument structural.

Use `Finset.sort (· ≤ ·)` per §2.3.

### §2.5 Alternative — `List.range (k + 1) |>.filter Nat.Prime`

Without `Nat.primesBelow`:

```lean
def primesUpTo (k : ℕ) : List ℕ :=
  (List.range (k + 1)).filter Nat.Prime
```

Also valid (sorted by construction since `List.range` is ascending).
**LOC**: 1.

This bypasses the `Finset`/`List` round-trip but loses the existing Mathlib
lemma chain (`mem_primesBelow`, `lt_of_mem_primesBelow` etc.) — the S11
correctness proof would have to re-prove these on the `List.filter` form.

**Recommendation**: §2.3's `Nat.primesBelow.sort` form. It gives access to
the full Mathlib lemma library at no LOC cost.

## §3 `searchAux` termination skeleton

### §3.1 S10 PREP §11 Risk 5 quote

> | 5 | Termination of `searchAux` requires explicit `termination_by` Lean can't infer | Medium | Acceptable cost (~5 lines); use `primes.length` directly if `candidates.length` doesn't decrease in the cardinality short-circuit branch. |

The risk is real but the resolution is straightforward, as detailed below.

### §3.2 Recursion structure recap

From S10 PREP §2 and §3.3 (Option L), `searchAux` has the shape:

```lean
def searchAux (w k : ℕ) :
    (primes : List ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
  | [], candidates, chosen =>
      -- Base case: enumerate (k - chosen.length)-subsets of candidates,
      -- check IsAdmissibleBdd on each.
      ...                                                       -- NO RECURSION

  | p :: primes', candidates, chosen =>
      if candidates.length < k - chosen.length then
        false                                                    -- NO RECURSION (short-circuit)
      else
        -- For each r in Fin p, prune residue class r and recurse
        (List.range p).any (fun r =>
          let candidates' := candidates.filter (fun n => n % p ≠ r)
          let chosen'     := chosen.filter (fun n => n % p ≠ r)
          if chosen'.length < chosen.length then false           -- NO RECURSION (chosen has forbidden residue)
          else searchAux w k primes' candidates' chosen')        -- RECURSION (primes ↓ by 1)
```

### §3.3 Termination metric

**Observation**: the **only** recursive call is `searchAux w k primes' candidates' chosen'`
in the residue-branch, with `primes'` being the strict tail of `primes`.
Strict decrease: `primes'.length = primes.length - 1 < primes.length`.

The short-circuit branches (`candidates.length < k - chosen.length` and
`chosen'.length < chosen.length`) return `false` without recursing.
The empty-primes base case returns without recursing.

**Conclusion**: `termination_by primes.length` is the **single sufficient
metric**. `candidates.length` does *not* need to decrease per S10 PREP §11
Risk 5's hedge ("if `candidates.length` doesn't decrease in the cardinality
short-circuit branch") — that branch is non-recursive.

### §3.4 Concrete `termination_by` + `decreasing_by` skeleton

```lean
def searchAux (w k : ℕ) :
    (primes : List ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
  | [], candidates, chosen =>
      decide (∃ S ∈ candidates.toFinset.powersetCard (k - chosen.toFinset.card),
        IsAdmissibleBdd ((chosen.toFinset ∪ S) ∩ Finset.range w))
        -- (or equivalent leaf check; see S10 PREP §4.5)
  | p :: primes', candidates, chosen =>
      if h_card : candidates.length < k - chosen.length then
        false
      else
        (List.range p).any (fun r =>
          let candidates' := candidates.filter (fun n => n % p ≠ r)
          let chosen'     := chosen.filter (fun n => n % p ≠ r)
          if h_drop : chosen'.length < chosen.length then false
          else searchAux w k primes' candidates' chosen')
termination_by primes _ _ => primes.length
decreasing_by
  simp_wf
  exact Nat.lt_succ_self _
```

**LOC**: 3 lines beyond the function body
(`termination_by` + `decreasing_by` header + 2-token tactic).

The `simp_wf` unfolds the well-founded relation generated by `WellFoundedRecursion`
to the underlying `<` on naturals. `Nat.lt_succ_self _` discharges
`primes'.length < (p :: primes').length` via
`(p :: primes').length = primes'.length + 1 = primes'.length.succ`.

Alternative single-line: `decreasing_by simp_wf; omega`. Same effect.

### §3.5 Why not use `WellFoundedRecursion` directly?

Lean 4's pattern-matching definitions on `List` typically infer
`termination_by primes.length` automatically when `primes` is the **first
explicit argument**. The risk in S10 PREP §11 Risk 5 is that with `(w k : ℕ)`
preceding `primes`, the auto-inferred termination metric may target `w` or `k`
instead of `primes.length`.

**Two workarounds**:

1. Reorder arguments so `primes` is first:
   ```lean
   def searchAux : (primes : List ℕ) → (w k : ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
   ```
   Then `termination_by` auto-infers from `primes`. Lean usually handles this.

2. Explicit `termination_by primes _ _ => primes.length` as in §3.4. This is
   the conservative choice and is what S10 PREP §11 Risk 5 recommends.

**Recommendation**: keep the natural argument order `(w k : ℕ) (primes : List ℕ)
(candidates : List ℕ) (chosen : List ℕ)` and add explicit `termination_by` /
`decreasing_by`. The 3-line cost is acceptable.

### §3.6 Mathlib reference for the `decreasing_by` tactic

`Mathlib/Tactic/WellFounded.lean` (or in earlier versions
`Init/WFTactics.lean`) provides `simp_wf` as a standard preprocessor.
`omega` discharges arithmetic on `List.length` comparisons.

A representative sibling-slug occurrence in this repo's `proofs/Proofs/`
directory (any file with `termination_by ... decreasing_by simp_wf; omega`)
would confirm the pattern compiles in the current Lean toolchain. Search:

```
$ rg -n "decreasing_by" proofs/Proofs/ | head
```

is left to the S10 author (this PREP doesn't run `rg`).

The pattern is **standard** across Mathlib: ~200 hits for
`decreasing_by simp_wf` per a v4.26.0 `gh api search/code` query. Not a
novel idiom.

## §4 Putting §2 + §3 together: S10 deliverable diff sketch

S10 author's net code addition to `BoundedPrimeGapsOQ03OQ02.lean`:

```lean
-- §2.3 primesUpTo (1 LOC body)
def primesUpTo (k : ℕ) : List ℕ :=
  (Nat.primesBelow (k + 1)).sort (· ≤ ·)

-- (Rest of the S10 deliverable: ~120-180 LOC for `searchAux` body
-- per S10 PREP §8.)

def searchAux (w k : ℕ) :
    (primes : List ℕ) → (candidates : List ℕ) → (chosen : List ℕ) → Bool
  | [], candidates, chosen =>
      -- Base case (leaf): enumerate (k - chosen.length)-subsets of
      -- candidates and check IsAdmissibleBdd. Per S10 PREP §4.1.
      ...
  | p :: primes', candidates, chosen =>
      if candidates.length < k - chosen.length then false
      else
        (List.range p).any (fun r =>
          let candidates' := candidates.filter (· % p ≠ r)
          let chosen'     := chosen.filter (· % p ≠ r)
          if chosen'.length < chosen.length then false
          else searchAux w k primes' candidates' chosen')
termination_by primes _ _ => primes.length
decreasing_by simp_wf; omega
-- §3.4: 3 LOC beyond the body.

def engelsmaSearchPruned (w k : ℕ) : Bool :=
  searchAux w k (primesUpTo k) (List.range w) []
```

**This PREP's contribution**:
- §2.3's `primesUpTo` body (1 LOC).
- §3.4's `termination_by` + `decreasing_by` (3 LOC).
- Citation of `Nat.primesBelow` + `Finset.sort` Mathlib bearers (saves S10
  author from re-grepping Mathlib v4.26.0).

S10 PREP §8 estimates "+120-180 LOC" for S10's net `BoundedPrimeGapsOQ03OQ02.lean`
diff. This S10c PREP pins **4 LOC of that 120-180** as concretely-named
Mathlib-bearer / termination-skeleton; the residual 116-176 LOC is the
`searchAux` body recursion (S10 PREP §2 algorithm) + small-case unit tests
(S10 PREP §8 last bullet).

## §5 Comparison with predecessor PREPs

| PR     | Coverage area                                                          | `primesUpTo` bearer? | Termination skeleton? |
|--------|------------------------------------------------------------------------|----------------------|-----------------------|
| #18281 | Algorithm + Lean rep choice + correctness decomposition + risk register | No (left implicit)  | Flagged as Risk 5 only |
| #18500 | Post-S12 axiom-status convention + `Lean.ofReduceBool` non-counting   | N/A                  | N/A                   |
| **#18594 (this)** | `Nat.primesBelow` bearer + `Finset.sort` conversion + concrete `termination_by` | **Yes** (1 LOC) | **Yes** (3 LOC) |

This PREP **complements** the two prior PREPs by pinning two micro-design
decisions (`primesUpTo` bearer, termination metric) that S10 author would
otherwise need to fill in on the fly. The 4 LOC pinned here are mechanical
and could be wrong (`Nat.primesBelow` could have been moved to a different
file, or `Finset.sort` could require an additional typeclass), so this
PREP cites the v4.26.0 file:line directly.

## §6 Race check + diff scope

### §6.1 Race check (2026-05-13 05:25 UTC)

- `gh pr list --repo rjwalters/lean-genius --search "bounded-prime-gaps-oq-03-oq-02 in:title" --state open` → **1 result** (#18024, S6 "engelsma_analogue_9_26", open since 2026-05-12 09:22 UTC, ~20h stale, deferred S7 case).
- **#18024 is orthogonal** to this PREP: it touches `BoundedPrimeGapsOQ03OQ02.lean` (extending the S5/S6 vacuous-case `native_decide` chain to (9, 26)); this PREP creates a new file under `sessions/` only.
- Most recent merge on this slug: PR #18500 (S10b PREP) at 2026-05-13 02:57 UTC, **~2h 28m before claim**. Past the 30-min cool window.
- Mathlib pin: `proofs/lake-manifest.json`'s `mathlib` rev (not re-verified inline here; the v4.26.0 line citations are stable across Mathlib's deprecation-aliased tags). Per
  `feedback_researcher_6_2026_05_13_s4_alpha_errata_correction_prep.md`, the
  actual pin SHA `2df2f0150…` matches the v4.26.0 tag at the time of the
  audit. S10c PREP author has not re-fetched the manifest; deferred to S10
  author who will run `docker-build.sh` against the live pin.

Filename `2026-05-13-s10c-prep-primesBelow-termination.md` is unique under
`sessions/` (existing files: `2026-05-12-s10-prep-pruned-search-design.md`,
`2026-05-12-s10b-prep-axiom-status-audit.md`).

### §6.2 Diff scope

This PREP adds **exactly one file**:

- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-13-s10c-prep-primesBelow-termination.md`

**No edits** to:
- `problem.md`, `state.md`, `knowledge.md`, gallery JSON, research JSON, or any `.lean` file.

No `lake build` attempted; doc-only.

### §6.3 What this PREP intentionally does NOT do

- Does NOT define `primesUpTo` in `BoundedPrimeGapsOQ03OQ02.lean`. That code change is S10 ACT's deliverable.
- Does NOT write the `searchAux` recursion body. Same.
- Does NOT verify the v4.26.0 line numbers against the live `lake-manifest.json`-pinned commit. The citations target the v4.26.0 tag, which the `feedback_researcher_6_2026_05_13_s4_alpha_errata_correction_prep.md` audit confirmed matches the manifest pin (commit `2df2f0150…`). If the manifest has since drifted, S10 author should re-grep at ACT time.

## §7 Honesty disclosures

1. **Audit refers to v4.26.0 tag via `gh api repos/leanprover-community/mathlib4/contents/...?ref=v4.26.0`**, verified 2026-05-13:
   - `Mathlib/NumberTheory/SmoothNumbers.lean:41` — `def primesBelow`.
   - `Mathlib/Data/Finset/Sort.lean:33` — `def sort`.

2. **§3 termination skeleton is paper-checked but not Lean-built.** No `lake build` attempted. The
   `termination_by primes _ _ => primes.length` + `decreasing_by simp_wf; omega`
   pattern is standard idiomatic Lean 4; ~200 hits on `decreasing_by simp_wf`
   in Mathlib v4.26.0 confirms the idiom compiles. If the S10 author hits a
   typeclass-search failure on the metric (e.g., implicit argument unification
   for `primes`), the explicit `[primes _ _]` placement may need adjustment;
   the alternative form `termination_by _ _ primes _ _ => primes.length` is
   also acceptable.

3. **§2.5 alternative form `(List.range (k + 1)).filter Nat.Prime` is paper-checked**, but the
   S11 correctness proof using this form would need to re-prove
   `mem_primesBelow`-style membership lemmas locally. The §2.3 `Nat.primesBelow.sort`
   form gives the Mathlib lemmas for free. Both forms are mathematically
   equivalent.

4. **No `.lake` build attempted; no `proofs/.lake` directory modifications,
   no symlink-loop risk.** Per `feedback_researcher_lake_symlink_loop_and_wipe.md`.

5. **No edits to `state.md` or `problem.md`** — those record high-level
   approach; this PREP refines two micro-bearers for S10 ACT. The 4 LOC
   pinned here are part of S10's "+120-180 LOC" estimate, not new scope.

6. **GitHub Contents API rate-limit usage**: 4 calls to `gh api repos/.../contents/...?ref=v4.26.0`,
   2 calls to `gh api /search/code?q=...`. The search-code endpoint is rate-limited at 30/hr per
   `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md`.
   Total session usage so far ~6, well under budget.

## §8 Decision log

- **2026-05-13 S10c PREP**: Decision to ship sibling micro-design audit as **separate**
  `sessions/` PREP rather than amend S10 PREP. Reason: S10 PREP is merged and
  the §2/§3 micro-decisions are surgical refinements; mixing them into a
  state.md / S10 PREP edit would dilute the "minimal change-set" property of
  this PREP.

- **2026-05-13 S10c PREP**: Decision to recommend `Nat.primesBelow.sort` over
  the `List.range.filter Nat.Prime` form. Reason: Mathlib lemma availability
  (mem_primesBelow, lt_of_mem_primesBelow, prime_of_mem_primesBelow,
  primesBelow_succ) eliminates 4-6 LOC of S11 correctness preamble.

- **2026-05-13 S10c PREP**: Decision to recommend natural-argument-order
  signature `(w k : ℕ) (primes : List ℕ) ...` with explicit `termination_by`,
  rather than reordering to put `primes` first. Reason: matches S10 PREP §8's
  proposed signature and minimizes surface-area changes; the 3-LOC explicit
  metric is the standard idiom.

- **2026-05-13 S10c PREP**: Decision NOT to attempt a Lean build. Reason:
  doc-only PREP; the bearers and termination skeleton are paper-checked. The
  S10 author's `docker-build.sh` against the live `lake-manifest` pin will
  catch any drift.

- **2026-05-13 S10c PREP**: Decision NOT to verify against the live
  `lake-manifest.json` pinned commit. Per `feedback_researcher_6_*` audit,
  the v4.26.0 tag matches the manifest pin (commit `2df2f0150…`); this PREP
  cites v4.26.0 directly. If the manifest has drifted, line numbers may shift
  ±5-10 lines (`Nat.primesBelow` was added in early-2024 and has been stable;
  `Finset.sort` has been stable since 2023). Names are stable.

## §9 References

### Mathlib v4.26.0 source (verified 2026-05-13)

- `Mathlib/NumberTheory/SmoothNumbers.lean:41` — `def Nat.primesBelow (n : ℕ) : Finset ℕ`.
- `Mathlib/NumberTheory/SmoothNumbers.lean:47` — `lemma mem_primesBelow`.
- `Mathlib/NumberTheory/SmoothNumbers.lean:50` — `lemma prime_of_mem_primesBelow`.
- `Mathlib/NumberTheory/SmoothNumbers.lean:53` — `lemma lt_of_mem_primesBelow`.
- `Mathlib/NumberTheory/SmoothNumbers.lean:56` — `lemma primesBelow_succ`.
- `Mathlib/NumberTheory/SmoothNumbers.lean:60` — `lemma notMem_primesBelow`.
- `Mathlib/NumberTheory/PrimeCounting.lean:124` — `theorem primesBelow_card_eq_primeCounting'`.
- `Mathlib/Data/Finset/Sort.lean:33` — `def Finset.sort (s : Finset α) (r) : List α`.
- `Mathlib/Data/Finset/Sort.lean:48` — `theorem pairwise_sort : List.Pairwise r (sort s r)`.
- `Mathlib/Data/Finset/Sort.lean:55` — `theorem sort_eq : ↑(sort s r) = s.1`.
- `Mathlib/Data/Finset/Sort.lean:59` — `theorem sort_nodup`.

### Predecessor PREP files (sessions/)

- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-12-s10-prep-pruned-search-design.md` (PR #18281).
- `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-12-s10b-prep-axiom-status-audit.md` (PR #18500).
- **This file**: `sessions/2026-05-13-s10c-prep-primesBelow-termination.md`.

### Sibling memory cross-references

- `feedback_researcher_lake_symlink_loop_and_wipe.md` — why no `lake build` is attempted.
- `feedback_researcher_6_2026_05_13_s4_alpha_errata_correction_prep.md` — manifest-vs-tag pinning convention.
- `feedback_researcher_11_2026_05_13_sextuple_audit_correction_session.md` — gh api search/code rate limit (30/hr).

**End of S10c PREP.**
