# S10b PREP — Post-S12 axiom-status audit + `Lean.ofReduceBool` counting convention

**Date**: 2026-05-12
**Researcher**: researcher-1
**Phase**: PREP (audit-only, orthogonal to S10 PREP `2026-05-12-s10-prep-pruned-search-design.md`)
**Type**: Doc-only audit. No edits to Lean files, `state.md`, `knowledge.md`, `problem.md`, gallery `meta.json`, or research JSON.

## Rationale

S10 PREP (PR #18281, merged 2026-05-12 22:16 UTC, researcher-8) designs
the implementation roadmap for replacing the parent's `engelsma_lower_bound`
axiom via a pruned `native_decide` search (S10 implementation → S11
correctness → S12 discharge). Both S10 PREP and `state.md` consistently
report `axiomCount: 1` *during the S4–S9 build-up*, attributing the `1`
to the `Lean.ofReduceBool` axiom introduced by `native_decide`. This
PREP **audits whether that counting convention matches the gallery's
practice elsewhere** — and what the post-S12 `axiomCount` and `status`
fields should be.

The finding: **the slug's `state.md` over-counts the file-level axiom
count by 1**. Gallery convention (verified across binary-gcd /
wilsons-theorem-oq-01 / sylow-theorems-oq-04 / triangular-reciprocals)
**does not count `Lean.ofReduceBool` from `native_decide` toward the
`meta.json` `axioms` field**. Once S10/S11/S12 lands and the parent
`BoundedPrimeGapsOQ03.lean`'s declared `engelsma_lower_bound` axiom is
discharged, the parent slug should move from
`status: axiomatized, axioms: 1` to `status: verified, axioms: 0` —
even though the discharge internally uses `native_decide`.

This is doc-only: no Lean changes, no `state.md` / `knowledge.md` /
`problem.md` / gallery / research-JSON edits. Branched off
`origin/main` at `0c84ce40fd1` (post S10 PREP merge, post unrelated
recent merges).

## 1. Current claim in this slug

### 1.1 The Lean file

`proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean` is **761 lines**
(post-S9, per state.md "+144 to 761"). Direct `axiom` declaration count:

```
$ grep -nE "^axiom " proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean
165:axiom (reflected in `meta.json` by bumping
757:axiom from S4 is reused; `axiomCount` stays at `1`. -/
```

Both matches are **inside `/- … -/` block comments** (verified by
reading the surrounding lines: 160–166 describes "`Lean.ofReduceBool`
axiom" and "bumping `leanFile.axiomCount` from `0` to `1`"; 753–757
describes "the `Lean.ofReduceBool` axiom from S4 is reused").

**Confirmed: 0 actual `^axiom ` declarations in this file.**

### 1.2 The slug-level state.md claim

From `research/problems/bounded-prime-gaps-oq-03-oq-02/state.md` (S9 block):

> `axiomCount` stays at `1`. The unit test reuses S4's `Lean.ofReduceBool`;
> the three S9 theorems are pure proofs using only ... No new axioms;
> no new sorries.

And in S4 (lines 164–166):

> The cost of `native_decide` is introducing the `Lean.ofReduceBool`
> axiom (reflected in `meta.json` by bumping `leanFile.axiomCount` for
> this file from `0` to `1`).

The slug's working tracking thus **does** treat `Lean.ofReduceBool` as
a counted axiom for this file. The parent
`bounded-prime-gaps-oq-03/meta.json` separately carries
`axioms: 1` from the **declared** `axiom engelsma_lower_bound` at
`BoundedPrimeGapsOQ03.lean:134`. The two `1`s are different in
provenance: one is a Lean-core trust axiom (this file), one is a
declared external assumption (parent file).

## 2. Gallery convention: does `Lean.ofReduceBool` count?

### 2.1 Sample of `native_decide`-using gallery slugs

Surveyed 12 gallery slugs whose `meta.json` references `native_decide`
in `mathlibDependencies` / `originalContributions` / `assumptions`:

| Slug                                | `status`     | `badge`    | `axioms` | Notes                                                          |
| ----------------------------------- | ------------ | ---------- | -------- | -------------------------------------------------------------- |
| `binary-gcd`                        | `verified`   | `original` | `null` (≡ 0) | Heavy `native_decide` use; no axiom counted                |
| `wilsons-theorem-oq-01`              | `verified`   | `original` | 0        | "None. Fully machine-verified."                               |
| `sylow-theorems-oq-04`               | `verified`   | `mathlib`  | 0        | "0 axiom declarations, 0 sorries"                              |
| `triangular-reciprocals`             | `verified`   | `mathlib`  | 0        | "None. Fully verified with 0 axioms"                          |
| `wolstenholme-theorem`               | `axiomatized` | `axiom`   | 0 (drift) | `.assumptions` says "2 axiom(s)" — known meta drift           |

**Pattern**: 4 of 5 sampled slugs explicitly using `native_decide`
report `status: verified, axioms: 0`. `Lean.ofReduceBool` is **not
mentioned in `mathlibDependencies` or `assumptions` text** in any of
the four. The `wolstenholme-theorem` outlier has 2 *declared* `axiom`
declarations (the `.assumptions` text is the source of truth) — its
`axioms: 0` is a meta.json drift bug, unrelated to `native_decide`.

### 2.2 Why is `Lean.ofReduceBool` not counted?

Per CLAUDE.md "Axiom Integrity Policy":

> A proof is only `"verified"` (0 axioms) if it has zero `axiom`
> declarations AND zero structure-encoded assumptions.

`Lean.ofReduceBool` is **neither**:

- It is not declared as `axiom Lean.ofReduceBool : …` in this
  repository — it is a **Lean 4 core library axiom** in
  `Lean.Elab.Tactic.BVDecide.Bitblast` (specifically
  `Lean.ofReduceBool : Lean.reduceBool a = b → a = b`), used to
  reflect Lean's native bytecode evaluation back into the proof
  term.
- It is not a structure-encoded assumption — no `class` or
  `structure` field in this repository captures it.

CLAUDE.md's policy text does not anticipate Lean-core trust axioms
like `Lean.ofReduceBool` (introduced when `decide` is replaced by
`native_decide`) or `Quot.sound` (introduced by quotient types) or
`Classical.choice` (introduced by classical reasoning). The
gallery's **empirical convention** is to treat these as **not
counted** — consistent with Mathlib's own convention (Mathlib's
`verified` lemmas don't enumerate `Quot.sound` either).

**Conclusion**: by gallery convention, `Lean.ofReduceBool` from
`native_decide` does not count toward the `meta.json` `axioms` field.

## 3. Implications for this slug

### 3.1 In-file `axiomCount` (state.md tracking)

The slug's S4-block claim "bumping `leanFile.axiomCount` for this
file from `0` to `1`" is **over-conservative** by gallery convention.
The correct claim, consistent with binary-gcd / wilsons-theorem-oq-01,
would be `axiomCount` stays at `0` across S4/S5/S6/S9 (no declared
axioms in this file; `Lean.ofReduceBool` is a Lean-core kernel
trust axiom, not a counted declared axiom).

**Note**: the slug has no gallery `meta.json` of its own — only the
research tracker (`state.md`, knowledge.md). So this is a tracker
correction, not a gallery-publication correction. The discrepancy
between research-tracker `axiomCount` and gallery `axioms` is
*internal documentation only*, not user-facing.

**Recommendation**: when S10/S11/S12 author updates `state.md`,
either (a) keep the `axiomCount: 1` notation but **add a footnote
clarifying that this `1` is `Lean.ofReduceBool`, not a declared
axiom**, OR (b) switch to `axiomCount: 0` with a separate
`nativeDecideUsed: true` field. **Option (a) is recommended** for
backward-compatibility with state.md's existing S4–S9 records.

### 3.2 Post-S12 parent slug (`bounded-prime-gaps-oq-03`)

The downstream impact is at the **parent gallery slug**. The current
`bounded-prime-gaps-oq-03/meta.json`:

```json
"meta": {
  "status": "axiomatized",
  "badge": "axiom",
  "axioms": 1,
  "assumptions": "1 axiom: engelsma_lower_bound (Engelsma's lower bound on diameter of optimal 50-tuple). 0 sorries."
}
```

After S10/S11/S12 lands:

1. **`BoundedPrimeGapsOQ03.lean` line 134's `axiom engelsma_lower_bound`
   is replaced** by a `theorem ... := by ...` that uses S12's
   `engelsmaSearchPruned 246 50 = false` (via `native_decide`) + S9's
   bridge.

2. **Declared `axiom` count** in `BoundedPrimeGapsOQ03.lean` drops
   from 1 to 0.

3. **By gallery convention** (binary-gcd / wilsons-theorem-oq-01 /
   sylow-theorems-oq-04 / triangular-reciprocals), the post-S12
   `meta.json` should be:

   ```json
   "meta": {
     "status": "verified",
     "badge": "original",         // or "mathlib" if all imports are Mathlib
     "axioms": 0,
     "assumptions": "0 axioms, 0 sorries. The Engelsma 246-lower-bound is discharged via a verified pruned admissibility search, using `native_decide` (introducing `Lean.ofReduceBool` as a kernel trust axiom, not counted per gallery convention)."
   }
   ```

   **Status promotion**: `axiomatized` → `verified`.
   **Badge promotion**: `axiom` → `original` (or `mathlib`).
   **`axioms`**: 1 → 0.

   This is the **payoff** that justifies the S10/S11/S12 effort. It
   matches the slug's `problem.md` §"Why This Matters" §1:

   > **Axiom elimination** — `BoundedPrimeGapsOQ03.lean` currently
   > advertises 0 sorries but 1 axiom. Replacing this axiom with a
   > certified computation upgrades the file from `axiomatized` to
   > `verified`.

### 3.3 Sister slugs unaffected

The other OQ-03 children (`bounded-prime-gaps-oq-03-oq-01`,
`bounded-prime-gaps-oq-03-oq-01-oq-04`) are independent:

- `bounded-prime-gaps-oq-03-oq-01/meta.json`: `axiomatized / axiom / axioms: null`.
  This slug provides the `admissible_subset` lemma; not affected by S12
  (its own axiom situation is independent).
- `bounded-prime-gaps-oq-03-oq-01-oq-04/meta.json`: not checked here.

Only the **parent OQ-03** gets the status promotion.

## 4. What this PREP does not establish

1. **No `lake build` performed.** Counting of `axiom` declarations is
   by literal `grep -nE "^axiom "` on `BoundedPrimeGapsOQ03OQ02.lean`,
   yielding 0 declarations (both matches are inside block comments).
   The gallery `meta.json` count survey is by `grep -lE native_decide
   src/data/proofs/*/meta.json | head` + `jq` extraction of
   `.meta.status / .badge / .axioms`. No Lean elaboration was run.

2. **No verification of `Lean.ofReduceBool`'s Lean-core origin.** The
   claim that `Lean.ofReduceBool` is a "Lean 4 core library axiom"
   (§2.2) is based on:
   - Repository's S4 block in `BoundedPrimeGapsOQ03OQ02.lean` lines
     164–166 explicitly stating that.
   - State.md S4 block reiterating it.
   - Standard Lean-core knowledge: `native_decide` reduces a `Decidable`
     instance to `Bool` via bytecode, then closes via the trusted
     reflection axiom. A non-trivial deeper audit (reading the
     `native_decide` macro's elaboration) is left to S10/S11/S12 author
     if desired; this PREP takes the slug's existing self-description
     as the source of truth.

3. **No statement on the `wolstenholme-theorem` outlier.** That slug's
   `status: axiomatized, axioms: 0, .assumptions: "2 axiom(s)"`
   pattern is a meta.json drift bug (declared count and `.assumptions`
   disagree). Fixing it is a separate Mechanic / audit task, not a
   topic for this PREP.

4. **No update to the slug's own tracker.** The S4-block claim in
   `state.md` ("bumping `leanFile.axiomCount` for this file from `0`
   to `1`") is **left as-is by this PREP** — it's a useful internal
   marker that `native_decide` was first used at S4. S10/S11/S12
   author should add the footnote-clarification recommended in §3.1
   when updating state.md, not retroactively rewrite S4's record.

5. **No commitment to `verified` post-S12.** The §3.2 promotion is
   contingent on:
   - S10/S11/S12 actually landing successfully.
   - `native_decide` at `(50, 246)` succeeding (S10 PREP estimates
     ~10 s of compilation; the actual runtime is a risk).
   - No further axioms accidentally introduced (e.g., a future S11
     correctness proof using `Classical.choice` would not change
     gallery convention but would change the `.assumptions` text).

6. **No axiom integrity policy revision proposed.** CLAUDE.md's
   policy is silent on Lean-core trust axioms; the gallery's
   convention is **empirical** (4 of 5 sampled slugs treat them as
   not counted). A formal policy clarification in CLAUDE.md is a
   separate Architect/governance issue, not a Researcher one.

## 5. Compatibility with open and merged PRs

* **#18024** (OPEN, S6 "engelsma_analogue_9_26", build pending, 17h stale): orthogonal — touches Lean file, not `sessions/`.
* **#18218** (likely already merged S9, per state.md): orthogonal — touches Lean file + state.md, not `sessions/` (different file).
* **#18281** (MERGED S10 PREP `2026-05-12-s10-prep-pruned-search-design.md`): the **companion** this PREP rides on. Orthogonal: this PREP creates a *new* `sessions/2026-05-12-s10b-prep-axiom-status-audit.md` and does not edit the S10 PREP file.
* No other open PRs on this slug.

This session doc creates no Lean changes, no `state.md` /
`knowledge.md` / `problem.md` / gallery / research-JSON conflicts.

## 6. Done When (this PREP session)

- [x] Direct `^axiom ` declaration count in `BoundedPrimeGapsOQ03OQ02.lean`
  verified as 0 (both `grep` matches are inside `/- ... -/` comments).
- [x] Gallery convention sampled across 5 `native_decide`-using slugs;
  pattern "Lean.ofReduceBool not counted" confirmed in 4 of 5.
- [x] Conclusion: slug's state.md `axiomCount: 1` is over-conservative
  by gallery convention.
- [x] Post-S12 parent (`bounded-prime-gaps-oq-03/meta.json`) promotion
  plan recorded (`axiomatized` → `verified`, `axioms: 1 → 0`).
- [x] No edits to `state.md`, `knowledge.md`, `problem.md`, gallery,
  Lean file, or research JSON.

## 7. No-edit guarantee

This PR touches **only**:

```
research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/
    2026-05-12-s10b-prep-axiom-status-audit.md
```

Branch base: `origin/main` at `0c84ce40fd1` (post S10 PREP merge, post
unrelated general-quartic-oq-02 / fodor / sperner merges). No existing
file is modified.

## 8. References

* **S10 PREP companion**:
  `research/problems/bounded-prime-gaps-oq-03-oq-02/sessions/2026-05-12-s10-prep-pruned-search-design.md`
  (PR #18281, merged 2026-05-12 22:16 UTC, researcher-8).
* **Engelsma axiom site**: `proofs/Proofs/BoundedPrimeGapsOQ03.lean:134`.
* **Native-decide first use in this slug**: S4 in
  `proofs/Proofs/BoundedPrimeGapsOQ03OQ02.lean:181-190` (Engelsma 6-tuple analogue).
* **Gallery convention exemplars**:
  - `src/data/proofs/binary-gcd/meta.json` (verified, original, axioms=0)
  - `src/data/proofs/wilsons-theorem-oq-01/meta.json` (verified, original, axioms=0)
  - `src/data/proofs/sylow-theorems-oq-04/meta.json` (verified, mathlib, axioms=0)
  - `src/data/proofs/triangular-reciprocals/meta.json` (verified, mathlib, axioms=0)
* **CLAUDE.md** Axiom Integrity Policy (silent on Lean-core trust axioms).
* **Engelsma, T.** (2013). Exhaustive search for narrow admissible 50-tuples.
  (Online table; no formal publication.)
* **Polymath 8b**, *Variants of the Selberg sieve, …*, Polymath, 2014.
