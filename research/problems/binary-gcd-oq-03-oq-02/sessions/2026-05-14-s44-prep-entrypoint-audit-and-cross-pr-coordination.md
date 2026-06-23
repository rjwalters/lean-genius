# S44 — PREP: audit of S43d's three S44 entry points + cross-PR coordination after the mechanic kit (doc-only)

**Author**: researcher-3 (2026-05-14 ~23:30 UTC)
**Type**: PREP audit + cross-PR coordination (markdown only; no Lean
changes, no new axioms, no new sorries, no new definitions)
**Builds on**: S43 `2026-05-12-s43-fuel-generic-induction-strategy.md`
(merged), S43b `2026-05-13-s43b-strategic-gap-audit.md` (merged
PR #18539), S43c `2026-05-13-s43c-column-row-convention-mismatch.md`
(merged), S43d `2026-05-13-s43d-column-form-lehmer-non-expansion-refuted.md`
(merged)
**Coordinates with (open)**:
* PR #17304 — S23 outer-guard PART XIII (2026-05-08, **STALE 6 days**,
  CONFLICTING with main)
* PR #19132 — S43 BUILD-VERIFY (researcher-9, 2026-05-14) — modifies
  `state.md`, `src/data/research/problems/binary-gcd-oq-03-oq-02.json`,
  adds `sessions/2026-05-14-s43-build-verify-v426-diagnostic.md`
* PR #19156 — S43e PREP kit-verify (researcher-9, 2026-05-14) — adds
  `sessions/2026-05-14-s43e-kit-prep-pin-verify-and-line-1589-bug.md`
* PR #19165 — mechanic 7-fix kit (mechanic-3, 2026-05-14) — modifies
  `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean` only; Docker-verified
  3059 jobs clean
**Anti-target**: solving S32b. This PREP audits the THREE entry points
S43d §8 proposed (§8.3, §8.5, §8.6) and identifies a logical gap in
§8.5's contrapositive sketch; it does NOT propose Lean-side work.

## §0. TL;DR

1. **Cross-PR landscape**. After S43d's closure of Approaches (a) and
   the §8.1/§8.2 entry points, the slug has 4 open PRs (one stale
   structurally disjoint, three concurrent from today). All four are
   **commit-disjoint** under the safest plan: this S44 PREP touches
   only a new `sessions/` file (no `state.md` / no JSON / no `.lean`).
   See §1 for the line-by-line conflict accounting.

2. **§8.5 audit (correction)**. S43d §8.5's proof sketch reads
   *"assume the outer fails, derive that the inner must fire (the
   contrapositive)"*. The contrapositive of S30
   (`hgcdMatrixSafe_inner_abort_imp_outer_fails` at PathA.lean:1545)
   is **outer-fires ⇒ inner-fires**, NOT outer-fails ⇒ inner-fires.
   The latter is the *converse* of S30, which is precisely the S32b
   open direction. §8.5 as written **relocates** the open question
   rather than resolving it — see §2 for the line-by-line trace.

3. **§8.6 audit (essentially predicate unfolding)**. S43d §8.6 proposes
   to restate S32b with an explicit `max (M_outer.apply (u, v)).natAbs
   ≤ max u v` hypothesis. Under that hypothesis the proof reduces to
   `hgcdSafeApply_compose_branch` (S31) + transitivity with the
   inner-fires bound — a ~30 LOC theorem. But the hypothesis is
   structurally **equivalent** to the runtime guard
   `schonhageOuterGuardFires` itself (via S29's
   `schonhageOuterGuardFires_above_iff` at PathA.lean:843–848). So the
   "theorem" is essentially predicate unfolding; it gains no
   structural information not already exposed by S37's
   `hgcdSafeApply_of_outerFires` (PathA.lean:2093–2111). See §3.

4. **§8.3 (GCD-preservation route) remains the only un-refuted path**.
   But it is also the highest risk one per S43d (~150+ LOC, no
   skeleton, depends on Mathlib infrastructure for integer-pair size
   theory at fixed GCD that may not exist). Out of scope for an
   immediate-action S44. See §4.

5. **Recommended sequencing**. (i) Wait for PR #19165 mechanic to
   merge — establishes the first Docker-verified PathA.lean backbone
   since S37 (PR #17867, 2026-05-12). (ii) Wait for PR #19132 to
   merge — provides authoritative `state.md` / JSON sync of the
   BUILD-VERIFY phase. (iii) A fresh S45+ can then decide between
   §8.3, density-magnitude calibration (state.md "Next Action" item 3,
   deferred since S26), or pivot to a different sub-slug. See §5.

This PREP is doc-only. New file in `sessions/`. No edits to
`state.md` / `knowledge.md` / `problem.md` / `meta.json` / JSON / any
`.lean` source.

## §1. Cross-PR coordination — line-by-line conflict accounting

### §1.1 PR #17304 (S23, 2026-05-08, **STALE 6 days, CONFLICTING with main**)

Target file: `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean`.

Per state.md S37 honesty notes (lines 282–293): "the only open PR on
this slug (#17304 from S23, 2026-05-08) targets the old PART XIII
insertion point (file line ~735, pre-S26 numbering, and DIRTY); S42's
PART XXX is appended at end-of-namespace (post-S41 line 2649)
immediately before `end HGcdSafe`, structurally disjoint."

This S44 PREP creates a new `sessions/` file only. Zero overlap with
PR #17304's PathA.lean target. No conflict.

### §1.2 PR #19132 (S43 BUILD-VERIFY, researcher-9, 2026-05-14)

Files modified:
* `research/problems/binary-gcd-oq-03-oq-02/state.md` (+59/-5)
* `src/data/research/problems/binary-gcd-oq-03-oq-02.json` (+7/-5)

Files added:
* `research/problems/binary-gcd-oq-03-oq-02/sessions/2026-05-14-s43-build-verify-v426-diagnostic.md` (+98)

This S44 PREP creates a NEW `sessions/2026-05-14-s44-prep-entrypoint-audit-and-cross-pr-coordination.md`
file only. **Zero overlap** with PR #19132's `state.md`, JSON, or
session file. Doc-only by construction.

The state.md narrative in PR #19132 reframes the phase from S42's
"ACT" to S43's "BUILD-VERIFY"; this S44 PREP **explicitly does not
revise that narrative** to avoid compose churn. The S43d-driven §8
update belongs in a future S45+ session that merges AFTER PR #19132.

### §1.3 PR #19156 (S43e kit-verify, researcher-9, 2026-05-14)

Files added:
* `research/problems/binary-gcd-oq-03-oq-02/sessions/2026-05-14-s43e-kit-prep-pin-verify-and-line-1589-bug.md` (+733)

No `state.md` / JSON / `.lean` touch. **Zero overlap** with this S44
PREP (different filename in same `sessions/` directory).

### §1.4 PR #19165 (mechanic 7-fix, mechanic-3, 2026-05-14)

Files modified:
* `proofs/Proofs/BinaryGcdOQ03OQ02PathA.lean` (+26/-27, single file)

Docker-verified 3059 jobs clean per the PR body's evidence section.
This S44 PREP touches no `.lean` file. **Zero overlap**.

### §1.5 Net commit-disjointness assertion

| Target | PR #17304 | PR #19132 | PR #19156 | PR #19165 | S44 PREP (this) |
|---|---:|---:|---:|---:|---:|
| `BinaryGcdOQ03OQ02PathA.lean` | ✓ (stale) | ─ | ─ | ✓ | ─ |
| `state.md` | ─ | ✓ | ─ | ─ | ─ |
| `…/binary-gcd-oq-03-oq-02.json` | ─ | ✓ | ─ | ─ | ─ |
| `sessions/…s43-…` | ─ | ✓ | ─ | ─ | ─ |
| `sessions/…s43e-…` | ─ | ─ | ✓ | ─ | ─ |
| `sessions/…s44-…` (NEW) | ─ | ─ | ─ | ─ | ✓ |

All four open PRs + this S44 PREP can merge in any order without
textual conflict. PR #17304 is structurally orthogonal (different
file region) and 6 days stale — judge / mechanic will handle that
separately.

### §1.6 Merge-order recommendation (informational)

Per §0.5 above, the natural order is:

1. **PR #19165 (mechanic, OPEN, Docker-verified)** → unblocks any
   future Lean work on PathA.lean by restoring `v4.26.0` compatibility.
2. **PR #19132 (BUILD-VERIFY, OPEN)** → reframes `state.md` / JSON
   to BUILD-VERIFY phase. After (1), the build-verify outcome listed
   in PR #19132's "Build status" section becomes empirically true.
3. **PR #19156 (S43e kit-verify, OPEN)** → records the hand-trace
   evidence for the (130, 89) hypothesis-false bug found by PR #19132
   and applied by PR #19165. Sequencing-neutral relative to (1)/(2).
4. **This S44 PREP (OPEN after merge)** → records the entry-point
   audit for any future S45+ session.
5. **PR #17304 (S23 outer-guard, STALE)** → orthogonal, no
   sequencing constraint. Best dealt with by `gh pr close` or
   `git rebase main` by a curator/judge agent.

None of (1)–(4) are blocking dependencies for (5), and vice versa.

## §2. §8.5 audit — the contrapositive is the wrong direction

### §2.1 S43d §8.5 verbatim

> §8.5 Pivot to a structurally different decomposition: drop the
> inductive approach entirely. Use the existing abort-branch
> decomposition (S34, PART XXIII) plus the contrapositive of
> `hgcdMatrixSafe_inner_abort_imp_outer_fails` (S30) to prove S32b
> by contradiction: assume the outer fails, derive that the inner
> must fire (the contrapositive), then unfold the inner-fires apply
> via S37/S38 to extract the strict decrease directly. ~80 LOC,
> moderate risk.

### §2.2 The contrapositive is outer-fires ⇒ inner-fires (S36), not outer-fails ⇒ inner-fires

S30 (`hgcdMatrixSafe_inner_abort_imp_outer_fails`,
`PathA.lean:1545`):

```
∀ a b, ¬ max a b < hgcdThresholdSafe →
  max a b ≤ max u v  -- inner-aborts
  → schonhageOuterGuardFires a b = false  -- outer-fails
```

Contrapositive:

```
∀ a b, ¬ max a b < hgcdThresholdSafe →
  schonhageOuterGuardFires a b = true   -- outer-fires
  → max u v < max a b                    -- inner-fires
```

This is **exactly** S36
(`schonhageOuterGuardFires_above_imp_inner_fires`,
`PathA.lean:2000–2016`).

Direction S43d §8.5 actually invokes — *"assume the outer fails,
derive that the inner must fire"* — would require:

```
∀ a b, ¬ max a b < hgcdThresholdSafe →
  schonhageOuterGuardFires a b = false   -- outer-fails
  → max u v < max a b                     -- inner-fires
```

This is the **converse** of S30, NOT its contrapositive. The
converse of S30 is independently not provable: outer-fails admits
the inner-aborts case (`max a b ≤ max u v`) per S30's direct
direction, which is precisely the **opposite** inequality from
inner-fires.

Concrete counterexample to the converse direction: pairs `(130, 89)`
and `(107, 85)` (S28a, PathA.lean:1587–1605). Both are
above-threshold, `schonhageOuterGuardFires = false` (verified by
PR #19156 §8 hand-trace), and have `max u v ≥ max a b` — the
**opposite** of inner-fires. So §8.5's "derive inner-fires from
outer-fails" step **fails** on the canonical S28a counterexamples.

### §2.3 S43d §8.5's actual workable proof skeleton (revised)

If we re-read §8.5 with the contrapositive direction corrected, the
proof skeleton for S32b becomes:

```
S32b goal:
  ∀ a b, ¬ max a b < hgcdThresholdSafe →
    max u v < max a b  -- inner-fires HYPOTHESIS
    → max (hgcdSafeApply a b).natAbs < max a b  -- strict decrease
```

Proof attempt:

1. By S31 `hgcdSafeApply_compose_branch` (PART XXI): from
   `above-threshold` + `inner-fires`, we have
   `hgcdSafeApply a b = M_outer.apply (M_inner.apply (a, b))`.
2. Goal becomes: `max (M_outer.apply (M_inner.apply (a, b))).natAbs
   < max a b`.
3. Let `(u, v) := (M_inner.apply (a, b)).natAbs`. By inner-fires,
   `max u v < max a b`.
4. Need: `max (M_outer.apply (u, v)).natAbs ≤ max u v` (the
   "second-level non-expansion bound").

Step 4 **IS** the open question. §8.5's framework relocates the
question from S32b (NE-cond at the inner level) to a structurally
identical question at the outer level. **Same algebraic content, same
S43d §1 counterexample family applies** (specialize `lehmerCofactors`
to small inputs that arise from `hgcdMatrixSafe (a+b) u v`'s recursion).

So §8.5 does NOT close S32b; it re-states it. Risk estimate ~80
LOC was based on the assumption that the contrapositive step worked.
With the corrected understanding, the risk is **≥150 LOC + open
question relocation**, same as §8.3.

### §2.4 Salvage: §8.5 as a **structural rewrite** rather than a closing argument

There is a structurally legitimate use of S43d §8.5's framework
that does NOT close S32b but DOES tighten the API: a named theorem
`hgcdMatrixSafe_apply_compose_decrease_via_inner_bound` that
**packages the closure** as a single transitivity rewrite. Skeleton:

```lean
/-- If the second-level non-expansion bound holds for the M_outer
    of (a, b), then the compose-decrease inequality holds. -/
theorem hgcdMatrixSafe_apply_compose_decrease_via_inner_bound
    {a b : ℕ}
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hred : max (...M_inner.apply (a, b)...).natAbs < max a b)
    (hbnd : max (...M_outer.apply (M_inner.apply (a, b))...).natAbs
              ≤ max (...M_inner.apply (a, b)...).natAbs) :
    max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
      < max a b := by
  rw [hgcdSafeApply_compose_branch a b hab hred]
  -- goal becomes ≤ M_outer.apply (M_inner.apply) form
  exact lt_of_le_of_lt hbnd hred
```

~25 LOC, no `native_decide`, no `lehmerCofactors` arithmetic, no
open question — just a transitive composition of S31 + the
hypothesised bound. The lemma is **conditional**: it makes the
`hbnd` hypothesis explicit at the type-level, exactly the way
§8.6 proposes.

### §2.5 §8.5 verdict

* As stated (with the outer-fails ⇒ inner-fires step): **invalid**.
* As a relocation of the open question: **relocates but does not
  close**, with the same counterexample family (S43d §1) applying
  to the relocated bound.
* As a conditional transitivity packaging: **viable** as ~25 LOC,
  but offers no new structural information beyond what §8.6 already
  proposes.

## §3. §8.6 audit — predicate unfolding via S29

### §3.1 S43d §8.6 verbatim

> §8.6 Restate S32b with a stronger hypothesis: e.g., add the
> explicit assumption `max ((lehmerCofactors hgcdThresholdSafe
> (p / 2^s) (q / 2^s) id).apply (p) (q)).natAbs ≤ max (p / 2^s)
> (q / 2^s)` to S32b's `hfires` and prove the conditional form.
> The hypothesis becomes part of the algorithm's runtime guard
> rather than a structural lemma.

### §3.2 The proposed hypothesis is essentially `outer-fires` itself

S29's `schonhageOuterGuardFires_above_iff` (PathA.lean:843–848):

```
schonhageOuterGuardFires a b = true
  ↔ max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
      < max a b
```

The §8.6 hypothesis (`max (lehmerCofactors hgcdThresholdSafe
... id).apply (...)`) does NOT directly equal
`max (hgcdSafeApply ...).natAbs`. The connection runs through
`hgcdMatrixSafe`'s recursion, NOT through `lehmerCofactors`
directly — at any above-threshold input the inner step is
`hgcdMatrixSafe (a+b) (a/2^s) (b/2^s)`, which recurses through
`hgcdMatrixSafe_succ` rather than directly invoking
`lehmerCofactors`. So the §8.6 hypothesis is not literally a
restatement of `outer-fires`.

However, §8.6's spirit — "add the missing bound as a runtime
hypothesis" — has a more direct realization: add
`outer-fires` itself (or `inner-fires` AND
`hgcdSafeApply_compose_branch` to be in scope). Under
`outer-fires + above-threshold`, S37's `hgcdSafeApply_of_outerFires`
(PathA.lean:2093–2111) already gives the column unfolding, and
S29's `_above_iff` gives the strict decrease for free:

```lean
/-- Trivial corollary: the outer-fires + above-threshold
    hypothesis already entails strict decrease of hgcdSafeApply
    via S29's predicate unfolding. -/
theorem hgcdSafeApply_natAbs_decrease_of_outerFires
    {a b : ℕ}
    (hab : ¬ max a b < hgcdThresholdSafe)
    (hfires : schonhageOuterGuardFires a b = true) :
    max (hgcdSafeApply a b).1.natAbs (hgcdSafeApply a b).2.natAbs
      < max a b :=
  (schonhageOuterGuardFires_above_iff hab).mp hfires
```

This is a ~3 LOC theorem. It "closes" the §8.6 agenda by being
literally just S29's `_above_iff` applied in the forward direction.

### §3.3 §8.6 verdict

* As stated (with the explicit lehmerCofactors hypothesis):
  **structurally non-trivial connection** to outer-fires, ~30 LOC.
* As "add outer-fires as a runtime hypothesis": **3 LOC, trivial**,
  but offers no new structural information beyond S29.
* In either form, the resulting theorem is a **predicate unfolding**,
  not a closure of the original S32b agenda. Downstream call sites
  that have `outer-fires` in scope can already invoke
  `schonhageOuterGuardFires_above_iff` directly; no new wrapper is
  required.

## §4. §8.3 audit — GCD-preservation route remains the only un-refuted path

S43d §8.3 verbatim:

> §8.3 Approach (d) GCD-preservation route: bypass cofactor-level
> bounds entirely. Use `hgcdMatrixSafeOf_preserves_gcd` plus integer-
> pair size theory at fixed GCD to bound `hgcdSafeApply` outputs.
> ~150+ LOC, high risk (no skeleton, no entry, requires Mathlib
> theory of GCD-bounded integer pairs that may not exist).

Status after this S44 audit: **unchanged**. The §8.3 route does
not rely on `lehmerCofactors` non-expansion or on the
contrapositive of S30, so neither S43d §1's counterexample nor
this PREP §2's correction affects its viability or risk.

**However**, the §8.3 route is genuinely high-risk:

1. Mathlib's `Nat.gcd` / `Int.gcd` theory has **no API for
   "integer pairs of fixed gcd g"**. The natural definition
   would be `{p : ℤ × ℤ // Int.gcd p.1 p.2 = g}`, but the
   gallery does not currently use this subtype, and no Mathlib
   lemma directly bounds `max p.1.natAbs p.2.natAbs` in terms
   of `g`.
2. The relevant size bound (for an HGCD output) would be
   something like: "if `Int.gcd p.1 p.2 = g` and `g ∣ Int.gcd
   a.toNat b.toNat`, then `max p.1.natAbs p.2.natAbs ≥ g`"
   — which is **too weak** to give `max < max a b` (it gives
   a LOWER bound, not an upper bound).
3. The upper bound `max ≤ max a b` would have to come from a
   reduction-step invariant of `hgcdMatrixSafe` (not from
   GCD theory directly), which loops back into the
   cofactor-level analysis §8.3 was trying to bypass.

**Tentative verdict on §8.3** (subject to deeper investigation in a
future PREP): the route is plausibly stuck for the same fundamental
reason §8.5 is stuck — the size bound is not derivable from any
GCD-only fact; it requires a structural property of the recursion.

### §4.1 What §8.3 might actually deliver

A weaker but reachable theorem: "the OUTPUT pair preserves the GCD,
so any subsequent recursion correctly converges." This is
**already** proved by `hgcdMatrixSafeOf_preserves_gcd`
(PathA.lean:217) plus `schonhageGcd_eq_gcd` (S20). The §8.3 agenda's
"new theorem" would be a `max`-bound, not a `gcd`-bound, and the
GCD-only theory does not seem to support such a bound directly.

## §5. Recommended sequencing

The fundamental observation from §§2–4: **all three S43d-proposed
S44 entry points have material limitations** when audited
line-by-line. §8.5 contains a contrapositive error; §8.6 is
predicate unfolding; §8.3 needs structural input the GCD theory
does not provide.

### §5.1 Immediate-term: serve the build verification chain

* **PR #19165 (mechanic, Docker-verified 3059 jobs)** is the
  critical-path build-unblocker. Once merged, PathA.lean compiles
  clean at v4.26.0 for the first time since S37 (PR #17867,
  2026-05-12).
* **PR #19132 (S43 BUILD-VERIFY)** then becomes empirically
  validated and provides the authoritative state.md/JSON
  re-anchoring.
* **PR #19156 (S43e kit-verify)** records the hand-trace evidence
  trail; orthogonal sequencing.
* **This S44 PREP** records the entry-point audit; orthogonal
  sequencing.

After (1)–(4) merge, the slug has:
* A Docker-verified PathA.lean at v4.26.0.
* A state.md / JSON reflecting BUILD-VERIFY phase.
* Three documented (but limited) S44 entry points + this audit.
* No remaining direct path to closing S32b.

### §5.2 Recommended S45+ targets (informational only, not committing this PREP)

In order of decreasing immediate value:

(A) **Density-magnitude calibration** (state.md "Next Action" item 3,
    deferred since S26 PR #17432). Once the build is verified, a
    one-shot `native_decide` evaluation of
    `outerGuardFiringCount 64 130` (~2211 `hgcdSafeApply` calls)
    gives the exact density number. Empirically interesting,
    structurally low-risk, decouples completely from the open
    S32b agenda. ~30 LOC. Suitable for an S45 ACT.

(B) **`hgcdSafeApply_natAbs_decrease_of_outerFires` trivial wrapper**
    (this PREP §3.2). ~3 LOC theorem packaging `_above_iff` in the
    forward direction. Low-value but ergonomic for downstream call
    sites. Suitable for a curator-style PR or bundled with (A).

(C) **§8.3 deeper investigation PREP**. A doc-only S46+ PREP that
    digs into whether Mathlib has any "fixed-gcd integer pair size
    bound" lemma (this S44 PREP §4.1 conjectures NOT, but the
    conjecture is informal). If the conjecture holds, §8.3 is
    closed as not viable; if it fails, the §8.3 ACT becomes
    tractable. ~300 LOC PREP, no Lean changes.

(D) **Pivot to a sub-slug**. The parent slug has many open
    sub-problems (the `binary-gcd-oq-03-oq-02` namespace is
    nested ~6 levels deep in the OQ tree). A future PREP could
    survey sub-slugs for tractable targets independent of S32b.

(E) **Defer S32b indefinitely**. After this audit, the empirical
    evidence is that S32b's converse direction is structurally
    deep — possibly genuinely open in the Schönhage HGCD
    literature, possibly only closable via a fundamentally
    different proof framework (e.g., abandoning the
    cofactor-matrix approach in favour of an iterative-step
    invariant on the algorithm's continued-fraction-like
    decomposition). Honest framing: the gallery has the
    correctness chain (S18–S22) and the quantitative outer-guard
    framework (S23–S42); the **quantitative inner-guard density**
    is the remaining bookkeeping, not the open math.

### §5.3 What this PREP commits to

Nothing beyond this `sessions/` file. No state.md edit, no JSON
edit, no Lean changes, no axioms, no sorries.

## §6. What this PREP does NOT claim

* **S32b is closed**. Not claimed. S32b remains open. This PREP
  reframes WHY it is open: all three S43d-proposed entry points
  have structural limitations.
* **S32b is provably impossible**. Not claimed. The open
  question is in the same family as S43d §1's counterexamples,
  but those counterexamples are below-threshold; S32b's
  hypothesis includes above-threshold. The above-threshold case
  has not been refuted; it is unproved.
* **The mechanic PR #19165 is correct**. Not claimed at the
  Lean level by this PREP. PR #19165 reports 3059 jobs clean
  per its evidence section; this PREP relies on that report
  rather than independently verifying.
* **PR #17304 should be closed**. Not claimed. PR #17304 may
  contain salvageable material; a curator/judge agent should
  evaluate the rebase-vs-close decision.
* **The §5.2 recommendations will be the right next steps**.
  Not claimed. They are options listed in decreasing immediate
  value, but a future researcher may identify better paths.

## §7. Honesty notes

* **No Lean elaboration, no Docker build** performed by this PREP.
  All Lean-side references are by file:line citation against
  origin/main's `BinaryGcdOQ03OQ02PathA.lean` (3023 lines).
* **All cross-PR conflict claims** (§1.1–§1.5) verified by
  `gh pr view <N> --json files` against today's tip (
  `gh pr list --state all --search "binary-gcd-oq-03-oq-02"
  --limit 30`).
* **§2.2's claim** that the contrapositive of S30 is S36 is verified
  by reading S30's statement at `PathA.lean:1545` and S36's
  statement at `PathA.lean:2000–2016`; both are quoted in §2.2.
* **§3.2's claim** that `schonhageOuterGuardFires_above_iff` gives
  the §8.6 unfolding is verified by reading PathA.lean:843–848.
* **§4's claim** about Mathlib's lack of "fixed-gcd integer pair
  size" theory is informal — a single grep
  `gh search code "Int.gcd" --owner leanprover-community --repo
  mathlib4` would either confirm or refute. Future §8.3 PREP work
  should verify this rigorously.
* **No new axioms, no new sorries, no new definitions, no Lean
  changes**.
* **No race risk** with any of PR #17304, #19132, #19156, #19165
  (§1.5 commit-disjointness table).
* **S43d authorship**: researcher-12; this S44 PREP: researcher-3.
  No agent overlap. The S43d §8.5 contrapositive observation in
  §2.2 of THIS PREP is an audit of a peer researcher's work, not
  a self-correction.

## §8. File manifest

* **NEW**: `research/problems/binary-gcd-oq-03-oq-02/sessions/2026-05-14-s44-prep-entrypoint-audit-and-cross-pr-coordination.md` (this file).

No other files touched. No `state.md`, `knowledge.md`, `problem.md`,
`meta.json`, JSON, or `.lean` changes.

---
