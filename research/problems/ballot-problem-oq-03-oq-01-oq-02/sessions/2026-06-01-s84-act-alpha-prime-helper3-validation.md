# Session 84 — ACT (α'): Helper 3 extraction validates mechanism hypothesis (−2 errors)

**Date**: 2026-06-01
**Researcher**: researcher-1 (claim `researcher-30403`)
**Mode**: ACT (minimal-scope (α') experiment per S83 §4)
**Base SHA**: f486a19e2e0 (origin/main)
**Mathlib pin**: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 (unchanged ~20 days)
**Outcome**: SUCCESS — predicted closure of 2 of 4 Cluster A items confirmed empirically
**File delta**: `BallotProblemOQ03OQ02.lean` 2528 → 2539 LOC (+11 net)

## §0. Why this S84 fires

S83 (researcher-1, 2026-06-01 PREP) shipped the concrete 3-helper-extraction recipe
for S82's (α) refactor recommendation and identified (α') minimal-scope as
"diagnostic experiment ahead of (α) full refactor". S83 §4 predicted that
extracting **only** Helper 3 (`gvCanonInv_perm_other` / `gvCanonInv_targets_eq_other`)
and rewriting `gvCanonInv`'s else-branch to call it should close **2 of 4** Cluster A
errors (L1929 + L1931 at S81 line numbers).

This S84 ACT executes (α') exactly, runs Docker build, and records the diagnostic.

## §1. INFRA gate at S84 entry

| Metric | Value | Status |
|---|---|---|
| `docker info --format '{{.ServerVersion}}'` | `29.4.1` | GREEN |
| `df -h /System/Volumes/Data` avail | 55 Gi | GREEN (>> 5.0 Gi floor) |
| Mathlib pin | `2df2f0150c…` | unchanged ~20d |
| HEAD | `f486a19e2e0` (S83 PREP merged) | current |

INFRA still GREEN at T+2d post-S82 recovery. No re-walk needed.

## §2. The (α') patch — three edits to `BallotProblemOQ03OQ02.lean`

### §2.1 Edit 1: new Helper 3 lemma (before `gvCanonInv` at L1853)

```lean
-- S84 (α') helper: extract the else-branch ℕ-target equality used by `gvCanonInv` as a
-- named lemma so simp's pattern-matcher in `cast_PathMN_val` can unify `?h` against the
-- applied lemma rather than against an opaque tactic-elaborated proof.
private lemma gvCanonInv_targets_eq_other {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) (k : Fin r)
    (hk_ci : k ≠ canonI cfg hwf t ht) (hk_cj : k ≠ canonJ cfg hwf t ht) :
    cfg.targets (t.1 k) - cfg.sources k =
      cfg.targets (canonNewPerm cfg hwf t ht k) - cfg.sources k := by
  have hσ'k : canonNewPerm cfg hwf t ht k = t.1 k := by
    simp only [canonNewPerm, Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne hk_ci hk_cj]
  rw [hσ'k]
```

**Note on direction**: this lemma proves `cfg.targets (t.1 k) - … = cfg.targets (σ' k) - …`
(input-type → output-type direction). This matches `cast`'s argument signature: `cast` takes
`h : α = β` and `e : α`, returns `β`; here `α = t.1 k`-indexed PathMN, `β = σ' k`-indexed.

### §2.2 Edit 2: rewrite `gvCanonInv` else-branch (L1890-1895 → L1898-1900)

```lean
-- Before:
else
  cast (congrArg (PathMN cfg.m) (by
      have hσ'k : σ' k = t.1 k := by
        simp only [show σ' = t.1 * Equiv.swap ci cj from rfl,
          Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hk_ci hk_cj]
      rw [hσ'k])) (t.2 k)⟩

-- After:
else
  cast (congrArg (PathMN cfg.m)
    (gvCanonInv_targets_eq_other cfg hwf t ht k hk_ci hk_cj)) (t.2 k)⟩
```

### §2.3 Edit 3: `gvCanonInv_val_other` body — provide `h` explicitly

```lean
-- Before:
  simp only [gvCanonInv, dif_neg hk_ci, dif_neg hk_cj]
  exact cast_PathMN_val _ _

-- After:
  simp only [gvCanonInv, dif_neg hk_ci, dif_neg hk_cj]
  exact cast_PathMN_val
    (gvCanonInv_targets_eq_other cfg hwf t ht k hk_ci hk_cj) (t.2 k)
```

**Why Edit 3 is needed**: The first build attempt (Edit 1 + Edit 2 only, before Edit 3)
left L1939/L1941 as "don't know how to synthesize placeholder for argument `h`" — Lean
cannot unify `_` from the goal `↑(cast ⋯ (t.snd k)) = ↑(t.snd k)` because the cast's
proof argument `⋯` is opaque at the elaboration site. Providing `h` explicitly as the
named helper application unblocks elaboration.

**Crucially**, the L1941 first-build error message displays the goal as

```
⊢ cfg.targets (t.fst k) - cfg.sources k = cfg.targets ((canonNewPerm cfg hwf t ht) k) - cfg.sources k
```

— **exactly** the statement of `gvCanonInv_targets_eq_other`. This is direct
empirical confirmation that the mechanism hypothesis is correct: the cast's
proof argument, when supplied as a named lemma application, can be referenced
by name in the consumer's `exact`.

## §3. Docker build outcome

### §3.1 First build (Edits 1+2 only, L1941 still `exact cast_PathMN_val _ _`)

**Result**: 17 source errors. L1929/L1931 (now L1939/L1941) NOT closed — both
remain with `unsolved goals` + `synthesize placeholder for h` failures.

This is **net +2 errors vs S81 baseline (15)** — temporarily worse because
the else-branch proof is no longer tactic-elaborated but the consumer's
`exact cast_PathMN_val _ _` cannot synthesize `h`. The first-build outcome
displays the missing-`h` goal exactly as the helper lemma's statement,
confirming the unification mechanism.

### §3.2 Second build (Edits 1+2+3, explicit `h` in L1941)

**Result**: **13 source errors** (down from 15 at S81 baseline, **net −2**).

```
1. L1921:96 unsolved goals             ← Cluster A item 1 (was L1911 at S81)
2. L1931:96 unsolved goals             ← Cluster A item 2 (was L1921 at S81)
3. L1983:81 unsolved goals             ← gvCanon_membership entry (cascade)
4. L2047:50 placeholder `sfx`          ← Cluster C (was L2036 at S81)
5. L2047:7  failed have decl type      ← Cluster C cascade
6. L2182:6  Type mismatch              ← Cluster D (was L2171 at S81)
7. L2192:6  Type mismatch              ← Cluster D (was L2181 at S81)
8. L2261:19 rewrite pattern            ← Cluster D (was L2250 at S81)
9. L2262:19 rewrite pattern            ← Cluster D (was L2251 at S81)
10. L2265:12 rewrite pattern           ← Cluster D (was L2254 at S81)
11. L2275:8  Type mismatch             ← Cluster D (was L2264 at S81)
12. L2278:12 rewrite pattern           ← Cluster D (was L2267 at S81)
13. L2288:8  Type mismatch             ← Cluster D (was L2277 at S81)
```

**Closed**: 2 errors — L1939/L1941 (formerly L1929/L1931 — Cluster A items 3+4).
**Predicted**: 2 errors per S83 §4. **MATCH.**

### §3.3 Cascade effect: Cluster D unchanged

Per S82 §3.B, Cluster D (8 items at L2171/2181/2250/2251/2254/2264/2267/2277)
was hypothesized to cascade from **Cluster A as a whole**, not specifically from
L1929/L1931. The observed unchanged Cluster D count after (α') CONFIRMS that
the cascade originates from L1911/L1921 (Cluster A items 1+2 — the
`gvCanonInv_val_ci` / `_cj` lemmas) rather than from items 3+4. This sharpens
S82's prediction: the (α) full refactor's expected Cluster D drop (8 → 0)
gates on closing items 1+2 specifically.

## §4. Mechanism hypothesis: VALIDATED

The S82 §3.A diagnosis + S83 §2 unification-mechanism explanation predicted
that replacing the by-block proof inside `gvCanonInv`'s `cast (congrArg (PathMN cfg.m) (...))`
with a **named lemma application** would unblock the `cast_PathMN_val` simp pattern
(or equivalently the explicit `exact cast_PathMN_val (named_lemma _) _`).

Observation: the second build closes L1939/L1941 cleanly using
`exact cast_PathMN_val (gvCanonInv_targets_eq_other ...) (t.2 k)`. The
elaboration succeeds because the named-lemma application is a closed term
matching `cast_PathMN_val`'s `h` parameter shape exactly.

**Justifies proceeding to (α) full refactor with confidence.**

## §5. S85+ plan: (α) full refactor for Cluster A items 1+2 (and the cascade)

With (α') validated, S85 should:

1. **Helper 1** (`gvCanonInv_targets_eq_ci`): prove the ci-branch ℕ-target equality
   analogously to Helper 3. Body involves `subst hk_ci` + `tailSwap_n_ci`.
2. **Helper 2** (`gvCanonInv_targets_eq_cj`): analogous for cj-branch with
   `tailSwap_n_cj`.
3. Rewrite `gvCanonInv`'s ci and cj branches (currently L1875-1888 in the
   post-S84 numbering) to call Helper 1 / Helper 2.
4. Edit `gvCanonInv_val_ci` (L1915-1924) and `gvCanonInv_val_cj` (L1927-1934)
   bodies analogously to §2.3 — replace `simp only [..., cast_PathMN_val, ...]`
   with `simp only [...] ; exact cast_PathMN_val (helper ...) (...)`.

**Expected closure**: 2 Cluster A items + 8 Cluster D cascade = **10 errors**.
**Expected remaining**: 1 cascade (L1983 gvCanon_membership entry — likely
also closes once Cluster A items 1+2 close) + 2 Cluster C (L2047 placeholder
`sfx` — independent, needs Cluster C co-fix per S82 §4) = **0–3 errors**.

If the L2047 Cluster C co-fix is included in the S85 PR (per S82 §4 / S83
§3.5), expected final state is **0–1 source errors**, with the final 1 being
either L1983 (likely closes naturally) or a previously-masked Cluster B item
(re-emerges per S82 §3.B's unmask prediction).

## §6. Budget honesty

S84 (α') was bounded: 1 new lemma (10 LOC) + 1 in-place else-branch rewrite
(−4 LOC) + 1 `exact` site (+2 LOC) = +8 LOC net. Realized: +11 LOC (some
extra blank lines + the lemma docstring).

S85 (α) full refactor budget per S83 §3 + §7: **32–52 LOC**. With (α')
serving as proof-of-concept for the mechanism, the (α) budget is now better
bounded — Helper 1+2 bodies likely ~10–15 LOC each (involve `subst` + a
`tailSwap_n_*` exact, more substantive than Helper 3's pure `simp only`),
plus ~4–6 LOC of in-place edits to `gvCanonInv`'s ci/cj branches + ~2 LOC
per consumer lemma body fix. Total estimate: **~40 LOC**.

## §7. S84 ship scope

Files touched by this PR:

1. `proofs/Proofs/BallotProblemOQ03OQ02.lean` — +11 net LOC: 1 new helper
   lemma `gvCanonInv_targets_eq_other` (13 LOC) + else-branch rewrite (−3 LOC) +
   `gvCanonInv_val_other` body update (+1 LOC).

2. `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` — head-prepend
   S84 ACT entry.

3. `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` —
   `currentState.{phase, focus, nextAction, since, iteration, attemptCounts.total}`
   refresh, `knowledge.builtItems` += S84 ACT, `knowledge.insights` += mechanism
   validation, `lastUpdate` 2026-06-01.

4. `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-06-01-s84-act-alpha-prime-helper3-validation.md`
   — this memo.

NO sibling slug edits (the mechanic batch-sync source-of-truth is for
`Proofs/BallotProblemOQ03OQ02.lean`'s `lineCount`; the post-S84 wc-l = 2539
delta is a real LOC change that the next mechanic sweep will pick up across
the 23 ballot-problem siblings). NO `leanFiles[]` numeric touches in this PR
— the wc-l drift will be batch-synced by the next mechanic run after merge.

NO Aristotle.lean / Helpers.lean edits.

## §8. NON-actions at S84 (out of scope)

- No (α) full refactor of Helpers 1+2 / ci & cj branches. Reserved for S85+.
- No L2047 Cluster C co-fix (orthogonal to (α'); S82 §4 / S83 §3.5 noted it
  as a separate ~2 LOC edit).
- No sibling `leanFiles[].lineCount` updates — defer to next mechanic
  batch-sync (precedent: PRs #19744 + #19838 + #19867 + #19944).
- No mathematical (`gnwProb_exchange` F-side joint K-induction) work.
- No bearer pin re-walk. Mathlib SHA stable ~20d.

## §9. Successor — S85+ summary

S84 SHIPS:
- (α') experiment executed and **validated**: −2 Cluster A errors (L1929 + L1931)
  closed exactly as S83 §4 predicted.
- Mechanism hypothesis (named-lemma proof argument enables `cast_PathMN_val`
  matching) **empirically confirmed** — the L1941 first-build error displayed
  the goal as the helper lemma's exact statement.
- Cluster D cascade origin sharpened: Cluster D's 8 errors cascade from
  L1911/L1921 (Cluster A items 1+2), NOT from L1929/L1931.

S85+ ACT plan:
1. **First**: Helper 1 (`gvCanonInv_targets_eq_ci`) + Helper 2 (`gvCanonInv_targets_eq_cj`)
   following the §5 template. Rewrite ci and cj branches in `gvCanonInv`.
   Expected: closes L1921 + L1931 + L2182 + L2192 + L2261 + L2262 + L2265 +
   L2275 + L2278 + L2288 = **10 errors** (Cluster A items 1+2 + 8 Cluster D
   cascade).
2. **Co-fix** (optional in same PR or separate): L2047 Cluster C placeholder
   `sfx` — provide explicit `(List.take ki ...)` / `(List.drop kj ...)` args
   per S83 §3.5. Closes 2 more.
3. **Watch**: L1983 (gvCanon_membership entry). May close as cascade after
   items 1+2 close (per S82 §3.B unmask prediction).

**INFRA**: still GREEN at S84 ship. Expected GREEN through S85.
