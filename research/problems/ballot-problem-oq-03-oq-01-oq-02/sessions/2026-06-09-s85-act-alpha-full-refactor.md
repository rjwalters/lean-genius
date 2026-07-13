# Session 85 — ACT (α): Full refactor — Helpers 1+2 close Cluster A items 1+2 (−2 errors)

**Date**: 2026-06-09
**Researcher**: researcher-3 (claim `researcher-30963`)
**Mode**: ACT (full (α) refactor per S84 §5 + S82 §4 recommendation)
**Base SHA**: ab09ff2d20d (origin/main)
**Mathlib pin**: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 (unchanged ~28 days)
**Outcome**: SUCCESS for Cluster A closure (items 1+2 closed); Cluster D cascade hypothesis FALSIFIED
**File delta**: `BallotProblemOQ03OQ02.lean` 2539 → 2583 LOC (+44 net)

## §0. Why this S85 fires

S84 (researcher-1, 2026-06-01 ACT (α')) extracted Helper 3 (`gvCanonInv_targets_eq_other`)
and validated the mechanism hypothesis: named-lemma proof arguments inside
`cast (congrArg (PathMN cfg.m) ...)` enable `cast_PathMN_val` matching where
opaque tactic-elaborated proofs failed (S82 §3.A). S84 closed Cluster A items
3+4 (L1929+L1931 at S81 numbering = L1939+L1941 post-S84) reducing the parent
file from 15 → 13 source errors.

S84 §5 left the (α) full refactor for S85+ — extract Helpers 1+2
(`gvCanonInv_targets_eq_ci`, `gvCanonInv_targets_eq_cj`) analogously to
Helper 3, rewrite `gvCanonInv`'s ci-branch and cj-branch to call them, and
update `gvCanonInv_val_ci` / `gvCanonInv_val_cj` bodies to provide `h`
explicitly to `cast_PathMN_val` per the S84 §2.3 template.

Expected closure per S84 §5: **10 errors** — 2 Cluster A items 1+2
(L1921+L1931 at post-S84 numbering) + **8 Cluster D cascade** (L2182/2192/
2261/2262/2265/2275/2278/2288).

This S85 ACT executes the full (α) refactor.

## §1. INFRA gate at S85 entry

| Metric | Value | Status |
|---|---|---|
| `docker info --format '{{.ServerVersion}}'` | `29.5.3` | GREEN |
| `df -h /System/Volumes/Data` avail | 92 Gi | GREEN (>> 5.0 Gi floor) |
| Mathlib pin | `2df2f0150c…` | unchanged ~28d |
| `proofs/.lake` symlink | self-circular (B3 RED) | non-blocking (per S79+) |
| HEAD | `ab09ff2d20d` (S84 ACT merged via #22026) | current |

INFRA still GREEN at T+8d post-S81 recovery. No re-walk needed.

## §2. The (α) patch — four edits to `BallotProblemOQ03OQ02.lean`

### §2.1 Edit 1: new Helper 1 `gvCanonInv_targets_eq_ci` (after Helper 3, L1866-1884)

```lean
-- S85 (α) Helper 1: ci-branch ℕ-target equality used by `gvCanonInv`'s ci branch.
-- Same purpose as `gvCanonInv_targets_eq_other` — replace tactic-elaborated proof
-- inside `cast (congrArg (PathMN cfg.m) (...))` with a named-lemma application.
private lemma gvCanonInv_targets_eq_ci {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) (k : Fin r)
    (hk_ci : k = canonI cfg hwf t ht) :
    let ci := canonI cfg hwf t ht
    let cj := canonJ cfg hwf t ht
    let c := canonCol cfg hwf t ht
    let y := canonY cfg hwf t ht
    let ki := splitPosAt cfg t c y ci
    let kj := splitPosAt cfg t c y cj
    ki + (cfg.targets (t.1 cj) - cfg.sources cj) - kj =
      cfg.targets (canonNewPerm cfg hwf t ht k) - cfg.sources k := by
  subst hk_ci
  have hσ'ci : canonNewPerm cfg hwf t ht (canonI cfg hwf t ht) =
      t.1 (canonJ cfg hwf t ht) := by
    simp only [canonNewPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_left]
  rw [hσ'ci]
  exact tailSwap_n_ci cfg hwf t ht
```

**Note on `k`-parameterization**: the helper takes `(k : Fin r)` + `(hk_ci : k = canonI ...)`
and uses `subst hk_ci` to substitute `k → canonI ci`. This factoring lets the
ci-branch invocation pass its local `hk_ci` directly without external `subst`.

### §2.2 Edit 2: new Helper 2 `gvCanonInv_targets_eq_cj` (after Helper 1, L1886-1903)

```lean
-- S85 (α) Helper 2: cj-branch ℕ-target equality used by `gvCanonInv`'s cj branch.
private lemma gvCanonInv_targets_eq_cj {r : ℕ} (cfg : LGVConfig r) (hwf : cfg.wellFormed)
    (t : TaggedPathTuple cfg) (ht : ¬isNonCancellable t) (k : Fin r)
    (hk_cj : k = canonJ cfg hwf t ht) :
    let ci := canonI cfg hwf t ht
    let cj := canonJ cfg hwf t ht
    let c := canonCol cfg hwf t ht
    let y := canonY cfg hwf t ht
    let ki := splitPosAt cfg t c y ci
    let kj := splitPosAt cfg t c y cj
    kj + (cfg.targets (t.1 ci) - cfg.sources ci) - ki =
      cfg.targets (canonNewPerm cfg hwf t ht k) - cfg.sources k := by
  subst hk_cj
  have hσ'cj : canonNewPerm cfg hwf t ht (canonJ cfg hwf t ht) =
      t.1 (canonI cfg hwf t ht) := by
    simp only [canonNewPerm, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  rw [hσ'cj]
  exact tailSwap_n_cj cfg hwf t ht
```

### §2.3 Edit 3: rewrite `gvCanonInv` ci/cj branches

```lean
-- Before:
if hk_ci : k = ci then
  cast (congrArg (PathMN cfg.m) (by
      subst hk_ci
      have hσ'ci : σ' ci = t.1 cj := by
        simp only [show σ' = t.1 * Equiv.swap ci cj from rfl,
          Equiv.Perm.mul_apply, Equiv.swap_apply_left]
      rw [hσ'ci]
      exact tailSwap_n_ci cfg hwf t ht)) <|
    tailSwapPath ...
else if hk_cj : k = cj then
  cast (congrArg (PathMN cfg.m) (by
      subst hk_cj
      have hσ'cj : σ' cj = t.1 ci := by
        simp only [show σ' = t.1 * Equiv.swap ci cj from rfl,
          Equiv.Perm.mul_apply, Equiv.swap_apply_right]
      rw [hσ'cj]
      exact tailSwap_n_cj cfg hwf t ht)) <|
    tailSwapPath ...

-- After:
if hk_ci : k = ci then
  cast (congrArg (PathMN cfg.m)
    (gvCanonInv_targets_eq_ci cfg hwf t ht k hk_ci)) <|
    tailSwapPath ...
else if hk_cj : k = cj then
  cast (congrArg (PathMN cfg.m)
    (gvCanonInv_targets_eq_cj cfg hwf t ht k hk_cj)) <|
    tailSwapPath ...
```

Net branch change: −14 LOC (two by-blocks of 7 LOC each replaced with 2-line
helper applications). Combined with Helpers 1+2 totaling ~30 LOC, net branch
overhead ≈ +16 LOC.

### §2.4 Edit 4: rewrite `gvCanonInv_val_ci` / `_val_cj` bodies (explicit `h`)

```lean
-- gvCanonInv_val_ci — before:
private lemma gvCanonInv_val_ci ... := by
  simp only [gvCanonInv, dite_true, tailSwapPath, cast_PathMN_val, Subtype.coe_mk]

-- gvCanonInv_val_ci — after:
private lemma gvCanonInv_val_ci ... := by
  simp only [gvCanonInv, dite_true]
  exact cast_PathMN_val
    (gvCanonInv_targets_eq_ci cfg hwf t ht (canonI cfg hwf t ht) rfl)
    (tailSwapPath (t.2 (canonI cfg hwf t ht)) (t.2 (canonJ cfg hwf t ht))
      (splitPosAt cfg t (canonCol cfg hwf t ht) (canonY cfg hwf t ht) (canonI cfg hwf t ht))
      (splitPosAt cfg t (canonCol cfg hwf t ht) (canonY cfg hwf t ht) (canonJ cfg hwf t ht))
      (splitPos_east_eq cfg hwf t ht)
      (splitPos_le_length cfg hwf t ht (canonI cfg hwf t ht) (Or.inl rfl))
      (splitPos_le_length cfg hwf t ht (canonJ cfg hwf t ht) (Or.inr rfl)))
```

Analogous edit for `gvCanonInv_val_cj`. Following the exact S84 §2.3 template
that worked for `gvCanonInv_val_other`: drop `tailSwapPath, cast_PathMN_val,
Subtype.coe_mk` from the simp set, then `exact cast_PathMN_val h e` with both
arguments explicit. The RHS of `cast_PathMN_val h e` is `e.val` which
definitionally reduces to `P.val.take kp ++ Q.val.drop kq` via tailSwapPath's
`where val := ...` clause, matching the goal's RHS.

## §3. Docker build outcome

### §3.1 First (and only) build

**Result**: **11 source errors** (down from 13 at S84 baseline, **net −2**).

```
1. L2027:81 unsolved goals             ← gvCanon_membership cascade (was L1983)
2. L2091:50 placeholder `sfx`          ← Cluster C (was L2047)
3. L2091:7  failed have decl type      ← Cluster C cascade (was L2047)
4. L2226:6  Type mismatch              ← Cluster D (was L2182)
5. L2236:6  Type mismatch              ← Cluster D (was L2192)
6. L2305:19 rewrite pattern            ← Cluster D (was L2261)
7. L2306:19 rewrite pattern            ← Cluster D (was L2262)
8. L2309:12 rewrite pattern            ← Cluster D (was L2265)
9. L2319:8  Type mismatch              ← Cluster D (was L2275)
10. L2322:12 rewrite pattern           ← Cluster D (was L2278)
11. L2332:8  Type mismatch             ← Cluster D (was L2288)
```

**Closed**: 2 errors — L1921/L1931 (Cluster A items 1+2).
**Predicted**: 10 errors per S84 §5 (2 Cluster A + 8 Cluster D cascade).
**Actual**: 2 errors. **Cluster D cascade hypothesis FALSIFIED.**

Per S84 §3.3, Cluster D was hypothesized to "cascade from L1911/L1921 (Cluster A
items 1+2 — the `gvCanonInv_val_ci` / `_cj` lemmas)". With items 1+2 now CLOSED,
Cluster D should have dropped to 0. **It did not.** Cluster D's 8 errors persist
at line numbers shifted by +44 LOC (matching the S85 file growth) — confirming
they are at the same logical positions as the S84 baseline. **Cluster D is
independent of Cluster A, not a cascade.**

### §3.2 Cluster A: FULLY CLOSED

| S82 cluster label | Items | Closed by | Status |
|---|---|---|---|
| Cluster A | 1+2 (val_ci/val_cj cast match) | S85 (this PR) | **CLOSED** |
| Cluster A | 3+4 (val_other cast match) | S84 (#22026) | CLOSED |
| Cluster B | gvCanon_membership inner (≥12 latent) | -- | masked-by-C, 1 visible |
| Cluster C | L2091 placeholder `sfx` (2 visible) | -- | open |
| Cluster D | 8 errors at canonCrossN_image | -- | open (NOT cascade) |

Cluster A is now **fully closed** via the combined S84 + S85 (α) refactor.

### §3.3 Cluster B/D revised understanding

S82 §3.B predicted Cluster B (≥12 errors in `gvCanon_membership` inner body)
was masked by Cluster C and would be revealed when Cluster C closes. S82
predicted Cluster D (8 errors) cascades from Cluster A.

S85 evidence refines both:
- **Cluster B**: 1 visible error (L2027 unsolved goals at `gvCanon_membership` entry)
  remains — consistent with the masked-by-C hypothesis (the entry visible at
  baseline cascades from Cluster C, the inner ≥12 latent errors will surface
  only when C closes).
- **Cluster D**: **NOT** a cascade from Cluster A. Independent. Likely a
  separate elaboration / `rw` pattern issue inside `canonCrossN_image`'s
  PART 2 (the `colEntry_eq` / `transfer_hi` helpers and the `canonCross_min`
  application).

## §4. Mechanism hypothesis (full refactor): RE-VALIDATED

S84's mechanism hypothesis — named-lemma proof arguments inside `cast (congrArg
(PathMN cfg.m) ...)` enable `cast_PathMN_val` matching — applies symmetrically
to Helpers 1+2. The (α') validation at S84 generalizes cleanly to (α) full
refactor.

**Justifies the explicit-`exact` pattern at val_ci/val_cj** (S84 §2.3 →
generalized at §2.4 here). The same pattern that closed val_other now closes
val_ci and val_cj.

## §5. S86+ plan: Cluster D investigation + Cluster C co-fix

Cluster A is closed. Remaining work:

### §5.1 Cluster D (8 errors) — independent investigation

Per S85's falsification of the cascade hypothesis, Cluster D needs a separate
diagnostic pass. The errors cluster around two `canonCrossN_image` subproofs:
- `colEntry_eq_ci` / `colEntry_eq_cj` at L2218-2236: `northBeforeEast_prefix`
  Type mismatch
- PART 1 of `canonCrossN_image` (h_le, L2298-2332): `rw [colEntry_eq ci c₀
  le_rfl]` failures + `simpa [if_neg hcm'] using hhi_*` Type mismatches

These errors involve `t.fst (swap ci cj k)` and `t'.fst k` shapes. Likely
candidate causes:
- (D-α) `colEntry_eq` ↦ `t'.2 k` shape mismatch (perhaps `gvCanonInv_val_other`
  is now returning a slightly different normal form?)
- (D-β) Mathlib v4.26.0 change in `northBeforeEast_prefix` / `colEntry`
  signature that bit-rotted some implicit args
- (D-γ) Independent `simpa` failure that needs `simp only [...]` instead

Recommended S86 ACT: bisect by commenting out PART 1 of `canonCrossN_image` and
checking if PART 2 still has issues; locate the first `rw` that fails and
inspect its expected vs actual pattern.

### §5.2 Cluster C (2 errors) — placeholder `sfx`

Per S82 §4 / S83 §3.5, this is the `northBeforeEast_ge_prefix_true _ _ c
hpfx_ci` invocation at L2091 — Lean can't synthesize the `sfx` (suffix)
placeholder. The fix is to provide it explicitly: `northBeforeEast_ge_prefix_true
(P.val.take ki) (Q.val.drop kj) c hpfx_ci` with the suffix spelled out.

Estimated ~4 LOC fix (2 sites × 2 LOC each). Independent of Cluster D.

### §5.3 Cluster B unmask (≥12 latent)

After Cluster C closes (§5.2), the visible error count is expected to JUMP per
S82 §3.B: the L2027 `gvCanon_membership` entry will reveal ≥12 latent inner-body
errors. This is **expected behavior**, not regression. S87+ will need to address
those one-by-one.

### §5.4 Sequencing recommendation

S86 ACT plan (~10-15 LOC): Cluster C co-fix (L2091 ×2) — independent of
Cluster D, smallest scope. Expected outcome: 11 → 9 visible errors, but Cluster
B will unmask 12 latent → visible count jumps to ~21. This is the predicted
trajectory per S82 §3.B.

S87+ ACT plan: Cluster D investigation per §5.1, then Cluster B inner-body
fixes one at a time (each likely a small simp/rw edit).

## §6. Budget honesty

S85 budget per S84 §6: **~40 LOC** for (α) full refactor (Helpers 1+2 + ci/cj
branches + val_ci/val_cj body fixes).

Realized: **+44 LOC** (slightly over). Breakdown:
- Helper 1 (`gvCanonInv_targets_eq_ci`): 19 LOC (with docstring)
- Helper 2 (`gvCanonInv_targets_eq_cj`): 18 LOC
- ci/cj branch simplifications: −14 LOC (replaces 2 by-blocks)
- val_ci body explicit `h` fix: +13 LOC
- val_cj body explicit `h` fix: +8 LOC
- Net: +44 LOC (was 2539 → 2583)

Close to budget — slight overage from helper docstrings and the explicit
arg-list verbosity in val_ci/val_cj (`splitPosAt` + `splitPos_le_length` spelled
out instead of `_` because Lean would not synthesize from goal context).

## §7. S85 ship scope

Files modified:

1. `proofs/Proofs/BallotProblemOQ03OQ02.lean` — +44 net LOC: 2 new helper
   lemmas (`gvCanonInv_targets_eq_ci`, `gvCanonInv_targets_eq_cj`) + ci/cj
   branch rewrites in `gvCanonInv` + `gvCanonInv_val_ci` / `_val_cj` body
   updates with explicit `cast_PathMN_val` arguments.

2. `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` — head-prepend
   S85 ACT entry.

3. `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json` —
   `currentState.{phase, focus, nextAction, since, iteration, attemptCounts.total}`
   refresh, `knowledge.builtItems` += S85 ACT, `knowledge.insights` += cascade-
   falsification + Cluster A closure, `lastUpdate` 2026-06-09.

4. `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-06-09-s85-act-alpha-full-refactor.md`
   — this memo.

NO sibling slug edits. NO `leanFiles[]` numeric touches in this PR — the wc-l
drift (2539 → 2583) will be batch-synced by the next mechanic run after merge
(precedent: PRs #19744 + #19838 + #19867 + #19944 + post-S84 batch).

NO Aristotle.lean / Helpers.lean edits.

## §8. NON-actions at S85 (out of scope)

- No Cluster C co-fix (deferred to S86 — independent, ~4 LOC).
- No Cluster D investigation (deferred to S87+ — needs separate diagnostic).
- No sibling `leanFiles[].lineCount` updates (mechanic source-of-truth).
- No mathematical (`gnwProb_exchange` F-side joint K-induction) work — still
  blocked on Cluster A+B+C+D parent rebuild.
- No bearer pin re-walk. Mathlib SHA stable ~28d.

## §9. Successor — S86+ summary

S85 SHIPS:
- (α) full refactor executed: Cluster A fully CLOSED (items 1+2 closed by S85,
  items 3+4 closed by S84). Parent file 13 → 11 source errors.
- Mechanism hypothesis (named-lemma proof argument enables `cast_PathMN_val`
  matching) re-validated symmetrically across ci/cj/other branches.
- Cluster D cascade hypothesis (S82 §3.B / S84 §3.3) **EMPIRICALLY FALSIFIED** —
  closing Cluster A items 1+2 did NOT auto-close Cluster D's 8 errors.
  Cluster D requires separate investigation in S87+.

S86+ ACT plan:
1. **S86 ACT** (recommended): Cluster C co-fix at L2091 — explicit `sfx`
   placeholders for `northBeforeEast_ge_prefix_true`. ~4 LOC. Expected outcome:
   11 → 9 visible (but Cluster B unmasks ~12 latent → ~21 visible).
2. **S87+ ACT**: Cluster D investigation per §5.1 — bisect, locate first failure,
   fix per cause (D-α/β/γ candidate paths).
3. **S88+ ACT**: Cluster B inner-body fixes after C+D close.

**INFRA**: still GREEN at S85 ship. Expected GREEN through S86.
