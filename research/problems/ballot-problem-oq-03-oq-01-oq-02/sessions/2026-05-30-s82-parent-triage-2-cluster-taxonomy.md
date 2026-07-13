# Session 82 — PARENT-TRIAGE-2: 4-cluster taxonomy + Cluster B unmask discovery (researcher-1, 2026-05-30T~22:10Z)

## §0. Why this S82 fires

S81 (researcher-1, ~T-6h earlier same day) shipped the trap.4 doctor
patch (parent file -4/+1 LOC) that confirmed:
- S78 ACT's `cast_PathMN_coe` lemma was malformed (type-sig fail at L1854)
- Trap.4 fallback (`@[simp] cast_PathMN_val`) reverts the file to the
  pre-S78 15-error baseline but does NOT close Cluster A's simp-only
  proof bodies at L1911/L1921/L1929
- BOTH branches of the S77 §5.2 / S78 §9 Cluster A strategy are
  empirically refuted

S81 §3 nextAction prescribed S82 PARENT-TRIAGE-2 to re-do S74's
6-cluster classification on the new 15-error baseline.  This S82
ships:

1. Refined 4-cluster taxonomy at post-S81 line numbers
2. Cascade-hypothesis verification via an in-session Cluster C fix
   experiment (L2036 placeholder synthesis)
3. **Critical new finding**: Cluster C's L2036 placeholder failure was
   **elaboration-short-circuiting 11 latent errors** in `gvCanon_membership`
   body (L2050-L2093 in the experimentally-patched build).  The
   "1-error Cluster B" of the baseline taxonomy was hiding a 12-error
   cascade; the apparent 15-error baseline is a MINIMUM upper bound
   on the true number of latent failures.
4. (α/β/γ) Cluster A replan refinement: (α) recommendation
   strengthened — the gvCanonInv refactor must close not just 4 Cluster
   A simp-only sites but also the 12-error gvCanon_membership cascade
   plus 8-error canonCrossN_image cascade

## §1. INFRA evidence at S82 entry

```
$ timeout 10 docker info --format '{{.ServerVersion}}'
29.4.1
$ df -h /System/Volumes/Data
/dev/disk3s5   926Gi   839Gi    57Gi    94%   /System/Volumes/Data
$ ls -la proofs/.lake
proofs/.lake -> /Users/rwalters/GitHub/lean-genius/proofs/.lake
$ jq -r '.packages[] | select(.name=="mathlib") | .rev' proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

| Surface | S81T (~15:51Z) | S82T (~22:10Z) | Delta |
|---|---|---|---|
| B1 Docker daemon | 29.4.1 | 29.4.1 | stable |
| B2 disk avail | 62 Gi | 57 Gi | −5 Gi (other workloads, well above floor) |
| B3 .lake symlink | self-circular | self-circular | unchanged |
| Mathlib SHA | `2df2f015...` | `2df2f015...` | stable ~18d |

INFRA is healthy at S82 entry.  Mathlib pin still stable.

## §2. The 15-error baseline at post-S81 line numbers

Carry-forward from S81 §2.5 second-build (hot cache, post-trap.4):

```
1.  L1911:96 unsolved goals             (gvCanonInv_val_ci simp closure)
2.  L1921:96 unsolved goals             (gvCanonInv_val_cj simp closure)
3.  L1929:57 unsolved goals             (gvCanonInv_val_other simp closure)
4.  L1931:24 placeholder `h`            (exact cast_PathMN_val _ _)
5.  L1972:81 unsolved goals             (gvCanon_membership cascade — APPARENT)
6.  L2036:50 placeholder `sfx`          (northBeforeEast_ge_prefix_true _ _ c hpfx_ci)
7.  L2036:7  failed have decl type      (cascade of #6)
8.  L2171:6  Type mismatch              (colEntry_eq_ci, northBeforeEast_prefix _ _ _ c')
9.  L2181:6  Type mismatch              (colEntry_eq_cj, northBeforeEast_prefix _ _ _ c')
10. L2250:19 rewrite failed             (colEntry_eq ci c₀ le_rfl in canonCrossN_image)
11. L2251:19 rewrite failed             (colEntry_eq cj c₀ le_rfl in canonCrossN_image)
12. L2254:12 rewrite failed             (himg_ci in split_ifs interior branch)
13. L2264:8  Type mismatch              (simpa [if_neg hcm'] using hhi_j in c₀=m branch)
14. L2267:12 rewrite failed             (himg_cj in split_ifs interior branch)
15. L2277:8  Type mismatch              (simpa [if_neg hcm'] using hhi_i in c₀=m branch)
```

Total: **15 errors** at parent file lineCount 2528 (post-S81 trap.4).

## §3. 4-cluster taxonomy with cascade analysis

### §3.A Cluster A (ROOT, 4 errors) — gvCanonInv simp closure

| # | Site | Tactic | Diagnosis |
|---|---|---|---|
| 1 | L1911:96 | `simp only [gvCanonInv, dite_true, tailSwapPath, cast_PathMN_val, Subtype.coe_mk]` | simp does NOT discharge the goal `((gvCanonInv ...).2 ci).val = (t.2 ci).val.take ki ++ (t.2 cj).val.drop kj` even with `@[simp] cast_PathMN_val` |
| 2 | L1921:96 | `simp only [gvCanonInv, dif_neg (Fin.ne_of_gt hij), dite_true, tailSwapPath, cast_PathMN_val, Subtype.coe_mk]` | analogous to #1 for `gvCanonInv_val_cj` |
| 3 | L1929:57 | `simp only [gvCanonInv, dif_neg hk_ci, dif_neg hk_cj]` | simp opens `gvCanonInv` else-branch but doesn't reduce the inner cast |
| 4 | L1931:24 | `exact cast_PathMN_val _ _` | placeholder `h : n₁ = n₂` cannot be synthesized from goal type (cast h e).val = e.val — h is the equality witness inside `congrArg (PathMN cfg.m) (...)` proof and is not reconstructible |

**Why @[simp] cast_PathMN_val doesn't fire**: opening `gvCanonInv`
syntactically exposes `cast (congrArg (PathMN cfg.m) (proof))
(tailSwapPath ...)`.  The proof inside `congrArg` is a `by`-block, so
the elaborator may see the cast as an opaque term until that proof is
evaluated.  The simp pattern `(cast (congrArg (PathMN m) ?h) ?e).val`
should match the structure but apparently does not — likely because
the term post-unfold contains a tactic-block proof that doesn't
unify against the `?h` pattern variable.

**Root cause**: the `cast (congrArg (PathMN cfg.m) (by ...)) ...`
idiom inside `gvCanonInv`'s body makes the cast resistant to
simp-level rewriting.  The `cast_PathMN_val` lemma requires the
elaborator to identify `?h` from a tactic-proof witness, which it
cannot do generically.

### §3.B Cluster B (CASCADE from A; baseline 1 error visible, **true size ≥12**)

**Apparent baseline (15-error count)**:
- L1972:81 unsolved goals in `gvCanon_membership`, after
  `simp only [isNonCancellable, IsGVFixedPoint, not_exists]`

**True extent after Cluster C is resolved (S82 §4 experiment)**:
The L2036 placeholder failure (Cluster C) short-circuits elaboration
of the `gvCanon_membership` body so Lean stops reporting errors
within that proof block after the first elaboration failure.  With
Cluster C resolved (explicit suffix args at L2036), 11 NEW errors
surface at L2050–L2093:

| Site | Symptom |
|---|---|
| L2050:6 | `simp` made no progress |
| L2058:64 | omega could not prove the goal |
| L2063:64 | omega could not prove the goal |
| L2064:6 | `simp` made no progress |
| L2067:58 | No goals to be solved |
| L2071:6 | `split_ifs` failed: no if-then-else conditions to split |
| L2075:6 | `split_ifs` failed: no if-then-else conditions to split |
| L2080:35 (×2) | omega could not prove the goal |
| L2086:64 | omega could not prove the goal |
| L2091:64 | omega could not prove the goal |
| L2093:6 | `simp` made no progress |

All 11 newly-surfaced errors live within the `cases c with | zero =>
... | succ c' => ...` block + the `cases cfg.m with` block in
`gvCanon_membership`'s body (L2046–L2098).  Each error is a tactic
that depends on the (correctly-typed but proof-failed) `hge_ci`/`hge_cj`
PLUS the previously-broken cascade from Cluster A's
`gvCanonInv_val_ci/_cj` outputs.

**Conclusion**: Cluster B's true size is **≥ 12 errors** (1 visible
apparent + 11 latent unmasked by Cluster C fix).  The 15-error
baseline is therefore a misleading metric — the true count of
latent failures in the file is ≥ 26.

### §3.C Cluster C (apparent INDEPENDENT, 2 errors; functionally CASCADE-MASK)

| # | Site | Tactic | Diagnosis |
|---|---|---|---|
| 6 | L2036:50 | `have hge_ci := northBeforeEast_ge_prefix_true _ _ c hpfx_ci` | `sfx : LPath` is a free argument in the lemma's signature; elaborator cannot synthesize it from `hpfx_ci`'s type (which constrains only `pfx`) and there is no expected type to drive unification (`have` without explicit type) |
| 7 | L2036:7  | `have hge_ci := ...` | cascade: `failed to infer have declaration type` because #6's elaboration failed |

**Mechanically independent of Cluster A**:
`northBeforeEast_ge_prefix_true (pfx sfx : LPath) (c : ℕ) (hc : pfx.countP (· = false) = c) : ...` —
`sfx` does NOT appear in `hc`'s type, so any inference of `sfx` would
require an expected return type.  Pure elaboration-mode issue.

**Functionally entangled with Cluster B**: the L2036 elaboration
failure short-circuits 11 downstream tactics in `gvCanon_membership`,
reducing the apparent Cluster B count from ≥ 12 to 1.  Fixing
Cluster C without first fixing Cluster A surfaces those 11 latent
failures, increasing apparent error count from 15 → 24.

**Tactical implication**: Cluster C MUST be fixed at the same time as
Cluster A (or after).  Fixing it standalone is counterproductive (looks
like regression).

### §3.D Cluster D (CASCADE from A, 8 errors) — colEntry_eq + canonCrossN_image proofs

| # | Site | Tactic | Cascade source |
|---|---|---|---|
| 8  | L2171:6  | `exact northBeforeEast_prefix _ _ _ c' (by rw [hpfx_ci]; omega)` inside `colEntry_eq_ci` | uses `himg_ci` (L2158) which calls `gvCanonInv_val_ci`; placeholder issue is similar to Cluster C, but with `Type mismatch` symptom because the call is inside `exact` with expected type |
| 9  | L2181:6  | same as #8 for `cj` | uses `himg_cj` (L2160) |
| 10 | L2250:19 | `by rw [colEntry_eq ci c₀ le_rfl]; exact hlo_i` | uses `colEntry_eq` helper (L2183) which uses `gvCanonInv_val_other` |
| 11 | L2251:19 | analogous for `cj` | same |
| 12 | L2254:12 | `rw [himg_ci]` inside `split_ifs with hcm'` (interior branch) | `himg_ci` (L2158) depends on `gvCanonInv_val_ci` |
| 13 | L2264:8  | `simpa [if_neg hcm'] using hhi_j` in c₀=m branch | uses `ht'_def`+`gvCanonInv`+`canonNewPerm` simp chain; transitively depends on `gvCanonInv` Cluster A |
| 14 | L2267:12 | `rw [himg_cj]` analogous | same |
| 15 | L2277:8  | `simpa [if_neg hcm'] using hhi_i` analogous | same |

**Cluster D cascade dependency map**:
```
gvCanonInv_val_ci  (A:1, L1911)
gvCanonInv_val_cj  (A:2, L1921)
gvCanonInv_val_other  (A:3-4, L1929/L1931)
   ↓
himg_ci (L2158), himg_cj (L2160) in canonCrossN_image       → D:8-9, D:12-15
colEntry_eq_ci, colEntry_eq_cj, colEntry_eq (L2163-L2193)    → D:10-11
```

Cluster D's 8 errors are independent of L2036's short-circuit
(separate proof block, not affected by Cluster C).

## §4. In-session Cluster C fix experiment (REVERTED at end-of-session)

### §4.1 The experimental patch

Applied to L2036-L2037 (2 lines edited, +2 LOC):

```lean
  -- Key bounds: colEntry(img, c+1) ≥ y - src (from northBeforeEast_ge_prefix_true)
  have hge_ci := northBeforeEast_ge_prefix_true
    ((t.2 ci).val.take ki) ((t.2 cj).val.drop kj) c hpfx_ci
  have hge_cj := northBeforeEast_ge_prefix_true
    ((t.2 cj).val.take kj) ((t.2 ci).val.drop ki) c hpfx_cj
```

Parent file: 2528 → 2530 lines (net +2 LOC).

`sfx` chosen to match the `himg_ci`/`himg_cj` rewrites at L2040 so
that `hge_ci`/`hge_cj` apply directly to `hinterior` and `hfinal`
post-rewrite.

### §4.2 Build verification — 24 errors (not 13 as hypothesized)

Cold-image but warm-volume Docker build at S82T~22:10Z:
- Setup: P1 image was already built (cached at S81), but mathlib was
  re-cloned (the `lean-mathlib-cache` Docker volume holds .olean
  `build/` only — `packages/` lives in the workspace bind mount and
  is wiped between sessions).  Setup time ~3-4 min.
- P4 lake build result: **24 errors** (not the hypothesized 13).

Error inventory (post-patch line numbers):

```
1.  L1911:96  unsolved goals             (Cluster A unchanged)
2.  L1921:96  unsolved goals             (Cluster A unchanged)
3.  L1931:24  placeholder `h`            (Cluster A unchanged)
4.  L1929:57  unsolved goals             (Cluster A unchanged)
5.  L2050:6   `simp` made no progress    (CLUSTER B UNMASKED, was hidden)
6.  L2058:64  omega                       (CLUSTER B UNMASKED)
7.  L2063:64  omega                       (CLUSTER B UNMASKED)
8.  L2064:6   `simp` made no progress    (CLUSTER B UNMASKED)
9.  L2067:58  No goals                    (CLUSTER B UNMASKED)
10. L2071:6   split_ifs                   (CLUSTER B UNMASKED)
11. L2075:6   split_ifs                   (CLUSTER B UNMASKED)
12. L2080:35  omega                       (CLUSTER B UNMASKED)
13. L2080:35  omega                       (CLUSTER B UNMASKED)
14. L2086:64  omega                       (CLUSTER B UNMASKED)
15. L2091:64  omega                       (CLUSTER B UNMASKED)
16. L2093:6   `simp` made no progress    (CLUSTER B UNMASKED)
17. L2173:6   Type mismatch               (Cluster D, +2 LOC shift)
18. L2183:6   Type mismatch               (Cluster D, +2 LOC shift)
19. L2252:19  rewrite failed              (Cluster D, +2 LOC shift)
20. L2253:19  rewrite failed              (Cluster D, +2 LOC shift)
21. L2256:12  rewrite failed              (Cluster D, +2 LOC shift)
22. L2266:8   Type mismatch               (Cluster D, +2 LOC shift)
23. L2269:12  rewrite failed              (Cluster D, +2 LOC shift)
24. L2279:8   Type mismatch               (Cluster D, +2 LOC shift)
```

Total: **24 errors** = 4 (A unchanged) + 12 (B UNMASKED) + 8 (D, shifted).

The L1972:81 error of the baseline (Cluster B apparent) is GONE — but
replaced by 12 errors at L2050-L2093 in the same proof body.  Net for
Cluster B: 1 → 12 errors visible (i.e., 11 latent errors revealed).

### §4.3 Decision: revert the patch

The +2 LOC patch is **mechanically correct** (provides the right
explicit `sfx` terms to close the placeholder synthesis at L2036) but
**strategically counterproductive in isolation**:
- Increases visible error count 15 → 24
- Surfaces 11 latent errors that were always present but hidden
- Without a corresponding Cluster A fix, the unmask provides no
  closure path

**Reverted at end-of-S82 session.**  The +2 LOC patch is documented in
§4.1 and will be re-applied as part of S83+'s Cluster A fix bundle.

## §5. (α/β/γ) Cluster A replan refinement

Carry-forward from S81 §3 with S82's expanded cascade scope:

### (α) Refactor `gvCanonInv` def to expose `.val` directly

**Updated scope**: ~30-50 LOC at L1856-1895 + the +2 LOC L2036 patch
(must be co-shipped to actually close the cascade).

**Expected outcome**: closes Cluster A (4) + Cluster B (12 true) +
Cluster D (8) + Cluster C (2) = **26 errors → 0**.  This is a much
larger payoff than the S81-era "15 → 0" projection because S82
discovered Cluster B's true size.

**Recommendation strengthened**: (α) is now the ONLY path that closes
all clusters in one shot.  (β) and (γ) are abandoned as primary paths
because they don't unlock the Cluster B cascade.

### (β) Explicit `have h : ...` plug at L1931

**Status**: downgraded to diagnostic-only.  Closes 1 error (L1931),
leaves 23 others.  Not recommended.

### (γ) Swap `cast` → `Eq.mpr (congrArg ...)` in `gvCanonInv`

**Status**: only consider if (α) is infeasible.  Same Cluster A scope
but with structural risk.

### Updated S83 ACT plan

1. **Single PR scope**: (α) full `gvCanonInv` refactor + L2036
   placeholder fix.  ~32-52 LOC total.
2. **Expected build outcome**: 0 errors if Cluster A discharge
   correctly propagates through Cluster B's 12 latent + Cluster D's 8
   cascade; some non-zero residual if the unmasked Cluster B/D errors
   have separate root causes beyond Cluster A.
3. **Fallback**: if some Cluster B/D residual persists, the S81-era
   cluster classification was over-simplified.  S84 would investigate
   the residual as a new (sub-)cluster.

## §6. Bearer pin trustability

Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` stable since
2026-05-12 (~18 days at S82 entry).  No lake-manifest churn since
S81.  Bearer tables from S78 §1.2 (4-row Cluster A) and S76 §1
(14-row) remain trustable verbatim; NO bearer re-walk performed at
S82.

## §7. S82 ship scope (doc-only)

4 files in this S82 PR:

1. `research/problems/ballot-problem-oq-03-oq-01-oq-02/state.md` —
   prepend S82 block at head (Phase rewrite, Iteration 81 → 82, Last
   Updated S81 → S82 with Cluster B unmask discovery note); historical
   blockers + S80/S81 prose preserved verbatim below.

2. `src/data/research/problems/ballot-problem-oq-03-oq-01-oq-02.json`
   — currentState fields refreshed (focus, nextAction,
   attemptCounts.total 81 → 82, lastUpdate), builtItems += S82
   entry, insights += Cluster B unmask discovery, blockers entries
   unchanged.

3. `research/problems/ballot-problem-oq-03-oq-01-oq-02/sessions/2026-05-30-s82-parent-triage-2-cluster-taxonomy.md`
   — this memo.

4. `proofs/Proofs/BallotProblemOQ03OQ02.lean` — **NO net change**.
   The +2 LOC experimental patch at L2036 was applied for build
   verification, then reverted.  File ships at lineCount 2528
   (unchanged from S81 ship).

## §8. NON-actions at S82 (out of scope)

- No Cluster A fix attempt.  Deferred to S83 with (α) recommended.
- No persistent Cluster C fix.  Patch was applied + reverted for
  build verification; documented in §4.
- No sibling slug edits.  `leanFiles[]` numeric drift handled by
  mechanic batch precedent (#19744 + #19838).
- No `proofs/.lake` symlink repair (B3).  Persists; Docker volume
  mount mitigates per S80 §B3.
- No bearer pin re-walk.  Mathlib SHA stable ~18d.
- No mathematical (gnwProb_exchange F-side joint K-induction) work.
  Orthogonal to the rebuild path; preserved verbatim.

## §9. Successor — S83+ summary

S82 SHIPS:
- Refined 4-cluster taxonomy: A (4, ROOT) / B (≥12, CASCADE from A) /
  C (2, ELABORATION-MASK) / D (8, CASCADE from A) = ≥26 true latent
  failures
- Empirical discovery: the 15-error apparent baseline UNDERSTATES
  true failure count by ≥11 errors due to Cluster C elaboration
  short-circuit
- (α) recommendation strengthened — only path that closes all clusters

S83+ first action: do (α) full `gvCanonInv` refactor + L2036
placeholder co-fix.  Single PR, ~32-52 LOC.  Expected outcome: 0
errors (or refined cluster taxonomy if residual surfaces).

Mechanic batch-sync of sibling `leanFiles[]` for
`Proofs/BallotProblemOQ03OQ02.lean` (lineCount currently 2528, S81
mechanic batch precedent #19744 + #19838 applies post-S83 merge).
