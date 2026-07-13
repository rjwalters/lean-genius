# Current State

**Phase**: COMPLETED — stated OQ answered (two-sided Markov / Paley-Zygmund bracket formalized + merged)
**Since**: 2026-06-13 (completion-sync by researcher-6)
**Iteration**: 11

## COMPLETION-SYNC (this PR, 2026-06-13, researcher-6)

The stated OQ deliverable — *bracket `probCollision` between the Markov
upper bound `k(k-1)/(2d)` and the Paley-Zygmund lower bound* — is now
**formalized and merged**. The S8 PREP head below was frozen at
2026-06-09 still scoping "S5 ACT Paley-Zygmund route" as future work,
but **PR #22921 (merged 2026-06-13T12:51Z, +28 LOC)** shipped the
deliverable directly:

- `theorem probCollision_bracket (k d : ℕ) (hkd : k ≤ d) (hd : 0 < d)`:
  `k(k-1)/(2d + k(k-1)) ≤ probCollision k d ≤ k(k-1)/(2d)`, proved as the
  pair `⟨probCollision_ge_paley_zygmund, probCollision_le_choose_two_div⟩`
  (L245) — the literal two-sided sandwich the problem statement asks for.
- `theorem probCollision_eq_one_sub_descFactorial_div` (L257): the closed
  counting form `probCollision k d = 1 - descFactorial d k / d^k`.

`proofs/Proofs/BirthdayProblemOQ01OQ02.lean` is now **263 LOC / 6 public
theorems + 1 private lemma / 0 sorries / 0 axioms** (the prose head below
still says "235 LOC / 5 theorems, byte-stable since #21601" — that trailed
the `.lean`-only commit #22921; the deployer-owned `leanFiles[]` had
already auto-synced to 264/6).

The tighter variance-based lower bound (Route Y-α, gain ≈ 0.00066 at
n=23) that the S5/S8 PREP iterations were scoping is a **beyond-deliverable
refinement**, not part of the stated bracket → slug status **completed**.
Any future sharper-PZ work would be tracked as a new refinement.

---

## S8 PREP update (this PR, 2026-06-09, researcher-11, 9-day STATE-SYNC)

Doc-only catch-up after 9 days of file-byte stability:

- `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`: byte-stable since
  PR #21601 (commit `a1ab1a83cdd`, 2026-05-31). 235 LOC / 5 theorems
  (4 public + 1 private) / 0 sorries / 0 axioms.
- Lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (`v4.26.0`):
  **26-day window** with zero drift. All 9 named bearers from S4 ACT
  + S6 ACT carry forward by the lake-manifest-byte-stability argument.
- No open PR contention on either the `.lean` file or the companion
  `src/data/research/problems/birthday-problem-oq-01-oq-02.json`.

This iteration ships:

1. **Math re-derivation of the S5 target formula.** Confirms the
   `E[X²] = E[X] + C(n,2)·(C(n,2) − 1) / d²` claim from state.md
   "Next Action" is **exact** (not a disjoint-pairs approximation),
   because for the birthday problem the indicators
   `I_{ij} := 𝟙[f(i) = f(j)]` are pairwise uncorrelated despite not
   being independent (case-split over `|{i,j} ∩ {i',j'}|`).
2. **Numerical recheck.** At `n = 23, d = 365`: current S4 ACT lower
   bound `0.40939` vs S5 ACT target `0.41005` → gain Δ ≈ 0.00066
   (slightly larger than the original 0.0003 estimate).
3. **Route choice for S5 ACT.** Recommend **Route Y-α** (combinatorial
   direct via `Finset.sum_mul_sq_le_sq_mul_sq` Cauchy-Schwarz +
   descFactorial bridge) over **Route Y-β** (Mathlib `Probability.Variance`
   lift). Y-α stays in already-verified API and reuses S6 ACT's
   bridge. Estimated LOC drops from the original ~120 monolith to
   70–90 split over two ACT PRs.
4. **Three-step S5 staging** (`S5a PREP / S5b ACT / S5c ACT`) so each
   PR is small and Docker-verifiable.
5. **Failure-mode register extension.** Add F10 (Nat.choose cast
   residue → stay in `k·(k−1)` arithmetic) and F11 (Cauchy-Schwarz
   bearer name TBD; flag for S5b PREP audit).

**Bearer pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` — unchanged
since v4.26.0 freeze (2026-05-14, now 26 days stable).

**Next Action**: **S5b PREP** — bearer audit for `Finset`-level
Cauchy-Schwarz at v4.26.0 (`Finset.sum_mul_sq_le_sq_mul_sq` vs
alternatives) + paste-ready scaffold for `expected_pairs_sq_eq`
closed-form `E[X²]` helper (~40 LOC, LOW risk).

See `sessions/2026-06-09-s8-prep-9day-state-sync-and-px-target-refinement.md`
for the full math re-derivation, route comparison, LOC budget split,
and updated failure-mode register.

---

## S6 ACT update (PR #21601, 2026-05-31, researcher-1, descFactorial bridge)

Ships the LOW-risk follow-on flagged by state.md "Next Action" — the
`probAllDistinct ↔ descFactorial` bridge, as a single ~22-line theorem
appended to `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`:

```lean
theorem probAllDistinct_eq_descFactorial_div (k d : ℕ) (hkd : k ≤ d) (hd : 0 < d) :
    probAllDistinct k d = (Nat.descFactorial d k : ℝ) / (d : ℝ) ^ k
```

**Proof outline** (no induction; all Mathlib name lookups):
1. Rewrite each factor `1 - i/d = ((d - i : ℕ) : ℝ) / d` for `i < k`
   using `Nat.cast_sub` (valid since `i ≤ d`) plus `field_simp`.
2. Split the product of fractions with `Finset.prod_div_distrib`.
3. Collapse the denominator `∏ d = d^k` via `Finset.prod_const +
   Finset.card_range`.
4. Identify the numerator with `Nat.descFactorial d k` via
   `Nat.descFactorial_eq_prod_range` (after `← Nat.cast_prod`).

**File status**: 235 LOC, 5 theorems (1 private), 0 sorries, 0 axioms.
**Docker**: GREEN, 7744 jobs, ~21s incremental (warm cache after a
fresh mathlib download; first build of the day was ~3 min wall-clock
including the cache pull).

**Bearer pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged
since v4.26.0 freeze 2026-05-14; 17 days stable). S7 PREP's 3-bearer
spot check carried forward; no Mathlib bump.

**Failure modes encountered at S6 ACT iter 1**: zero. The proof closed
on first Docker submission. F1–F9 + F-extra register from S6 STATE-SYNC
remains intact; no new failure modes emerged in the descFactorial scope.

**Next Action**: Optional **S5 PREP — tight Paley-Zygmund denominator**
(Δ ≈ 0.0003 via exact `E[X²]`, ~120 LOC, MEDIUM risk on Mathlib
`Probability.Variance` API). The descFactorial bridge is now
downstream-ready for any OQ01OQ01 counting-formulation Paley-Zygmund
coupling.

See `sessions/2026-05-31-s6-act-descfactorial-bridge.md` for the full
proof walkthrough.

---

## S6 STATE-SYNC update (2026-05-16, researcher-10, STATE-SYNC absorbing S4 ACT merge)

S4 ACT (PR #19422) merged 2026-05-16T04:40:14Z (merge commit `cbfc0fdd8f1`).
PR body explicitly stated "a follow-on S6 STATE-SYNC is owed to absorb this
ACT (state.md `phase` → `S4 ACT merged`; `iteration` 6 → 7; JSON
`currentState` refresh; bearer table augmented with `Real.exp_neg`'s
`← one_div` form + `field_simp + ring` trap)." This iteration discharges
that owed STATE-SYNC.

`proofs/Proofs/BirthdayProblemOQ01OQ02.lean` is now **203 LOC** on main
(was 143 pre-PR-#19422), **4 theorems** (was 2): `one_sub_prod_le_sum` (S2),
`probCollision_le_choose_two_div` (S3), `one_sub_exp_neg_ge_div_one_add`
(S4 private bridge), `probCollision_ge_paley_zygmund` (S4 main).
0 sorries, 0 axioms.

**Closed-form bracket** on `probCollision k d` now stands:

```
k(k-1) / (2d + k(k-1))  ≤  probCollision k d  ≤  k(k-1) / (2d)
```

Both bounds purely intra-namespace (no OQ01 dependency); OQ01's 7
v4.26.0 regressions owned by separate-slug mechanic pass (catalogue
unchanged since S4c §5).

This iteration ships:

- state.md head refresh (Phase, Since, Iteration); S4 ACT row appended
  to Iteration History; Next Action rewritten from "S4 ACT paste-ready"
  (DONE) to "S5 PREP — tight Paley-Zygmund denominator" target.
- Research JSON 13-field drift refresh (`phase`, `currentState.{phase,
  since, iteration, focus, attemptCounts.{total, currentApproach},
  nextAction}`, `knowledge.{progressSummary, builtItems, insights,
  nextSteps}`, `lastUpdate`).
- knowledge.md Insight 6 added: **F-extra trap** — `field_simp` on
  `1 - 1/(1+x) = x/(1+x)` leaves algebraic residue `1 + x - 1 = x`
  requiring `ring` to close. Surfaced at S4 ACT iter 1 (PR #19422),
  fixed at iter 2.
- Bearer-pin recheck: lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  unchanged (no Mathlib bump since v4.26.0 2026-05-14). 0 drift in any
  of the 9 S4c-era bearers or 4 S4-ACT-era bearers.
- Failure-mode register update: F1–F9 carried forward (F8, F9 pre-pinned
  by S5b §3a/§4a, fired & fixed at S4 ACT iter 1); **F-extra is new**
  at S4 ACT iter 1 (not anticipated by S4c/S5/S5b registers).
- S5 PREP target documented (tight Paley-Zygmund Δ ≈ 0.0003 via exact
  `E[X²]`, ~120 LOC, MEDIUM risk on Mathlib `Probability.Variance` API
  surface); S6 PREP target documented (probAllDistinct ↔ descFactorial
  bridge, ~30 LOC, LOW risk).

Infrastructure (2026-05-16T09:55Z): Docker daemon hung exit 124 + host
disk 100% / 6.9Gi avail. **Irrelevant** to this doc-only STATE-SYNC.

See `sessions/2026-05-16-s6-state-sync-absorb-s4-act-merge.md` for the
full drift inventory, F-extra trap analysis, S5/S6 PREP target
specifications, and ACT-readiness forward-gate.

---

## S5 update (2026-05-16, researcher-3, STATE-SYNC post-S3-ACT-merge)

Post-merge STATE-SYNC catching `state.md` and the website JSON up to the
post-S3-ACT-merge reality:

- PR #19098 (S3 ACT, Markov closed-form `probCollision_le_choose_two_div`,
  build verified 7744 jobs) **MERGED** 2026-05-15T23:30:27Z (merge commit
  `e44038366d8df3c9be9c65858e63c6997b7e1646`). `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`
  is now 143 LOC on main, 2 theorems, 0 sorries, 0 axioms.
- 0 open PRs on the slug or on the file at this STATE-SYNC's commit time;
  no rebase risk for S4 ACT.
- Lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged in the ~5.5h
  since S4c PREP (researcher-9, PR #19315 merged 19:47Z); 9-row bearer
  drift table is byte-stable.

This iteration ships:

- Bearer drift recheck (same 9 bearers as S4c §3, byte-stability argument
  via lake-manifest immutability). **Net: 0 rows drifted.**
- S4 ACT readiness gate refresh — Option A/B stacking choice from S4c §4b
  is **settled by event** (Option B selected; #19098 merged within drain
  wave). The next S4 ACT worker writes a clean 25-LOC delta against
  `origin/main` HEAD `d35a6f0f`; no overlay-stack work owed.
- Paste-anchor pin: PR #19250 §4's 25-LOC scaffold inserts between L142
  (`  exact hbound`, last line of `probCollision_le_choose_two_div`) and
  L143 (`end BirthdayProblemOQ01OQ02`). New failure-mode row F7 (paste
  outside namespace) added to the F1–F6 register.
- OQ01 parent-regression catalogue re-verified: L408 `Nat.choose_three_right (m + 2)`
  unchanged; L508–511 four `native_decide` examples unchanged; no
  mechanic / doctor PR has touched the file since S4c.

See `sessions/2026-05-16-s5-state-sync-post-s3-act-merge.md` for the full
post-merge snapshot, byte-stability methodology note, settled-by-event
stacking analysis, paste-anchor pin, refreshed failure-mode register, and
re-verified OQ01 handoff catalogue.

## S4c update (2026-05-15, researcher-9, STATE-SYNC + drift recheck)

STATE-SYNC catching `state.md` and the website JSON up to the post-18:00-drain
reality:

- PR #19098 (S3 ACT, Markov closed-form `probCollision_le_choose_two_div`,
  build verified 7744 jobs) is OPEN/MERGEABLE on `BirthdayProblemOQ01OQ02.lean`.
- PR #19250 (S4 PREP, Path Z 25-LOC scaffold for the Paley-Zygmund-equivalent
  lower bound `probCollision_ge_paley_zygmund`) MERGED 2026-05-15T18:03:33Z.
- PR #19262 (S4b PREP, bearer-pin re-verification + numerical witness for
  PR #19250) MERGED 2026-05-15T18:02:47Z.

This iteration ships:

- Drift recheck (9 bearer rows: 5 from S3 ACT + 4 from S4 PREP) against lake
  SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. **Net: 0 rows drifted.**
- S4 ACT readiness gate (entry conditions, stacking-strategy choice A vs B,
  paste sequence, 6-row failure-mode register).
- OQ01 parent-regression handoff catalogue (7 v4.26.0 errors with replacement
  candidates; `Nat.choose_three_right` confirmed absent from Mathlib v4.26.0).

See `sessions/2026-05-15-s4c-prep-state-sync-and-act-readiness-gate.md` for
the full STATE-SYNC + drift recheck + readiness gate.

## S4b update (2026-05-15, researcher-8)

PR #19262 strict-sibling audit of PR #19250 §5 bearer table:

- 4/4 named Path Z bearers re-verified at lake SHA `2df2f015...`:
  `Real.add_one_le_exp` (Exponential.lean:646), `Real.exp_neg` (Exponential.lean:236
  inside `namespace Real` 198-346), `one_div_le_one_div_of_le` (Field/Basic.lean:77).
- Flagged `Complex.exp_neg` co-existence at Exponential.lean:161 (`namespace
  Complex` 88-196) — advised explicit `Real.` qualifier in the Path Z bridge.
- Surveyed for direct 1-line bearers for `x/(1+x) ≤ 1 - exp(-x)` at the pin:
  0 hits, confirming PR #19250's choice to chain three bearers is canonical.

## S4 update (2026-05-15, researcher-8)

PR #19250 doc-only design memo proposing **Path Z** — Paley-Zygmund-equivalent
lower bound via exponential composition (recommended over Path X / Path Y):

| Path | Approach | LOC | Status |
|------|----------|----:|-------|
| X    | OQ01-import named bound (`variancePairs_le_expected`) | ~60 | ❌ blocked by 7-error v4.26.0 regression in `BirthdayProblemOQ01.lean` |
| Y    | full closed-form Paley-Zygmund via E[X²] expansion (gain Δ ≈ 0.0003) | ~120 | ⚠ overlong for the marginal tightening |
| **Z**| chain OQ02.probCollision_ge (already-shipped exponential lower bound) with `1 - exp(-x) ≥ x/(1+x)` via `Real.add_one_le_exp` | ~25 | ✅ recommended |

Ships a paste-ready 25-LOC scaffold materialising `probCollision_ge_paley_zygmund`
as:

```lean
probCollision k d ≥ k(k-1) / (2d + k(k-1))
```

Match: `knowledge.md` §"Paley–Zygmund bound" weak form.

## S3 update (2026-05-14, researcher-?)

PR #19098 shipped the Markov coupling closed-form theorem in
`proofs/Proofs/BirthdayProblemOQ01OQ02.lean`:

```lean
theorem probCollision_le_choose_two_div (k d : ℕ) (hkd : k ≤ d) (hd : 0 < d) :
    probCollision k d ≤ (k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ))
```

- 1 new theorem (`probCollision_le_choose_two_div`) chained on S2's
  `one_sub_prod_le_sum` (line 38) + OQ02's `gauss_sum_div` (OQ02:145).
- 0 sorries, 0 new axioms, 0 changes to OQ01 / OQ02 namespace.
- **Docker build verified**: 7744 jobs, 11s warm cache.
- Closed form `k(k-1)/(2d)` chosen over `expectedPairs` form to avoid
  importing the v4.26.0-regressed parent `Proofs.BirthdayProblemOQ01`
  (7 errors at L410-511 — see S4c session note §5 for catalogue).
- Together with OQ02's `probCollision_ge` (exponential lower bound, OQ02:173),
  brackets `probCollision` between `1 - exp(-k(k-1)/(2d))` and `k(k-1)/(2d)`.

## S2 update (2026-05-13, researcher-10)

Created `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` (~80 LOC) with the
single helper theorem `one_sub_prod_le_sum` per S1 §"Next Action" sketch:

```lean
theorem one_sub_prod_le_sum {n : ℕ} (f : ℕ → ℝ)
    (hnn : ∀ i, i < n → 0 ≤ f i) (hle : ∀ i, i < n → f i ≤ 1) :
    1 - ∏ i ∈ Finset.range n, (1 - f i)
      ≤ ∑ i ∈ Finset.range n, f i
```

- 0 sorries, 0 new axioms.
- Proof by induction on `n`. Successor step uses `Finset.prod_range_succ` +
  `Finset.sum_range_succ`, then closes with `nlinarith` given the
  side-conditions `0 ≤ ∏ ≤ 1` (from `Finset.prod_nonneg` /
  `Finset.prod_le_one`) and the product hint
  `mul_nonneg (sub_nonneg.mpr hP_le_one) hfk_nn`.
- **Build status**: pending Docker verification
  (`./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ02`).
  Per the lake-symlink-loop trap precedent, shipping the file as a
  build-pending PR so the Auditor or Doctor can verify from a clean
  worktree.

## Open PRs

- (this PR — S6 STATE-SYNC) — doc-only catch-up absorbing S4 ACT merge.
- No competing open PRs on `BirthdayProblemOQ01OQ02.lean`.

## Iteration History (recent)

| Iter | Date       | Researcher    | PR     | Outcome                                                                                                                                |
|------|------------|---------------|--------|----------------------------------------------------------------------------------------------------------------------------------------|
| S1   | 2026-05-11 | researcher-12 | (memo) | OBSERVE — two-coupling decomposition (Markov + Paley-Zygmund); 5-step S2-S6 roadmap                                                    |
| S2   | 2026-05-13 | researcher-10 | #18921 | ACT — `one_sub_prod_le_sum` (union bound for products); +80 LOC; Docker pending                                                        |
| S3   | 2026-05-14 | researcher-?  | #19098 | ACT — `probCollision_le_choose_two_div` Markov closed-form; +63 LOC (143 total); Docker 7744 jobs; 0/0/0; merged 2026-05-15T23:30:27Z |
| S4   | 2026-05-15 | researcher-8  | #19250 | PREP — Path Z 25-LOC scaffold design memo (recommended over X/Y); merged 2026-05-15T18:03:33Z                                          |
| S4b  | 2026-05-15 | researcher-8  | #19262 | PREP — bearer pin re-verification (4/4); merged 2026-05-15T18:02:47Z                                                                   |
| S4c  | 2026-05-15 | researcher-9  | #19315 | PREP — STATE-SYNC + ACT readiness gate; merged 2026-05-15T19:47Z                                                                       |
| S5   | 2026-05-16 | researcher-3  | #19355 | STATE-SYNC — post-S3-ACT-merge catch-up + paste anchor pin; merged 2026-05-16T03:51:17Z                                                |
| S5b  | 2026-05-16 | researcher-?  | #19417 | audit-at-pick-time — F8/F9 elaboration trap pre-pins; merged 2026-05-16T03:51:17Z                                                      |
| S4   | 2026-05-16 | researcher-?  | #19422 | ACT — `probCollision_ge_paley_zygmund` + private bridge; +61 LOC (143→203); Docker 7744 jobs; 0/0/0; merged 2026-05-16T04:40:14Z       |
| S6   | 2026-05-16 | researcher-10 | #19430 | STATE-SYNC — absorb S4 ACT merge; state.md head + JSON 13-field refresh + knowledge Insight 6 (F-extra trap); doc-only                  |
| S7   | 2026-05-30 | researcher-1  | #21311 | PREP — 14-day bearer drift recheck (3-bearer spot check; ZERO drift; Docker recovered)                                                 |
| S6 ACT| 2026-05-31 | researcher-1  | #21601 | ACT — `probAllDistinct_eq_descFactorial_div` bridge; +30 LOC (205→235); Docker 7744 jobs; 0/0/0; zero iter-1 failure modes              |
| S8 PREP| 2026-06-09 | researcher-11 | (this) | PREP — 9-day STATE-SYNC + math re-derivation of E[X²] formula + Route Y-α vs Y-β choice + 3-step S5 staging plan; doc-only             |

## Next Action

**S5b PREP — Cauchy-Schwarz bearer audit + `expected_pairs_sq_eq` scaffold** (next iteration, doc-only).

Audit the Mathlib v4.26.0 surface for `Finset`-level Cauchy-Schwarz:

- Primary candidate: `Finset.sum_mul_sq_le_sq_mul_sq` (or its
  `Real.inner_mul_le_norm_mul_norm` Finset specialisation).
- Secondary: hand-rolled via `Finset.inner_mul_le_norm_mul_norm`
  (if the above is missing).

Then produce a paste-ready scaffold for the helper

```lean
lemma expected_pairs_sq_eq (k d : ℕ) (_hd : 0 < d) :
    -- E[X²] over uniform `Fin n → Fin d`, in closed form
    ((1 : ℝ) / (d : ℝ)^k) *
      ∑ f : Fin k → Fin d, (collisionCount f : ℝ)^2
      = (k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ))
        + ((k : ℝ) * ((k : ℝ) - 1) / 2)
          * ((k : ℝ) * ((k : ℝ) - 1) / 2 - 1) / (d : ℝ)^2
```

(or its OQ02-product equivalent via S6 ACT's descFactorial bridge).

**LOC budget**: ~40 LOC for the helper; S5c ACT then chains in
~40 more LOC for the closed-form
`probCollision_ge_paley_zygmund_tight`.

**Risk**: LOW-MEDIUM — main risk is the Cauchy-Schwarz bearer name
(F11 above). If the named bearer is missing, fall back to a 6-line
Lagrange identity proof.

**Original "S5 PREP — Tight Paley-Zygmund (Path Y elaboration)" superseded by this S8 PREP route choice. Retained below for context.**

---

### Superseded — original "S5 PREP" target (Path Y monolith)

Tighten the lower-bound denominator from `2d + k(k-1)` (current S4 ACT) to `2d + k(k-1) - 2` using exact second-moment formula:

```
E[X²] = E[X] + C(n,2) * (C(n,2) - 1) / d²
```

instead of the variance bound `Var(X) ≤ E[X]`. The resulting tight Paley-Zygmund lower bound:

```
probCollision k d ≥ E[X]² / E[X²]
                  = (k(k-1)/(2d))² / (k(k-1)/(2d) + C(n,2)*(C(n,2)-1)/d²)
                  ≥ k(k-1) / (2d + k(k-1) - 2)  [after algebraic simplification]
```

**Gain**: Δ ≈ 0.0003 at threshold `n = 23, d = 365` (lower bound 0.4732 → 0.4735). Marginal but completes textbook Paley-Zygmund.

**LOC budget**: ~120 LOC (one major second-moment helper + one closed-form theorem mirroring `probCollision_ge_paley_zygmund` with the tighter denominator).

**Risk**: MEDIUM — `E[X²]` Mathlib `Probability.Variance` API surface unverified; may need ad-hoc derivation from `BirthdayProblemOQ02.gauss_sum_div` + a new `gauss_sum_sq_div` helper (~30 LOC).

**Parallel S6 PREP target**: `probAllDistinct_eq_descFactorial_div` bridge (~30 LOC telescoping) connecting OQ02-product to OQ01OQ01-counting. Independent of S5 PREP; either can be picked first.

**Infrastructure gate**: S5 PREP is doc-only (design memo + Mathlib API recheck), unblocked by Docker. S5 ACT after PREP would need Docker recovery.

---

## Original S1 OBSERVE state (preserved for reference)

## Current Focus

S1 (researcher-12): Initial survey of the coupling between
`BirthdayProblemOQ01.expectedPairs` (first-moment quantity, `ℚ`) and
`BirthdayProblemOQ02.probCollision` (probability quantity, `ℝ`).
Establishes:

1. **Markov coupling** `probCollision ≤ ↑expectedPairs` is a direct
   chain of `one_sub_prod_le_sum` (union bound for products) + the
   existing `gauss_sum_div` (`OQ02`). ~40 lines.
2. **Paley-Zygmund coupling** `probCollision ≥ E[X]² / E[X²]` is
   heavier — requires (a) the second-moment formula in OQ02-style and
   (b) a bridge to the OQ01OQ01 finite-sample-space `collisionCount`
   random variable. ~80 lines split over S5/S6.
3. **Bridge** `probAllDistinct n d = descFactorial(d,n) / d^n` unifies
   OQ02's product formulation and OQ01OQ01's counting formulation;
   needed for Paley-Zygmund but stands as its own ~30-line lemma.

## Active Approach

**Two complementary couplings, Markov first.**

The Markov path (S2 → S3) is mechanical: a new helper
`one_sub_prod_le_sum` + the existing `gauss_sum_div` + `two_mul_choose_two`
+ casts. This delivers the upper-bound half of the coupling.

The Paley-Zygmund path (S4 → S6 → S5) is heavier and depends on the
bridge S6 between OQ02 and OQ01OQ01. Deferred to multiple sessions.

The two couplings together place `probCollision` strictly between
`(C(n,2)/d) / (1 + C(n,2)/d)` (P-Z lower) and `C(n,2)/d` (Markov upper).
For `n ≥ 28` (`d = 365`) the lower bound is ≥ 1/2, recovering the
classical birthday threshold without invoking the exponential bound.

## Blockers

None mathematical. Practical: the `proofs/.lake` symlink is broken in
researcher worktrees (~25-45 min cost per Docker build), but S2/S3 are
short enough that one end-of-S3 Docker build is feasible.

## Next Action

**S2 (any researcher)**: Create
`proofs/Proofs/BirthdayProblemOQ01OQ02.lean` and add the helper:

```lean
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset
import Proofs.BirthdayProblemOQ01
import Proofs.BirthdayProblemOQ02

namespace BirthdayProblemOQ01OQ02

open BirthdayProblemOQ01 BirthdayProblemOQ02 BigOperators

/-- Union-bound form: for `f` valued in `[0, 1]`,
    `1 - ∏ (1 - f i) ≤ ∑ f i`. -/
theorem one_sub_prod_le_sum {n : ℕ} (f : ℕ → ℝ)
    (hnn : ∀ i, i < n → 0 ≤ f i) (hle : ∀ i, i < n → f i ≤ 1) :
    1 - ∏ i ∈ Finset.range n, (1 - f i)
      ≤ ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih =>
    -- ... use `Finset.prod_range_succ`, `Finset.sum_range_succ`,
    -- and the algebraic identity
    --   1 - (1-a)·P = a + (1-a)·(1-P)
    -- with the bound (1-a)·(1-P) ≤ 1-P from 0 ≤ 1-a ≤ 1.
    sorry

end BirthdayProblemOQ01OQ02
```

Verify with Docker build (`./proofs/scripts/docker-build.sh
Proofs.BirthdayProblemOQ01OQ02`) at the end of S2; ~25-45 min wall-clock
with the broken `.lake` symlink.

**S3 (next session after S2)**: Add the Markov coupling
`probCollision_le_expectedPairs`. Chains `one_sub_prod_le_sum` with
`gauss_sum_div` (OQ02:145) and `two_mul_choose_two` (OQ01:109) plus
`push_cast` for the ℚ → ℝ bridge.

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 1
- Approaches tried: 1

## Open files

- `problem.md` — Plain statement, why-it-matters, Mathlib infrastructure
  map, S2-through-S6 decomposition, risk notes.
- `knowledge.md` — S1 session note: Markov 1-line proof, Paley-Zygmund
  formula, worked numerics for `n = 23` and `n = 50`, Mathlib gaps,
  next-action priority table.

## S1 Deliverable

This iteration is **survey-only**:

- 0 new theorems
- 0 new sorries
- 0 axioms touched
- 0 `.lean` files created

Substantive output: `problem.md` (Mathlib API map + suggested S2-S6
decomposition + risk notes) and `knowledge.md` (math content of both
couplings + worked numerics + Mathlib gap inventory). Ready hand-off
for the S2 implementer.
